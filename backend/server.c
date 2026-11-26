#include <winsock2.h>
#include <ws2tcpip.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <io.h>
#include <bcrypt.h>

/*
 * Include the original DSA implementation without editing it.
 * Renaming its CLI main lets this HTTP server provide its own main().
 */
#define main orbit_original_cli_main
#include "chat_dsa.c"
#undef main

#define PORT 8080
#define BUFFER_SIZE 16384
#define OUTPUT_SIZE 8192
#define AUTH_SALT_SIZE 16
#define AUTH_HASH_SIZE 32
#define AUTH_ITERATIONS 120000

typedef struct {
    char username[NAME_LEN];
    unsigned char salt[AUTH_SALT_SIZE];
    unsigned char hash[AUTH_HASH_SIZE];
} AuthCredential;

static AuthCredential credentials[MAX_USERS];
static int credential_count = 0;

static void send_response(SOCKET client, int status, const char *status_text,
                          const char *content_type, const char *body) {
    char header[1024];
    int body_len = (int)strlen(body);
    int header_len = snprintf(header, sizeof(header),
        "HTTP/1.1 %d %s\r\n"
        "Content-Type: %s\r\n"
        "Access-Control-Allow-Origin: *\r\n"
        "Access-Control-Allow-Methods: GET, POST, OPTIONS\r\n"
        "Access-Control-Allow-Headers: Content-Type\r\n"
        "Content-Length: %d\r\n"
        "Connection: close\r\n\r\n",
        status, status_text, content_type, body_len);
    if (header_len > 0) {
        send(client, header, header_len, 0);
        send(client, body, body_len, 0);
    }
}

static int receive_request(SOCKET client, char *request, size_t capacity) {
    size_t total = 0, content_length = 0;
    char *header_end = NULL;
    request[0] = '\0';

    while ((header_end = strstr(request, "\r\n\r\n")) == NULL) {
        if (total >= capacity - 1) return 0;
        int n = recv(client, request + total, (int)(capacity - total - 1), 0);
        if (n <= 0) return 0;
        total += (size_t)n;
        request[total] = '\0';
    }

    size_t header_size = (size_t)(header_end - request) + 4;
    char *line = request;
    while (line < header_end) {
        char *end = strstr(line, "\r\n");
        if (!end || end > header_end) break;
        if (_strnicmp(line, "Content-Length:", 15) == 0) {
            content_length = (size_t)strtoul(line + 15, NULL, 10);
            break;
        }
        line = end + 2;
    }
    if (content_length > capacity - header_size - 1) return 0;

    while (total < header_size + content_length) {
        int n = recv(client, request + total, (int)(capacity - total - 1), 0);
        if (n <= 0) return 0;
        total += (size_t)n;
        request[total] = '\0';
    }
    return 1;
}

/* Read one JSON string property, including escaped characters. */
static int json_string(const char *body, const char *property,
                       char *out, size_t out_size) {
    char key[80];
    snprintf(key, sizeof(key), "\"%s\"", property);
    const char *p = strstr(body, key);
    if (!p) return 0;
    p = strchr(p, ':');
    if (!p) return 0;
    while (*++p && isspace((unsigned char)*p)) {}
    if (*p != '"') return 0;
    p++;
    size_t used = 0;
    while (*p && *p != '"') {
        char ch = *p++;
        if (ch == '\\') {
            if (!*p) return 0;
            ch = *p++;
            if (ch == 'n') ch = '\n';
            else if (ch == 'r') ch = '\r';
            else if (ch == 't') ch = '\t';
        }
        if (used + 1 >= out_size) return 0;
        out[used++] = ch;
    }
    if (*p != '"') return 0;
    out[used] = '\0';
    return 1;
}

static void json_escape(const char *input, char *output, size_t size) {
    size_t j = 0;
    for (size_t i = 0; input[i] && j + 2 < size; i++) {
        unsigned char c = (unsigned char)input[i];
        if (c == '"' || c == '\\') {
            output[j++] = '\\'; output[j++] = (char)c;
        } else if (c == '\n') {
            output[j++] = '\\'; output[j++] = 'n';
        } else if (c == '\r') {
            output[j++] = '\\'; output[j++] = 'r';
        } else if (c == '\t') {
            output[j++] = '\\'; output[j++] = 't';
        } else if (c >= 32) {
            output[j++] = (char)c;
        }
    }
    output[j] = '\0';
}

/* Passwords are stored as PBKDF2-HMAC-SHA256 hashes, never as plain text. */
static int derive_password_hash(const char *password,
                                const unsigned char salt[AUTH_SALT_SIZE],
                                unsigned char hash[AUTH_HASH_SIZE]) {
    BCRYPT_ALG_HANDLE algorithm = NULL;
    NTSTATUS status = BCryptOpenAlgorithmProvider(
        &algorithm, BCRYPT_SHA256_ALGORITHM, NULL, BCRYPT_ALG_HANDLE_HMAC_FLAG);
    if (status < 0) return 0;

    status = BCryptDeriveKeyPBKDF2(
        algorithm,
        (PUCHAR)password, (ULONG)strlen(password),
        (PUCHAR)salt, AUTH_SALT_SIZE,
        AUTH_ITERATIONS,
        hash, AUTH_HASH_SIZE, 0);
    BCryptCloseAlgorithmProvider(algorithm, 0);
    return status >= 0;
}

static AuthCredential *find_credential(const char *username) {
    char key[NAME_LEN];
    lower_copy(key, username, sizeof key);
    for (int i = 0; i < credential_count; i++)
        if (strcmp(credentials[i].username, key) == 0) return &credentials[i];
    return NULL;
}

static int constant_time_equal(const unsigned char *a, const unsigned char *b, size_t n) {
    unsigned char difference = 0;
    for (size_t i = 0; i < n; i++) difference |= (unsigned char)(a[i] ^ b[i]);
    return difference == 0;
}

static void send_auth_result(SOCKET client, int status, const char *status_text,
                             int success, const char *message) {
    char body[512];
    char escaped[256];
    json_escape(message, escaped, sizeof escaped);
    snprintf(body, sizeof body,
             "{\"success\":%s,\"message\":\"%s\"}",
             success ? "true" : "false", escaped);
    send_response(client, status, status_text, "application/json", body);
}

static void handle_auth_register(SOCKET client, const char *body) {
    char username[NAME_LEN] = {0};
    char password[65] = {0};
    if (!json_string(body, "username", username, sizeof username) ||
        !json_string(body, "password", password, sizeof password)) {
        send_auth_result(client, 400, "Bad Request", 0, "Enter a username and password.");
        return;
    }
    size_t name_len = strlen(username), password_len = strlen(password);
    if (name_len < 1 || name_len >= NAME_LEN) {
        send_auth_result(client, 400, "Bad Request", 0, "Username must be 1–30 characters.");
        return;
    }
    for (size_t i = 0; i < name_len; i++) {
        if (!isalnum((unsigned char)username[i]) && username[i] != '_') {
            send_auth_result(client, 400, "Bad Request", 0, "Use letters, numbers and underscores in usernames.");
            return;
        }
    }
    if (password_len < 6 || password_len > 64) {
        send_auth_result(client, 400, "Bad Request", 0, "Password must be 6–64 characters.");
        return;
    }
    if (hash_find(username) || find_credential(username)) {
        send_auth_result(client, 409, "Conflict", 0, "That username is already taken.");
        return;
    }
    if (credential_count >= MAX_USERS) {
        send_auth_result(client, 503, "Service Unavailable", 0, "The account limit has been reached.");
        return;
    }

    AuthCredential credential;
    memset(&credential, 0, sizeof credential);
    lower_copy(credential.username, username, sizeof credential.username);
    if (BCryptGenRandom(NULL, credential.salt, AUTH_SALT_SIZE,
                        BCRYPT_USE_SYSTEM_PREFERRED_RNG) < 0 ||
        !derive_password_hash(password, credential.salt, credential.hash)) {
        send_auth_result(client, 500, "Internal Server Error", 0, "Could not securely create the account.");
        return;
    }

    User *user = register_user(username);
    if (!user) {
        send_auth_result(client, 400, "Bad Request", 0, "Could not create that account.");
        return;
    }
    credentials[credential_count++] = credential;
    cur = user;
    send_auth_result(client, 200, "OK", 1, "Account created. Welcome to Orbit!");
}

static void handle_auth_login(SOCKET client, const char *body) {
    char username[NAME_LEN] = {0};
    char password[65] = {0};
    if (!json_string(body, "username", username, sizeof username) ||
        !json_string(body, "password", password, sizeof password)) {
        send_auth_result(client, 400, "Bad Request", 0, "Enter your username and password.");
        return;
    }
    AuthCredential *credential = find_credential(username);
    User *user = hash_find(username);
    unsigned char candidate[AUTH_HASH_SIZE];
    if (!credential || !user || !derive_password_hash(password, credential->salt, candidate) ||
        !constant_time_equal(candidate, credential->hash, AUTH_HASH_SIZE)) {
        cur = NULL;
        send_auth_result(client, 401, "Unauthorized", 0, "Incorrect username or password.");
        return;
    }
    cur = user;
    send_auth_result(client, 200, "OK", 1, "Welcome back!");
}

/* Execute the existing C command parser and capture its real output. */
static int execute_dsa_command(const char *command, char *output, size_t out_size) {
    FILE *capture = tmpfile();
    if (!capture) return 0;

    fflush(stdout);
    int saved_stdout = _dup(_fileno(stdout));
    if (saved_stdout < 0 || _dup2(_fileno(capture), _fileno(stdout)) != 0) {
        if (saved_stdout >= 0) _close(saved_stdout);
        fclose(capture);
        return 0;
    }

    run_command(command);
    fflush(stdout);

    _dup2(saved_stdout, _fileno(stdout));
    _close(saved_stdout);

    rewind(capture);
    size_t n = fread(output, 1, out_size - 1, capture);
    output[n] = '\0';
    fclose(capture);
    return 1;
}


#define MAX_BLOCK_PAIRS 1024
typedef struct {
    char owner[NAME_LEN];
    char target[NAME_LEN];
} BlockPair;
static BlockPair block_pairs[MAX_BLOCK_PAIRS];
static int block_pair_count = 0;

static int blocked_by(const char *owner, const char *target) {
    char a[NAME_LEN], b[NAME_LEN];
    lower_copy(a, owner, sizeof a);
    lower_copy(b, target, sizeof b);
    for (int i = 0; i < block_pair_count; i++)
        if (strcmp(block_pairs[i].owner, a) == 0 &&
            strcmp(block_pairs[i].target, b) == 0) return 1;
    return 0;
}
static int add_block(const char *owner, const char *target) {
    char a[NAME_LEN], b[NAME_LEN];
    lower_copy(a, owner, sizeof a);
    lower_copy(b, target, sizeof b);
    if (blocked_by(a, b)) return 1;
    if (block_pair_count >= MAX_BLOCK_PAIRS) return 0;
    strncpy(block_pairs[block_pair_count].owner, a, NAME_LEN-1);
    strncpy(block_pairs[block_pair_count].target, b, NAME_LEN-1);
    block_pair_count++;
    return 1;
}
static int remove_block(const char *owner, const char *target) {
    char a[NAME_LEN], b[NAME_LEN];
    lower_copy(a, owner, sizeof a);
    lower_copy(b, target, sizeof b);
    for (int i = 0; i < block_pair_count; i++) {
        if (strcmp(block_pairs[i].owner, a) == 0 &&
            strcmp(block_pairs[i].target, b) == 0) {
            block_pairs[i] = block_pairs[--block_pair_count];
            return 1;
        }
    }
    return 0;
}
static void handle_block_action(SOCKET client, const char *body, int block) {
    char target[NAME_LEN] = {0};
    if (!cur) {
        send_response(client, 401, "Unauthorized", "application/json",
                     "{\"success\":false,\"message\":\"Please log in first.\"}");
        return;
    }
    if (!json_string(body, "target", target, sizeof target) || !hash_find(target) ||
        _stricmp(cur->name, target) == 0) {
        send_response(client, 400, "Bad Request", "application/json",
                     "{\"success\":false,\"message\":\"Choose a valid existing user.\"}");
        return;
    }
    if (block) {
        if (!add_block(cur->name, target)) {
            send_response(client, 503, "Unavailable", "application/json",
                         "{\"success\":false,\"message\":\"Block list is full.\"}");
            return;
        }
        send_response(client, 200, "OK", "application/json",
                     "{\"success\":true,\"blocked\":true}");
    } else {
        remove_block(cur->name, target);
        send_response(client, 200, "OK", "application/json",
                     "{\"success\":true,\"blocked\":false}");
    }
}
static void handle_block_status(SOCKET client, const char *body) {
    char target[NAME_LEN] = {0}, response[128];
    if (!cur || !json_string(body, "target", target, sizeof target)) {
        send_response(client, 401, "Unauthorized", "application/json",
                     "{\"success\":false,\"blocked\":false}");
        return;
    }
    snprintf(response, sizeof response, "{\"success\":true,\"blocked\":%s}",
             blocked_by(cur->name, target) ? "true" : "false");
    send_response(client, 200, "OK", "application/json", response);
}
static int is_blocked_chat_send(const char *command) {
    if (!cur || strncmp(command, "send ", 5) != 0) return 0;
    char target[NAME_LEN] = {0};
    const char *p = command + 5;
    size_t n = 0;
    while (*p && !isspace((unsigned char)*p) && n + 1 < sizeof target)
        target[n++] = *p++;
    target[n] = '\0';
    if (!target[0]) return 0;
    return blocked_by(cur->name, target) || blocked_by(target, cur->name);
}

int main(void) {
    WSADATA wsa;
    if (WSAStartup(MAKEWORD(2, 2), &wsa) != 0) {
        puts("Winsock startup failed."); return 1;
    }

    /* Same initialization used by the original command-line main(). */
    trie_root = trie_new();
    ban_word("spam"); ban_word("scam");
    ban_word("stupid"); ban_word("idiot");

    SOCKET server = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (server == INVALID_SOCKET) {
        puts("Could not create server socket."); WSACleanup(); return 1;
    }

    struct sockaddr_in address;
    memset(&address, 0, sizeof(address));
    address.sin_family = AF_INET;
    address.sin_addr.s_addr = htonl(INADDR_ANY);
    address.sin_port = htons(PORT);

    if (bind(server, (struct sockaddr *)&address, sizeof(address)) == SOCKET_ERROR) {
        printf("Could not bind port %d. Close any other server using this port.\n", PORT);
        closesocket(server); WSACleanup(); return 1;
    }
    if (listen(server, 8) == SOCKET_ERROR) {
        puts("Could not listen."); closesocket(server); WSACleanup(); return 1;
    }

    printf("\nORBIT CHAT — C DATA STRUCTURES BACKEND\n");
    printf("Server running at http://localhost:%d\n", PORT);
    printf("Keep this terminal open while using the app.\n");

    for (;;) {
        SOCKET client = accept(server, NULL, NULL);
        if (client == INVALID_SOCKET) continue;

        char request[BUFFER_SIZE];
        if (receive_request(client, request, sizeof(request))) {
            if (strncmp(request, "OPTIONS ", 8) == 0) {
                send_response(client, 200, "OK", "application/json", "{}");
            } else if (strncmp(request, "GET /api/health", 15) == 0) {
                send_response(client, 200, "OK", "application/json",
                    "{\"status\":\"online\",\"backend\":\"C\",\"project\":\"Orbit Chat\"}");
            } else if (strncmp(request, "POST /api/auth/register", 23) == 0) {
                char *body = strstr(request, "\r\n\r\n");
                if (body) handle_auth_register(client, body + 4);
                else send_auth_result(client, 400, "Bad Request", 0, "Missing request body.");
            } else if (strncmp(request, "POST /api/auth/login", 20) == 0) {
                char *body = strstr(request, "\r\n\r\n");
                if (body) handle_auth_login(client, body + 4);
                else send_auth_result(client, 400, "Bad Request", 0, "Missing request body.");
            } else if (strncmp(request, "POST /api/auth/logout", 21) == 0) {
                cur = NULL;
                send_auth_result(client, 200, "OK", 1, "You have been logged out.");
            } else if (strncmp(request, "POST /api/block/status", 22) == 0) {
                char *body = strstr(request, "\r\n\r\n");
                if (body) handle_block_status(client, body + 4);
                else send_response(client, 400, "Bad Request", "application/json",
                    "{\"success\":false,\"blocked\":false}");
            } else if (strncmp(request, "POST /api/block", 15) == 0) {
                char *body = strstr(request, "\r\n\r\n");
                if (body) handle_block_action(client, body + 4, 1);
                else send_response(client, 400, "Bad Request", "application/json",
                    "{\"success\":false,\"message\":\"Missing body\"}");
            } else if (strncmp(request, "POST /api/unblock", 17) == 0) {
                char *body = strstr(request, "\r\n\r\n");
                if (body) handle_block_action(client, body + 4, 0);
                else send_response(client, 400, "Bad Request", "application/json",
                    "{\"success\":false,\"message\":\"Missing body\"}");
            } else if (strncmp(request, "POST /api/command", 17) == 0) {
                char *body = strstr(request, "\r\n\r\n");
                char command[512] = {0};
                char result[OUTPUT_SIZE] = {0};
                char escaped[OUTPUT_SIZE * 2] = {0};
                char response[OUTPUT_SIZE * 2 + 128];

                if (!body || !json_string(body + 4, "command", command, sizeof(command))) {
                    send_response(client, 400, "Bad Request", "application/json",
                        "{\"success\":false,\"output\":\"Missing command\"}");
                } else if (is_blocked_chat_send(command)) {
                    send_response(client, 403, "Forbidden", "application/json",
                        "{\"success\":false,\"output\":\"Message not sent: this conversation is blocked.\"}");
                } else if (!execute_dsa_command(command, result, sizeof(result))) {
                    send_response(client, 500, "Internal Server Error", "application/json",
                        "{\"success\":false,\"output\":\"Could not capture C command output\"}");
                } else {
                    json_escape(result, escaped, sizeof(escaped));
                    snprintf(response, sizeof(response),
                        "{\"success\":true,\"output\":\"%s\"}", escaped);
                    send_response(client, 200, "OK", "application/json", response);
                    printf("C command executed: %.100s\n", command);
                }
            } else {
                send_response(client, 404, "Not Found", "application/json",
                    "{\"success\":false,\"output\":\"Unknown endpoint\"}");
            }
        }
        closesocket(client);
    }
    closesocket(server);
    WSACleanup();
    return 0;
}
