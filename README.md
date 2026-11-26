# Orbit — Real-Time Chat System

Orbit is a chat-style web interface connected to the original C chat application. The frontend is built with HTML, CSS and JavaScript; the C program remains responsible for the application's existing user, messaging and data-structure logic.

## Project structure

```text
orbit-chat/
├── backend/
│   ├── chat_dsa.c
│   └── server.c
├── frontend/
│   ├── index.html
│   ├── style.css
│   └── script.js
├── .gitignore
└── README.md
```

## Run locally (Windows + MinGW GCC)

1. Open a terminal in the `backend` folder.
2. Compile the server:

   ```powershell
   gcc -Wall -Wextra -std=c99 server.c -o server.exe -lws2_32 -lbcrypt
   ```

3. Start it:

   ```powershell
   .\server.exe
   ```

4. Keep the server terminal open and open `frontend/index.html` in a browser.

The interface talks to the local server at `http://localhost:8080`.

## Notes

- The original `chat_dsa.c` source is included as supplied; the browser interface does not reimplement its data-structure logic.
- Accounts use PBKDF2-HMAC-SHA256 password hashes (Windows CNG); plaintext passwords are not stored. Account credentials and chat data are held in memory and reset when the server process is stopped.
- This is a local academic demonstration, not a production deployment. Do not expose the server directly to the public internet.


## Blocking contacts
Open a direct conversation and use the **Block** button in the chat header. Confirm to block; the button changes to **Unblock**. A blocked contact cannot send messages to you, and you cannot send messages to them. Blocking is enforced by the HTTP bridge before the existing C command parser is called. The original `chat_dsa.c` file is preserved unchanged. Block records are held in server memory and reset when the server restarts.


## Blocking contacts
- Log in and open a contact from Direct Messages.
- The chat header shows a Block button.
- Block/unblock is confirmed, enforced by the C backend, and message sends are rejected if either side has blocked the other.
- Block lists are held in server memory and reset when the server restarts.
