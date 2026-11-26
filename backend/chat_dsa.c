/*
 * ======================================================================
 *  REAL-TIME CHAT SYSTEM v2  -  Data Structures & Algorithms Project (C)
 * ======================================================================
 *  A terminal chat "server" where every feature is powered by a classic
 *  data structure or algorithm.
 *
 *    Feature                        Data structure / algorithm
 *    -----------------------------  -----------------------------------
 *    User lookup / login            Hash table (chaining)        O(1)
 *    Username autocomplete          Trie                         O(L)
 *    Message delivery order         Max-heap priority queue      O(log n)
 *    Per-user inbox                 Queue (linked list)          O(1)
 *    Chat history                   Doubly linked list           O(1) delete
 *    Undo / unsend                  Stack                        O(1)
 *    Friend network                 Weighted graph (adj. list)
 *    Fewest hops between users      BFS                          O(V+E)
 *    Strongest friend connection    Dijkstra + min-heap          O(E log V)
 *    Friend communities             Union-Find (DSU)             O(a(n))
 *    People you may know            Graph traversal (depth 2)
 *    Keyword search                 KMP string matching          O(n+m)
 *    Activity leaderboard           Merge sort                   O(n log n)
 *  --- new in v2 ---------------------------------------------------
 *    Time-indexed message store     AVL tree (self-balancing BST)
 *    Messages in a time range       AVL range query              O(log n + k)
 *    Recent chats list              LRU cache (map + linked list) O(1)
 *    Group chat rooms               Hash table + circular buffer  O(1)
 *    Message-id index (disk style)  B-tree (min degree 2)         O(log n)
 *    Profanity / spam filter        Aho-Corasick automaton       O(n + hits)
 *    History compression stats      Huffman coding (greedy + heap)
 *
 *  Build :  gcc -Wall -Wextra -std=c99 -o chat chat_dsa.c
 *  Run   :  ./chat        then type  demo   (or  help)
 * ======================================================================
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAX_USERS    64
#define NAME_LEN     32
#define MSG_LEN      256
#define HASH_SIZE    31
#define HEAP_MAX     512
#define UNDO_MAX     16
#define LRU_CAP      3
#define RING_CAP     5
#define MH_MAX       4096
#define INF          1000000000L
#define AC_MAX       512
#define MAX_BANNED   16
#define BANNED_LEN   16

/* ----------------------------------------------------------------------
 *  CORE TYPES
 * -------------------------------------------------------------------- */

typedef struct Message {
    int    id;
    int    from;            /* sender user id                    */
    int    to;              /* receiver user id, -1 = broadcast  */
    int    priority;        /* 0 = normal, 2 = urgent            */
    int    deleted;         /* set by undo (unsend)              */
    long   ts;              /* logical timestamp (AVL key)       */
    char   text[MSG_LEN];
    struct Message *prev, *next;   /* history: doubly linked list */
} Message;

typedef struct QNode { Message *m; struct QNode *next; } QNode;
typedef struct { QNode *front, *rear; int size; } Queue;

typedef struct Friend {                 /* weighted graph edge */
    int id;
    int w;                              /* 1 = best friends ... 9 = distant */
    struct Friend *next;
} Friend;

typedef struct LNode {                  /* LRU cache node */
    int partner;
    struct LNode *prev, *next;
} LNode;

typedef struct {                        /* LRU cache: direct map + DLL */
    LNode *head, *tail;                 /* head = most recently used */
    LNode *map[MAX_USERS];
    int size;
} LRU;

typedef struct User {
    int  id;
    char name[NAME_LEN];
    char key[NAME_LEN];                 /* lowercase name = hash/trie key  */
    int  sent;
    Queue inbox;                        /* QUEUE                           */
    Message *undo[UNDO_MAX];            /* STACK                           */
    int undo_top;
    Friend *friends;                    /* GRAPH adjacency list            */
    LRU recent;                         /* LRU CACHE of recent chats       */
} User;

typedef struct HNode { User *user; struct HNode *next; } HNode;

typedef struct TrieNode {
    struct TrieNode *c[128];
    User *user;
} TrieNode;

typedef struct AVL {                    /* AVL tree node */
    long key;                           /* message timestamp */
    Message *m;
    int height;
    struct AVL *l, *r;
} AVL;

#define BT_T 2                          /* B-tree minimum degree t        */
                                        /* each node: t-1 .. 2t-1 keys    */
typedef struct BNode {                  /* B-tree node */
    int n;                              /* number of keys stored */
    int leaf;
    long key[2 * BT_T - 1];             /* message ids, sorted   */
    Message *val[2 * BT_T - 1];
    struct BNode *child[2 * BT_T];
} BNode;

typedef struct Room {                   /* group chat room */
    char name[NAME_LEN], key[NAME_LEN];
    char member[MAX_USERS];
    int  nmembers;
    Message *ring[RING_CAP];            /* CIRCULAR BUFFER of last msgs */
    int head, count;
    struct Room *next;                  /* chaining in room hash table */
} Room;

typedef struct { long key; int v; void *p; } MHItem;   /* generic min-heap */
typedef struct { MHItem a[MH_MAX]; int n; } MinHeap;

typedef struct HuffNode {
    int ch; long freq;
    struct HuffNode *l, *r;
} HuffNode;

/* ----------------------------------------------------------------------
 *  GLOBAL "SERVER" STATE
 * -------------------------------------------------------------------- */
static User     *users[MAX_USERS];
static int       user_count = 0;
static User     *cur = NULL;

static HNode    *table[HASH_SIZE];
static TrieNode *trie_root;
static Message  *hist_head, *hist_tail;
static Message  *heap[HEAP_MAX];
static int       heap_n = 0;
static int       next_msg_id = 1;
static long      tick = 0;                  /* logical clock: +1 per command */

static AVL      *avl_root = NULL;
static int       avl_count = 0;

static BNode    *bt_root = NULL;
static int       bt_count = 0;

static int       uf_parent[MAX_USERS], uf_rank[MAX_USERS];

static Room     *room_table[HASH_SIZE];
static int       room_count = 0;

static char      banned[MAX_BANNED][BANNED_LEN];
static int       banned_n = 0;
static int       ac_go[AC_MAX][128];
static int       ac_fail[AC_MAX];
static int       ac_len[AC_MAX];

/* ----------------------------------------------------------------------
 *  SMALL HELPERS
 * -------------------------------------------------------------------- */
static void lower_copy(char *dst, const char *src, size_t size) {
    size_t i = 0;
    for (; src[i] && i < size - 1; i++)
        dst[i] = (char)tolower((unsigned char)src[i]);
    dst[i] = '\0';
}

static char *ltrim(char *s) {
    while (*s == ' ' || *s == '\t') s++;
    return s;
}

static void print_msg(const Message *m) {
    const char *tag = (m->priority == 2) ? " [URGENT]" : "";
    if (m->to < 0)
        printf("  #%d t=%ld %s -> ALL%s: %s\n", m->id, m->ts,
               users[m->from]->name, tag, m->text);
    else
        printf("  #%d t=%ld %s -> %s%s: %s\n", m->id, m->ts,
               users[m->from]->name, users[m->to]->name, tag, m->text);
}

static int visible_to(const Message *m, const User *u) {
    return m->to < 0 || m->from == u->id || m->to == u->id;
}

/* ======================================================================
 *  GENERIC MIN-HEAP  (used by Dijkstra and Huffman)
 * ==================================================================== */
static void mh_push(MinHeap *h, long key, int v, void *p) {
    if (h->n == MH_MAX) return;
    int i = h->n++;
    h->a[i].key = key; h->a[i].v = v; h->a[i].p = p;
    while (i > 0) {
        int par = (i - 1) / 2;
        if (h->a[par].key <= h->a[i].key) break;
        MHItem t = h->a[par]; h->a[par] = h->a[i]; h->a[i] = t;
        i = par;
    }
}

static MHItem mh_pop(MinHeap *h) {
    MHItem top = h->a[0];
    h->a[0] = h->a[--h->n];
    int i = 0;
    for (;;) {
        int l = 2 * i + 1, r = l + 1, s = i;
        if (l < h->n && h->a[l].key < h->a[s].key) s = l;
        if (r < h->n && h->a[r].key < h->a[s].key) s = r;
        if (s == i) break;
        MHItem t = h->a[s]; h->a[s] = h->a[i]; h->a[i] = t;
        i = s;
    }
    return top;
}

/* ======================================================================
 *  1. HASH TABLE  -  username -> User*
 * ==================================================================== */
static unsigned hash_str(const char *s) {          /* djb2 */
    unsigned h = 5381;
    while (*s) h = h * 33 + (unsigned char)*s++;
    return h % HASH_SIZE;
}

static void hash_insert(User *u) {
    unsigned b = hash_str(u->key);
    HNode *n = malloc(sizeof *n);
    n->user = u;
    n->next = table[b];
    table[b] = n;
}

static User *hash_find(const char *name) {
    char key[NAME_LEN];
    lower_copy(key, name, sizeof key);
    for (HNode *n = table[hash_str(key)]; n; n = n->next)
        if (strcmp(n->user->key, key) == 0) return n->user;
    return NULL;
}

static void hash_print(void) {
    puts("Hash table (bucket -> chain):");
    for (int i = 0; i < HASH_SIZE; i++) {
        if (!table[i]) continue;
        printf("  [%2d]", i);
        for (HNode *n = table[i]; n; n = n->next)
            printf(" -> %s", n->user->name);
        putchar('\n');
    }
}

/* ======================================================================
 *  2. TRIE  -  username autocomplete
 * ==================================================================== */
static TrieNode *trie_new(void) { return calloc(1, sizeof(TrieNode)); }

static void trie_insert(const char *key, User *u) {
    TrieNode *n = trie_root;
    for (; *key; key++) {
        int i = (unsigned char)*key & 127;
        if (!n->c[i]) n->c[i] = trie_new();
        n = n->c[i];
    }
    n->user = u;
}

static void trie_collect(TrieNode *n, int *count) {
    if (n->user) { printf("   - %s\n", n->user->name); (*count)++; }
    for (int i = 0; i < 128; i++)
        if (n->c[i]) trie_collect(n->c[i], count);
}

static void trie_autocomplete(const char *prefix) {
    char key[NAME_LEN];
    lower_copy(key, prefix, sizeof key);
    TrieNode *n = trie_root;
    for (const char *p = key; *p && n; p++)
        n = n->c[(unsigned char)*p & 127];
    int count = 0;
    if (n) trie_collect(n, &count);
    if (!count) puts("   (no users match)");
}

/* ======================================================================
 *  3. QUEUE  -  per-user inbox
 * ==================================================================== */
static void q_push(Queue *q, Message *m) {
    QNode *n = malloc(sizeof *n);
    n->m = m; n->next = NULL;
    if (q->rear) q->rear->next = n; else q->front = n;
    q->rear = n;
    q->size++;
}

static Message *q_pop(Queue *q) {
    if (!q->front) return NULL;
    QNode *n = q->front;
    Message *m = n->m;
    q->front = n->next;
    if (!q->front) q->rear = NULL;
    free(n);
    q->size--;
    return m;
}

/* ======================================================================
 *  4. MAX-HEAP  -  server delivery queue
 * ==================================================================== */
static int higher(const Message *a, const Message *b) {
    if (a->priority != b->priority) return a->priority > b->priority;
    return a->id < b->id;
}

static int heap_push(Message *m) {
    if (heap_n == HEAP_MAX) return 0;
    int i = heap_n++;
    heap[i] = m;
    while (i > 0) {
        int p = (i - 1) / 2;
        if (!higher(heap[i], heap[p])) break;
        Message *t = heap[i]; heap[i] = heap[p]; heap[p] = t;
        i = p;
    }
    return 1;
}

static Message *heap_pop(void) {
    if (!heap_n) return NULL;
    Message *top = heap[0];
    heap[0] = heap[--heap_n];
    int i = 0;
    for (;;) {
        int l = 2 * i + 1, r = l + 1, b = i;
        if (l < heap_n && higher(heap[l], heap[b])) b = l;
        if (r < heap_n && higher(heap[r], heap[b])) b = r;
        if (b == i) break;
        Message *t = heap[i]; heap[i] = heap[b]; heap[b] = t;
        i = b;
    }
    return top;
}

/* ======================================================================
 *  5. DOUBLY LINKED LIST  -  chat history
 * ==================================================================== */
static void hist_append(Message *m) {
    m->prev = hist_tail; m->next = NULL;
    if (hist_tail) hist_tail->next = m; else hist_head = m;
    hist_tail = m;
}

static void hist_unlink(Message *m) {
    if (m->prev) m->prev->next = m->next; else hist_head = m->next;
    if (m->next) m->next->prev = m->prev; else hist_tail = m->prev;
    m->prev = m->next = NULL;
}

/* ======================================================================
 *  6. AVL TREE  -  messages indexed by timestamp (self-balancing BST)
 * ==================================================================== */
static int avl_h(const AVL *n) { return n ? n->height : 0; }

static void avl_update(AVL *n) {
    int l = avl_h(n->l), r = avl_h(n->r);
    n->height = 1 + (l > r ? l : r);
}

static AVL *rot_right(AVL *y) {
    AVL *x = y->l;
    y->l = x->r;
    x->r = y;
    avl_update(y); avl_update(x);
    return x;
}

static AVL *rot_left(AVL *x) {
    AVL *y = x->r;
    x->r = y->l;
    y->l = x;
    avl_update(x); avl_update(y);
    return y;
}

static AVL *avl_rebalance(AVL *n) {
    avl_update(n);
    int b = avl_h(n->l) - avl_h(n->r);
    if (b > 1) {                                   /* left heavy  */
        if (avl_h(n->l->l) < avl_h(n->l->r)) n->l = rot_left(n->l);   /* LR */
        return rot_right(n);                       /* LL */
    }
    if (b < -1) {                                  /* right heavy */
        if (avl_h(n->r->r) < avl_h(n->r->l)) n->r = rot_right(n->r);  /* RL */
        return rot_left(n);                        /* RR */
    }
    return n;
}

static AVL *avl_insert(AVL *n, long key, Message *m) {
    if (!n) {
        AVL *x = calloc(1, sizeof *x);
        x->key = key; x->m = m; x->height = 1;
        avl_count++;
        return x;
    }
    if (key < n->key) n->l = avl_insert(n->l, key, m);
    else              n->r = avl_insert(n->r, key, m);
    return avl_rebalance(n);
}

static AVL *avl_delete(AVL *n, long key) {
    if (!n) return NULL;
    if (key < n->key)      n->l = avl_delete(n->l, key);
    else if (key > n->key) n->r = avl_delete(n->r, key);
    else {
        if (!n->l || !n->r) {                      /* 0 or 1 child */
            AVL *child = n->l ? n->l : n->r;
            free(n);
            avl_count--;
            return child;
        }
        AVL *s = n->r;                             /* in-order successor */
        while (s->l) s = s->l;
        n->key = s->key; n->m = s->m;
        n->r = avl_delete(n->r, s->key);
    }
    return avl_rebalance(n);
}

/* range query: only visits subtrees that can contain keys in [lo, hi] */
static int avl_range(const AVL *n, long lo, long hi) {
    int c = 0;
    if (!n) return 0;
    if (lo < n->key) c += avl_range(n->l, lo, hi);
    if (lo <= n->key && n->key <= hi && visible_to(n->m, cur)) {
        print_msg(n->m);
        c++;
    }
    if (hi > n->key) c += avl_range(n->r, lo, hi);
    return c;
}

static void avl_print(const AVL *n, int depth) {   /* sideways view */
    if (!n) return;
    avl_print(n->r, depth + 1);
    printf("%*s[t=%ld  h=%d]\n", depth * 7, "", n->key, n->height);
    avl_print(n->l, depth + 1);
}

/* ======================================================================
 *  6b. B-TREE  -  message-id index (the structure databases use on disk)
 *      Every node holds many keys, so the tree is very shallow and a
 *      search touches few nodes (= few disk pages). Minimum degree t:
 *      every node except the root has t-1 .. 2t-1 keys.
 *      Insert: split full nodes on the way down.
 *      Delete: borrow from a sibling or merge nodes on the way down.
 * ==================================================================== */
static BNode *bt_new(int leaf) {
    BNode *x = calloc(1, sizeof *x);
    x->leaf = leaf;
    return x;
}

static Message *bt_search(const BNode *x, long k, int *visited) {
    while (x) {
        (*visited)++;                               /* one "page read" */
        int i = 0;
        while (i < x->n && k > x->key[i]) i++;
        if (i < x->n && k == x->key[i]) return x->val[i];
        if (x->leaf) return NULL;
        x = x->child[i];
    }
    return NULL;
}

static int bt_height(const BNode *x) {
    int h = 0;
    while (x) { h++; x = x->leaf ? NULL : x->child[0]; }
    return h;
}

/* ---- insertion ---- */
static void bt_split_child(BNode *x, int i) {       /* x->child[i] is full */
    BNode *y = x->child[i];
    BNode *z = bt_new(y->leaf);
    z->n = BT_T - 1;
    for (int j = 0; j < BT_T - 1; j++) {
        z->key[j] = y->key[j + BT_T];
        z->val[j] = y->val[j + BT_T];
    }
    if (!y->leaf)
        for (int j = 0; j < BT_T; j++) z->child[j] = y->child[j + BT_T];
    for (int j = x->n; j >= i + 1; j--) x->child[j + 1] = x->child[j];
    x->child[i + 1] = z;
    for (int j = x->n - 1; j >= i; j--) {
        x->key[j + 1] = x->key[j];
        x->val[j + 1] = x->val[j];
    }
    x->key[i] = y->key[BT_T - 1];                   /* median moves up */
    x->val[i] = y->val[BT_T - 1];
    y->n = BT_T - 1;
    x->n++;
}

static void bt_insert_nonfull(BNode *x, long k, Message *m) {
    int i = x->n - 1;
    if (x->leaf) {
        while (i >= 0 && k < x->key[i]) {
            x->key[i + 1] = x->key[i];
            x->val[i + 1] = x->val[i];
            i--;
        }
        x->key[i + 1] = k;
        x->val[i + 1] = m;
        x->n++;
    } else {
        while (i >= 0 && k < x->key[i]) i--;
        i++;
        if (x->child[i]->n == 2 * BT_T - 1) {
            bt_split_child(x, i);
            if (k > x->key[i]) i++;
        }
        bt_insert_nonfull(x->child[i], k, m);
    }
}

static void bt_insert(long k, Message *m) {
    if (!bt_root) bt_root = bt_new(1);
    if (bt_root->n == 2 * BT_T - 1) {               /* root full: tree grows */
        BNode *s = bt_new(0);
        s->child[0] = bt_root;
        bt_root = s;
        bt_split_child(s, 0);
    }
    bt_insert_nonfull(bt_root, k, m);
    bt_count++;
}

/* ---- deletion ---- */
static void bt_merge(BNode *x, int idx) {           /* merge child idx+1 into idx */
    BNode *c = x->child[idx], *s = x->child[idx + 1];
    c->key[BT_T - 1] = x->key[idx];                 /* pull separator down */
    c->val[BT_T - 1] = x->val[idx];
    for (int i = 0; i < s->n; i++) {
        c->key[i + BT_T] = s->key[i];
        c->val[i + BT_T] = s->val[i];
    }
    if (!c->leaf)
        for (int i = 0; i <= s->n; i++) c->child[i + BT_T] = s->child[i];
    for (int i = idx + 1; i < x->n; i++) {
        x->key[i - 1] = x->key[i];
        x->val[i - 1] = x->val[i];
    }
    for (int i = idx + 2; i <= x->n; i++) x->child[i - 1] = x->child[i];
    c->n += s->n + 1;
    x->n--;
    free(s);
}

static void bt_borrow_prev(BNode *x, int idx) {     /* rotate right */
    BNode *c = x->child[idx], *s = x->child[idx - 1];
    for (int i = c->n - 1; i >= 0; i--) {
        c->key[i + 1] = c->key[i];
        c->val[i + 1] = c->val[i];
    }
    if (!c->leaf)
        for (int i = c->n; i >= 0; i--) c->child[i + 1] = c->child[i];
    c->key[0] = x->key[idx - 1];
    c->val[0] = x->val[idx - 1];
    if (!c->leaf) c->child[0] = s->child[s->n];
    x->key[idx - 1] = s->key[s->n - 1];
    x->val[idx - 1] = s->val[s->n - 1];
    c->n++;
    s->n--;
}

static void bt_borrow_next(BNode *x, int idx) {     /* rotate left */
    BNode *c = x->child[idx], *s = x->child[idx + 1];
    c->key[c->n] = x->key[idx];
    c->val[c->n] = x->val[idx];
    if (!c->leaf) c->child[c->n + 1] = s->child[0];
    x->key[idx] = s->key[0];
    x->val[idx] = s->val[0];
    for (int i = 1; i < s->n; i++) {
        s->key[i - 1] = s->key[i];
        s->val[i - 1] = s->val[i];
    }
    if (!s->leaf)
        for (int i = 1; i <= s->n; i++) s->child[i - 1] = s->child[i];
    c->n++;
    s->n--;
}

static void bt_fill(BNode *x, int idx) {            /* child idx has too few keys */
    if (idx != 0 && x->child[idx - 1]->n >= BT_T)        bt_borrow_prev(x, idx);
    else if (idx != x->n && x->child[idx + 1]->n >= BT_T) bt_borrow_next(x, idx);
    else if (idx != x->n)                                 bt_merge(x, idx);
    else                                                  bt_merge(x, idx - 1);
}

static void bt_remove(BNode *x, long k) {
    int idx = 0;
    while (idx < x->n && x->key[idx] < k) idx++;
    if (idx < x->n && x->key[idx] == k) {
        if (x->leaf) {                              /* case 1: key in a leaf */
            for (int i = idx + 1; i < x->n; i++) {
                x->key[i - 1] = x->key[i];
                x->val[i - 1] = x->val[i];
            }
            x->n--;
        } else if (x->child[idx]->n >= BT_T) {      /* case 2a: predecessor */
            BNode *p = x->child[idx];
            while (!p->leaf) p = p->child[p->n];
            x->key[idx] = p->key[p->n - 1];
            x->val[idx] = p->val[p->n - 1];
            bt_remove(x->child[idx], x->key[idx]);
        } else if (x->child[idx + 1]->n >= BT_T) {  /* case 2b: successor */
            BNode *s = x->child[idx + 1];
            while (!s->leaf) s = s->child[0];
            x->key[idx] = s->key[0];
            x->val[idx] = s->val[0];
            bt_remove(x->child[idx + 1], x->key[idx]);
        } else {                                    /* case 2c: merge */
            bt_merge(x, idx);
            bt_remove(x->child[idx], k);
        }
    } else {
        if (x->leaf) return;                        /* not in tree */
        int last = (idx == x->n);
        if (x->child[idx]->n < BT_T) bt_fill(x, idx);    /* case 3 */
        if (last && idx > x->n) bt_remove(x->child[idx - 1], k);
        else                    bt_remove(x->child[idx], k);
    }
}

static void bt_delete(long k) {
    int visited = 0;
    if (!bt_root || !bt_search(bt_root, k, &visited)) return;
    bt_remove(bt_root, k);
    bt_count--;
    if (bt_root->n == 0) {                          /* tree shrinks */
        BNode *old = bt_root;
        bt_root = old->leaf ? NULL : old->child[0];
        free(old);
    }
}

static void bt_print(const BNode *x, int depth) {
    if (!x) return;
    printf("%*s[", depth * 4, "");
    for (int i = 0; i < x->n; i++) printf("%s#%ld", i ? " | " : "", x->key[i]);
    printf("]%s\n", x->leaf ? "  (leaf)" : "");
    if (!x->leaf)
        for (int i = 0; i <= x->n; i++) bt_print(x->child[i], depth + 1);
}

/* ======================================================================
 *  7. LRU CACHE  -  recent conversations (direct map + doubly linked list)
 * ==================================================================== */
static void lru_unlink(LRU *c, LNode *n) {
    if (n->prev) n->prev->next = n->next; else c->head = n->next;
    if (n->next) n->next->prev = n->prev; else c->tail = n->prev;
    n->prev = n->next = NULL;
}

static void lru_push_front(LRU *c, LNode *n) {
    n->prev = NULL;
    n->next = c->head;
    if (c->head) c->head->prev = n;
    c->head = n;
    if (!c->tail) c->tail = n;
}

static void lru_touch(LRU *c, int partner) {
    LNode *n = c->map[partner];
    if (n) {                                        /* hit: move to front */
        lru_unlink(c, n);
        lru_push_front(c, n);
        return;
    }
    if (c->size == LRU_CAP) {                       /* full: evict LRU */
        LNode *old = c->tail;
        printf("  (recent-chats cache full: evicted %s)\n",
               users[old->partner]->name);
        lru_unlink(c, old);
        c->map[old->partner] = NULL;
        free(old);
        c->size--;
    }
    n = calloc(1, sizeof *n);
    n->partner = partner;
    c->map[partner] = n;
    lru_push_front(c, n);
    c->size++;
}

static void show_recent(User *u) {
    printf("Recent chats of %s (most recent first, capacity %d):\n",
           u->name, LRU_CAP);
    if (!u->recent.size) { puts("   (none)"); return; }
    for (LNode *n = u->recent.head; n; n = n->next)
        printf("   - %s\n", users[n->partner]->name);
}

/* ======================================================================
 *  8. GRAPH: BFS, Dijkstra, Union-Find
 * ==================================================================== */
static int uf_find(int x) {                         /* path halving */
    while (uf_parent[x] != x) {
        uf_parent[x] = uf_parent[uf_parent[x]];
        x = uf_parent[x];
    }
    return x;
}

static void uf_union(int a, int b) {                /* union by rank */
    a = uf_find(a); b = uf_find(b);
    if (a == b) return;
    if (uf_rank[a] < uf_rank[b]) { int t = a; a = b; b = t; }
    uf_parent[b] = a;
    if (uf_rank[a] == uf_rank[b]) uf_rank[a]++;
}

static int is_friend(int a, int b) {
    for (Friend *f = users[a]->friends; f; f = f->next)
        if (f->id == b) return 1;
    return 0;
}

static void add_edge(int a, int b, int w) {
    Friend *f = malloc(sizeof *f);
    f->id = b; f->w = w; f->next = users[a]->friends;
    users[a]->friends = f;
}

static void add_friend(User *a, User *b, int w) {
    if (a == b) { puts("You can't friend yourself."); return; }
    if (w < 1 || w > 9) { puts("Weight must be 1 (closest) to 9."); return; }
    if (is_friend(a->id, b->id)) { puts("Already friends."); return; }
    add_edge(a->id, b->id, w);                      /* undirected graph */
    add_edge(b->id, a->id, w);
    uf_union(a->id, b->id);
    printf("%s and %s are now friends (distance %d).\n", a->name, b->name, w);
}

static void print_path(const int *parent, int dst) {
    int path[MAX_USERS], len = 0;
    for (int v = dst; v != -1; v = parent[v]) path[len++] = v;
    for (int i = len - 1; i >= 0; i--)
        printf("%s%s", users[path[i]]->name, i ? " -> " : "\n");
}

static void bfs_path(User *src, User *dst) {
    int parent[MAX_USERS], visited[MAX_USERS] = {0}, q[MAX_USERS];
    int head = 0, tail = 0;
    for (int i = 0; i < MAX_USERS; i++) parent[i] = -1;
    visited[src->id] = 1;
    q[tail++] = src->id;
    while (head < tail) {
        int u = q[head++];
        if (u == dst->id) break;
        for (Friend *f = users[u]->friends; f; f = f->next)
            if (!visited[f->id]) {
                visited[f->id] = 1;
                parent[f->id] = u;
                q[tail++] = f->id;
            }
    }
    if (!visited[dst->id]) { puts("No connection between these users."); return; }
    int hops = 0;
    for (int v = dst->id; parent[v] != -1; v = parent[v]) hops++;
    printf("Fewest hops (BFS, %d hop%s): ", hops, hops == 1 ? "" : "s");
    print_path(parent, dst->id);
}

static void bond_path(User *src, User *dst) {       /* Dijkstra */
    static MinHeap mh;
    long dist[MAX_USERS];
    int parent[MAX_USERS], done[MAX_USERS];
    for (int i = 0; i < MAX_USERS; i++) { dist[i] = INF; parent[i] = -1; done[i] = 0; }
    mh.n = 0;
    dist[src->id] = 0;
    mh_push(&mh, 0, src->id, NULL);
    while (mh.n) {
        int u = mh_pop(&mh).v;
        if (done[u]) continue;
        done[u] = 1;
        for (Friend *f = users[u]->friends; f; f = f->next)
            if (!done[f->id] && dist[u] + f->w < dist[f->id]) {
                dist[f->id] = dist[u] + f->w;
                parent[f->id] = u;
                mh_push(&mh, dist[f->id], f->id, NULL);
            }
    }
    if (dist[dst->id] >= INF) { puts("No connection between these users."); return; }
    printf("Strongest bond (Dijkstra, total distance %ld): ", dist[dst->id]);
    print_path(parent, dst->id);
}

static void suggest_friends(User *u) {
    int mutual[MAX_USERS] = {0}, direct[MAX_USERS] = {0}, found = 0;
    for (Friend *f = u->friends; f; f = f->next) direct[f->id] = 1;
    for (Friend *f = u->friends; f; f = f->next)
        for (Friend *g = users[f->id]->friends; g; g = g->next)
            if (g->id != u->id && !direct[g->id]) mutual[g->id]++;
    puts("People you may know:");
    for (int i = 0; i < user_count; i++)
        if (mutual[i]) {
            printf("   - %s (%d mutual friend%s)\n", users[i]->name,
                   mutual[i], mutual[i] == 1 ? "" : "s");
            found = 1;
        }
    if (!found) puts("   (no suggestions yet)");
}

static void show_communities(void) {
    int groups = 0;
    puts("Friend communities (Union-Find):");
    for (int r = 0; r < user_count; r++) {
        if (uf_find(r) != r) continue;
        int cnt = 0;
        for (int i = 0; i < user_count; i++) if (uf_find(i) == r) cnt++;
        printf("   Group %d (%d member%s):", ++groups, cnt, cnt == 1 ? "" : "s");
        for (int i = 0; i < user_count; i++)
            if (uf_find(i) == r) printf(" %s", users[i]->name);
        putchar('\n');
    }
    if (!groups) puts("   (no users yet)");
}

/* ======================================================================
 *  9. KMP STRING SEARCH
 * ==================================================================== */
static int kmp_contains(const char *text, const char *pat) {
    int n = (int)strlen(text), m = (int)strlen(pat);
    int lps[MSG_LEN];
    if (m == 0) return 1;
    lps[0] = 0;
    for (int i = 1, len = 0; i < m;) {
        if (pat[i] == pat[len]) lps[i++] = ++len;
        else if (len)           len = lps[len - 1];
        else                    lps[i++] = 0;
    }
    for (int i = 0, j = 0; i < n;) {
        if (text[i] == pat[j]) {
            i++; j++;
            if (j == m) return 1;
        } else if (j) j = lps[j - 1];
        else i++;
    }
    return 0;
}

/* ======================================================================
 *  10. MERGE SORT
 * ==================================================================== */
static void merge_sort(User **a, User **tmp, int lo, int hi) {
    if (hi - lo < 2) return;
    int mid = (lo + hi) / 2, i = lo, j = mid, k = lo;
    merge_sort(a, tmp, lo, mid);
    merge_sort(a, tmp, mid, hi);
    while (i < mid && j < hi)
        tmp[k++] = (a[i]->sent >= a[j]->sent) ? a[i++] : a[j++];
    while (i < mid) tmp[k++] = a[i++];
    while (j < hi)  tmp[k++] = a[j++];
    for (k = lo; k < hi; k++) a[k] = tmp[k];
}

/* ======================================================================
 *  11. AHO-CORASICK  -  multi-pattern profanity / spam filter
 *      Builds a trie of banned words, adds failure links with BFS, and
 *      then scans a message once, however many words are banned.
 * ==================================================================== */
static void ac_rebuild(void) {
    int ac_n = 1;
    memset(ac_go, 0, sizeof ac_go);
    memset(ac_fail, 0, sizeof ac_fail);
    memset(ac_len, 0, sizeof ac_len);

    for (int w = 0; w < banned_n; w++) {            /* 1) build the trie */
        int s = 0;
        for (const char *p = banned[w]; *p; p++) {
            int ch = (unsigned char)*p & 127;
            if (!ac_go[s][ch]) ac_go[s][ch] = ac_n++;
            s = ac_go[s][ch];
        }
        ac_len[s] = (int)strlen(banned[w]);
    }

    int q[AC_MAX], head = 0, tail = 0;              /* 2) BFS: fail links */
    for (int ch = 0; ch < 128; ch++)
        if (ac_go[0][ch]) q[tail++] = ac_go[0][ch];
    while (head < tail) {
        int u = q[head++];
        if (ac_len[ac_fail[u]] > ac_len[u]) ac_len[u] = ac_len[ac_fail[u]];
        for (int ch = 0; ch < 128; ch++) {
            int v = ac_go[u][ch];
            if (v) {
                ac_fail[v] = ac_go[ac_fail[u]][ch];
                q[tail++] = v;
            } else {
                ac_go[u][ch] = ac_go[ac_fail[u]][ch];
            }
        }
    }
}

static int ban_word(const char *w) {
    char key[BANNED_LEN];
    size_t len = strlen(w);
    if (len < 2 || len >= BANNED_LEN) { puts("Banned word must be 2-15 characters."); return 0; }
    if (banned_n >= MAX_BANNED)       { puts("Banned-word list is full."); return 0; }
    lower_copy(key, w, sizeof key);
    for (int i = 0; i < banned_n; i++)
        if (!strcmp(banned[i], key)) { puts("Already banned."); return 0; }
    strcpy(banned[banned_n++], key);
    ac_rebuild();
    return 1;
}

/* replaces banned words with '*', returns number of matches */
static int censor(char *text) {
    int s = 0, hits = 0;
    for (int i = 0; text[i]; i++) {
        s = ac_go[s][tolower((unsigned char)text[i]) & 127];
        if (ac_len[s]) {
            for (int j = i - ac_len[s] + 1; j <= i; j++) text[j] = '*';
            hits++;
        }
    }
    return hits;
}

/* ======================================================================
 *  12. HUFFMAN CODING  -  greedy algorithm + min-heap + binary tree
 * ==================================================================== */
static char hcode[256][256];

static void huff_assign(const HuffNode *n, char *buf, int depth) {
    if (!n) return;
    if (!n->l && !n->r) {
        if (depth == 0) strcpy(hcode[n->ch], "0");
        else { memcpy(hcode[n->ch], buf, (size_t)depth); hcode[n->ch][depth] = '\0'; }
        return;
    }
    buf[depth] = '0'; huff_assign(n->l, buf, depth + 1);
    buf[depth] = '1'; huff_assign(n->r, buf, depth + 1);
}

static void huff_free(HuffNode *n) {
    if (!n) return;
    huff_free(n->l); huff_free(n->r);
    free(n);
}

static void huffman_stats(void) {
    static MinHeap mh;
    long freq[256] = {0}, total = 0;
    if (!cur) { puts("Login first."); return; }
    for (Message *m = hist_head; m; m = m->next)
        if (visible_to(m, cur))
            for (const char *p = m->text; *p; p++) { freq[(unsigned char)*p]++; total++; }
    if (!total) { puts("No messages to compress."); return; }

    mh.n = 0;
    for (int i = 0; i < 256; i++)
        if (freq[i]) {
            HuffNode *n = calloc(1, sizeof *n);
            n->ch = i; n->freq = freq[i];
            mh_push(&mh, n->freq, 0, n);
        }
    while (mh.n > 1) {                              /* merge 2 smallest */
        HuffNode *a = mh_pop(&mh).p, *b = mh_pop(&mh).p;
        HuffNode *p = calloc(1, sizeof *p);
        p->ch = -1; p->freq = a->freq + b->freq; p->l = a; p->r = b;
        mh_push(&mh, p->freq, 0, p);
    }
    HuffNode *root = mh_pop(&mh).p;

    char buf[256];
    memset(hcode, 0, sizeof hcode);
    huff_assign(root, buf, 0);

    long bits = 0;
    for (int i = 0; i < 256; i++)
        if (freq[i]) bits += freq[i] * (long)strlen(hcode[i]);

    puts("Huffman code table (10 most frequent characters):");
    int shown[256] = {0};
    for (int k = 0; k < 10; k++) {
        int best = -1;
        for (int i = 0; i < 256; i++)
            if (freq[i] && !shown[i] && (best < 0 || freq[i] > freq[best])) best = i;
        if (best < 0) break;
        shown[best] = 1;
        if (best == ' ') printf("   'SP'  freq %-3ld code %s\n", freq[best], hcode[best]);
        else             printf("   '%c'   freq %-3ld code %s\n", best, freq[best], hcode[best]);
    }
    printf("Original size : %ld bits (8 bits per character)\n", total * 8);
    printf("Huffman size  : %ld bits\n", bits);
    printf("Space saved   : %.1f%%\n", 100.0 * (double)(total * 8 - bits) / (double)(total * 8));
    huff_free(root);
}

/* ======================================================================
 *  13. GROUP ROOMS  -  hash table of rooms + circular buffer per room
 * ==================================================================== */
static Room *room_find(const char *name) {
    char key[NAME_LEN];
    lower_copy(key, name, sizeof key);
    for (Room *r = room_table[hash_str(key)]; r; r = r->next)
        if (!strcmp(r->key, key)) return r;
    return NULL;
}

static void room_create(const char *name) {
    if (!cur) { puts("Login first."); return; }
    size_t len = strlen(name);
    if (len == 0 || len >= NAME_LEN) { puts("Room name must be 1-31 characters."); return; }
    for (const char *p = name; *p; p++)
        if (!isalnum((unsigned char)*p) && *p != '_' && *p != '-') {
            puts("Use letters, digits, '-' and '_' only.");
            return;
        }
    if (room_find(name)) { puts("Room already exists."); return; }
    Room *r = calloc(1, sizeof *r);
    strncpy(r->name, name, NAME_LEN - 1);
    lower_copy(r->key, name, sizeof r->key);
    r->member[cur->id] = 1;
    r->nmembers = 1;
    unsigned b = hash_str(r->key);
    r->next = room_table[b];
    room_table[b] = r;
    room_count++;
    printf("Room '%s' created. %s joined.\n", r->name, cur->name);
}

static void room_join(const char *name) {
    if (!cur) { puts("Login first."); return; }
    Room *r = room_find(name);
    if (!r) { puts("No such room."); return; }
    if (r->member[cur->id]) { puts("Already in that room."); return; }
    r->member[cur->id] = 1;
    r->nmembers++;
    printf("%s joined room '%s' (%d member%s).\n", cur->name, r->name,
           r->nmembers, r->nmembers == 1 ? "" : "s");
}

static void ring_push(Room *r, Message *m) {
    if (r->count == RING_CAP) {                     /* overwrite the oldest */
        free(r->ring[r->head]);
        r->ring[r->head] = m;
        r->head = (r->head + 1) % RING_CAP;
    } else {
        r->ring[(r->head + r->count) % RING_CAP] = m;
        r->count++;
    }
}

static void room_say(const char *name, const char *text) {
    if (!cur) { puts("Login first."); return; }
    Room *r = room_find(name);
    if (!r) { puts("No such room."); return; }
    if (!r->member[cur->id]) { puts("Join the room first."); return; }
    if (!text || !*text) { puts("Message is empty."); return; }
    Message *m = calloc(1, sizeof *m);
    m->from = cur->id; m->to = -1; m->ts = tick;
    strncpy(m->text, text, MSG_LEN - 1);
    int hits = censor(m->text);
    int overwrote = (r->count == RING_CAP);
    ring_push(r, m);
    printf("Posted to '%s'%s%s.\n", r->name,
           hits ? " (filtered)" : "",
           overwrote ? ", oldest message dropped (ring buffer full)" : "");
}

static void room_log(const char *name) {
    Room *r = room_find(name);
    if (!r) { puts("No such room."); return; }
    printf("Room '%s' - last %d message%s (circular buffer, capacity %d):\n",
           r->name, r->count, r->count == 1 ? "" : "s", RING_CAP);
    if (!r->count) puts("   (empty)");
    for (int i = 0; i < r->count; i++) {
        Message *m = r->ring[(r->head + i) % RING_CAP];
        printf("   t=%ld %s: %s\n", m->ts, users[m->from]->name, m->text);
    }
}

static void rooms_list(void) {
    printf("Rooms (%d):\n", room_count);
    if (!room_count) { puts("   (none)"); return; }
    for (int i = 0; i < HASH_SIZE; i++)
        for (Room *r = room_table[i]; r; r = r->next)
            printf("   - %-12s %d member%s, %d buffered message%s\n", r->name,
                   r->nmembers, r->nmembers == 1 ? "" : "s",
                   r->count, r->count == 1 ? "" : "s");
}

/* ======================================================================
 *  CHAT OPERATIONS (glue code)
 * ==================================================================== */
static User *register_user(const char *name) {
    if (user_count >= MAX_USERS) { puts("User limit reached."); return NULL; }
    size_t len = strlen(name);
    if (len == 0 || len >= NAME_LEN) { puts("Name must be 1-31 characters."); return NULL; }
    for (const char *p = name; *p; p++)
        if (!isalnum((unsigned char)*p) && *p != '_') {
            puts("Use letters, digits and underscore only.");
            return NULL;
        }
    if (hash_find(name)) { puts("That username is taken."); return NULL; }

    User *u = calloc(1, sizeof *u);
    u->id = user_count;
    strncpy(u->name, name, NAME_LEN - 1);
    lower_copy(u->key, name, sizeof u->key);
    users[user_count] = u;
    uf_parent[user_count] = user_count;             /* new singleton set */
    uf_rank[user_count] = 0;
    user_count++;
    hash_insert(u);
    trie_insert(u->key, u);
    printf("Registered user '%s' (id %d).\n", u->name, u->id);
    return u;
}

static void send_message(const char *to_name, const char *text, int priority) {
    if (!cur) { puts("Login first."); return; }
    int to = -1;
    if (to_name) {
        User *t = hash_find(to_name);
        if (!t)       { puts("No such user."); return; }
        if (t == cur) { puts("You can't message yourself."); return; }
        to = t->id;
    }
    if (!text || !*text) { puts("Message is empty."); return; }

    Message *m = calloc(1, sizeof *m);
    m->id = next_msg_id++;
    m->from = cur->id;
    m->to = to;
    m->priority = priority;
    m->ts = tick;
    strncpy(m->text, text, MSG_LEN - 1);
    int hits = censor(m->text);                     /* Aho-Corasick */

    if (!heap_push(m)) { puts("Server queue full."); free(m); return; }
    hist_append(m);                                 /* linked list  */
    avl_root = avl_insert(avl_root, m->ts, m);      /* AVL index    */
    bt_insert(m->id, m);                            /* B-tree index */
    if (to >= 0) lru_touch(&cur->recent, to);       /* LRU cache    */
    if (cur->undo_top == UNDO_MAX) {
        memmove(cur->undo, cur->undo + 1, (UNDO_MAX - 1) * sizeof(Message *));
        cur->undo_top--;
    }
    cur->undo[cur->undo_top++] = m;                 /* stack push   */
    cur->sent++;
    printf("Message #%d queued (%s)%s. Run 'process' to deliver.\n",
           m->id, priority == 2 ? "URGENT" : "normal",
           hits ? ", banned words filtered" : "");
}

static void process_queue(void) {
    if (!heap_n) { puts("Nothing to deliver."); return; }
    puts("Delivering in priority order (heap):");
    Message *m;
    while ((m = heap_pop()) != NULL) {
        if (m->deleted) { printf("  #%d was unsent - skipped.\n", m->id); continue; }
        if (m->to >= 0) q_push(&users[m->to]->inbox, m);
        else
            for (int i = 0; i < user_count; i++)
                if (i != m->from) q_push(&users[i]->inbox, m);
        printf("  delivered");
        print_msg(m);
    }
}

static void read_inbox(void) {
    if (!cur) { puts("Login first."); return; }
    int shown = 0;
    Message *m;
    printf("Inbox of %s:\n", cur->name);
    while ((m = q_pop(&cur->inbox)) != NULL) {
        if (m->deleted) continue;
        print_msg(m);
        shown++;
    }
    if (!shown) puts("  (empty)");
}

static void undo_last(void) {
    if (!cur) { puts("Login first."); return; }
    if (cur->undo_top == 0) { puts("Nothing to undo."); return; }
    Message *m = cur->undo[--cur->undo_top];        /* stack pop */
    m->deleted = 1;
    hist_unlink(m);                                 /* O(1) list removal */
    avl_root = avl_delete(avl_root, m->ts);         /* AVL delete + rebalance */
    bt_delete(m->id);                               /* B-tree delete (borrow/merge) */
    cur->sent--;
    printf("Unsent message #%d: \"%s\"\n", m->id, m->text);
}

static void show_history(int reverse) {
    if (!cur) { puts("Login first."); return; }
    printf("Chat history (%s):\n", reverse ? "newest first" : "oldest first");
    int shown = 0;
    for (Message *m = reverse ? hist_tail : hist_head; m;
         m = reverse ? m->prev : m->next)
        if (visible_to(m, cur)) { print_msg(m); shown++; }
    if (!shown) puts("  (no messages)");
}

static void open_chat(User *t) {
    if (!cur) { puts("Login first."); return; }
    if (t == cur) { puts("That's you."); return; }
    lru_touch(&cur->recent, t->id);
    printf("Conversation %s <-> %s:\n", cur->name, t->name);
    int n = 0;
    for (Message *m = hist_head; m; m = m->next)
        if ((m->from == cur->id && m->to == t->id) ||
            (m->from == t->id && m->to == cur->id)) { print_msg(m); n++; }
    if (!n) puts("  (no messages yet)");
}

static void search_history(const char *kw) {
    if (!cur) { puts("Login first."); return; }
    char pat[MSG_LEN], text[MSG_LEN];
    lower_copy(pat, kw, sizeof pat);
    int shown = 0;
    printf("Messages containing \"%s\":\n", kw);
    for (Message *m = hist_head; m; m = m->next) {
        if (!visible_to(m, cur)) continue;
        lower_copy(text, m->text, sizeof text);
        if (kmp_contains(text, pat)) { print_msg(m); shown++; }
    }
    if (!shown) puts("  (no matches)");
}

static void leaderboard(void) {
    if (!user_count) { puts("No users yet."); return; }
    User *a[MAX_USERS], *tmp[MAX_USERS];
    for (int i = 0; i < user_count; i++) a[i] = users[i];
    merge_sort(a, tmp, 0, user_count);
    puts("Most active users (merge sort):");
    for (int i = 0; i < user_count; i++)
        printf("  %d. %-12s %d message%s\n", i + 1, a[i]->name,
               a[i]->sent, a[i]->sent == 1 ? "" : "s");
}

static void explain(void) {
    puts("Data structures and algorithms used in this project:");
    puts("  Hash table      users, rooms                       O(1) average");
    puts("  Trie            username autocomplete              O(prefix)");
    puts("  Max-heap        delivery order, urgent first       O(log n)");
    puts("  Queue           per-user inbox                     O(1)");
    puts("  Linked list     chat history, O(1) unsend          (doubly linked)");
    puts("  Stack           undo / unsend                      O(1)");
    puts("  AVL tree        messages indexed by time           O(log n)");
    puts("  B-tree          message-id index (disk style)      O(log n)");
    puts("  LRU cache       recent chats (map + linked list)   O(1)");
    puts("  Circular buffer last messages of a room            O(1)");
    puts("  Graph + BFS     fewest hops between users          O(V+E)");
    puts("  Dijkstra        strongest bond (weighted graph)    O(E log V)");
    puts("  Union-Find      friend communities                 O(a(n))");
    puts("  Aho-Corasick   multi-word banned-word filter      O(n + hits)");
    puts("  Huffman coding  history compression statistics     O(n log n)");
    puts("  KMP             keyword search                     O(n+m)");
    puts("  Merge sort      leaderboard                        O(n log n)");
}

static void help(void) {
    puts("Users & graph:");
    puts("  register <name>          create a user          (hash table + trie + DSU)");
    puts("  login <name>             switch user            (hash lookup)");
    puts("  users [prefix]           autocomplete usernames (trie)");
    puts("  friend <name> [1-9]      add friend, 1=closest   (weighted graph, union)");
    puts("  path <name>              fewest hops            (BFS)");
    puts("  bond <name>              strongest connection   (Dijkstra)");
    puts("  communities              friend groups          (union-find)");
    puts("  suggest                  people you may know    (graph)");
    puts("Messaging:");
    puts("  send <name> <text>       send a message         (heap+list+stack+AVL+LRU)");
    puts("  urgent <name> <text>     urgent message         (heap priority)");
    puts("  broadcast <text>         message everyone");
    puts("  process                  deliver queued msgs    (heap -> queues)");
    puts("  inbox                    read your inbox        (queue)");
    puts("  open <name>              open a conversation    (LRU cache)");
    puts("  recent                   recent chats           (LRU cache)");
    puts("  history [rev]            chat history           (doubly linked list)");
    puts("  search <keyword>         search history         (KMP)");
    puts("  undo                     unsend last message    (stack, AVL delete)");
    puts("  ban <word>               add banned word        (Aho-Corasick)");
    puts("Rooms:");
    puts("  room create|join <name>  group chat rooms       (hash table)");
    puts("  room say <name> <text>   post to a room         (circular buffer)");
    puts("  room log <name>          show last messages");
    puts("  rooms                    list rooms");
    puts("Analysis:");
    puts("  avl                      show the AVL tree      (self-balancing BST)");
    puts("  btree                    show the B-tree        (message-id index)");
    puts("  find <id>                look up a message by id (B-tree search)");
    puts("  range <t1> <t2>          messages in time range (AVL range query)");
    puts("  huffman                  compression statistics (Huffman coding)");
    puts("  top                      leaderboard            (merge sort)");
    puts("  tables / ds / demo / help / quit");
}

/* ======================================================================
 *  COMMAND INTERPRETER + DEMO
 * ==================================================================== */
static int run_command(const char *input);

static void run_demo(void) {
    static const char *script[] = {
        "register alice", "register bob", "register carol",
        "register dave",  "register alina", "register eve", "register frank",
        "login alice", "friend bob 1", "friend dave 9",
        "login bob",   "friend carol 1",
        "login carol", "friend dave 1",
        "login eve",   "friend frank 2",
        "login alice",
        "users al",
        "path dave",
        "bond dave",
        "suggest",
        "communities",
        "send bob hey bob, ready for the DSA showcase?",
        "urgent carol server is down, ignore that scam email!",
        "send dave sorry, my last message was stupid",
        "broadcast good morning everyone",
        "process",
        "login bob",   "inbox",
        "login alice",
        "open bob", "open dave", "open eve", "recent",
        "room create dsa-club",
        "room say dsa-club welcome to the club",
        "login bob", "room join dsa-club",
        "room say dsa-club thanks alice",
        "login alice",
        "room say dsa-club today: AVL trees",
        "login bob",
        "room say dsa-club and Dijkstra",
        "login alice",
        "room say dsa-club plus Huffman coding",
        "login bob",
        "room say dsa-club and Aho-Corasick",
        "room log dsa-club",
        "rooms",
        "login alice",
        "send bob oops wrong chat",
        "send bob oops again",
        "send bob oops once more",
        "btree",
        "find 3",
        "avl",
        "undo", "undo", "undo",
        "btree",
        "find 6",
        "avl",
        "range 25 36",
        "search SHOWCASE",
        "history rev",
        "huffman",
        "top",
        "tables",
        NULL
    };
    puts("=== DEMO START ===");
    for (int i = 0; script[i]; i++) {
        printf("\n> %s\n", script[i]);
        run_command(script[i]);
    }
    puts("\n=== DEMO END ===");
}

/* returns 0 when the program should quit */
static int run_command(const char *input) {
    char line[512];
    strncpy(line, input, sizeof line - 1);
    line[sizeof line - 1] = '\0';
    line[strcspn(line, "\r\n")] = '\0';

    char *cmd = strtok(line, " \t");
    if (!cmd) return 1;
    tick++;                                         /* logical clock */
    for (char *p = cmd; *p; p++) *p = (char)tolower((unsigned char)*p);

    if (!strcmp(cmd, "help"))             help();
    else if (!strcmp(cmd, "ds"))          explain();
    else if (!strcmp(cmd, "demo"))        run_demo();
    else if (!strcmp(cmd, "tables"))      hash_print();
    else if (!strcmp(cmd, "top"))         leaderboard();
    else if (!strcmp(cmd, "process"))     process_queue();
    else if (!strcmp(cmd, "inbox"))       read_inbox();
    else if (!strcmp(cmd, "undo"))        undo_last();
    else if (!strcmp(cmd, "communities")) show_communities();
    else if (!strcmp(cmd, "rooms"))       rooms_list();
    else if (!strcmp(cmd, "huffman"))     huffman_stats();
    else if (!strcmp(cmd, "recent")) {
        if (cur) show_recent(cur); else puts("Login first.");
    }
    else if (!strcmp(cmd, "avl")) {
        printf("AVL tree: %d node%s, height %d  (root at left, right subtree on top)\n",
               avl_count, avl_count == 1 ? "" : "s", avl_h(avl_root));
        if (!avl_root) puts("   (empty)");
        avl_print(avl_root, 0);
    }
    else if (!strcmp(cmd, "btree")) {
        printf("B-tree (min degree %d, max %d keys per node): %d key%s, height %d\n",
               BT_T, 2 * BT_T - 1, bt_count, bt_count == 1 ? "" : "s", bt_height(bt_root));
        if (!bt_root) puts("   (empty)");
        bt_print(bt_root, 0);
    }
    else if (!strcmp(cmd, "find")) {
        char *a = strtok(NULL, " \t");
        if (!cur) puts("Login first.");
        else if (!a) puts("Usage: find <message id>");
        else {
            int visited = 0;
            Message *m = bt_search(bt_root, atol(a), &visited);
            if (m && visible_to(m, cur)) print_msg(m);
            else puts("  No such message.");
            printf("  (B-tree search touched %d node%s; tree height %d)\n",
                   visited, visited == 1 ? "" : "s", bt_height(bt_root));
        }
    }
    else if (!strcmp(cmd, "range")) {
        char *a = strtok(NULL, " \t"), *b = strtok(NULL, " \t");
        if (!cur) puts("Login first.");
        else if (!a || !b) puts("Usage: range <from_t> <to_t>");
        else {
            printf("Messages with t in [%ld, %ld] (AVL range query):\n", atol(a), atol(b));
            if (!avl_range(avl_root, atol(a), atol(b))) puts("  (none)");
        }
    }
    else if (!strcmp(cmd, "ban")) {
        char *a = strtok(NULL, " \t");
        if (!a) puts("Usage: ban <word>");
        else if (ban_word(a)) printf("'%s' is now filtered.\n", a);
    }
    else if (!strcmp(cmd, "quit") || !strcmp(cmd, "exit")) return 0;
    else if (!strcmp(cmd, "register")) {
        char *a = strtok(NULL, " \t");
        if (a) register_user(a); else puts("Usage: register <name>");
    }
    else if (!strcmp(cmd, "login")) {
        char *a = strtok(NULL, " \t");
        User *u = a ? hash_find(a) : NULL;
        if (u) { cur = u; printf("Logged in as %s.\n", u->name); }
        else   puts("Unknown user. Use: login <name>");
    }
    else if (!strcmp(cmd, "users")) {
        char *a = strtok(NULL, " \t");
        printf("Users starting with \"%s\":\n", a ? a : "");
        trie_autocomplete(a ? a : "");
    }
    else if (!strcmp(cmd, "friend")) {
        char *a = strtok(NULL, " \t"), *w = strtok(NULL, " \t");
        User *u = a ? hash_find(a) : NULL;
        if (!cur) puts("Login first.");
        else if (!u) puts("Usage: friend <existing user> [distance 1-9]");
        else add_friend(cur, u, w ? atoi(w) : 5);
    }
    else if (!strcmp(cmd, "path") || !strcmp(cmd, "bond")) {
        char *a = strtok(NULL, " \t");
        User *u = a ? hash_find(a) : NULL;
        if (!cur) puts("Login first.");
        else if (!u) puts("Usage: path|bond <existing user>");
        else if (!strcmp(cmd, "path")) bfs_path(cur, u);
        else bond_path(cur, u);
    }
    else if (!strcmp(cmd, "suggest")) {
        if (cur) suggest_friends(cur); else puts("Login first.");
    }
    else if (!strcmp(cmd, "open")) {
        char *a = strtok(NULL, " \t");
        User *u = a ? hash_find(a) : NULL;
        if (!u) puts("Usage: open <existing user>"); else open_chat(u);
    }
    else if (!strcmp(cmd, "send") || !strcmp(cmd, "urgent")) {
        char *a = strtok(NULL, " \t");
        char *t = strtok(NULL, "");
        if (!a || !t) puts("Usage: send <name> <text>");
        else send_message(a, ltrim(t), strcmp(cmd, "urgent") == 0 ? 2 : 0);
    }
    else if (!strcmp(cmd, "broadcast")) {
        char *t = strtok(NULL, "");
        if (!t) puts("Usage: broadcast <text>");
        else send_message(NULL, ltrim(t), 0);
    }
    else if (!strcmp(cmd, "room")) {
        char *sub = strtok(NULL, " \t"), *name = strtok(NULL, " \t");
        if (!sub || !name) puts("Usage: room create|join|say|log <room> [text]");
        else if (!strcmp(sub, "create")) room_create(name);
        else if (!strcmp(sub, "join"))   room_join(name);
        else if (!strcmp(sub, "log"))    room_log(name);
        else if (!strcmp(sub, "say")) {
            char *t = strtok(NULL, "");
            room_say(name, t ? ltrim(t) : NULL);
        }
        else puts("Usage: room create|join|say|log <room> [text]");
    }
    else if (!strcmp(cmd, "history")) {
        char *a = strtok(NULL, " \t");
        show_history(a && !strcmp(a, "rev"));
    }
    else if (!strcmp(cmd, "search")) {
        char *t = strtok(NULL, "");
        if (!t) puts("Usage: search <keyword>");
        else search_history(ltrim(t));
    }
    else puts("Unknown command. Type 'help'.");
    return 1;
}

int main(void) {
    char buf[512];
    trie_root = trie_new();
    ban_word("spam");  ban_word("scam");           /* default filter words */
    ban_word("stupid"); ban_word("idiot");

    puts("==========================================");
    puts("  Real-Time Chat System v2  (DSA project, C)");
    puts("==========================================");
    puts("Type 'demo' for an automatic walkthrough, or 'help'.\n");

    for (;;) {
        printf("%s> ", cur ? cur->name : "guest");
        if (!fgets(buf, sizeof buf, stdin)) break;
        if (!run_command(buf)) break;
    }
    puts("Goodbye!");
    return 0;
}
