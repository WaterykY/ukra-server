#!/usr/bin/env python3
"""Мінімальний сервер UKRA: акаунти за нікнеймом, публічні профілі та особисті повідомлення.

Запуск (потрібен лише Python 3.8+, нічого встановлювати не треба):
    python3 ukra_server.py --host 0.0.0.0 --port 8080

Це навчальний MVP. Перед публічним запуском потрібні HTTPS (наприклад, за reverse-proxy),
модерація, скарги/блокування, резервні копії та політика приватності.
"""
import argparse
import hashlib
import json
import os
import re
import secrets
import hmac
import socket
import sqlite3
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, unquote, urlparse

NICK_RE = re.compile(r"^[a-z0-9_.]{3,20}$")
MAX_IMAGE = 800 * 1024
MAX_JSON = 160 * 1024
MAX_TEXT = 8000  # зашифроване повідомлення довше за відкритий текст
RATE_LIMIT = 30  # повідомлень на хвилину з одного акаунта
REGISTER_LIMIT = 10  # нових акаунтів на годину з однієї адреси

db_lock = threading.Lock()
rate = {}  # user_id -> [timestamps]
reg_rate = {}  # ip -> [timestamps]
DB = None


def init_db(path):
    global DB
    DB = sqlite3.connect(path, check_same_thread=False)
    DB.row_factory = sqlite3.Row
    DB.executescript(
        """
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            nick TEXT UNIQUE NOT NULL,
            email TEXT UNIQUE NOT NULL DEFAULT '',
            pass_salt TEXT NOT NULL DEFAULT '',
            pass_hash TEXT NOT NULL DEFAULT '',
            token_hash TEXT NOT NULL,
            name TEXT DEFAULT '', name_lc TEXT DEFAULT '', uid INTEGER, pub TEXT DEFAULT '', bio TEXT DEFAULT '',
            city TEXT DEFAULT '', oblast TEXT DEFAULT '', locality_id TEXT DEFAULT '',
            avatar BLOB, cover BLOB, avatar_v INTEGER DEFAULT 0, cover_v INTEGER DEFAULT 0,
            created_at INTEGER NOT NULL
        );
        CREATE TABLE IF NOT EXISTS messages (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            from_id INTEGER NOT NULL, to_id INTEGER NOT NULL,
            text TEXT NOT NULL, ts INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_msg_to ON messages(to_id, id);
        CREATE INDEX IF NOT EXISTS idx_msg_from ON messages(from_id, id);

        CREATE TABLE IF NOT EXISTS message_events (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            direct_message_id INTEGER UNIQUE,
            group_message_id INTEGER UNIQUE
        );
        INSERT OR IGNORE INTO message_events (id, direct_message_id)
            SELECT id, id FROM messages ORDER BY id;

        CREATE TABLE IF NOT EXISTS chat_groups (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            description TEXT NOT NULL DEFAULT '',
            invite_code TEXT UNIQUE NOT NULL,
            owner_id INTEGER NOT NULL,
            created_at INTEGER NOT NULL
        );
        CREATE TABLE IF NOT EXISTS group_members (
            group_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            role TEXT NOT NULL DEFAULT 'member',
            joined_at INTEGER NOT NULL,
            PRIMARY KEY (group_id, user_id)
        );
        CREATE INDEX IF NOT EXISTS idx_group_members_user ON group_members(user_id, group_id);
        CREATE TABLE IF NOT EXISTS group_messages (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            group_id INTEGER NOT NULL,
            from_id INTEGER NOT NULL,
            ciphertexts TEXT NOT NULL,
            ts INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_group_messages_group ON group_messages(group_id, id);

        CREATE TABLE IF NOT EXISTS market_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            seller_nick TEXT NOT NULL,
            seller_name TEXT NOT NULL,
            title TEXT NOT NULL,
            description TEXT NOT NULL,
            price INTEGER NOT NULL,
            category TEXT NOT NULL,
            condition TEXT NOT NULL,
            city TEXT NOT NULL,
            oblast TEXT NOT NULL,
            locality_id TEXT NOT NULL,
            district TEXT DEFAULT '',
            photo BLOB,
            photo_v INTEGER DEFAULT 0,
            status TEXT DEFAULT 'active',
            views_count INTEGER DEFAULT 0,
            created_at INTEGER NOT NULL,
            updated_at INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_market_loc ON market_items(locality_id, status);
        CREATE INDEX IF NOT EXISTS idx_market_city ON market_items(city, status);
        CREATE INDEX IF NOT EXISTS idx_market_user ON market_items(user_id, status);

        CREATE TABLE IF NOT EXISTS missions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            author_nick TEXT NOT NULL,
            author_name TEXT NOT NULL,
            locality_id TEXT NOT NULL,
            city TEXT NOT NULL,
            oblast TEXT NOT NULL DEFAULT '',
            title TEXT NOT NULL,
            description TEXT NOT NULL,
            category TEXT NOT NULL,
            district TEXT NOT NULL DEFAULT '',
            schedule TEXT NOT NULL DEFAULT '',
            target INTEGER NOT NULL DEFAULT 1,
            status TEXT NOT NULL DEFAULT 'Шукаємо учасників',
            created_at INTEGER NOT NULL,
            updated_at INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_missions_locality_status ON missions(locality_id, status, created_at);
        CREATE INDEX IF NOT EXISTS idx_missions_user ON missions(user_id, status);
        CREATE TABLE IF NOT EXISTS mission_participants (
            mission_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            joined_at INTEGER NOT NULL,
            PRIMARY KEY (mission_id, user_id)
        );
        CREATE INDEX IF NOT EXISTS idx_mission_participants_user ON mission_participants(user_id, mission_id);
        CREATE TABLE IF NOT EXISTS mission_reports (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            reporter_id INTEGER NOT NULL,
            mission_id INTEGER NOT NULL,
            reason TEXT NOT NULL,
            details TEXT NOT NULL DEFAULT '',
            created_at INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_mission_reports_mission ON mission_reports(mission_id, created_at);

        CREATE TABLE IF NOT EXISTS map_places (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            author_nick TEXT NOT NULL,
            author_name TEXT NOT NULL,
            locality_id TEXT NOT NULL,
            city TEXT NOT NULL DEFAULT '',
            name TEXT NOT NULL,
            description TEXT NOT NULL,
            category TEXT NOT NULL,
            lat REAL NOT NULL,
            lon REAL NOT NULL,
            photo BLOB,
            photo_v INTEGER DEFAULT 0,
            created_at INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_map_places_locality ON map_places(locality_id, created_at);
        CREATE INDEX IF NOT EXISTS idx_map_places_user ON map_places(user_id, created_at);

        CREATE TABLE IF NOT EXISTS market_favorites (
            user_id INTEGER NOT NULL,
            item_id INTEGER NOT NULL,
            created_at INTEGER NOT NULL,
            PRIMARY KEY (user_id, item_id)
        );

        CREATE TABLE IF NOT EXISTS market_offers (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            item_id INTEGER NOT NULL,
            buyer_id INTEGER NOT NULL,
            buyer_nick TEXT NOT NULL,
            buyer_name TEXT NOT NULL,
            seller_id INTEGER NOT NULL,
            seller_nick TEXT NOT NULL,
            offer_price INTEGER NOT NULL,
            status TEXT DEFAULT 'pending',
            message TEXT DEFAULT '',
            created_at INTEGER NOT NULL
        );

        CREATE TABLE IF NOT EXISTS market_reviews (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            seller_id INTEGER NOT NULL,
            seller_nick TEXT NOT NULL,
            buyer_id INTEGER NOT NULL,
            buyer_nick TEXT NOT NULL,
            buyer_name TEXT NOT NULL,
            item_id INTEGER DEFAULT 0,
            rating INTEGER NOT NULL,
            comment TEXT DEFAULT '',
            created_at INTEGER NOT NULL
        );

        CREATE TABLE IF NOT EXISTS market_reports (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            reporter_id INTEGER NOT NULL,
            item_id INTEGER NOT NULL,
            reason TEXT NOT NULL,
            details TEXT DEFAULT '',
            created_at INTEGER NOT NULL
        );

        CREATE TABLE IF NOT EXISTS blocked_users (
            user_id INTEGER NOT NULL,
            blocked_id INTEGER NOT NULL,
            created_at INTEGER NOT NULL,
            PRIMARY KEY (user_id, blocked_id)
        );
        """
    )
    # Migrate existing MVP databases without discarding existing nick accounts.
    cols = {r[1] for r in DB.execute("PRAGMA table_info(users)").fetchall()}
    for name, sql in (("email", "ALTER TABLE users ADD COLUMN email TEXT NOT NULL DEFAULT ''"), ("pass_salt", "ALTER TABLE users ADD COLUMN pass_salt TEXT NOT NULL DEFAULT ''"), ("pass_hash", "ALTER TABLE users ADD COLUMN pass_hash TEXT NOT NULL DEFAULT ''")):
        if name not in cols:
            DB.execute(sql)
    DB.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_users_email ON users(email) WHERE email != ''")
    DB.commit()
    for column in ("name_lc TEXT DEFAULT ''", "uid INTEGER", "pub TEXT DEFAULT ''"):
        try:
            DB.execute("ALTER TABLE users ADD COLUMN " + column)
        except sqlite3.OperationalError:
            pass  # колонка вже є
    DB.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_users_uid ON users(uid)")
    for row in DB.execute("SELECT id FROM users WHERE uid IS NULL").fetchall():
        DB.execute("UPDATE users SET uid = ? WHERE id = ?", (new_uid(), row["id"]))
    DB.commit()


def new_uid():
    # 8-значний числовий ID, як у іграх; унікальність гарантує індекс
    while True:
        candidate = secrets.randbelow(90_000_000) + 10_000_000
        if DB.execute("SELECT 1 FROM users WHERE uid = ?", (candidate,)).fetchone() is None:
            return candidate


def find_user(query):
    """Шукає за числовим ID (5+ цифр) або за нікнеймом."""
    query = str(query or "").strip().lstrip("@").lower()
    with db_lock:
        if query.isdigit() and len(query) >= 5:
            return DB.execute("SELECT * FROM users WHERE uid = ?", (int(query),)).fetchone()
        return DB.execute("SELECT * FROM users WHERE nick = ?", (query,)).fetchone()


def valid_pub(value):
    value = str(value or "").strip()
    if value.startswith("-----BEGIN PUBLIC KEY-----") and value.rstrip().endswith("-----END PUBLIC KEY-----") and len(value) <= 2000:
        return value
    return ""


def clean(value, limit):
    return str(value or "").strip()[:limit]


def public_user(row, with_pub=False):
    data = {
        "uid": row["uid"],
        "nick": row["nick"],
        "name": row["name"],
        "bio": row["bio"],
        "city": row["city"],
        "oblast": row["oblast"],
        "has_avatar": row["avatar"] is not None,
        "has_cover": row["cover"] is not None,
        "avatar_v": row["avatar_v"],
        "cover_v": row["cover_v"],
        "created_at": row["created_at"],
    }
    if with_pub:
        data["pub"] = row["pub"] or ""
    return data


def public_market_item(row):
    return {
        "id": row["id"],
        "user_id": row["user_id"],
        "seller_nick": row["seller_nick"],
        "seller_name": row["seller_name"],
        "title": row["title"],
        "description": row["description"],
        "price": row["price"],
        "category": row["category"],
        "condition": row["condition"],
        "city": row["city"],
        "oblast": row["oblast"],
        "locality_id": row["locality_id"],
        "district": row["district"] or "",
        "has_photo": row["photo"] is not None,
        "photo_v": row["photo_v"],
        "status": row["status"],
        "views_count": row["views_count"],
        "created_at": row["created_at"],
        "updated_at": row["updated_at"],
    }


class Handler(BaseHTTPRequestHandler):
    server_version = "UKRA/0.1"

    def log_message(self, fmt, *args):
        pass

    # ---------- допоміжне ----------
    def send_json(self, status, payload):
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def fail(self, status, message):
        self.send_json(status, {"error": message})

    def read_body(self, limit):
        length = int(self.headers.get("Content-Length") or 0)
        if length > limit:
            return None
        return self.rfile.read(length) if length else b""

    def read_json(self):
        raw = self.read_body(MAX_JSON)
        if raw is None:
            self.fail(413, "Запит завеликий")
            return None
        try:
            data = json.loads(raw.decode("utf-8") or "{}")
        except (ValueError, UnicodeDecodeError):
            self.fail(400, "Некоректний JSON")
            return None
        if not isinstance(data, dict):
            self.fail(400, "Очікувався JSON-обʼєкт")
            return None
        return data

    def client_ip(self):
        ip = self.client_address[0]
        # За reverse-proxy на цій самій машині реальну адресу беремо із X-Forwarded-For.
        if ip in ("127.0.0.1", "::1"):
            forwarded = self.headers.get("X-Forwarded-For", "")
            if forwarded:
                return forwarded.split(",")[0].strip()
        return ip

    def auth(self):
        header = self.headers.get("Authorization", "")
        if not header.startswith("Bearer "):
            return None
        digest = hashlib.sha256(header[7:].strip().encode()).hexdigest()
        with db_lock:
            return DB.execute("SELECT * FROM users WHERE token_hash = ?", (digest,)).fetchone()

    def require_auth(self):
        user = self.auth()
        if user is None:
            self.fail(401, "Потрібно увійти")
        return user

    # ---------- маршрути ----------
    def do_GET(self):
        url = urlparse(self.path)
        parts = [unquote(p) for p in url.path.strip("/").split("/")]
        query = parse_qs(url.query)
        if parts == ["api", "health"]:
            return self.send_json(200, {"ok": True})
        if len(parts) == 3 and parts[:2] == ["api", "user"]:
            return self.get_user(parts[2].lower())
        if len(parts) == 4 and parts[:2] == ["api", "media"]:
            return self.get_media(parts[2].lower(), parts[3])
        if parts == ["api", "search"]:
            return self.search(query.get("q", [""])[0])
        if parts == ["api", "messages"]:
            return self.get_messages(query.get("since", ["0"])[0])
        if parts == ["api", "missions"]:
            return self.get_missions(query)
        if parts == ["api", "map", "places"]:
            return self.get_map_places()
        if len(parts) == 5 and parts[:3] == ["api", "map", "places"] and parts[4] == "photo":
            return self.get_map_place_photo(parts[3])
        if parts == ["api", "groups"]:
            return self.list_groups()
        if len(parts) == 3 and parts[:2] == ["api", "groups"]:
            return self.get_group(parts[2])
        # UKRA Market GET routes
        if parts == ["api", "market", "items"]:
            return self.get_market_items(query)
        if len(parts) == 4 and parts[:3] == ["api", "market", "items"]:
            return self.get_market_item(parts[3])
        if len(parts) == 5 and parts[:3] == ["api", "market", "items"] and parts[4] == "photo":
            return self.get_market_photo(parts[3])
        if parts == ["api", "market", "favorites"]:
            return self.get_market_favorites()
        if parts == ["api", "market", "offers"]:
            return self.get_market_offers()
        if len(parts) == 4 and parts[:3] == ["api", "market", "seller"]:
            return self.get_seller_profile(parts[3])
        if parts == ["api", "users", "blocked"]:
            return self.get_blocked_users()
        self.fail(404, "Не знайдено")

    def do_POST(self):
        parts = [unquote(p) for p in urlparse(self.path).path.strip("/").split("/")]
        if parts == ["api", "register"]:
            return self.register()
        if parts == ["api", "login"]:
            return self.login()
        if parts == ["api", "profile"]:
            return self.update_profile()
        if len(parts) == 2 and parts[0] == "api" and parts[1] in ("avatar", "cover"):
            return self.upload_image(parts[1])
        if parts == ["api", "send"]:
            return self.send_message()
        if parts == ["api", "missions"]:
            return self.create_mission()
        if parts == ["api", "map", "places"]:
            return self.create_map_place()
        if len(parts) == 5 and parts[:3] == ["api", "map", "places"] and parts[4] == "photo":
            return self.upload_map_place_photo(parts[3])
        if len(parts) == 4 and parts[:2] == ["api", "missions"]:
            if parts[3] == "join":
                return self.join_mission(parts[2])
            if parts[3] == "status":
                return self.update_mission_status(parts[2])
            if parts[3] == "report":
                return self.report_mission(parts[2])
        if parts == ["api", "groups"]:
            return self.create_group()
        if parts == ["api", "groups", "join"]:
            return self.join_group()
        if len(parts) == 4 and parts[:2] == ["api", "groups"]:
            actions = {
                "members": self.add_group_member,
                "role": self.set_group_member_role,
                "remove": self.remove_group_member,
                "leave": self.leave_group,
                "update": self.update_group,
                "messages": self.send_group_message,
            }
            if parts[3] in actions:
                return actions[parts[3]](parts[2])
        # UKRA Market POST routes
        if parts == ["api", "market", "items"]:
            return self.create_market_item()
        if len(parts) == 4 and parts[:3] == ["api", "market", "items"]:
            return self.update_market_item(parts[3])
        if len(parts) == 5 and parts[:3] == ["api", "market", "items"] and parts[4] == "photo":
            return self.upload_market_photo(parts[3])
        if len(parts) == 5 and parts[:3] == ["api", "market", "items"] and parts[4] == "status":
            return self.set_market_item_status(parts[3])
        if len(parts) == 5 and parts[:3] == ["api", "market", "items"] and parts[4] == "bump":
            return self.bump_market_item(parts[3])
        if len(parts) == 5 and parts[:3] == ["api", "market", "items"] and parts[4] == "delete":
            return self.delete_market_item(parts[3])
        if len(parts) == 5 and parts[:3] == ["api", "market", "items"] and parts[4] == "favorite":
            return self.toggle_market_favorite(parts[3])
        if len(parts) == 5 and parts[:3] == ["api", "market", "items"] and parts[4] == "offer":
            return self.create_market_offer(parts[3])
        if len(parts) == 5 and parts[:3] == ["api", "market", "offers"] and parts[4] == "respond":
            return self.respond_market_offer(parts[3])
        if parts == ["api", "market", "reviews"]:
            return self.add_market_review()
        if len(parts) == 5 and parts[:3] == ["api", "market", "items"] and parts[4] == "report":
            return self.report_market_item(parts[3])
        if len(parts) == 4 and parts[:3] == ["api", "users", "block"]:
            return self.toggle_block_user(parts[3])
        self.fail(404, "Не знайдено")

    def do_DELETE(self):
        parts = [unquote(p) for p in urlparse(self.path).path.strip("/").split("/")]
        if len(parts) == 4 and parts[:3] == ["api", "market", "items"]:
            return self.delete_market_item(parts[3])
        self.fail(404, "Не знайдено")

    # ---------- обробники ----------
    def register(self):
        data = self.read_json()
        if data is None:
            return
        now = time.time()
        ip = self.client_ip()
        recent = [t for t in reg_rate.get(ip, []) if now - t < 3600]
        if len(recent) >= REGISTER_LIMIT:
            return self.fail(429, "Забагато нових акаунтів з цієї адреси, спробуй пізніше")
        nick = clean(data.get("nick"), 40).lstrip("@").lower()
        if not NICK_RE.match(nick) or nick.startswith(".") or nick.endswith(".") or nick.isdigit():
            return self.fail(400, "Нікнейм: 3–20 символів, лише a–z, 0–9, _ та крапка, і не лише з цифр")
        email = clean(data.get("email"), 254).strip().lower()
        password = str(data.get("password", ""))
        if not re.fullmatch(r"[^\s@]+@[^\s@]+\.[^\s@]+", email):
            return self.fail(400, "Вкажи коректну електронну пошту")
        if len(password) < 12 or len(password) > 256:
            return self.fail(400, "Пароль має містити від 12 до 256 символів")
        salt = secrets.token_bytes(16)
        password_hash = hashlib.scrypt(password.encode(), salt=salt, n=2**14, r=8, p=1).hex()
        token = secrets.token_urlsafe(32)
        digest = hashlib.sha256(token.encode()).hexdigest()
        try:
            with db_lock:
                DB.execute(
                    "INSERT INTO users (nick, email, pass_salt, pass_hash, token_hash, name, name_lc, uid, pub, bio, city, oblast, locality_id, created_at) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                    (nick, email, salt.hex(), password_hash, digest, clean(data.get("name"), 40), clean(data.get("name"), 40).lower(), new_uid(),
                     valid_pub(data.get("pub")), clean(data.get("bio"), 200), clean(data.get("city"), 60),
                     clean(data.get("oblast"), 60), clean(data.get("locality_id"), 40), int(time.time())),
                )
                DB.commit()
                row = DB.execute("SELECT * FROM users WHERE nick = ?", (nick,)).fetchone()
        except sqlite3.IntegrityError:
            return self.fail(409, "Цей нікнейм або email уже використовується")
        recent.append(now)
        reg_rate[ip] = recent
        self.send_json(201, {"token": token, "user": public_user(row)})

    def login(self):
        data = self.read_json()
        if data is None:
            return
        email = clean(data.get("email"), 254).strip().lower()
        password = str(data.get("password", ""))
        with db_lock:
            row = DB.execute("SELECT * FROM users WHERE email = ?", (email,)).fetchone()
        if row is None or not row["pass_salt"] or not row["pass_hash"]:
            return self.fail(401, "Email або пароль неправильні")
        actual = hashlib.scrypt(password.encode(), salt=bytes.fromhex(row["pass_salt"]), n=2**14, r=8, p=1).hex()
        if not hmac.compare_digest(actual, row["pass_hash"]):
            return self.fail(401, "Email або пароль неправильні")
        token = secrets.token_urlsafe(32)
        with db_lock:
            DB.execute("UPDATE users SET token_hash = ? WHERE id = ?", (hashlib.sha256(token.encode()).hexdigest(), row["id"]))
            DB.commit()
            row = DB.execute("SELECT * FROM users WHERE id = ?", (row["id"],)).fetchone()
        self.send_json(200, {"token": token, "user": public_user(row)})

    def update_profile(self):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        pub = valid_pub(data.get("pub")) or (user["pub"] or "")
        with db_lock:
            DB.execute(
                "UPDATE users SET name=?, name_lc=?, bio=?, city=?, oblast=?, locality_id=?, pub=? WHERE id=?",
                (clean(data.get("name"), 40), clean(data.get("name"), 40).lower(), clean(data.get("bio"), 200),
                 clean(data.get("city"), 60), clean(data.get("oblast"), 60), clean(data.get("locality_id"), 40), pub, user["id"]),
            )
            DB.commit()
            row = DB.execute("SELECT * FROM users WHERE id = ?", (user["id"],)).fetchone()
        self.send_json(200, {"user": public_user(row)})

    def upload_image(self, kind):
        user = self.require_auth()
        if user is None:
            return
        raw = self.read_body(MAX_IMAGE)
        if raw is None:
            return self.fail(413, "Зображення завелике (максимум 800 КБ)")
        if raw and not raw.startswith(b"\xff\xd8"):
            return self.fail(400, "Потрібен файл JPEG")
        value = raw if raw else None
        column, version = ("avatar", "avatar_v") if kind == "avatar" else ("cover", "cover_v")
        with db_lock:
            DB.execute(f"UPDATE users SET {column}=?, {version}={version}+1 WHERE id=?", (value, user["id"]))
            DB.commit()
        self.send_json(200, {"ok": True})

    def get_user(self, query):
        row = find_user(query)
        if row is None:
            return self.fail(404, "Користувача не знайдено")
        self.send_json(200, public_user(row, True))

    def get_media(self, query, kind):
        if kind not in ("avatar", "cover"):
            return self.fail(404, "Не знайдено")
        found = find_user(query)
        if found is None or found[kind] is None:
            return self.fail(404, "Немає зображення")
        data = bytes(found[kind])
        self.send_response(200)
        self.send_header("Content-Type", "image/jpeg")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "public, max-age=86400")
        self.end_headers()
        self.wfile.write(data)

    def search(self, q):
        q = clean(q, 40).lstrip("@").lower()
        if len(q) < 2:
            return self.send_json(200, {"users": []})
        esc = q.replace("%", "").replace("_", "\\_")
        like = esc + "%"
        contains = "%" + esc + "%"
        with db_lock:
            rows = DB.execute(
                "SELECT * FROM users WHERE nick LIKE ? ESCAPE '\\' OR name_lc LIKE ? ESCAPE '\\' ORDER BY nick LIMIT 20",
                (like, contains),
            ).fetchall()
            if q.isdigit() and len(q) >= 5:
                exact = DB.execute("SELECT * FROM users WHERE uid = ?", (int(q),)).fetchone()
                if exact is not None and all(r["id"] != exact["id"] for r in rows):
                    rows = [exact] + list(rows)
        self.send_json(200, {"users": [public_user(r) for r in rows]})

    def send_message(self):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        text = str(data.get("text") or "").strip()
        if not text or len(text) > MAX_TEXT:
            return self.fail(400, "Повідомлення порожнє або завелике")
        now = time.time()
        stamps = [t for t in rate.get(user["id"], []) if now - t < 60]
        if len(stamps) >= RATE_LIMIT:
            return self.fail(429, "Забагато повідомлень, зачекай хвилину")
        stamps.append(now)
        rate[user["id"]] = stamps
        target = find_user(data.get("to"))
        if target is None:
            return self.fail(404, "Користувача з таким ID або нікнеймом немає")
        if target["id"] == user["id"]:
            return self.fail(400, "Не можна писати самому собі")
        with db_lock:
            cur = DB.execute(
                "INSERT INTO messages (from_id, to_id, text, ts) VALUES (?,?,?,?)",
                (user["id"], target["id"], text, int(now)),
            )
            event = DB.execute(
                "INSERT INTO message_events (direct_message_id) VALUES (?)", (cur.lastrowid,)
            )
            DB.commit()
            msg_id = event.lastrowid
        self.send_json(201, {"id": msg_id, "ts": int(now)})

    def get_messages(self, since_raw):
        user = self.require_auth()
        if user is None:
            return
        try:
            since = max(0, int(since_raw))
        except ValueError:
            since = 0
        with db_lock:
            direct_rows = DB.execute(
                """SELECT e.id AS event_id, m.text, m.ts, f.nick AS from_nick, t.nick AS to_nick
                   FROM message_events e JOIN messages m ON m.id = e.direct_message_id
                   JOIN users f ON f.id = m.from_id JOIN users t ON t.id = m.to_id
                   WHERE (m.to_id = ? OR m.from_id = ?) AND e.id > ? ORDER BY e.id LIMIT 200""",
                (user["id"], user["id"], since),
            ).fetchall()
            group_rows = DB.execute(
                """SELECT e.id AS event_id, gm.group_id, gm.ciphertexts, gm.ts, u.nick AS from_nick
                   FROM message_events e JOIN group_messages gm ON gm.id = e.group_message_id
                   JOIN users u ON u.id = gm.from_id
                   JOIN group_members mine ON mine.group_id = gm.group_id AND mine.user_id = ?
                   WHERE e.id > ? ORDER BY e.id LIMIT 200""",
                (user["id"], since),
            ).fetchall()
        messages = [
            {"id": r["event_id"], "type": "direct", "from": r["from_nick"], "to": r["to_nick"], "text": r["text"], "ts": r["ts"]}
            for r in direct_rows
        ]
        for row in group_rows:
            try:
                envelopes = json.loads(row["ciphertexts"])
            except (ValueError, TypeError):
                continue
            cipher = envelopes.get(user["nick"])
            if not isinstance(cipher, str):
                continue
            messages.append({
                "id": row["event_id"], "type": "group", "group_id": row["group_id"],
                "from": row["from_nick"], "text": cipher, "ts": row["ts"],
            })
        messages.sort(key=lambda item: item["id"])
        self.send_json(200, {"messages": messages[:200]})

    def _group_payload(self, group_id, user_id):
        group = DB.execute(
            """SELECT g.*, owner.nick AS owner_nick
               FROM chat_groups g JOIN users owner ON owner.id = g.owner_id WHERE g.id = ?""",
            (group_id,),
        ).fetchone()
        if group is None:
            return None
        mine = DB.execute(
            "SELECT role FROM group_members WHERE group_id = ? AND user_id = ?", (group_id, user_id)
        ).fetchone()
        if mine is None:
            return None
        members = DB.execute(
            """SELECT u.nick, u.name, u.pub, gm.role, gm.joined_at
               FROM group_members gm JOIN users u ON u.id = gm.user_id
               WHERE gm.group_id = ? ORDER BY CASE gm.role WHEN 'owner' THEN 0 WHEN 'moderator' THEN 1 ELSE 2 END, u.nick""",
            (group_id,),
        ).fetchall()
        return {
            "id": group["id"], "name": group["name"], "description": group["description"],
            "invite_code": group["invite_code"], "owner": group["owner_nick"],
            "created_at": group["created_at"], "my_role": mine["role"],
            "member_count": len(members),
            "members": [{"nick": m["nick"], "name": m["name"], "pub": m["pub"], "role": m["role"], "joined_at": m["joined_at"]} for m in members],
        }

    def list_groups(self):
        user = self.require_auth()
        if user is None:
            return
        with db_lock:
            rows = DB.execute(
                "SELECT group_id FROM group_members WHERE user_id = ? ORDER BY joined_at DESC", (user["id"],)
            ).fetchall()
            groups = [self._group_payload(row["group_id"], user["id"]) for row in rows]
        self.send_json(200, {"groups": [group for group in groups if group is not None]})

    def get_group(self, group_id_raw):
        user = self.require_auth()
        if user is None:
            return
        try:
            group_id = int(group_id_raw)
        except (ValueError, TypeError):
            return self.fail(400, "Некоректний ID групи")
        with db_lock:
            group = self._group_payload(group_id, user["id"])
        if group is None:
            return self.fail(404, "Групу не знайдено або в тебе немає доступу")
        self.send_json(200, {"group": group})

    def create_group(self):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        name = clean(data.get("name"), 50).strip()
        description = clean(data.get("description"), 600).strip()
        if len(name) < 2:
            return self.fail(400, "Назва групи має містити щонайменше 2 символи")
        now = int(time.time())
        code = secrets.token_hex(6)
        with db_lock:
            cur = DB.execute(
                "INSERT INTO chat_groups (name, description, invite_code, owner_id, created_at) VALUES (?,?,?,?,?)",
                (name, description, code, user["id"], now),
            )
            group_id = cur.lastrowid
            DB.execute(
                "INSERT INTO group_members (group_id, user_id, role, joined_at) VALUES (?,?,?,?)",
                (group_id, user["id"], "owner", now),
            )
            DB.commit()
            group = self._group_payload(group_id, user["id"])
        self.send_json(201, {"group": group})

    def join_group(self):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        code = clean(data.get("invite_code"), 32).strip().lower()
        now = int(time.time())
        with db_lock:
            group = DB.execute("SELECT id FROM chat_groups WHERE invite_code = ?", (code,)).fetchone()
            if group is None:
                return self.fail(404, "Посилання-запрошення не знайдено")
            count = DB.execute("SELECT COUNT(*) AS n FROM group_members WHERE group_id = ?", (group["id"],)).fetchone()["n"]
            if count >= 32:
                return self.fail(409, "У групі вже максимальна кількість учасників")
            DB.execute(
                "INSERT OR IGNORE INTO group_members (group_id, user_id, role, joined_at) VALUES (?,?,?,?)",
                (group["id"], user["id"], "member", now),
            )
            DB.commit()
            result = self._group_payload(group["id"], user["id"])
        self.send_json(200, {"group": result})

    def _group_id(self, raw):
        try:
            return max(0, int(raw))
        except (ValueError, TypeError):
            return 0

    def _group_admin(self, group_id, user_id):
        return DB.execute(
            "SELECT role FROM group_members WHERE group_id = ? AND user_id = ?", (group_id, user_id)
        ).fetchone()

    def add_group_member(self, group_id_raw):
        user = self.require_auth()
        if user is None:
            return
        group_id = self._group_id(group_id_raw)
        data = self.read_json()
        if not group_id or data is None:
            return self.fail(400, "Некоректна група")
        target = find_user(data.get("nick"))
        if target is None:
            return self.fail(404, "Користувача не знайдено")
        now = int(time.time())
        with db_lock:
            mine = self._group_admin(group_id, user["id"])
            if mine is None or mine["role"] not in ("owner", "moderator"):
                return self.fail(403, "Додавати учасників можуть лише власник і модератори")
            count = DB.execute("SELECT COUNT(*) AS n FROM group_members WHERE group_id = ?", (group_id,)).fetchone()["n"]
            if count >= 32:
                return self.fail(409, "У групі вже 32 учасники")
            DB.execute(
                "INSERT OR IGNORE INTO group_members (group_id, user_id, role, joined_at) VALUES (?,?,?,?)",
                (group_id, target["id"], "member", now),
            )
            DB.commit()
            result = self._group_payload(group_id, user["id"])
        self.send_json(200, {"group": result})

    def set_group_member_role(self, group_id_raw):
        user = self.require_auth()
        if user is None:
            return
        group_id = self._group_id(group_id_raw)
        data = self.read_json()
        role = clean(data.get("role"), 20) if isinstance(data, dict) else ""
        if not group_id or not isinstance(data, dict) or role not in ("moderator", "member"):
            return self.fail(400, "Некоректна роль учасника")
        target = find_user(data.get("nick"))
        if target is None:
            return self.fail(404, "Користувача не знайдено")
        with db_lock:
            mine = self._group_admin(group_id, user["id"])
            target_member = self._group_admin(group_id, target["id"])
            if mine is None or mine["role"] != "owner":
                return self.fail(403, "Керувати ролями може лише власник групи")
            if target_member is None or target_member["role"] == "owner":
                return self.fail(400, "Не можна змінити роль цього учасника")
            DB.execute("UPDATE group_members SET role = ? WHERE group_id = ? AND user_id = ?", (role, group_id, target["id"]))
            DB.commit()
            result = self._group_payload(group_id, user["id"])
        self.send_json(200, {"group": result})

    def remove_group_member(self, group_id_raw):
        user = self.require_auth()
        if user is None:
            return
        group_id = self._group_id(group_id_raw)
        data = self.read_json()
        if not group_id or data is None:
            return self.fail(400, "Некоректна група")
        target = find_user(data.get("nick"))
        if target is None:
            return self.fail(404, "Користувача не знайдено")
        with db_lock:
            mine = self._group_admin(group_id, user["id"])
            target_member = self._group_admin(group_id, target["id"])
            if mine is None or mine["role"] not in ("owner", "moderator"):
                return self.fail(403, "Видаляти учасників можуть власник і модератори")
            if target_member is None or target_member["role"] == "owner":
                return self.fail(400, "Цього учасника не можна видалити")
            if mine["role"] == "moderator" and target_member["role"] == "moderator":
                return self.fail(403, "Модератор не може видалити іншого модератора")
            DB.execute("DELETE FROM group_members WHERE group_id = ? AND user_id = ?", (group_id, target["id"]))
            DB.commit()
            result = self._group_payload(group_id, user["id"])
        self.send_json(200, {"group": result})

    def leave_group(self, group_id_raw):
        user = self.require_auth()
        if user is None:
            return
        group_id = self._group_id(group_id_raw)
        with db_lock:
            mine = self._group_admin(group_id, user["id"])
            if mine is None:
                return self.fail(404, "Ти не є учасником цієї групи")
            if mine["role"] == "owner":
                return self.fail(409, "Власник має передати роль іншому учаснику перед виходом")
            DB.execute("DELETE FROM group_members WHERE group_id = ? AND user_id = ?", (group_id, user["id"]))
            DB.commit()
        self.send_json(200, {"ok": True})

    def update_group(self, group_id_raw):
        user = self.require_auth()
        if user is None:
            return
        group_id = self._group_id(group_id_raw)
        data = self.read_json()
        if not group_id or data is None:
            return self.fail(400, "Некоректна група")
        name = clean(data.get("name"), 50).strip()
        description = clean(data.get("description"), 600).strip()
        if len(name) < 2:
            return self.fail(400, "Назва має містити щонайменше 2 символи")
        with db_lock:
            mine = self._group_admin(group_id, user["id"])
            if mine is None or mine["role"] not in ("owner", "moderator"):
                return self.fail(403, "Змінювати групу можуть власник і модератори")
            DB.execute("UPDATE chat_groups SET name = ?, description = ? WHERE id = ?", (name, description, group_id))
            DB.commit()
            result = self._group_payload(group_id, user["id"])
        self.send_json(200, {"group": result})

    def send_group_message(self, group_id_raw):
        user = self.require_auth()
        if user is None:
            return
        group_id = self._group_id(group_id_raw)
        data = self.read_json()
        envelopes = data.get("ciphertexts") if isinstance(data, dict) else None
        if not group_id or not isinstance(envelopes, dict) or not envelopes:
            return self.fail(400, "Немає зашифрованого повідомлення")
        if len(json.dumps(envelopes, separators=(",", ":"))) > 150 * 1024:
            return self.fail(413, "Зашифроване повідомлення завелике")
        if any(not isinstance(value, str) or not value.startswith("UKRA1:") for value in envelopes.values()):
            return self.fail(400, "Усі копії повідомлення мають бути зашифровані")
        now = int(time.time())
        stamps = [stamp for stamp in rate.get(user["id"], []) if now - stamp < 60]
        if len(stamps) >= RATE_LIMIT:
            return self.fail(429, "Забагато повідомлень, зачекай хвилину")
        stamps.append(now)
        rate[user["id"]] = stamps
        with db_lock:
            members = DB.execute(
                "SELECT u.id, u.nick FROM group_members gm JOIN users u ON u.id = gm.user_id WHERE gm.group_id = ?",
                (group_id,),
            ).fetchall()
            if not any(member["id"] == user["id"] for member in members):
                return self.fail(403, "Ти більше не є учасником цієї групи")
            expected = {member["nick"] for member in members}
            if set(envelopes.keys()) != expected:
                return self.fail(400, "Зашифровані копії не відповідають списку учасників")
            cur = DB.execute(
                "INSERT INTO group_messages (group_id, from_id, ciphertexts, ts) VALUES (?,?,?,?)",
                (group_id, user["id"], json.dumps(envelopes, separators=(",", ":")), now),
            )
            event = DB.execute("INSERT INTO message_events (group_message_id) VALUES (?)", (cur.lastrowid,))
            DB.commit()
            message_id = event.lastrowid
        self.send_json(201, {"id": message_id, "ts": now})

    # ==================== UKRA MARKET ОБРОБНИКИ ====================

    def get_map_places(self):
        user = self.require_auth()
        locality_id = clean(user["locality_id"], 50)
        if not locality_id:
            return self.send_json(200, {"places": [], "total": 0})
        with db_lock:
            rows = DB.execute(
                """SELECT p.*, u.nick AS current_nick FROM map_places p
                   JOIN users u ON u.id=p.user_id
                   WHERE p.locality_id=?
                     AND p.user_id NOT IN (SELECT blocked_id FROM blocked_users WHERE user_id=?)
                   ORDER BY p.created_at DESC LIMIT 300""",
                (locality_id, user["id"]),
            ).fetchall()
        places = [{
            "id": int(row["id"]), "name": row["name"], "description": row["description"],
            "category": row["category"], "lat": row["lat"], "lon": row["lon"],
            "locality_id": row["locality_id"], "city": row["city"],
            "author": row["author_name"], "author_nick": row["author_nick"],
            "has_photo": row["photo"] is not None, "photo_v": row["photo_v"], "created_at": row["created_at"],
        } for row in rows]
        self.send_json(200, {"places": places, "total": len(places)})

    def create_map_place(self):
        user = self.require_auth()
        data = self.read_json()
        if data is None:
            return
        name = clean(data.get("name"), 80)
        description = clean(data.get("description"), 600)
        category = clean(data.get("category"), 30)
        locality_id = clean(user["locality_id"], 50)
        allowed = {"shop", "food", "pharmacy", "service", "public"}
        letters_name = re.findall(r"[^\W\d_]", name, flags=re.UNICODE)
        letters_desc = re.findall(r"[^\W\d_]", description, flags=re.UNICODE)
        vowels = set("аеиіоуяєюїыэёaeiouy")
        vowel_count = sum(1 for char in letters_desc if char.casefold() in vowels)
        if (not locality_id or len(name) < 3 or len(letters_name) < 3
                or len(set(c.casefold() for c in letters_name)) < 2
                or len(description) < 20 or len(description.split()) < 4 or len(letters_desc) < 12 or vowel_count < 3
                or len(set(c.casefold() for c in letters_desc)) < 5
                or category not in allowed):
            return self.fail(400, "Додай справжню назву й опис щонайменше з чотирьох слів, обери категорію та населений пункт у профілі")
        try:
            lat, lon = float(data.get("lat")), float(data.get("lon"))
        except (TypeError, ValueError):
            return self.fail(400, "Не вдалося визначити точку на мапі")
        if not (43.0 <= lat <= 53.0 and 21.0 <= lon <= 41.0):
            return self.fail(400, "Точка має бути в межах України")
        now = int(time.time())
        normalized = " ".join(name.casefold().split())
        with db_lock:
            recent = DB.execute("SELECT COUNT(*) FROM map_places WHERE user_id=? AND created_at>?", (user["id"], now - 86400)).fetchone()[0]
            if recent >= 3:
                return self.fail(429, "За добу можна додати не більше трьох місць")
            recent_names = DB.execute("SELECT name FROM map_places WHERE locality_id=? AND created_at>?", (locality_id, now - 30 * 86400)).fetchall()
            if any(" ".join(row["name"].casefold().split()) == normalized for row in recent_names):
                return self.fail(409, "Схоже місце вже додали у твоєму населеному пункті")
            cur = DB.execute(
                """INSERT INTO map_places(user_id,author_nick,author_name,locality_id,city,name,description,category,lat,lon,created_at)
                   VALUES(?,?,?,?,?,?,?,?,?,?,?)""",
                (user["id"], user["nick"], clean(user["name"] or user["nick"], 60), locality_id,
                 clean(user["city"], 60), name, description, category, lat, lon, now),
            )
            DB.commit()
            place_id = cur.lastrowid
        self.send_json(201, {"ok": True, "place": {"id": place_id, "name": name, "description": description,
            "category": category, "lat": lat, "lon": lon, "locality_id": locality_id,
            "city": user["city"], "author": user["name"] or user["nick"], "author_nick": user["nick"],
            "has_photo": False, "created_at": now}})

    def get_map_place_photo(self, place_id):
        try:
            place_id = int(place_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")
        user = self.require_auth()
        with db_lock:
            row = DB.execute("SELECT photo,locality_id FROM map_places WHERE id=?", (place_id,)).fetchone()
            if not row or not row["photo"] or row["locality_id"] != clean(user["locality_id"], 50):
                return self.fail(404, "Фото недоступне")
            data = bytes(row["photo"])
        self.send_response(200)
        self.send_header("Content-Type", "image/jpeg")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "private, max-age=86400")
        self.end_headers()
        self.wfile.write(data)

    def upload_map_place_photo(self, place_id):
        user = self.require_auth()
        try:
            place_id = int(place_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")
        raw = self.read_body(MAX_IMAGE)
        if raw is None:
            return self.fail(413, "Фото завелике (максимум 800 КБ)")
        if not raw.startswith(b"\xff\xd8"):
            return self.fail(400, "Потрібен файл JPEG")
        with db_lock:
            row = DB.execute("SELECT user_id FROM map_places WHERE id=?", (place_id,)).fetchone()
            if not row:
                return self.fail(404, "Місце не знайдено")
            if row["user_id"] != user["id"]:
                return self.fail(403, "Змінювати фото може лише автор")
            DB.execute("UPDATE map_places SET photo=?, photo_v=photo_v+1 WHERE id=?", (raw, place_id))
            DB.commit()
        self.send_json(200, {"ok": True})

    def get_missions(self, query):
        locality_id = clean(query.get("locality_id", [""])[0], 50)
        if not locality_id:
            return self.send_json(200, {"missions": [], "total": 0})
        user = self.auth()
        if user and clean(user["locality_id"], 50) != locality_id:
            return self.send_json(200, {"missions": [], "total": 0})
        with db_lock:
            rows = DB.execute(
                """SELECT m.*, u.nick AS author_nick, u.name AS author_name,
                          (SELECT COUNT(*) FROM mission_participants mp WHERE mp.mission_id=m.id) AS participant_count,
                          (SELECT COUNT(*) FROM mission_participants mp WHERE mp.mission_id=m.id AND mp.user_id=?) AS joined
                   FROM missions m JOIN users u ON u.id=m.user_id
                   WHERE m.locality_id=? AND m.status != 'Скасовано'
                     AND (? IS NULL OR m.user_id NOT IN (SELECT blocked_id FROM blocked_users WHERE user_id=?))
                   ORDER BY m.created_at DESC LIMIT 100""",
                (user["id"] if user else 0, locality_id, user["id"] if user else None, user["id"] if user else 0),
            ).fetchall()
            missions = []
            for row in rows:
                missions.append({
                    "id": row["id"], "server_id": row["id"], "author_nick": row["author_nick"],
                    "author": row["author_name"] or row["author_nick"], "locality_id": row["locality_id"],
                    "city": row["city"], "oblast": row["oblast"], "title": row["title"],
                    "description": row["description"], "category": row["category"],
                    "district": row["district"], "schedule": row["schedule"], "target": row["target"],
                    "status": row["status"], "participant_count": row["participant_count"],
                    "joined": bool(row["joined"]), "is_owner": bool(user and row["user_id"] == user["id"]),
                    "created_at": row["created_at"],
                })
        self.send_json(200, {"missions": missions, "total": len(missions)})

    def create_mission(self):
        user = self.require_auth()
        data = self.read_json()
        if data is None:
            return
        title = clean(data.get("title"), 100)
        description = clean(data.get("description"), 1800)
        category = clean(data.get("category"), 40)
        locality_id = clean(user["locality_id"], 50)
        district = clean(data.get("district"), 80)
        schedule = clean(data.get("schedule"), 100)
        try:
            target = max(1, min(100, int(data.get("target", 1))))
        except (TypeError, ValueError):
            target = 1
        allowed = {"Взаємодопомога", "Благоустрій", "Тварини", "Подія", "Збір речей", "Інше"}
        if len(title) < 3 or len(description) < 10 or not locality_id or clean(data.get("locality_id"), 50) != locality_id or category not in allowed:
            return self.fail(400, "Перевір назву, опис, категорію та населений пункт")
        status = "Шукаємо учасників"
        now = int(time.time())
        with db_lock:
            recent_count = DB.execute("SELECT COUNT(*) FROM missions WHERE user_id=? AND created_at>?", (user["id"], now - 86400)).fetchone()[0]
            if recent_count >= 5:
                return self.fail(429, "За добу можна створити не більше п’яти місій")
            cur = DB.execute(
                """INSERT INTO missions (user_id,author_nick,author_name,locality_id,city,oblast,title,description,category,district,schedule,target,status,created_at,updated_at)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                (user["id"], user["nick"], clean(user["name"] or user["nick"], 60), locality_id,
                 clean(user["city"], 60), clean(user["oblast"], 60), title, description,
                 category, district, schedule, target, status, now, now),
            )
            mission_id = cur.lastrowid
            DB.commit()
        self.send_json(201, {"ok": True, "mission": {"id": mission_id, "server_id": mission_id, "author": user["name"] or user["nick"], "author_nick": user["nick"], "locality_id": locality_id, "city": user["city"], "oblast": user["oblast"], "title": title, "description": description, "text": description, "category": category, "district": district, "schedule": schedule, "target": target, "status": status, "participant_count": 0, "joined": False, "is_owner": True, "created_at": now}})

    def join_mission(self, mission_id):
        user = self.require_auth()
        try:
            mission_id = int(mission_id)
        except ValueError:
            return self.fail(400, "Некоректна місія")
        with db_lock:
            mission = DB.execute("SELECT * FROM missions WHERE id=?", (mission_id,)).fetchone()
            if mission is None or mission["status"] in ("Завершено", "Скасовано"):
                return self.fail(404, "Місія вже недоступна")
            if mission["user_id"] == user["id"]:
                return self.fail(400, "Організатор не може долучитися до власної місії")
            blocked = DB.execute("SELECT 1 FROM blocked_users WHERE user_id=? AND blocked_id=?", (user["id"], mission["user_id"])).fetchone()
            if blocked:
                return self.fail(403, "Дія недоступна")
            exists = DB.execute("SELECT 1 FROM mission_participants WHERE mission_id=? AND user_id=?", (mission_id, user["id"])).fetchone()
            if exists:
                DB.execute("DELETE FROM mission_participants WHERE mission_id=? AND user_id=?", (mission_id, user["id"]))
                joined = False
            else:
                DB.execute("INSERT INTO mission_participants(mission_id,user_id,joined_at) VALUES(?,?,?)", (mission_id, user["id"], int(time.time())))
                joined = True
            DB.commit()
            count = DB.execute("SELECT COUNT(*) FROM mission_participants WHERE mission_id=?", (mission_id,)).fetchone()[0]
        self.send_json(200, {"ok": True, "joined": joined, "participant_count": count})

    def update_mission_status(self, mission_id):
        user = self.require_auth()
        try:
            mission_id = int(mission_id)
        except ValueError:
            return self.fail(400, "Некоректна місія")
        data = self.read_json()
        if data is None:
            return
        status = clean(data.get("status"), 40)
        if status not in {"Шукаємо учасників", "У процесі", "Завершено", "Скасовано"}:
            return self.fail(400, "Некоректний статус")
        with db_lock:
            cur = DB.execute("UPDATE missions SET status=?, updated_at=? WHERE id=? AND user_id=?", (status, int(time.time()), mission_id, user["id"]))
            if cur.rowcount == 0:
                return self.fail(404, "Місію не знайдено або немає прав")
            DB.commit()
        self.send_json(200, {"ok": True, "status": status})

    def report_mission(self, mission_id):
        user = self.require_auth()
        try:
            mission_id = int(mission_id)
        except ValueError:
            return self.fail(400, "Некоректна місія")
        data = self.read_json()
        if data is None:
            return
        reason = clean(data.get("reason"), 60)
        details = clean(data.get("details"), 500)
        if reason not in {"Спам", "Шахрайство", "Небезпечний вміст", "Неправдива інформація", "Інше"}:
            return self.fail(400, "Обери причину скарги")
        with db_lock:
            if DB.execute("SELECT 1 FROM missions WHERE id=?", (mission_id,)).fetchone() is None:
                return self.fail(404, "Місію не знайдено")
            recent = DB.execute("SELECT 1 FROM mission_reports WHERE reporter_id=? AND mission_id=? AND created_at>?", (user["id"], mission_id, int(time.time()) - 3600)).fetchone()
            if recent:
                return self.fail(429, "Ти вже поскаржився на цю місію")
            DB.execute("INSERT INTO mission_reports(reporter_id,mission_id,reason,details,created_at) VALUES(?,?,?,?,?)", (user["id"], mission_id, reason, details, int(time.time())))
            DB.commit()
        self.send_json(201, {"ok": True})

    def get_market_items(self, query):
        locality_id = clean(query.get("locality_id", [""])[0], 50)
        city = clean(query.get("city", [""])[0], 60)
        category = clean(query.get("category", [""])[0], 40)
        condition = clean(query.get("condition", [""])[0], 40)
        seller = clean(query.get("seller", [""])[0], 40).lstrip("@").lower()
        q = clean(query.get("q", [""])[0], 100).lower()
        status = clean(query.get("status", ["active"])[0], 20)
        sort_by = clean(query.get("sort", ["newest"])[0], 20)
        try:
            min_price = max(0, int(query.get("min_price", ["0"])[0] or 0))
        except (ValueError, TypeError):
            min_price = 0
        try:
            max_price = max(0, int(query.get("max_price", ["0"])[0] or 0))
        except (ValueError, TypeError):
            max_price = 0

        current_user = self.auth()

        # Суворе міське обмеження на рівні сервера:
        # Якщо запит не за конкретним продавцем (профіль продавця), то обовʼязково вимагається locality_id або city!
        if not seller and not locality_id and not city:
            return self.send_json(200, {"items": [], "city": "", "locality_id": "", "total": 0})

        conditions = []
        params = []

        if seller:
            conditions.append("LOWER(seller_nick) = ?")
            params.append(seller)
        else:
            # Ізоляція: тільки оголошення з цього населеного пункту
            if locality_id:
                conditions.append("locality_id = ?")
                params.append(locality_id)
            elif city:
                conditions.append("LOWER(city) = ?")
                params.append(city.lower())

        if status and status != "all":
            conditions.append("status = ?")
            params.append(status)
        else:
            conditions.append("status != 'hidden'")

        if category and category != "all" and category != "Усі":
            conditions.append("category = ?")
            params.append(category)

        if condition and condition != "all" and condition != "Усі":
            conditions.append("condition = ?")
            params.append(condition)

        if min_price > 0:
            conditions.append("price >= ?")
            params.append(min_price)

        if max_price > 0:
            conditions.append("price <= ?")
            params.append(max_price)

        if q:
            esc = q.replace("%", "").replace("_", "\\_")
            conditions.append("(LOWER(title) LIKE ? ESCAPE '\\' OR LOWER(description) LIKE ? ESCAPE '\\')")
            params.extend(["%" + esc + "%", "%" + esc + "%"])

        if current_user:
            # Приховуємо оголошення від заблокованих користувачів
            conditions.append("user_id NOT IN (SELECT blocked_id FROM blocked_users WHERE user_id = ?)")
            params.append(current_user["id"])

        where_clause = " WHERE " + " AND ".join(conditions) if conditions else ""

        if sort_by == "price_asc":
            order_clause = " ORDER BY price ASC, updated_at DESC"
        elif sort_by == "price_desc":
            order_clause = " ORDER BY price DESC, updated_at DESC"
        else:
            order_clause = " ORDER BY updated_at DESC"

        limit_clause = " LIMIT 120"

        with db_lock:
            rows = DB.execute("SELECT * FROM market_items" + where_clause + order_clause + limit_clause, params).fetchall()
            fav_ids = set()
            if current_user:
                fav_rows = DB.execute("SELECT item_id FROM market_favorites WHERE user_id = ?", (current_user["id"],)).fetchall()
                fav_ids = {r["item_id"] for r in fav_rows}

        items = []
        for r in rows:
            item_data = public_market_item(r)
            item_data["is_favorite"] = r["id"] in fav_ids
            items.append(item_data)

        self.send_json(200, {
            "items": items,
            "city": city or (items[0]["city"] if items else ""),
            "locality_id": locality_id,
            "total": len(items)
        })

    def get_market_item(self, item_id):
        try:
            item_id = int(item_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")

        current_user = self.auth()

        with db_lock:
            DB.execute("UPDATE market_items SET views_count = views_count + 1 WHERE id = ?", (item_id,))
            DB.commit()
            item = DB.execute("SELECT * FROM market_items WHERE id = ?", (item_id,)).fetchone()
            if not item:
                return self.fail(404, "Оголошення не знайдено")
            seller = DB.execute("SELECT * FROM users WHERE id = ?", (item["user_id"],)).fetchone()
            rating_row = DB.execute("SELECT AVG(rating) as avg_r, COUNT(id) as c FROM market_reviews WHERE seller_id = ?", (item["user_id"],)).fetchone()
            is_fav = False
            if current_user:
                is_fav = DB.execute("SELECT 1 FROM market_favorites WHERE user_id = ? AND item_id = ?", (current_user["id"], item_id)).fetchone() is not None

        avg_rating = round(float(rating_row["avg_r"] or 5.0), 1) if rating_row and rating_row["c"] > 0 else 5.0
        review_count = int(rating_row["c"] or 0) if rating_row else 0

        res = public_market_item(item)
        res["is_favorite"] = is_fav
        res["seller"] = {
            "uid": seller["uid"] if seller else 0,
            "nick": seller["nick"] if seller else item["seller_nick"],
            "name": seller["name"] if seller else item["seller_name"],
            "city": seller["city"] if seller else item["city"],
            "rating": avg_rating,
            "reviews_count": review_count,
            "has_avatar": seller["avatar"] is not None if seller else False,
            "avatar_v": seller["avatar_v"] if seller else 0,
        }
        self.send_json(200, {"item": res})

    def get_market_photo(self, item_id):
        try:
            item_id = int(item_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")
        with db_lock:
            row = DB.execute("SELECT photo FROM market_items WHERE id = ?", (item_id,)).fetchone()
            if not row or not row["photo"]:
                return self.fail(404, "Немає зображення")
            data = bytes(row["photo"])
        self.send_response(200)
        self.send_header("Content-Type", "image/jpeg")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "public, max-age=86400")
        self.end_headers()
        self.wfile.write(data)

    def create_market_item(self):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        title = clean(data.get("title"), 120)
        desc = clean(data.get("description"), 4000)
        category = clean(data.get("category"), 40)
        condition = clean(data.get("condition"), 40) or "Вживаний"
        district = clean(data.get("district"), 80)
        try:
            price = max(0, int(data.get("price") or 0))
        except (ValueError, TypeError):
            price = 0

        city = clean(data.get("city") or user["city"], 60)
        oblast = clean(data.get("oblast") or user["oblast"], 60)
        locality_id = clean(data.get("locality_id") or user["locality_id"], 40)

        if not title:
            return self.fail(400, "Вкажи назву товару")
        if not category:
            return self.fail(400, "Обери категорію")
        if not locality_id and not city:
            return self.fail(400, "Обери своє місто у профілі перед створенням оголошення")

        now = int(time.time())
        with db_lock:
            cur = DB.execute(
                """INSERT INTO market_items (
                    user_id, seller_nick, seller_name, title, description, price, category, condition,
                    city, oblast, locality_id, district, status, created_at, updated_at
                ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,'active',?,?)""",
                (user["id"], user["nick"], user["name"] or user["nick"], title, desc, price, category,
                 condition, city, oblast, locality_id, district, now, now)
            )
            DB.commit()
            item_id = cur.lastrowid
            row = DB.execute("SELECT * FROM market_items WHERE id = ?", (item_id,)).fetchone()
        self.send_json(201, {"item": public_market_item(row)})

    def update_market_item(self, item_id):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        try:
            item_id = int(item_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")

        with db_lock:
            item = DB.execute("SELECT * FROM market_items WHERE id = ?", (item_id,)).fetchone()
            if not item:
                return self.fail(404, "Оголошення не знайдено")
            if item["user_id"] != user["id"]:
                return self.fail(403, "Це не твоє оголошення")

            title = clean(data.get("title") or item["title"], 120)
            desc = clean(data.get("description") or item["description"], 4000)
            category = clean(data.get("category") or item["category"], 40)
            condition = clean(data.get("condition") or item["condition"], 40)
            district = clean(data.get("district") if "district" in data else item["district"], 80)
            try:
                price = max(0, int(data.get("price") if "price" in data else item["price"]))
            except (ValueError, TypeError):
                price = item["price"]

            now = int(time.time())
            DB.execute(
                """UPDATE market_items SET title=?, description=?, price=?, category=?, condition=?, district=?, updated_at=?
                   WHERE id=?""",
                (title, desc, price, category, condition, district, now, item_id)
            )
            DB.commit()
            row = DB.execute("SELECT * FROM market_items WHERE id = ?", (item_id,)).fetchone()
        self.send_json(200, {"item": public_market_item(row)})

    def upload_market_photo(self, item_id):
        user = self.require_auth()
        if user is None:
            return
        try:
            item_id = int(item_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")
        raw = self.read_body(MAX_IMAGE)
        if raw is None:
            return self.fail(413, "Зображення завелике (максимум 800 КБ)")
        if raw and not raw.startswith(b"\xff\xd8"):
            return self.fail(400, "Потрібен файл JPEG")
        value = raw if raw else None
        with db_lock:
            item = DB.execute("SELECT * FROM market_items WHERE id = ?", (item_id,)).fetchone()
            if not item:
                return self.fail(404, "Оголошення не знайдено")
            if item["user_id"] != user["id"]:
                return self.fail(403, "Це не твоє оголошення")
            DB.execute("UPDATE market_items SET photo = ?, photo_v = photo_v + 1 WHERE id = ?", (value, item_id))
            DB.commit()
        self.send_json(200, {"ok": True})

    def set_market_item_status(self, item_id):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        try:
            item_id = int(item_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")
        new_status = clean(data.get("status"), 20)
        if new_status not in ("active", "sold", "hidden"):
            return self.fail(400, "Недопустимий статус")
        with db_lock:
            item = DB.execute("SELECT * FROM market_items WHERE id = ?", (item_id,)).fetchone()
            if not item:
                return self.fail(404, "Оголошення не знайдено")
            if item["user_id"] != user["id"]:
                return self.fail(403, "Це не твоє оголошення")
            now = int(time.time())
            DB.execute("UPDATE market_items SET status = ?, updated_at = ? WHERE id = ?", (new_status, now, item_id))
            DB.commit()
        self.send_json(200, {"ok": True, "status": new_status})

    def bump_market_item(self, item_id):
        user = self.require_auth()
        if user is None:
            return
        try:
            item_id = int(item_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")
        with db_lock:
            item = DB.execute("SELECT * FROM market_items WHERE id = ?", (item_id,)).fetchone()
            if not item:
                return self.fail(404, "Оголошення не знайдено")
            if item["user_id"] != user["id"]:
                return self.fail(403, "Це не твоє оголошення")
            now = int(time.time())
            DB.execute("UPDATE market_items SET updated_at = ? WHERE id = ?", (now, item_id))
            DB.commit()
        self.send_json(200, {"ok": True, "updated_at": now})

    def delete_market_item(self, item_id):
        user = self.require_auth()
        if user is None:
            return
        try:
            item_id = int(item_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")
        with db_lock:
            item = DB.execute("SELECT * FROM market_items WHERE id = ?", (item_id,)).fetchone()
            if not item:
                return self.fail(404, "Оголошення не знайдено")
            if item["user_id"] != user["id"]:
                return self.fail(403, "Це не твоє оголошення")
            DB.execute("DELETE FROM market_items WHERE id = ?", (item_id,))
            DB.execute("DELETE FROM market_favorites WHERE item_id = ?", (item_id,))
            DB.execute("DELETE FROM market_offers WHERE item_id = ?", (item_id,))
            DB.commit()
        self.send_json(200, {"ok": True})

    def toggle_market_favorite(self, item_id):
        user = self.require_auth()
        if user is None:
            return
        try:
            item_id = int(item_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")
        with db_lock:
            exists = DB.execute("SELECT 1 FROM market_favorites WHERE user_id = ? AND item_id = ?", (user["id"], item_id)).fetchone()
            if exists:
                DB.execute("DELETE FROM market_favorites WHERE user_id = ? AND item_id = ?", (user["id"], item_id))
                fav = False
            else:
                DB.execute("INSERT INTO market_favorites (user_id, item_id, created_at) VALUES (?,?,?)", (user["id"], item_id, int(time.time())))
                fav = True
            DB.commit()
        self.send_json(200, {"favorited": fav})

    def get_market_favorites(self):
        user = self.require_auth()
        if user is None:
            return
        with db_lock:
            rows = DB.execute(
                """SELECT m.* FROM market_items m
                   JOIN market_favorites f ON f.item_id = m.id
                   WHERE f.user_id = ? ORDER BY f.created_at DESC""",
                (user["id"],)
            ).fetchall()
        items = [public_market_item(r) for r in rows]
        for it in items:
            it["is_favorite"] = True
        self.send_json(200, {"items": items})

    def create_market_offer(self, item_id):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        try:
            item_id = int(item_id)
            offer_price = int(data.get("price") or 0)
        except (ValueError, TypeError):
            return self.fail(400, "Некоректні дані")
        if offer_price <= 0:
            return self.fail(400, "Вкажи дійсну ціну")
        message = clean(data.get("message"), 400)
        now = int(time.time())
        with db_lock:
            item = DB.execute("SELECT * FROM market_items WHERE id = ?", (item_id,)).fetchone()
            if not item:
                return self.fail(404, "Оголошення не знайдено")
            if item["user_id"] == user["id"]:
                return self.fail(400, "Не можна торгуватися з самим собою")
            seller = DB.execute("SELECT * FROM users WHERE id = ?", (item["user_id"],)).fetchone()
            if not seller:
                return self.fail(404, "Продавця не знайдено")

            cur = DB.execute(
                """INSERT INTO market_offers (
                    item_id, buyer_id, buyer_nick, buyer_name, seller_id, seller_nick, offer_price, status, message, created_at
                ) VALUES (?,?,?,?,?,?,?,'pending',?,?)""",
                (item["id"], user["id"], user["nick"], user["name"] or user["nick"],
                 seller["id"], seller["nick"], offer_price, message, now)
            )
            # Реальне сповіщення в системі повідомлень, щоб продавець одразу побачив чат!
            extra = f"\nКоментар: {message}" if message else ""
            alert_text = f"🤝 [Пропозиція ціни на UKRA Market]\nТовар: «{item['title']}»\nПропонована ціна: {offer_price} ₴ (початкова: {item['price']} ₴){extra}"
            DB.execute("INSERT INTO messages (from_id, to_id, text, ts) VALUES (?,?,?,?)", (user["id"], seller["id"], alert_text, now))
            DB.commit()
            offer_id = cur.lastrowid
        self.send_json(201, {"ok": True, "offer_id": offer_id})

    def get_market_offers(self):
        user = self.require_auth()
        if user is None:
            return
        with db_lock:
            in_rows = DB.execute(
                """SELECT o.*, m.title as item_title, m.price as item_price, m.city as item_city
                   FROM market_offers o JOIN market_items m ON m.id = o.item_id
                   WHERE o.seller_id = ? ORDER BY o.created_at DESC LIMIT 50""",
                (user["id"],)
            ).fetchall()
            out_rows = DB.execute(
                """SELECT o.*, m.title as item_title, m.price as item_price, m.city as item_city
                   FROM market_offers o JOIN market_items m ON m.id = o.item_id
                   WHERE o.buyer_id = ? ORDER BY o.created_at DESC LIMIT 50""",
                (user["id"],)
            ).fetchall()

        def parse_offer(r):
            return {
                "id": r["id"], "item_id": r["item_id"], "item_title": r["item_title"],
                "item_price": r["item_price"], "item_city": r["item_city"],
                "buyer_id": r["buyer_id"], "buyer_nick": r["buyer_nick"], "buyer_name": r["buyer_name"],
                "seller_id": r["seller_id"], "seller_nick": r["seller_nick"],
                "offer_price": r["offer_price"], "status": r["status"],
                "message": r["message"], "created_at": r["created_at"]
            }

        self.send_json(200, {
            "incoming": [parse_offer(r) for r in in_rows],
            "outgoing": [parse_offer(r) for r in out_rows]
        })

    def respond_market_offer(self, offer_id):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        try:
            offer_id = int(offer_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")
        new_status = clean(data.get("status"), 20)
        if new_status not in ("accepted", "rejected"):
            return self.fail(400, "Некоректний статус відповіді")

        with db_lock:
            offer = DB.execute("SELECT * FROM market_offers WHERE id = ?", (offer_id,)).fetchone()
            if not offer:
                return self.fail(404, "Пропозицію не знайдено")
            if offer["seller_id"] != user["id"]:
                return self.fail(403, "Це не твоя пропозиція")
            now = int(time.time())
            DB.execute("UPDATE market_offers SET status = ? WHERE id = ?", (new_status, offer_id))
            item = DB.execute("SELECT title FROM market_items WHERE id = ?", (offer["item_id"],)).fetchone()
            item_title = item["title"] if item else "Товар"
            # Сповіщення покупцю
            action_ua = "прийняв вашу пропозицію" if new_status == "accepted" else "відхилив вашу пропозицію"
            msg = f"🤝 [Відповідь на пропозицію ціни]\nПродавець @{user['nick']} {action_ua} {offer['offer_price']} ₴ за «{item_title}»."
            DB.execute("INSERT INTO messages (from_id, to_id, text, ts) VALUES (?,?,?,?)", (user["id"], offer["buyer_id"], msg, now))
            DB.commit()
        self.send_json(200, {"ok": True, "status": new_status})

    def add_market_review(self):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        seller_query = clean(data.get("seller"), 50)
        target = find_user(seller_query)
        if not target:
            return self.fail(404, "Продавця не знайдено")
        if target["id"] == user["id"]:
            return self.fail(400, "Не можна залишати відгук самому собі")
        try:
            rating = max(1, min(5, int(data.get("rating") or 5)))
        except (ValueError, TypeError):
            rating = 5
        comment = clean(data.get("comment"), 1000)
        try:
            item_id = int(data.get("item_id") or 0)
        except (ValueError, TypeError):
            item_id = 0
        now = int(time.time())
        with db_lock:
            DB.execute(
                """INSERT INTO market_reviews (seller_id, seller_nick, buyer_id, buyer_nick, buyer_name, item_id, rating, comment, created_at)
                   VALUES (?,?,?,?,?,?,?,?,?)""",
                (target["id"], target["nick"], user["id"], user["nick"], user["name"] or user["nick"], item_id, rating, comment, now)
            )
            DB.commit()
        self.send_json(201, {"ok": True})

    def get_seller_profile(self, query):
        seller = find_user(query)
        if not seller:
            return self.fail(404, "Продавця не знайдено")
        with db_lock:
            active_items = DB.execute("SELECT * FROM market_items WHERE user_id = ? AND status = 'active' ORDER BY updated_at DESC", (seller["id"],)).fetchall()
            sold_items = DB.execute("SELECT * FROM market_items WHERE user_id = ? AND status = 'sold' ORDER BY updated_at DESC", (seller["id"],)).fetchall()
            reviews = DB.execute("SELECT * FROM market_reviews WHERE seller_id = ? ORDER BY created_at DESC LIMIT 50", (seller["id"],)).fetchall()
            rating_row = DB.execute("SELECT AVG(rating) as avg_r, COUNT(id) as c FROM market_reviews WHERE seller_id = ?", (seller["id"],)).fetchone()

        avg_rating = round(float(rating_row["avg_r"] or 5.0), 1) if rating_row and rating_row["c"] > 0 else 5.0
        review_count = int(rating_row["c"] or 0) if rating_row else 0

        self.send_json(200, {
            "seller": public_user(seller),
            "rating": avg_rating,
            "reviews_count": review_count,
            "active_items": [public_market_item(r) for r in active_items],
            "sold_items": [public_market_item(r) for r in sold_items],
            "reviews": [
                {
                    "id": r["id"],
                    "buyer_nick": r["buyer_nick"],
                    "buyer_name": r["buyer_name"],
                    "rating": r["rating"],
                    "comment": r["comment"],
                    "created_at": r["created_at"]
                } for r in reviews
            ]
        })

    def report_market_item(self, item_id):
        user = self.require_auth()
        if user is None:
            return
        data = self.read_json()
        if data is None:
            return
        try:
            item_id = int(item_id)
        except ValueError:
            return self.fail(400, "Некоректний ID")
        reason = clean(data.get("reason"), 100)
        details = clean(data.get("details"), 1000)
        if not reason:
            return self.fail(400, "Вкажи причину скарги")
        now = int(time.time())
        with db_lock:
            DB.execute(
                "INSERT INTO market_reports (reporter_id, item_id, reason, details, created_at) VALUES (?,?,?,?,?)",
                (user["id"], item_id, reason, details, now)
            )
            DB.commit()
        self.send_json(201, {"ok": True, "message": "Скаргу прийнято. Дякуємо за допомогу у безпеці громади!"})

    def toggle_block_user(self, query):
        user = self.require_auth()
        if user is None:
            return
        target = find_user(query)
        if not target:
            return self.fail(404, "Користувача не знайдено")
        if target["id"] == user["id"]:
            return self.fail(400, "Не можна заблокувати самого себе")
        with db_lock:
            exists = DB.execute("SELECT 1 FROM blocked_users WHERE user_id = ? AND blocked_id = ?", (user["id"], target["id"])).fetchone()
            if exists:
                DB.execute("DELETE FROM blocked_users WHERE user_id = ? AND blocked_id = ?", (user["id"], target["id"]))
                blocked = False
            else:
                DB.execute("INSERT INTO blocked_users (user_id, blocked_id, created_at) VALUES (?,?,?)", (user["id"], target["id"], int(time.time())))
                blocked = True
            DB.commit()
        self.send_json(200, {"blocked": blocked})

    def get_blocked_users(self):
        user = self.require_auth()
        if user is None:
            return
        with db_lock:
            rows = DB.execute(
                """SELECT u.id, u.nick, u.name FROM users u
                   JOIN blocked_users b ON b.blocked_id = u.id
                   WHERE b.user_id = ?""",
                (user["id"],)
            ).fetchall()
        self.send_json(200, {"blocked": [{"id": r["id"], "nick": r["nick"], "name": r["name"]} for r in rows]})


def lan_ips():
    """Локальні IP цього комп'ютера (для підказки, яку адресу вписати)."""
    ips = set()
    try:
        probe = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        probe.connect(("10.255.255.255", 1))  # пакет не надсилається, лише визначається інтерфейс
        ips.add(probe.getsockname()[0])
        probe.close()
    except OSError:
        pass
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ips.add(info[4][0])
    except OSError:
        pass
    return sorted(ip for ip in ips if not ip.startswith("127."))


def main():
    parser = argparse.ArgumentParser(description="Сервер UKRA")
    parser.add_argument("--host", default=os.environ.get("HOST", "127.0.0.1"))
    parser.add_argument("--port", type=int, default=int(os.environ.get("PORT", "8080")))
    parser.add_argument("--db", default=os.environ.get("UKRA_DB", "ukra.db"))
    args = parser.parse_args()
    init_db(args.db)
    server = ThreadingHTTPServer((args.host, args.port), Handler)
    print(f"UKRA сервер запущено (база: {args.db})")
    if args.host in ("0.0.0.0", ""):
        for ip in lan_ips():
            print(f"  Адреса для застосунку: http://{ip}:{args.port}")
        print("  Вставте одну з цих адрес у застосунок (Профіль → «Нікнейм»).")
    else:
        print(f"  Адреса: http://{args.host}:{args.port} (для телефона запускай з --host 0.0.0.0)")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
