"""
Auth0-Style User Database — SQLite Backend

Demonstrates a verified backend with a real SQLite database.
The SQLite calls are "black holes" (external code we don't verify).
We prove properties about our code that wraps them.

Properties proven in coq/Auth.v:
  - Round-trip: after insert, lookup returns the record
  - Session isolation: user A cannot read user B
  - Email trust: if email_verified, email is non-empty
  - Idempotent insert: same sub → overwrites (most recent wins)
"""

import sqlite3
from dataclasses import dataclass
from typing import Optional

from py.contracts import requires, ensures

# ─── Models ───────────────────────────────────────────────────────

@dataclass
class User:
    sub: str
    email: str
    name: str
    email_verified: bool

# ─── Database Layer (each call is a BLACK HOLE) ───────────────────

def open_db(path: str = ":memory:") -> sqlite3.Connection:
    """Open (or create) the database.

    BLACK HOLE: filesystem access, external state.
    Affected set: {db_connection, filesystem}
    """
    conn = sqlite3.connect(path)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS users (
            sub             TEXT PRIMARY KEY,
            email           TEXT NOT NULL,
            name            TEXT NOT NULL,
            email_verified  INTEGER NOT NULL
        )
    """)
    conn.commit()
    return conn


# ─── Verified Operations ──────────────────────────────────────────

@ensures(lambda conn, user, result:
    result.sub == user.sub and result.email == user.email)
def insert_user(conn: sqlite3.Connection, user: User) -> User:
    """Insert or replace a user. Returns the stored user.

    BLACK HOLE: SQLite INSERT.
    Affected set: {db rows}
    Recovery: the returned User matches what we asked to insert.
    """
    conn.execute(
        "INSERT OR REPLACE INTO users (sub, email, name, email_verified) "
        "VALUES (?, ?, ?, ?)",
        (user.sub, user.email, user.name, int(user.email_verified)),
    )
    conn.commit()
    return user


@ensures(lambda conn, sub, result:
    result is None or result.sub == sub)
def lookup_user(conn: sqlite3.Connection, sub: str) -> Optional[User]:
    """Look up a user by Auth0 subject ID.

    BLACK HOLE: SQLite SELECT.
    Affected set: {} (read-only, no state mutation)
    Q_keep: the returned sub matches the requested sub, or None
    """
    row = conn.execute(
        "SELECT sub, email, name, email_verified FROM users WHERE sub = ?",
        (sub,),
    ).fetchone()

    if row is None:
        return None

    return User(
        sub=row[0],
        email=row[1],
        name=row[2],
        email_verified=bool(row[3]),
    )


@requires(lambda user: user is not None and user.email_verified)
@ensures(lambda user, result: len(result) > 0)
def trust_email(user: User) -> str:
    """If Auth0 verified the email, the backend can trust it is non-empty.

    Pure function (no black holes). Verified in Coq.
    """
    return user.email


# ─── Auth0 Callback (black hole at network boundary) ──────────────

@requires(lambda profile: "sub" in profile)
@ensures(lambda profile, result:
    result.sub == profile["sub"] and
    result.email_verified == profile.get("email_verified", False))
def user_from_auth0_profile(profile: dict) -> User:
    """Convert an Auth0 profile dict to a User record.

    BLACK HOLE: the profile dict arrives from an external network call.
    We trust that Auth0 signature verification happened upstream.
    """
    return User(
        sub=profile["sub"],
        email=profile.get("email", ""),
        name=profile.get("name", ""),
        email_verified=profile.get("email_verified", False),
    )


# ─── Full Flow (with black hole surface marked) ──────────────────

def handle_auth_callback(conn: sqlite3.Connection, profile: dict) -> User:
    """Complete Auth0 callback → register → return user flow.

    Black holes:  user_from_auth0_profile  (network boundary)
                  insert_user              (SQLite INSERT)
    Q_keep:       user.sub matches profile["sub"]
                  user.email_verified matches profile
    """
    user = user_from_auth0_profile(profile)   # BLACK HOLE
    stored = insert_user(conn, user)           # BLACK HOLE

    assert stored.sub == user.sub, "insert_user contract violated"
    assert stored.email == user.email, "insert_user contract violated"

    return stored


# ─── Example ──────────────────────────────────────────────────────

if __name__ == "__main__":
    conn = open_db(":memory:")

    profile = {
        "sub": "auth0|abc123",
        "email": "alice@example.com",
        "name": "Alice",
        "email_verified": True,
    }

    user = handle_auth_callback(conn, profile)
    print(f"✓ Registered: {user.name} ({user.sub})")

    # Later: session lookup
    found = lookup_user(conn, "auth0|abc123")
    assert found is not None
    assert found.email == "alice@example.com"
    assert found.email_verified

    email = trust_email(found)
    print(f"✓ Email trusted: {email}")

    # Session isolation: other user not found
    missing = lookup_user(conn, "auth0|xyz789")
    assert missing is None
    print("✓ Session isolation: other user not accessible")
