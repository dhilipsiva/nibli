"""Lossless private records with a disposable SQLite FTS5 search index."""
import datetime
import json
import os
from pathlib import Path
import re
import sqlite3


class Memory:
    def __init__(self, root):
        self.root = Path(root).absolute()
        if self.root.resolve() != self.root or str(self.root).startswith('/nix/store/'):
            raise ValueError('Private memory must be outside symlinks and the Nix store')
        if any((p / '.git').is_file() or (p / '.git/HEAD').exists() or (p / 'flake.nix').exists()
               for p in (self.root, *self.root.parents)):
            raise ValueError('Private memory must be outside repositories and Nix sources')
        self.db = None

    def open(self):
        if self.db is None:
            self.root.mkdir(mode=0o700, parents=True, exist_ok=True)
            os.chmod(self.root, 0o700)
            path = self.root / 'conversations.sqlite3'
            if path.is_symlink():
                raise ValueError('Refusing a symlinked private archive')
            self.db = sqlite3.connect(path, check_same_thread=False)
            os.chmod(path, 0o600)
            self.db.executescript('''
                PRAGMA journal_mode=WAL;
                CREATE TABLE IF NOT EXISTS messages (
                    id TEXT PRIMARY KEY, source TEXT NOT NULL, session TEXT NOT NULL,
                    role TEXT NOT NULL, text TEXT NOT NULL, payload TEXT NOT NULL
                );
                CREATE VIRTUAL TABLE IF NOT EXISTS recall USING fts5(id UNINDEXED, text);
            ''')
        return self.db

    def record(self, record):
        # No inferred facts, tool internals or reasoning are conversation records.
        required = ('id', 'source', 'session', 'role', 'text')
        if any(not isinstance(record.get(k), str) for k in required):
            raise ValueError('Records require string id, source, session, role and text')
        if not record['id'] or record['role'] not in ('user', 'assistant'):
            raise ValueError('Invalid conversation record')
        db = self.open()
        old = db.execute('SELECT payload FROM messages WHERE id=?', (record['id'],)).fetchone()
        if old:
            saved = json.loads(old[0])
            if any(saved.get(k) != v for k, v in record.items()):
                raise ValueError('Record ID reused with different content')
            return saved
        record = dict(record)
        record.setdefault('timestamp', datetime.datetime.now(datetime.timezone.utc).isoformat())
        record.setdefault('timestamp_kind', 'capture')
        record.setdefault('channel', record['role'])
        record['private'] = True
        with db:
            db.execute('INSERT INTO messages VALUES (?,?,?,?,?,?)',
                       tuple(record[k] for k in required) + (json.dumps(record, ensure_ascii=False),))
            db.execute('INSERT INTO recall VALUES (?,?)', (record['id'], record['text']))
        return record

    def search(self, query, exclude=None):
        words = list(dict.fromkeys(re.findall(r'\w{3,}', query.lower())))[:16]
        if not words:
            return []
        expr = ' OR '.join('"' + w + '"' for w in words)
        rows = self.open().execute('''
            SELECT m.payload, snippet(recall,1,'','', ' … ',48)
            FROM recall JOIN messages m ON m.id=recall.id
            WHERE recall MATCH ? AND m.id != ? ORDER BY rank LIMIT 4
        ''', (expr, exclude or '')).fetchall()
        return [dict(id=(r := json.loads(payload))['id'], source=r['source'],
                     session=r['session'], role=r['role'], excerpt=excerpt[:1200])
                for payload, excerpt in rows]

    def transcript(self, source, session):
        return [json.loads(r[0]) for r in self.open().execute(
            'SELECT payload FROM messages WHERE source=? AND session=? ORDER BY rowid',
            (source, session))]

    def rebuild(self):
        db = self.open()
        with db:
            db.execute('DELETE FROM recall')
            db.execute('INSERT INTO recall SELECT id,text FROM messages')
