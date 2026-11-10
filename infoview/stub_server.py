#!/usr/bin/env python3
"""A stand-in for `wiz lsp --infoview SOCK` (infoview-protocol.md §8), for testing the
infoviews before the server has these methods: it listens on SOCK, sends one
`wiz/infoview/cursor`, and answers the infoview's requests with canned goals. With
--stdio it is a language server on stdin/stdout instead (for web/node_test.mjs).
    usage: stub_server.py SOCK [--once] | stub_server.py --stdio"""
import json, os, socket, sys

GOALS = {"session": 3, "range": {"start": {"line": 3, "character": 2}, "end": {"line": 3, "character": 9}},
         "goals": [{"userName": None, "goalPrefix": "⊢ ",
                    "hyps": [{"names": ["A"], "type": {"tag": [{"ref": 1, "kind": "sort"}, {"text": "Type"}]}, "val": None},
                             {"names": ["x"], "type": {"tag": [{"ref": 2, "kind": "var", "name": "A"}, {"text": "A"}]}, "val": None}],
                    "type": {"tag": [{"ref": 4, "kind": "pi"}, {"append": [
                        {"tag": [{"ref": 5, "kind": "const", "name": "Nat"}, {"text": "Nat"}]},
                        {"text": " → "},
                        {"tag": [{"ref": 6, "kind": "var", "name": "A"}, {"text": "A"}]}]}]}}]}
INFO = {"text": "Nat", "kind": "const", "name": "Nat", "session": 3,
        "type": {"tag": [{"ref": 7, "kind": "sort"}, {"text": "Type"}]},
        "definition": {"uri": "file:///lib/Prelude.wiz", "range": {"start": {"line": 6, "character": 0}, "end": {"line": 6, "character": 9}}}}

def frame(obj):
    body = json.dumps(obj, ensure_ascii=False).encode()
    return b"Content-Length: %d\r\n\r\n" % len(body) + body

def messages(conn):
    buf = b""
    recv = conn.recv if hasattr(conn, "recv") else (lambda n: os.read(0, n))
    while True:
        while b"\r\n\r\n" in buf:
            head, rest = buf.split(b"\r\n\r\n", 1)
            n = int([l for l in head.split(b"\r\n") if l.lower().startswith(b"content-length:")][0].split(b":")[1])
            if len(rest) < n: break
            yield json.loads(rest[:n]); buf = rest[n:]
        data = recv(65536)
        if not data: return
        buf += data

def answer(m):
    return {"wiz/interactiveGoals": GOALS, "wiz/interactiveTermGoal": None, "wiz/subtermInfo": INFO,
            "initialize": {"capabilities": {}}}.get(m.get("method"))

def stdio():
    for m in messages(None):
        if "id" in m:
            os.write(1, frame({"jsonrpc": "2.0", "id": m["id"], "result": answer(m)}))

def main():
    if sys.argv[1] == "--stdio": return stdio()
    path = sys.argv[1]
    if os.path.exists(path): os.unlink(path)
    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); srv.bind(path); srv.listen(1)
    while True:
        conn, _ = srv.accept()
        conn.sendall(frame({"jsonrpc": "2.0", "method": "wiz/infoview/cursor", "params": {
            "textDocument": {"uri": "file:///tmp/t.wiz"}, "position": {"line": 3, "character": 4}, "session": 3}}))
        for m in messages(conn):
            if "id" in m: conn.sendall(frame({"jsonrpc": "2.0", "id": m["id"], "result": answer(m)}))
        conn.close()
        if "--once" in sys.argv: break
    os.unlink(path)

main()
