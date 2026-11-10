#!/usr/bin/env python3
"""Play the editor for an end-to-end test of `wiz lsp --infoview SOCK`: start the server
with the socket, open FILE, put the cursor at LINE:COL (0-based) with a hover, run
CMD... (an infoview pointed at SOCK) and print its output, then shut the server down.
    usage: editor_stub.py WIZ SOCK FILE LINE COL -- CMD..."""
import json, os, subprocess, sys, time

def frame(obj):
    body = json.dumps(obj).encode()
    return b"Content-Length: %d\r\n\r\n" % len(body) + body

def main():
    wiz, sock, path, line, col = sys.argv[1:6]
    cmd = sys.argv[sys.argv.index("--") + 1:]
    uri = "file://" + os.path.abspath(path)
    srv = subprocess.Popen([wiz, "lsp", "--infoview", sock], stdin=subprocess.PIPE,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    send = lambda m: (srv.stdin.write(frame(m)), srv.stdin.flush())
    send({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}})
    send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
    send({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
        "uri": uri, "languageId": "wiz", "version": 1, "text": open(path).read()}}})
    send({"jsonrpc": "2.0", "id": 2, "method": "textDocument/hover", "params": {
        "textDocument": {"uri": uri}, "position": {"line": int(line), "character": int(col)}}})
    for _ in range(100):
        if os.path.exists(sock): break
        time.sleep(0.1)
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    sys.stdout.write(out.stdout)
    send({"jsonrpc": "2.0", "id": 3, "method": "shutdown", "params": None})
    send({"jsonrpc": "2.0", "method": "exit", "params": None})
    srv.stdin.close()
    srv.wait(timeout=30)
    sys.exit(out.returncode)

main()
