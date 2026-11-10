#!/usr/bin/env python3
"""Drive the terminal infoview in a pseudo-terminal and print the screen it leaves.
    usage: pty_test.py COLS ROWS KEYS -- PROGRAM ARGS...
KEYS is a Python string literal (escapes allowed), sent a character group at a time
(split on '|'), with a pause before each. A tiny terminal emulator applies the cursor
moves (CSI H), clears (CSI K, CSI J) and drops colours (CSI m), so the result is the
text on the screen, one line per row, trailing spaces removed."""
import ast, fcntl, os, pty, re, select, struct, sys, termios, time

def run(cols, rows, keys, argv):
    pid, fd = pty.fork()
    if pid == 0:
        os.execvp(argv[0], argv)
    fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, 0, 0))
    os.kill(pid, 28)  # SIGWINCH, in case it started before the size was set
    out = b""
    def pump(t):
        nonlocal out
        end = time.time() + t
        while time.time() < end:
            r, _, _ = select.select([fd], [], [], 0.05)
            if r:
                try: out += os.read(fd, 65536)
                except OSError: return False
        return True
    pump(1.5)
    for k in keys:
        os.write(fd, k.encode()); pump(0.7)
    pump(0.5)
    try: os.kill(pid, 15)
    except ProcessLookupError: pass
    return out.decode("utf-8", "replace")

def screen(text, cols, rows):
    grid = [[" "] * cols for _ in range(rows)]
    r = c = 0
    i = 0
    alt_seen = False
    while i < len(text):
        ch = text[i]
        if ch == "\x1b":
            m = re.match(r"\x1b\[([?0-9;<]*)([A-Za-z~])", text[i:])
            if not m: i += 1; continue
            args, cmd = m.group(1), m.group(2)
            if cmd == "H":
                p = [int(x) if x else 1 for x in args.split(";")] if args else [1, 1]
                r, c = p[0] - 1, (p[1] - 1 if len(p) > 1 else 0)
            elif cmd == "K":
                for x in range(c, cols): grid[min(r, rows - 1)][x] = " "
            elif cmd == "J":
                grid = [[" "] * cols for _ in range(rows)]
            elif cmd == "l" and args == "?1049":
                break   # left the alternate screen: what was on it is the result
            i += len(m.group(0)); continue
        if ch == "\r": c = 0
        elif ch == "\n": r += 1
        elif 0 <= r < rows and 0 <= c < cols:
            grid[r][c] = ch; c += 1
        i += 1
    return "\n".join("".join(row).rstrip() for row in grid)

if __name__ == "__main__":
    cols, rows = int(sys.argv[1]), int(sys.argv[2])
    keys = ast.literal_eval("'" + sys.argv[3] + "'").split("|") if sys.argv[3] else []
    argv = sys.argv[sys.argv.index("--") + 1:]
    print(screen(run(cols, rows, keys, argv), cols, rows))
