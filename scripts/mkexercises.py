#!/usr/bin/env python3
"""Generate the exercise tree (master) from the solution tree (solutions branch).

Usage: scripts/mkexercises.py SRC_WORKTREE DST_WORKTREE

In tracked files, a block

    <indent>--<sol
    ...solution lines...
    <indent>--|ex                (optional)
    <indent>--| exercise line    (each line of the exercise version)
    <indent>--sol>

becomes the exercise lines (with `--| ` stripped), or `<indent>sorry` when there is
no `--|ex` part. An empty `--|ex` part deletes the block (solution-only helpers). Files listed in .solutions-only are not copied. Tracked files in DST
that no longer exist in SRC are deleted.
"""
import os, re, subprocess, sys

BEGIN = re.compile(r"^(\s*)--<sol\s*$")
EX = re.compile(r"^\s*--\|ex\s*$")
EXLINE = re.compile(r"^(\s*)--\|(?: (.*))?$")
END = re.compile(r"^\s*--sol>\s*$")


def strip(text: str, path: str) -> str:
    out, lines, i = [], text.split("\n"), 0
    while i < len(lines):
        m = BEGIN.match(lines[i])
        if not m:
            if "--sol>" in lines[i] or "--|ex" in lines[i]:
                sys.exit(f"{path}:{i+1}: stray marker")
            out.append(lines[i]); i += 1; continue
        indent, start = m.group(1), i
        i += 1
        ex, in_ex = [], False
        while i < len(lines) and not END.match(lines[i]):
            if BEGIN.match(lines[i]):
                sys.exit(f"{path}:{i+1}: nested --<sol")
            if EX.match(lines[i]):
                in_ex = True
            elif in_ex:
                em = EXLINE.match(lines[i])
                if not em:
                    sys.exit(f"{path}:{i+1}: exercise lines must start with --|")
                ex.append(em.group(1) + (em.group(2) or "") if em.group(2) else "")
            i += 1
        if i == len(lines):
            sys.exit(f"{path}:{start+1}: unterminated --<sol")
        if not in_ex and indent == "":
            sys.exit(f"{path}:{start+1}: top-level block needs an --|ex part (empty to delete)")
        out.extend(ex if in_ex else [indent + "sorry"])
        i += 1
    return "\n".join(out)


def tracked(root):
    r = subprocess.run(["git", "-C", root, "ls-files"], capture_output=True, text=True, check=True)
    return set(r.stdout.split())


def main(src, dst):
    only = set()
    p = os.path.join(src, ".solutions-only")
    if os.path.exists(p):
        only = {l.strip() for l in open(p) if l.strip() and not l.startswith("#")}
    files = {f for f in tracked(src) if f not in only and f != ".solutions-only"}
    for f in sorted(files):
        with open(os.path.join(src, f), "rb") as h:
            data = h.read()
        if f.endswith(".lean"):
            data = strip(data.decode(), f).encode()
        target = os.path.join(dst, f)
        os.makedirs(os.path.dirname(target) or ".", exist_ok=True)
        with open(target, "wb") as h:
            h.write(data)
    for f in tracked(dst) - files:
        os.remove(os.path.join(dst, f))
        print("deleted", f)


if __name__ == "__main__":
    main(*sys.argv[1:3])
