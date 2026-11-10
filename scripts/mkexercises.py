#!/usr/bin/env python3
"""Generate the exercise tree from the solution tree (a checkout of master).

Usage: scripts/mkexercises.py SRC_WORKTREE DST

DST is a new or empty directory, or a git worktree of an earlier exercise tree, which
is updated in place (see docs/exercises.md).

In tracked files, a block

    <indent>--<sol
    ...solution lines...
    <indent>--|ex                (optional)
    <indent>--| exercise line    (each line of the exercise version)
    <indent>--sol>

becomes the exercise lines (with `--| ` stripped), or `<indent>sorry` when there is
no `--|ex` part. An empty `--|ex` part deletes the block (solution-only helpers).
Files listed in .solutions-only are not copied. When DST is a git worktree, it must be
clean, and its tracked files that no longer exist in SRC are deleted.
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


def is_worktree(d):
    """Is `d` the top of a git worktree (not a directory inside another one)?"""
    if not os.path.isdir(d):
        return False
    r = subprocess.run(["git", "-C", d, "rev-parse", "--show-toplevel"],
                       capture_output=True, text=True)
    return r.returncode == 0 and os.path.realpath(r.stdout.strip()) == os.path.realpath(d)


def main(src, dst):
    git_dst = is_worktree(dst)
    if git_dst:
        dirty = subprocess.run(["git", "-C", dst, "status", "--porcelain"],
                               capture_output=True, text=True, check=True).stdout.strip()
        if dirty:
            sys.exit(f"{dst} has uncommitted changes; refusing to overwrite them:\n{dirty}")
    elif os.path.isdir(dst) and os.listdir(dst):
        sys.exit(f"{dst} is neither empty nor a git worktree; refusing to write into it")
    only = set()
    p = os.path.join(src, ".solutions-only")
    if os.path.exists(p):
        only = {l.strip() for l in open(p) if l.strip() and not l.startswith("#")}
    files = {f for f in tracked(src) if f not in only and f != ".solutions-only"}
    for f in sorted(files):
        with open(os.path.join(src, f), "rb") as h:
            data = h.read()
        if f.endswith((".lean", ".wiz")):
            data = strip(data.decode(), f).encode()
        target = os.path.join(dst, f)
        os.makedirs(os.path.dirname(target) or ".", exist_ok=True)
        with open(target, "wb") as h:
            h.write(data)
    for f in (tracked(dst) if git_dst else set()) - files:
        os.remove(os.path.join(dst, f))
        print("deleted", f)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__.split("\n\n")[1])
    main(*sys.argv[1:3])
