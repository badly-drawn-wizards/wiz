#!/usr/bin/env python3
"""Helpers for .github/workflows/ci.yml.

  scripts/ci.py matrix               the shards of .github/test-shards.json as a JSON
                                     matrix (one line, for $GITHUB_OUTPUT); each shard's
                                     selectors are joined by newlines
  scripts/ci.py check-shards [BIN]   check that every test group (BIN --list; default
                                     .lake/build/bin/tests) is run by exactly one shard,
                                     and that every selector of a shard selects something
  scripts/ci.py summary TITLE LOG..  a Markdown summary of `lake test` logs (per-group
                                     pass/fail counts and the failing cases), for
                                     $GITHUB_STEP_SUMMARY
  scripts/ci.py check-include-str BASE
                                     Lake doesn't track `include_str`: fail if a file a
                                     .lean file embeds changed since BASE (a commit) and
                                     the .lean file didn't (bump its counter comment)

Selectors are the arguments of `lake test --`: `=NAME` selects the group NAME, anything
else is a prefix of group names (see Tests/Main.lean).
"""
import json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SHARDS = os.path.join(ROOT, ".github", "test-shards.json")


def shards():
    with open(SHARDS) as f:
        return json.load(f)


def selects(group, sel):
    return group == sel[1:] if sel.startswith("=") else group.startswith(sel)


def matrix():
    print(json.dumps({"shard": [{"name": s["name"], "select": "\n".join(s["select"])}
                                for s in shards()]}, ensure_ascii=False))


def check_shards(binary):
    out = subprocess.run([binary, "--list"], capture_output=True, text=True, check=True).stdout
    groups = [g for g in out.split("\n") if g]
    errors = []
    runs = {g: [] for g in groups}
    names = set()
    for s in shards():
        if s["name"] in names:
            errors.append(f"shard name {s['name']!r} is used twice")
        names.add(s["name"])
        picked = set()   # a group selected twice within a shard still runs once
        for sel in s["select"]:
            hit = [g for g in groups if selects(g, sel)]
            if not hit:
                errors.append(f"shard {s['name']!r}: selector {sel!r} selects no group")
            picked.update(hit)
        for g in picked:
            runs[g].append(s["name"])
    for g, by in runs.items():
        if not by:
            errors.append(f"group {g!r} is in no shard: add it to .github/test-shards.json")
        elif len(by) > 1:
            errors.append(f"group {g!r} is run by several shards: {', '.join(by)}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"ok: {len(groups)} groups, each in exactly one of {len(names)} shards")
    return 0


GROUP = re.compile(r"^── (.*) \((.*)\)$")
PASS = re.compile(r"^  ✓ (.*)$")
FAIL = re.compile(r"^  ✗ (.*)$")
TIME = re.compile(r"^  \((.*): (\d+) s\)$")
TOTAL = re.compile(r"^(\d+) passed, (\d+) failed$")


def parse_log(path):
    """(groups, total) of one `lake test` log; groups: [name, passed, failed, seconds,
    [(case, detail)]]; total: (passed, failed), or None if the driver did not finish."""
    groups, total = [], None
    lines = open(path, encoding="utf-8", errors="replace").read().split("\n")
    for i, line in enumerate(lines):
        if m := GROUP.match(line):
            groups.append([m.group(1), 0, 0, None, []])
        elif groups and PASS.match(line):
            groups[-1][1] += 1
        elif groups and (m := FAIL.match(line)):
            groups[-1][2] += 1
            detail = []
            for l in lines[i + 1:i + 6]:
                if not l.startswith("      "):
                    break
                detail.append(l.strip())
            groups[-1][4].append((m.group(1), " ".join(detail)[:300].replace("`", "'")))
        elif groups and (m := TIME.match(line)):
            groups[-1][3] = m.group(2)
        elif m := TOTAL.match(line):
            total = (int(m.group(1)), int(m.group(2)))
    return groups, total


def summary(title, logs):
    groups, passed, failed, unfinished = [], 0, 0, []
    for log in logs:
        g, total = parse_log(log)
        groups += g
        if total is None:
            unfinished.append(os.path.basename(log))
        else:
            passed, failed = passed + total[0], failed + total[1]
    out = [f"### {title}", ""]
    mark = "✅" if failed == 0 and not unfinished and logs else "❌"
    out.append(f"{mark} **{passed} passed, {failed} failed**")
    if unfinished:
        out.append(f"\n**The test driver did not finish** in: {', '.join(unfinished)} (see the log).")
    if not logs:
        out.append("\nNo test logs.")
    out += ["", "| group | passed | failed | time |", "|---|---:|---:|---:|"]
    for name, p, f, t, _ in groups:
        out.append(f"| {name} | {p} | {f} | {t + ' s' if t else ''} |")
    fails = [(g[0], c, d) for g in groups for c, d in g[4]]
    if fails:
        out += ["", "<details><summary>failing cases</summary>", ""]
        out += [f"- **{g}**: {c}" + (f" — `{d}`" if d else "") for g, c, d in fails[:200]]
        out += ["", "</details>"]
    print("\n".join(out))
    return 0


def check_include_str(base):
    changed = set(subprocess.run(["git", "diff", "--name-only", base, "HEAD"], cwd=ROOT,
                                 capture_output=True, text=True, check=True).stdout.split())
    lean = subprocess.run(["git", "grep", "-l", "include_str", "--", "*.lean"], cwd=ROOT,
                          capture_output=True, text=True).stdout.split()
    errors = []
    for f in lean:
        with open(os.path.join(ROOT, f)) as h:
            text = h.read()
        for inc in re.findall(r'include_str\s+"([^"]+)"', text):
            target = os.path.normpath(os.path.join(os.path.dirname(f), inc))
            if target in changed and f not in changed:
                errors.append(f"{target} changed but {f}, which embeds it with include_str, did not: "
                              f"bump its counter comment so Lake rebuilds it")
    for e in errors:
        print(f"::error::{e}")
    if not errors:
        print("include_str: every embedded file that changed has its .lean file changed too")
    return 1 if errors else 0


def main(args):
    if args[:1] == ["matrix"]:
        matrix()
        return 0
    if args[:1] == ["check-shards"]:
        return check_shards(args[1] if len(args) > 1 else os.path.join(ROOT, ".lake/build/bin/tests"))
    if args[:1] == ["check-include-str"] and len(args) == 2:
        return check_include_str(args[1])
    if args[:1] == ["summary"] and len(args) >= 2:
        return summary(args[1], args[2:])
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
