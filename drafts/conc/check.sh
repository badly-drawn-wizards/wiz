#!/bin/sh
# Check the concurrency / separation-logic drafts, and that the negative examples are
# rejected. Run from the worktree root: `sh drafts/conc/check.sh` (uses .lake/build/bin/wiz).
WIZ=${WIZ:-.lake/build/bin/wiz}
tmp=$(mktemp -d)
fail=0
for f in drafts/conc/Session.wiz drafts/seplogic/HProp.wiz; do
  if "$WIZ" check --no-cache "$f" >"$tmp/out" 2>&1 && ! grep -q error "$tmp/out"; then echo "ok   $f"
  else echo "FAIL $f"; cat "$tmp/out"; fail=1; fi
done
# each negative is appended to Session.wiz and must be rejected
neg() {
  { cat drafts/conc/Session.wiz; printf '%s\n' "$2"; } >"$tmp/neg.wiz"
  if "$WIZ" check --no-cache "$tmp/neg.wiz" 2>&1 | grep -q "rejected $1"; then echo "ok   rejected $1"
  else echo "FAIL accepted $1"; fail=1; fi
}
neg twice "def twice (1 c : Chan sumProto) : IO N := Chan.send (k := fun n => sendMany ack n) c one (fun c' => runClient c)"
neg leak "def leak (1 c : Chan Proto.done) : IO Unit := IO.pure ()"
neg dupe "def dupe (1 c : Chan Proto.done) : IO Unit := IO.then1 (Chan.close c) (Chan.close c)"
# a closure may capture a linear endpoint (the closure is then linear itself), but the
# caller cannot call it twice
neg dupf "def capture (1 c : Chan Proto.done) : Unit → IO Unit := fun _ => Chan.close c
def dupf (1 c : Chan Proto.done) : IO Unit := let f := capture c; IO.then1 (f ()) (f ())"
rm -rf "$tmp"
exit $fail
