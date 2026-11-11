#!/bin/sh
# Tests scripts/release-snapshots.sh (stage 26g) against a fake `gh` whose releases are
# directories and whose tags are refs of a local bare repository (REMOTE). Offline; nothing
# is published. Run from the checkout: sh scripts/test-release-snapshots.sh
set -eu
here=$(cd "$(dirname "$0")" && pwd)
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
fail() { echo "FAIL: $*" >&2; exit 1; }

# the upstream: a linear master c1..c25 and a commit d off c20
repo=$t/repo.git
git init -q --bare "$repo"
w=$t/work
git init -q "$w"
g() { git -C "$w" -c user.name=t -c user.email=t@t -c commit.gpgsign=false "$@"; }
i=1
while [ $i -le 25 ]; do
  g commit -q --allow-empty -m "c$i"
  eval "c$i=\$(g rev-parse HEAD)"
  [ $i -eq 20 ] && base=$(g rev-parse HEAD)
  i=$((i + 1))
done
g push -q "$repo" HEAD:refs/heads/master
g checkout -q -b side "$base"; g commit -q --allow-empty -m d; d=$(g rev-parse HEAD)
g push -q "$repo" side
g tag keep/old "$c2"; g tag -a -m v1 v1 "$c4"
g push -q "$repo" keep/old v1

# the fake gh
S=$t/gh; mkdir -p "$S/rel" "$t/bin"
cat > "$t/bin/gh" <<'EOF'
#!/bin/sh
set -eu
S=$FAKE_GH; repo=$REMOTE
echo "gh $*" >> "$S/log"
case "$1 ${2:-}" in
  "release view") [ -d "$S/rel/$3" ] ;;
  "release create")
    tag=$3; shift 3; files=; target=
    while [ $# -gt 0 ]; do
      case $1 in
        --target) target=$2; shift 2 ;;
        --title|--notes) shift 2 ;;
        --*) shift ;;
        *) files="$files $1"; shift ;;
      esac
    done
    mkdir -p "$S/rel/$tag"
    n=$(cat "$S/clock" 2>/dev/null || echo 0); n=$((n + 1)); echo $n > "$S/clock"
    printf '%06d' $n > "$S/rel/$tag/.created"
    for f in $files; do cp "$f" "$S/rel/$tag/"; done
    git -C "$repo" rev-parse -q --verify "refs/tags/$tag" >/dev/null || git -C "$repo" update-ref "refs/tags/$tag" "$target" ;;
  "release upload")
    tag=$3; shift 3
    for f in "$@"; do case $f in --*) ;; *) cp "$f" "$S/rel/$tag/" ;; esac; done ;;
  "release list")
    for r in "$S/rel"/snapshot-*; do [ -d "$r" ] && printf '%s\t%s\n' "$(cat "$r/.created")" "$(basename "$r")"; done; true ;;
  "release download")
    tag=$3; shift 3; [ "$1" = --dir ] && mkdir -p "$2" && cp "$S/rel/$tag"/* "$2/" ;;
  "run list") cat "$S/running" 2>/dev/null || echo 1 ;;
  "release delete") rm -rf "$S/rel/$3"; git -C "$repo" update-ref -d "refs/tags/$3" ;;
  "release edit") ;;
  api*)
    shift; method=GET
    [ "$1" = -X ] && { method=$2; shift 2; }
    path=$1; shift
    val() { k=$1; shift; while [ $# -gt 0 ]; do case $1 in -f|-F) case $2 in "$k"=*) echo "${2#*=}"; return ;; esac; shift 2 ;; *) shift ;; esac; done; }
    case "$method $path" in
      "GET repos/{owner}/{repo}/releases/tags/"*)
        rel=${path##*/}
        for f in "$S/rel/$rel"/*; do [ -f "$f" ] && printf '%s\t%s\n' "$rel@$(basename "$f")" "$(basename "$f")"; done; true ;;
      "DELETE repos/{owner}/{repo}/releases/assets/"*)
        id=${path##*/}; rm "$S/rel/${id%%@*}/${id#*@}" ;;
      "PATCH repos/{owner}/{repo}/releases/assets/"*)
        id=${path##*/}; mv "$S/rel/${id%%@*}/${id#*@}" "$S/rel/${id%%@*}/$(val name "$@")" ;;
      "POST repos/{owner}/{repo}/git/refs") git -C "$repo" update-ref "$(val ref "$@")" "$(val sha "$@")" ;;
      "PATCH repos/{owner}/{repo}/git/refs/"*) git -C "$repo" update-ref "${path#repos/\{owner\}/\{repo\}/git/}" "$(val sha "$@")" ;;
      "GET repos/{owner}/{repo}/compare/"*)
        range=${path##*/}; a=${range%...*}; b=${range#*...}
        if [ "$a" = "$b" ]; then echo identical
        elif git -C "$repo" merge-base --is-ancestor "$a" "$b"; then echo ahead
        elif git -C "$repo" merge-base --is-ancestor "$b" "$a"; then echo behind
        else echo diverged; fi ;;
      *) echo "fake gh: no api $method $path" >&2; exit 1 ;;
    esac ;;
  *) echo "fake gh: no $*" >&2; exit 1 ;;
esac
EOF
chmod 755 "$t/bin/gh"
export PATH="$t/bin:$PATH" FAKE_GH=$S REMOTE=$repo SNAPSHOT_KEEP=20

dist() { # a dist directory for commit $1
  dd=$t/dist-$1; mkdir -p "$dd"
  echo "tarball $1" > "$dd/wiz-x86_64-linux.tar.gz"
  (cd "$dd" && sha256sum wiz-x86_64-linux.tar.gz > wiz-x86_64-linux.tar.gz.sha256)
  echo "$dd"
}
run() { sh "$here/release-snapshots.sh" "$@" > "$t/out" 2>&1 || { cat "$t/out"; fail "release-snapshots.sh $*"; }; }
tagAt() { git -C "$repo" rev-parse -q --verify "refs/tags/$1^{commit}" 2>/dev/null || true; }
have() { [ -d "$S/rel/snapshot-$1" ]; }

i=1
while [ $i -le 25 ]; do
  eval "c=\$c$i"
  run publish "$c" "$(dist "$c")"
  [ "$(tagAt nightly)" = "$c" ] && [ $i -gt 1 ] && fail "publish moved nightly"
  run nightly "$c"
  [ "$(tagAt nightly)" = "$c" ] || fail "nightly is not at c$i after publishing it"
  [ "$(cat "$S/rel/nightly/wiz-x86_64-linux.tar.gz")" = "tarball $c" ] || fail "nightly assets are not c$i's"
  i=$((i + 1))
done
ls "$S/rel/nightly" | grep -q next && fail "nightly kept a .next asset"
[ "$(ls -A "$S/rel/nightly" | wc -l)" -eq 3 ] || fail "nightly has $(ls -A "$S/rel/nightly")"
# retention: the newest 20 (c6..c25), plus c2 (keep/old) and c4 (v1, an annotated tag)
for k in 2 4 6 15 25; do eval "c=\$c$k"; have "$c" || fail "snapshot c$k was pruned"; [ "$(tagAt "snapshot-$c")" = "$c" ] || fail "tag snapshot-c$k"; done
for k in 1 3 5; do eval "c=\$c$k"; have "$c" && fail "snapshot c$k was kept"; [ -z "$(tagAt "snapshot-$c")" ] || fail "tag snapshot-c$k left"; done
[ "$(ls -d "$S/rel"/snapshot-* | wc -l)" -eq 22 ] || fail "$(ls -d "$S/rel"/snapshot-* | wc -l) snapshots, expected 22"
# the snapshot is the release's whole content, checksum included
(cd "$S/rel/snapshot-$c25" && sha256sum -c --quiet wiz-x86_64-linux.tar.gz.sha256) || fail "snapshot checksum"

# a rerun leaves the snapshot alone; nightly stays
run publish "$c25" "$(dist "$c25")"
grep -q "exists" "$t/out" || fail "rerun: $(cat "$t/out")"

# workflow_dispatch of an old commit: snapshot c1, nightly stays at c25, the oldest (c6) goes
run publish "$c1" "$(dist "$c1")"
have "$c1" || fail "dispatched snapshot c1 missing"
have "$c6" && fail "c6 should have been pruned"
[ "$(tagAt nightly)" = "$c25" ] || fail "snapshot moved nightly"

# a diverged commit gets a snapshot, but nightly does not move to it
run publish "$d" "$(dist "$d")"
have "$d" || fail "snapshot d missing"
run nightly "$d"
[ "$(tagAt nightly)" = "$c25" ] || fail "nightly moved to a diverged commit"
grep -q "not moving" "$t/out" || fail "diverged: $(cat "$t/out")"
# ... and an older master commit does not move it back
run nightly "$c24"
[ "$(tagAt nightly)" = "$c25" ] || fail "nightly moved backwards"

# CI passed on a commit whose snapshot never appears (release.yml failed): nightly stays
g checkout -q master 2>/dev/null || g checkout -q -B master "$c25"
g commit -q --allow-empty -m c26; c26=$(g rev-parse HEAD); g push -q "$repo" HEAD:refs/heads/master
NIGHTLY_WAIT=2 NIGHTLY_POLL=1 sh "$here/release-snapshots.sh" nightly "$c26" > "$t/out" 2>&1 && fail "nightly without a snapshot"
grep -q "no snapshot-$c26 after" "$t/out" || fail "no snapshot: $(cat "$t/out")"
echo 0 > "$S/running" # release.yml failed or was cancelled: stop at once
NIGHTLY_WAIT=600 NIGHTLY_POLL=1 sh "$here/release-snapshots.sh" nightly "$c26" > "$t/out" 2>&1 && fail "nightly without a release run"
grep -q "not running" "$t/out" || fail "release not running: $(cat "$t/out")"
rm "$S/running"
[ "$(tagAt nightly)" = "$c25" ] || fail "nightly moved without a snapshot"
# ... and one still uploading: nightly waits for it
NIGHTLY_WAIT=30 NIGHTLY_POLL=1 sh "$here/release-snapshots.sh" nightly "$c26" > "$t/out-wait" 2>&1 &
waiter=$!
sleep 2
run publish "$c26" "$(dist "$c26")"
wait $waiter || { cat "$t/out-wait"; fail "nightly did not wait for the snapshot"; }
grep -q "waiting for snapshot-$c26" "$t/out-wait" || fail "did not wait: $(cat "$t/out-wait")"
[ "$(tagAt nightly)" = "$c26" ] || fail "nightly is not at c26"
[ "$(cat "$S/rel/nightly/wiz-x86_64-linux.tar.gz")" = "tarball $c26" ] || fail "nightly assets are not c26's"

# bad arguments
sh "$here/release-snapshots.sh" publish abc "$t" >/dev/null 2>&1 && fail "accepted a short sha"
echo "release-snapshots: all passed"
