#!/bin/sh
# Per-commit release tarballs (stage 26g): what release.yml does with a green master push.
#
#   scripts/release-snapshots.sh publish SHA DIST   snapshot-SHA, then prune (release.yml,
#                                                   a master push or a dispatched commit)
#   scripts/release-snapshots.sh nightly SHA        move nightly to SHA once snapshot-SHA is
#                                                   there (nightly.yml, after CI passed on SHA)
#   scripts/release-snapshots.sh prune              only the pruning
#
# * every master commit gets a pre-release `snapshot-<full sha>` (its tag at that commit)
#   holding DIST/* (wiz-ARCH-linux.tar.gz and its .sha256). `gh release create` makes a
#   draft, uploads, then publishes, so the tag (and the release) appear only once the
#   assets are complete: whoever sees the tag (`git ls-remote`) can download them.
#   A snapshot of a commit whose CI fails may exist (a pin names it explicitly).
# * `nightly` runs when the CI workflow succeeded on SHA: it waits (NIGHTLY_WAIT seconds,
#   default 3600) for the tag snapshot-SHA, then moves the tag `nightly` to SHA, only
#   forwards (an older commit never moves it back). A ref update is atomic: tower reads
#   `refs/tags/nightly` and downloads snapshot-<that commit>, which exists by then, so
#   there is no window with a 404.
# * the release `nightly` (releases/download/nightly/…, for people and old towers) gets
#   the snapshot's files: each is uploaded under a temporary name, then the old asset is
#   deleted and the new one renamed, so a download misses it for one API call, not an
#   upload.
# * pruning keeps the newest $SNAPSHOT_KEEP snapshots (default 20) and every snapshot of a
#   commit that a `v*` tag, a `keep/…` tag or `nightly` points at; the rest are deleted
#   with their tags. To keep a pinnable toolchain, push a tag `keep/NAME` at its commit.
#
# Uses `gh` (GH_TOKEN, GH_REPO or the checkout's repository) and `git ls-remote $REMOTE`
# (default origin). scripts/test-release-snapshots.sh runs it against a fake gh.
set -eu
keep=${SNAPSHOT_KEEP:-20}
remote=${REMOTE:-origin}

# the commits that tags v*, keep/… and nightly point at (annotated tags peeled)
protected() {
  git ls-remote --tags "$remote" | awk '
    $2 ~ /^refs\/tags\/(v[^\/]*|keep\/.+|nightly)(\^\{\})?$/ {
      r = $2; sub(/\^\{\}$/, "", r)
      if ($2 ~ /\^\{\}$/ || !(r in c)) c[r] = $1
    }
    END { for (r in c) print c[r] }'
}

prune() {
  prot=$(protected)
  # newest first; drafts are not listed
  gh release list --limit 1000 --exclude-drafts --json tagName,createdAt \
      --jq '.[] | select(.tagName | startswith("snapshot-")) | [.createdAt, .tagName] | @tsv' |
    sort -r | awk -v keep="$keep" 'NR > keep { print $2 }' |
    while read -r tag; do
      sha=${tag#snapshot-}
      if printf '%s\n' "$prot" | grep -qx "$sha"; then
        echo "keeping $tag (a v*, keep/ or nightly tag points at it)"
        continue
      fi
      echo "pruning $tag"
      gh release delete "$tag" --yes --cleanup-tag
    done
}

# replace the assets of release $1 by the files $2… without a window as long as an upload
swap_assets() {
  rel=$1; shift
  tmp=$(mktemp -d)
  for f in "$@"; do cp "$f" "$tmp/$(basename "$f").next"; done
  gh release upload "$rel" "$tmp"/*.next --clobber
  rm -rf "$tmp"
  assets=$(gh api "repos/{owner}/{repo}/releases/tags/$rel" --jq '.assets[] | [.id, .name] | @tsv')
  for f in "$@"; do
    name=$(basename "$f")
    new=$(printf '%s\n' "$assets" | awk -F '\t' -v n="$name.next" '$2 == n { print $1 }')
    old=$(printf '%s\n' "$assets" | awk -F '\t' -v n="$name" '$2 == n { print $1 }')
    [ -n "$new" ] || { echo "release $rel: $name.next did not upload" >&2; exit 1; }
    [ -z "$old" ] || gh api -X DELETE "repos/{owner}/{repo}/releases/assets/$old" >/dev/null
    gh api -X PATCH "repos/{owner}/{repo}/releases/assets/$new" -f name="$name" >/dev/null
  done
}

fullsha() {
  case $1 in *[!0-9a-f]*|'') echo "$1 is not a commit sha" >&2; exit 2 ;; esac
  [ ${#1} -eq 40 ] || { echo "$1 is not a full (40 hex) sha" >&2; exit 2; }
}

snapshot() {
  sha=$1 dist=$2
  fullsha "$sha"
  tag=snapshot-$sha
  if gh release view "$tag" >/dev/null 2>&1; then
    echo "$tag exists (a rerun); leaving it as it is"
  else
    gh release create "$tag" "$dist"/* --prerelease --latest=false --target "$sha" \
      --title "Wiz snapshot ${sha%"${sha#????????????}"}" \
      --notes "Wiz built from master at $sha. Snapshots are pruned (the newest $keep, plus those that a v*, keep/… or nightly tag points at); install with tower: \`tower toolchain install master@$sha\` (docs/stages/26-tower.md)."
  fi
}

nightly() {
  sha=$1
  fullsha "$sha"
  tag=snapshot-$sha
  # the release job may still be building or uploading: its tag appears once it is complete
  waited=0
  until [ -n "$(git ls-remote --tags "$remote" "refs/tags/$tag")" ]; do
    if [ "$waited" -ge "${NIGHTLY_WAIT:-3600}" ]; then
      echo "no $tag after ${waited}s; nightly stays" >&2; exit 1
    fi
    # no release.yml run of SHA is still going (it failed, or a newer push cancelled it):
    # don't hold the queue of later nightly runs
    running=$(gh run list --workflow release.yml --commit "$sha" --json status \
      --jq 'map(select(.status != "completed")) | length')
    if [ "$running" = 0 ]; then
      echo "no $tag, and release.yml is not running on $sha (failed or cancelled); nightly stays" >&2; exit 1
    fi
    echo "waiting for $tag"
    sleep "${NIGHTLY_POLL:-60}"; waited=$((waited + ${NIGHTLY_POLL:-60}))
  done
  # nightly moves forwards only: SHA must be ahead of (or at) where it is
  cur=$(git ls-remote --tags "$remote" refs/tags/nightly | awk '{ print $1 }')
  if [ -z "$cur" ]; then
    gh api -X POST "repos/{owner}/{repo}/git/refs" -f ref=refs/tags/nightly -f sha="$sha" >/dev/null
  else
    st=$(gh api "repos/{owner}/{repo}/compare/$cur...$sha" --jq .status)
    case $st in
      ahead) gh api -X PATCH "repos/{owner}/{repo}/git/refs/tags/nightly" -f sha="$sha" -F force=true >/dev/null ;;
      identical) ;;
      *) echo "nightly is at $cur, which $sha is not ahead of ($st); not moving it"; return ;;
    esac
  fi
  echo "nightly -> $sha"
  if ! gh release view nightly >/dev/null 2>&1; then
    gh release create nightly --prerelease --latest=false --target "$sha" --title "Wiz nightly" \
      --notes "Wiz built from master; moves with it. tower installs the snapshot the tag nightly points at."
  fi
  files=$(mktemp -d)
  gh release download "$tag" --dir "$files"
  swap_assets nightly "$files"/*
  rm -rf "$files"
  gh release edit nightly --notes "Wiz built from master at $sha (snapshot-$sha), the newest commit whose CI passed. tower installs the snapshot the tag nightly points at."
}

case ${1:-} in
  publish) [ $# -eq 3 ] || { echo "usage: $0 publish SHA DIST" >&2; exit 2; }; snapshot "$2" "$3"; prune ;;
  nightly) [ $# -eq 2 ] || { echo "usage: $0 nightly SHA" >&2; exit 2; }; nightly "$2" ;;
  prune) prune ;;
  *) echo "usage: $0 publish SHA DIST | nightly SHA | prune" >&2; exit 2 ;;
esac
