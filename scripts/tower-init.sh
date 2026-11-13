#!/bin/sh
# Install tower and a default Wiz toolchain from a release tarball (stage 26d):
#
#   curl -sSfL https://raw.githubusercontent.com/wiz-pl/wiz/master/scripts/tower-init.sh | sh -s -- [CHANNEL]
#
# CHANNEL is nightly (the default) or a release tag. tower goes to ~/.tower/bin with the
# shims; add that directory to PATH. Needs curl and tar (and git for nightly, as tower
# does). The tarball brings its own C compiler and GMP (26f): `wiz build` needs nothing
# else. docs/install.md has the details.
set -eu
channel=${1:-nightly}
arch=$(uname -m)
repo=https://github.com/wiz-pl/wiz
rel=$channel
# nightly: the snapshot the tag nightly points at (26g), which is complete when the tag
# moves; the release `nightly` itself is replaced in place and may be briefly missing
if [ "$channel" = nightly ] && command -v git >/dev/null 2>&1; then
  sha=$(git ls-remote "$repo" refs/tags/nightly | cut -f1)
  [ -z "$sha" ] || rel=snapshot-$sha
fi
url=$repo/releases/download/$rel/wiz-$arch-linux.tar.gz
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
echo "tower-init: downloading $url"
curl -sSfL -o "$tmp/wiz.tar.gz" "$url"
if curl -sSfL -o "$tmp/wiz.tar.gz.sha256" "$url.sha256"; then
  (cd "$tmp" && sed 's/ .*/  wiz.tar.gz/' wiz.tar.gz.sha256 | sha256sum -c --quiet -) || { echo "tower-init: checksum mismatch" >&2; exit 1; }
fi
tar -xzf "$tmp/wiz.tar.gz" -C "$tmp"
"$tmp/wiz-$arch-linux/bin/tower" self install
"$HOME/.tower/bin/tower" default "$channel"
echo "tower-init: done; add ~/.tower/bin to PATH (export PATH=\"\$HOME/.tower/bin:\$PATH\")"
