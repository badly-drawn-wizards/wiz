#!/bin/sh
# Install tower and a default Wiz toolchain from a release tarball (stage 26d):
#
#   curl -sSfL https://raw.githubusercontent.com/badly-drawn-wizards/wiz/master/scripts/tower-init.sh | sh -s -- [CHANNEL]
#
# CHANNEL is nightly (the default) or a release tag. tower goes to ~/.tower/bin with the
# shims; add that directory to PATH. Needs curl and tar; `wiz build` needs cc and GMP.
set -eu
channel=${1:-nightly}
arch=$(uname -m)
url=https://github.com/badly-drawn-wizards/wiz/releases/download/$channel/wiz-$arch-linux.tar.gz
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
echo "tower-init: downloading $url"
curl -sSfL -o "$tmp/wiz.tar.gz" "$url"
tar -xzf "$tmp/wiz.tar.gz" -C "$tmp"
"$tmp/wiz-$arch-linux/bin/tower" self install
"$HOME/.tower/bin/tower" default "$channel"
echo "tower-init: done; add ~/.tower/bin to PATH (export PATH=\"\$HOME/.tower/bin:\$PATH\")"
