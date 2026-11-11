#!/bin/sh
# A release tarball of the Wiz toolchain (stage 26d): what `tower` installs from GitHub
# Releases, and what you can untar by hand.
#
#   scripts/release-tarball.sh OUT.tar.gz [BINDIR] [REVISION]
#
# BINDIR (default .lake/build/bin) holds the built wiz, grail and tower; the standard
# library, the nvim plugin and the docs come from this checkout. The tarball is one
# directory, wiz-ARCH-linux/:
#
#   bin/wiz, bin/grail       wrappers: the binary with -I share/wiz/lib (no other flags:
#                            `wiz build` uses `cc` and the system's GMP; tower rewrites
#                            them with your flags)
#   bin/tower                the toolchain manager
#   share/wiz/lib/           the standard library
#   share/wiz/.lake/build/bin/{wiz,grail}   the binaries (grail finds lib/ from there)
#   share/wiz/editors/       the editor plugins, when the checkout has them
#   share/wiz/REVISION       the commit
#
# OUT.tar.gz.sha256 is written next to it.
set -eu
out=$1
bindir=${2:-.lake/build/bin}
rev=${3:-$(git rev-parse HEAD 2>/dev/null || echo unknown)}
arch=$(uname -m)
name=wiz-$arch-linux
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
top=$work/$name
mkdir -p "$top/bin" "$top/share/wiz/.lake/build/bin"
for b in wiz grail; do
  cp "$bindir/$b" "$top/share/wiz/.lake/build/bin/$b"
done
[ -f "$bindir/tower" ] && cp "$bindir/tower" "$top/bin/tower"
cp -R lib "$top/share/wiz/lib"
[ -d editors ] && cp -R editors "$top/share/wiz/editors"
echo "$rev" > "$top/share/wiz/REVISION"
cat > "$top/bin/wiz" <<'EOF'
#!/bin/sh
d=$(cd "$(dirname "$0")/.." && pwd)
exec "$d/share/wiz/.lake/build/bin/wiz" -I "$d/share/wiz/lib" "$@"
EOF
cat > "$top/bin/grail" <<'EOF'
#!/bin/sh
d=$(cd "$(dirname "$0")/.." && pwd)
exec "$d/share/wiz/.lake/build/bin/grail" "$@"
EOF
chmod 755 "$top/bin/wiz" "$top/bin/grail"
case $out in /*) ;; *) out=$(pwd)/$out ;; esac
tar -czf "$out" -C "$work" "$name"
(cd "$(dirname "$out")" && sha256sum "$(basename "$out")") > "$out.sha256"
echo "$out"
