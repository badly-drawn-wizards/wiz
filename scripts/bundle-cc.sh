#!/bin/sh
# The C toolchain a release tarball ships (stage 26f): `share/wiz/cc/` of the tarball, so
# that `wiz build`, `wiz run` and grail need no system compiler, GMP or Boehm GC.
#
#   scripts/bundle-cc.sh OUT [DOWNLOADS]
#
# OUT gets (and is replaced):
#
#   bin/cc            clang with the sysroot below: what `wiz` uses by default
#   bin/llc           the same clang on textual LLVM IR, with llc's arguments (`--llvm`)
#   bin/clang, bin/ld.lld, lib/*.so*   the compiler and linker, from the Lean toolchain
#                     (`lean --print-prefix`, or $LEAN_PREFIX): the same LLVM as Lean's
#   lib/clang/N/      compiler-rt (builtins, crtbegin/end) and clang's own headers
#   sysroot/          glibc 2.27 and Linux 4.15 headers and the libraries to link against
#                     (Ubuntu 18.04's libc6, libc6-dev, linux-libc-dev), with static
#                     GMP 6.3.0 and the Boehm GC 8.2.8 built here
#   LICENSES/         the licences of all of the above
#   VERSIONS          what went in
#
# Programs it builds link GMP and the GC statically and need only glibc >= 2.27 (libc,
# libm, libpthread) at run time. DOWNLOADS (default ~/.cache/wiz-bundle-cc) keeps the
# fetched files; each is checked against its sha256. Runs outside Nix (the release job).
set -eu
out=$1
dl=${2:-${HOME:-/tmp}/.cache/wiz-bundle-cc}
lean=${LEAN_PREFIX:-$(lean --print-prefix)}
jobs=$(nproc 2>/dev/null || echo 2)
mkdir -p "$dl"
case $out in /*) ;; *) out=$(pwd)/$out ;; esac
case $dl in /*) ;; *) dl=$(pwd)/$dl ;; esac

ubuntu=http://archive.ubuntu.com/ubuntu/pool/main
# url sha256 (one per line)
sources="
$ubuntu/g/glibc/libc6_2.27-3ubuntu1.6_amd64.deb 5b813d4512491cd8fb30b2eb9192349ee75ffe3c9f21ae136cc7b2429f70c3b2
$ubuntu/g/glibc/libc6-dev_2.27-3ubuntu1.6_amd64.deb 96ae7d2cf38f0547ca3cccb3344c8802fdf5bcd71c4b6d9aed09558ac8cc87db
$ubuntu/l/linux/linux-libc-dev_4.15.0-213.224_amd64.deb 06d9f16644d3a1b2ab7dd01730e833d516b6f575d975855f496eea6463fef2f6
https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898
https://github.com/ivmai/bdwgc/releases/download/v8.2.8/gc-8.2.8.tar.gz 7649020621cb26325e1fb5c8742590d92fb48ce5c259b502faf7d9fb5dabb160
"
echo "$sources" | while read -r url sum; do
  [ -n "$url" ] || continue
  f=$dl/$(basename "$url")
  if ! { [ -f "$f" ] && echo "$sum  $f" | sha256sum -c --quiet - >/dev/null 2>&1; }; then
    curl -sSfL --retry 3 -o "$f.part" "$url"
    echo "$sum  $f.part" | sha256sum -c --quiet -
    mv "$f.part" "$f"
  fi
done

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
rm -rf "$out"
mkdir -p "$out/bin" "$out/lib" "$out/LICENSES"

# the compiler and linker, and the shared libraries they need (from Lean's lib/)
cp -L "$lean/bin/clang" "$lean/bin/ld.lld" "$out/bin/"
need() { readelf -d "$1" | sed -n 's/.*(NEEDED).*\[\(.*\)\]/\1/p'; }
todo="$out/bin/clang $out/bin/ld.lld"
while [ -n "$todo" ]; do
  next=
  for b in $todo; do
    for l in $(need "$b"); do
      if [ -e "$lean/lib/$l" ] && [ ! -e "$out/lib/$l" ]; then
        cp -L "$lean/lib/$l" "$out/lib/$l"
        next="$next $out/lib/$l"
      fi
    done
  done
  todo=$next
done
ver=$(ls "$lean/lib/clang")
mkdir -p "$out/lib/clang/$ver/include"
cp -R "$lean/lib/clang/$ver/lib" "$out/lib/clang/$ver/"
cp "$lean/include/clang/"*.h "$out/lib/clang/$ver/include/"
cp "$lean/LICENSE" "$out/LICENSES/lean4-LICENSE"
[ -d "$lean/LICENSES" ] && cp -R "$lean/LICENSES" "$out/LICENSES/lean4-LICENSES"

# the sysroot: glibc 2.27 and the kernel headers, only what compiling and linking need
sys=$out/sysroot
mkdir -p "$work/deb" "$sys"
for d in libc6_2.27-3ubuntu1.6_amd64.deb libc6-dev_2.27-3ubuntu1.6_amd64.deb linux-libc-dev_4.15.0-213.224_amd64.deb; do
  rm -rf "$work/deb"/*
  (cd "$work/deb" && ar x "$dl/$d" && tar -xf data.tar.* -C "$sys")
done
mkdir -p "$out/LICENSES/glibc" "$out/LICENSES/linux"
cp "$sys/usr/share/doc/libc6/copyright" "$out/LICENSES/glibc/copyright"
cp "$sys/usr/share/doc/linux-libc-dev/copyright" "$out/LICENSES/linux/copyright"
rm -rf "$sys/etc" "$sys/usr/share" "$sys/usr/bin" "$sys/usr/sbin" "$sys/sbin" "$sys/usr/lib/x86_64-linux-gnu/gconv" \
  "$sys/usr/lib/x86_64-linux-gnu/audit" "$sys/lib/x86_64-linux-gnu/security"
# static libc and friends are not used (programs link libc dynamically)
find "$sys/usr/lib/x86_64-linux-gnu" -name '*.a' ! -name '*_nonshared.a' -delete
# absolute symlinks (libdl.so -> /lib/x86_64-linux-gnu/libdl.so.2) point into the sysroot
find "$sys" -type l | while read -r l; do
  t=$(readlink "$l")
  case $t in /*) ln -sfn "$(realpath -m --relative-to="$(dirname "$l")" "$sys$t")" "$l" ;; esac
done

cat > "$out/bin/cc" <<'EOF'
#!/bin/sh
# Wiz's bundled C compiler (scripts/bundle-cc.sh): clang with glibc 2.27, GMP and the GC
d=$(cd "$(dirname "$0")/.." && pwd)
# a link also gets libm (as needed): `import_c "math.h"` calls it, and with glibc 2.27
# libpthread and libm are libraries of their own
link=yes
for a in "$@"; do
  case $a in -c|-E|-S|-r|-M|-MM) link= ;; esac
done
if [ -n "$link" ]; then
  exec "$d/bin/clang" --sysroot="$d/sysroot" -pthread -Wno-unused-command-line-argument "$@" \
    -Wl,--as-needed -lm -Wl,--no-as-needed
fi
exec "$d/bin/clang" --sysroot="$d/sysroot" -pthread -Wno-unused-command-line-argument "$@"
EOF
cat > "$out/bin/llc" <<'EOF'
#!/bin/sh
# `llc` for Wiz's LLVM backend: the bundled clang compiles the textual IR
# (it understands -O<n>, -filetype=obj|asm, -relocation-model=pic|static, -o FILE, FILE)
d=$(cd "$(dirname "$0")/.." && pwd)
opt=-O2 kind=-c pic=-fPIC o= in=
while [ $# -gt 0 ]; do
  case $1 in
    -O*) opt=$1 ;;
    -filetype=obj) kind=-c ;;
    -filetype=asm) kind=-S ;;
    -relocation-model=pic) pic=-fPIC ;;
    -relocation-model=static) pic=-fno-pic ;;
    -o) o=$2; shift ;;
    -*) echo "llc (wiz bundle): unsupported option $1" >&2; exit 2 ;;
    *) in=$1 ;;
  esac
  shift
done
exec "$d/bin/clang" -Wno-override-module $kind $opt $pic -x ir -o "${o:--}" "$in"
EOF
chmod 755 "$out/bin/cc" "$out/bin/llc"

# GMP and the Boehm GC, static and position-independent, into the sysroot
cc=$out/bin/cc
tar -xJf "$dl/gmp-6.3.0.tar.xz" -C "$work"
(cd "$work/gmp-6.3.0" &&
  # --enable-fat: code for every x86-64 CPU, picked at run time (a build tuned to this
  # machine's CPU would fail on older ones)
  ./configure -q --host=x86_64-pc-linux-gnu --enable-fat --enable-static --disable-shared --with-pic \
    --prefix="$sys/usr" CC="$cc" CFLAGS="-O2 -w" >/dev/null &&
  make -s -j"$jobs" >/dev/null && make -s install >/dev/null)
cp "$work/gmp-6.3.0/COPYING.LESSERv3" "$out/LICENSES/gmp-COPYING.LESSERv3"
cp "$work/gmp-6.3.0/COPYINGv3" "$out/LICENSES/gmp-COPYINGv3"
cp "$work/gmp-6.3.0/COPYINGv2" "$out/LICENSES/gmp-COPYINGv2"
tar -xzf "$dl/gc-8.2.8.tar.gz" -C "$work"
(cd "$work/gc-8.2.8" &&
  ./configure -q --host=x86_64-pc-linux-gnu --enable-static --disable-shared --with-pic --enable-threads=posix \
    --disable-docs --with-libatomic-ops=none --prefix="$sys/usr" CC="$cc" CFLAGS="-O2 -w" >/dev/null &&
  make -s -j"$jobs" >/dev/null && make -s install >/dev/null)
# its licence is the top of README.QUICK
cp "$work/gc-8.2.8/README.QUICK" "$out/LICENSES/bdwgc-README.QUICK"
rm -rf "$sys/usr/share" "$sys/usr/lib/pkgconfig"
find "$sys/usr/lib" -name '*.la' -delete

cat > "$out/VERSIONS" <<EOF
clang, ld.lld, compiler-rt: from $(basename "$lean") ($("$out/bin/clang" --version | head -1))
glibc 2.27 (libc6, libc6-dev 2.27-3ubuntu1.6), Linux headers 4.15 (linux-libc-dev 4.15.0-213.224): Ubuntu 18.04
GMP 6.3.0 (static, --enable-fat), Boehm GC 8.2.8 (static, threads)
EOF

# it works
cat > "$work/t.c" <<'EOF'
#include <gmp.h>
#include <gc.h>
#include <stdio.h>
int main(void) { mpz_t a; mpz_init_set_ui(a, 1); mpz_mul_2exp(a, a, 100); GC_INIT();
  char *p = GC_MALLOC(16); gmp_printf("%Zd %d\n", a, p != 0); return 0; }
EOF
"$cc" -O2 "$work/t.c" -o "$work/t" -lgmp -lgc
"$work/t"
du -sh "$out"
