/* What tower needs from the system that lib/Sys.wiz doesn't have yet (stage 26e). */
#include <limits.h>
#include <stdlib.h>

/* the absolute path with links resolved; "" if it doesn't exist */
const char *tower_realpath(const char *p) {
  static char buf[PATH_MAX];
  return realpath(p, buf) ? buf : "";
}
