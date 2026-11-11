/* grail's job supervisor (Grail/Exec.lean) ends with `_exit`: its thread that watches
   stdin is blocked in a read, and Lean's own exit waits for running tasks.

   The linker compiles this file into the executables that contain grail (`moreLinkObjs`
   in the lakefile), without Lean's include directory, as c/sockets.c. */
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>

typedef struct lean_object lean_object;

lean_object *grail_exit_now(uint8_t code, lean_object *world) {
  (void)world;
  fflush(stdout);
  fflush(stderr);
  _exit(code);
}

/* Whether a file is executable by its owner (`stat`), so that installed command outputs
   keep their mode (Grail/Command.lean). The path is sent a byte at a time and results
   are built by functions Grail/Exec.lean exports, as in c/sockets.c, so that this file
   needs no Lean headers. */
#include <sys/stat.h>

extern lean_object *grail_ok_unit(lean_object *w);
extern lean_object *grail_ok_bool(uint8_t b, lean_object *w);

static char grail_path[4096];
static size_t grail_path_len;

lean_object *grail_path_clear(lean_object *w) {
  grail_path_len = 0;
  grail_path[0] = 0;
  return grail_ok_unit(w);
}

lean_object *grail_path_push(uint8_t b, lean_object *w) {
  if (grail_path_len + 1 < sizeof grail_path) {
    grail_path[grail_path_len++] = (char)b;
    grail_path[grail_path_len] = 0;
  }
  return grail_ok_unit(w);
}

lean_object *grail_path_executable(lean_object *w) {
  struct stat st;
  int x = stat(grail_path, &st) == 0 && (st.st_mode & S_IXUSR);
  return grail_ok_bool((uint8_t)x, w);
}
