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
