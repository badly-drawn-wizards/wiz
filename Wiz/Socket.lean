/-!
# Unix-domain sockets

Lean's library has TCP and UDP sockets but no Unix-domain ones, which
`wiz lsp --infoview SOCK` needs. The few calls it uses are in `c/sockets.c` (which the
linker compiles into every executable, see the lakefile); a connection comes back as a
pair of ordinary handles, one to read and one to write. The C side cannot read Lean
objects (it is compiled without Lean's headers), so paths go to it a byte at a time and
it builds its results with the functions exported here.
-/

namespace Wiz.Socket

/-! The C side's results. -/
@[export wiz_sock_ok_unit] def okUnit : IO Unit := pure ()
@[export wiz_sock_ok_fd] def okFd (fd : UInt32) : IO UInt32 := pure fd
@[export wiz_sock_ok_conn] def okConn (fd : UInt32) (r w : IO.FS.Handle) : IO (UInt32 × IO.FS.Handle × IO.FS.Handle) :=
  pure (fd, r, w)
@[export wiz_sock_ok_handles] def okHandles (r w : IO.FS.Handle) : IO (IO.FS.Handle × IO.FS.Handle) := pure (r, w)
@[export wiz_sock_ok_pair] def okPair (r₀ w₀ r₁ w₁ : IO.FS.Handle) :
    IO ((IO.FS.Handle × IO.FS.Handle) × (IO.FS.Handle × IO.FS.Handle)) := pure ((r₀, w₀), (r₁, w₁))
@[export wiz_sock_error] def error (e : IO.Error) : IO Unit := throw e

@[extern "wiz_sock_path_clear"] opaque pathClear : IO Unit
@[extern "wiz_sock_path_push"] opaque pathPush (b : UInt8) : IO Unit
@[extern "wiz_unix_listen"] opaque listenRaw : IO UInt32
@[extern "wiz_unix_connect"] opaque connectRaw : IO (IO.FS.Handle × IO.FS.Handle)
@[extern "wiz_unix_close"] opaque closeRaw (fd : UInt32) : IO Unit

/-- Hand the socket path to the C side. -/
def setPath (path : String) : IO Unit := do
  pathClear
  for b in path.toUTF8 do pathPush b

/-- Listen on the socket file `path` (replacing a stale one); the listening descriptor. -/
def listen (path : String) : IO UInt32 := do setPath path; listenRaw

/-- Wait for a connection: its descriptor (for `shutdown`), and its read and write handles. -/
@[extern "wiz_unix_accept"] opaque accept (fd : UInt32) : IO (UInt32 × IO.FS.Handle × IO.FS.Handle)

/-- Connect to the socket file `path`: read and write handles. -/
def connect (path : String) : IO (IO.FS.Handle × IO.FS.Handle) := do setPath path; connectRaw

/-- Two connected sockets, each as (read, write) handles. -/
@[extern "wiz_socket_pair"] opaque pair : IO ((IO.FS.Handle × IO.FS.Handle) × (IO.FS.Handle × IO.FS.Handle))

/-- Shut a connection down (a thread reading it sees the end of the stream). -/
@[extern "wiz_fd_shutdown"] opaque shutdown (fd : UInt32) : IO Unit

/-- Stop listening on `fd` and remove the socket file `path`. -/
def close (fd : UInt32) (path : String) : IO Unit := do setPath path; closeRaw fd

end Wiz.Socket
