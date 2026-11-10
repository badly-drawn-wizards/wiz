# Stage 11: tooling

## 11a–b: queries and a language server ✅

* **Queries** (`Wiz/Query.lean`): elaboration is a pure function of the text, so each
  command's result is memoised under a **content hash chained through every command
  before it**. After an edit, only the commands from the edit on are elaborated again;
  the same text gives the same result (deterministic builds). The elaborator records
  identifiers with their types and ranges, and each global's declaration site, for
  `hoverAt`, `definitionAt` and `completionsAt`.
* **`wiz lsp`** (`Wiz/LSP.lean`): the Language Server Protocol over stdio, with
  diagnostics as you type, hover types, go to definition (also into `lib/`), and
  completion of global names. Each open document has its own query engine.

## 11c: a shared, content-addressed cache ✅

`wiz check`/`build`/`run` keep each command's **effect** (declarations, messages,
registrations, info trees) in the cache directory (`--cache DIR`, default `~/.cache/wiz`;
`--no-cache` turns it off), under the command's chained content hash. A shared directory is a shared cache,
since equal keys mean equal results. Imported modules are cached command by command
too. Commands that change the grammar or the macros rerun (they are cheap).
`Wiz/Cache.lean` serialises terms as S-expressions (quantities through the rig's
literal syntax). Every example gives the same output from the cache as without it.

Next: finer dependencies (re-elaborate only what an edit affects, not everything
after it).

## 11d: the info tree, the infoview and code actions ✅

* **The info tree** (`Elab/Basic.lean`, `Elab/Info.lean`): while elaborating, the
  elaborator records identifiers, the expected type of every checked term (and of every
  hole), the open goals before and after each tactic, `match`es and declarations. It
  keeps values and contexts as it goes (free) and quotes and zonks them at the end of the
  declaration, into `Term`s, not strings. An error carries the state it was thrown in,
  so a declaration that fails (unsolved goals, a hole) still has its tree. The tree is
  memoised and cached with its command; hovers and go to definition read it.
* **The infoview** (`Wiz/Infoview.lean`): `Term.prettyTagged` prints a term exactly as
  `Term.pretty` does, as tagged text: every subterm is a tag whose ref points into the
  document's session table (valid until the next edit). `wiz lsp` answers
  `wiz/plainGoal`, `wiz/plainTermGoal`, `wiz/interactiveGoals`,
  `wiz/interactiveTermGoal` and `wiz/subtermInfo` (a subterm's type, from the kernel,
  and where a constant was declared); the protocol is in
  `wiz-notes/infoview-protocol.md`.
* **Code actions** (`Wiz/Actions.lean`): diagnostics carry a code and data; the server
  offers *did you mean* (edit distance ≤ 2 over locals and globals), *add missing cases*
  (`| .c x y => ?c` per missing constructor) and *add type ascription* to a `def` without
  a type, with edits inline or through `codeAction/resolve`.

```
def k : Nat → Bool → Nat := by
  intro n         -- wiz/plainGoal here:  n : Nat ⊢ Bool → Nat
  intro b
  exact n
def four : Nat := doubel 2    -- unknown identifier 'doubel'   [Did you mean 'double'?]
```

## 11l: the infoview socket ✅

`wiz lsp --infoview SOCK` also listens on the Unix socket `SOCK`, for infoviews that run
beside the editor (the terminal infoview connects there). The editor never says where
its cursor is, so the server infers it from the editor's requests: any request with a
position (hover, `documentHighlight`, which the server now advertises so that editors
send it on every move, go to definition, completion, …) and code actions (at the
range's start). When the cursor moves, and after each elaboration of its document,
every connected infoview gets `wiz/infoview/cursor` (uri, position, session) and pulls
with the ordinary `wiz/*` requests on the socket; sessions and refs are the editor's.
Lean's library has no Unix sockets, so `c/sockets.c` (compiled into the executables by
the linker, `moreLinkObjs` in the lakefile) listens, accepts, and turns a connection
into two ordinary Lean handles. The server's state stays single-threaded: a reader
thread per connection feeds one channel, and one loop answers in order. Protocol §8 of
`wiz-notes/infoview-protocol.md`; tested in-process (the `lsp-server` group: the editor
on a socket pair, an infoview on the socket).

## 11m–n: the infoview, in a terminal and in a browser ✅

```
wiz lsp --infoview /tmp/wiz.sock          # the editor's server (11l)
wiz-infoview /tmp/wiz.sock                # in a tmux split: the goals at the cursor
wiz-infoview --file t.wiz --at 4:5        # or on its own: starts `wiz lsp` itself
web/build.sh && web/bridge.sh             # the same infoview in a browser
```

Both clients are Wiz programs, and they share their logic:

* `lib/Json.wiz`: JSON values (mutual inductive types: Wiz has no nested ones), a
  parser and a printer. Strings are code points; `\uXXXX` escapes and surrogate pairs
  are decoded, and the printer escapes control characters (or everything non-ASCII,
  `Json.renderAscii`).
* `lib/Infoview.wiz`: the protocol's tagged text and goals; a **layout** that flattens
  tagged text into styled pieces (numbering the tags in reading order), word-wraps them
  to a width with hanging indents, and renders lines with SGR colours by kind; the same
  goals as **HTML** with a `data-ref` and `data-idx` on every subterm's `<span>`;
  navigation (next, previous, enclosing, first inside); `Content-Length` framing
  (counting UTF-8 bytes); and the decoding of terminal keys and SGR mouse reports.
* `infoview/Tui.wiz` (`infoview/build.sh`): the terminal program. The alternate screen,
  raw mode, `poll` over the keyboard, the socket and a `SIGWINCH` self-pipe, and Unix
  sockets are `infoview/term.c`, bound with `extern` (Wiz has no callbacks or
  structs in its FFI, so the event loop is Wiz around a blocking `iv_wait`). ←/→ select
  a subterm, ↑/↓ go out of and into it, and the bottom line says what it is
  (`wiz/subtermInfo`); a mouse click selects too.
* `web/Web.wiz` (`web/build.sh`): the page's language client, compiled to C and then to
  WebAssembly by Emscripten: wasm64 keeps the runtime's 62-bit small numbers, mini-gmp
  stands in for GMP, and Asyncify lets `js_next_event` wait for the page. The page
  (`web/infoview.html`, `web/infoview.js`, about 100 lines of JavaScript) only moves events
  in and HTML out. `web/bridge.sh` puts `websocat` in front of `wiz lsp` until the server
  speaks WebSocket itself.

Running it in tmux, next to an editor whose language server is `wiz lsp --infoview
/tmp/wiz.sock` (11l):

```
infoview/build.sh                                   # → .lake/build/bin/wiz-infoview
tmux split-window -h -l 60 '.lake/build/bin/wiz-infoview /tmp/wiz.sock'
```

The pane waits for the server, then follows the editor's cursor. Without an editor:
`wiz-infoview --file examples/tactics.wiz --at 6:3` (`[` and `]` move the line).
`infoview/test.sh` (in the `infoview` test group) runs the terminal infoview against
`infoview/stub_server.py` (canned goals; as text and in a pseudo-terminal) and against
the real `wiz lsp --infoview`, with `infoview/editor_stub.py` as the editor.
`web/test.sh` (needs nix: Emscripten, websocat, Chromium; not in CI) runs the Wasm
module under Node, then the page in headless Chromium over the DevTools protocol.
