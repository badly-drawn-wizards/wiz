import Wiz.Core.Term

/-!
# Modules by path (stage 23b)

A module name is a dotted path: `import A.B` reads `A/B.wiz` under the first **root**
that has it. The standard library `lib/` is a root, so `import Prelude` reads
`lib/Prelude.wiz`. The frontend is pure: the caller reads every module a file can reach
up front, by scanning import lines (a superset of the imports the frontend will see,
since an `import` is always a whole command on its own line).
-/

namespace Wiz.Module

/-- `A.B` ↦ `A/B.wiz`. -/
def relPath (m : Name) : System.FilePath :=
  System.FilePath.mk ("/".intercalate (m.splitOn ".") ++ ".wiz")

/-- `A/B.wiz` (relative to a root) ↦ `A.B`. -/
def nameOf (rel : System.FilePath) : Name :=
  let s := rel.toString
  let s := if s.endsWith ".wiz" then (s.dropEnd 4).toString else s
  ".".intercalate ((s.splitOn "/").filter (· ≠ ""))

/-- The modules a source text imports, in order: every line `import M` (not `import_c`). -/
def importsOf (src : String) : List Name := Id.run do
  let mut out : Array Name := #[]
  for line in src.splitOn "\n" do
    let l := line.trimAsciiStart.toString
    if l.startsWith "import " || l.startsWith "import\t" then
      let rest := (l.drop 7).trimAsciiStart.toString
      let m := String.ofList (rest.toList.takeWhile fun c => c.isAlphanum || c == '_' || c == '.' || c == '\'')
      if !m.isEmpty && !out.contains m then out := out.push m
  pure out.toList

/-- The `import_c "h"` headers of a source text. -/
def headersOf (src : String) : List String :=
  ((src.splitOn "import_c \"").drop 1).filterMap fun part =>
    let h := (part.splitOn "\"").headD ""
    if h.isEmpty then none else some h

/-- Where module `m` lives: the first root that has it. -/
def resolve (roots : List System.FilePath) (m : Name) : IO (Option System.FilePath) := do
  for r in roots do
    let p := r / relPath m
    if ← p.pathExists then return some p
  pure none

/-- The `link_c "f.c"` files of a source text (9f), as written. -/
def cSourcesOf (src : String) : List String :=
  ((src.splitOn "link_c \"").drop 1).filterMap fun part =>
    let f := (part.splitOn "\"").headD ""
    if f.isEmpty then none else some f

/-- The key of a `link_c` path in `cSourceTable`: the module (`""`: the main file) and the
path as written. -/
def cSourceKey (m : Name) (rel : String) : String := m ++ "\x00" ++ rel

/-- Resolve the `link_c` files of the main file (in `dir`) and of the modules it reaches
(with their paths): each relative to its own file. Files that don't exist are left out
(the elaborator reports them). -/
def cSourceTable (dir : System.FilePath) (src : String)
    (mods : Std.HashMap Name (System.FilePath × String)) : IO (Std.HashMap String String) := do
  let mut t : Std.HashMap String String := {}
  for (m, base, text) in ("", dir, src) :: mods.toList.map (fun (n, p, txt) => (n, p.parent.getD ".", txt)) do
    for rel in cSourcesOf text do
      let f := if System.FilePath.isAbsolute rel then System.FilePath.mk rel else base / rel
      if ← f.pathExists then
        if !(← f.isDir) then t := t.insert (cSourceKey m rel) (← IO.FS.realPath f).toString
  pure t

/-- `cSourceTable` as the elaborator's resolver (`CommandState.cSources`). -/
def cSourceResolver (t : Std.HashMap String String) : String → String → Option String :=
  fun m rel => t[cSourceKey m rel]?

/-- The toolchain's own library: `lib/` of the checkout or installation the running
binary belongs to (`<dir>/.lake/build/bin/wiz`: a checkout, `share/wiz` of the Nix
package and of the release tarball, which tower installs), else `./lib`. As grail's
`findStd`. It is the first module root, so no other root can replace its modules. -/
def toolchainLib : IO System.FilePath := do
  let exe ← IO.appPath
  let guess := ((((exe.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD ".") / "lib"
  if ← (guess / "Prelude.wiz").pathExists then return guess
  pure "lib"

/-- The module roots of `wiz`: the toolchain's library first (`toolchainLib`; `./lib`
only when there is none next to the binary), then `dirs` (the `-I` directories). -/
def roots (dirs : List System.FilePath) : IO (List System.FilePath) :=
  return (← toolchainLib) :: dirs

/-- The modules of `m` from the first root that a later root also has a file for (a
different file): that file is never read. `(module, ignored file)`. -/
def shadowed (roots : List System.FilePath) (m : Std.HashMap Name (System.FilePath × String)) :
    IO (List (Name × System.FilePath)) := do
  let some lib := roots.head? | return []
  let mut out := []
  for (n, (p, _)) in m.toList do
    unless p == lib / relPath n do continue
    let real ← IO.FS.realPath p
    for r in roots.drop 1 do
      let q := r / relPath n
      if ← q.pathExists then
        if (← IO.FS.realPath q) != real then out := (n, q) :: out
  pure out

/-- The modules of `m` (from `loadClosure` or `loadAll`) that come from the first root,
the toolchain's library (`toolchainLib`): their `builtin` registrations are trusted (a
later root can't replace them, since the first root that has a module wins). -/
def fromFirstRoot (roots : List System.FilePath) (m : Std.HashMap Name (System.FilePath × String)) : List Name :=
  match roots with
  | [] => []
  | lib :: _ => m.toList.filterMap fun (n, (p, _)) => if p == lib / relPath n then some n else none

/-- Every module reachable from `src` by imports, with its path and text. Modules that
can't be found are left out (the frontend reports them). -/
partial def loadClosure (roots : List System.FilePath) (src : String) :
    IO (Std.HashMap Name (System.FilePath × String)) := do
  let mut m : Std.HashMap Name (System.FilePath × String) := {}
  let mut todo := importsOf src
  let mut missing : List Name := []
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if m.contains n || missing.contains n then continue
      match ← resolve roots n with
      | none => missing := n :: missing
      | some p =>
        let text ← IO.FS.readFile p
        m := m.insert n (p, text)
        todo := importsOf text ++ todo
  pure m

/-- Every module under a root (recursively), sorted by name. -/
partial def listRoot (root : System.FilePath) : IO (Array (Name × System.FilePath)) := do
  if !(← root.isDir) then return #[]
  let rec go (dir : System.FilePath) (rel : String) : IO (Array (Name × System.FilePath)) := do
    let mut out := #[]
    for e in ← dir.readDir do
      let relE := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
      if ← e.path.isDir then
        if !e.fileName.startsWith "." then out := out ++ (← go e.path relE)
      else if e.path.extension == some "wiz" then
        out := out.push (nameOf relE, e.path)
    pure out
  pure ((← go root "").qsort (fun a b => a.1 < b.1))

/-- Every module under the roots (the first root wins for a name), with paths and texts. -/
def loadAll (roots : List System.FilePath) : IO (Std.HashMap Name (System.FilePath × String)) := do
  let mut m : Std.HashMap Name (System.FilePath × String) := {}
  for r in roots do
    for (n, p) in ← listRoot r do
      if !m.contains n then m := m.insert n (p, ← IO.FS.readFile p)
  pure m

end Wiz.Module
