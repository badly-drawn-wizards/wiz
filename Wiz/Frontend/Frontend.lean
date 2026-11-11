import Wiz.Elab.Command
import Wiz.Module
import Wiz.Rig.Instances

/-!
# The frontend

Parse a command, elaborate it, repeat. The parser tables come from the command state,
so a `syntax` command affects everything after it.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-! ## Modules in isolation, once per process

Nearly every file starts with `import Prelude`, and `runFrontend` elaborates each import
in isolation (below). A process that runs the frontend many times (the language server,
on every document it opens; a test that checks several files) would elaborate the
Prelude again each time, so the isolated results are kept, per process, under a key that
determines them:

    key = hash(the base state's settings, text of M, M's C headers, key of each import of M)

The base state must be an initial one (`pristine`, with no declarations, imports or info
tree), so that it is determined by its settings: the loader and the C headers enter the
key through the texts they give, and the rest (`termInfo`, the kernel options, …) is
hashed. A module whose imports run in a cycle is not kept (its errors depend on where
the cycle was entered). Since the key determines what the module elaborates to, a hit
gives what elaborating again would: `runFrontend` stays a function of its arguments,
although it reads and writes a global table (an `IO.Ref`, through `unsafeBaseIO`, behind
the opaque `isoGet`/`isoPut`). The table is per quantity rig (`IsoCache`): it holds
states of one `R`, and rigs without an instance are not cached. -/

/-- A module elaborated in isolation: its state, and its errors. -/
structure Isolated (R : Type) where
  state : CommandState R
  errs : Array Msg

instance : Inhabited (Isolated R) := ⟨{ state := {}, errs := #[] }⟩

/-- Where this process keeps the modules elaborated in isolation, for quantities `R`. -/
class IsoCache (R : Type) where
  ref : Option (IO.Ref (Std.HashMap UInt64 (Isolated R)))

instance (priority := low) : IsoCache R := ⟨none⟩

initialize isoCacheZOM : IO.Ref (Std.HashMap UInt64 (Isolated ZeroOneMany)) ← IO.mkRef {}

instance : IsoCache ZeroOneMany := ⟨some isoCacheZOM⟩

/-- How many entries the table keeps (it starts again when full). -/
def isoCacheSize : Nat := 256

private unsafe def isoGetImpl (ref : IO.Ref (Std.HashMap UInt64 (Isolated R))) (k : UInt64) : Option (Isolated R) :=
  unsafeBaseIO (do pure ((← ref.get).get? k))

/-- The module kept under `k`, if any. -/
@[implemented_by isoGetImpl]
opaque isoGet (ref : IO.Ref (Std.HashMap UInt64 (Isolated R))) (k : UInt64) : Option (Isolated R)

private unsafe def isoPutImpl (ref : IO.Ref (Std.HashMap UInt64 (Isolated R))) (k : UInt64) (v : Isolated R) : Isolated R :=
  unsafeBaseIO (do
    ref.modify fun m => (if m.size ≥ isoCacheSize then {} else m).insert k v
    pure v)

/-- Keep `v` under `k`; returns `v` (the caller uses the result, so the write happens). -/
@[implemented_by isoPutImpl]
opaque isoPut (ref : IO.Ref (Std.HashMap UInt64 (Isolated R))) (k : UInt64) (v : Isolated R) : Isolated R

/-- The key of module `m` elaborated in isolation from `base` (see above), or `none` if
it is not to be kept: `base` is not an initial state, or `m`'s imports run in a cycle. -/
partial def isoKey (base : CommandState R) (m : Name) : Option UInt64 := do
  unless base.pristine && base.globals.order.isEmpty && base.imported.isEmpty && base.infos.isEmpty do none
  let g := base.globals
  -- (every option of `Globals` that a module's state depends on or carries)
  let settings := hash (base.termInfo, base.nextScope, g.eager, g.predicativeProp, toString (repr g.regularity),
    toString (repr g.inertReg), g.builtins, g.unboxStructs, g.lazyProofs)
  let (k, _) ← go [] m {}
  pure (mixHash settings k)
where
  go (stack : List Name) (m : Name) (memo : Std.HashMap Name UInt64) : Option (UInt64 × Std.HashMap Name UInt64) :=
    match memo.get? m with
    | some k => some (k, memo)
    | none =>
      if stack.contains m then none else
      match base.loader m with
      | none => some (hash ("unknown", m), memo)
      | some src => do
        -- (9f) the files a module links are resolved per run: not kept across runs
        if base.cSources.isSome && !(Module.cSourcesOf src).isEmpty then none
        let k₀ := mixHash (hash m) (hash src)
        let k₀ := (Module.headersOf src).foldl (fun k h => mixHash k (hash ((base.cHeaders h).getD ""))) k₀
        let (k, memo) ← (Module.importsOf src).foldlM (fun (k, memo) n => do
          let (kn, memo) ← go (m :: stack) n memo
          pure (mixHash k kn, memo)) (k₀, memo)
        pure (k, memo.insert m k)

variable [IsoCache R]

/-- Run the frontend on `input` from the state `s`.

`import M` elaborates the library module `M` (once) into the current state. Like
`wiz check` (`Cache.elaborateWith`), a module sees only what it imports: it is first
checked **in isolation**, from the initial state `base` plus its own imports, and its
errors are reported at the `import`. Then, unless the importer's state is still the
initial one (`pristine`: then the isolated result is what it would get), it is
elaborated again into the importer's state, which is what the rest of the file sees.
Each module is checked in isolation once per run (its errors are kept in
`CommandState.checked`, its isolated state in `memo` for as long as one call runs), and,
from an initial state, once per process (`isoKey`). -/
partial def runFrontend (input : String) (s : CommandState R := {}) : CommandState R :=
  go input s input.toList.toArray 0 s
where
  go (input : String) (base : CommandState R) (chars : Array Char) (pos : Nat) (s : CommandState R) : CommandState R :=
    (go' input base chars pos s {}).1
  go' (input : String) (base : CommandState R) (chars : Array Char) (pos : Nat) (s : CommandState R)
      (memo : Std.HashMap Name (CommandState R)) : CommandState R × Std.HashMap Name (CommandState R) :=
    if skipWs chars pos ≥ chars.size then (s, memo) else
    match parseCommand chars s.tables pos with
    | .ok (cmd, stop) =>
      if cmd.isOfKind "command.import" then
        let m := ((cmd.getArg 1).getId?).getD "_"
        if s.imported.contains m then go' input base chars stop s memo else
        let err (text : String) : CommandState R :=
          { s with messages := s.messages.push { info := cmd.info, severity := .error, text } }
        match s.loader m, s.checked.get? m with
        | none, _ => go' input base chars stop (err s!"unknown module {m}") memo
        | some _, some none => go' input base chars stop (err s!"import cycle through {m}") memo
        | some src, done =>
          let srcChars := src.toList.toArray
          -- in isolation (unless already done in this run)
          let (isoErrs, checked, iso?, memo) : Array Msg × Std.HashMap Name (Option (Array Msg)) × Option (CommandState R) × Std.HashMap Name (CommandState R) := match done with
            | some (some errs) => (errs, s.checked, memo.get? m, memo)
            | _ =>
              let isolate (_ : Unit) :=
                let (iso, memo) := go' src base srcChars 0
                  { base with imported := m :: base.imported, messages := #[], module := m,
                              checked := s.checked.insert m none } memo
                (({ state := iso, errs := iso.messages.filter (·.severity == .error) } : Isolated R), iso.checked, memo)
              -- kept from an earlier run in this process, or elaborated (and kept)
              let (e, checked, memo) := match IsoCache.ref (R := R), isoKey base m with
                | some ref, some k => match isoGet ref k with
                  | some e => (e, s.checked, memo)
                  | none => let (e, checked, memo) := isolate (); (isoPut ref k e, checked, memo)
                | _, _ => isolate ()
              (e.errs, checked.insert m (some e.errs), some e.state, memo.insert m e.state)
          let s := { s with checked }
          let (inner, memo) := match iso? with
            -- (a pristine state may still list imports, of modules without commands; the
            -- isolated state may come from another run: the loader and headers are ours)
            | some iso => if s.pristine then ({ iso with checked, loader := s.loader, cHeaders := s.cHeaders, cSources := s.cSources,
                                                          imported := iso.imported.filter (!s.imported.contains ·) ++ s.imported }, memo) else
                go' src base srcChars 0 { s with imported := m :: s.imported, messages := #[], module := m } memo
            | none => go' src base srcChars 0 { s with imported := m :: s.imported, messages := #[], module := m } memo
          let errs := if isoErrs.isEmpty then inner.messages.filter (·.severity == .error) else isoErrs
          let msg : Msg := { info := cmd.info, severity := .error,
                             text := s!"module {m} has errors: {errs.toList.map (·.render src)}" }
          let msgs := if errs.isEmpty then s.messages else s.messages.push msg
          -- (a module's warnings, such as an unchecked `builtin`, are shown at the import)
          let msgs := msgs ++ (inner.messages.filter (·.severity == .warning)).map fun w =>
            { info := cmd.info, severity := .warning, text := s!"module {m}: {w.render src}" }
          -- the info tree is positions in this file: keep only ours
          go' input base chars stop { inner with messages := msgs, module := s.module, infos := s.infos } memo
      else go' input base chars stop (step cmd s) memo
    | .error e =>
      let msg := (e.render input).splitOn ": " |>.drop 1 |> ": ".intercalate
      go' input base chars (recoverPos chars (skipWs chars pos))
        { s with messages := s.messages.push { info := { start := e.pos, stop := e.pos },
                                                severity := .error, text := msg } } memo

  /-- Elaborate one command, recording where the declarations it adds come from. -/
  step (cmd : Syntax) (s : CommandState R) : CommandState R :=
    let before := s.globals.order.size
    let s' := ((elabCommand cmd).run { s with pristine := false }).2
    let added := s'.globals.order.extract before s'.globals.order.size
    { s' with declSites := added.foldl (fun m n => m.insert n (cmd.info, s.module)) s'.declSites }

end Wiz
