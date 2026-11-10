import Wiz.Elab.Command

/-!
# The frontend

Parse a command, elaborate it, repeat. The parser tables come from the command state,
so a `syntax` command affects everything after it.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- Run the frontend on `input` from the state `s`.

`import M` elaborates the library module `M` (once) into the current state. Like
`wiz check` (`Cache.elaborateWith`), a module sees only what it imports: it is first
checked **in isolation**, from the initial state `base` plus its own imports, and its
errors are reported at the `import`. Then, unless the importer's state is still the
initial one (`pristine`: then the isolated result is what it would get), it is
elaborated again into the importer's state, which is what the rest of the file sees.
Each module is checked in isolation once per run (its errors are kept in
`CommandState.checked`, its isolated state in `memo` for as long as one call runs). -/
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
              let (iso, memo) := go' src base srcChars 0
                { base with imported := m :: base.imported, messages := #[], module := m,
                            checked := s.checked.insert m none } memo
              let errs := iso.messages.filter (·.severity == .error)
              (errs, iso.checked.insert m (some errs), some iso, memo.insert m iso)
          let s := { s with checked }
          let (inner, memo) := match iso? with
            -- (a pristine state may still list imports, of modules without commands)
            | some iso => if s.pristine then ({ iso with checked, imported := iso.imported.filter (!s.imported.contains ·) ++ s.imported }, memo) else
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
