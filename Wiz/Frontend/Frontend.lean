import Wiz.Elab.Command

/-!
# The frontend

Parse a command, elaborate it, repeat. The parser tables come from the command state,
so a `syntax` command affects everything after it.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- `import M`: elaborate the library module `M` (once) into the current state. Its
messages are reported at the `import` if it has errors. -/
partial def runFrontend (input : String) (s : CommandState R := {}) : CommandState R :=
  go input.toList.toArray 0 s
where
  go (chars : Array Char) (pos : Nat) (s : CommandState R) : CommandState R :=
    if skipWs chars pos ≥ chars.size then s else
    match parseCommand chars s.tables pos with
    | .ok (cmd, stop) =>
      if cmd.isOfKind "command.import" then
        let m := ((cmd.getArg 1).getId?).getD "_"
        if s.imported.contains m then go chars stop s else
        match s.loader m with
        | none =>
          let msg : Msg := { info := cmd.info, severity := .error, text := s!"unknown module {m}" }
          go chars stop { s with messages := s.messages.push msg }
        | some src =>
          let inner := runFrontend src { s with imported := m :: s.imported, messages := #[], module := m }
          let errs := inner.messages.filter (·.severity == .error)
          let msg : Msg := { info := cmd.info, severity := .error,
                             text := s!"module {m} has errors: {errs.toList.map (·.render src)}" }
          let msgs := if errs.isEmpty then s.messages else s.messages.push msg
          -- the info tree is positions in this file: keep only ours
          go chars stop { inner with messages := msgs, module := s.module, infos := s.infos }
      else go chars stop (step cmd s)
    | .error e =>
      let msg := (e.render input).splitOn ": " |>.drop 1 |> ": ".intercalate
      go chars (recoverPos chars (skipWs chars pos))
        { s with messages := s.messages.push { info := { start := e.pos, stop := e.pos },
                                                severity := .error, text := msg } }

  /-- Elaborate one command, recording where the declarations it adds come from. -/
  step (cmd : Syntax) (s : CommandState R) : CommandState R :=
    let before := s.globals.order.size
    let s' := ((elabCommand cmd).run s).2
    let added := s'.globals.order.extract before s'.globals.order.size
    { s' with declSites := added.foldl (fun m n => m.insert n (cmd.info, s.module)) s'.declSites }

end Wiz
