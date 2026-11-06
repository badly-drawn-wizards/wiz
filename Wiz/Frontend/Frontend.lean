import Wiz.Elab.Command

/-!
# The frontend

Parse a command, elaborate it, repeat. The parser tables come from the command state,
so a `syntax` command affects everything after it.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

partial def runFrontend (input : String) (s : CommandState R := {}) : CommandState R :=
  go input.toList.toArray 0 s
where
  go (chars : Array Char) (pos : Nat) (s : CommandState R) : CommandState R :=
    if skipWs chars pos ≥ chars.size then s else
    match parseCommand chars s.tables pos with
    | .ok (cmd, stop) => go chars stop ((elabCommand cmd).run s).2
    | .error e =>
      let msg := (e.render input).splitOn ": " |>.drop 1 |> ": ".intercalate
      go chars (recoverPos chars (skipWs chars pos))
        { s with messages := s.messages.push { info := { start := e.pos, stop := e.pos },
                                                severity := .error, text := msg } }

end Wiz
