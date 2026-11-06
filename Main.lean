import Wiz

open Wiz

def usage : String := "usage:
  wiz parse FILE    print the syntax tree of every command
  wiz check FILE    elaborate and type check (quantities: 0, 1, ω)"

def parseCmd (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let r := parseFile input
  for cmd in r.commands do
    IO.println cmd.toSExpr
  for m in r.messages do
    IO.eprintln s!"{path}:{m.render input}"
  pure (if r.messages.isEmpty then 0 else 1)

def checkCmd (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let s := runFrontend (R := ZeroOneMany) input
  for m in s.messages do
    let line := s!"{path}:{m.render input}"
    if m.severity == .error then IO.eprintln line else IO.println line
  pure (if s.messages.any (·.severity == .error) then 1 else 0)

def main : List String → IO UInt32
  | ["parse", path] => parseCmd path
  | ["check", path] => checkCmd path
  | _ => do IO.println usage; pure 0
