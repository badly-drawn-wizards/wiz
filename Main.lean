import Wiz

open Wiz

def usage : String := "usage: wiz parse FILE    print the syntax tree of every command"

def parseCmd (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let r := parseFile input
  for cmd in r.commands do
    IO.println cmd.toSExpr
  for m in r.messages do
    IO.eprintln s!"{path}:{m.render input}"
  pure (if r.messages.isEmpty then 0 else 1)

def main : List String → IO UInt32
  | ["parse", path] => parseCmd path
  | _ => do IO.println usage; pure 0
