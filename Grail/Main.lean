import Grail.Cli

/-! grail's executable: `Grail.cliMain` (`Grail/Cli.lean`). -/

def main (args : List String) : IO UInt32 := Grail.cliMain args
