import Tower

/-! `tower`, the Wiz toolchain manager (stage 26): `Tower/Cli.lean`. -/

def main (args : List String) : IO UInt32 := do
  Tower.main (← Tower.defaultEnv) args
