import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def cGroup : Group where
  name := "c"
  exercise := "Exercise 8.2"
  cases := nativeCases false

builtin_initialize registerGroup cGroup

end Tests.Elab
