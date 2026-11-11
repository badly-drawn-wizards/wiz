import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## 25: concurrency (runtime/wiz.c threads, lib/Session.wiz, lib/MVar.wiz) -/

/-- The dependent protocol of docs/stages/25-concurrency.md: send a length `n`, then `n`
numbers, receive their sum; the server and client as pure processes and over channels. -/
def concSum : String := "import IO
import Session
def sendMany (k : Proto) : Nat → Proto
  | .zero => k
  | .succ n => .send Nat (fun _ => sendMany k n)
def ack : Proto := .recv Nat (fun _ => .done)
def sumProto : Proto := .send Nat (fun n => sendMany ack n)
def nums : (n : Nat) → Proc Nat (sendMany ack n)
  | .zero => fun s => s
  | .succ n => (n + 1, nums n)
def client (m : Nat) : Proc Nat sumProto := (m, nums m)
def serverMany : (n : Nat) → (acc : Nat) → Proc Unit (Proto.dual (sendMany ack n))
  | .zero, acc => (acc, ())
  | .succ n, acc => fun x => serverMany n (acc + x)
def server : Proc Unit (Proto.dual sumProto) := fun n => serverMany n 0
def serveMany : (n : Nat) → (acc : Nat) → (1 c : Chan (Proto.dual (sendMany ack n))) → IO Unit
  | .zero, acc => fun c => Chan.send c acc (fun c' => Chan.close c' (IO.pure ()))
  | .succ n, acc => fun c =>
      Chan.recv c (fun x c' => serveMany n (acc + x) c')
def serve (1 c : Chan (Proto.dual sumProto)) : IO Unit :=
  Chan.recv c (fun n c' => serveMany n 0 c')
def sendNums : (n : Nat) → (1 c : Chan (sendMany ack n)) → IO Nat
  | .zero => fun c => Chan.recv c (fun s c' => Chan.close c' (IO.pure s))
  | .succ n => fun c => Chan.send c (n + 1) (fun c' => sendNums n c')
def runClient (m : Nat) (1 c : Chan sumProto) : IO Nat :=
  Chan.send c m (fun c' => sendNums m c')
"

/-- A chain of threads: each adds one to every element of a list and passes it on; the
last sums, and the sum travels back up. -/
def concChain : String := "import IO
import Session
def Q : Proto := .send (List Nat) (fun _ => .recv Nat (fun _ => .done))
def bump : List Nat → List Nat
  | .nil => .nil
  | .cons x xs => .cons (x + 1) (bump xs)
def total : List Nat → Nat
  | .nil => 0
  | .cons x xs => x + total xs
def upto : Nat → List Nat
  | .zero => .nil
  | .succ n => .cons n (upto n)
def stage : Nat → (1 c : Chan (Proto.dual Q)) → IO Unit
  | .zero => fun c => Chan.recv c (fun xs c' =>
      Chan.send c' (total xs) (fun c'' => Chan.close c'' (IO.pure ())))
  | .succ n => fun c => Chan.recv c (fun xs c' =>
      Chan.fork Q (stage n) (fun d => Chan.send d (bump xs) (fun d' =>
        Chan.recv d' (fun s d'' => Chan.close d''
          (Chan.send c' s (fun c'' => Chan.close c'' (IO.pure ())))))))
def shared : List Nat := upto 100
def main : IO Unit := Chan.fork Q (stage 50) (fun d =>
  Chan.send d shared (fun d' => Chan.recv d' (fun s d'' =>
    Chan.close d'' (IO.bind (IO.println (Nat.toString s)) (fun _ => IO.println (Nat.toString (total shared)))))))
"

/-- A cancellable protocol (decision CS13): up to `n` numbers, each one a value or a
cancel. -/
def concCancel : String := "import IO
import Session
def items : Nat → Proto
  | .zero => .done
  | .succ n => Proto.sendC Nat (fun _ => items n)
def onMsg (n acc : Nat) (serve : (acc : Nat) → (1 c : Chan (Proto.dual (items n))) → IO Unit) :
    (m : Msg Nat) → (1 c : Chan (Proto.dual (Msg.next (fun _ => items n) m))) → IO Unit
  | .val x => fun c => serve (acc + x) c
  | .cancel => fun c => Chan.close c (IO.println (String.append \"cancelled after \" (Nat.toString acc)))
def serveItems : (n : Nat) → (acc : Nat) → (1 c : Chan (Proto.dual (items n))) → IO Unit
  | .zero, acc => fun c => Chan.close c (IO.println (String.append \"all: \" (Nat.toString acc)))
  | .succ n, acc => fun c =>
      Chan.recv c (fun m c' => onMsg n acc (serveItems n) m c')
def client (1 c : Chan (items 3)) : IO Unit :=
  Chan.send c (.val 10) (fun c1 =>
    Chan.send c1 (.val 20) (fun c2 =>
      Chan.cancel c2 (IO.pure ())))
def full (1 c : Chan (items 2)) : IO Unit :=
  Chan.send c (.val 1) (fun c1 =>
    Chan.send c1 (.val 2) (fun c2 => Chan.close c2 (IO.pure ())))
def main : IO Unit := Chan.fork (items 3) (serveItems 3 0) (fun c => client c)
"

/-- Eight threads bump one counter a thousand times each (MVar.modify: the linear
borrow/fill discipline), under a lock, and report through an MVar. -/
def concCounter : String := "import IO
import Session
import MVar
def worker (m : MVar Nat) (l : Lock) : Nat → IO Unit
  | .zero => IO.pure ()
  | .succ n => IO.bind (MVar.modify m (fun x => x + 1)) (fun _ =>
      IO.bind (Lock.with l (IO.pure ())) (fun _ => worker m l n))
def spawnN (m : MVar Nat) (l : Lock) (done : MVar Nat) : Nat → IO Unit
  | .zero => IO.pure ()
  | .succ k => Chan.fork Proto.done (fun c => Chan.close c (IO.bind (worker m l 1000) (fun _ => MVar.put done 1)))
      (fun c => Chan.close c (spawnN m l done k))
def waitN (done : MVar Nat) : Nat → IO Unit
  | .zero => IO.pure ()
  | .succ k => IO.bind (MVar.take done) (fun _ => waitN done k)
def main : IO Unit := do1
  m ← MVar.newFull 0;
  l ← Lock.new;
  done ← MVar.new (A := Nat);
  spawnN m l done 8;
  waitN done 8;
  n ← MVar.take m;
  IO.println (Nat.toString n)
"

/-- Two threads observe one lazy stream (shared lazy cells are not overwritten, 25a). -/
def concStream : String := "import IO
import Session
import MVar
coinductive Stream (A : Type) where
  head : A
  tail : Stream A
def natsFrom (n : Nat) : Stream Nat
  | .head => n
  | .tail => natsFrom (n + 1)
def sumN : Nat → Stream Nat → Nat
  | .zero, _ => 0
  | .succ k, s => s.head + sumN k s.tail
def main : IO Unit := IO.bind (MVar.new (A := Nat)) (fun r =>
  let s := natsFrom 0;
  Chan.fork Proto.done (fun c => Chan.close c (MVar.put r (sumN 2000 s)))
    (fun c => Chan.close c (IO.bind (MVar.take r) (fun a =>
      IO.println (Nat.toString (a + sumN 2000 s))))))
"

def concGroup : Group where
  name := "conc"
  exercise := "lib/Session.wiz, lib/MVar.wiz, runtime threads (stage 25)"
  cases := [
    { name := "a dependent protocol: the pure semantics `link` runs it", run := fun _ =>
        okLibs (concSum ++ "#eval (link sumProto (client 100) server).1") ["5050"] },
    { name := "the same protocol over a channel, server in a new thread", run := fun _ =>
        cRunLibs (concSum ++ "def main : IO Unit := Chan.fork sumProto serve (fun c =>\n" ++
          "  IO.bind (runClient 1000 c) (fun s => IO.println (Nat.toString s)))") "500500\n" },
    { name := "Proc.runLinked: the model is `link`, compiled code runs threads (differential)", run := fun _ => do
        okLibs (concSum ++ "#eval (link sumProto (client 300) server).1") ["45150"]
        cRunLibs (concSum ++ "def main : IO Unit := IO.bind (Proc.runLinked sumProto (client 300) server)\n" ++
          "  (fun r => IO.println (Nat.toString r.1))") "45150\n" },
    { name := "a chain of 51 threads; endpoints move into children", run := fun _ =>
        cRunLibs concChain "9950\n4950\n" },
    { name := "cancellation is a branch of the protocol", run := fun _ => do
        cRunLibs concCancel "cancelled after 30\n"
        cRunLibs (concCancel.replace "def main : IO Unit := Chan.fork (items 3) (serveItems 3 0) (fun c => client c)" "" ++
          "def main : IO Unit := Chan.fork (items 2) (serveItems 2 0) (fun c => full c)") "all: 3\n" },
    { name := "MVars and locks: eight threads, one counter", run := fun _ =>
        cRunLibs concCounter "8000\n" },
    { name := "a lazy stream shared between threads", run := fun _ =>
        cRunLibs concStream "3998000\n" },
    { name := "an endpoint can't be used twice, dropped, or closed twice", run := fun _ => do
        failsLibs (concSum ++ "def twice (1 c : Chan sumProto) : IO Nat :=\n" ++
          "  Chan.send c 1 (fun c' => runClient 1 c)") "quantity 1"
        failsLibs "import IO\nimport Session\ndef leak (1 c : Chan Proto.done) : IO Unit := IO.pure ()" "quantity 1"
        failsLibs "import IO\nimport Session\ndef dupe (1 c : Chan Proto.done) : IO Unit := Chan.close c (Chan.close c (IO.pure ()))" "quantity 1" },
    { name := "a closure that captured an endpoint is linear itself", run := fun _ =>
        failsLibs ("import IO\nimport Session\n" ++
          "def capture (1 c : Chan Proto.done) : Unit → IO Unit := fun _ => Chan.close c (IO.pure ())\n" ++
          "def dupf (1 c : Chan Proto.done) : IO Unit := let f := capture c; IO.bind (f ()) (fun _ => f ())") "quantity" },
    { name := "the protocol is checked: wrong message type, wrong step", run := fun _ => do
        failsLibs (concSum ++ "def bad (1 c : Chan sumProto) : IO Unit :=\n" ++
          "  Chan.send c Bool.true (fun c' => Chan.close c' (IO.pure ()))") "mismatch"
        failsLibs (concSum ++ "def bad (1 c : Chan sumProto) : IO Unit := Chan.close c (IO.pure ())") "mismatch" },
    { name := "endpoints can't be forged, retyped, sent, or stored", run := fun _ => do
        failsLibs "import IO\nimport Session\ndef bad (1 c : Chan Proto.done) : Chan (.send Nat (fun _ => .done)) := c" "mismatch"
        failsLibs ("import IO\nimport Session\ndef bad (1 c : Chan (.send Nat (fun _ => .done))) : IO (Chan (.recv Nat (fun _ => .done))) :=\n" ++
          "  Chan.sendRaw c 1") "private"
        -- an endpoint is not a message (no delegation: the channel graph stays a forest)
        failsLibs ("import IO\nimport Session\ndef bad (1 c : Chan (.send (Chan Proto.done) (fun _ => .done))) (1 d : Chan Proto.done) : IO Unit :=\n" ++
          "  Chan.send c d (fun c' => Chan.close c' (IO.pure ()))") "quantity 1"
        failsLibs ("import IO\nimport Session\nimport MVar\ndef bad (m : MVar (Chan Proto.done)) (1 d : Chan Proto.done) : IO Unit :=\n" ++
          "  MVar.put m d") "quantity 1" },
    { name := "a lock guard and an MVar hole must be given back exactly once", run := fun _ => do
        failsLibs "import IO\nimport MVar\ndef bad (l : Lock) : IO Unit := Lock.acquire l (fun g => IO.pure ())" "quantity 1"
        failsLibs ("import IO\nimport MVar\ndef bad {B : Type} (l : Lock) (b : B) : IO B :=\n" ++
          "  Lock.acquire l (fun g => Lock.release l g (Lock.release l g (IO.pure b)))") "quantity 1"
        failsLibs "import IO\nimport MVar\ndef bad (m : MVar Nat) : IO Nat := MVar.borrow m (fun a h => IO.pure a)" "quantity 1"
        failsLibs "import IO\nimport MVar\ndef forge (l : Lock) : IO (Lock.Guard l) := Lock.acquireRaw l" "private" }
  ]

builtin_initialize registerGroup concGroup

end Tests.Elab
