import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- A user-declared `ShareLet` (no HDL library): the hook fires on a `let` in check mode
with no explicit quantity, and only when an instance exists. -/
def shareLetHook : String := "import Prelude
structure W where
  n : Nat
class ShareLet (A B : Type) where
  share : A → (A → B) → B
instance : ShareLet W W where
  share := fun x f => f (W.mk (x.n + 100))
def t1 : W := let y := W.mk 1; y
def t2 : W := let ω y := W.mk 1; y
def t3 : Nat := let y := 1; y
#eval t1.n
#eval t2.n
#eval t3
"

/-- Circuits whose Verilog the `hdl` group looks at: a counter (non-zero initial value), a
64-bit state (an initial value above 2^32) and a circuit with an input and a pair state. -/
def hdlVerilogSrc : String := "import Hdl.Core
def u8 : HwTy := HwTy.bits 8
def c1 : Circuit (HwTy.bits 1) u8 := Circuit.mk u8 (BitVec.ofNat 8 250) (fun s u => Hw.pair (Hw.add s (Hw.lit 8 1)) s)
def v1 : String := Verilog.emit (Circuit.netlist \"counter\" c1)
def u64 : HwTy := HwTy.bits 64
def c2 : Circuit u8 u64 := Circuit.mk u64 (BitVec.ofNat 64 13835062455471964160) (fun s x => Hw.pair (Hw.add s (Hw.lit 64 1)) s)
def v2 : String := Verilog.emit (Circuit.netlist \"wide\" c2)
def c3 : Circuit u8 u8 := Circuit.mk (HwTy.prod u8 u8) (BitVec.ofNat 8 1, BitVec.ofNat 8 2)
  (fun s x => Hw.pair (Hw.pair x (Hw.fst s)) (Hw.mux (Hw.ult x (Hw.snd s)) (Hw.fst s) (Hw.sub x (Hw.snd s))))
def v3 : String := Verilog.emit (Circuit.netlist \"pairs\" c3)
"

def hdlGroup : Group where
  name := "hdl"
  exercise := "HDL stage S0 (hdl-plan H14)"
  cases := [
    { name := "auto-share: a let becomes ShareLet.share when an instance exists", run := fun _ =>
        okLibs shareLetHook ["101", "1", "1"] },
    { name := "L2 examples: hash-consed netlists are no bigger, three simulations agree; the doubling chain is linear", run := fun _ => do
        -- r1–r4: (nodes hash-consed, nodes naive), then the value simulation and the netlist
        -- simulations (hash-consed, naive). q1: the chain at k = 20 (nodes, adders, builder
        -- work). q2: the chain at k = 3 simulated. q3: the chain without sharing (`let ω`) at
        -- k = 10 (nodes, work, naive nodes). Last: (x + y) * (y + x) has one adder.
        okLibs (← IO.FS.readFile "examples/hdl.wiz") ["((4, 4), .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))), .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))), .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))))", "((7, 7), .cons 250 (.cons 251 (.cons 252 (.cons 253 (.cons 254 (.cons 255 .nil))))), .cons 250 (.cons 251 (.cons 252 (.cons 253 (.cons 254 (.cons 255 .nil))))), .cons 250 (.cons 251 (.cons 252 (.cons 253 (.cons 254 (.cons 255 .nil))))))", "((28, 35), .cons 1 (.cons 1 (.cons 2 (.cons 1 (.cons 3 (.cons 3 .nil))))), .cons 1 (.cons 1 (.cons 2 (.cons 1 (.cons 3 (.cons 3 .nil))))), .cons 1 (.cons 1 (.cons 2 (.cons 1 (.cons 3 (.cons 3 .nil))))))", "((8, 9), .cons 1 (.cons 4 (.cons 9 (.cons 15 (.cons 216 (.cons 162 .nil))))), .cons 1 (.cons 4 (.cons 9 (.cons 15 (.cons 216 (.cons 162 .nil))))), .cons 1 (.cons 4 (.cons 9 (.cons 15 (.cons 216 (.cons 162 .nil))))))", "(22, 20, 22)", "(.cons 8 (.cons 16 (.cons 24 (.cons 32 (.cons 64 (.cons 56 .nil))))), .cons 8 (.cons 16 (.cons 24 (.cons 32 (.cons 64 (.cons 56 .nil))))))", "(11, 2047, 2047)", "4"] },
    { name := "auto-share elaborates an object let to ShareLet.share; an erased or meta let stays a let", run := fun _ =>
        okLibs ("import Hdl.Core\ndef f {r : HwTy → Type} [Hw r] (x : r (HwTy.bits 8)) : r (HwTy.bits 8) := let y := Hw.add x x; Hw.add y y\n" ++
          "def g {r : HwTy → Type} [Hw r] (x : r (HwTy.bits 8)) (k : Nat) : r (HwTy.bits 8) := let j := Nat.succ k; Hw.lit 8 j\n#erase f\n#erase g")
          ["f := (λr. (λinst✝. (λx. (((((ShareLet.share ◾) ◾) ((((instShareLetRARB ◾) #1) ⟨0 8⟩) ⟨0 8⟩)) (((((Hw.add ◾) #1) 8) #0) #0)) (λy. (((((Hw.add ◾) #2) 8) #0) #0))))))",
           "g := (λr. (λinst✝. (λx. (λk. (let j := (Nat.succ #0); ((((Hw.lit ◾) #3) 8) #0))))))"] },
    { name := "Verilog: declarations before use (regs, wires, then the updates), sized initial values", run := fun _ =>
        okLibs (hdlVerilogSrc ++ "#eval v1\n")
          ["\"module counter(input clk, input [0:0] x, output [7:0] y);\\n  reg [7:0] r; initial r = 8'd250;\\n  wire [7:0] n3 = r + 8'd1;\\n  always @(posedge clk) r <= n3;\\n  assign y = r;\\nendmodule\\n\""] },
    { name := "S1: bundles, composition, reset and enable at random cycles; netlist simulation = values; names, test bench, PCF, VCD", run := fun _ => do
        -- t1–t6: (agreement of the netlist simulations with `Circuit.run`, the netlist size
        -- and the outputs) for the bundled counter, a delay chain, `par`, a feedback loop,
        -- two instances, and reset and enable driven at random cycles; then the counter's
        -- Verilog (named ports and registers, `if (rst) … else if (en)`), pin constraints,
        -- the problems of a bad pin list, a waveform, and the sizes of a list of designs
        okLibs (← IO.FS.readFile "examples/hdl-compose.wiz")
          ["(.true, .cons 17 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 4 (.cons 6 (.cons 8 (.cons 8 (.cons 10 (.cons 10 (.cons 10 (.cons 12 (.cons 14 (.cons 14 (.cons 14 (.cons 16 (.cons 19 (.cons 16 (.cons 14 (.cons 12 (.cons 12 (.cons 12 (.cons 12 (.cons 10 (.cons 8 (.cons 6 (.cons 6 (.cons 4 (.cons 2 .nil)))))))))))))))))))))))))))))))",
           "(.true, .cons 5 (.cons 9 (.cons 7 (.cons 0 (.cons 0 (.cons 140 (.cons 173 (.cons 172 (.cons 30 (.cons 11 (.cons 226 (.cons 250 (.cons 211 .nil)))))))))))))",
           "(.true, .cons 9 (.cons 2389 (.cons 1798 (.cons 150 (.cons 40 (.cons 17709 (.cons 24795 (.cons 35041 (.cons 43032 .nil)))))))))",
           "(.true, .cons 4 (.cons 1 (.cons 1 (.cons 26 (.cons 128 (.cons 123 (.cons 250 (.cons 41 (.cons 185 .nil)))))))))",
           "(.true, .cons 29 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 .nil)))))))))))))))))))))))))))))))))))))))))",
           "(.true, .cons 19 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 2 (.cons 0 (.cons 0 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))",
           "\"module counter(input clk, input [0:0] rst, input [0:0] en, input [0:0] go, output [3:0] leds, output [0:0] top);\\n  reg [3:0] count; initial count = 4'd0;\\n  reg [0:0] up; initial up = 1'd1;\\n  wire [3:0] n6 = count + 4'd1;\\n  wire [3:0] n7 = count - 4'd1;\\n  wire [3:0] n8 = up ? n6 : n7;\\n  wire [3:0] next = go ? n8 : count;\\n  wire [0:0] n11 = next == 4'd9;\\n  wire [0:0] n13 = next == 4'd0;\\n  wire [0:0] n16 = n13 ? 1'd1 : up;\\n  wire [0:0] n17 = n11 ? 1'd0 : n16;\\n  wire [0:0] n18 = count == 4'd9;\\n  always @(posedge clk) if (rst) count <= 4'd0; else if (en) count <= next;\\n  always @(posedge clk) if (rst) up <= 1'd1; else if (en) up <= n17;\\n  assign leds = count;\\n  assign top = n18;\\nendmodule\\n\"",
           "\"set_io clk 21\\nset_io rst 1\\nset_io en 2\\nset_io go 3\\nset_io leds[0] 99\\nset_io leds[1] 98\\nset_io leds[2] 97\\nset_io leds[3] 96\\nset_io top 95\\n\"",
           ".cons \"no pin for port rst\" (.cons \"no pin for port en\" (.cons \"port leds has 4 bits, one pin given\" (.cons \"no pin for port top\" (.cons \"pin for no port: led\" .nil))))",
           "\"$timescale 1ns $end\\n$scope module counter $end\\n$var wire 1 ! clk $end\\n$var wire 1 \\\" go $end\\n$var wire 4 # leds $end\\n$var wire 1 $ top $end\\n$var wire 4 % count $end\\n$var wire 1 & up $end\\n$upscope $end\\n$enddefinitions $end\\n#0\\n0!\\n0\\\"\\nb0000 #\\n0$\\nb0000 %\\n1&\\n#1\\n1!\\n#2\\n0!\\n#3\\n1!\\n#4\\n0!\\n#5\\n1!\\n#6\\n0!\\n1\\\"\\n#7\\n1!\\n#8\\n\"",
           ".cons 17 (.cons 5 (.cons 4 .nil))"] },
    { name := "Verilog: Icarus Verilog accepts the emitted modules (skipped without iverilog on PATH)", run := fun _ => do
        let found ← (do let o ← IO.Process.output { cmd := "iverilog", args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
        unless found do skip "no iverilog"; return
        let s := runFrontend (R := ZeroOneMany) (hdlVerilogSrc ++ "#eval v1\n#eval v2\n#eval v3\n")
          { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render ""
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
        IO.FS.withTempDir fun dir => do
          for m in s.messages.toList, i in [0:3] do
            -- the message is the string as `#eval` prints it: quoted, newlines escaped
            let text := ((m.text.drop 1).dropRight 1).replace "\\n" "\n"
            let file := dir / s!"m{i}.v"
            IO.FS.writeFile file text
            let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "out.vvp").toString, file.toString] }
            unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects module {i}:\n{o.stderr}\n{text}")
        -- the composed circuits, and the generated test bench replaying the counter with
        -- reset and enable at random cycles against its value simulation
        let src ← IO.FS.readFile "examples/hdl-compose.wiz"
        let s := runFrontend (R := ZeroOneMany) (src ++ "\n#eval vCounter\n#eval vTwo\n#eval vPipe\n#eval tbCounter\n#eval vecCounter\n")
          { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render ""
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
        let texts := (s.messages.toList.map (·.text)).drop 11
        let unq (t : String) : String := ((t.drop 1).dropRight 1).replace "\\n" "\n" |>.replace "\\\"" "\""
        IO.FS.withTempDir fun dir => do
          let names := ["counter.v", "two.v", "pipe.v", "tb.v", "counter.vec"]
          for t in texts, nm in names do IO.FS.writeFile (dir / nm) (unq t)
          for nm in ["two.v", "pipe.v"] do
            let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "x.vvp").toString, (dir / nm).toString] }
            unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects {nm}:\n{o.stderr}")
          let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "tb.vvp").toString, (dir / "tb.v").toString, (dir / "counter.v").toString], cwd := dir }
          unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects the test bench:\n{o.stderr}")
          let r ← IO.Process.output { cmd := "vvp", args := #["-n", (dir / "tb.vvp").toString], cwd := dir }
          unless (r.stdout.splitOn "PASS counter: 60 cycles").length > 1 do
            throw (IO.userError s!"test bench: {r.stdout}{r.stderr}") }
  ]

initialize registerGroup hdlGroup

end Tests.Elab
