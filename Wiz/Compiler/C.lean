import Wiz.Compiler.IR
import Wiz.Compiler.Run

/-!
# C code generation

Each IR function becomes a C function on `wiz_val`s, plus a *boxed* version taking an
array, which closures point to. Variables become locals, `case` a `switch` on the
tag, join points labelled blocks entered with `goto` (their parameters are locals
assigned before the jump), and `dup`/`drop` calls to the runtime (`runtime/wiz.c`,
which is pasted at the top of the output).
-/

namespace Wiz.C

open IR

/-- The runtime, embedded in the compiler. (Lake does not track `include_str`: after
editing `runtime/wiz.c`, change this file too, e.g. this counter: 33.) -/
def runtime : String := include_str "../../runtime/wiz.c"

/-- A C identifier for a Wiz name: letters and digits stay, anything else is `_xx`. -/
def mangle (n : Name) : String :=
  "w_" ++ String.join (n.toList.map fun c =>
    if c.isAlphanum then c.toString
    else "_" ++ (Nat.toDigits 16 c.toNat).asString ++ "_")

def var (x : Var) : String := s!"x{x}"

/-- The C wrapper of a foreign function. -/
def externWrapper (key : Name) : String := "wiz_ext" ++ (mangle key).drop 1

/-- The variables a body binds (to declare them up front). -/
partial def bound (b : Body) (acc : Array Var := #[]) : Array Var :=
  match b with
  | .vdecl x _ b => bound b (acc.push x)
  | .case _ alts => alts.foldl (fun acc a => bound a acc) acc
  | .jdecl _ ps body k => bound k (bound body (acc ++ ps))
  | .dup _ b | .drop _ b => bound b acc
  | _ => acc

def args (xs : Array Var) : String := ", ".intercalate (xs.toList.map var)

def expr (arities : Std.HashMap Name Nat) (x : Var) : Expr → String
  | .erased => s!"{var x} = WIZ_BOX(0);"
  | .lit n =>
    if n < 2 ^ 62 then s!"{var x} = WIZ_BOX({n}UL);" else s!"{var x} = wiz_nat_lit(\"{n}\");"
  | .ctor t as =>
    if as.isEmpty then s!"{var x} = WIZ_BOX({t});"
    else
      let sets := as.toList.zipIdx.map fun (a, i) => s!" WIZ_SET({var x}, {i}, {var a});"
      s!"{var x} = wiz_ctor_new({t}, {as.size});" ++ String.join sets
  | .proj i y => s!"{var x} = wiz_proj({var y}, {i});"
  | .fap f as => s!"{var x} = {mangle f}({args as});"
  | .pap f as =>
    let arr := if as.isEmpty then "NULL" else s!"(wiz_val[]){lb}{args as}{rb}"
    s!"{var x} = wiz_clo_new({mangle f}_boxed, {(arities.get? f).getD 0}, {as.size}, {arr});"
  | .ap f as => s!"{var x} = wiz_apply({var f}, {as.size}, (wiz_val[]){lb}{args as}{rb});"
  | .reset y => s!"{var x} = wiz_reset({var y});"
  | .reuse tok t as =>
    let sets := as.toList.zipIdx.map fun (a, i) => s!" WIZ_SET({var x}, {i}, {var a});"
    s!"{var x} = wiz_reuse({var tok}, {t}, {as.size});" ++ String.join sets
  | .prim op as =>
    let fn := match op with
      | "nat.succ" => "wiz_nat_succ" | "nat.pred" => "wiz_nat_pred"
      | "nat.add" => "wiz_nat_add" | "nat.sub" => "wiz_nat_sub" | "nat.mul" => "wiz_nat_mul"
      | "nat.beq" => "wiz_nat_beq" | "nat.blt" => "wiz_nat_blt" | "lazyTag" => "wiz_lazy_tag" | "lazySet" => "wiz_lazy_set" | "memo" => "wiz_memo"
      | "tag" => "wiz_tag_of" | "natTag" => "wiz_nat_tag" | "fieldAt" => "wiz_field_at" | "mkObj" => "wiz_mk_obj"
      | "dropMoved" => "wiz_drop_moved"
      | op => if op.startsWith "nat." then "wiz_nat_" ++ (op.drop 4).toString
        else if (RVal.ExternSig.ofKey? op).isSome then externWrapper op else "wiz_unknown_prim"
    s!"{var x} = {fn}({args as});"
where
  lb := "{"
  rb := "}"

/-- The foreign functions a program uses. -/
partial def externs (decls : Array IR.Decl) : Array Name :=
  let rec go : Body → Array Name → Array Name
    | .vdecl _ (.prim op _) b, acc => go b (if (RVal.ExternSig.ofKey? op).isSome && !acc.contains op then acc.push op else acc)
    | .vdecl _ _ b, acc | .dup _ b, acc | .drop _ b, acc => go b acc
    | .case _ alts, acc => alts.foldl (fun acc a => go a acc) acc
    | .jdecl _ _ jb k, acc => go k (go jb acc)
    | _, acc => acc
  (decls.foldl (fun acc d => go d.body acc) #[]).qsort (· < ·)

def ctype : Char → String
  | 'n' | 'u' => "uint64_t"
  | 'f' => "double"
  | 's' => "const char *"
  | 'b' => "int"
  | 'p' => "void *"
  | 'w' => "wiz_val"
  | _ => "void"

/-- Is this a C identifier? (an exported function's name) -/
def isCIdent (s : String) : Bool :=
  match s.toList with
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_')
  | [] => false

/-! ### Calls from C into Wiz (stage 9g)

An exported function and a callback both turn C values into Wiz values (`wiz_out_*`),
apply a Wiz closure, and turn the result back (`wiz_in_*`): the reverse of a foreign
function's wrapper. A result in `IO` gets the world (a scalar) and drops it after. -/

/-- The C type of a value C passes to Wiz (`const char *` is borrowed: Wiz copies it). -/
def ctypeIn : Char → String
  | 's' => "const char *"
  | k => ctype k

/-- The C type of a value Wiz gives C: a string is `malloc`ed, the caller frees it. -/
def ctypeOut : Char → String
  | 's' => "char *"
  | k => ctype k

/-- A C value of kind `k` as a Wiz value (C → Wiz). A pointer is lent: no finalizer. -/
def wizOfC (k : Char) (x : String) : String := match k with
  | 'n' => s!"wiz_out_nat({x})" | 'u' => s!"wiz_out_u64({x})" | 'f' => s!"wiz_out_f64({x})"
  | 's' => s!"wiz_out_string({x})" | 'b' => s!"wiz_out_bool({x})"
  | 'p' => s!"wiz_out_ptr((void *)({x}), NULL)"
  | _ => x

/-- A Wiz value (owned) as a C value of kind `k` (Wiz → C). -/
def cOfWiz (k : Char) (x : String) : String := match k with
  | 'n' => s!"wiz_in_nat({x})" | 'u' => s!"wiz_in_u64({x})" | 'f' => s!"wiz_in_f64({x})"
  | 's' => s!"wiz_in_string({x})" | 'b' => s!"wiz_in_bool({x})"
  | _ => x

/-- The body of a C function that applies the closure `f` (an owned `wiz_val`
expression) to its parameters `a0 …` of the signature `c`. -/
def callIntoWiz (c : RVal.CallbackSig) (f : String) : String :=
  let n := c.params.length + (if c.io then 1 else 0)
  let args := (c.params.zipIdx.map fun (k, i) => wizOfC k s!"a{i}") ++ (if c.io then ["WIZ_BOX(0)"] else [])
  let call := if n == 0 then s!"  wiz_val r = {f};\n"
    else s!"  wiz_val f = {f};\n  wiz_val args[{n}] = {lb}{", ".intercalate args}{rb};\n  wiz_val r = wiz_apply(f, {n}, args);\n"
  let io := if c.io then "  r = wiz_io_value(r);\n" else ""
  let ret := if c.result == 'v' then "  wiz_dec(r);\n" else s!"  return {cOfWiz c.result "r"};\n"
  call ++ io ++ ret
where
  lb := "{"
  rb := "}"

def cParams (c : RVal.CallbackSig) : List String :=
  c.params.zipIdx.map fun (k, i) => s!"{ctypeIn k} a{i}"

/-- The trampoline of a callback signature: C calls it with the context first. -/
def trampoline (c : RVal.CallbackSig) : String :=
  "wiz_cb_" ++ String.mk c.params ++ "_" ++ (if c.io then "io_" else "") ++ c.result.toString

def trampolineDef (c : RVal.CallbackSig) : String :=
  let ps := ", ".intercalate ("void *ctx" :: cParams c)
  s!"static {ctypeOut c.result} {trampoline c}({ps}) {lb}\n  wiz_inc((wiz_val)ctx);\n{callIntoWiz c "(wiz_val)ctx"}{rb}\n"
where
  lb := "{"
  rb := "}"

/-- The C type of a callback's function pointer. -/
def callbackType (c : RVal.CallbackSig) : String :=
  s!"{ctypeOut c.result} (*)({", ".intercalate ("void *" :: c.params.map ctypeIn)})"

/-- An exported function's C prototype. -/
def exportProto (sig : RVal.ExternSig) : String :=
  let ps := (sig.params.zipIdx.map fun (k, i) => s!"{ctypeIn k} a{i}")
  s!"{ctypeOut sig.result} {sig.cname}({if ps.isEmpty then "void" else ", ".intercalate ps})"

/-- The IR function that gives an exported function's closure. -/
def exportEntry (cname : String) : Name := "wiz.export." ++ cname

/-- The C functions of the exports (after the generated code; with `llvm`, the closures
come from the LLVM module). -/
def exportWrappers (exports : List RVal.ExternSig) (llvm : Bool := false) : String :=
  String.join (exports.map fun sig =>
    let entry := mangle (exportEntry sig.cname)
    let decl := if llvm then s!"extern wiz_val {entry}(void);\n" else ""
    let c : RVal.CallbackSig := { params := sig.params, result := sig.result, io := sig.io }
    decl ++ s!"{exportProto sig} {lb}\n{callIntoWiz c s!"{entry}()"}{rb}\n")
where
  lb := "{"
  rb := "}"

/-- A header for a library's exports (`wiz build --lib`). -/
def exportHeader (exports : List RVal.ExternSig) : String :=
  "/* generated by wiz build --lib: the functions the Wiz program exports (stage 9g) */\n" ++
  "#include <stdint.h>\n#ifndef WIZ_VAL_DEFINED\n#define WIZ_VAL_DEFINED\ntypedef uintptr_t wiz_val;\n#endif\n" ++
  "void wiz_release(void *v);\nvoid wiz_retain(void *v);\nlong wiz_live_objects(void);\n" ++
  String.join (exports.map (exportProto · ++ ";\n"))

/-- C glue for the foreign functions: their headers (or prototypes), and a marshalling
wrapper for each (`WIZ_API`, so the LLVM backend can call them). -/
def glue (keys : Array Name) : String := Id.run do
  let mut includes : Array String := #[]
  let mut out := ""
  -- the trampolines of the callbacks
  let mut cbs : Array String := #[]
  for key in keys do
    let some sig := RVal.ExternSig.ofKey? key | continue
    for c in sig.callbacks do
      let t := trampolineDef c
      unless cbs.contains t do cbs := cbs.push t
  out := String.join cbs.toList
  for key in keys do
    let some sig := RVal.ExternSig.ofKey? key | continue
    if sig.header != "" then
      unless includes.contains sig.header do includes := includes.push sig.header
    else if !sig.cname.startsWith "wiz_" then
      let ps := Id.run do
        let mut ps : Array String := #[]
        let mut j := 0
        for k in sig.params do
          if k == 'k' || k == 'K' then
            ps := ps ++ #[callbackType (sig.callbacks[j]?.getD default), "void *"]
            j := j + 1
          else if k != 'v' && k != 'e' then ps := ps.push (ctype k)
        pure ps.toList
      out := out ++ s!"extern {ctype sig.result} {sig.cname}({if ps.isEmpty then "void" else ", ".intercalate ps});\n"
    let n := sig.params.length
    let params := (List.range n).map (s!"wiz_val a{·}") ++ (if sig.io then ["wiz_val w"] else [])
    let mut body := ""
    let mut cargs : Array String := #[]
    let mut cb := 0
    for k in sig.params, i in [0:n] do
      match k with
      -- a callback: the trampoline and the closure (9g)
      | 'k' | 'K' =>
        cargs := cargs ++ #[trampoline (sig.callbacks[cb]?.getD default), s!"(void *)a{i}"]
        cb := cb + 1
      | 'n' => body := body ++ s!"  uint64_t c{i} = wiz_in_nat(a{i});\n"; cargs := cargs.push s!"c{i}"
      | 'u' => body := body ++ s!"  uint64_t c{i} = wiz_in_u64(a{i});\n"; cargs := cargs.push s!"c{i}"
      | 'f' => body := body ++ s!"  double c{i} = wiz_in_f64(a{i});\n"; cargs := cargs.push s!"c{i}"
      | 's' => body := body ++ s!"  char *c{i} = wiz_in_string(a{i});\n"; cargs := cargs.push s!"c{i}"
      | 'b' => body := body ++ s!"  int c{i} = wiz_in_bool(a{i});\n"; cargs := cargs.push s!"c{i}"
      | 'p' => body := body ++ s!"  void *c{i} = wiz_in_ptr(a{i});\n"; cargs := cargs.push s!"c{i}"
      | 'w' => cargs := cargs.push s!"a{i}"
      | 'e' => pure ()
      | _ => body := body ++ s!"  wiz_dec(a{i});\n"
    let call := s!"{sig.cname}({", ".intercalate cargs.toList})"
    body := body ++ match sig.result with
      | 'n' => s!"  wiz_val r = wiz_out_nat({call});\n"
      | 'u' => s!"  wiz_val r = wiz_out_u64({call});\n"
      | 'f' => s!"  wiz_val r = wiz_out_f64({call});\n"
      | 's' => s!"  wiz_val r = wiz_out_string({call});\n"
      | 'b' => s!"  wiz_val r = wiz_out_bool({call});\n"
      | 'p' =>
        let fin := if sig.fin == "" then "NULL" else s!"(void (*)(void *)){sig.fin}"
        s!"  wiz_val r = wiz_out_ptr((void *){call}, {fin});\n"
      | 'w' => s!"  wiz_val r = {call};\n"
      | _ => s!"  {call};\n  wiz_val r = WIZ_BOX(0);\n"
    for k in sig.params, i in [0:n] do
      if k == 's' then body := body ++ s!"  free(c{i});\n"
      -- a foreign pointer is borrowed for the call: release it after
      if k == 'p' then body := body ++ s!"  wiz_dec(a{i});\n"
      -- a borrowed callback is released after the call; a `Callback` is C's now
      if k == 'k' then body := body ++ s!"  wiz_dec(a{i});\n"
    body := body ++ (if sig.io then "  return wiz_io_result(r, w);\n" else "  return r;\n")
    out := out ++ s!"WIZ_API wiz_val {externWrapper key}({", ".intercalate params}) {lb}\n{body}{rb}\n"
  pure (String.join (includes.toList.map (s!"#include <{·}>\n")) ++ out)
where
  lb := "{"
  rb := "}"

/-- **Exercise 8.2.** Emit the C statements of a body (see the module docstring). A
join point's body goes after the code that jumps to it, under the label `jN:`; a
jump assigns the parameters (through temporaries, since arguments may overlap them)
and `goto`s the label. -/
partial def body (arities : Std.HashMap Name Nat) (joins : Std.HashMap JoinId (Array Var)) (b : Body)
    (ind : String := "  ") : String :=
  --<sol
  match b with
  | .vdecl x e rest => s!"{ind}{expr arities x e}\n{body arities joins rest ind}"
  | .case x alts =>
    let cases := alts.toList.zipIdx.map fun (a, i) =>
      s!"{ind}case {i}: {lb}\n{body arities joins a (ind ++ "  ")}{ind}{rb}\n"
    s!"{ind}switch (wiz_tag({var x})) {lb}\n{String.join cases}{ind}default: wiz_unreachable(); return 0;\n{ind}{rb}\n"
  | .ret x => s!"{ind}return {var x};\n"
  | .jdecl j ps jb k =>
    let joins := joins.insert j ps
    s!"{body arities joins k ind}{ind}j{j}: {lb}\n{body arities joins jb (ind ++ "  ")}{ind}{rb}\n"
  | .jmp j as =>
    let ps := (joins.get? j).getD #[]
    let tmps := as.toList.zipIdx.map fun (a, i) => s!"wiz_val t{i} = {var a}; "
    let sets := ps.toList.zipIdx.map fun (p, i) => s!"{var p} = t{i}; "
    s!"{ind}{lb} {String.join tmps}{String.join sets}goto j{j}; {rb}\n"
  | .dup x rest => s!"{ind}wiz_inc({var x});\n{body arities joins rest ind}"
  | .drop x rest => s!"{ind}wiz_dec({var x});\n{body arities joins rest ind}"
  | .unreachable => s!"{ind}wiz_unreachable(); return 0;\n"
where
  lb := "{"
  rb := "}"
  --|ex
  --| sorry
  --sol>

def signature (d : IR.Decl) : String :=
  let ps := if d.params.isEmpty then "void" else ", ".intercalate (d.params.toList.map (s!"wiz_val {var ·}"))
  s!"static wiz_val {mangle d.name}({ps})"

def decl (arities : Std.HashMap Name Nat) (d : IR.Decl) : String :=
  -- (a reuse token may be bound in several branches: declare it once)
  let locals := ((bound d.body).filter (!d.params.contains ·)).toList.eraseDups.toArray
  let decls := if locals.isEmpty then "" else s!"  wiz_val {", ".intercalate (locals.toList.map var)};\n"
  let boxedArgs := ", ".intercalate ((List.range d.params.size).map (s!"a[{·}]"))
  -- (a hoisted constant is built once, made immortal, and shared; threads may race to
  -- build it: the first to publish wins, a loser's copy stays immortal and unused)
  if d.name.startsWith "wiz.const." && d.params.isEmpty then
    s!"static wiz_val {mangle d.name}_build(void) {lb}\n{decls}{body arities {} d.body}{rb}\n" ++
    s!"{signature d} {lb} static wiz_val c = 0; wiz_val v = __atomic_load_n(&c, __ATOMIC_ACQUIRE); " ++
    s!"if (!v) {lb} wiz_val z = 0; v = {mangle d.name}_build(); wiz_immortal(v); " ++
    s!"if (!__atomic_compare_exchange_n(&c, &z, v, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) v = z; {rb} " ++
    s!"wiz_inc(v); return v; {rb}\n" ++
    s!"static wiz_val {mangle d.name}_boxed(wiz_val *a) {lb} return {mangle d.name}(); {rb}\n"
  else
  s!"{signature d} {lb}\n{decls}{body arities {} d.body}{rb}\n" ++
  s!"static wiz_val {mangle d.name}_boxed(wiz_val *a) {lb} return {mangle d.name}({boxedArgs}); {rb}\n"
where
  lb := "{"
  rb := "}"

/-- A whole C program: the runtime, the foreign glue, the functions, and a `main` that
prints the result of the Wiz `main` (or, for `main : IO A`, runs it) and checks for
leaks. -/
def program (decls : Array IR.Decl) (io : Bool := false) (extra : String := "")
    (exports : List RVal.ExternSig := []) (lib : Bool := false) : String :=
  let arities := decls.foldl (fun m d => m.insert d.name d.params.size) {}
  let protos := decls.toList.map fun d =>
    s!"{signature d};\nstatic wiz_val {mangle d.name}_boxed(wiz_val *a);\n"
  let finish := if io then "1" else "0"
  runtime ++ "\n/* ---- foreign functions ---- */\n\n" ++ extra ++ "\n" ++ glue (externs decls) ++
    "\n/* ---- generated ---- */\n\n" ++ String.join protos ++ "\n" ++
    String.join (decls.toList.map (decl arities ·)) ++
    (if exports.isEmpty then "" else "\n/* ---- exported functions ---- */\n\n" ++ exportWrappers exports) ++
    -- (a library has no `main`: C calls its exports)
    if lib then "" else
    s!"\nint main(int argc, char **argv) \{ wiz_set_args(argc, argv); return wiz_run_main({mangle "wiz.entry"}, {finish}); }\n"

end Wiz.C
