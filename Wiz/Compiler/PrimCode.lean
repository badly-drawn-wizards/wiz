import Wiz.Compiler.Erase

/-!
# The generic eliminators, as code

The interpreter implements `ind`, `Desc.elim` and `out` natively (`Run.lean`). The
backend instead compiles these definitions, written in the erased language, like any
other code. They walk the description at runtime, exactly as the interpreter does
(see its module docstring). A description is `⟨0 i⟩` (ret), `⟨1 ◾ F⟩` (arg),
`⟨2 j D⟩` (rec) or `⟨3 ◾ j D⟩` (hrec). Lazy codata is `⟨1000 D step i s⟩` (`coit`)
or `⟨1001 f i a⟩` (`scofix`).
-/

namespace Wiz.PrimCode

open ETerm

private def v (i : Nat) : ETerm := .var i
private def g (n : Name) : ETerm := .global n
private def p (i : Nat) (t : ETerm) : ETerm := .proj i t
private def lams (xs : List Name) (b : ETerm) : ETerm := xs.foldr .lam b

/-- `ind D m i x = m i x (hyps D m D x)` -/
def ind : ETerm :=
  -- x0 i1 m2 D3
  lams ["D", "m", "i", "x"] (apps (v 2) [v 1, v 0, apps (g "wiz.hyps") [v 3, v 2, v 3, v 0]])

/-- The induction hypotheses: `ind` at every recursive field. -/
def hyps : ETerm :=
  -- xs0 d1 m2 D3
  lams ["D", "m", "d", "xs"] (.case (v 1) #[
    .erased,
    apps (g "wiz.hyps") [v 3, v 2, .app (p 1 (v 1)) (p 0 (v 0)), p 1 (v 0)],
    .obj 0 #[apps (g "wiz.ind") [v 3, v 2, p 0 (v 1), p 0 (v 0)],
             apps (g "wiz.hyps") [v 3, v 2, p 1 (v 1), p 1 (v 0)]],
    -- h0 xs1 d2 m3 D4
    .obj 0 #[.lam "h" (apps (g "wiz.ind") [v 4, v 3, .app (p 1 (v 2)) (v 0), .app (p 0 (v 1)) (v 0)]),
             apps (g "wiz.hyps") [v 3, v 2, p 2 (v 1), p 1 (v 0)]]])

/-- `Desc.elim mret marg mrec mhrec D` -/
def delim : ETerm :=
  -- D0 mhrec1 mrec2 marg3 mret4
  lams ["mret", "marg", "mrec", "mhrec", "D"] (.case (v 0) #[
    .app (v 4) (p 0 (v 0)),
    -- s0 D1 mhrec2 mrec3 marg4 mret5
    apps (v 3) [.erased, .erased, p 1 (v 0),
      .lam "s" (apps (g "wiz.delim") [v 5, v 4, v 3, v 2, .app (p 1 (v 1)) (v 0)])],
    apps (v 2) [.erased, p 0 (v 0), p 1 (v 0), apps (g "wiz.delim") [v 4, v 3, v 2, v 1, p 1 (v 0)]],
    apps (v 1) [.erased, .erased, p 1 (v 0), p 2 (v 0), apps (g "wiz.delim") [v 4, v 3, v 2, v 1, p 2 (v 0)]]])

/-- `map D f xs`: apply `f` to the recursive positions of a payload. -/
def map : ETerm :=
  -- xs0 f1 d2
  lams ["d", "f", "xs"] (.case (v 2) #[
    v 0,
    .obj 0 #[p 0 (v 0), apps (g "wiz.map") [.app (p 1 (v 2)) (p 0 (v 0)), v 1, p 1 (v 0)]],
    .obj 0 #[apps (v 1) [p 0 (v 2), p 0 (v 0)], apps (g "wiz.map") [p 1 (v 2), v 1, p 1 (v 0)]],
    -- h0 xs1 f2 d3
    .obj 0 #[.lam "h" (apps (v 2) [.app (p 1 (v 3)) (v 0), .app (p 0 (v 1)) (v 0)]),
             apps (g "wiz.map") [p 2 (v 2), v 1, p 1 (v 0)]]])

/-- `out x`: run one step of a lazy coinductive value. -/
def out : ETerm :=
  lams ["x"] (.case (.prim .lazyTag #[v 0]) #[
    v 0,
    -- coit D step i s: map D (fun j s => coit D step j s) (step i s);  inside: s0 j1 x2
    apps (g "wiz.map") [p 0 (v 0),
      lams ["j", "s"] (.prim .coit #[p 0 (v 2), p 1 (v 2), v 1, v 0]),
      apps (p 1 (v 0)) [p 2 (v 0), p 3 (v 0)]],
    -- scofix f i a: out (f ◾ (fun j i a => scofix f i a) i a);  inside: a0 i1 j2 x3
    .app (g "wiz.out") (apps (p 0 (v 0)) [.erased,
      lams ["j", "i", "a"] (.prim .scofix #[p 0 (v 3), v 1, v 0]), p 1 (v 0), p 2 (v 0)])])

def all : List (Name × ETerm) :=
  [("wiz.ind", ind), ("wiz.hyps", hyps), ("wiz.delim", delim), ("wiz.map", map), ("wiz.out", out)]

end Wiz.PrimCode
