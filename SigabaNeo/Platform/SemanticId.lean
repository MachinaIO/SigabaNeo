/-
UNTRUSTED. Semantic IDs of DAG nodes (docs/GITHUB_PLATFORM.md, "Identity: semantic IDs").

A theorem node is identified by what its statement means, not by its text or by the environment as
a whole. `closure` collects every constant the statement refers to, recursively. Each one becomes
a *unit*, written in a canonical form:

* expressions are hash-consed into numbered nodes, so the form is independent of sharing;
* bound variables are de Bruijn indices, binder names and binder info are dropped, metadata is
  dropped;
* universe parameters are numbered;
* every subterm that is a proof is replaced by `X` (proof irrelevance), so a changed proof inside a
  definition or a statement changes nothing;
* a theorem contributes its type only, a definition its type and value, and opaque constants and
  axioms their type;
* an inductive family (the inductive types of one `mutual` block, their constructors and
  recursors) is one unit, `block:<first type>`, so its self-references are not cycles.

The Python side (`python/dag.py`, `semantic_id`) hashes the units bottom-up (a Merkle hash: a unit's
hash covers its form and the hashes of the units it refers to), and the root (the statement's type
without the theorem's name, or the definitions a definition file declares) gives the ID.
-/
import Lean

open Lean Meta

namespace SigabaNeo.Platform.Semantic

/-- The unit of a constant. -/
def unitOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.inductInfo v) => s!"block:{v.all.headD n}"
  | some (.ctorInfo v) =>
    match env.find? v.induct with
    | some (.inductInfo w) => s!"block:{w.all.headD v.induct}"
    | _ => s!"block:{v.induct}"
  | some (.recInfo v) => s!"block:{v.all.headD n}"
  | _ => n.toString

/-- The stand-in for a proof. It is not a constant of the environment. -/
def proofMark : Name := `_sigaba_neo_proof

/-- Replace every proof inside `e` by `proofMark`. -/
def stripProofs (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    -- Sorts and Π-types are never proofs; a λ can be (a proof of a `∀`), so it is tested too.
    if e.isSort || e.isForall || e.isMData then return .continue
    try
      if ← Meta.isProof e then return .done (mkConst proofMark) else return .continue
    catch _ => return .continue)

structure SerState where
  ids : Std.HashMap Expr Nat := {}
  lines : Array String := #[]
  consts : NameSet := {}

abbrev SerM := StateT SerState (Except String)

def serLevel (lps : List Name) : Level → Except String String
  | .zero => pure "0"
  | .succ l => return s!"s({← serLevel lps l})"
  | .max a b => return s!"m({← serLevel lps a},{← serLevel lps b})"
  | .imax a b => return s!"i({← serLevel lps a},{← serLevel lps b})"
  | .param n => match lps.idxOf? n with
    | some i => pure s!"u{i}"
    | none => throw s!"unknown universe parameter {n}"
  | .mvar _ => throw "a universe metavariable"

def emit (e : Expr) (line : String) : SerM Nat := do
  let s ← get
  let i := s.lines.size
  set { s with lines := s.lines.push line, ids := s.ids.insert e i }
  return i

/-- The node number of `e`, emitting the nodes it needs. -/
partial def ser (lps : List Name) (e : Expr) : SerM Nat := do
  if let some i := (← get).ids[e]? then return i
  match e with
  | .mdata _ b =>
    let i ← ser lps b
    modify fun s => { s with ids := s.ids.insert e i }
    return i
  | .bvar i => emit e s!"V {i}"
  | .sort u => emit e s!"S {← liftM (serLevel lps u)}"
  | .const n us =>
    if n == proofMark then return ← emit e "X"
    let ls ← us.mapM fun u => liftM (serLevel lps u)
    modify fun s => { s with consts := s.consts.insert n }
    emit e s!"C {n} {",".intercalate ls}"
  | .app f a =>
    let i ← ser lps f
    let j ← ser lps a
    emit e s!"A {i} {j}"
  | .lam _ t b _ =>
    let i ← ser lps t
    let j ← ser lps b
    emit e s!"L {i} {j}"
  | .forallE _ t b _ =>
    let i ← ser lps t
    let j ← ser lps b
    emit e s!"P {i} {j}"
  | .letE _ t v b _ =>
    let i ← ser lps t
    let j ← ser lps v
    let k ← ser lps b
    emit e s!"E {i} {j} {k}"
  | .lit (.natVal n) => emit e s!"N {n}"
  | .lit (.strVal s) => emit e s!"T {s.quote}"
  | .proj s i b =>
    modify fun st => { st with consts := st.consts.insert s }
    let j ← ser lps b
    emit e s!"J {s} {i} {j}"
  | .fvar _ => throw "a free variable"
  | .mvar _ => throw "a metavariable"

/-- Serialize several labelled expressions into one form: the node lines, then one line per label
naming its root node. -/
def serAll (lps : List Name) (header : String) (es : List (String × Expr)) :
    MetaM (String × NameSet) := do
  let mut st : SerState := {}
  let mut roots := #[]
  for (label, e) in es do
    let e ← stripProofs e
    match (ser lps e).run st with
    | .ok (i, st') => st := st'; roots := roots.push s!"{label} {i}"
    | .error msg => throwError "cannot serialize {label}: {msg}"
  let body := "\n".intercalate (header :: st.lines.toList ++ roots.toList)
  return (body, st.consts)

/-- The form of a unit, and the constants it mentions. -/
def unitForm (env : Environment) (key : String) (n : Name) : MetaM (String × NameSet) := do
  let some ci := env.find? n | throwError "unknown constant {n}"
  let lps := ci.levelParams
  let k := lps.length
  match ci with
  | .defnInfo v => serAll lps s!"def {n} {k}" [("type", v.type), ("value", v.value)]
  | .thmInfo v => serAll lps s!"thm {n} {k}" [("type", v.type)]
  | .opaqueInfo v => serAll lps s!"opaque {n} {k}" [("type", v.type)]
  | .axiomInfo v => serAll lps s!"axiom {n} {k}" [("type", v.type)]
  | .quotInfo v =>
    let qk := match v.kind with | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
    serAll lps s!"quot {n} {k} {qk}" [("type", v.type)]
  | _ =>
    -- An inductive family: every type of the block with its constructors.
    let all := match ci with
      | .inductInfo v => v.all
      | .ctorInfo v => match env.find? v.induct with
        | some (.inductInfo w) => w.all
        | _ => [v.induct]
      | .recInfo v => v.all
      | _ => [n]
    let mut es : List (String × Expr) := []
    let mut header := s!"block {key} {k}"
    for t in all do
      let some (.inductInfo v) := env.find? t | throwError "{t} is not an inductive type"
      header := header ++ s!"\nind {t} {v.numParams} {v.numIndices} {v.ctors.length}"
      es := es ++ [(s!"ind {t}", v.type)]
      for c in v.ctors do
        let some (.ctorInfo cv) := env.find? c | throwError "{c} is not a constructor"
        es := es ++ [(s!"ctor {c}", cv.type)]
    serAll lps header es

/-- The units reachable from `roots`: unit key ↦ (form, referenced unit keys). -/
partial def closure (roots : NameSet) : MetaM (Std.HashMap String (String × Array String)) := do
  let env ← getEnv
  let mut out : Std.HashMap String (String × Array String) := {}
  let mut todo := roots.toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if n == proofMark then continue
    let key := unitOf env n
    if out.contains key then continue
    let (form, consts) ← unitForm env key n
    let refs := consts.toList.filter (· != proofMark) |>.map (unitOf env)
      |>.filter (· != key) |>.eraseDups |>.toArray.qsort (· < ·)
    out := out.insert key (form, refs)
    todo := consts.toList ++ todo
  return out

/-- The semantic data of a theorem (its type, without its name) or of a definition file (the
definitions it declares, by name). -/
def nodeData (kind : String) (decls : List Name) : MetaM Json := do
  let env ← getEnv
  let (rootForm, rootConsts) ← match kind with
    | "theorem" =>
      let some ci := env.find? decls.head! | throwError "unknown theorem {decls.head!}"
      serAll ci.levelParams s!"theorem-node {ci.levelParams.length}" [("statement", ci.type)]
    | _ =>
      pure ("definition-node\n" ++ "\n".intercalate (decls.map (s!"decl {·}")),
        decls.foldl (·.insert ·) {})
  let units ← closure rootConsts
  let rootRefs := rootConsts.toList.filter (· != proofMark) |>.map (unitOf env) |>.eraseDups
    |>.toArray.qsort (· < ·)
  let unitJson := units.toList.map fun (k, (f, r)) =>
    (k, Json.mkObj [("form", Json.str f), ("refs", Json.arr (r.map Json.str))])
  return Json.mkObj [
    ("kind", Json.str kind),
    ("root", Json.mkObj [("form", Json.str rootForm), ("refs", Json.arr (rootRefs.map Json.str))]),
    ("units", Json.mkObj unitJson)]

end SigabaNeo.Platform.Semantic
