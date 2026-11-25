/-
UNTRUSTED. The Lean side of the DAG's verifier (`python/dag_verify.py`, docs/GITHUB_PLATFORM.md).
CI decides the verdicts it reports with these commands, but nothing depends on them: a client
checks every proof itself with the trusted `#sigaba_neo_check`.

* `#sigaba_neo_platform_module "M" "definition"|"theorem" "<theorem name>" "out.json"`: may the built
  module `M` be published as a definition (no `sorry`, nothing forbidden) or as the statement of
  the named theorem (it declares that theorem and nothing else)?
* `#sigaba_neo_platform_submission "<theorem>" "prove"|"disprove" "Solutions.M" "out.json"`: the
  status of a submission (`OK`, `WA`, `SORRY`, `FAILED`, `CE`) and the platform theorems it uses.
* `#sigaba_neo_platform_lint "out.json" "A.lean" "B.lean" …`: the syntactic filter
  (`SigabaNeo.Platform.Lint`), run on files before they are built: their imports and problems.
* `#sigaba_neo_platform_semantic "M" "definition"|"theorem" "<theorem name>" "out.json"`: the
  semantic data of a built node (`SigabaNeo.Platform.Semantic`), which `python/dag.py` hashes into
  its semantic ID.
* `#sigaba_neo_platform_assumption "M" "<name>" "out.json"`: may the constant `<name>` of the built
  module `M` be registered as an assumption (a definition of type `SigabaNeo.Assumption`, without
  `sorry` or other axioms), and the semantic data of its parameter set and problem (not of its
  security function, so re-registering a problem with another `H` is a duplicate).
* `#sigaba_neo_platform_lowering "<theorem>" "out.json"`: whether the statement of a theorem node
  is `SigabaNeo.Assumption.Lowering a H H'` with `a` and `H'` constants and `H` either `a.H` or a
  constant, and which ones (a strength version, docs/ASSUMPTIONS.md).
-/
import SigabaNeo.Trusted.Check
import SigabaNeo.Platform.Lint
import SigabaNeo.Platform.SemanticId

open Lean Elab Command

namespace SigabaNeo.Platform

open SigabaNeo.Check (moduleOf? runCore standardAxioms)

def slug (n : Name) : String := (n.toString (escape := false)).replace "." "_"

def thmModuleOf (thm : Name) : Name := .str `Theorems s!"Thm_{slug thm}"

def result (status msg : String) (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("status", Json.str status), ("message", Json.str msg)] ++ extra)

def constantsOf (env : Environment) (mod : Name) : Array ConstantInfo :=
  env.constants.map₁.toList.toArray.filterMap fun (n, ci) =>
    if moduleOf? env n == some mod then some ci else none

/-- Declarations a platform module may not contain. -/
def forbidden (env : Environment) (mod : Name) : Array String :=
  (constantsOf env mod).filterMap fun ci =>
    let why := match ci with
      | .axiomInfo _ => some "an axiom"
      | .opaqueInfo _ => some "opaque"
      | _ => if ci.isUnsafe then some "unsafe"
        else if ci.isPartial then some "partial"
        else if ci.name.isInternal then none
        else if (Compiler.getImplementedBy? env ci.name).isSome then some "implemented_by"
        else if isExtern env ci.name then some "extern" else none
    why.map fun w => s!"{ci.name} is {w}"

/-- The axioms a proof reaches and the platform theorems it uses (theorems of a `Theorems.*`
module; the walk does not descend into them). -/
def proofDeps (env : Environment) (root : Name) : Array Name × Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  let mut axs := #[]
  let mut uses := #[]
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if n != root && (moduleOf? env n).any (·.getRoot == `Theorems) && ci matches .thmInfo _ then
      uses := uses.push n
      continue
    if ci matches .axiomInfo _ then axs := axs.push n
    for u in ci.getUsedConstantsAsSet.toList do
      unless seen.contains u do stack := stack.push u
  return (axs, uses)

def moduleCheck (mod : Name) (kind : String) (thm : Name) : IO Json := do
  let env ← try importModules #[{ module := mod }] {} catch e =>
    return result "FAILED" s!"cannot load {mod}: {e}"
  let bad := forbidden env mod
  unless bad.isEmpty do return result "FAILED" ("\n".intercalate bad.toList)
  if kind == "definition" then
    for ci in constantsOf env mod do
      if (← runCore env (collectAxioms ci.name)).contains ``sorryAx then
        return result "FAILED" s!"{ci.name} uses `sorry`: a definition file must be sorry-free"
    return result "OK" ""
  match env.find? thm with
  | some (.thmInfo _) =>
    unless moduleOf? env thm == some mod do
      return result "FAILED" s!"{thm} is not declared by the formal statement"
    let others := (constantsOf env mod).filter fun ci =>
      ci.name != thm && !ci.name.isInternal && !thm.isPrefixOf ci.name
    unless others.isEmpty do
      return result "FAILED" s!"the statement declares more than {thm}: \
        {others.toList.map (·.name)}; publish definitions with submit-definition"
    return result "OK" ""
  | _ => return result "FAILED" s!"the formal statement does not declare `theorem {thm}`"

/-- Kernel replay of the constants of module `sol` onto the environment of the others. -/
def replay (env : Environment) (sol : Name) : IO Unit := do
  let others := env.header.moduleNames.filter (· != sol)
  let base ← importModules (others.map ({ module := · })) {}
  let mut new : Std.HashMap Name ConstantInfo := {}
  for ci in constantsOf env sol do new := new.insert ci.name ci
  discard <| base.toKernelEnv.replay new

def submissionCheck (thm : Name) (negate : Bool) (sol : Name) : IO Json := do
  let thmMod := thmModuleOf thm
  let env ← try importModules #[{ module := thmMod }, { module := sol }] {} catch e =>
    return result "CE" s!"cannot load the submission: {e}"
  let some tci := env.find? thm | return result "ERROR" s!"{thmMod} does not declare {thm}"
  let some (.thmInfo v) := env.find? `solution
    | return result "WA" "the submission does not declare `theorem solution`"
  unless moduleOf? env `solution == some sol do
    return result "WA" "`solution` is not declared by the submission"
  let want := if negate then mkApp (mkConst ``Not) tci.type else tci.type
  unless v.levelParams == tci.levelParams && v.type == want do
    return result "WA" s!"the type of `solution` is not {if negate then "the negation of " else ""}\
      the formal statement of {thm}"
  let bad := forbidden env sol
  unless bad.isEmpty do return result "FAILED" ("\n".intercalate bad.toList)
  let (axs, uses) := proofDeps env `solution
  if axs.contains ``sorryAx then return result "SORRY" "the proof uses `sorry`"
  let odd := axs.filter (!standardAxioms.contains ·)
  unless odd.isEmpty do return result "FAILED" s!"the proof depends on the axioms {odd.toList}"
  if uses.contains thm then return result "FAILED" "the proof imports its own target"
  if negate && !uses.isEmpty then
    return result "FAILED" "a disproof may not import platform theorems"
  try replay env sol catch e => return result "FAILED" s!"kernel replay failed: {e}"
  return result "OK" "" [("uses", Json.arr (uses.map (Json.str ·.toString)))]

def write (out : String) (j : Json) : CommandElabM Unit := do
  liftCoreM (liftM (IO.FS.writeFile out (j.compress ++ "\n") : IO Unit))
  logInfo s!"{(j.getObjValAs? String "status").toOption.getD "?"}"

syntax (name := platformModule) "#sigaba_neo_platform_module " str str str str : command
syntax (name := platformSubmission) "#sigaba_neo_platform_submission " str str str str : command
syntax (name := platformLint) "#sigaba_neo_platform_lint " str str* : command
syntax (name := platformSemantic) "#sigaba_neo_platform_semantic " str str str str : command

elab_rules : command
  | `(#sigaba_neo_platform_module $m:str $k:str $t:str $o:str) => do
    write o.getString (← liftCoreM (liftM (moduleCheck m.getString.toName k.getString
      t.getString.toName : IO Json)))
  | `(#sigaba_neo_platform_submission $t:str $k:str $s:str $o:str) => do
    write o.getString (← liftCoreM (liftM (submissionCheck t.getString.toName
      (k.getString == "disprove") s.getString.toName : IO Json)))

/-- The semantic data of the theorem `thm` (kind `theorem`) or of the definitions module `mod`
declares (kind `definition`). -/
def semantic (mod : Name) (kind : String) (thm : Name) : IO Json := do
  let env ← try importModules #[{ module := mod }] {} catch e =>
    return result "FAILED" s!"cannot load {mod}: {e}"
  let decls := if kind == "theorem" then [thm] else
    ((constantsOf env mod).filter (!·.name.isInternal)).map (·.name) |>.toList
      |>.mergeSort (·.toString < ·.toString)
  try
    let j ← runCore env (Meta.MetaM.run' (Semantic.nodeData kind decls))
    return j.setObjVal! "status" (Json.str "OK")
  catch e => return result "FAILED" s!"semantic ID: {e}"

elab_rules : command
  | `(#sigaba_neo_platform_lint $o:str $fs:str*) => do
    let mut files := #[]
    for f in fs do
      let (imports, problems) ← liftCoreM (liftM (Lint.lintFile f.getString : IO _))
      files := files.push (Json.mkObj [("file", Json.str f.getString),
        ("imports", Json.arr (imports.map Json.str)),
        ("problems", Json.arr (problems.map Json.str))])
    write o.getString (Json.mkObj [("status", Json.str "OK"), ("files", Json.arr files)])
  | `(#sigaba_neo_platform_semantic $m:str $k:str $t:str $o:str) => do
    write o.getString (← liftCoreM (liftM (semantic m.getString.toName k.getString
      t.getString.toName : IO Json)))

/-! ### Assumptions and strength versions -/

def assumptionCheck (mod decl : Name) : IO Json := do
  let env ← try importModules #[{ module := mod }] {} catch e =>
    return result "FAILED" s!"cannot load {mod}: {e}"
  let some ci := env.find? decl | return result "FAILED" s!"{mod} does not declare {decl}"
  unless moduleOf? env decl == some mod do
    return result "FAILED" s!"{decl} is not declared by {mod}"
  let .defnInfo v := ci | return result "FAILED" s!"{decl} is not a definition"
  unless v.levelParams.isEmpty && v.type == mkConst `SigabaNeo.Assumption do
    return result "FAILED" s!"the type of {decl} is not `SigabaNeo.Assumption`"
  let axs ← runCore env (collectAxioms decl)
  let odd := axs.filter (!standardAxioms.contains ·)
  unless odd.isEmpty do return result "FAILED" s!"{decl} depends on the axioms {odd.toList}"
  try
    let j ← runCore env <| Meta.MetaM.run' do
      -- The fields of the structure the definition unfolds to; the security function is left out.
      let w ← Meta.whnf (mkConst decl)
      let (params, problem) :=
        if w.isAppOfArity `SigabaNeo.Assumption.mk 3 then (w.getArg! 0, w.getArg! 1)
        else (mkApp (mkConst `SigabaNeo.Assumption.Params) (mkConst decl),
          mkApp (mkConst `SigabaNeo.Assumption.problem) (mkConst decl))
      Semantic.exprNodeData "assumption" [("params", params), ("problem", problem)]
    return j.setObjVal! "status" (Json.str "OK")
  catch e => return result "FAILED" s!"semantic ID: {e}"

/-- `a.H` (the assumption's own security function), as a projection or its function. -/
def ownH? (e : Expr) : Option Name :=
  match e.consumeMData with
  | .proj `SigabaNeo.Assumption 2 (.const a []) => some a
  | e => if e.isAppOfArity `SigabaNeo.Assumption.H 1 then e.getArg! 0 |>.consumeMData.constName?
    else none

def loweringCheck (thm : Name) : IO Json := do
  let mod := thmModuleOf thm
  let env ← try importModules #[{ module := mod }] {} catch e =>
    return result "FAILED" s!"cannot load {mod}: {e}"
  let some (.thmInfo v) := env.find? thm | return result "FAILED" s!"{mod} does not declare {thm}"
  let t := v.type.consumeMData
  unless v.levelParams.isEmpty && t.isAppOfArity `SigabaNeo.Assumption.Lowering 3 do
    return result "FAILED" s!"the statement of {thm} is not `SigabaNeo.Assumption.Lowering a H H'`"
  let some a := (t.getArg! 0).consumeMData.constName?
    | return result "FAILED" "the assumption of the lowering is not a constant"
  let src := t.getArg! 1
  let fromJ ← match ownH? src, src.consumeMData.constName? with
    | some a', _ =>
      if a' == a then pure Json.null
      else return result "FAILED" s!"the lowered function is the security function of {a'}, not {a}"
    | none, some h => pure (Json.str h.toString)
    | none, none => return result "FAILED" "the lowered function is neither `a.H` nor a constant"
  let some h' := (t.getArg! 2).consumeMData.constName?
    | return result "FAILED" "the new security function is not a constant"
  return result "OK" "" [("assumption", Json.str a.toString), ("from", fromJ),
    ("to", Json.str h'.toString)]

syntax (name := platformAssumption) "#sigaba_neo_platform_assumption " str str str : command
syntax (name := platformLowering) "#sigaba_neo_platform_lowering " str str : command

elab_rules : command
  | `(#sigaba_neo_platform_assumption $m:str $d:str $o:str) => do
    write o.getString (← liftCoreM (liftM (assumptionCheck m.getString.toName
      d.getString.toName : IO Json)))
  | `(#sigaba_neo_platform_lowering $t:str $o:str) => do
    write o.getString (← liftCoreM (liftM (loweringCheck t.getString.toName : IO Json)))

end SigabaNeo.Platform
