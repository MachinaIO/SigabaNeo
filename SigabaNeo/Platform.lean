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

/-- Compiler code Lean generates beside an ordinary declaration, in the same module:
* `f._unsafe_rec`, a `partial` copy of a safe recursive definition `f`;
* `T.ctorIdx`, implemented by the `unsafe` `T.ctorIdx._impl`, for an inductive type `T` in a
  universe that is never `Prop` (Lean makes neither for an inductive proposition).
The kernel forbids a safe declaration to use a `partial` or `unsafe` one, so no theorem or
definition can use `f._unsafe_rec` or `T.ctorIdx._impl`; `T.ctorIdx` itself is checked by the
kernel like any definition. A declaration with such a name that is not of this form (another
safety, another implementation, or `T` a proposition or in another module) is not skipped. -/
def compilerAux (env : Environment) (mod : Name) : Name → Bool
  | n@(.str f "_unsafe_rec") => match env.find? n, env.find? f with
    | some (.defnInfo d), some (.defnInfo g) =>
      d.safety == .partial && g.safety == .safe && moduleOf? env f == some mod
    | _, _ => false
  | n@(.str (.str t "ctorIdx") "_impl") => match env.find? n with
    | some (.defnInfo d) => d.safety == .unsafe && dataType t
    | _ => false
  | n@(.str t "ctorIdx") => match env.find? n with
    | some (.defnInfo d) => d.safety == .safe && dataType t &&
      Compiler.getImplementedBy? env n == some (n ++ `_impl)
    | _ => false
  | _ => false
where
  /-- An inductive type of this module whose universe is never `Prop`. -/
  dataType (t : Name) : Bool := match env.find? t with
    | some (.inductInfo i) => moduleOf? env t == some mod && resultSort i.type
    | _ => false
  resultSort : Expr → Bool
    | .forallE _ _ b _ => resultSort b
    | .sort l => l.isNeverZero
    | _ => false

/-- Declarations a platform module may not contain. -/
def forbidden (env : Environment) (mod : Name) : Array String :=
  (constantsOf env mod).filterMap fun ci =>
    let why := match ci with
      | .axiomInfo _ => some "an axiom"
      | .opaqueInfo _ => some "opaque"
      | _ => if compilerAux env mod ci.name then none
        else if ci.isUnsafe then some "unsafe"
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

end SigabaNeo.Platform
