/-
TRUSTED. The whole trusted code of Sigaba-Neo (docs/DESIGN.md).

The submitter's claim is a directory it wrote:

    claim.json             {"target": "T", "hypotheses": ["H₀", "¬ H₁", …]}
    Definitions/Def_*.lean the definitions of T and the Hᵢ (Prove2Me's format)

A hypothesis is a name `H` or a negated name `¬ H` (an assumption, or another claim's refutation).

A proof is a theorem of a Lake workspace (the current directory) that requires this core and
holds copies of the claim's definition files next to modules from anywhere (the server, agents).

    #sigaba_neo_check "<claim directory>"                      -- the theorem `Claim.proof` of `Claim`
    #sigaba_neo_check "<claim directory>" "<module>" "<theorem>"

It checks:

1. the workspace's `Definitions/Def_X.lean` is byte for byte the claim's, for every definition file
   of the claim; these modules are built in the workspace and import nothing else built there;
2. the target and the hypotheses are declared by them;
3. the theorem's type is one of the four claims, built from the names (never elaborated from
   text): `∀ (h₀ : H₀) …, T`, `∀ (h₀ : H₀) …, ¬ T`, or the negation of either;
4. the theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`, and,
   unless it is a negated claim, on axioms whose type is exactly one of the hypotheses (an
   assembled proof states its leaves this way; from `⊢ H → C` under an axiom `a : H` for a
   hypothesis `H`, the deduction theorem gives `H → C` again);
5. every declaration of every other module built in the workspace, and of every module of the
   standard library (`SigabaNeoStd`) that the claim's definitions do not import, passes the kernel
   again (replayed onto the rest), so nothing their code did while it was built can bypass the
   kernel. The std modules the definitions import are part of the claim's meaning, read like the
   core's definitions.

It prints what was established and whether that proves or refutes the target, and writes the same
to `result.json`. A false hypothesis implies anything: read `referenced hypotheses`, and believe a
conclusion under hypotheses only as much as the hypotheses.
-/
import Lean

open Lean Elab Command

namespace SigabaNeo.Check

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- A hypothesis: `H` or `¬ H`, built from the name. -/
def hypType (h : String) : Expr :=
  if h.startsWith "¬ " then mkApp (mkConst ``Not) (mkConst (h.drop 2).toString.toName)
  else mkConst h.toName

def hypName (h : String) : Name := (if h.startsWith "¬ " then (h.drop 2).toString else h).toName

def binderName (i : Nat) : Name :=
  .mkSimple ("h" ++ (toString i).map fun c => Char.ofNat (0x2080 + (c.toNat - '0'.toNat)))

/-- A claim, built from names: `∀ (h₀ : H₀) …, C`, `C` = `T` or `¬ T`, negated as a whole or
not. -/
def claimType (target : Name) (hyps : Array String) (refute negated : Bool) : Expr := Id.run do
  let mut e := if refute then mkApp (mkConst ``Not) (mkConst target) else mkConst target
  for i in (List.range hyps.size).reverse do
    e := .forallE (binderName i) (hypType hyps[i]!) e .default
  return if negated then mkApp (mkConst ``Not) e else e

def claimText (target : Name) (hyps : Array String) (refute negated : Bool) : String :=
  let c := " → ".intercalate ((hyps.map fun h => if h.startsWith "¬ " then s!"({h})" else h).toList ++
    [if refute then s!"¬ {target}" else toString target])
  if negated then s!"¬ ({c})" else c

def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?

def runCore (env : Environment) (x : CoreM α) : IO α := do
  let ctx : Core.Context := { fileName := "<sigaba-neo>", fileMap := default, maxHeartbeats := 0 }
  return (← x.toIO ctx { env }).1

/-- The hypotheses whose variable occurs in the proof applied to fresh variables. -/
def referencedHypotheses (env : Environment) (v : TheoremVal) (k : Nat) : IO (Array String) :=
  runCore env <| Meta.MetaM.run' <| Meta.forallBoundedTelescope v.type k fun xs _ => do
    let body := (mkAppN v.value xs).headBeta
    return (List.range xs.size).toArray.filterMap fun i =>
      if body.containsFVar xs[i]!.fvarId! then some (binderName i).toString else none

def check (claimDir : System.FilePath) (module thm : Name) : IO Json := do
  let mut problems : Array String := #[]
  let reject (ps : Array String) : Json :=
    Json.mkObj [("verdict", "rejected"), ("problems", Json.arr (ps.map Json.str))]
  -- The claim.
  let claim ← IO.ofExcept (Json.parse (← IO.FS.readFile (claimDir / "claim.json")))
  let target := (← IO.ofExcept (claim.getObjValAs? String "target")).toName
  let hyps ← IO.ofExcept (claim.getObjValAs? (Array String) "hypotheses")
  let mut defs : Array Name := #[]
  for e in ← (claimDir / "Definitions").readDir do
    if e.fileName.startsWith "Def_" && e.fileName.endsWith ".lean" then
      let m : Name := .str `Definitions (e.fileName.take (e.fileName.length - 5)).toString
      defs := defs.push m
      let copy : System.FilePath := "Definitions" / e.fileName
      unless (← copy.pathExists) && (← IO.FS.readBinFile copy) == (← IO.FS.readBinFile e.path) do
        problems := problems.push s!"{copy} is not the claim's {e.path}"
  if defs.isEmpty then return reject #[s!"{claimDir}/Definitions has no Def_*.lean"]
  let env ← try importModules #[{ module }] {} catch e => return reject (problems.push s!"cannot load: {e}")
  -- 1, 2. The claim's modules and constants.
  let localDir := ((← IO.currentDir) / ".lake" / "build").toString ++ "/"
  let mut isLocal : NameSet := {}
  for m in env.header.moduleNames do
    if (← findOLean m).toString.startsWith localDir then isLocal := isLocal.insert m
  -- The std modules the definitions import (transitively) are part of the claim's meaning; the
  -- other std modules are proof helpers, untrusted like the workspace's own.
  let mut defClosure : NameSet := {}
  let mut todo := defs.toList
  while !todo.isEmpty do
    let m := todo.head!
    todo := todo.tail!
    if defClosure.contains m then continue
    defClosure := defClosure.insert m
    if let some i := env.getModuleIdx? m then
      if let some d := env.header.moduleData[i.toNat]? then
        todo := d.imports.toList.map (·.module) ++ todo
  let others := env.header.moduleNames.filter fun m =>
    (isLocal.contains m && !defs.contains m) || (m.getRoot == `SigabaNeoStd && !defClosure.contains m)
  for n in #[target] ++ hyps.map hypName do
    unless (moduleOf? env n).any fun m => defs.contains m && isLocal.contains m do
      problems := problems.push s!"{n} is not declared by the claim's definitions"
  -- 3. The theorem.
  let some (.thmInfo v) := env.find? thm
    | return reject (problems.push s!"there is no theorem {thm}")
  let forms := [(false, false), (true, false), (false, true), (true, true)]
  let form := forms.find? fun (r, n) => v.levelParams.isEmpty && v.type == claimType target hyps r n
  if form.isNone then problems := problems.push s!"the type of {thm} is none of the claims"
  -- 4. Axioms.
  let axs ← runCore env (collectAxioms thm)
  let mut axiomRefs : Array Nat := #[]
  for a in axs do
    let i? := match env.find? a with
      | some (.axiomInfo ax) => if ax.levelParams.isEmpty then
          (List.range hyps.size).find? fun i => ax.type == hypType hyps[i]! else none
      | _ => none
    match i?, form with
    | some i, some (_, false) => axiomRefs := axiomRefs.push i
    | _, _ => unless standardAxioms.contains a do
        problems := problems.push s!"{thm} depends on the axiom {a}"
  -- 5. Kernel replay of the other local modules, onto everything else.
  try
    let baseEnv ← importModules ((env.header.moduleNames.filter (!others.contains ·)).map
      ({ module := · })) {}
    for m in baseEnv.header.moduleNames do
      if others.contains m then
        problems := problems.push s!"the claim's definitions import {m}, which is built in the workspace"
    let mut new : Std.HashMap Name ConstantInfo := {}
    for (n, ci) in env.constants.map₁.toList do
      if (moduleOf? env n).any others.contains then new := new.insert n ci
    discard <| baseEnv.toKernelEnv.replay new
  catch e => problems := problems.push s!"kernel replay failed: {e}"
  let some (refute, negated) := form | return reject problems
  unless problems.isEmpty do return reject problems
  -- `H → T` and `¬(H → ¬T)` prove T; `H → ¬T` and `¬(H → T)` refute it.
  let byBinder ← if negated then pure #[] else referencedHypotheses env v hyps.size
  let refs := (List.range hyps.size).toArray.filterMap fun i =>
    let n := (binderName i).toString
    if byBinder.contains n || axiomRefs.contains i then some n else none
  return Json.mkObj [
    ("verdict", "verified"), ("claim", (← IO.FS.realPath claimDir).toString),
    ("established", claimText target hyps refute negated),
    ("outcome", if refute == negated then "proved" else "refuted"),
    ("axioms", Json.arr ((axs.filter standardAxioms.contains).map (Json.str ·.toString))),
    ("hypothesisAxioms", Json.arr ((axs.filter (!standardAxioms.contains ·)).map (Json.str ·.toString))),
    ("referencedHypotheses", Json.arr (refs.map Json.str))]

def report (j : Json) : String :=
  let s (k : String) := (j.getObjValAs? String k).toOption.getD ""
  let l (k : String) := ", ".intercalate ((j.getObjValAs? (Array String) k).toOption.getD #[]).toList
  if s "verdict" == "verified" then
    s!"sigaba-neo: verified\nclaim: {s "claim"}\nestablished: {s "established"}\n\
      outcome: {s "outcome"}\naxioms: {l "axioms"}\nhypothesis axioms: {l "hypothesisAxioms"}\n\
      referenced hypotheses: {l "referencedHypotheses"}"
  else s!"sigaba-neo: rejected\n{"\n".intercalate ((j.getObjValAs? (Array String) "problems").toOption.getD #[]).toList}"

def run (claimDir module thm : String) : CommandElabM Unit := do
  let j ← liftCoreM (liftM (do
    let j ← check claimDir module.toName thm.toName
    IO.FS.writeFile "result.json" (j.pretty ++ "\n")
    return j : IO Json))
  logInfo (report j)

syntax (name := sigabaNeoCheck) "#sigaba_neo_check " str (ppSpace str str)? : command

elab_rules : command
  | `(#sigaba_neo_check $d:str) => run d.getString "Claim" "Claim.proof"
  | `(#sigaba_neo_check $d:str $m:str $t:str) => run d.getString m.getString t.getString

end SigabaNeo.Check
