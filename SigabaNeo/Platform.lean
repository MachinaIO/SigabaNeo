/-
UNTRUSTED. The Lean side of the Prove2Me-compatible platform (`python/p2m_server.py`,
docs/PLATFORM.md). The platform decides the statuses it reports with these commands, but nothing
depends on them: a client checks every proof itself with the trusted `#sigaba_neo_check`.

* `#sigaba_neo_platform_module "M" "definition"|"theorem" "<theorem name>" "out.json"`: may the built
  module `M` be published as a definition (no `sorry`, nothing forbidden) or as the statement of
  the named theorem (it declares that theorem and nothing else)?
* `#sigaba_neo_platform_submission "<theorem>" "prove"|"disprove" "Solutions.M" "out.json"`: the
  status of a submission (`OK`, `WA`, `SORRY`, `FAILED`, `CE`) and the platform theorems it uses.
* `#sigaba_neo_platform_canon "File.lean" "out.txt"`: the file's canonical form, its syntax tree
  without positions, whitespace or comments (header and every command, parsed after the imports
  and the earlier commands, as Lean parses it). The platform's content IDs hash it.
-/
import SigabaNeo.Trusted.Check

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

/-! ### Canonical form -/

/-- A syntax tree without source information: node kinds, atoms, and resolved identifiers. -/
partial def canonSyntax : Syntax → String
  | .missing => "?"
  | .node _ kind args =>
    "(" ++ kind.toString ++ args.foldl (fun acc a => acc ++ " " ++ canonSyntax a) "" ++ ")"
  | .atom _ val => val.quote
  | .ident _ _ val _ => "`" ++ (val.toString (escape := true)).quote

/-- The canonical form of a Lean file: its header and commands, parsed (and elaborated, since
later commands can depend on earlier ones) in the current search path. Importing with the
imported modules' parser extensions runs their initializers, as compiling the file does. -/
unsafe def canonFileUnsafe (path : System.FilePath) : IO String := do
  enableInitializersExecution
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header {} messages inputCtx
  let s ← Elab.IO.processCommands inputCtx parserState (Command.mkState env messages {})
  let mut out := canonSyntax header.raw
  for c in s.commands do
    out := out ++ "\n" ++ canonSyntax c
  return out ++ "\n"

@[implemented_by canonFileUnsafe]
opaque canonFile (path : System.FilePath) : IO String

def write (out : String) (j : Json) : CommandElabM Unit := do
  liftCoreM (liftM (IO.FS.writeFile out (j.compress ++ "\n") : IO Unit))
  logInfo s!"{(j.getObjValAs? String "status").toOption.getD "?"}"

syntax (name := platformModule) "#sigaba_neo_platform_module " str str str str : command
syntax (name := platformSubmission) "#sigaba_neo_platform_submission " str str str str : command
syntax (name := platformCanon) "#sigaba_neo_platform_canon " str str : command

elab_rules : command
  | `(#sigaba_neo_platform_module $m:str $k:str $t:str $o:str) => do
    write o.getString (← liftCoreM (liftM (moduleCheck m.getString.toName k.getString
      t.getString.toName : IO Json)))
  | `(#sigaba_neo_platform_submission $t:str $k:str $s:str $o:str) => do
    write o.getString (← liftCoreM (liftM (submissionCheck t.getString.toName
      (k.getString == "disprove") s.getString.toName : IO Json)))

elab_rules : command
  | `(#sigaba_neo_platform_canon $f:str $o:str) => do
    let c ← liftCoreM (liftM (canonFile f.getString : IO String))
    liftCoreM (liftM (IO.FS.writeFile o.getString c : IO Unit))
    logInfo s!"{c.length} characters"

end SigabaNeo.Platform
