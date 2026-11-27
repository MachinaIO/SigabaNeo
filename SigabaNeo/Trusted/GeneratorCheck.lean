/-
TRUSTED. The checks of certified task generators and of solutions of sampled tasks
(`SigabaNeo.Trusted.Benchmark`). Same style as `SigabaNeo.Trusted.Check`: every expected statement
is built from names and numerals as an `Expr`, never elaborated from text; the module is imported
apart from the command's own environment; only the axioms `propext`, `Classical.choice` and
`Quot.sound` are allowed; and every declaration of every module built in the workspace, and of
every module of the standard library that the family's module does not import, passes the kernel
again (replayed onto the rest).

The family, the levels `L`, the seed width `k`, the diversity `h`, the level and the seed come from
the trusted policy and the trusted sampler, never from the generator.

    #sigaba_generator_check "<module>" "<family>" "<generate>" "<certificate>" L k h

checks that `<family>` is a definition of type `SigabaNeo.Benchmark.Family` declared outside the
workspace, and that `<certificate>` is a theorem whose type is exactly
`SigabaNeo.Benchmark.Certified <family> L k h <generate>`: universal over every level and seed.
It writes `generator-result.json`.

    #sigaba_generator_sample "<module>" "<family>" "<generate>" L k level "<seed: k digits 0/1>" [heartbeats]

is the runtime bridge. Seed bit `i` is the value of the seed at `i`. It runs
`<family>.encode (<generate> ⟨level, _⟩ seed)` with Lean's evaluator (the compiled code of the
encoder and the generator), then has the kernel check the theorem
`<family>.encode (<generate> ⟨level, _⟩ seed) = <the bits it printed>` by `Eq.refl`, with a bounded
number of heartbeats (`heartbeats` thousands, as the option `maxHeartbeats`; by default
`sampleHeartbeats`). The descriptor is printed only if the kernel accepts. A level `≥ L`, a seed
of the wrong width, a failed evaluation, an oversized output, a mismatch or a timeout is rejected.
It writes `sample-result.json`.

    #sigaba_generator_link "<module>" "<family>" "<generate>" L k level "<seed>" "<descriptor>" [heartbeats]

is the same kernel check of a given descriptor, without running any generator code (the evaluator
is not called). The generator's compiled code runs in the sample command's process, so a runner
that does not trust that process accepts a descriptor only once this command, in a separate
process, confirms it. It writes `link-result.json`.

Modules are local to the workspace when their build outputs are under `.lake/build` of the
current directory: run every command from the workspace's root.

    #sigaba_task_check "<module>" "<family>" "<descriptor bits 0/1>" "<theorem>" "<forbidden>"…

checks a solver's theorem: its type is exactly `SigabaNeo.Benchmark.Target <family> <bits>`, and
no module of the environment has one of the forbidden prefixes (by name components, e.g. the
generator's modules, whose certificate is not a premise of the solution). It writes
`task-result.json`.
-/
import Lean

open Lean Elab Command Meta

namespace SigabaNeo.GeneratorCheck

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The module of the trusted vocabulary. -/
def benchmarkModule : Name := `SigabaNeo.Trusted.Benchmark

def familyType : Expr := mkConst `SigabaNeo.Benchmark.Family

/-- The numeral `n : ℕ` as elaborated: `@OfNat.ofNat ℕ n (instOfNatNat n)`. -/
def natLit (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [Level.zero]) (mkConst ``Nat) (mkRawNatLit n)
    (mkApp (mkConst ``instOfNatNat) (mkRawNatLit n))

def boolLit (b : Bool) : Expr := mkConst (if b then ``Bool.true else ``Bool.false)

def listBool : Expr := mkApp (mkConst ``List [Level.zero]) (mkConst ``Bool)

/-- The list literal `[b₀, b₁, …] : List Bool`. -/
def bitsLit (bs : List Bool) : Expr :=
  bs.foldr (fun b e => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Bool) (boolLit b) e)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Bool))

def parseBits (s : String) : Option (List Bool) :=
  s.toList.mapM fun c => if c == '0' then some false else if c == '1' then some true else none

def showBits (bs : List Bool) : String := String.ofList (bs.map fun b => if b then '1' else '0')

/-- `Certified F L k h gen`, built from the names and the numerals. -/
def certifiedType (family gen : Name) (L k h : Nat) : Expr :=
  mkApp5 (mkConst `SigabaNeo.Benchmark.Certified) (mkConst family) (natLit L) (natLit k)
    (natLit h) (mkConst gen)

/-- `Target F bits`, built from the name and the bits. -/
def targetType (family : Name) (bits : List Bool) : Expr :=
  mkApp2 (mkConst `SigabaNeo.Benchmark.Target) (mkConst family) (bitsLit bits)

/-- `⟨level, _⟩ : Fin L`, with the proof `of_decide_eq_true rfl` of `level < L`. -/
def finLit (L level : Nat) : Expr :=
  let lt := mkApp4 (mkConst ``LT.lt [Level.zero]) (mkConst ``Nat) (mkConst ``instLTNat)
    (natLit level) (natLit L)
  let prf := mkApp3 (mkConst ``of_decide_eq_true) lt
    (mkApp2 (mkConst ``Nat.decLt) (natLit level) (natLit L))
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  mkApp3 (mkConst ``Fin.mk) (natLit L) (natLit level) prf

/-- The seed `fun i : Fin k => [b₀, …].getD i false`: seed bit `i` is its value at `i`. -/
def seedLit (k : Nat) (seed : List Bool) : Expr :=
  .lam `i (mkApp (mkConst ``Fin) (natLit k))
    (mkApp4 (mkConst ``List.getD [Level.zero]) (mkConst ``Bool) (bitsLit seed)
      (mkApp2 (mkConst ``Fin.val) (natLit k) (.bvar 0)) (boolLit false)) .default

/-- `F.encode (gen ⟨level, _⟩ seed)`. -/
def encodeSample (family gen : Name) (L k level : Nat) (seed : List Bool) : Expr :=
  mkApp2 (mkConst `SigabaNeo.Benchmark.Family.encode) (mkConst family)
    (mkApp2 (mkConst gen) (finLit L level) (seedLit k seed))

def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?

def runCore (env : Environment) (x : CoreM α) (heartbeats : Nat := 0) : IO α := do
  let ctx : Core.Context :=
    { fileName := "<sigaba-neo>", fileMap := default, maxHeartbeats := heartbeats }
  return (← x.toIO ctx { env }).1

/-- The modules built in the workspace (the current directory). -/
def localModules (env : Environment) : IO NameSet := do
  let localDir := ((← IO.currentDir) / ".lake" / "build").toString ++ "/"
  let mut isLocal : NameSet := {}
  for m in env.header.moduleNames do
    if (← findOLean m).toString.startsWith localDir then isLocal := isLocal.insert m
  return isLocal

/-- The modules that `m` imports, transitively, with `m`. -/
def importClosure (env : Environment) (m : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [m]
  while !todo.isEmpty do
    let m := todo.head!
    todo := todo.tail!
    if seen.contains m then continue
    seen := seen.insert m
    if let some i := env.getModuleIdx? m then
      if let some d := env.header.moduleData[i.toNat]? then
        todo := d.imports.toList.map (·.module) ++ todo
  return seen

/-- The trusted vocabulary comes from the core, and the family is a definition of type `Family`
declared outside the workspace. Returns the family's module. -/
def checkVocabulary (env : Environment) (isLocal : NameSet) (family : Name) :
    Array String × Option Name := Id.run do
  let mut problems : Array String := #[]
  for n in [`SigabaNeo.Benchmark.Family, `SigabaNeo.Benchmark.Certified,
      `SigabaNeo.Benchmark.Target, `SigabaNeo.Benchmark.Family.encode] do
    unless moduleOf? env n == some benchmarkModule && !isLocal.contains benchmarkModule do
      problems := problems.push s!"{n} is not the core's ({benchmarkModule})"
  let fm := moduleOf? env family
  match env.find? family with
  | some (.defnInfo v) =>
    unless v.levelParams.isEmpty && v.type == familyType do
      problems := problems.push s!"{family} is not a family (of type SigabaNeo.Benchmark.Family)"
    if fm.any isLocal.contains then
      problems := problems.push s!"the family {family} is declared in the workspace"
  | _ => problems := problems.push s!"there is no definition {family}"
  return (problems, fm)

/-- Every axiom is a standard one. -/
def checkAxioms (env : Environment) (n : Name) : IO (Array String × Array Name) := do
  let axs ← runCore env (collectAxioms n)
  return (axs.filterMap fun a =>
    if standardAxioms.contains a then none else some s!"{n} depends on the axiom {a}", axs)

/-- Kernel replay of every declaration of the workspace's modules, and of the std modules that the
family's module does not import, onto everything else. -/
def replay (env : Environment) (isLocal : NameSet) (familyModule : Option Name) :
    IO (Array String) := do
  let trusted := (familyModule.map (importClosure env)).getD {}
  let others := env.header.moduleNames.filter fun m =>
    isLocal.contains m || (m.getRoot == `SigabaNeoStd && !trusted.contains m)
  try
    let baseEnv ← importModules ((env.header.moduleNames.filter (!others.contains ·)).map
      ({ module := · })) {}
    let mut problems : Array String := #[]
    for m in baseEnv.header.moduleNames do
      if others.contains m then
        problems := problems.push s!"the family's modules import {m}, which is replayed"
    let mut new : Std.HashMap Name ConstantInfo := {}
    for (n, ci) in env.constants.map₁.toList do
      if (moduleOf? env n).any others.contains then new := new.insert n ci
    discard <| baseEnv.toKernelEnv.replay new
    return problems
  catch e => return #[s!"kernel replay failed: {e}"]

def reject (ps : Array String) : Json :=
  Json.mkObj [("verdict", "rejected"), ("problems", Json.arr (ps.map Json.str))]

def load (module : Name) : IO (Except String Environment) := do
  try
    return .ok (← importModules #[{ module }] {})
  catch e => return .error s!"cannot load: {e}"

/-! ### The generator's certificate -/

def checkGenerator (module family gen cert : Name) (L k h : Nat) : IO Json := do
  let env ← match ← load module with
    | .ok env => pure env
    | .error e => return reject #[e]
  let isLocal ← localModules env
  let (ps, fm) := checkVocabulary env isLocal family
  let mut problems := ps
  match env.find? gen with
  | some (.defnInfo v) =>
    unless v.levelParams.isEmpty do problems := problems.push s!"{gen} is universe polymorphic"
  | _ => problems := problems.push s!"there is no definition {gen}"
  let expected := certifiedType family gen L k h
  match env.find? cert with
  | some (.thmInfo v) =>
    unless v.levelParams.isEmpty && v.type == expected do
      problems := problems.push
        s!"the type of {cert} is not SigabaNeo.Benchmark.Certified {family} {L} {k} {h} {gen}"
  | _ => problems := problems.push s!"there is no theorem {cert}"
  if problems.isEmpty then
    problems := problems ++ (← checkAxioms env cert).1
  problems := problems ++ (← replay env isLocal fm)
  unless problems.isEmpty do return reject problems
  return Json.mkObj [
    ("verdict", "certified"), ("module", module.toString), ("family", family.toString),
    ("generator", gen.toString), ("certificate", cert.toString),
    ("levels", L), ("seedBits", k), ("diversityBits", h),
    ("established", s!"SigabaNeo.Benchmark.Certified {family} {L} {k} {h} {gen}"),
    ("axioms", Json.arr ((← checkAxioms env cert).2.map (Json.str ·.toString)))]

/-! ### The runtime bridge -/

/-- The default kernel budget for the link of one sample, in thousands of heartbeats (the unit of
the option `maxHeartbeats`). -/
def sampleHeartbeats : Nat := 400000

/-- The longest descriptor accepted, in bits. -/
def maxDescriptorBits : Nat := 1 <<< 20

/-- Run `F.encode (gen ⟨level, _⟩ seed)` with the evaluator. The encoder is the head normal form of
`F.encode` (the family's own encoder, compiled even when the family is noncomputable as a whole:
its other fields are mathematical objects). -/
unsafe def evalSampleImpl (family gen : Name) (L k level : Nat) (seed : List Bool) :
    MetaM (List Bool) := do
  let enc ← whnf (mkApp (mkConst `SigabaNeo.Benchmark.Family.encode) (mkConst family))
  let task := mkApp2 (mkConst gen) (finLit L level) (seedLit k seed)
  evalExpr (List Bool) listBool (mkApp enc task)

@[implemented_by evalSampleImpl]
opaque evalSample (family gen : Name) (L k level : Nat) (seed : List Bool) : MetaM (List Bool)

/-- Sample (`supplied = none`: run the generator with the evaluator, then let the kernel confirm the
descriptor) or link (`supplied = some bits`: no generator code runs at all; only the kernel checks
that `F.encode (gen ⟨level, _⟩ seed)` reduces to the given bits). A runner that does not trust the
process which evaluated the generator links its output in a separate process. -/
def sample (module family gen : Name) (L k level : Nat) (seedText : String)
    (heartbeats : Nat := sampleHeartbeats) (supplied : Option String := none) : IO Json := do
  let some seed := parseBits seedText
    | return reject #["the seed is not a string of 0 and 1"]
  unless seed.length == k do
    return reject #[s!"the seed has {seed.length} bits, not {k}"]
  unless level < L do
    return reject #[s!"the level {level} is not supported (the generator has {L} levels)"]
  let env ← match ← load module with
    | .ok env => pure env
    | .error e => return reject #[e]
  let isLocal ← localModules env
  let (ps, fm) := checkVocabulary env isLocal family
  let mut problems := ps
  match env.find? gen with
  | some (.defnInfo v) =>
    unless v.levelParams.isEmpty do problems := problems.push s!"{gen} is universe polymorphic"
  | _ => problems := problems.push s!"there is no definition {gen}"
  unless problems.isEmpty do return reject problems
  problems := (← checkAxioms env gen).1 ++ (← replay env isLocal fm)
  unless problems.isEmpty do return reject problems
  -- The evaluator, unless the descriptor is given.
  let bits ← match supplied with
    | some text => match parseBits text with
      | some b => pure b
      | none => return reject #["the descriptor is not a string of 0 and 1"]
    | none => try runCore env (evalSample family gen L k level seed |>.run')
        catch e => return reject #[s!"the evaluation failed: {e}"]
  if bits.length > maxDescriptorBits then
    return reject #[s!"the descriptor has {bits.length} bits, more than {maxDescriptorBits}"]
  -- The kernel's check of the link.
  let stmt := mkApp3 (mkConst ``Eq [Level.one]) listBool (encodeSample family gen L k level seed)
    (bitsLit bits)
  let decl := Declaration.thmDecl {
    name := `SigabaNeo.GeneratorCheck.sampleLink, levelParams := [], type := stmt,
    value := mkApp2 (mkConst ``Eq.refl [Level.one]) listBool (bitsLit bits) }
  match env.addDeclCore (heartbeats * 1000).toUSize 100000 decl none with
  | .error e =>
    let msg ← try (e.toMessageData {}).toString catch _ => pure "kernel error"
    return reject #[s!"the kernel does not confirm the evaluated descriptor: {msg}"]
  | .ok _ =>
    return Json.mkObj [
      ("verdict", "linked"), ("module", module.toString), ("family", family.toString),
      ("generator", gen.toString), ("levels", L), ("seedBits", k), ("level", level),
      ("seed", seedText), ("descriptor", showBits bits), ("descriptorBits", bits.length),
      ("evaluated", supplied.isNone),
      ("established", s!"{family}.encode ({gen} ⟨{level}, _⟩ seed) = descriptor")]

/-! ### A solver's theorem -/

def checkTask (module family thm : Name) (bitsText : String) (forbidden : Array Name) :
    IO Json := do
  let some bits := parseBits bitsText
    | return reject #["the descriptor is not a string of 0 and 1"]
  let env ← match ← load module with
    | .ok env => pure env
    | .error e => return reject #[e]
  let isLocal ← localModules env
  let (ps, fm) := checkVocabulary env isLocal family
  let mut problems := ps
  for m in env.header.moduleNames do
    if forbidden.any (·.isPrefixOf m) then
      problems := problems.push s!"the solution imports the forbidden module {m}"
  match env.find? thm with
  | some (.thmInfo v) =>
    unless v.levelParams.isEmpty && v.type == targetType family bits do
      problems := problems.push
        s!"the type of {thm} is not SigabaNeo.Benchmark.Target {family} <the descriptor>"
  | _ => problems := problems.push s!"there is no theorem {thm}"
  if problems.isEmpty then
    problems := problems ++ (← checkAxioms env thm).1
  problems := problems ++ (← replay env isLocal fm)
  unless problems.isEmpty do return reject problems
  return Json.mkObj [
    ("verdict", "solved"), ("module", module.toString), ("family", family.toString),
    ("theorem", thm.toString), ("descriptor", bitsText),
    ("established", s!"SigabaNeo.Benchmark.Target {family} <descriptor>"),
    ("axioms", Json.arr ((← checkAxioms env thm).2.map (Json.str ·.toString)))]

/-! ### Commands -/

def report (j : Json) : String :=
  let s (k : String) := (j.getObjValAs? String k).toOption.getD ""
  let ps := (j.getObjValAs? (Array String) "problems").toOption.getD #[]
  if s "verdict" == "rejected" then s!"sigaba-neo: rejected\n{"\n".intercalate ps.toList}"
  else s!"sigaba-neo: {s "verdict"}\n{j.pretty}"

def emit (file : System.FilePath) (x : IO Json) : CommandElabM Unit := do
  let j ← liftCoreM (liftM (do
    let j ← x
    IO.FS.writeFile file (j.pretty ++ "\n")
    return j : IO Json))
  logInfo (report j)

syntax (name := generatorCheck) "#sigaba_generator_check " str str str str num num num : command
syntax (name := generatorSample)
  "#sigaba_generator_sample " str str str num num num str (ppSpace num)? : command
syntax (name := generatorLink)
  "#sigaba_generator_link " str str str num num num str str (ppSpace num)? : command
syntax (name := taskCheck) "#sigaba_task_check " str str str str (ppSpace str)* : command

elab_rules : command
  | `(#sigaba_generator_check $m:str $f:str $g:str $c:str $L:num $k:num $h:num) =>
    emit "generator-result.json" (checkGenerator m.getString.toName f.getString.toName
      g.getString.toName c.getString.toName L.getNat k.getNat h.getNat)
  | `(#sigaba_generator_sample $m:str $f:str $g:str $L:num $k:num $d:num $s:str $[$hb:num]?) =>
    emit "sample-result.json" (sample m.getString.toName f.getString.toName g.getString.toName
      L.getNat k.getNat d.getNat s.getString ((hb.map (·.getNat)).getD sampleHeartbeats))
  | `(#sigaba_generator_link $m:str $f:str $g:str $L:num $k:num $d:num $s:str $b:str
      $[$hb:num]?) =>
    emit "link-result.json" (sample m.getString.toName f.getString.toName g.getString.toName
      L.getNat k.getNat d.getNat s.getString ((hb.map (·.getNat)).getD sampleHeartbeats)
      (some b.getString))
  | `(#sigaba_task_check $m:str $f:str $b:str $t:str $[$p:str]*) =>
    emit "task-result.json" (checkTask m.getString.toName f.getString.toName t.getString.toName
      b.getString (p.map (·.getString.toName)))

end SigabaNeo.GeneratorCheck
