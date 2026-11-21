import SigabaNeo.Trusted.Assumption
import SigabaNeo.Trusted.Primitive

/-!
# Predicate encryption (weakly attribute-hiding)

Predicate encryption as a Sigaba Neo primitive (`SigabaNeo.Trusted.Primitive`), independent of any
implementation. It follows Section 3.2 of Brakerski–Tsabary–Vaikuntanathan–Wee, *Private
Constrained PRFs (and more) from LWE* (ePrint 2017/795), made concrete in the way of the Sigaba
Neo concept: "`1 − negl(λ)`" becomes `1 − 2^{-κ}` and "every PPT adversary has negligible
advantage" becomes "every explicit adversary has `cost / advantage² ≥ 2^λ`".

**Universes.** A `Universe` is the paper's attribute universe `X` and message space `M`, with the
encodings of their elements as bit strings, the predicates the scheme must support (`Req`, each a
relation `req r x`: "`r` is authorized for `x`"), and the description given to the algorithms. The
universe is fixed outside the primitive; `PE U` is the primitive for `U`.

**Predicates are the implementation's.** How a predicate is represented (a circuit, a branching
program, …) is not fixed: a predicate `C` is any word, and the implementation gives it its meaning
by the deterministic algorithm `Eval(C, x)`, whose output `[true]` means "`C` is authorized for
`x`" (`Authorized`; the paper's `C(x) = 0`). The paper's predicate universe is thus the
implementation's own; correctness and attribute hiding hold for all of it, and it must contain the
required predicates (`Expressive`).

**Parameters.** `λ` (`secBits`), the correctness failure target `κ` (`corrBits`), and the numbers
of runs the cost assumes: `q` encryptions and decryptions (`runs`) and `q_k` key generations
(`keyRuns`). Every algorithm receives `(1^λ, 1^κ, desc)` first; `q` and `q_k` only weigh
the cost and are not given to the algorithms.

**Algorithms.**

| Algorithm | Inputs | Outputs | Randomized |
| --- | --- | --- | --- |
| `Setup` | | `mpk`, `msk` | yes |
| `Enc` | `mpk`, `x`, `μ` | `ct` | yes |
| `KeyGen` | `msk`, `C` | `sk` | yes |
| `Dec` | `sk`, `C`, `ct` | `μ` | no |
| `Eval` | `C`, `x` | `b` | no |

The encodings of `x` and `μ` are fixed by the universe; `C`, `mpk`, `msk`, `sk` and `ct` are the
implementation's own. `Dec` outputs `⊥` by outputting a word that encodes no message.

**Propositions.**

1. `Correct`: for every `x`, every `C` authorized for `x` and every `μ`,
   `Pr[Dec(sk_C, C, Enc(mpk, x, μ)) = μ] ≥ 1 − 2^{-κ}` over the coins of `Setup`, `KeyGen`, `Enc`.
2. `AttributeHiding` (Definition 3.3, weak attribute hiding): there is a simulator `Sim` (an
   explicit machine) such that for every admissible adversary `Adv` and every distinguisher `D`,
   `(cost Adv + cost D) / advantage² ≥ 2^λ`, where the advantage is that of `D` between the
   outputs `(x, μ, α)` of `exp^real` and `exp^ideal`.
3. `Expressive`: every required predicate `r` is some `C`: `C` is authorized for exactly the `x`
   with `req r x`.

Correctness and attribute hiding together make `Eval` the meaning the scheme actually has: a key for
`C` decrypts the attributes `C` is authorized for (correctness), and no others, since a key that
decrypted an unauthorized attribute would be an admissible key query that recovers `μ`.

**The experiments as one interactive machine.** The stateful adversary of Definition 3.3 is one
`Machine 3` that talks to the experiment through three channels:

* `selectOp` (step 1–2): it writes `x`; the experiment runs `Setup` and answers `mpk`.
* `keyGenOp` (steps 3, 5): it writes `C`; the experiment answers `KeyGen(msk, C)`.
* `challengeOp` (steps 3–4): it writes `μ`; the experiment answers `Enc(mpk, x, μ)` in the real
  experiment and `Sim(mpk, X, M)` in the ideal one.

Its output word is `α` (step 5–6). A query out of this order (a second `x` or `μ`, a key or a
challenge before `x`), or a word that encodes no element, is answered with the empty word and
changes nothing. `Adv` is admissible if, with probability `1` in both experiments, every key query
`C` it makes is not authorized for `x` (`GameState.bad` records a violation).

**Cost.** The steps of the assumed use, one `Setup`, `q_k` runs of `KeyGen` and `q` runs each of
`Enc` and `Dec`, each run counted at its worst case (the machine's clock), plus the description
length of each machine once:

    time(Setup) + q_k · time(KeyGen) + q · (time(Enc) + time(Dec))
      + descLen(Setup) + descLen(KeyGen) + descLen(Enc) + descLen(Dec)

The description lengths exclude implementations that replace computation by a table hard-wired in
the control states, which the parameters being fixed would otherwise allow. `Eval` only gives
predicates their meaning and is not counted.
-/

namespace AdvancedEncryption

open SigabaNeo

namespace PE

/-- The attribute universe `X` and message space `M` with the encodings of their elements, the
predicates the scheme must support, and the description given to the algorithms. -/
structure Universe where
  /-- The attribute universe `X`. -/
  Attr : Type
  /-- The message space `M`. -/
  Msg : Type
  /-- The encoding of attributes. -/
  encAttr : Attr ↪ List Bool
  /-- The encoding of messages. -/
  encMsg : Msg ↪ List Bool
  /-- The required predicates. -/
  Req : Type
  /-- `req r x`: the required predicate `r` is authorized for `x`. -/
  req : Req → Attr → Prop
  /-- The description given to the algorithms. -/
  desc : List Bool

/-- The parameters of predicate encryption. -/
structure Params where
  /-- `λ`: the bits of security of attribute hiding. -/
  secBits : ℕ
  /-- `κ`: decryption fails with probability at most `2^{-κ}`. -/
  corrBits : ℕ
  /-- `q`: the number of runs of `Enc` and of `Dec` the cost assumes. -/
  runs : ℕ
  /-- `q_k`: the number of runs of `KeyGen` the cost assumes. -/
  keyRuns : ℕ

/-- The algorithms of predicate encryption. -/
inductive Alg where
  | setup | enc | keyGen | dec | eval
  deriving DecidableEq

/-- The signatures of the algorithms. -/
def sig : Alg → AlgSig
  | .setup => { name := "Setup", inputs := [], outputs := ["mpk", "msk"], randomized := true }
  | .enc => { name := "Enc", inputs := ["mpk", "x", "μ"], outputs := ["ct"], randomized := true }
  | .keyGen => { name := "KeyGen", inputs := ["msk", "C"], outputs := ["sk"], randomized := true }
  | .dec => { name := "Dec", inputs := ["sk", "C", "ct"], outputs := ["μ"], randomized := false }
  | .eval => { name := "Eval", inputs := ["C", "x"], outputs := ["b"], randomized := false }

/-- The propositions of predicate encryption. -/
inductive PropIndex where
  | correctness | attributeHiding | expressiveness
  deriving DecidableEq

variable (U : Universe)

/-- The encoded parameters given to every algorithm: `(1^λ, 1^κ, desc)`. -/
def paramsWord (p : Params) : List Bool :=
  encodeTuple [List.replicate p.secBits true, List.replicate p.corrBits true, U.desc]

/-! ### The algorithms of an implementation -/

section Algorithms

variable {U} (p : Params) (impl : Impl sig)

/-- `Setup`: the law of `(mpk, msk)`. -/
noncomputable def setup : PMF (List Bool × List Bool) :=
  (impl.run .setup (paramsWord U p) []).map fun out => (out.getD 0 [], out.getD 1 [])

/-- `Enc(mpk, x, μ)`: the law of `ct`. -/
noncomputable def enc (mpk : List Bool) (x : U.Attr) (μ : U.Msg) : PMF (List Bool) :=
  (impl.run .enc (paramsWord U p) [mpk, U.encAttr x, U.encMsg μ]).map fun out => out.getD 0 []

/-- `KeyGen(msk, C)`: the law of `sk_C`. -/
noncomputable def keyGen (msk : List Bool) (C : List Bool) : PMF (List Bool) :=
  (impl.run .keyGen (paramsWord U p) [msk, C]).map fun out => out.getD 0 []

/-- `Dec((sk_C, C), ct)`: the law of its output word (a point mass: `Dec` is deterministic). -/
noncomputable def dec (sk : List Bool) (C : List Bool) (ct : List Bool) : PMF (List Bool) :=
  (impl.run .dec (paramsWord U p) [sk, C, ct]).map fun out => out.getD 0 []

/-- `Eval(C, x)`: the law of its output word (a point mass: `Eval` is deterministic). -/
noncomputable def eval (C : List Bool) (x : U.Attr) : PMF (List Bool) :=
  (impl.run .eval (paramsWord U p) [C, U.encAttr x]).map fun out => out.getD 0 []

/-- The predicate `C` is authorized for `x`: `Eval(C, x)` outputs `[true]`. -/
def Authorized (C : List Bool) (x : U.Attr) : Prop := eval p impl C x [true] = 1

end Algorithms

/-! ### Correctness -/

/-- The law of the output of `Dec((sk_C, C), ct)` for `(mpk, msk) ← Setup`, `sk_C ← KeyGen(msk, C)`
and `ct ← Enc(mpk, x, μ)`. -/
noncomputable def decryptLaw (p : Params) (impl : Impl sig) (x : U.Attr) (C : List Bool)
    (μ : U.Msg) : PMF (List Bool) := do
  let (mpk, msk) ← setup (U := U) p impl
  let sk ← keyGen (U := U) p impl msk C
  let ct ← enc p impl mpk x μ
  dec (U := U) p impl sk C ct

/-- Correctness: for all `x`, all `C` authorized for `x` and all `μ`, decryption returns `μ` with
probability at least `1 − 2^{-κ}`. -/
def Correct (p : Params) (impl : Impl sig) : Prop :=
  ∀ (x : U.Attr) (C : List Bool), Authorized p impl C x → ∀ μ : U.Msg,
    1 - ((2 : ℝ) ^ p.corrBits)⁻¹ ≤ (decryptLaw U p impl x C μ (U.encMsg μ)).toReal

/-! ### Weak attribute hiding -/

/-- The channel on which the adversary chooses the attribute `x` (answered with `mpk`). -/
def selectOp : Fin 3 := 0
/-- The key generation oracle `KeyGen(msk, ·)`. -/
def keyGenOp : Fin 3 := 1
/-- The channel on which the adversary chooses the message `μ` (answered with the challenge). -/
def challengeOp : Fin 3 := 2

/-- The state of the experiment. -/
structure GameState where
  /-- The attribute `x` chosen by the adversary. -/
  attr : Option U.Attr := none
  /-- The master public key. -/
  mpk : List Bool := []
  /-- The master secret key. -/
  msk : List Bool := []
  /-- The message `μ` chosen by the adversary. -/
  msg : Option U.Msg := none
  /-- Some key query `C` was authorized for `x`: the adversary was not admissible. -/
  bad : Bool := false

open Classical in
/-- The element a word encodes, if any. -/
noncomputable def decode {α : Type} (e : α ↪ List Bool) (w : List Bool) : Option α :=
  if h : ∃ a, e a = w then some (Classical.choose h) else none

/-- The encoding of an optional element: empty for none, `true` before the element otherwise. -/
def encOpt {α : Type} (e : α ↪ List Bool) : Option α → List Bool
  | none => []
  | some a => true :: e a

variable {U}

open Classical in
/-- The experiment's oracle. `challenge mpk x μ` is the law of the challenge ciphertext. -/
noncomputable def oracle (p : Params) (impl : Impl sig)
    (challenge : List Bool → U.Attr → U.Msg → PMF (List Bool)) :
    Fin 3 × List Bool → StateT (GameState U) PMF (List Bool) := fun q s =>
  if q.1 = selectOp then
    match s.attr, decode U.encAttr q.2 with
    | none, some x =>
      (setup (U := U) p impl).map fun keys =>
        (keys.1, { s with attr := some x, mpk := keys.1, msk := keys.2 })
    | _, _ => PMF.pure ([], s)
  else if q.1 = keyGenOp then
    match s.attr with
    | some x =>
      (keyGen (U := U) p impl s.msk q.2).map fun sk =>
        (sk, { s with bad := s.bad || decide (Authorized p impl q.2 x) })
    | none => PMF.pure ([], s)
  else
    match s.attr, s.msg, decode U.encMsg q.2 with
    | some x, none, some μ => (challenge s.mpk x μ).map fun ct => (ct, { s with msg := some μ })
    | _, _, _ => PMF.pure ([], s)

/-- The run of the adversary in an experiment, on input `(1^λ, 1^κ, desc)`: the law of its
output `α` and the final state. -/
noncomputable def game (p : Params) (impl : Impl sig)
    (challenge : List Bool → U.Attr → U.Msg → PMF (List Bool)) (A : Machine 3) :
    PMF (List Bool × GameState U) :=
  A.runWith (oracle p impl challenge) (paramsWord U p) {}

/-- The output `(x, μ, α)` of an experiment, encoded for the distinguisher. -/
def view (r : List Bool × GameState U) : List Bool :=
  encodeTuple [encOpt U.encAttr r.2.attr, encOpt U.encMsg r.2.msg, r.1]

variable (U)

/-- `exp^real`: the challenge is `Enc(mpk, x, μ)`. -/
noncomputable def real (p : Params) (impl : Impl sig) (A : Machine 3) :
    PMF (List Bool × GameState U) :=
  game p impl (enc (U := U) p impl) A

/-- The simulator's challenge `Sim(mpk, X, M)`: it is run on `(1^λ, 1^κ, desc)` and `mpk`,
and its output word is read as the encoding of `ct`, as `Enc`'s is. -/
noncomputable def simulate (p : Params) (Sim : Machine) (mpk : List Bool) : PMF (List Bool) :=
  (Sim.run (encodeTuple [paramsWord U p, mpk])).map fun w => (decodeTuple 1 w).getD 0 []

/-- `exp^ideal`: the challenge is `Sim(mpk, X, M)`. -/
noncomputable def ideal (p : Params) (impl : Impl sig) (Sim : Machine) (A : Machine 3) :
    PMF (List Bool × GameState U) :=
  game p impl (fun mpk (_ : U.Attr) (_ : U.Msg) => simulate U p Sim mpk) A

/-- The adversary is admissible: in both experiments, with probability `1`, no key query `C` is
authorized for `x`. -/
def Admissible (p : Params) (impl : Impl sig) (Sim : Machine) (A : Machine 3) : Prop :=
  (∀ r ∈ (real U p impl A).support, r.2.bad = false) ∧
    (∀ r ∈ (ideal U p impl Sim A).support, r.2.bad = false)

/-- Weak attribute hiding with `λ` bits: there is a simulator such that for every admissible
adversary and every distinguisher of the outputs `(x, μ, α)` of the two experiments,
`(cost Adv + cost D) / advantage² ≥ 2^λ`. -/
def AttributeHiding (p : Params) (impl : Impl sig) : Prop :=
  ∃ Sim : Machine, ∀ A : Machine 3, Admissible U p impl Sim A → ∀ D : Machine,
    (2 : ℝ) ^ p.secBits *
        (Problem.decision ((real U p impl A).map view) ((ideal U p impl Sim A).map view)).gain D ≤
      ((A.cost + D.cost : ℕ) : ℝ)

/-- Expressiveness: every required predicate is a predicate of the implementation, authorized for
exactly the same attributes. -/
def Expressive (p : Params) (impl : Impl sig) : Prop :=
  ∀ r : U.Req, ∃ C : List Bool, ∀ x : U.Attr, Authorized p impl C x ↔ U.req r x

/-- The cost of the assumed use: one `Setup`, `q_k` runs of `KeyGen` and `q` runs each of `Enc`
and `Dec`, at their worst-case steps, plus the description length of each machine once. -/
def cost (p : Params) (impl : Impl sig) : ℕ :=
  (impl.machine .setup).time + p.keyRuns * (impl.machine .keyGen).time +
    p.runs * ((impl.machine .enc).time + (impl.machine .dec).time) +
    ((impl.machine .setup).descLen + (impl.machine .keyGen).descLen +
      (impl.machine .enc).descLen + (impl.machine .dec).descLen)

end PE

/-- Predicate encryption for the universe `U` at the parameters `p`. -/
def PE (U : PE.Universe) (p : PE.Params) : Primitive where
  Params := PE.Params
  params := p
  encodeParams := PE.paramsWord U
  Alg := PE.Alg
  sig := PE.sig
  PropIndex := PE.PropIndex
  prop
    | .correctness, p, impl => PE.Correct U p impl
    | .attributeHiding, p, impl => PE.AttributeHiding U p impl
    | .expressiveness, p, impl => PE.Expressive U p impl
  cost p impl := PE.cost p impl

end AdvancedEncryption
