import SigabaNeo.Lib.Machines.Prog.Frame
import SigabaNeo.Lib.Machines.Prog.Det

/-!
# Per-tape bounds of tape programs by symbolic evaluation

`timeBoundT p ℓ` (`SigabaNeo.Lib.Machines.Prog.BoundsT`) is defined by recursion on the syntax of
`p`, and a program of the word algorithms has thousands of primitives, so its per-tape bound is
computed here by a **verified abstract interpreter** over symbolic sizes:

* sizes are polynomials with natural coefficients in variables `N, K, m, …` (`Sym.Poly`, a list of
  monomials with coefficients; `Sym.pEval ρ` evaluates at the values `ρ` of the variables);
* an abstract store `σ : Sym.Asg` assigns a polynomial to each tape; it stands for the per-tape
  bound `Sym.bnd ρ σ : Fin k → ℕ`;
* `Sym.absRun fuel p σ = some (σ', w)` runs `p` abstractly: `σ'` bounds the tapes afterwards and
  `w` counts the *sweeps* of the compiled machine. A loop is analysed at an invariant abstract
  store, found by iterating the body and joining (at most `fuel` times), and charged `σ i` rounds,
  the abstract bound of its counter at entry.

**Soundness** (`absRun_sound`): for a program of the fragment `NoGrow` (deterministic, never
lengthening a word) and every per-tape bound `ℓ ≤ bnd ρ σ` whose entries are all at most `M`,

  `lenBoundT p ℓ ≤ bnd ρ σ'`  and  `timeBoundT p ℓ ≤ (2 M + 3) · pEval ρ w`.

Here `2 M + 3` is the cost of one primitive (its column machine sweeps every tape, so it is
charged the longest word `M`), and `w` the number of primitives executed, loops multiplied by their
counter lengths. Checking `absRun fuel p σ = some (σ', w)` for given `σ'`, `w` is a closed
computation (`by decide`), so the per-tape bounds of large programs are certified by evaluation.

The interpreter is cheap: copies, clears and pops are tracked exactly per tape (strong updates),
branches and loop rounds are joined (`pJoin`: the larger polynomial when one dominates the other
coefficientwise, else the sum). Domination is decided by coefficientwise subtraction (`pLe`).
-/

namespace SigabaNeo.Tape

namespace Sym

/-! ### Monomials and polynomials -/

/-- A monomial: the exponents of the variables `0, 1, 2, …` (missing ones are `0`). -/
abbrev Mono := List ℕ

/-- A polynomial with natural coefficients: a list of monomials with coefficients. -/
abbrev Poly := List (Mono × ℕ)

/-- The value of a monomial at the values `ρ` of the variables. -/
def mEval : List ℕ → Mono → ℕ
  | _, [] => 1
  | ρ, e :: es => ρ.headD 0 ^ e * mEval ρ.tail es

/-- All exponents are zero. -/
def mZero : Mono → Bool
  | [] => true
  | a :: as => a.beq 0 && mZero as

/-- Equality of monomials (up to trailing zero exponents). -/
def mBeq : Mono → Mono → Bool
  | [], bs => mZero bs
  | a :: as, [] => a.beq 0 && mZero as
  | a :: as, b :: bs => a.beq b && mBeq as bs

/-- The product of monomials. -/
def mMul : Mono → Mono → Mono
  | [], m => m
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: mMul as bs

theorem mEval_nil (ρ : List ℕ) : mEval ρ [] = 1 := by cases ρ <;> rfl

theorem mEval_of_mZero : ∀ {m : Mono}, mZero m = true → ∀ ρ, mEval ρ m = 1
  | [], _, ρ => mEval_nil ρ
  | a :: as, h, ρ => by
    simp only [mZero, Bool.and_eq_true] at h
    rw [mEval, Nat.eq_of_beq_eq_true h.1, pow_zero, one_mul, mEval_of_mZero h.2]

theorem mEval_of_mBeq : ∀ {m m' : Mono}, mBeq m m' = true → ∀ ρ, mEval ρ m = mEval ρ m'
  | [], bs, h, ρ => by rw [mEval_nil, mEval_of_mZero h]
  | a :: as, [], h, ρ => by
    simp only [mBeq, Bool.and_eq_true] at h
    rw [mEval_nil, mEval, Nat.eq_of_beq_eq_true h.1, pow_zero, one_mul, mEval_of_mZero h.2]
  | a :: as, b :: bs, h, ρ => by
    simp only [mBeq, Bool.and_eq_true] at h
    rw [mEval, mEval, Nat.eq_of_beq_eq_true h.1, mEval_of_mBeq h.2]

theorem mEval_mMul : ∀ (m m' : Mono) (ρ : List ℕ), mEval ρ (mMul m m') = mEval ρ m * mEval ρ m'
  | [], m, ρ => by rw [mMul, mEval_nil, one_mul]
  | a :: as, [], ρ => by rw [mMul, mEval_nil, mul_one]
  | a :: as, b :: bs, ρ => by
    rw [mMul, mEval, mEval, mEval, mEval_mMul as bs, pow_add]; ring

/-- The value of a polynomial. -/
def pEval (ρ : List ℕ) : Poly → ℕ
  | [] => 0
  | (m, c) :: p => c * mEval ρ m + pEval ρ p

/-- The constant polynomial `c`. -/
def pC (c : ℕ) : Poly := [([], c)]

@[simp] theorem pEval_pC (ρ : List ℕ) (c : ℕ) : pEval ρ (pC c) = c := by
  simp [pC, pEval, mEval_nil]

@[simp] theorem pEval_nil (ρ : List ℕ) : pEval ρ [] = 0 := rfl

/-- Add a term, merging it with a term of the same monomial. -/
def addTerm : Mono × ℕ → Poly → Poly
  | t, [] => [t]
  | (m, c), (m', c') :: p => if mBeq m m' then (m', c + c') :: p else (m', c') :: addTerm (m, c) p

theorem pEval_addTerm (ρ : List ℕ) (m : Mono) (c : ℕ) :
    ∀ p : Poly, pEval ρ (addTerm (m, c) p) = c * mEval ρ m + pEval ρ p
  | [] => by simp [addTerm, pEval]
  | (m', c') :: p => by
    simp only [addTerm]
    split_ifs with h
    · simp only [pEval, mEval_of_mBeq h ρ]; ring
    · simp only [pEval, pEval_addTerm ρ m c p]; ring

/-- The sum of polynomials. -/
def pAdd : Poly → Poly → Poly
  | p, [] => p
  | p, t :: q => pAdd (addTerm t p) q

@[simp] theorem pEval_pAdd (ρ : List ℕ) : ∀ p q : Poly, pEval ρ (pAdd p q) = pEval ρ p + pEval ρ q
  | p, [] => rfl
  | p, (m, c) :: q => by
    simp only [pAdd, pEval_pAdd ρ _ q, pEval_addTerm, pEval]; ring

/-- A polynomial times a term. -/
def pScale (m : Mono) (c : ℕ) : Poly → Poly
  | [] => []
  | (m', c') :: q => (mMul m m', c * c') :: pScale m c q

theorem pEval_pScale (ρ : List ℕ) (m : Mono) (c : ℕ) :
    ∀ q : Poly, pEval ρ (pScale m c q) = c * mEval ρ m * pEval ρ q
  | [] => by simp [pScale, pEval]
  | (m', c') :: q => by
    simp only [pScale, pEval, pEval_pScale ρ m c q, mEval_mMul]; ring

/-- The product of polynomials. -/
def pMul : Poly → Poly → Poly
  | [], _ => []
  | (m, c) :: p, q => pAdd (pMul p q) (pScale m c q)

@[simp] theorem pEval_pMul (ρ : List ℕ) : ∀ p q : Poly, pEval ρ (pMul p q) = pEval ρ p * pEval ρ q
  | [], q => by simp [pMul, pEval]
  | (m, c) :: p, q => by
    simp only [pMul, pEval_pAdd, pEval_pMul ρ p q, pEval_pScale, pEval]; ring

/-- Subtract a term from a term of the same monomial with a large enough coefficient. -/
def subTerm : Mono × ℕ → Poly → Option Poly
  | (_, c), [] => if c.beq 0 then some [] else none
  | (m, c), (m', c') :: p =>
    if mBeq m m' && c.ble c' then some ((m', c' - c) :: p)
    else (subTerm (m, c) p).map ((m', c') :: ·)

theorem pEval_subTerm (ρ : List ℕ) (m : Mono) (c : ℕ) :
    ∀ (p p' : Poly), subTerm (m, c) p = some p' → pEval ρ p = c * mEval ρ m + pEval ρ p'
  | [], p', h => by
    simp only [subTerm] at h
    split_ifs at h with hc
    · simp only [Option.some.injEq] at h
      subst h
      simp [Nat.eq_of_beq_eq_true hc, pEval]
  | (m', c') :: p, p', h => by
    simp only [subTerm] at h
    split_ifs at h with hc
    · simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hc
      have hcc := Nat.le_of_ble_eq_true hc.2
      simp only [pEval, mEval_of_mBeq hc.1 ρ]
      have : c' = c + (c' - c) := by omega
      conv_lhs => rw [this]
      ring
    · rcases hq : subTerm (m, c) p with _ | q
      · rw [hq] at h; simp at h
      · rw [hq] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp only [pEval, pEval_subTerm ρ m c p q hq]; ring

/-- `p ≤ q` coefficientwise, decided by subtracting the terms of `p` from `q`. -/
def pLe : Poly → Poly → Bool
  | [], _ => true
  | t :: p, q => match subTerm t q with
    | some q' => pLe p q'
    | none => false

theorem pEval_le_of_pLe (ρ : List ℕ) : ∀ {p q : Poly}, pLe p q = true → pEval ρ p ≤ pEval ρ q
  | [], _, _ => Nat.zero_le _
  | (m, c) :: p, q, h => by
    simp only [pLe] at h
    rcases hq : subTerm (m, c) q with _ | q'
    · rw [hq] at h; simp at h
    · rw [hq] at h
      have := pEval_le_of_pLe ρ h
      rw [pEval_subTerm ρ m c q q' hq, pEval]
      omega

/-- An upper bound of two polynomials: the larger one if one dominates, else the sum. -/
def pJoin (p q : Poly) : Poly :=
  if pLe p q then q else if pLe q p then p else pAdd p q

theorem le_pEval_pJoin (ρ : List ℕ) (p q : Poly) :
    pEval ρ p ≤ pEval ρ (pJoin p q) ∧ pEval ρ q ≤ pEval ρ (pJoin p q) := by
  unfold pJoin
  split_ifs with h1 h2
  · exact ⟨pEval_le_of_pLe ρ h1, le_rfl⟩
  · exact ⟨le_rfl, pEval_le_of_pLe ρ h2⟩
  · simp

/-! ### Abstract stores -/

/-- An abstract store: one polynomial per tape (missing tapes are blank). -/
abbrev Asg := List Poly

/-- The polynomial of tape `i`. -/
def aGet (σ : Asg) (i : ℕ) : Poly := σ.getD i []

/-- Set the polynomial of tape `i`. -/
def aSet : Asg → ℕ → Poly → Asg
  | [], 0, p => [p]
  | [], n + 1, p => [] :: aSet [] n p
  | _ :: σ, 0, p => p :: σ
  | a :: σ, n + 1, p => a :: aSet σ n p

theorem aGet_aSet : ∀ (σ : Asg) (i : ℕ) (p : Poly) (j : ℕ),
    aGet (aSet σ i p) j = if j = i then p else aGet σ j
  | [], 0, p, 0 => rfl
  | [], 0, p, j + 1 => by simp [aSet, aGet]
  | [], n + 1, p, 0 => by simp [aSet, aGet]
  | [], n + 1, p, j + 1 => by
    have := aGet_aSet [] n p j
    simp only [aGet, List.getD_nil] at this ⊢
    simp only [aSet, List.getD_cons_succ, this, Nat.add_right_cancel_iff]
  | _ :: σ, 0, p, 0 => rfl
  | _ :: σ, 0, p, j + 1 => by simp [aSet, aGet]
  | a :: σ, n + 1, p, 0 => by simp [aSet, aGet]
  | a :: σ, n + 1, p, j + 1 => by
    have := aGet_aSet σ n p j
    simp only [aGet] at this ⊢
    simp only [aSet, List.getD_cons_succ, this, Nat.add_right_cancel_iff]

/-- Pointwise domination of abstract stores. -/
def aLe : Asg → Asg → Bool
  | [], _ => true
  | p :: σ, τ => pLe p (aGet τ 0) && aLe σ τ.tail

theorem aLe_spec (ρ : List ℕ) : ∀ {σ τ : Asg}, aLe σ τ = true →
    ∀ j, pEval ρ (aGet σ j) ≤ pEval ρ (aGet τ j)
  | [], _, _, j => by simp [aGet]
  | p :: σ, τ, h, j => by
    simp only [aLe, Bool.and_eq_true] at h
    cases j with
    | zero => simpa [aGet] using pEval_le_of_pLe ρ h.1
    | succ j =>
      have := aLe_spec ρ h.2 j
      cases τ with
      | nil => simpa [aGet] using this
      | cons q τ => simpa [aGet] using this

/-- The pointwise join of abstract stores. -/
def aJoin : Asg → Asg → Asg
  | [], τ => τ
  | p :: σ, [] => p :: σ
  | p :: σ, q :: τ => pJoin p q :: aJoin σ τ

theorem le_aJoin (ρ : List ℕ) : ∀ (σ τ : Asg) (j : ℕ),
    pEval ρ (aGet σ j) ≤ pEval ρ (aGet (aJoin σ τ) j) ∧
      pEval ρ (aGet τ j) ≤ pEval ρ (aGet (aJoin σ τ) j)
  | [], τ, j => by simp [aJoin, aGet]
  | p :: σ, [], j => by simp [aJoin, aGet]
  | p :: σ, q :: τ, 0 => by simpa [aJoin, aGet] using le_pEval_pJoin ρ p q
  | p :: σ, q :: τ, j + 1 => by simpa [aJoin, aGet] using le_aJoin ρ σ τ j

variable {k : ℕ}

/-- The per-tape bound an abstract store stands for. -/
def bnd (ρ : List ℕ) (σ : Asg) : Fin k → ℕ := fun t => pEval ρ (aGet σ t.val)

theorem bnd_aSet (ρ : List ℕ) (σ : Asg) (i : Fin k) (p : Poly) :
    bnd ρ (aSet σ i.val p) = Function.update (bnd ρ σ) i (pEval ρ p) := by
  funext t
  simp only [bnd, aGet_aSet, Function.update_apply, Fin.val_inj]
  split_ifs <;> rfl

/-! ### The abstract interpreter -/

/-- A primitive of the fragment on an abstract store. -/
def absPrim : Prim k → Asg → Option Asg
  | .clear i, σ => some (aSet σ i.val [])
  | .copy i j, σ => some (aSet σ i.val (aGet σ j.val))
  | .carry _ _ _, σ => some σ
  | .tail _, σ => some σ
  | .pop _ j, σ => some (aSet σ j.val (pC 1))
  | _, _ => none

/-- Iterate the abstract body of a loop from `σ`, joining, until a round stays below the current
store (at most `n` times). Returns the invariant store, the body's result on it and its sweeps. -/
def fixIter (f : Asg → Option (Asg × Poly)) : ℕ → Asg → Option (Asg × Asg × Poly)
  | 0, _ => none
  | n + 1, σ => match f σ with
    | none => none
    | some (σb, w) => if aLe σb σ then some (σ, σb, w) else fixIter f n (aJoin σ σb)

/-- **The abstract interpreter**: the abstract store afterwards and the number of sweeps. -/
def absRun (fuel : ℕ) : Prog k → Asg → Option (Asg × Poly)
  | .prim p, σ => (absPrim p σ).map fun σ' => (σ', pC 1)
  | .coin _, _ => none
  | .seq p q, σ => match absRun fuel p σ with
    | none => none
    | some (σ₁, w₁) => match absRun fuel q σ₁ with
      | none => none
      | some (σ₂, w₂) => some (σ₂, pAdd w₁ w₂)
  | .ifBlank _ p q, σ => match absRun fuel p σ, absRun fuel q σ with
    | some (σ₁, w₁), some (σ₂, w₂) => some (aJoin σ₁ σ₂, pAdd (pJoin w₁ w₂) (pC 1))
    | _, _ => none
  | .ifBit _ p q, σ => match absRun fuel p σ, absRun fuel q σ with
    | some (σ₁, w₁), some (σ₂, w₂) => some (aJoin σ₁ σ₂, pAdd (pJoin w₁ w₂) (pC 1))
    | _, _ => none
  | .loop i body, σ => match fixIter (absRun fuel body) fuel σ with
    | none => none
    | some (σi, _, wb) => some (σi, pAdd (pMul (aGet σ i.val) (pAdd wb (pC 2))) (pC 1))
  termination_by structural p => p

/-! ### Soundness -/

theorem fixIter_spec (ρ : List ℕ) (f : Asg → Option (Asg × Poly)) :
    ∀ (n : ℕ) (σ σi σb : Asg) (w : Poly), fixIter f n σ = some (σi, σb, w) →
      f σi = some (σb, w) ∧ aLe σb σi = true ∧ ∀ j, pEval ρ (aGet σ j) ≤ pEval ρ (aGet σi j)
  | 0, σ, σi, σb, w, h => by simp [fixIter] at h
  | n + 1, σ, σi, σb, w, h => by
    simp only [fixIter] at h
    rcases hf : f σ with _ | ⟨σ₁, w₁⟩
    · rw [hf] at h; simp at h
    · rw [hf] at h
      simp only at h
      split_ifs at h with hle
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hf, hle, fun _ => le_rfl⟩
      · obtain ⟨h1, h2, h3⟩ := fixIter_spec ρ f n _ σi σb w h
        exact ⟨h1, h2, fun j => (le_aJoin ρ σ σ₁ j).1.trans (h3 j)⟩

open Prog

/-- A program of the fragment keeps every tape below a common bound `M`. -/
theorem lenBoundT_le_const (p : Prog k) (hp : p.NoGrow) {ℓ : Fin k → ℕ} {M : ℕ}
    (h : ∀ t, ℓ t ≤ M) (t : Fin k) : lenBoundT p ℓ t ≤ M := by
  have := (lenBoundT_mono p (show ℓ ≤ fun _ => M from h)).trans (lenBoundT_const_le p M) t
  rwa [lenBound_eq p hp] at this

theorem supB_le_const {ℓ : Fin k → ℕ} {M : ℕ} (h : ∀ t, ℓ t ≤ M) : supB ℓ ≤ M :=
  Finset.sup_le fun t _ => h t

theorem absPrim_sound (ρ : List ℕ) (p : Prim k) {σ σ' : Asg} (h : absPrim p σ = some σ')
    {ℓ : Fin k → ℕ} (hℓ : ℓ ≤ bnd ρ σ) : p.lenT ℓ ≤ bnd ρ σ' := by
  cases p with
  | clear i =>
    simp only [absPrim, Option.some.injEq] at h; subst h
    rw [bnd_aSet]; exact update_le_update hℓ i (by simp)
  | copy i j =>
    simp only [absPrim, Option.some.injEq] at h; subst h
    rw [bnd_aSet]; exact update_le_update hℓ i (hℓ j)
  | carry f i j => simp only [absPrim, Option.some.injEq] at h; subst h; exact hℓ
  | tail i =>
    simp only [absPrim, Option.some.injEq] at h; subst h
    exact (tailB_le i ℓ).trans hℓ
  | pop i j =>
    simp only [absPrim, Option.some.injEq] at h; subst h
    rw [bnd_aSet]
    exact update_le_update ((tailB_le i ℓ).trans hℓ) j (by simp)
  | eq | cons | snoc | consHead | snocHead => simp [absPrim] at h

theorem noGrowB_of_absPrim {p : Prim k} {σ σ' : Asg} (h : absPrim p σ = some σ') :
    p.noGrowB = true := by
  cases p <;> simp_all [absPrim, Prim.noGrowB]

/-! ### Relabelling -/

theorem _root_.SigabaNeo.Tape.Prim.map_map {m n : ℕ} (v : Fin m → Fin n) (u : Fin n → Fin k)
    (p : Prim m) : (p.map v).map u = p.map (u ∘ v) := by
  cases p <;> rfl

theorem _root_.SigabaNeo.Tape.Prim.map_id (p : Prim k) : p.map id = p := by cases p <;> rfl

theorem _root_.SigabaNeo.Tape.Prog.map_map {m n : ℕ} (v : Fin m → Fin n) (u : Fin n → Fin k) :
    ∀ p : Prog m, map u (map v p) = map (u ∘ v) p
  | .prim p => congrArg Prog.prim (Prim.map_map v u p)
  | .coin _ => rfl
  | .seq p q => by simp only [map, Prog.map_map v u p, Prog.map_map v u q]
  | .ifBlank _ p q => by simp only [map, Prog.map_map v u p, Prog.map_map v u q]; rfl
  | .ifBit _ p q => by simp only [map, Prog.map_map v u p, Prog.map_map v u q]; rfl
  | .loop _ b => by simp only [map, Prog.map_map v u b]; rfl

theorem _root_.SigabaNeo.Tape.Prog.map_id : ∀ p : Prog k, map id p = p
  | .prim p => congrArg Prog.prim (Prim.map_id p)
  | .coin _ => rfl
  | .seq p q => by simp only [map, Prog.map_id p, Prog.map_id q]
  | .ifBlank _ p q => by simp only [map, Prog.map_id p, Prog.map_id q]; rfl
  | .ifBit _ p q => by simp only [map, Prog.map_id p, Prog.map_id q]; rfl
  | .loop _ b => by simp only [map, Prog.map_id b]; rfl

theorem lenT_map {n : ℕ} {u : Fin n → Fin k} (hu : Function.Injective u) (p : Prim n)
    (ℓ : Fin k → ℕ) (j : Fin n) : (p.map u).lenT ℓ (u j) = p.lenT (ℓ ∘ u) j := by
  cases p <;> simp [Prim.map, Prim.lenT, Function.update_apply, hu.eq_iff]

/-! ### Sound summaries

`Sound p σ σ' w`: wherever `p` is placed (`map u p`, `u` injective) in a store whose tapes are all
at most `M` and whose tapes `u j` are at most `bnd ρ σ j`, its tapes `u j` end at most
`bnd ρ σ' j` and it runs within `(2 M + 3) · pEval ρ w` steps, for all values `ρ` of the
variables. Summaries compose (`Sound.seq`, `Sound.ifBit`, `Sound.loop`, `Sound.call`), so a
subprogram is analysed once and its summary reused wherever it is placed. -/

/-- The value of the variable `0`, the **top** size: it bounds every tape, and a summary charges
`2 · top + 3` steps per primitive. -/
def top (ρ : List ℕ) : ℕ := ρ.headD 0

/-- The polynomial `X₀`, standing for the top size. -/
def pTop : Poly := [([1], 1)]

/-- `p` is literally `pTop`. -/
def isTop : Poly → Bool
  | [([1], 1)] => true
  | _ => false

theorem pEval_of_isTop {p : Poly} (h : isTop p = true) (ρ : List ℕ) : pEval ρ p = top ρ := by
  match p, h with
  | [([1], 1)], _ => simp [pEval, mEval, mEval_nil, top]

/-- A sound summary of a program: abstract input store, abstract output store, sweeps. -/
def Sound {n : ℕ} (p : Prog n) (σ σ' : Asg) (w : Poly) : Prop :=
  ∀ (ρ : List ℕ) (k : ℕ) (u : Fin n → Fin k), Function.Injective u → ∀ ℓ : Fin k → ℕ,
    (∀ j, ℓ (u j) ≤ bnd ρ σ j) → (∀ t, ℓ t ≤ top ρ) →
      (∀ j, lenBoundT (map u p) ℓ (u j) ≤ bnd ρ σ' j) ∧
        timeBoundT (map u p) ℓ ≤ (2 * top ρ + 3) * pEval ρ w

variable {n : ℕ}

theorem Sound.prim {p : Prim n} {σ σ' : Asg} (h : absPrim p σ = some σ') :
    Sound (.prim p) σ σ' (pC 1) := by
  intro ρ k u hu ℓ hℓ hM
  refine ⟨fun j => ?_, ?_⟩
  · show (p.map u).lenT ℓ (u j) ≤ _
    rw [lenT_map hu]
    exact absPrim_sound ρ p h (ℓ := ℓ ∘ u) hℓ j
  · have := supB_le_const hM
    show 2 * (supB ℓ + (p.map u).pad) + 3 ≤ _
    rw [Prim.pad_map, Prim.pad_of_noGrowB (noGrowB_of_absPrim h), pEval_pC]
    omega

theorem Sound.seq {p q : Prog n} (hp : p.NoGrow) {σ σ₁ σ₂ : Asg} {w₁ w₂ : Poly}
    (h₁ : Sound p σ σ₁ w₁) (h₂ : Sound q σ₁ σ₂ w₂) : Sound (.seq p q) σ σ₂ (pAdd w₁ w₂) := by
  intro ρ k u hu ℓ hℓ hM
  obtain ⟨a₁, b₁⟩ := h₁ ρ k u hu ℓ hℓ hM
  obtain ⟨a₂, b₂⟩ := h₂ ρ k u hu _ a₁ (lenBoundT_le_const _ (hp.map u) hM)
  refine ⟨a₂, ?_⟩
  show timeBoundT (map u p) ℓ + timeBoundT (map u q) (lenBoundT (map u p) ℓ) ≤ _
  rw [pEval_pAdd, Nat.mul_add]
  omega

theorem Sound.branch {p q : Prog n} {σ σ₁ σ₂ : Asg} {w₁ w₂ : Poly}
    (h₁ : Sound p σ σ₁ w₁) (h₂ : Sound q σ σ₂ w₂) (ρ : List ℕ) (k : ℕ) (u : Fin n → Fin k)
    (hu : Function.Injective u) (ℓ : Fin k → ℕ) (hℓ : ∀ j, ℓ (u j) ≤ bnd ρ σ j)
    (hM : ∀ t, ℓ t ≤ top ρ) :
    (∀ j, max (lenBoundT (map u p) ℓ (u j)) (lenBoundT (map u q) ℓ (u j)) ≤
      bnd ρ (aJoin σ₁ σ₂) j) ∧
      max (timeBoundT (map u p) ℓ) (timeBoundT (map u q) ℓ) + 1 ≤
        (2 * top ρ + 3) * pEval ρ (pAdd (pJoin w₁ w₂) (pC 1)) := by
  obtain ⟨a₁, b₁⟩ := h₁ ρ k u hu ℓ hℓ hM
  obtain ⟨a₂, b₂⟩ := h₂ ρ k u hu ℓ hℓ hM
  obtain ⟨hj₁, hj₂⟩ := le_pEval_pJoin ρ w₁ w₂
  refine ⟨fun j => max_le ((a₁ j).trans (le_aJoin ρ σ₁ σ₂ j).1)
    ((a₂ j).trans (le_aJoin ρ σ₁ σ₂ j).2), ?_⟩
  simp only [pEval_pAdd, pEval_pC, Nat.mul_add, Nat.mul_one]
  have := Nat.mul_le_mul_left (2 * (top ρ) + 3) hj₁
  have := Nat.mul_le_mul_left (2 * (top ρ) + 3) hj₂
  omega

theorem Sound.ifBit {p q : Prog n} (i : Fin n) {σ σ₁ σ₂ : Asg} {w₁ w₂ : Poly}
    (h₁ : Sound p σ σ₁ w₁) (h₂ : Sound q σ σ₂ w₂) :
    Sound (.ifBit i p q) σ (aJoin σ₁ σ₂) (pAdd (pJoin w₁ w₂) (pC 1)) :=
  fun ρ k u hu ℓ hℓ hM => Sound.branch h₁ h₂ ρ k u hu ℓ hℓ hM

theorem Sound.ifBlank {p q : Prog n} (i : Fin n) {σ σ₁ σ₂ : Asg} {w₁ w₂ : Poly}
    (h₁ : Sound p σ σ₁ w₁) (h₂ : Sound q σ σ₂ w₂) :
    Sound (.ifBlank i p q) σ (aJoin σ₁ σ₂) (pAdd (pJoin w₁ w₂) (pC 1)) :=
  fun ρ k u hu ℓ hℓ hM => Sound.branch h₁ h₂ ρ k u hu ℓ hℓ hM

/-- **A loop analysed at an invariant abstract store** `σi` (above the entry store `σ`, and above
one round from it) is charged the entry bound of its counter. -/
theorem Sound.loop {body : Prog n} (i : Fin n) (hb : body.NoGrow) {σ σi σb : Asg} {wb : Poly}
    (h : Sound body σi σb wb) (hle : aLe σb σi = true)
    (hge : ∀ ρ (j : ℕ), pEval ρ (aGet σ j) ≤ pEval ρ (aGet σi j)) :
    Sound (.loop i body) σ σi (pAdd (pMul (aGet σ i.val) (pAdd wb (pC 2))) (pC 1)) := by
  intro ρ k u hu ℓ hℓ hM
  set g : Fin n → ℕ := fun j => min (bnd ρ σi j) (top ρ)
  set ℓ' : Fin k → ℕ := Function.extend u g ℓ
  have hu' : ∀ j, ℓ' (u j) = g j := fun j => hu.extend_apply g ℓ j
  have ho : ∀ t, (∀ j, u j ≠ t) → ℓ' t = ℓ t := fun t ht =>
    Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => ht j hj
  have h0 : ℓ ≤ ℓ' := by
    intro t
    by_cases ht : ∃ j, u j = t
    · obtain ⟨j, rfl⟩ := ht
      rw [hu']; exact le_min ((hℓ j).trans (hge ρ j)) (hM _)
    · push Not at ht; rw [ho t ht]
  have hℓ'M : ∀ t, ℓ' t ≤ (top ρ) := by
    intro t
    by_cases ht : ∃ j, u j = t
    · obtain ⟨j, rfl⟩ := ht; rw [hu']; exact min_le_right _ _
    · push Not at ht; rw [ho t ht]; exact hM t
  obtain ⟨hlb, htb⟩ := h ρ k u hu ℓ' (fun j => by rw [hu']; exact min_le_left _ _) hℓ'M
  have hb' : (map u body).NoGrow := hb.map u
  have hinv : loopStepT (u i) (map u body) ℓ' ≤ ℓ' := by
    intro t
    by_cases ht : ∃ j, u j = t
    · obtain ⟨j, rfl⟩ := ht
      rw [hu']
      refine le_min ?_ (lenBoundT_le_const _ hb'
        (fun t => (tailB_le (u i) ℓ' t).trans (hℓ'M t)) _)
      exact ((lenBoundT_mono _ (tailB_le (u i) ℓ')) (u j)).trans
        ((hlb j).trans (aLe_spec ρ hle j))
    · push Not at ht
      rw [loopStepT, lenBoundT_of_preserves t _ (preserves_map_of_not_mem ht _), tailB,
        Function.update_of_ne (ht i).symm]
  refine ⟨fun j => ((lenBoundT_loop_le_of_inv (u i) _ h0 hinv) (u j)).trans
    (by rw [hu']; exact min_le_left _ _), ?_⟩
  have ht := timeBoundT_loop_le_of_inv (u i) _ h0 hinv
  have hr := roundTimeT_le (map u body) (u i) ℓ'
  have hs := supB_le_const hℓ'M
  have hi : ℓ (u i) ≤ pEval ρ (aGet σ i.val) := hℓ i
  simp only [pEval_pAdd, pEval_pMul, pEval_pC]
  set A := pEval ρ (aGet σ i.val)
  set W := pEval ρ wb
  set c := 2 * (top ρ) + 3
  have hround : roundTimeT (timeBoundT (map u body)) (u i) ℓ' + 1 ≤ c * (W + 2) := by
    have : 2 * supB ℓ' + 3 ≤ c := by omega
    rw [Nat.mul_add]; omega
  calc timeBoundT (map u (.loop i body)) ℓ
      ≤ ℓ (u i) * (roundTimeT (timeBoundT (map u body)) (u i) ℓ' + 1) + 2 := ht
    _ ≤ A * (c * (W + 2)) + c := Nat.add_le_add (Nat.mul_le_mul hi hround) (by omega)
    _ = c * (A * (W + 2) + 1) := by ring

/-- Write the abstract outputs `τ' j` on the tapes `v j`. -/
def setMany {m : ℕ} (v : Fin m → Fin n) (τ' : Asg) : Asg → List (Fin m) → Asg
  | σ, [] => σ
  | σ, j :: js => setMany v τ' (aSet σ (v j).val (aGet τ' j.val)) js

theorem aGet_setMany_of_not_mem {m : ℕ} (v : Fin m → Fin n) (τ' : Asg) (t : ℕ) :
    ∀ (js : List (Fin m)) (σ : Asg), (∀ j ∈ js, (v j).val ≠ t) →
      aGet (setMany v τ' σ js) t = aGet σ t
  | [], σ, _ => rfl
  | j :: js, σ, h => by
    rw [setMany, aGet_setMany_of_not_mem v τ' t js _ (fun j' hj' => h j' (by simp [hj'])),
      aGet_aSet, if_neg (Ne.symm (h j (by simp)))]

theorem aGet_setMany_of_mem {m : ℕ} {v : Fin m → Fin n} (hv : Function.Injective v)
    (τ' : Asg) : ∀ (js : List (Fin m)) (σ : Asg) (j : Fin m), j ∈ js →
      aGet (setMany v τ' σ js) (v j).val = aGet τ' j.val
  | [], σ, j, h => by simp at h
  | a :: js, σ, j, h => by
    rw [setMany]
    by_cases hj : j ∈ js
    · exact aGet_setMany_of_mem hv τ' js _ j hj
    · have hja : j = a := by simpa [hj] using h
      subst hja
      rw [aGet_setMany_of_not_mem v τ' _ js _ (fun j' hj' he => hj
        (by rw [← hv (Fin.val_injective he)]; exact hj')), aGet_aSet, if_pos rfl]

/-- **A placed subprogram with a sound summary.** -/
theorem Sound.call {m : ℕ} {v : Fin m → Fin n} (hv : Function.Injective v) {p : Prog m}
    {τ τ' : Asg} {w : Poly} (hS : Sound p τ τ' w) {σ : Asg}
    (hin : ∀ j : Fin m,
      (pLe (aGet σ (v j).val) (aGet τ j.val) || isTop (aGet τ j.val)) = true) :
    Sound (map v p) σ (setMany v τ' σ (List.finRange m)) w := by
  intro ρ k u hu ℓ hℓ hM
  have hin' : ∀ j, ℓ ((u ∘ v) j) ≤ bnd ρ τ j := by
    intro j
    rcases Bool.or_eq_true_iff.mp (hin j) with h | h
    · exact (hℓ (v j)).trans (pEval_le_of_pLe ρ h)
    · exact (hM _).trans (pEval_of_isTop h ρ).ge
  rw [Prog.map_map]
  have huv : Function.Injective (u ∘ v) := hu.comp hv
  obtain ⟨a, b⟩ := hS ρ k (u ∘ v) huv ℓ (fun j => hin' j) hM
  refine ⟨fun t => ?_, b⟩
  by_cases ht : ∃ j, v j = t
  · obtain ⟨j, rfl⟩ := ht
    show _ ≤ pEval ρ (aGet (setMany v τ' σ (List.finRange m)) (v j).val)
    rw [aGet_setMany_of_mem hv τ' _ σ j (List.mem_finRange j)]
    exact a j
  · push Not at ht
    rw [lenBoundT_of_preserves (u t) _ (preserves_map_of_not_mem (u := u ∘ v)
      (fun j h => ht j (hu h)) p) ℓ]
    refine (hℓ t).trans (le_of_eq ?_)
    show pEval ρ (aGet σ t.val) = pEval ρ (aGet (setMany v τ' σ (List.finRange m)) t.val)
    rw [aGet_setMany_of_not_mem v τ' _ _ σ (fun j _ he => ht j (Fin.val_injective he))]

theorem noGrow_of_absRun (fuel : ℕ) : ∀ (p : Prog n) {σ σ' : Asg} {w : Poly},
    absRun fuel p σ = some (σ', w) → p.NoGrow := by
  intro p
  induction p with
  | prim p =>
    intro σ σ' w h
    rcases hq : absPrim p σ with _ | σ₁
    · simp [absRun, hq] at h
    · exact noGrowB_of_absPrim hq
  | coin i => intro σ σ' w h; simp [absRun] at h
  | seq p q ihp ihq =>
    intro σ σ' w h
    rcases h₁ : absRun fuel p σ with _ | ⟨σ₁, w₁⟩
    · simp [absRun, h₁] at h
    rcases h₂ : absRun fuel q σ₁ with _ | ⟨σ₂, w₂⟩
    · simp [absRun, h₁, h₂] at h
    show (p.noGrowB && q.noGrowB) = true
    rw [ihp h₁, ihq h₂]; rfl
  | ifBlank i p q ihp ihq | ifBit i p q ihp ihq =>
    intro σ σ' w h
    rcases h₁ : absRun fuel p σ with _ | ⟨σ₁, w₁⟩
    · simp [absRun, h₁] at h
    rcases h₂ : absRun fuel q σ with _ | ⟨σ₂, w₂⟩
    · simp [absRun, h₁, h₂] at h
    show (p.noGrowB && q.noGrowB) = true
    rw [ihp h₁, ihq h₂]; rfl
  | loop i body ih =>
    intro σ σ' w h
    rcases hf : fixIter (absRun fuel body) fuel σ with _ | ⟨σi, σb, wb⟩
    · simp [absRun, hf] at h
    exact ih (fixIter_spec [] _ fuel σ σi σb wb hf).1

/-- **Soundness of the abstract interpreter**: its result is a sound summary. -/
theorem absRun_sound (fuel : ℕ) : ∀ (p : Prog n) {σ σ' : Asg} {w : Poly},
    absRun fuel p σ = some (σ', w) → Sound p σ σ' w := by
  intro p
  induction p with
  | prim p =>
    intro σ σ' w h
    rcases hq : absPrim p σ with _ | σ₁
    · simp [absRun, hq] at h
    · simp only [absRun, hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Sound.prim hq
  | coin i => intro σ σ' w h; simp [absRun] at h
  | seq p q ihp ihq =>
    intro σ σ' w h
    rcases h₁ : absRun fuel p σ with _ | ⟨σ₁, w₁⟩
    · simp [absRun, h₁] at h
    rcases h₂ : absRun fuel q σ₁ with _ | ⟨σ₂, w₂⟩
    · simp [absRun, h₁, h₂] at h
    simp only [absRun, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Sound.seq (noGrow_of_absRun fuel p h₁) (ihp h₁) (ihq h₂)
  | ifBlank i p q ihp ihq =>
    intro σ σ' w h
    rcases h₁ : absRun fuel p σ with _ | ⟨σ₁, w₁⟩
    · simp [absRun, h₁] at h
    rcases h₂ : absRun fuel q σ with _ | ⟨σ₂, w₂⟩
    · simp [absRun, h₁, h₂] at h
    simp only [absRun, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Sound.ifBlank i (ihp h₁) (ihq h₂)
  | ifBit i p q ihp ihq =>
    intro σ σ' w h
    rcases h₁ : absRun fuel p σ with _ | ⟨σ₁, w₁⟩
    · simp [absRun, h₁] at h
    rcases h₂ : absRun fuel q σ with _ | ⟨σ₂, w₂⟩
    · simp [absRun, h₁, h₂] at h
    simp only [absRun, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Sound.ifBit i (ihp h₁) (ihq h₂)
  | loop i body ih =>
    intro σ σ' w h
    rcases hf : fixIter (absRun fuel body) fuel σ with _ | ⟨σi, σb, wb⟩
    · simp [absRun, hf] at h
    simp only [absRun, hf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hrun, hle, -⟩ := fixIter_spec [] _ fuel σ σi σb wb hf
    exact Sound.loop i (noGrow_of_absRun fuel body hrun) (ih hrun) hle
      (fun ρ j => (fixIter_spec ρ _ fuel σ σi σb wb hf).2.2 j)

/-! ### Programs with summarised subprograms

An `Ast` is a program in which some placed subprograms `map v p` are replaced by a summary of `p`
(`call`), so the interpreter does not re-analyse them: a large program is certified bottom-up, one
definition at a time. -/

/-- Programs with summarised calls. -/
inductive Ast (n : ℕ) : Type
  /-- A plain program, analysed by `absRun`. -/
  | prog (p : Prog n) : Ast n
  /-- The program `map v p`, with a sound summary of `p`. -/
  | call {m : ℕ} (v : Fin m → Fin n) (p : Prog m) (τ τ' : Asg) (w : Poly)
      (hv : Function.Injective v) (hp : p.NoGrow) (hS : Sound p τ τ' w) : Ast n
  | seq (a b : Ast n) : Ast n
  | ifBit (i : Fin n) (a b : Ast n) : Ast n
  | loop (i : Fin n) (a : Ast n) : Ast n

namespace Ast

/-- The program an `Ast` stands for. -/
def toProg : Ast n → Prog n
  | prog p => p
  | call v p _ _ _ _ _ _ => map v p
  | seq a b => .seq a.toProg b.toProg
  | ifBit i a b => .ifBit i a.toProg b.toProg
  | loop i a => .loop i a.toProg

/-- The abstract interpreter on an `Ast`. -/
def abs (fuel : ℕ) : Ast n → Asg → Option (Asg × Poly)
  | prog p, σ => absRun fuel p σ
  | @call _ m v _ τ τ' w _ _ _, σ =>
    if (List.finRange m).all fun j => pLe (aGet σ (v j).val) (aGet τ j.val) || isTop (aGet τ j.val)
    then
      some (setMany v τ' σ (List.finRange m), w)
    else none
  | seq a b, σ => match abs fuel a σ with
    | none => none
    | some (σ₁, w₁) => match abs fuel b σ₁ with
      | none => none
      | some (σ₂, w₂) => some (σ₂, pAdd w₁ w₂)
  | ifBit _ a b, σ => match abs fuel a σ, abs fuel b σ with
    | some (σ₁, w₁), some (σ₂, w₂) => some (aJoin σ₁ σ₂, pAdd (pJoin w₁ w₂) (pC 1))
    | _, _ => none
  | loop i a, σ => match fixIter (abs fuel a) fuel σ with
    | none => none
    | some (σi, _, wb) => some (σi, pAdd (pMul (aGet σ i.val) (pAdd wb (pC 2))) (pC 1))
  termination_by structural a => a

/-- **Soundness of the interpreter on an `Ast`.** -/
theorem abs_sound (fuel : ℕ) : ∀ (a : Ast n) {σ σ' : Asg} {w : Poly},
    abs fuel a σ = some (σ', w) → a.toProg.NoGrow ∧ Sound a.toProg σ σ' w := by
  intro a
  induction a with
  | prog p =>
    intro σ σ' w h
    exact ⟨noGrow_of_absRun fuel p h, absRun_sound fuel p h⟩
  | call v p τ τ' w hv hp hS =>
    intro σ σ' w' h
    simp only [abs] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hp.map v, Sound.call hv hS fun j => List.all_eq_true.mp hc j (List.mem_finRange j)⟩
  | seq a b iha ihb =>
    intro σ σ' w h
    rcases h₁ : abs fuel a σ with _ | ⟨σ₁, w₁⟩
    · simp [abs, h₁] at h
    rcases h₂ : abs fuel b σ₁ with _ | ⟨σ₂, w₂⟩
    · simp [abs, h₁, h₂] at h
    simp only [abs, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨ga, sa⟩ := iha h₁
    obtain ⟨gb, sb⟩ := ihb h₂
    refine ⟨?_, Sound.seq ga sa sb⟩
    show (a.toProg.noGrowB && b.toProg.noGrowB) = true
    rw [ga, gb]; rfl
  | ifBit i a b iha ihb =>
    intro σ σ' w h
    rcases h₁ : abs fuel a σ with _ | ⟨σ₁, w₁⟩
    · simp [abs, h₁] at h
    rcases h₂ : abs fuel b σ with _ | ⟨σ₂, w₂⟩
    · simp [abs, h₁, h₂] at h
    simp only [abs, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨ga, sa⟩ := iha h₁
    obtain ⟨gb, sb⟩ := ihb h₂
    refine ⟨?_, Sound.ifBit i sa sb⟩
    show (a.toProg.noGrowB && b.toProg.noGrowB) = true
    rw [ga, gb]; rfl
  | loop i a ih =>
    intro σ σ' w h
    rcases hf : fixIter (abs fuel a) fuel σ with _ | ⟨σi, σb, wb⟩
    · simp [abs, hf] at h
    simp only [abs, hf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hrun, hle, -⟩ := fixIter_spec [] _ fuel σ σi σb wb hf
    obtain ⟨ga, sa⟩ := ih hrun
    exact ⟨ga, Sound.loop i ga sa hle fun ρ j => (fixIter_spec ρ _ fuel σ σi σb wb hf).2.2 j⟩

end Ast

/-! ### Using a summary -/

/-- **The per-tape bounds from a summary**, for the program on its own tapes: from any per-tape
bound `ℓ ≤ bnd ρ σ` with entries at most `top ρ` (the value of the variable `0`). -/
theorem Sound.bounds {p : Prog n} {σ σ' : Asg} {w : Poly} (h : Sound p σ σ' w) (ρ : List ℕ)
    {ℓ : Fin n → ℕ} (hℓ : ℓ ≤ bnd ρ σ) (hM : ∀ t, ℓ t ≤ top ρ) :
    lenBoundT p ℓ ≤ bnd ρ σ' ∧ timeBoundT p ℓ ≤ (2 * top ρ + 3) * pEval ρ w := by
  have := h ρ n id Function.injective_id ℓ hℓ hM
  rw [Prog.map_id] at this
  exact ⟨this.1, this.2⟩

/-- **A summarised program framed inside a larger store** (`XProg.frame`): its cost depends only on
the framed tapes, which must fit `bnd ρ σ` and be at most `top ρ`; the other tapes may be
arbitrarily long, and keep their bounds. -/
theorem Sound.frame {p : Prog n} {σ σ' : Asg} {w : Poly} (h : Sound p σ σ' w) (ρ : List ℕ)
    {k : ℕ} (e : Fin n ↪ Fin k) {ℓ : Fin k → ℕ} (hℓ : ∀ j, ℓ (e j) ≤ bnd ρ σ j)
    (hM : ∀ j, ℓ (e j) ≤ top ρ) :
    XProg.timeBoundT (.frame e (.prog p)) ℓ ≤ (2 * top ρ + 3) * pEval ρ w ∧
      XProg.lenBoundT (.frame e (.prog p)) ℓ ≤ embedF e ℓ (bnd ρ σ') := by
  obtain ⟨h1, h2⟩ := h.bounds ρ (ℓ := fun j => ℓ (e j)) hℓ hM
  exact ⟨h2, embedF_mono e le_rfl h1⟩

end Sym

end SigabaNeo.Tape
