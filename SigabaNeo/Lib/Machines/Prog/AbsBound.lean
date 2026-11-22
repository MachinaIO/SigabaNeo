import SigabaNeo.Lib.Machines.Prog.BoundsT
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

/-- Equality of monomials (up to trailing zero exponents). -/
def mBeq : Mono → Mono → Bool
  | [], [] => true
  | [], b :: bs => b.beq 0 && mBeq [] bs
  | a :: as, [] => a.beq 0 && mBeq as []
  | a :: as, b :: bs => a.beq b && mBeq as bs

/-- The product of monomials. -/
def mMul : Mono → Mono → Mono
  | [], m => m
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: mMul as bs

theorem mEval_nil (ρ : List ℕ) : mEval ρ [] = 1 := by cases ρ <;> rfl

theorem mEval_of_mBeq : ∀ {m m' : Mono}, mBeq m m' = true → ∀ ρ, mEval ρ m = mEval ρ m'
  | [], [], _, _ => rfl
  | [], b :: bs, h, ρ => by
    simp only [mBeq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1]
    simp only [mEval, pow_zero, one_mul]
    rw [← mEval_of_mBeq h.2, mEval_nil]
  | a :: as, [], h, ρ => by
    simp only [mBeq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1]
    simp only [mEval, pow_zero, one_mul]
    rw [mEval_of_mBeq h.2, mEval_nil]
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

/-- **Soundness of the abstract interpreter.** For a program of the fragment, from every per-tape
bound `ℓ ≤ bnd ρ σ` with entries at most `M`: the bound afterwards is at most `bnd ρ σ'`, and the
time at most `(2 M + 3)` times the sweeps `w`. -/
theorem absRun_sound (ρ : List ℕ) (M fuel : ℕ) :
    ∀ (p : Prog k), p.NoGrow → ∀ (σ σ' : Asg) (w : Poly), absRun fuel p σ = some (σ', w) →
      ∀ ℓ : Fin k → ℕ, ℓ ≤ bnd ρ σ → (∀ t, ℓ t ≤ M) →
        lenBoundT p ℓ ≤ bnd ρ σ' ∧ timeBoundT p ℓ ≤ (2 * M + 3) * pEval ρ w := by
  intro p
  induction p with
  | prim p =>
    intro hp σ σ' w h ℓ hℓ hM
    rcases hq : absPrim p σ with _ | σ₁
    · simp [absRun, hq] at h
    · simp only [absRun, hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨absPrim_sound ρ p hq hℓ, ?_⟩
      have := supB_le_const hM
      simp only [timeBoundT, Prim.pad_of_noGrowB (p := p) hp, pEval_pC]
      omega
  | coin i => intro hp; exact absurd hp (by simp [NoGrow, noGrowB])
  | seq p q ihp ihq =>
    intro hp σ σ' w h ℓ hℓ hM
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at hp
    rcases h₁ : absRun fuel p σ with _ | ⟨σ₁, w₁⟩
    · simp [absRun, h₁] at h
    rcases h₂ : absRun fuel q σ₁ with _ | ⟨σ₂, w₂⟩
    · simp [absRun, h₁, h₂] at h
    simp only [absRun, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hl₁, ht₁⟩ := ihp hp.1 σ σ₁ w₁ h₁ ℓ hℓ hM
    obtain ⟨hl₂, ht₂⟩ := ihq hp.2 σ₁ _ w₂ h₂ _ hl₁ (lenBoundT_le_const p hp.1 hM)
    refine ⟨hl₂, ?_⟩
    rw [timeBoundT_seq, pEval_pAdd, Nat.mul_add]
    omega
  | ifBlank i p q ihp ihq | ifBit i p q ihp ihq =>
    intro hp σ σ' w h ℓ hℓ hM
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at hp
    rcases h₁ : absRun fuel p σ with _ | ⟨σ₁, w₁⟩
    · simp [absRun, h₁] at h
    rcases h₂ : absRun fuel q σ with _ | ⟨σ₂, w₂⟩
    · simp [absRun, h₁, h₂] at h
    simp only [absRun, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hl₁, ht₁⟩ := ihp hp.1 σ σ₁ w₁ h₁ ℓ hℓ hM
    obtain ⟨hl₂, ht₂⟩ := ihq hp.2 σ σ₂ w₂ h₂ ℓ hℓ hM
    obtain ⟨hj₁, hj₂⟩ := le_pEval_pJoin ρ w₁ w₂
    refine ⟨fun t => max_le ((hl₁ t).trans (le_aJoin ρ σ₁ σ₂ t).1)
      ((hl₂ t).trans (le_aJoin ρ σ₁ σ₂ t).2), ?_⟩
    simp only [timeBoundT, pEval_pAdd, pEval_pC, Nat.mul_add, Nat.mul_one]
    have := Nat.mul_le_mul_left (2 * M + 3) hj₁
    have := Nat.mul_le_mul_left (2 * M + 3) hj₂
    omega
  | loop i body ih =>
    intro hp σ σ' w h ℓ hℓ hM
    have hb : body.NoGrow := hp
    rcases hf : fixIter (absRun fuel body) fuel σ with _ | ⟨σi, σb, wb⟩
    · simp [absRun, hf] at h
    simp only [absRun, hf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hrun, hle, hge⟩ := fixIter_spec ρ _ fuel σ σi σb wb hf
    set ℓ' : Fin k → ℕ := fun t => min (bnd ρ σi t) M with hℓ'
    have h0 : ℓ ≤ ℓ' := fun t => le_min ((hℓ t).trans (hge t)) (hM t)
    have hℓ'M : ∀ t, ℓ' t ≤ M := fun t => min_le_right _ _
    obtain ⟨hlb, htb⟩ := ih hb σi σb wb hrun ℓ' (fun t => min_le_left _ _) hℓ'M
    have hinv : loopStepT i body ℓ' ≤ ℓ' := by
      intro t
      refine le_min ?_ (lenBoundT_le_const body hb (fun t => (tailB_le i ℓ' t).trans (hℓ'M t)) t)
      exact ((lenBoundT_mono body (tailB_le i ℓ')) t).trans ((hlb t).trans (aLe_spec ρ hle t))
    refine ⟨(lenBoundT_loop_le_of_inv i body h0 hinv).trans fun t => min_le_left _ _, ?_⟩
    have ht := timeBoundT_loop_le_of_inv i body h0 hinv
    have hr := roundTimeT_le body i ℓ'
    have hs := supB_le_const hℓ'M
    have hi : ℓ i ≤ pEval ρ (aGet σ i.val) := hℓ i
    simp only [pEval_pAdd, pEval_pMul, pEval_pC]
    set A := pEval ρ (aGet σ i.val)
    set W := pEval ρ wb
    set c := 2 * M + 3
    have hround : roundTimeT (timeBoundT body) i ℓ' + 1 ≤ c * (W + 2) := by
      have : 2 * supB ℓ' + 3 ≤ c := by omega
      rw [Nat.mul_add]; omega
    calc timeBoundT (loop i body) ℓ ≤ ℓ i * (roundTimeT (timeBoundT body) i ℓ' + 1) + 2 := ht
      _ ≤ A * (c * (W + 2)) + c := Nat.add_le_add (Nat.mul_le_mul hi hround) (by omega)
      _ = c * (A * (W + 2) + 1) := by ring

/-- **The per-tape bounds from the abstract interpreter**, at the abstract input store itself
(all of whose entries are at most `M`). -/
theorem bounds_of_absRun (ρ : List ℕ) (fuel : ℕ) (p : Prog k) (hp : p.NoGrow) {σ σ' : Asg}
    {w : Poly} (h : absRun fuel p σ = some (σ', w)) {M : ℕ} (hM : ∀ t : Fin k, bnd ρ σ t ≤ M) :
    lenBoundT p (bnd ρ σ) ≤ bnd ρ σ' ∧ timeBoundT p (bnd ρ σ) ≤ (2 * M + 3) * pEval ρ w :=
  absRun_sound ρ M fuel p hp σ σ' w h _ le_rfl hM

end Sym

end SigabaNeo.Tape
