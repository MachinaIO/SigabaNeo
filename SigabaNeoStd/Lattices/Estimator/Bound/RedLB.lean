import SigabaNeoStd.Lattices.Estimator.Bound.Scan

/-!
# A lower bound on the reduction cost

`RC.MATZOV(β, d)` costs at least `redLB β`, the cost of one sieve in dimension `β − d4f(β)` with
the progressive overhead: the `LLL` term and the `log₂ (d − β)` repetitions are dropped. Every
lattice attack pays `RC.MATZOV(β, d)` for its block size `β`, so a block size with
`redLB β ≥ k` gives cost at least `k`.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx Reduction

/-- `2 log₂ C + 0.296 (β − d4f(β)) + 20.4`. -/
def Reduction.redLB (β : ℕ) : Fx := log2C + log2C + mul NN_A (ofInt β - d4f β) + NN_B

theorem log2_ofInt_nonneg {x : ℤ} (hx : 1 ≤ x) : 0 ≤ log2 (ofInt x) := by
  apply log2_nonneg; unfold ofInt; have := ONE_pos; nlinarith

theorem Reduction.redLB_le {β : ℕ} (hβ : 20 ≤ β) (d : ℕ) : redLB β ≤ matzovBits β d := by
  unfold matzovBits redLB
  have h20 : ¬ β < 20 := by omega
  simp only [h20, ↓reduceIte]
  refine le_trans ?_ (le_log2Add_right _ _)
  have := log2_ofInt_nonneg (x := max ((d : ℤ) - β) 1) (le_max_right _ _)
  linarith

theorem NumDual.shortBits_ge {b d : ℕ} {count r : Fx} (h : NumDual.shortBits b d count = some r) :
    matzovBits b d ≤ r := by
  unfold NumDual.shortBits at h
  simp only at h
  split at h
  · cases h; exact le_rfl
  · split at h
    · exact absurd h (by simp)
    · injection h with h
      rw [← h]
      have h1 := le_log2Add_left (matzovBits b d) (log2C + NN_A * (NumDual.sieveDim b d : ℤ) + NN_B)
      have h2 := log2Nat_nonneg ((max 1 ((ceil (exp2 count) + floor (exp2 (ofRat 2075 10000 *
        (NumDual.sieveDim b d : ℤ))) - 1) / floor (exp2 (ofRat 2075 10000 *
        (NumDual.sieveDim b d : ℤ))))).toNat)
      linarith

/-! ### uSVP and dual: evaluate below `β₀`, `redLB` above -/

/-- The per-block-size check of uSVP: the reduction bound, or the candidate itself. -/
def Usvp.check (k l2q : Fx) (p : LWEParams) (β : ℕ) : Bool :=
  decide (k ≤ redLB β) || costGeB k (Usvp.costGsaQ l2q β p.normalize (Usvp.embedM p.normalize))

theorem Usvp.costGsaQ_ge_redLB {l2q : Fx} {β : ℕ} (hβ : 20 ≤ β) {p : LWEParams} {m : Option ℕ}
    {x : Fx} (h : Usvp.costGsaQ l2q β p m = some x) : redLB β ≤ x := by
  unfold Usvp.costGsaQ at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · split_ifs at h <;> (injection h with h; rw [← h]; exact redLB_le hβ _)

theorem Usvp.check_spec {k l2q : Fx} {p : LWEParams} {β : ℕ} (hβ : 20 ≤ β)
    (h : Usvp.check k l2q p β = true) :
    CostGe k (Usvp.costGsaQ l2q β p.normalize (Usvp.embedM p.normalize)) := by
  unfold Usvp.check at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · intro x hx; exact (of_decide_eq_true h).trans (costGsaQ_ge_redLB hβ hx)
  · exact costGe_iff.mpr h

/-- The candidate of the dual attack at block size `b`, with `lq = log₂ q`. -/
def Dual.cand (lq : Fx) (p : LWEParams) (b : ℕ) : Cost :=
  Dual.candidate p.normalize (log2 p.normalize.Xs.stddev)
    (log2 p.normalize.Xs.stddev + lq - log2 p.normalize.Xe.stddev) b

/-- The per-block-size check of the dual attack. -/
def Dual.check (k lq : Fx) (p : LWEParams) (b : ℕ) : Bool :=
  decide (k ≤ redLB b) || costGeB k (Dual.cand lq p b)

theorem Dual.candidate_ge_redLB {p : LWEParams} {xs c : Fx} {b : ℕ} (hb : 20 ≤ b) {x : Fx}
    (h : Dual.candidate p xs c b = some x) : redLB b ≤ x := by
  have key : ∀ (d : ℕ) (o : Option Fx), (o.bind fun cnt =>
      (NumDual.shortBits b d cnt).bind fun r => some (log2Add r cnt)) = some x → redLB b ≤ x := by
    intro d o ho
    obtain ⟨cnt, -, ho⟩ := Option.bind_eq_some_iff.mp ho
    obtain ⟨r, hr, hx⟩ := Option.bind_eq_some_iff.mp ho
    injection hx with hx
    rw [← hx]
    exact (redLB_le hb _).trans ((NumDual.shortBits_ge hr).trans (le_log2Add_left _ _))
  unfold Dual.candidate at h
  dsimp only at h
  split_ifs at h <;> exact key _ _ h

theorem Dual.check_spec {k lq : Fx} {p : LWEParams} {b : ℕ} (hb : 20 ≤ b)
    (h : Dual.check k lq p b = true) : CostGe k (Dual.cand lq p b) := by
  unfold Dual.check at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · intro x hx; exact (of_decide_eq_true h).trans (candidate_ge_redLB hb hx)
  · exact costGe_iff.mpr h

end SigabaNeo.Lattices.Estimator
