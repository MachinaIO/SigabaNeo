module

public import SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlock

/-! # Candidate verification on reserved rows (PROOF_GAP Wall 1, Parts 131/132)

A candidate residue `c ≠ s` (mod `q`), fixed independently of `v` reserved LWE rows, passes the
residual test on all of them (every residual `⟨a, s⟩ + e − ⟨a, c⟩` has centered representative in
`[−3, 3]`) with probability exactly `(7/q)^v` over the uniform reserved design, for every value of
the reserved errors (`verify_exact`), hence also over CBD errors (`verify_cbd`). A union bound
covers a list of candidates (`verify_union`, `verify_union_avg`). -/

public section
namespace SigabaNeo.Wall1.MultiBlock
open SigabaNeo.SampleDeletion

variable {n q : ℕ}

/-- The residual test: the residue has a representative in `[−3, 3]` (for `q > 6` this is the
centered representative). -/
@[expose] def accept (x : ZMod q) : Prop := ∃ t : ℤ, -3 ≤ t ∧ t ≤ 3 ∧ (t : ZMod q) = x

/-- The accepted residues. -/
@[expose] def acceptSet (q : ℕ) : Finset (ZMod q) := (Finset.Icc (-3 : ℤ) 3).image (Int.cast)

theorem accept_iff (x : ZMod q) : accept x ↔ x ∈ acceptSet q := by
  simp [accept, acceptSet, and_assoc]

noncomputable instance : DecidablePred (accept (q := q)) := fun _ ↦ Classical.dec _

/-- For `q > 6` exactly seven residues are accepted. -/
theorem acceptSet_card (hq : 6 < q) : (acceptSet q).card = 7 := by
  unfold acceptSet
  rw [Finset.card_image_of_injOn]
  · rfl
  intro a ha b hb hab
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  have hd : (q : ℤ) ∣ a - b := (ZMod.intCast_eq_intCast_iff_dvd_sub b a q).mp hab.symm
  by_contra hne
  have := Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hne)) ((dvd_abs _ _).mpr hd)
  have : |a - b| ≤ 6 := abs_le.mpr ⟨by omega, by omega⟩
  omega

/-- A nonzero linear form `a ↦ a ⬝ d` is equidistributed: for every predicate `P`,
`#{a | P (a ⬝ d)} · q = #{x | P x} · q^n`. -/
theorem row_count [Fact q.Prime] (d : Fin n → ZMod q) (hd : d ≠ 0) (P : ZMod q → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun a : Fin n → ZMod q ↦ P (a ⬝ᵥ d)).card * q =
      (Finset.univ.filter P).card * q^n := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by contrapose! hd; ext i; exact hd i
  let u : Fin n → ZMod q := Pi.single j (d j)⁻¹
  have hu : u ⬝ᵥ d = 1 := by simp [u, hj]
  let fib (t : ZMod q) := Finset.univ.filter fun a : Fin n → ZMod q ↦ a ⬝ᵥ d = t
  have hfib (t : ZMod q) : (fib t).card = (fib 0).card := by
    refine Finset.card_bij' (fun a _ ↦ a - t • u) (fun a _ ↦ a + t • u) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [sub_dotProduct, smul_dotProduct, hu, ha, smul_eq_mul, mul_one, sub_self]
    · intro a ha
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [add_dotProduct, smul_dotProduct, hu, ha, smul_eq_mul, mul_one, zero_add]
    · intro a _; simp
    · intro a _; simp
  have htot : (fib 0).card * q = q^n := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n → ZMod q)))
      (t := Finset.univ) (f := fun a ↦ a ⬝ᵥ d) (fun _ _ ↦ Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
    rw [h]
    change (fib 0).card * q = ∑ t, (fib t).card
    simp_rw [hfib]
    simp [Finset.card_univ, ZMod.card, mul_comm]
  have hsplit : (Finset.univ.filter fun a : Fin n → ZMod q ↦ P (a ⬝ᵥ d)).card =
      ∑ t ∈ Finset.univ.filter P, (fib t).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a : Fin n → ZMod q ↦ a ⬝ᵥ d)
      (t := Finset.univ.filter P) (fun a ha ↦ by simpa using ha)]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    congr 1
    ext a
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl
    simpa using ht
  rw [hsplit]
  simp_rw [hfib]
  rw [Finset.sum_const, smul_eq_mul, mul_assoc, htot]

/-- Exact acceptance probability of a wrong residue on `v` reserved rows, for any fixed values `e`
of the reserved errors: `#{A | ∀ j, accept (A j ⬝ s + e j − A j ⬝ c)} / q^{nv} = (7/q)^v`. -/
theorem verify_exact [Fact q.Prime] (hq : 6 < q) {v : ℕ} (s c : Fin n → ZMod q) (hc : c ≠ s)
    (e : Fin v → ZMod q) :
    ((Finset.univ.filter fun A : Matrix (Fin v) (Fin n) (ZMod q) ↦
        ∀ j, accept (A j ⬝ᵥ s + e j - A j ⬝ᵥ c)).card : ℚ) / (q : ℚ)^(n*v) = (7/q)^v := by
  classical
  have hd : s - c ≠ 0 := sub_ne_zero.mpr hc.symm
  let T (j : Fin v) := Finset.univ.filter fun a : Fin n → ZMod q ↦ accept (a ⬝ᵥ (s - c) + e j)
  have hT (j : Fin v) : (T j).card * q = 7 * q^n := by
    have h := row_count (s - c) hd (fun x ↦ accept (x + e j))
    have h7 : (Finset.univ.filter fun x : ZMod q ↦ accept (x + e j)).card = 7 := by
      rw [← acceptSet_card hq]
      refine Finset.card_bij' (fun x _ ↦ x + e j) (fun y _ ↦ y - e j) ?_ ?_ ?_ ?_
      · intro x hx; simpa [accept_iff] using hx
      · intro y hy; simpa [accept_iff] using hy
      · intro x _; simp
      · intro y _; simp
    rw [h7] at h
    exact h
  change ((Finset.univ.filter fun A : Fin v → Fin n → ZMod q ↦
      ∀ j, accept (A j ⬝ᵥ s + e j - A j ⬝ᵥ c)).card : ℚ) / (q : ℚ)^(n*v) = (7/q)^v
  have hset : (Finset.univ.filter fun A : Fin v → Fin n → ZMod q ↦
      ∀ j, accept (A j ⬝ᵥ s + e j - A j ⬝ᵥ c)) = Fintype.piFinset T := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, T,
      dotProduct_sub]
    refine forall_congr' fun j ↦ ?_
    rw [show A j ⬝ᵥ s + e j - A j ⬝ᵥ c = A j ⬝ᵥ s - A j ⬝ᵥ c + e j by ring]
  rw [hset, Fintype.card_piFinset]
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hT' (j : Fin v) : ((T j).card : ℚ) = 7 * q^n / q := by
    rw [eq_div_iff hq0]; exact_mod_cast hT j
  push_cast
  simp_rw [hT']
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, mul_pow, ← pow_mul,
    mul_comm n v, pow_mul]
  field_simp
  rw [← mul_pow, mul_div_cancel₀ _ hq0]

/-- Union bound over a candidate list fixed independently of the reserved rows: the probability
that some wrong residue in `C` passes all `v` reserved rows is at most `#C · (7/q)^v`. -/
theorem verify_union [Fact q.Prime] (hq : 6 < q) {v : ℕ} (s : Fin n → ZMod q)
    (C : Finset (Fin n → ZMod q)) (hC : s ∉ C) (e : Fin v → ZMod q) :
    ((Finset.univ.filter fun A : Matrix (Fin v) (Fin n) (ZMod q) ↦
        ∃ c ∈ C, ∀ j, accept (A j ⬝ᵥ s + e j - A j ⬝ᵥ c)).card : ℚ) / (q : ℚ)^(n*v) ≤
      C.card * (7/q)^v := by
  classical
  have hsub : (Finset.univ.filter fun A : Matrix (Fin v) (Fin n) (ZMod q) ↦
        ∃ c ∈ C, ∀ j, accept (A j ⬝ᵥ s + e j - A j ⬝ᵥ c)) ⊆
      C.biUnion fun c ↦ Finset.univ.filter fun A : Matrix (Fin v) (Fin n) (ZMod q) ↦
        ∀ j, accept (A j ⬝ᵥ s + e j - A j ⬝ᵥ c) := by
    intro A hA
    obtain ⟨c, hc, h⟩ := (Finset.mem_filter.mp hA).2
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hpos : (0 : ℚ) < (q : ℚ)^(n*v) := by
    have : (0 : ℚ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    positivity
  calc _ ≤ ((∑ c ∈ C, (Finset.univ.filter fun A : Matrix (Fin v) (Fin n) (ZMod q) ↦
            ∀ j, accept (A j ⬝ᵥ s + e j - A j ⬝ᵥ c)).card : ℕ) : ℚ) / (q : ℚ)^(n*v) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard) hpos.le
    _ = ∑ c ∈ C, (7/q : ℚ)^v := by
        push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun c hc ↦ verify_exact hq s c ?_ e
        rintro rfl; exact hC hc
    _ = _ := by simp

/-- `verify_exact` averaged over iid CBD(η) reserved errors (cast into `ZMod q`). -/
theorem verify_cbd [Fact q.Prime] (hq : 6 < q) (η : ℕ) {v : ℕ} (s c : Fin n → ZMod q)
    (hc : c ≠ s) :
    expect (cbdWeight η) (fun e : Fin v → Digit η ↦
      ((Finset.univ.filter fun A : Matrix (Fin v) (Fin n) (ZMod q) ↦
        ∀ j, accept (A j ⬝ᵥ s + ((centered (e j) : ℤ) : ZMod q) - A j ⬝ᵥ c)).card : ℚ) /
          (q : ℚ)^(n*v)) = (7/q)^v := by
  unfold expect
  simp_rw [verify_exact hq s c hc, ← Finset.sum_mul]
  rw [← Fintype.prod_sum (fun (_ : Fin v) a ↦ cbdWeight η a), cbdWeight_sum]
  simp

/-- The union bound when the candidate list `C ω` depends on other data `ω` (other blocks,
the secret), drawn with weights `p` and independent of the reserved rows. -/
theorem verify_union_avg [Fact q.Prime] (hq : 6 < q) {v : ℕ} {Ω : Type*} [Fintype Ω]
    (p : Ω → ℚ) (hp : ∀ ω, 0 ≤ p ω) (s : Ω → Fin n → ZMod q) (e : Ω → Fin v → ZMod q)
    (C : Ω → Finset (Fin n → ZMod q)) (hC : ∀ ω, s ω ∉ C ω) :
    ∑ ω, p ω * (((Finset.univ.filter fun A : Matrix (Fin v) (Fin n) (ZMod q) ↦
        ∃ c ∈ C ω, ∀ j, accept (A j ⬝ᵥ s ω + e ω j - A j ⬝ᵥ c)).card : ℚ) / (q : ℚ)^(n*v)) ≤
      (∑ ω, p ω * (C ω).card) * (7/q)^v := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ ↦ ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (verify_union hq (s ω) (C ω) (hC ω) (e ω)) (hp ω)

end SigabaNeo.Wall1.MultiBlock

#print axioms SigabaNeo.Wall1.MultiBlock.acceptSet_card
#print axioms SigabaNeo.Wall1.MultiBlock.row_count
#print axioms SigabaNeo.Wall1.MultiBlock.verify_exact
#print axioms SigabaNeo.Wall1.MultiBlock.verify_union
#print axioms SigabaNeo.Wall1.MultiBlock.verify_cbd
#print axioms SigabaNeo.Wall1.MultiBlock.verify_union_avg
