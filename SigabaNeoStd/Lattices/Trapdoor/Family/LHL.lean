import SigabaNeoStd.Lattices.Trapdoor.Family.Smooth
import CslibFrontier.Probability.Collision

/-!
# Trapdoor sampler: `Ā R` is close to uniform (leftover hash lemma)

A column `r` of `R` has independent entries `−1, 0, 0, 1` (two fair bits each: `dec4`). For a
uniform `Ā ∈ Z_q^{n×mb}`, `(Ā, Ā r)` is within `√(q^n (3/8)^{mb}) / 2` of `(Ā, u)` with `u` uniform
(`lhl_column`):

* for each `Ā`, `dist(Ā r, u) ≤ √(q^n · cp_Ā − 1)/2` (cslib-frontier's `dist_uniform_le`);
* averaging the square root over `Ā` (Cauchy–Schwarz) and computing the expected collision
  probability: two codes `x, x'` collide under every `Ā` if `r(x) = r(x')` (probability
  `(6/16)^{mb}`), and otherwise with probability `1/q^n`, because `r(x) − r(x')` has entries in
  `[−2, 2]`, so it is nonzero mod `q`, and `Ā d` is uniform for `d ≠ 0`.
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal Matrix Cslib.Probability.PMF

/-- Two fair bits to `−1, 0, 0, 1`. -/
def dec4 (c : Fin 4) : ℤ := if c = 0 then -1 else if c = 3 then 1 else 0

theorem abs_dec4_le (c : Fin 4) : |dec4 c| ≤ 1 := by unfold dec4; split_ifs <;> simp

theorem card_dec4_pairs :
    (Finset.univ.filter fun p : Fin 4 × Fin 4 => dec4 p.1 = dec4 p.2).card = 6 := by decide

section
variable (κ : ℕ)

/-- Codes of one column. -/
abbrev Codes : Type := Fin (mb κ) → Fin 4

def colOf (x : Codes κ) : Fin (mb κ) → ℤ := fun a => dec4 (x a)

/-- `Ā r`. -/
noncomputable def hA (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ))) (x : Codes κ) :
    Fin (n κ) → ZMod (q κ) :=
  Abar *ᵥ fun a => (colOf κ x a : ZMod (q κ))

/-- The number of uniform matrices `Ā` with `Ā d = 0` for `d ≠ 0`. -/
theorem card_ker (d : Fin (mb κ) → ZMod (q κ)) (hd : d ≠ 0) :
    (Finset.univ.filter fun Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)) =>
      Abar *ᵥ d = 0).card * q κ ^ n κ = q κ ^ (n κ * mb κ) := by
  classical
  have h := card_vecMul_field (K := ZMod (q κ)) (n := mb κ) (m := n κ) d hd 0
  rw [ZMod.card] at h
  have e : (Finset.univ.filter fun Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)) =>
      Abar *ᵥ d = 0).card =
      (Finset.univ.filter fun B : Matrix (Fin (mb κ)) (Fin (n κ)) (ZMod (q κ)) =>
        d ᵥ* B = 0).card := by
    refine Finset.card_bij (fun Abar _ => Abarᵀ) ?_ ?_ ?_
    · intro Abar hA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
      rw [Matrix.vecMul_transpose]; exact hA
    · intro a _ b _ h; exact Matrix.transpose_injective h
    · intro B hB
      refine ⟨Bᵀ, ?_, Matrix.transpose_transpose B⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
      rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]; exact hB
  rw [e, h, mul_comm (mb κ)]


/-! ### Counting collisions of codes -/

noncomputable def ι4 (p : Fin 4 × Fin 4) : ℝ := if dec4 p.1 = dec4 p.2 then 1 else 0

theorem sum_ι4 : ∑ p : Fin 4 × Fin 4, ι4 p = 6 := by
  unfold ι4
  rw [← Finset.sum_filter, Finset.sum_const, card_dec4_pairs]; norm_num

theorem colOf_eq_iff (x x' : Codes κ) : colOf κ x = colOf κ x' ↔ ∀ a, dec4 (x a) = dec4 (x' a) := by
  constructor
  · intro h a; exact congrFun h a
  · intro h; funext a; exact h a

theorem sum_codes_collide :
    ∑ x : Codes κ, ∑ x' : Codes κ, (if colOf κ x = colOf κ x' then (1 : ℝ) else 0) =
      6 ^ mb κ := by
  have h1 : ∀ x x' : Codes κ, (if colOf κ x = colOf κ x' then (1 : ℝ) else 0) =
      ∏ a, ι4 (x a, x' a) := by
    intro x x'
    by_cases h : colOf κ x = colOf κ x'
    · rw [if_pos h]
      symm; refine Finset.prod_eq_one fun a _ => ?_
      unfold ι4; rw [if_pos ((colOf_eq_iff κ x x').mp h a)]
    · rw [if_neg h]
      obtain ⟨a, ha⟩ : ∃ a, dec4 (x a) ≠ dec4 (x' a) := by
        by_contra hc; push Not at hc; exact h ((colOf_eq_iff κ x x').mpr hc)
      symm; refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      unfold ι4; rw [if_neg ha]
  simp only [h1]
  rw [← Fintype.sum_prod_type']
  let e : (Fin (mb κ) → Fin 4 × Fin 4) ≃ (Codes κ × Codes κ) :=
    { toFun := fun z => (fun a => (z a).1, fun a => (z a).2)
      invFun := fun p a => (p.1 a, p.2 a)
      left_inv := fun z => by funext a; rfl
      right_inv := fun p => rfl }
  rw [← e.sum_comp]
  have : ∀ z : Fin (mb κ) → Fin 4 × Fin 4, ∏ a, ι4 ((e z).1 a, (e z).2 a) = ∏ a, ι4 (z a) :=
    fun z => rfl
  simp only [this]
  rw [← Fintype.prod_sum (fun _ : Fin (mb κ) => fun p : Fin 4 × Fin 4 => ι4 p), sum_ι4,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem q_gt_four : 4 < q κ := by
  have := q_gt_nat κ
  have : 2 ^ 8 ≤ 2 ^ w κ := Nat.pow_le_pow_right (by norm_num) (by unfold w; omega)
  omega

theorem diff_ne_zero (x x' : Codes κ) (h : colOf κ x ≠ colOf κ x') :
    (fun a => ((colOf κ x a - colOf κ x' a : ℤ) : ZMod (q κ))) ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a, dec4 (x a) ≠ dec4 (x' a) := by
    by_contra hc; push Not at hc; exact h ((colOf_eq_iff κ x x').mpr hc)
  intro h0
  have h1 := congrFun h0 a
  simp only [Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  have hb : |dec4 (x a) - dec4 (x' a)| ≤ 2 := by
    have := abs_dec4_le (x a); have := abs_dec4_le (x' a)
    rw [abs_le] at *; constructor <;> linarith
  have hne : dec4 (x a) - dec4 (x' a) ≠ 0 := sub_ne_zero.mpr ha
  have := Int.natAbs_le_of_dvd_ne_zero h1 hne
  rw [Int.natAbs_natCast] at this
  have h4 := q_gt_four κ
  have : (dec4 (x a) - dec4 (x' a)).natAbs ≤ 2 := by
    have h' := abs_le.mp hb; omega
  simp only [colOf] at *
  omega


/-! ### The expected collision probability -/

abbrev MatA : Type := Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ))
abbrev Syn : Type := Fin (n κ) → ZMod (q κ)

/-- The collision probability of `Ā r`. -/
noncomputable def cpA (Abar : MatA κ) : ℝ :=
  PMF.collisionProbability ((PMF.uniformOfFintype (Codes κ)).map (hA κ Abar))

theorem card_MatA : Fintype.card (MatA κ) = q κ ^ (n κ * mb κ) := card_matrix _ _

theorem card_Syn : Fintype.card (Syn κ) = q κ ^ n κ := by simp [Syn, Fintype.card_fun]

theorem card_Codes : Fintype.card (Codes κ) = 4 ^ mb κ := by simp [Codes, Fintype.card_fun]

theorem avg_ker (x x' : Codes κ) :
    ∑ Abar : MatA κ, (PMF.uniformOfFintype (MatA κ) Abar).toReal *
        (if hA κ Abar x = hA κ Abar x' then (1 : ℝ) else 0) =
      if colOf κ x = colOf κ x' then 1 else 1 / (q κ : ℝ) ^ n κ := by
  classical
  have hq : (0 : ℝ) < q κ := q_pos κ
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, card_MatA]
  rw [← Finset.mul_sum]
  have hiff : ∀ Abar : MatA κ, hA κ Abar x = hA κ Abar x' ↔
      Abar *ᵥ (fun a => ((colOf κ x a - colOf κ x' a : ℤ) : ZMod (q κ))) = 0 := by
    intro Abar
    have : (fun a => ((colOf κ x a - colOf κ x' a : ℤ) : ZMod (q κ))) =
        (fun a => (colOf κ x a : ZMod (q κ))) - fun a => (colOf κ x' a : ZMod (q κ)) := by
      funext a; simp
    rw [this, Matrix.mulVec_sub, sub_eq_zero]; rfl
  simp only [hiff]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  split_ifs with h
  · have : (fun a => ((colOf κ x a - colOf κ x' a : ℤ) : ZMod (q κ))) = 0 := by
      funext a; rw [h]; simp
    simp only [this, Matrix.mulVec_zero, Finset.filter_true, Finset.card_univ, card_MatA]
    push_cast
    field_simp
  · have hc := card_ker κ _ (diff_ne_zero κ x x' h)
    have hc' : ((Finset.univ.filter fun Abar : MatA κ =>
        Abar *ᵥ (fun a => ((colOf κ x a - colOf κ x' a : ℤ) : ZMod (q κ))) = 0).card : ℝ) =
        (q κ : ℝ) ^ (n κ * mb κ) / (q κ : ℝ) ^ n κ := by
      rw [eq_div_iff (by positivity)]; exact_mod_cast hc
    rw [hc']
    field_simp
    push_cast; ring

theorem avg_cpA_le :
    ∑ Abar : MatA κ, (PMF.uniformOfFintype (MatA κ) Abar).toReal * cpA κ Abar ≤
      (3 / 8 : ℝ) ^ mb κ + 1 / (q κ : ℝ) ^ n κ := by
  classical
  have hq : (0 : ℝ) < q κ := q_pos κ
  set u : ℝ := ((Fintype.card (Codes κ) : ℝ))⁻¹
  have hcp : ∀ Abar : MatA κ, cpA κ Abar =
      ∑ x : Codes κ, ∑ x' : Codes κ, u * u * (if hA κ Abar x = hA κ Abar x' then 1 else 0) := by
    intro Abar
    unfold cpA
    rw [PMF.collisionProbability_map]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, u]
    split_ifs <;> ring
  simp only [hcp, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := MatA κ)]
  have h1 : ∀ x x' : Codes κ, ∑ Abar : MatA κ, (PMF.uniformOfFintype (MatA κ) Abar).toReal *
      (u * u * (if hA κ Abar x = hA κ Abar x' then 1 else 0)) =
      u * u * (if colOf κ x = colOf κ x' then 1 else 1 / (q κ : ℝ) ^ n κ) := by
    intro x x'
    rw [← avg_ker, Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => by ring
  simp only [h1]
  have h2 : ∀ x x' : Codes κ, u * u * (if colOf κ x = colOf κ x' then 1 else 1 / (q κ : ℝ) ^ n κ) ≤
      u * u * (if colOf κ x = colOf κ x' then 1 else 0) + u * u * (1 / (q κ : ℝ) ^ n κ) := by
    intro x x'
    have hu : 0 ≤ u * u := by positivity
    split_ifs
    · nlinarith [mul_nonneg hu (by positivity : (0 : ℝ) ≤ 1 / (q κ : ℝ) ^ n κ)]
    · linarith
  calc ∑ x : Codes κ, ∑ x' : Codes κ,
        u * u * (if colOf κ x = colOf κ x' then 1 else 1 / (q κ : ℝ) ^ n κ)
      ≤ ∑ x : Codes κ, ∑ x' : Codes κ, (u * u * (if colOf κ x = colOf κ x' then 1 else 0) +
          u * u * (1 / (q κ : ℝ) ^ n κ)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => h2 x x'
    _ = u * u * 6 ^ mb κ + (Fintype.card (Codes κ) : ℝ) ^ 2 * (u * u) *
          (1 / (q κ : ℝ) ^ n κ) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_codes_collide, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
        ring
    _ = (3 / 8 : ℝ) ^ mb κ + 1 / (q κ : ℝ) ^ n κ := by
        simp only [u, card_Codes]
        push_cast
        have h4 : (4 : ℝ) ^ mb κ ≠ 0 := by positivity
        field_simp
        have e : ((4 : ℝ) ^ mb κ) ^ 2 * (3 / 8) ^ mb κ = 6 ^ mb κ := by
          rw [← pow_mul, mul_comm (mb κ) 2, pow_mul, ← mul_pow]; norm_num
        rw [mul_add, mul_one, ← e]; ring


/-- Jensen for the square root, by Cauchy–Schwarz. -/
theorem sum_mul_sqrt_le {ι : Type*} (S : Finset ι) (w f : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hf : ∀ i ∈ S, 0 ≤ f i) (h1 : ∑ i ∈ S, w i = 1) :
    ∑ i ∈ S, w i * Real.sqrt (f i) ≤ Real.sqrt (∑ i ∈ S, w i * f i) := by
  apply Real.le_sqrt_of_sq_le
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * Real.sqrt (f i))
  have e1 : ∀ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * Real.sqrt (f i)) = w i * Real.sqrt (f i) :=
    fun i hi => by rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have e2 : ∀ i ∈ S, Real.sqrt (w i) ^ 2 = w i := fun i hi => Real.sq_sqrt (hw i hi)
  have e3 : ∀ i ∈ S, (Real.sqrt (w i) * Real.sqrt (f i)) ^ 2 = w i * f i := fun i hi => by
    rw [mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hf i hi)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, h1, one_mul] at hcs
  exact hcs

/-- **Leftover hash lemma, one column.** -/
theorem lhl_column :
    ∑ Abar : MatA κ, (PMF.uniformOfFintype (MatA κ) Abar).toReal *
        dist ((PMF.uniformOfFintype (Codes κ)).map (hA κ Abar)) (PMF.uniformOfFintype (Syn κ)) ≤
      Real.sqrt ((q κ : ℝ) ^ n κ * (3 / 8) ^ mb κ) / 2 := by
  classical
  set N : ℝ := (Fintype.card (Syn κ) : ℝ)
  have hN : N = (q κ : ℝ) ^ n κ := by simp only [N, card_Syn]; push_cast; rfl
  have hq : (0 : ℝ) < q κ := q_pos κ
  set w : MatA κ → ℝ := fun A => (PMF.uniformOfFintype (MatA κ) A).toReal
  set f : MatA κ → ℝ := fun A => N * cpA κ A - 1
  have hw : ∀ A ∈ Finset.univ, 0 ≤ w A := fun A _ => ENNReal.toReal_nonneg
  have hf : ∀ A ∈ Finset.univ, 0 ≤ f A := fun A _ => by
    have := PMF.dist_uniform_sq_le ((PMF.uniformOfFintype (Codes κ)).map (hA κ A))
    simp only [f, cpA]; nlinarith [sq_nonneg (dist ((PMF.uniformOfFintype (Codes κ)).map (hA κ A))
      (PMF.uniformOfFintype (Syn κ)))]
  have h1 : ∑ A ∈ Finset.univ, w A = 1 := PMF.sum_toReal _
  have hdist : ∀ A, dist ((PMF.uniformOfFintype (Codes κ)).map (hA κ A))
      (PMF.uniformOfFintype (Syn κ)) ≤ Real.sqrt (f A) / 2 := fun A =>
    PMF.dist_uniform_le _
  calc ∑ A : MatA κ, w A * dist ((PMF.uniformOfFintype (Codes κ)).map (hA κ A))
        (PMF.uniformOfFintype (Syn κ))
      ≤ ∑ A : MatA κ, w A * (Real.sqrt (f A) / 2) :=
        Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (hdist A) (hw A (Finset.mem_univ _))
    _ = (∑ A : MatA κ, w A * Real.sqrt (f A)) / 2 := by rw [Finset.sum_div]; ring_nf
    _ ≤ Real.sqrt (∑ A : MatA κ, w A * f A) / 2 := by
        gcongr; exact sum_mul_sqrt_le _ w f hw hf h1
    _ ≤ Real.sqrt ((q κ : ℝ) ^ n κ * (3 / 8) ^ mb κ) / 2 := by
        gcongr
        have hsum : ∑ A : MatA κ, w A * f A = N * (∑ A : MatA κ, w A * cpA κ A) - 1 := by
          simp only [f, mul_sub, mul_one, Finset.sum_sub_distrib, h1, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun A _ => by ring
        rw [hsum]
        have := avg_cpA_le κ
        rw [hN] at *
        have hqn : (0 : ℝ) < (q κ : ℝ) ^ n κ := by positivity
        calc (q κ : ℝ) ^ n κ * (∑ A : MatA κ, w A * cpA κ A) - 1
            ≤ (q κ : ℝ) ^ n κ * ((3 / 8 : ℝ) ^ mb κ + 1 / (q κ : ℝ) ^ n κ) - 1 := by gcongr
          _ = _ := by field_simp; ring

end

end SigabaNeo.Lattices.Trapdoor.Family

