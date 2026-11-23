import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledRawBall

/-! A void bound for projective raw graph witnesses on the uniform matrix law.
Normalize the distinguished input coordinate to one. Equal input directions
with different outputs are incompatible, and different inputs give uniform pairs. -/

noncomputable section
namespace SigabaNeo.Wall1.RawGraphVoid
open Finset Matrix QaryMembership DualExit
open scoped Classical

variable {m n q : ℕ} [Fact q.Prime]
abbrev Vec (d q : ℕ) := Fin d → ZMod q
abbrev Direction (m n q : ℕ) := Vec m q × Vec n q

def incident (A : Design m n q) (z : Direction m n q) : Prop := A *ᵥ z.2 = z.1

private def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) := (∑ a, f a) / Fintype.card Ω
private def flag (P : Prop) : ℝ := if P then 1 else 0

private lemma mean_sum {Ω I : Type*} [Fintype Ω] (T : Finset I) (f : I → Ω → ℝ) :
    mean (fun a ↦ ∑ z ∈ T, f z a) = ∑ z ∈ T, mean (f z) := by
  simp only [mean, sum_comm (s := (univ : Finset Ω)) (t := T), sum_div]

private lemma mean_flag (P : Design m n q → Prop) :
    mean (fun A ↦ flag (P A)) = probability P := by
  simp [mean, probability, designs, flag]

private lemma uniform {G H : Type*} [AddGroup G] [Fintype G] [AddGroup H] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (b : H) :
    mean (fun a ↦ flag (f a = b)) = 1 / Fintype.card H := by
  have he (c : H) : (univ.filter (fun a ↦ f a = c)).card =
      (univ.filter (fun a ↦ f a = b)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (AddMonoidHom.fiberEquivOfSurjective hf c b)
  have count : Fintype.card G = Fintype.card H * (univ.filter (fun a ↦ f a = b)).card := by
    simpa [he] using card_eq_sum_card_fiberwise (s := (univ : Finset G)) (t := univ)
      (f := f) (fun _ _ ↦ mem_univ _)
  simp only [mean, flag, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  rw [one_mul, mul_comm]
  exact_mod_cast count.symm

private def eval (u : Vec n q) : Design m n q →+ Vec m q :=
  ⟨⟨fun A ↦ A *ᵥ u, by simp⟩, fun A B ↦ add_mulVec A B u⟩

private lemma single_mean (p : Fin n) (z : Direction m n q) (hz : z.2 p = 1) :
    mean (fun A ↦ flag (incident A z)) = 1 / (q:ℝ)^m := by
  have onto : Function.Surjective (eval (m := m) z.2) := by
    intro b
    refine ⟨fun i ↦ Pi.single p (b i), ?_⟩
    ext i
    simp [eval, mulVec, single_dotProduct, hz]
  simpa [incident, eval] using uniform (eval z.2) onto z.1

private lemma joint_mean (p : Fin n) {z w : Direction m n q} (hz : z.2 p = 1)
    (hw : w.2 p = 1) (hn : z ≠ w) :
    mean (fun A ↦ flag (incident A z) * flag (incident A w)) ≤ (1 / (q:ℝ)^m)^2 := by
  by_cases h : z.2 = w.2
  · have disj (A : Design m n q) (ha : incident A z) : ¬ incident A w := fun hb ↦
      hn (Prod.ext ((ha.symm.trans (congrArg (A *ᵥ ·) h)).trans hb) h)
    have zero (A : Design m n q) : flag (incident A z) * flag (incident A w) = 0 := by
      by_cases ha : incident A z <;> simp [flag, ha, disj]
    simp only [zero, mean, sum_const_zero, zero_div, sq_nonneg]
  obtain ⟨k,hk⟩ : ∃ k, z.2 k ≠ w.2 k := by simpa [funext_iff] using h
  let f := (eval (m := m) z.2).prod (eval w.2)
  have onto : Function.Surjective f := by
    rintro ⟨b,c⟩
    let a (i : Fin m) := (b i - c i) / (z.2 k - w.2 k)
    let A : Design m n q := fun i ↦ Pi.single k (a i) + Pi.single p (b i - a i * z.2 k)
    have row (v : Vec n q) (hv : v p = 1) (i : Fin m) :
        (A *ᵥ v) i = a i * v k + (b i - a i * z.2 k) := by
      change (Pi.single k (a i) + Pi.single p (b i - a i * z.2 k)) ⬝ᵥ v = _
      rw [add_dotProduct, single_dotProduct, single_dotProduct, hv, mul_one]
    refine ⟨A, Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)⟩
    · change (A *ᵥ z.2) i = _
      rw [row _ hz]; ring
    · change (A *ᵥ w.2) i = _
      rw [row _ hw]
      dsimp [a]
      field_simp [sub_ne_zero.mpr hk]
      ring
  have eqn (A : Design m n q) : flag (incident A z) * flag (incident A w) =
      flag (f A = (z.1, w.1)) := by
    change _ = flag ((A *ᵥ z.2, A *ᵥ w.2) = _)
    by_cases hz' : incident A z <;> by_cases hw' : incident A w <;>
      simp_all only [Prod.mk.injEq, incident, flag, and_self, false_and, and_false, ite_true,
        ite_false, mul_zero, zero_mul, one_mul]
  simp_rw [eqn]
  rw [uniform f onto]
  simp [pow_two, Nat.cast_pow]

/-- For a family of normalized distinct directions with expected hit count μ, the
probability of missing them all is at most 1/(1+μ). -/
theorem void_probability (p : Fin n) (T : Finset (Direction m n q))
    (normed : ∀ z ∈ T, z.2 p = 1) :
    probability (fun A ↦ ∀ z ∈ T, ¬ incident A z) ≤ (q : ℝ)^m / ((q:ℝ)^m + T.card) := by
  let I (z : Direction m n q) (A : Design m n q) := flag (incident A z)
  let Z (A : Design m n q) := ∑ z ∈ T, I z A
  let d : ℝ := 1 / (q:ℝ)^m
  let μ : ℝ := T.card * d
  have qp : (0:ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have dpos : 0 < d := by dsimp [d]; positivity
  have mnonneg : 0 ≤ μ := mul_nonneg (Nat.cast_nonneg _) dpos.le
  have positive : 0 < μ + 1 := by linarith
  have first : mean Z = μ := by
    rw [show mean Z = ∑ z ∈ T, mean (I z) from mean_sum T I]
    simp only [I, sum_congr rfl (fun z hz ↦ single_mean p z (normed z hz))]
    simp [μ, d]
  have pair (z) (hz : z ∈ T) (w) (hw : w ∈ T) :
      mean (fun A ↦ I z A * I w A) ≤ (if w = z then d else 0) + d^2 := by
    by_cases he : w = z
    · subst w
      have diag (A : Design m n q) : I z A * I z A = I z A := by
        by_cases h : incident A z <;> simp [I, flag, h]
      simpa only [diag, ite_true, I, single_mean p z (normed z hz)] using
        (le_add_of_nonneg_right (sq_nonneg d) : d ≤ d + d^2)
    · simpa [he, I, d] using joint_mean p (normed z hz) (normed w hw) (Ne.symm he)
  have second : mean (fun A ↦ Z A ^ 2) ≤ μ + μ^2 := by
    simp only [Z, pow_two, sum_mul, mul_sum, mean_sum]
    rw [sum_comm (s := T) (t := T)]
    calc
      _ ≤ ∑ z ∈ T, ∑ w ∈ T, ((if w = z then d else 0) + d^2) :=
        sum_le_sum fun z hz ↦ sum_le_sum fun w hw ↦ pair z hz w hw
      _ = _ := by simp [sum_add_distrib, μ, pow_two]; ring
  let void := fun A : Design m n q ↦ ∀ z ∈ T, ¬ incident A z
  have pt (A : Design m n q) : flag (void A) * (μ+1)^2 ≤ (Z A - (μ+1))^2 := by
    by_cases h : void A
    · have zero : Z A = 0 := sum_eq_zero fun z hz ↦ by simp [I, flag, h z hz]
      simp only [flag, h, ite_true, one_mul, zero, zero_sub, neg_sq, le_refl]
    · simp [flag, h, sq_nonneg]
  have H := sum_le_sum (s := univ) fun A _ ↦ pt A
  have hm : mean (fun A ↦ flag (void A)) * (μ+1)^2 ≤
      mean (fun A ↦ Z A^2) - 2*mean Z*(μ+1) + (μ+1)^2 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const,
      card_univ, nsmul_eq_mul] at H
    simp only [mean]
    have cp : (0:ℝ) < Fintype.card (Design m n q) := by exact_mod_cast Fintype.card_pos
    field_simp
    nlinarith only [H]
  rw [mean_flag, first] at hm
  have bound : probability void * (μ+1) ≤ 1 := by
    apply (mul_le_mul_iff_left₀ positive).mp
    nlinarith only [hm, second]
  have hq : (0:ℝ) < (q:ℝ)^m := pow_pos qp _
  apply (le_div_iff₀ (add_pos_of_pos_of_nonneg hq (Nat.cast_nonneg _))).2
  have eq : (q:ℝ)^m + T.card = (μ+1) * q^m := by
    dsimp [μ, d]
    field_simp
    ring
  rw [eq, ← mul_assoc]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right bound hq.le

end SigabaNeo.Wall1.RawGraphVoid

#print axioms SigabaNeo.Wall1.RawGraphVoid.void_probability
