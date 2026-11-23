module

public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Randomized
public import SigabaNeo.Lib.Lattices.Research.Wall1.PMFSeedAveraging
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Randomized
import all SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockAttack
import Mathlib.Tactic

/-! `recovery_randomized` for an arbitrary seed PMF. -/

public section
noncomputable section
namespace SigabaNeo.Wall1.Width638
open MultiBlock QaryMembership SigabaNeo.SampleDeletion Finset
open scoped Classical ENNReal
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private theorem lweProb_le_one {m n q η : ℕ} [Fact q.Prime]
    (P : (Fin n → Digit η) → (Fin m → Digit η) → Matrix (Fin m) (Fin n) (ZMod q) → Prop) :
    Attack.lweProb m n q η P ≤ 1 := by
  have h := Attack.lweProb_not m n q η P
  have h0 : 0 ≤ Attack.lweProb m n q η (fun s e A ↦ ¬ P s e A) := by
    unfold Attack.lweProb
    apply div_nonneg _ (by positivity)
    exact sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ by
      split_ifs <;> positivity
  linarith

private theorem lweProb_nonneg {m n q η : ℕ} [Fact q.Prime]
    (P : (Fin n → Digit η) → (Fin m → Digit η) → Matrix (Fin m) (Fin n) (ZMod q) → Prop) :
    0 ≤ Attack.lweProb m n q η P := by
  unfold Attack.lweProb
  apply div_nonneg _ (by positivity)
  exact sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ by
    split_ifs <;> positivity

private theorem summable_weighted {Ω : Type*} (μ : PMF Ω) (f : Ω → ℝ)
    (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) :
    Summable fun ω ↦ (μ ω).toReal * f ω := by
  have hs : Summable fun ω ↦ (μ ω).toReal :=
    ENNReal.summable_toReal (by rw [μ.tsum_coe]; exact ENNReal.one_ne_top)
  refine Summable.of_nonneg_of_le (fun ω ↦ mul_nonneg ENNReal.toReal_nonneg (h0 ω))
    (fun ω ↦ ?_) hs
  simpa using mul_le_mul_of_nonneg_left (h1 ω) (ENNReal.toReal_nonneg (a := μ ω))

private theorem tsum_toReal_one {Ω : Type*} (μ : PMF Ω) : ∑' ω, (μ ω).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun ω ↦ μ.apply_ne_top ω), μ.tsum_coe, ENNReal.toReal_one]

/-- Seed law `μ` independent of the sample; per-input error at most `δ`. -/
theorem recovery_randomized_pmf {Ω : Type*} (μ : PMF Ω) (S : Ω → Solver) (δ : ℝ) (hδ : 0 ≤ δ)
    (herr : ∀ A t, μ.toOuterMeasure {ω | ¬ Correct (S ω) A t} ≤ ENNReal.ofReal δ) :
    (643162094166 / 10^12 : ℝ) - 4*δ ≤ ∑' ω, (μ ω).toReal * (Attack.lweProb 512 511 3329 3
      (fun s e A ↦ firstValidatedBy (S ω) blockRow reservedRow A (Attack.lweSample A s e) =
        some (centered ∘ s)) : ℝ) := by
  obtain ⟨O₀⟩ := graphOracle_nonempty (r := 127) (n := 511) (q := 3329)
  let Bad (ω : Ω) (i : Fin 4) (s : Fin 511 → Digit 3) (e : Fin 512 → Digit 3) (A : Sample) :=
    ¬ Correct (S ω) (query blockRow A (Attack.lweSample A s e) i).1
      (query blockRow A (Attack.lweSample A s e) i).2
  let raw (ω : Ω) : ℝ := (Attack.lweProb 512 511 3329 3 (fun s e A ↦
    firstValidatedBy (S ω) blockRow reservedRow A (Attack.lweSample A s e) =
      some (centered ∘ s)) : ℝ)
  let bad (ω : Ω) (i : Fin 4) : ℝ := (Attack.lweProb 512 511 3329 3 (Bad ω i) : ℝ)
  have seedwise (ω : Ω) : (643162094166 / 10^12 : ℝ) ≤ raw ω + ∑ i, bad ω i := by
    have base := recovery_std (patch O₀ (S ω))
    have un : Attack.lweProb 512 511 3329 3 (fun s e A ↦
          firstValidated (patch O₀ (S ω)) blockRow reservedRow A (Attack.lweSample A s e) =
            some (centered ∘ s)) ≤
        Attack.lweProb 512 511 3329 3 (fun s e A ↦
          firstValidatedBy (S ω) blockRow reservedRow A (Attack.lweSample A s e) =
            some (centered ∘ s)) + ∑ i, Attack.lweProb 512 511 3329 3 (Bad ω i) := by
      apply Attack.lweProb_union
      intro s e A hp
      by_cases hall : ∀ i, ¬ Bad ω i s e A
      · left
        rw [agree O₀ (S ω) blockRow reservedRow A _ (fun i ↦ by simpa [Bad] using hall i)]
        exact hp
      · right
        push_neg at hall
        exact hall
    have h := base.le.trans un
    have hr := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at hr
    simpa [raw, bad] using hr
  have nn (P : (Fin 511 → Digit 3) → (Fin 512 → Digit 3) → Sample → Prop) :
      (0:ℝ) ≤ (Attack.lweProb 512 511 3329 3 P : ℝ) := by
    exact_mod_cast lweProb_nonneg P
  have le1 (P : (Fin 511 → Digit 3) → (Fin 512 → Digit 3) → Sample → Prop) :
      (Attack.lweProb 512 511 3329 3 P : ℝ) ≤ 1 := by
    exact_mod_cast lweProb_le_one P
  have sraw := summable_weighted μ raw (fun ω ↦ nn _) (fun ω ↦ le1 _)
  have sbad (i : Fin 4) := summable_weighted μ (fun ω ↦ bad ω i) (fun ω ↦ nn _) (fun ω ↦ le1 _)
  have errs (i : Fin 4) : ∑' ω, (μ ω).toReal * bad ω i ≤ δ :=
    lweProb_pmf_seed_average_le μ (fun ω ↦ Bad ω i) δ hδ fun s e A ↦ herr _ _
  have sum_bad : ∑' ω, (μ ω).toReal * ∑ i, bad ω i = ∑ i, ∑' ω, (μ ω).toReal * bad ω i := by
    simp_rw [mul_sum]
    exact Summable.tsum_finsetSum fun i _ ↦ sbad i
  have sbad' : Summable fun ω ↦ (μ ω).toReal * ∑ i, bad ω i := by
    simp_rw [mul_sum]
    exact summable_sum fun i _ ↦ sbad i
  have hs1 : Summable fun ω ↦ (μ ω).toReal :=
    ENNReal.summable_toReal (by rw [μ.tsum_coe]; exact ENNReal.one_ne_top)
  have lower : ∑' ω, (μ ω).toReal * (643162094166 / 10^12 : ℝ) ≤
      ∑' ω, ((μ ω).toReal * raw ω + (μ ω).toReal * ∑ i, bad ω i) :=
    Summable.tsum_le_tsum (fun ω ↦ by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left (seedwise ω) ENNReal.toReal_nonneg)
      (hs1.mul_right _) (sraw.add sbad')
  rw [tsum_mul_right, tsum_toReal_one, one_mul, Summable.tsum_add sraw sbad', sum_bad] at lower
  have hE : ∑ i : Fin 4, ∑' ω, (μ ω).toReal * bad ω i ≤ 4*δ := by
    have := sum_le_sum (s := (univ : Finset (Fin 4))) fun i _ ↦ errs i
    simpa using this
  linarith

end SigabaNeo.Wall1.Width638

#print axioms SigabaNeo.Wall1.Width638.recovery_randomized_pmf
