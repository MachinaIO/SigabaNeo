import SigabaNeo.Lib.Lattices.Trapdoor.Family.Exp
import SigabaNeo.Lib.Lattices.Trapdoor.Family.Close2
import CslibFrontier.Languages.Probabilistic.Retry
import CslibFrontier.Languages.Probabilistic.UniformNat

/-!
# Trapdoor sampler: a strict-time sampler for `D_{Z,τ}`

One attempt draws `v < 2^{A+1}` and `u < 2^T` and accepts `z = v − 2^A` when
`u · s^E < 2^T` in exact arithmetic (`accept`), where `s = Σ_{i<N} (y/E)^i / i!` and `y = π̂ z² / τ²`
with `π̂ = piInt P J / 2^P` (`Family/Pi.lean`, `Family/Exp.lean`). `samp1` retries at most
`Rt` times and outputs `0` if every attempt fails.

* `eval_samp1`: the law of `samp1`, from cslib-frontier's `evalWith_retry_some`/`_none`.
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib Cslib.Probability
open scoped ENNReal

section
variable (κ : ℕ)

/-- `m < 2^Lg`. -/
def Lg : ℕ := Nat.log 2 (m κ) + 1
/-- `2^A = τ · 2^{Lg+1}`: the range of the proposals. -/
def Aex : ℕ := κ + 4 + Lg κ
def Pbits : ℕ := 4 * (κ + Lg κ) + 64
def Ecnt : ℕ := 4 ^ (Lg κ + 2)
def Nterms : ℕ := κ + 2 * Lg κ + 40
def Tbits : ℕ := 2 * Ecnt κ + κ + 10
def Rt : ℕ := 2 ^ (Lg κ + 8) * (κ + 1)

/-- `π̂ · 2^P`. -/
def piNat : ℕ := (piInt (Pbits κ) (Pbits κ)).toNat

/-- The proposal `z = v − 2^A`. -/
def zOf (v : ℕ) : ℤ := (v : ℤ) - 2 ^ Aex κ

/-- `y = yN / yD = π̂ z² / τ²`. -/
def yN (v : ℕ) : ℕ := piNat κ * (zOf κ v).natAbs ^ 2
def yD : ℕ := 2 ^ (Pbits κ + 2 * κ + 6)

def Lnum (v : ℕ) : ℕ := sNum (yN κ v) (yD κ) (Ecnt κ) (Nterms κ) ^ Ecnt κ
def Lden : ℕ := sDen (yD κ) (Ecnt κ) (Nterms κ) ^ Ecnt κ

/-- Accept `u` for the proposal `v`. -/
def accept (κ v u : ℕ) : Bool := decide (u * Lnum κ v < 2 ^ Tbits κ * Lden κ)

/-- One attempt: the coins, tagged with `κ`. -/
noncomputable def attempt : ProbComp (ℕ × ℕ × ℕ) := do
  let v ← ProbComp.sampleBinaryNat (Aex κ + 1)
  let u ← ProbComp.sampleBinaryNat (Tbits κ)
  pure (κ, v, u)

/-- The output of the loop. -/
def outZ : Option (ℕ × ℕ × ℕ) → ℤ
  | some t => zOf t.1 t.2.1
  | none => 0

/-- The sampler for `D_{Z,τ}`. -/
noncomputable def samp1 : ProbComp ℤ :=
  outZ <$> OracleComp.retry (fun t : ℕ × ℕ × ℕ => accept t.1 t.2.1 t.2.2 = true) (attempt κ)
    (Rt κ)


/-! ### The law -/

/-- The acceptance probability of the proposal `v`. -/
noncomputable def pacc (v : ℕ) : ℝ≥0∞ :=
  (((Finset.range (2 ^ Tbits κ)).filter fun u => accept κ v u = true).card : ℝ≥0∞) /
    2 ^ Tbits κ

/-- The failure probability of one attempt. -/
noncomputable def qfail : ℝ≥0∞ :=
  (ProbComp.eval (attempt κ)).toOuterMeasure {t | ¬ accept t.1 t.2.1 t.2.2 = true}

/-- The expected number of attempts, truncated. -/
noncomputable def Gsum : ℝ≥0∞ := ∑ i ∈ Finset.range (Rt κ), qfail κ ^ i

theorem ev_binaryNat (w : ℕ) (f : ℕ → ℝ≥0∞) :
    ev (ProbComp.eval (ProbComp.sampleBinaryNat w)) f =
      (∑ v ∈ Finset.range (2 ^ w), f v) / 2 ^ w := by
  rw [ProbComp.eval_sampleBinaryNat, ev_map, ev_uniform, Fintype.card_fin]
  push_cast
  congr 1
  exact (Finset.sum_range (fun v => f v)).symm

theorem ev_attempt (f : ℕ × ℕ × ℕ → ℝ≥0∞) :
    ev (ProbComp.eval (attempt κ)) f =
      (∑ v ∈ Finset.range (2 ^ (Aex κ + 1)),
        (∑ u ∈ Finset.range (2 ^ Tbits κ), f (κ, v, u)) / 2 ^ Tbits κ) / 2 ^ (Aex κ + 1) := by
  unfold attempt
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ev_bind, ev_pure, ev_binaryNat]

theorem tsum_option' {α : Type} (F : Option α → ℝ≥0∞) :
    ∑' o, F o = F none + ∑' t, F (some t) := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  have h := (Option.some_injective α).tsum_eq (f := fun x => if x = none then 0 else F x) (by
    intro o ho
    cases o with
    | none => simp at ho
    | some t => exact ⟨t, rfl⟩)
  simp only [reduceCtorEq, if_false] at h
  convert h.symm using 3
  split_ifs <;> rfl

set_option maxHeartbeats 2000000 in
theorem ev_samp1 (f : ℤ → ℝ≥0∞) :
    ev (ProbComp.eval (samp1 κ)) f =
      Gsum κ * ((∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v * f (zOf κ v)) / 2 ^ (Aex κ + 1)) +
        qfail κ ^ Rt κ * f 0 := by
  unfold samp1
  rw [ProbComp.eval_map, ev_map]
  unfold ev
  rw [tsum_option']
  have hnone : ProbComp.eval (OracleComp.retry (fun t : ℕ × ℕ × ℕ => accept t.1 t.2.1 t.2.2 = true)
      (attempt κ) (Rt κ)) none = qfail κ ^ Rt κ := by
    rw [ProbComp.eval_eq_evalWith, OracleComp.evalWith_retry_none]; rfl
  have hsome : ∀ t, ProbComp.eval (OracleComp.retry (fun t : ℕ × ℕ × ℕ => accept t.1 t.2.1 t.2.2 = true)
      (attempt κ) (Rt κ)) (some t) =
      (if accept t.1 t.2.1 t.2.2 = true then ProbComp.eval (attempt κ) t else 0) * Gsum κ := by
    intro t
    rw [ProbComp.eval_eq_evalWith, OracleComp.evalWith_retry_some]; rfl
  simp only [hnone, hsome, Function.comp_apply, outZ]
  rw [add_comm (qfail κ ^ Rt κ * f 0)]
  refine congrArg (fun x => x + qfail κ ^ Rt κ * f 0) ?_
  have hev : ∑' t : ℕ × ℕ × ℕ, (if accept t.1 t.2.1 t.2.2 = true then
      ProbComp.eval (attempt κ) t else 0) * Gsum κ * f (zOf t.1 t.2.1) =
      Gsum κ * ev (ProbComp.eval (attempt κ))
        (fun t => ind (accept t.1 t.2.1 t.2.2 = true) * f (zOf t.1 t.2.1)) := by
    unfold ev
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun t => ?_
    beta_reduce
    by_cases h : accept t.1 t.2.1 t.2.2 = true
    · rw [if_pos h, ind_of h]; ring
    · rw [if_neg h, ind_of_not h]; ring
  have hv : ∀ v : ℕ, (∑ u ∈ Finset.range (2 ^ Tbits κ),
      ind (accept κ v u = true) * f (zOf κ v)) / 2 ^ Tbits κ = pacc κ v * f (zOf κ v) := by
    intro v
    have hc : ∑ u ∈ Finset.range (2 ^ Tbits κ), ind (accept κ v u = true) =
        (((Finset.range (2 ^ Tbits κ)).filter fun u => accept κ v u = true).card : ℝ≥0∞) := by
      rw [Finset.card_filter]; push_cast
      refine Finset.sum_congr rfl fun u _ => ?_
      unfold ind; split_ifs <;> simp_all
    unfold pacc
    rw [← Finset.sum_mul, hc, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    ring
  rw [hev, ev_attempt]
  simp only [hv]

end

end SigabaNeo.Lattices.Trapdoor.Family
