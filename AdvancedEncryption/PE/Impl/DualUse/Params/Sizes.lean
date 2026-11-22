import PE.Impl.DualUse.ConcreteNoise
import PE.Impl.DualUse.Params.SimTrapNorm

/-!
# Parameters for simulated keys: the sizes and the noise

The parameters of `DualUse.Concrete` cover the shift of the *real* trapdoor only (`2^76`); the
shift of the simulated trapdoor `W_f` of the reductions is `simTrapBound N k n`
(`DualUse.cnorm_simTrap_le`), astronomically larger. Here:

* `q = 2^K`, `K = 2^25`, `k = K + 1` binary digits;
* ring degree `N = 2^34`, so that `log₂ q / N = 2^{-9}` (Ring-LWE estimate in `Params/Stat.lean`);
* `|Wd| = 2^61 ≥ 2 · K · N + 600` columns of `B₀`, for the leftover hash lemma over `R_q²`;
* the shift of every trapdoor (real or simulated, window predicates of at most `375` gates)
  within `τ = 2^{16041210}` (`simTrapBound_le`, `realShift_le`);
* key boxes of `B = 16041444` bits per coefficient;
* errors from the centered binomial law of width `16`, flooding below `2^512`.

For every predicate of at most `375` gates and keys within `2^{B−1}`, the noise bound is below
`2^{32083266} / 4 < q / 4` (`noise_ok`). The sizes are opaque (`irreducible_def`): no power of
`2` with a large exponent is evaluated, all bounds are exponent arithmetic.
-/

namespace AdvancedEncryption.DualUse.Params

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP AdvancedEncryption.RingBTVW
open AdvancedEncryption.DualUse.Concrete (pow_mul_le' pow_mul_le pow_le_pow' sum_bound)

/-- `K = log₂ q`. -/
irreducible_def Kp : ℕ := 2 ^ 25
/-- The number of digits. -/
def kp : ℕ := Kp + 1
/-- The ring degree. -/
irreducible_def Np : ℕ := 2 ^ 34
/-- The columns of `B₀`. -/
irreducible_def dp : ℕ := 2 ^ 61
/-- `log₂` of the bound on the shifts of the trapdoors. -/
irreducible_def Eτ : ℕ := 16041210
/-- The bits of a coefficient of the big box. -/
irreducible_def Bp : ℕ := 16041444

theorem hkp : 2 ^ Kp < 2 ^ kp := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self Kp)

theorem Np_pos : 0 < Np := by rw [Np_def]; positivity

theorem kp_le : kp ≤ 2 ^ 26 := by
  have : 2 ^ 25 + 1 ≤ 2 ^ 26 := by norm_num
  rw [kp, Kp_def]; exact this

theorem card_colP : Fintype.card (Col kp) = 2 * kp := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

theorem WN_le : Fintype.card (Col kp) * Np ≤ 2 ^ 61 := by
  rw [card_colP, Np_def]
  have := kp_le
  have h : 2 * kp * 2 ^ 34 ≤ 2 * 2 ^ 26 * 2 ^ 34 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
  exact h.trans (by norm_num)

theorem WN1_le : Fintype.card (Col kp) * Np + 1 ≤ 2 ^ 62 := by
  have := WN_le; have : (2 : ℕ) ^ 62 = 2 * 2 ^ 61 := by norm_num
  omega

theorem modFactor_le : modFactor (Fintype.card (Col kp) * Np) kp ≤ 2 ^ 678 := by
  unfold modFactor
  have h1 : 4 * kp + 14 ≤ 2 ^ 29 := by have := kp_le; omega
  have h2 : (4 * kp + 14) ^ 2 ≤ 2 ^ 58 := by
    calc (4 * kp + 14) ^ 2 ≤ (2 ^ 29) ^ 2 := Nat.pow_le_pow_left h1 _
      _ = 2 ^ 58 := by rw [← pow_mul]
  have h3 : (Fintype.card (Col kp) * Np + 1) ^ 10 ≤ 2 ^ 620 := by
    calc (Fintype.card (Col kp) * Np + 1) ^ 10 ≤ (2 ^ 62) ^ 10 := Nat.pow_le_pow_left WN1_le _
      _ = 2 ^ 620 := by rw [← pow_mul]
  exact pow_mul_le' h2 h3 rfl

theorem treeHeight_le : treeHeight Np kp ≤ 62 := by
  unfold treeHeight
  refine Nat.clog_le_of_le_pow ?_
  have : Fintype.card ((Fin 2 × Fin kp) × Fin Np) = Fintype.card (Col kp) * Np := by
    rw [Fintype.card_prod, Fintype.card_fin]
  rw [this]
  exact WN1_le

theorem gswFactor_le : gswFactor (Fintype.card (Col kp) * Np) Np kp ≤ 2 ^ 42776 := by
  unfold gswFactor
  have h1 : modFactor (Fintype.card (Col kp) * Np) kp ^ (treeHeight Np kp + 1) ≤ 2 ^ 42714 := by
    calc modFactor (Fintype.card (Col kp) * Np) kp ^ (treeHeight Np kp + 1)
        ≤ (2 ^ 678) ^ (treeHeight Np kp + 1) := Nat.pow_le_pow_left modFactor_le _
      _ ≤ (2 ^ 678) ^ 63 := Nat.pow_le_pow_right (by positivity) (by have := treeHeight_le; omega)
      _ = 2 ^ 42714 := by rw [← pow_mul]
  have h := pow_mul_le h1 WN1_le
  rwa [show 42714 + 62 = 42776 from rfl] at h

/-- `G^n` for `n ≤ 375` gates. -/
theorem gswPow_le {n : ℕ} (hn : n ≤ 375) :
    gswFactor (Fintype.card (Col kp) * Np) Np kp ^ n ≤ 2 ^ 16041000 :=
  calc gswFactor (Fintype.card (Col kp) * Np) Np kp ^ n
      ≤ gswFactor (Fintype.card (Col kp) * Np) Np kp ^ 375 :=
        Nat.pow_le_pow_right (gswFactor_pos _ Np kp) hn
    _ ≤ (2 ^ 42776) ^ 375 := Nat.pow_le_pow_left gswFactor_le _
    _ = 2 ^ (42776 * 375) := (pow_mul 2 42776 375).symm
    _ = 2 ^ 16041000 := by rw [show 42776 * 375 = 16041000 from rfl]

theorem R_le : Fintype.card (Fin 1 × Col kp × Fin kp × Fin Np) ≤ 2 ^ 87 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  have := kp_le
  rw [Np_def]
  calc 1 * (2 * kp * (kp * 2 ^ 34)) ≤ 1 * (2 * 2 ^ 26 * (2 ^ 26 * 2 ^ 34)) := by gcongr
    _ = 2 ^ 87 := by norm_num

theorem RW_le : Fintype.card (Fin 1 × Col kp × Fin kp × Fin Np) * (Fintype.card (Col kp) * Np) + 1
    ≤ 2 ^ 149 := by
  have := pow_mul_le' R_le WN_le (rfl : 87 + 61 = 148)
  have h2 : (2 : ℕ) ^ 149 = 2 * 2 ^ 148 := by rw [← pow_succ']
  have h1 : 1 ≤ (2 : ℕ) ^ 148 := Nat.one_le_two_pow
  omega

theorem card_trapColP : Fintype.card (DualUse.TrapCol kp) ≤ 2 ^ 29 := by
  rw [Fintype.card_sum, Fintype.card_sum, card_colP, Fintype.card_fin]
  have := kp_le
  have : (2 : ℕ) ^ 29 = 8 * 2 ^ 26 := by norm_num
  omega

theorem E_le : Fintype.card (Fin dp) * Np * 2 ^ 512 ≤ 2 ^ 607 := by
  rw [Fintype.card_fin, dp_def, Np_def, ← pow_add, ← pow_add]

theorem Np_le : Np ≤ 2 ^ 34 := by rw [Np_def]

/-- `τ = 2^{Eτ}`: the bound on the shifts of the trapdoors. -/
noncomputable def τp : ℕ := 2 ^ Eτ

/-- **The shift of the simulated trapdoor** for predicates of at most `375` gates. -/
theorem simTrapBound_le {n : ℕ} (hn : n ≤ 375) : DualUse.simTrapBound Np kp n ≤ τp := by
  unfold DualUse.simTrapBound τp
  have h := pow_mul_le' WN_le (pow_mul_le' RW_le (gswPow_le hn) rfl)
    rfl
  exact h.trans (le_of_eq (congrArg (2 ^ ·) (by rw [Eτ_def])))

/-- **The shift of the real trapdoor** (errors within `16`). -/
theorem realShift_le : (Fintype.card (Col kp) * Np) ^ 2 * 16 ≤ τp := by
  have h : (Fintype.card (Col kp) * Np) ^ 2 * 16 ≤ (2 ^ 61) ^ 2 * 2 ^ 4 :=
    Nat.mul_le_mul (Nat.pow_le_pow_left WN_le 2) (le_refl _)
  rw [← pow_mul, ← pow_add] at h
  exact h.trans (pow_le_pow' (by rw [Eτ_def]; norm_num))

/-- **The noise of a predicate of at most `375` gates is far below `q/4`**, for keys within
`2^{B−1}`. -/
theorem noise_ok (f : SLP (Fin 10) × Wire (Fin 10)) (hf : f.1.length ≤ 375) (S : ℕ)
    (hS : S ≤ 2 ^ (Bp - 1)) :
    4 * DualUse.noiseBound (Wd := Fin dp) (Wt := DualUse.TrapCol kp) (N := Np) hkp (2 ^ 512) S f + 2
      < 2 ^ Kp := by
  have hS' : S ≤ 2 ^ 16041443 := hS.trans (le_of_eq (congrArg (2 ^ ·) (by rw [Bp_def])))
  have hGn := gswPow_le hf
  have hRB := RingBTVW.noiseBound_le (N := Np) (Attr := Fin 10) hkp
    (Fintype.card (Fin dp) * Np * 2 ^ 512) S f
  have T2 : _ ≤ 2 ^ 16042111 := pow_mul_le' (pow_mul_le' WN_le E_le rfl) hS' rfl
  have T3 : _ ≤ 2 ^ 32083260 := pow_mul_le' (pow_mul_le' WN_le (pow_mul_le' RW_le (pow_mul_le' hGn E_le rfl) rfl) rfl)
    hS' rfl
  have T4 : _ ≤ 2 ^ 16042050 := pow_mul_le' E_le hS' rfl
  have T5 : _ ≤ 2 ^ 16042018 := pow_mul_le' (pow_mul_le' (pow_mul_le' card_trapColP Np_le rfl) (le_refl (2 ^ 512)) rfl)
    hS' rfl
  have m1 : (2 : ℕ) ^ 607 ≤ 2 ^ 32083260 := pow_le_pow' (by norm_num)
  have m2 : (2 : ℕ) ^ 16042111 ≤ 2 ^ 32083260 := pow_le_pow' (by norm_num)
  have m4 : (2 : ℕ) ^ 16042050 ≤ 2 ^ 32083260 := pow_le_pow' (by norm_num)
  have m5 : (2 : ℕ) ^ 16042018 ≤ 2 ^ 32083260 := pow_le_pow' (by norm_num)
  have hsum := sum_bound _ _ _ _ _ (2 ^ 32083260) (E_le.trans m1) (T2.trans m2) T3 (T4.trans m4)
    (T5.trans m5) (pow_le_pow' (Nat.zero_le _))
  have e64 : 64 * (2 : ℕ) ^ 32083260 = 2 ^ 32083266 := by
    rw [show 32083266 = 6 + 32083260 from rfl, pow_add, show (2 : ℕ) ^ 6 = 64 from rfl]
  have hfin : (2 : ℕ) ^ 32083266 ≤ 2 ^ Kp := pow_le_pow' (by rw [Kp_def]; norm_num)
  unfold DualUse.noiseBound
  rw [Fintype.card_fin] at hRB ⊢
  rw [Fintype.card_fin] at hsum
  calc 4 * (RingBTVW.noiseBound (N := Np) hkp (dp * Np * 2 ^ 512) S f +
        (dp * Np * 2 ^ 512 * S + Fintype.card (DualUse.TrapCol kp) * Np * 2 ^ 512 * S)) + 2
      ≤ 4 * (dp * Np * 2 ^ 512 + Fintype.card (Col kp) * Np * (dp * Np * 2 ^ 512) * S +
          Fintype.card (Col kp) * Np * ((Fintype.card (Fin 1 × Col kp × Fin kp × Fin Np) *
            (Fintype.card (Col kp) * Np) + 1) *
            (gswFactor (Fintype.card (Col kp) * Np) Np kp ^ f.1.length * (dp * Np * 2 ^ 512))) * S +
          (dp * Np * 2 ^ 512 * S + Fintype.card (DualUse.TrapCol kp) * Np * 2 ^ 512 * S)) + 2 := by
        gcongr
    _ < 64 * 2 ^ 32083260 := hsum
    _ = 2 ^ 32083266 := e64
    _ ≤ 2 ^ Kp := hfin

end AdvancedEncryption.DualUse.Params
