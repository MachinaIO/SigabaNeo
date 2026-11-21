import PE.Impl.DualUse.Noise
import PE.Impl.DualUse.Trapdoor
import PE.Impl.RingBTVW.NoiseClosed

/-!
# Concrete parameters: the noise

`K = 2^24` (`q = 2^K`), `k = K + 1`, `N = 2^10`, `|Wd| = 2^35`, the encryption errors within
`2^512` and the keys within `2^511`. For every predicate of at most `375` gates (the window
predicates, `Gates.DateWindow.length_winGates`), the noise bound is below `2^6057083 / 4`, far below
`q/4` (`noise_ok`). The numbers are kept as exponents: no power of `2` is evaluated.
-/

namespace AdvancedEncryption.DualUse.Concrete

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP AdvancedEncryption.RingBTVW

/-- `K = log₂ q` (opaque, so that `2^K` is never evaluated). -/
irreducible_def Kc : ℕ := 2 ^ 24
/-- The number of digits. -/
def kc : ℕ := Kc + 1
/-- The ring degree. -/
def Nc : ℕ := 2 ^ 10
/-- The columns of `B₀` (opaque, so that `Fin dc` is never enumerated). -/
irreducible_def dc : ℕ := 2 ^ 35

theorem hkc : 2 ^ Kc < 2 ^ kc := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self Kc)

theorem pow_mul_le' {a b α β γ : ℕ} (ha : a ≤ 2 ^ α) (hb : b ≤ 2 ^ β) (h : α + β = γ) :
    a * b ≤ 2 ^ γ := by
  rw [← h, pow_add]; exact Nat.mul_le_mul ha hb

theorem pow_mul_le {a b α β : ℕ} (ha : a ≤ 2 ^ α) (hb : b ≤ 2 ^ β) : a * b ≤ 2 ^ (α + β) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

theorem pow_add_le {a b α : ℕ} (ha : a ≤ 2 ^ α) (hb : b ≤ 2 ^ α) : a + b ≤ 2 ^ (α + 1) := by
  rw [pow_succ]; omega

theorem pow_le_pow' {α β : ℕ} (h : α ≤ β) : 2 ^ α ≤ 2 ^ β := Nat.pow_le_pow_right (by norm_num) h

theorem kc_le : kc ≤ 2 ^ 25 := by
  have : 2 ^ 24 + 1 ≤ 2 ^ 25 := by norm_num
  rw [kc, Kc_def]; exact this

theorem card_col : Fintype.card (Col kc) = 2 * kc := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

theorem WN_le : Fintype.card (Col kc) * Nc ≤ 2 ^ 36 := by
  rw [card_col]
  have := kc_le
  have h : 2 * kc * Nc ≤ 2 * 2 ^ 25 * 2 ^ 10 := by
    unfold Nc; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
  exact h.trans (by norm_num)

theorem WN1_le : Fintype.card (Col kc) * Nc + 1 ≤ 2 ^ 37 := by
  have := WN_le; have : (2 : ℕ) ^ 37 = 2 * 2 ^ 36 := by norm_num
  omega

theorem modFactor_le : modFactor (Fintype.card (Col kc) * Nc) kc ≤ 2 ^ 426 := by
  unfold modFactor
  have h1 : 4 * kc + 14 ≤ 2 ^ 28 := by have := kc_le; omega
  have h2 : (4 * kc + 14) ^ 2 ≤ 2 ^ 56 := by
    calc (4 * kc + 14) ^ 2 ≤ (2 ^ 28) ^ 2 := Nat.pow_le_pow_left h1 _
      _ = 2 ^ 56 := by rw [← pow_mul]
  have h3 : (Fintype.card (Col kc) * Nc + 1) ^ 10 ≤ 2 ^ 370 := by
    calc (Fintype.card (Col kc) * Nc + 1) ^ 10 ≤ (2 ^ 37) ^ 10 := Nat.pow_le_pow_left WN1_le _
      _ = 2 ^ 370 := by rw [← pow_mul]
  exact pow_mul_le h2 h3

theorem treeHeight_le : treeHeight Nc kc ≤ 37 := by
  unfold treeHeight
  refine Nat.clog_le_of_le_pow ?_
  have : Fintype.card ((Fin 2 × Fin kc) × Fin Nc) = Fintype.card (Col kc) * Nc := by
    rw [Fintype.card_prod, Fintype.card_fin]
  rw [this]
  have := WN1_le
  exact this

theorem gswFactor_le : gswFactor (Fintype.card (Col kc) * Nc) Nc kc ≤ 2 ^ 16225 := by
  unfold gswFactor
  have h1 : modFactor (Fintype.card (Col kc) * Nc) kc ^ (treeHeight Nc kc + 1) ≤ 2 ^ 16188 := by
    calc modFactor (Fintype.card (Col kc) * Nc) kc ^ (treeHeight Nc kc + 1)
        ≤ (2 ^ 426) ^ (treeHeight Nc kc + 1) := Nat.pow_le_pow_left modFactor_le _
      _ ≤ (2 ^ 426) ^ 38 := Nat.pow_le_pow_right (by positivity) (by have := treeHeight_le; omega)
      _ = 2 ^ 16188 := by rw [← pow_mul]
  have h := pow_mul_le h1 WN1_le
  rwa [show 16188 + 37 = 16225 from rfl] at h

theorem R_le : Fintype.card (Fin 1 × Col kc × Fin kc × Fin Nc) ≤ 2 ^ 61 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  have := kc_le
  calc 1 * (2 * kc * (kc * Nc)) ≤ 1 * (2 * 2 ^ 25 * (2 ^ 25 * 2 ^ 10)) := by
        unfold Nc; gcongr
    _ = 2 ^ 61 := by norm_num

theorem card_trapCol : Fintype.card (TrapCol kc) ≤ 2 ^ 28 := by
  rw [Fintype.card_sum, Fintype.card_sum, card_col, Fintype.card_fin]
  have := kc_le
  have : (2 : ℕ) ^ 28 = 8 * 2 ^ 25 := by norm_num
  omega

theorem RW_le : Fintype.card (Fin 1 × Col kc × Fin kc × Fin Nc) * (Fintype.card (Col kc) * Nc) + 1
    ≤ 2 ^ 98 := by
  have := pow_mul_le' R_le WN_le (rfl : 61 + 36 = 97)
  have h2 : (2 : ℕ) ^ 98 = 2 * 2 ^ 97 := by rw [← pow_succ']
  have h1 : 1 ≤ (2 : ℕ) ^ 97 := Nat.one_le_two_pow
  omega

theorem E_le : Fintype.card (Fin dc) * Nc * 2 ^ 512 ≤ 2 ^ 557 := by
  rw [Fintype.card_fin, dc_def, Nc, ← pow_add, ← pow_add]

theorem Nc_le : Nc ≤ 2 ^ 10 := le_refl _

/-- The final sum, with the large power kept as a variable. -/
theorem sum_bound (a₁ a₂ a₃ a₄ a₅ M : ℕ) (h₁ : a₁ ≤ M) (h₂ : a₂ ≤ M) (h₃ : a₃ ≤ M) (h₄ : a₄ ≤ M)
    (h₅ : a₅ ≤ M) (hM : 1 ≤ M) : 4 * (a₁ + a₂ + a₃ + (a₄ + a₅)) + 2 < 64 * M := by
  omega

/-- **The noise of a predicate of at most `375` gates is far below `q/4`.** -/
theorem noise_ok (f : SLP (Fin 10) × Wire (Fin 10)) (hf : f.1.length ≤ 375) (S : ℕ)
    (hS : S ≤ 2 ^ 511) :
    4 * noiseBound (Wd := Fin dc) (Wt := TrapCol kc) (N := Nc) hkc (2 ^ 512) S f + 2 < 2 ^ Kc := by
  have hGn : gswFactor (Fintype.card (Col kc) * Nc) Nc kc ^ f.1.length ≤ 2 ^ 6084375 := by
    calc gswFactor (Fintype.card (Col kc) * Nc) Nc kc ^ f.1.length
        ≤ gswFactor (Fintype.card (Col kc) * Nc) Nc kc ^ 375 :=
          Nat.pow_le_pow_right (gswFactor_pos _ Nc kc) hf
      _ ≤ (2 ^ 16225) ^ 375 := Nat.pow_le_pow_left gswFactor_le _
      _ = 2 ^ (16225 * 375) := (pow_mul 2 16225 375).symm
      _ = 2 ^ 6084375 := by rw [show 16225 * 375 = 6084375 from rfl]
  have hRB := RingBTVW.noiseBound_le (N := Nc) (Attr := Fin 10) hkc
    (Fintype.card (Fin dc) * Nc * 2 ^ 512) S f
  have T2 := pow_mul_le' (pow_mul_le' WN_le E_le rfl) hS (rfl : 36 + 557 + 511 = 1104)
  have T3 := pow_mul_le' (pow_mul_le' WN_le (pow_mul_le' RW_le (pow_mul_le' hGn E_le rfl) rfl) rfl)
    hS (rfl : 36 + (98 + (6084375 + 557)) + 511 = 6085577)
  have T4 := pow_mul_le' E_le hS (rfl : 557 + 511 = 1068)
  have T5 := pow_mul_le' (pow_mul_le' (pow_mul_le' card_trapCol Nc_le rfl) (le_refl (2 ^ 512)) rfl)
    hS (rfl : 28 + 10 + 512 + 511 = 1061)
  have m1 : (2 : ℕ) ^ 557 ≤ 2 ^ 6085577 := pow_le_pow' (by norm_num)
  have m2 : (2 : ℕ) ^ 1104 ≤ 2 ^ 6085577 := pow_le_pow' (by norm_num)
  have m4 : (2 : ℕ) ^ 1068 ≤ 2 ^ 6085577 := pow_le_pow' (by norm_num)
  have m5 : (2 : ℕ) ^ 1061 ≤ 2 ^ 6085577 := pow_le_pow' (by norm_num)
  have hsum := sum_bound _ _ _ _ _ (2 ^ 6085577) (E_le.trans m1) (T2.trans m2) T3 (T4.trans m4)
    (T5.trans m5) Nat.one_le_two_pow
  have e64 : 64 * (2 : ℕ) ^ 6085577 = 2 ^ 6085583 := by
    rw [show 6085583 = 6 + 6085577 from rfl, pow_add, show (2 : ℕ) ^ 6 = 64 from rfl]
  have hfin : (2 : ℕ) ^ 6085583 ≤ 2 ^ Kc := pow_le_pow' (by rw [Kc_def]; norm_num)
  unfold noiseBound
  rw [Fintype.card_fin] at hRB ⊢
  rw [Fintype.card_fin] at hsum
  calc 4 * (RingBTVW.noiseBound (N := Nc) hkc (dc * Nc * 2 ^ 512) S f +
        (dc * Nc * 2 ^ 512 * S + Fintype.card (TrapCol kc) * Nc * 2 ^ 512 * S)) + 2
      ≤ 4 * (dc * Nc * 2 ^ 512 + Fintype.card (Col kc) * Nc * (dc * Nc * 2 ^ 512) * S +
          Fintype.card (Col kc) * Nc * ((Fintype.card (Fin 1 × Col kc × Fin kc × Fin Nc) *
            (Fintype.card (Col kc) * Nc) + 1) *
            (gswFactor (Fintype.card (Col kc) * Nc) Nc kc ^ f.1.length * (dc * Nc * 2 ^ 512))) * S +
          (dc * Nc * 2 ^ 512 * S + Fintype.card (TrapCol kc) * Nc * 2 ^ 512 * S)) + 2 := by
        gcongr
    _ < 64 * 2 ^ 6085577 := hsum
    _ = 2 ^ 6085583 := e64
    _ ≤ 2 ^ Kc := hfin

end AdvancedEncryption.DualUse.Concrete
