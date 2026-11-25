import PE.Impl.RingBTVW.Impl

/-!
# The coins of the implementation are short

With an error law whose support is within `η` (centered), every key of `Setup` has a short
trapdoor (`setup_trapdoor_short`), every coin of `Enc` is within `max η 2^w`
(`coins_short`), and the real trapdoor shifts a key by at most `τ = (|W| N)² η` in every
coefficient (`cnorm_realTrap_le`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability

variable {N Q : ℕ} [NeZero Q]

theorem polyOf_short {χ : PMF (ZMod Q)} {η : ℕ} (hχ : ∀ e ∈ χ.support, zabs e ≤ η)
    {a : Negacyclic (ZMod Q) N} (ha : a ∈ (polyOf (N := N) χ).support) : cnorm a ≤ η := by
  rw [polyOf, PMF.mem_support_map_iff] at ha
  obtain ⟨v, hv, rfl⟩ := ha
  rw [cnorm_le_iff]
  intro j
  rw [Negacyclic.coeffs_ofCoeffs]
  exact hχ _ ((Cslib.Probability.PMF.mem_support_pi_iff _ v).mp hv j)

theorem rowLaw_short {χ : PMF (Negacyclic (ZMod Q) N)} {η : ℕ}
    (hχ : ∀ a ∈ χ.support, cnorm a ≤ η) {ι : Type} [Fintype ι]
    {e : Matrix (Fin 1) ι (Negacyclic (ZMod Q) N)} (he : e ∈ (rowLaw χ ι).support) :
    rnorm e ≤ η := by
  rw [rowLaw, PMF.mem_support_map_iff] at he
  obtain ⟨v, hv, rfl⟩ := he
  rw [rnorm_le_iff]
  intro c
  exact hχ _ ((Cslib.Probability.PMF.mem_support_pi_iff _ v).mp hv c)

variable {K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The trapdoor of `Setup` is short.** -/
theorem setup_trapdoor_short {η : ℕ} (hχ : ∀ e ∈ c.χc.support, zabs e ≤ η)
    (v : PK hk c × SKey hk c) (hv : v ∈ (setupM hk c).support) :
    rnorm v.2.2.1 ≤ η ∧ cnorm v.2.2.2 ≤ η := by
  unfold setupM setupLaw at hv
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hv
  obtain ⟨B₀, -, a, -, t, ht, e, he, Bj, -, p, -, rfl⟩ := hv
  exact ⟨rowLaw_short (fun a ha => polyOf_short hχ ha) he, polyOf_short hχ ht⟩

theorem cnorm_bitVal_le (b : Bool) : cnorm (bitVal b : Negacyclic (ZMod Q) N) ≤ 1 := by
  cases b
  · simp [bitVal, cnorm_zero]
  · simpa [bitVal] using cnorm_one_le (N := N) (q := Q)

/-- **The coins of `Enc` are short**: within `2^w` when `η ≤ 2^w`. -/
theorem coins_short {η : ℕ} (hχ : ∀ e ∈ c.χc.support, zabs e ≤ η) (hηw : η ≤ 2 ^ c.w)
    (r : EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k)) (hr : r ∈ (coinsM hk c).support) :
    cnorm r.e' ≤ 2 ^ c.w ∧ rnorm r.e₀ ≤ 2 ^ c.w ∧ rnorm r.e₁ ≤ 2 ^ c.w ∧
      (∀ i a b, cnorm (r.Rm i a b) ≤ 1) ∧ ∀ j, rnorm (r.ej j) ≤ 2 ^ c.w := by
  have hpoly : ∀ a ∈ (polyOf (N := N) c.χc).support, cnorm a ≤ η := fun a ha => polyOf_short hχ ha
  unfold coinsM lawCoins at hr
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hr
  obtain ⟨rest, hrest, ej, hej, rfl⟩ := hr
  unfold lawRestNF at hrest
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hrest
  obtain ⟨σ, hσ, u₀, -, e₀, he₀, ea, hea, ez, hez, Rm, hRm, e', he', rfl⟩ := hrest
  refine ⟨(hpoly e' he').trans hηw, (rowLaw_short hpoly he₀).trans hηw, ?_, ?_, ?_⟩
  · rw [rnorm_le_iff]
    intro col
    have hea' := (rnorm_le_iff ea η).mp (rowLaw_short hpoly hea)
    have hez' := (rnorm_le_iff ez η).mp (rowLaw_short hpoly hez)
    simp only [coinsOf]
    rcases col with _ | col | col
    · exact (hpoly σ hσ).trans hηw
    · exact (hea' col).trans hηw
    · exact (hez' col).trans hηw
  · intro i a b
    simp only [coinsOf]
    unfold lawRmBin at hRm
    rw [PMF.mem_support_map_iff] at hRm
    obtain ⟨bits, -, rfl⟩ := hRm
    exact cnorm_bitVal_le _
  · intro j
    simp only [coinsOf]
    have : NeZero (2 ^ c.w) := ⟨by positivity⟩
    unfold floodRows floodLaw at hej
    simp only [PMF.map_comp, PMF.mem_support_map_iff] at hej
    obtain ⟨T, -, rfl⟩ := hej
    rw [rnorm_le_iff]
    intro col
    rw [cnorm_le_iff]
    intro i
    simp only [Function.comp_apply, Matrix.of_apply, Negacyclic.coeffs_ofCoeffs]
    have := zabs_intCast_le (q := 2 ^ K) ((T ((j, col), i) : ℕ) : ℤ)
    simp only [Int.cast_natCast, Int.natAbs_natCast] at this
    exact this.trans (T ((j, col), i)).isLt.le

/-- The entries of the trapdoor `[e; t I; I]` are within `η ≥ 1`. -/
theorem cnorm_trapMat_le {η : ℕ} (hη : 1 ≤ η) (e : Matrix (Fin 1) (Col k) (Rg N K)) (t : Rg N K)
    (he : rnorm e ≤ η) (ht : cnorm t ≤ η) (r : TrapCol k) (c : Col k) :
    cnorm (trapMat e t r c) ≤ η := by
  rcases r with _ | r | r
  · exact (rnorm_le_iff e η).mp he c
  · simp only [trapMat, Matrix.of_apply]
    split_ifs
    · exact ht
    · simp [cnorm_zero]
  · simp only [trapMat, Matrix.of_apply]
    split_ifs
    · exact cnorm_one_le.trans hη
    · simp [cnorm_zero]

/-- **The shift of the real trapdoor**: `(0, T G⁻¹(B_f − G̲) z)` has coefficients within
`(|W| N)² η` for a binary `z`. -/
theorem cnorm_realTrap_le {η : ℕ} (hη : 1 ≤ η) (e : Matrix (Fin 1) (Col k) (Rg N K)) (t : Rg N K)
    (he : rnorm e ≤ η) (ht : cnorm t ≤ η) (Bf : Matrix (Fin 1) (Col k) (Rg N K))
    (z : Col k → Rg N K) (hz : ∀ c, cnorm (z c) ≤ 1) :
    (realTrap (Wd := Fin c.d) (S := Sdw (N := N) hk) (trapMat e t) Bf z).1 = 0 ∧
      ∀ r, cnorm ((realTrap (Wd := Fin c.d) (S := Sdw (N := N) hk) (trapMat e t) Bf z).2 r) ≤
        (Fintype.card (Col k) * N) ^ 2 * η := by
  refine ⟨rfl, fun r => ?_⟩
  set Gi := (Sdw (N := N) hk).Γ₁.ginv (Bf - (Sdw (N := N) hk).Γ₁.G)
  have hGi : ∀ a b, cnorm (Gi a b) ≤ 1 := fun a b =>
    cnorm_gadgetOf_binary_ginv_le hk.le (fun _ : Fin 1 => (0 : Fin 2)) _ _ a b
  have hM : ∀ c', cnorm ((trapMat e t * Gi) r c') ≤ Fintype.card (Col k) * N * η := by
    intro c'
    rw [Matrix.mul_apply]
    refine (cnorm_sum_le _ _).trans ?_
    calc ∑ x, cnorm (trapMat e t r x * Gi x c') ≤ ∑ _x : Col k, N * η * 1 :=
          Finset.sum_le_sum fun x _ => (cnorm_mul_le _ _).trans
            (Nat.mul_le_mul (Nat.mul_le_mul_left _ (cnorm_trapMat_le hη e t he ht r x)) (hGi x c'))
      _ = Fintype.card (Col k) * N * η := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring
  show cnorm (((trapMat e t * Gi) *ᵥ z) r) ≤ _
  simp only [Matrix.mulVec, dotProduct]
  refine (cnorm_sum_le _ _).trans ?_
  calc ∑ x, cnorm ((trapMat e t * Gi) r x * z x)
      ≤ ∑ _x : Col k, N * (Fintype.card (Col k) * N * η) * 1 :=
        Finset.sum_le_sum fun x _ => (cnorm_mul_le _ _).trans
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ (hM x)) (hz x))
    _ = (Fintype.card (Col k) * N) ^ 2 * η := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring

end AdvancedEncryption.RingBTVW
