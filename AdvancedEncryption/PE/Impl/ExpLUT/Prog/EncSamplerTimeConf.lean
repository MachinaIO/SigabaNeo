import PE.Impl.ExpLUT.Prog.EncSamplerTime
import PE.Impl.ExpLUT.Prog.EncSizeConf
/-! # Concrete numerical budgets of the encryption coin sampler -/
namespace AdvancedEncryption.ExpLUT.Prog.EncConf
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.ExpLUT.Params AdvancedEncryption.RingBTVW.Prog

/-- Numerals for the three coefficient loops, without enumerating any finite index type. -/
theorem small_coefficient_count : nEncSmall Dc * Dc.N = 55340330084525408256 := by
  simp only [nEncSmall, BCol, Wb, Jh, Col, Enum.length_prod, len_sum, len_fin]
  norm_num [Dc, Kc, mbar]

theorem flood_coefficient_count : nFl Dc * Dc.N = 1435599410829755540307968 := by
  simp only [nFl, Dig, Col, Pos, Enum.length_prod, len_fin]
  norm_num [Dc, Kc, PE.BranchingProgram.w8, PE.BranchingProgram.Width.len]

def concreteCoinsBound : Bnd :=
  ((bCbd 16 6 65536).count 55340330084525408256).seq
    (((bEntF 65536 400).count 1435599410829755540307968).seq
      ((bCbd 16 6 65536).count 16777216))

theorem encCoinsBound_eq : encCoinsBound Dc 16 6 eFl = concreteCoinsBound := by
  unfold encCoinsBound
  rw [small_coefficient_count, flood_coefficient_count, eFl_def]
  have hk : Dc.K = 65536 := by change Kc = 65536; rw [Kc_def]; norm_num
  have hN : Dc.N = 16777216 := by norm_num [Dc]
  rw [hk, hN]
  rfl

set_option maxRecDepth 100000 in
theorem coins_threshold : concreteCoinsBound.S₀ ≤ 2 ^ 98 := by decide +kernel

set_option maxRecDepth 100000 in
theorem coins_output : concreteCoinsBound.a ≤ 2 ^ 98 := by decide +kernel

set_option maxRecDepth 100000 in
theorem coins_scratch : concreteCoinsBound.s ≤ 2 ^ 97 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem coins_time : concreteCoinsBound.T 0 (2 ^ 98) ≤ 2 ^ 250 := by decide +kernel

/-- Time and output length bounds of the actual encryption sampler, from a blank output. -/
theorem encCoins_bounds {ℓ : Fin 7 → ℕ} (hℓ : ℓ ≤ shp 0 0 (2 ^ 98)) :
    timeBoundT (encCoinsP Dc 16 6 eFl) ℓ ≤ 2 ^ 250 ∧
      ∀ i, lenBoundT (encCoinsP Dc 16 6 eFl) ℓ i ≤ 2 ^ 99 := by
  have h : ATBb (encCoinsP Dc 16 6 eFl) concreteCoinsBound := by
    rw [← encCoinsBound_eq]
    exact atbb_encCoinsP Dc 16 6 eFl
  have hb := h 0 (2 ^ 98) coins_threshold
  refine ⟨((timeBoundT_mono _ hℓ).trans hb.1).trans coins_time, ?_⟩
  have hl := (lenBoundT_mono (encCoinsP Dc 16 6 eFl) hℓ).trans hb.2
  intro i
  refine (hl i).trans ?_
  simp only [shp, Nat.zero_add]
  split_ifs
  · exact coins_output.trans (by norm_num)
  · exact (Nat.add_le_add_left coins_scratch (2 ^ 98)).trans (by norm_num)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem coins_time_loose : concreteCoinsBound.T (2 ^ 104) (2 ^ 104) ≤ 2 ^ 300 := by decide +kernel

/-- The coarse compiler bounds left by the parser need not assert a blank output. -/
theorem encCoins_bounds_loose {ℓ : Fin 7 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 104) :
    timeBoundT (encCoinsP Dc 16 6 eFl) ℓ ≤ 2 ^ 300 ∧
      ∀ i, lenBoundT (encCoinsP Dc 16 6 eFl) ℓ i ≤ 2 ^ 105 := by
  have h : ATBb (encCoinsP Dc 16 6 eFl) concreteCoinsBound := by
    rw [← encCoinsBound_eq]; exact atbb_encCoinsP Dc 16 6 eFl
  have hb := h (2 ^ 104) (2 ^ 104) (coins_threshold.trans (by norm_num))
  have hin : ℓ ≤ shp 0 (2 ^ 104) (2 ^ 104) := fun i => by simpa [shp] using hℓ i
  refine ⟨((timeBoundT_mono _ hin).trans hb.1).trans coins_time_loose, ?_⟩
  have hl := (lenBoundT_mono (encCoinsP Dc 16 6 eFl) hin).trans hb.2
  intro i
  refine (hl i).trans ?_
  simp only [shp]
  split_ifs
  · exact (Nat.add_le_add_left coins_output (2 ^ 104)).trans (by norm_num)
  · exact (Nat.add_le_add_left coins_scratch (2 ^ 104)).trans (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.EncConf
