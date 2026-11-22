import PE.Impl.DualUse.ImplCorrect
import PE.Impl.DualUse.ParamSupport
import PE.Impl.DualUse.KeyBoxes
import PE.Impl.DualUse.ConcreteNoise

/-!
# A correct implementation for date windows

Concrete parameters of the dual-use scheme: `q = 2^K` with `K = 2^24`, `k = K + 1` binary digits,
`N = 2^10`, `|Wd| = 2^35`, errors from the centered binomial law of width `16`, flooding errors
below `2^512`, and boxes of `512`-bit coefficients for key generation (`conf`). Every condition
of `DualUse.correct` holds, so the implementation `impl hkc conf` is correct
(`correct_concrete`) and expressive (`expressive_concrete`).

The sizes `K` and `|Wd|` are opaque (`irreducible_def`): no power `2^K` is evaluated and `Fin |Wd|`
is never enumerated, by the elaborator or the kernel.
-/

namespace AdvancedEncryption.DualUse.Concrete

set_option maxRecDepth 100000

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped ENNReal

/-- The error law: centered binomial of width `16`. -/
noncomputable def χc : PMF (ZMod (2 ^ Kc)) :=
  SigabaNeo.Lattices.ModuleLWE.coeffLaw (2 ^ Kc) (SigabaNeo.Lattices.SecretDist.cbd 16)

theorem χc_short : ∀ e ∈ χc.support, zabs e ≤ 16 := by
  intro e he
  simp only [χc, ModuleLWE.coeffLaw, PMF.mem_support_map_iff] at he
  obtain ⟨ab, -, rfl⟩ := he
  rw [← Int.cast_sub]
  refine (zabs_intCast_le (q := 2 ^ Kc) _).trans ?_
  have h1 := Finset.card_le_univ (Finset.univ.filter fun i => ab.1 i)
  have h2 := Finset.card_le_univ (Finset.univ.filter fun i => ab.2 i)
  simp only [Fintype.card_fin] at h1 h2
  omega

/-- The shift of the real trapdoor. -/
def τc : ℕ := (Fintype.card (Col kc) * Nc) ^ 2 * 16

theorem τc_le : τc ≤ 2 ^ 76 := by
  have h : τc ≤ (2 ^ 36) ^ 2 * 16 := Nat.mul_le_mul_right 16 (Nat.pow_le_pow_left WN_le 2)
  have e : ((2 : ℕ) ^ 36) ^ 2 * 16 = 2 ^ 76 := by
    rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_add]
  exact h.trans (le_of_eq e)

/-- The radius of the small box. -/
def Sc : ℕ := 2 ^ 511 - 1 - τc

theorem hBc : 2 ^ 512 ≤ 2 ^ Kc := pow_le_pow' (by rw [Kc_def]; norm_num)

/-- A column of the gadget. -/
def c₀ : Col kc := (0, ⟨0, Nat.succ_pos _⟩)

/-- The binary decomposition of a ring element. -/
noncomputable def decc (u : Rg Nc Kc) : Col kc → Rg Nc Kc := fun c =>
  (Sdw (N := Nc) hkc).Γ₁.ginv (Matrix.of fun _ _ => u) c c₀

/-- The number of coins of the big box. -/
def mBc : ℕ := (dc + (1 + (2 * kc + 2 * kc))) * Nc * 512

theorem card_coef :
    Fintype.card (Coef dc (TrapCol kc) Nc) = (dc + (1 + (2 * kc + 2 * kc))) * Nc := by
  rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_sum,
    Fintype.card_sum, Fintype.card_fin, card_col]

theorem hmBc : Fintype.card (Coef dc (TrapCol kc) Nc) * 512 = mBc := by rw [card_coef]; rfl

/-- **The parameters.** -/
noncomputable def conf : Conf Nc Kc kc where
  hN := Nat.pos_of_ne_zero (by unfold Nc; positivity)
  d := dc
  χc := χc
  mχ := 16 + 16
  hχ := BitLaw.cbd 16
  w := 512
  mB := mBc
  emb := keyEmb 512 hBc mBc hmBc
  Small := keyBall (2 ^ Kc) dc (TrapCol kc) Nc Sc
  dec := decc
  L := dateBound

/-- The inner box. -/
noncomputable def innerc : Finset (KeyShort (Fin dc) (TrapCol kc) (Rg Nc Kc)) :=
  keyBall (2 ^ Kc) dc (TrapCol kc) Nc (2 ^ 511 - 1 - 2 * τc)

theorem hdecc (u : Rg Nc Kc) : gadgetMap (S := Sdw (N := Nc) hkc) (decc u) = u := by
  have h := congrFun (congrFun ((Sdw (N := Nc) hkc).Γ₁.mul_ginv (Matrix.of fun _ _ => u)) 0) c₀
  simp only [Matrix.mul_apply, Matrix.of_apply] at h
  exact h

theorem cnorm_decc (u : Rg Nc Kc) (c : Col kc) : cnorm (decc u c) ≤ 1 :=
  cnorm_gadgetOf_binary_ginv_le hkc.le (fun _ : Fin 1 => (0 : Fin 2)) _ _ c c₀

theorem big_eq :
    conf.Big = Finset.univ.map (keyEmb (d := dc) (Wt := TrapCol kc) (N := Nc) 512 hBc mBc hmBc) :=
  rfl

theorem ball_sub_big : keyBall (2 ^ Kc) dc (TrapCol kc) Nc (2 ^ 511 - 1) ⊆ conf.Big := by
  rw [big_eq]; exact keyBall_subset_big 512 hBc (by norm_num) mBc hmBc

/-- The shift of the real trapdoor for a key of `Setup`. -/
theorem shift_short (v : PK hkc conf × SKey hkc conf) (hv : v ∈ (setupM hkc conf).support)
    (Bf : Matrix (Fin 1) (Col kc) (Rg Nc Kc)) (u : Rg Nc Kc) :
    ∀ i, zabs (keyEquiv (realTrap (Wd := Fin dc) (S := Sdw (N := Nc) hkc)
      (trapMat v.2.2.1 v.2.2.2) Bf (decc u)) i) ≤ τc := by
  obtain ⟨he, ht⟩ := setup_trapdoor_short hkc conf χc_short v hv
  obtain ⟨-, h2⟩ := cnorm_realTrap_le hkc conf (by norm_num) v.2.2.1 v.2.2.2 he ht Bf (decc u)
    (cnorm_decc u)
  refine zabs_keyEquiv_le (fun i => ?_) h2
  show cnorm ((0 : Fin dc → Rg Nc Kc) i) ≤ τc
  simp [cnorm_zero]

theorem card_coef_le : Fintype.card (Coef dc (TrapCol kc) Nc) ≤ 2 ^ 46 := by
  rw [card_coef, dc_def]
  have := kc_le
  unfold Nc
  have h : 2 ^ 35 + (1 + (2 * kc + 2 * kc)) ≤ 2 ^ 36 := by omega
  calc (2 ^ 35 + (1 + (2 * kc + 2 * kc))) * 2 ^ 10 ≤ 2 ^ 36 * 2 ^ 10 := Nat.mul_le_mul_right _ h
    _ = 2 ^ 46 := by rw [← pow_add]

/-- **The implementation is correct.** -/
theorem correct_concrete (M : SEMachines hkc conf) : Correct dateUniverse params (impl hkc conf M) := by
  have hτ := τc_le
  refine DualUse.correct hkc conf (by show 0 < dc; rw [dc_def]; positivity) hdecc (2 ^ 512) Sc
    innerc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the inner box lies in the big box
    exact (keyBall_mono (by omega)).trans ball_sub_big
  · -- coverage
    intro v hv w y hy u
    exact ball_sub_big (keyBall_mono (by unfold Sc; omega) (add_mem_keyBall hy (shift_short v hv _ u)))
  · -- the inner box shifted stays in the small box
    intro v hv w p hp u
    exact keyBall_mono (by unfold Sc; omega) (sub_mem_keyBall hp (shift_short v hv _ u))
  · -- the abort probability
    have h4 : 4 * τc + 1 ≤ 2 ^ 79 := by omega
    have hprod := pow_mul_le' (pow_mul_le' card_coef_le h4 rfl) (le_refl ((2 : ℕ) ^ 128))
      (rfl : 46 + 79 + 128 = 253)
    have hab := abort_le (d := dc) (Wt := TrapCol kc) (N := Nc) 512 τc 128 hBc (by norm_num)
      mBc hmBc (h4.trans (pow_le_pow' (by norm_num))) (hprod.trans (pow_le_pow' (by norm_num)))
    rw [show 512 - 1 = 511 from rfl] at hab
    exact hab
  · -- the small box is short
    intro v hv
    exact cnorm_of_mem_keyBall hv
  · -- the decomposition is short
    intro u i
    exact (cnorm_decc u i).trans (by unfold Sc; omega)
  · -- the coins are short
    refine coins_short hkc conf χc_short ?_
    show (16 : ℕ) ≤ 2 ^ 512
    calc (16 : ℕ) = 2 ^ 4 := rfl
      _ ≤ 2 ^ 512 := pow_le_pow' (by norm_num)
  · -- the noise
    intro w
    refine noise_ok _ ?_ Sc (by unfold Sc; omega)
    simp only [predC, winWord, parse_unparse, predOf, fromGates, List.length_map]
    exact length_winGates w

attribute [local irreducible] dateBound in
theorem conf_L : conf.L = dateBound := rfl

/-- **The implementation is expressive.** -/
theorem expressive_concrete (M : SEMachines hkc conf) : Expressive dateUniverse params (impl hkc conf M) :=
  DualUse.expressive hkc conf M (le_of_eq conf_L.symm)

end AdvancedEncryption.DualUse.Concrete
