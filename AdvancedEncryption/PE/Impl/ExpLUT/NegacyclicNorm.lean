import PE.Impl.ExpLUT.Canonical
import PE.Impl.ExpLUT.Noise
import SigabaNeo.Lib.Lattices.Automorphism.Instance
import SigabaNeo.Lib.Lattices.Automorphism.Norm
import SigabaNeo.Lib.Lattices.Homomorphic.BinaryDigits

/-!
# The coefficient norm of `ℤ_q[X]/(X^n + 1)` as a `NormSpec`

For `n = 2^e`, the ring `Negacyclic (ZMod q) n` with automorphisms `expRingOf n b w …`
(`SigabaNeo.Lib.Lattices.Automorphism.Instance`, e.g. `expRingMersenne` for `q = 2^K − 1`) and the
binary gadget digits (`binaryDigits`), with `idx j = g^j` (`canonSetting`):

* `binaryDigits_g`: the gadget entries are natural numbers `2^i` (so the automorphisms fix them);
* `cnorm_mul_monoX_pow_le`: multiplying by `X^p` does not increase `cnorm`;
* `cnorm_binaryDigit_le`: binary digits have `cnorm ≤ 1`;
* **`cnormSpec`**: the centered coefficient norm `cnorm` satisfies `NormSpec` (automorphisms by
  `SigabaNeo.Lattices.cnorm_aut`).
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Cslib

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
theorem cnorm_mul_monoX_le {n : ℕ} (a : Negacyclic (ZMod q) n) : cnorm (a * monoX n) ≤ cnorm a := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cnorm_le_iff]; intro j; exact j.elim0
  rw [cnorm_le_iff]; intro i
  rw [mul_monoX hn]
  split_ifs
  · exact zabs_coeffs_le_cnorm a _
  · rw [zabs_neg]; exact zabs_coeffs_le_cnorm a _

omit [NeZero q] in
/-- **Monomials do not increase the norm.** -/
theorem cnorm_mul_monoX_pow_le {n : ℕ} (p : ℕ) (a : Negacyclic (ZMod q) n) :
    cnorm (monoX n ^ p * a) ≤ cnorm a := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show monoX n ^ (p + 1) * a = (monoX n ^ p * a) * monoX n by ring]
    exact (cnorm_mul_monoX_le _).trans ih

theorem cnorm_binaryDigit_le {n : ℕ} (a : Negacyclic (ZMod q) n) (i : ℕ) : cnorm (binaryDigit a i) ≤ 1 := by
  rw [cnorm_le_iff]; intro j
  rw [coeffs_binaryDigit]
  split_ifs
  · exact zabs_one_le
  · simp [zabs_zero]

theorem binaryDigits_g {n τ : ℕ} (hτ : q ≤ 2 ^ τ) (i : Fin τ) :
    ∃ m : ℕ, (binaryDigits n q τ hτ).g i = m :=
  ⟨2 ^ (i : ℕ), by
    show algebraMap (ZMod q) (Negacyclic (ZMod q) n) (2 ^ (i : ℕ)) = _
    rw [← map_natCast (algebraMap (ZMod q) (Negacyclic (ZMod q) n)), Nat.cast_pow, Nat.cast_ofNat]⟩

/-- **The coefficient norm is a `NormSpec`** for the canonical setting over `ℤ_q[X]/(X^{2^e} + 1)`
with binary digits. -/
noncomputable def cnormSpec (e b : ℕ) (w : ZMod q) (hw : (2 : ZMod q) ^ b * w = 1) (hn : 0 < 2 ^ e)
    (hW : 2 ^ b ∣ 2 ^ e) (hlt : 2 ^ b < 2 ^ e) (h2 : 2 * 2 ^ b ∣ 2 ^ e) {τ : ℕ} (hτ : q ≤ 2 ^ τ) :
    NormSpec (canonSetting (expRingOf (2 ^ e) b w hw hn hW hlt) rfl h2 (binaryDigits (2 ^ e) q τ hτ)
      (binaryDigits_g hτ)) where
  nrm := cnorm
  nrm_zero := cnorm_zero
  nrm_add := cnorm_add_le
  nrm_neg := cnorm_neg
  nrm_mul := cnorm_mul_le
  nrm_digit a i := cnorm_binaryDigit_le a i
  nrm_X_pow_mul p a := cnorm_mul_monoX_pow_le p a
  nrm_σ k a hk := by
    show cnorm (autσ (2 ^ e) k a) ≤ cnorm a
    rw [autσ_of_odd hk, cnorm_aut (coprime_pow_two hk e)]

end AdvancedEncryption.ExpLUT
