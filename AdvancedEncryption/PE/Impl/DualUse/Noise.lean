import PE.Impl.DualUse.Scheme
import PE.Impl.RingBTVW.Noise

/-!
# Correctness of the dual-use scheme over `R_q`

The dual-use ciphertexts are those of `PE.Impl.RingBTVW` with the coins `aᵢ = B₀ Rᵢ` and
`eΨᵢ = e₀ Rᵢ` (`gswCts_eq`), so the noise is that of `PE.Impl.RingBTVW` plus `−e₀ k₀` (`noise_eq`),
and its bound follows (`cnorm_noise_le`): with binary `Rᵢ`, the Ring-GSW errors are at most
`|Wd| · N · Bχ`. Decryption is then correct when `4 · bound + 2 < q` (`decrypt_correct_of_bounds`).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib

variable {R : Type*} [CommRing R] {k : ℕ} {S : Setting R k} {Wd Wt : Type*} [Fintype Wd] [Fintype Wt]

/-- The public key of `PE.Impl.RingBTVW` with `B = 0` (both parts of `B` are counted apart). -/
def oldMPK (mpk : MPK S Wd Wt) : RingBTVW.MPK S := ⟨0, mpk.Bj, mpk.p⟩

/-- The coins of `PE.Impl.RingBTVW`: `aᵢ = B₀ Rᵢ`, `eΨᵢ = e₀ Rᵢ`, and no error against `B`. -/
def oldCoins (mpk : MPK S Wd Wt) (r : EncCoins S Wd Wt) : RingBTVW.EncCoins S :=
  ⟨r.s, fun i => mpk.B₀ * r.Rm i, fun i => r.e₀ * r.Rm i, 0, r.ej, r.e'⟩

/-- The key of `PE.Impl.RingBTVW`: `(0, k₂)`. -/
def oldKey (sk : SecretKey Wd Wt (R := R) (k := k)) : RingBTVW.SecretKey (R := R) (k := k) :=
  ⟨0, sk.k₂⟩

omit [Fintype Wt] in
theorem gswPK_mul (s : R) (B₀ e₀ : Matrix (Fin 1) Wd R) (Rm : Matrix Wd (Col k) R) :
    gswPK B₀ (scalar s * B₀ + e₀) * Rm = stackKey (B₀ * Rm) (e₀ * Rm) s := by
  ext a c
  fin_cases a <;>
    simp [gswPK, stackKey, RingBTVW.scalar, Matrix.mul_apply, Finset.mul_sum, add_mul,
      Finset.sum_add_distrib, mul_assoc]

omit [Fintype Wt] in
theorem gswCts_eq (mpk : MPK S Wd Wt) (x : S.Attr → Bool) (r : EncCoins S Wd Wt) :
    gswCts mpk x r = fun i => stackKey ((oldCoins mpk r).a i) ((oldCoins mpk r).eΨ i) r.s +
      bitR (R := R) (x i) • S.Γ.G := by
  funext i
  simp only [gswCts, gswPK_mul, oldCoins]

/-- **The noise** is that of `PE.Impl.RingBTVW` minus `e₀ k₀ + e₁ k₁`. -/
theorem noise_eq (mpk : MPK S Wd Wt) (x : S.Attr → Bool) (f : S.Pred)
    (sk : SecretKey Wd Wt (R := R) (k := k)) (r : EncCoins S Wd Wt) :
    noise mpk x f sk r = RingBTVW.noise (oldMPK mpk) x f (oldKey sk) (oldCoins mpk r) -
      (r.e₀ * sk.k₀ + r.e₁ * sk.k₁) 0 0 := by
  simp only [noise, RingBTVW.noise, gswCts_eq, oldMPK, oldKey, oldCoins, Matrix.add_apply,
    Matrix.zero_mul, Matrix.zero_apply]
  ring

section Ring

variable {N q : ℕ} [NeZero q] (hk : q < 2 ^ k) {Attr : Type} [Fintype Attr]

/-- The noise bound: that of `PE.Impl.RingBTVW` with errors at most `|Wd| · N · Bχ`, plus the
term of `e₀ k₀`. -/
noncomputable def noiseBound (Bχ K : ℕ) (f : SLP Attr × Wire Attr) : ℕ :=
  RingBTVW.noiseBound (N := N) hk (Fintype.card Wd * N * Bχ) K f +
    (Fintype.card Wd * N * Bχ * K + Fintype.card Wt * N * Bχ * K)

omit [Fintype Attr] in
/-- **The noise is bounded** by the errors of `Enc`, the binary `Rᵢ` and the key. -/
theorem cnorm_noise_le (mpk : MPK (ringSetting N q k hk Attr) Wd Wt) (x : Attr → Bool)
    (f : SLP Attr × Wire Attr) (sk : SecretKey Wd Wt (R := Negacyclic (ZMod q) N) (k := k))
    (r : EncCoins (ringSetting N q k hk Attr) Wd Wt) (Bχ K : ℕ) (hN : 0 < N) (hW : 0 < Fintype.card Wd)
    (he' : cnorm r.e' ≤ Bχ) (he₀ : rnorm r.e₀ ≤ Bχ) (he₁ : rnorm r.e₁ ≤ Bχ)
    (hR : ∀ i c c', cnorm (r.Rm i c c') ≤ 1) (hej : ∀ j, rnorm (r.ej j) ≤ Bχ)
    (hk₀ : ∀ c d, cnorm (sk.k₀ c d) ≤ K)
    (hk₁ : ∀ c d, cnorm (sk.k₁ c d) ≤ K) (hk₂ : ∀ c d, cnorm (sk.k₂ c d) ≤ K) :
    cnorm (noise mpk x f sk r) ≤ noiseBound (Wd := Wd) (Wt := Wt) (N := N) hk Bχ K f := by
  have hle : Bχ ≤ Fintype.card Wd * N * Bχ :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos hW hN)
  rw [show noise mpk x f sk r = _ from noise_eq (S := ringSetting N q k hk Attr) mpk x f sk r]
  refine (cnorm_sub_le _ _).trans (Nat.add_le_add ?_ ?_)
  · refine RingBTVW.cnorm_noise_le hk _ x f _ _ _ K (he'.trans hle)
      (by simp [oldCoins, rnorm_zero]) (fun i => ?_) (fun j => (hej j).trans hle)
      (fun c d => by simp [oldKey, cnorm_zero]) hk₂
    have := rnorm_mul_le r.e₀ (r.Rm i) 1 (hR i)
    simp only [oldCoins]
    calc rnorm (r.e₀ * r.Rm i) ≤ Fintype.card Wd * N * rnorm r.e₀ * 1 := this
      _ ≤ Fintype.card Wd * N * Bχ := by rw [mul_one]; exact Nat.mul_le_mul_left _ he₀
  · rw [Matrix.add_apply]
    refine (cnorm_add_le _ _).trans (Nat.add_le_add ?_ ?_)
    · refine (cnorm_le_rnorm _ 0).trans ((rnorm_mul_le r.e₀ sk.k₀ K hk₀).trans ?_)
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he₀)
    · refine (cnorm_le_rnorm _ 0).trans ((rnorm_mul_le r.e₁ sk.k₁ K hk₁).trans ?_)
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he₁)

omit [Fintype Attr] in
/-- **Correctness from bounds.** If `f(x) = 0`, the key is valid, the errors of `Enc` have
coefficients at most `Bχ`, the `Rᵢ` are binary, the key coefficients are at most `K` and
`4 · noiseBound + 2 < q`, decryption returns `M`. -/
theorem decrypt_correct_of_bounds (hN : 0 < N) (hW : 0 < Fintype.card Wd)
    (mpk : MPK (ringSetting N q k hk Attr) Wd Wt) (x : Attr → Bool) (M : Bool)
    (r : EncCoins (ringSetting N q k hk Attr) Wd Wt) (f : SLP Attr × Wire Attr)
    (sk : SecretKey Wd Wt) (hsk : ValidKey mpk f sk) (hfx : SLP.evalBool x f.1 f.2 = false)
    (Bχ K : ℕ) (he' : cnorm r.e' ≤ Bχ) (he₀ : rnorm r.e₀ ≤ Bχ) (he₁ : rnorm r.e₁ ≤ Bχ)
    (hR : ∀ i c c', cnorm (r.Rm i c c') ≤ 1) (hej : ∀ j, rnorm (r.ej j) ≤ Bχ)
    (hk₀ : ∀ c d, cnorm (sk.k₀ c d) ≤ K)
    (hk₁ : ∀ c d, cnorm (sk.k₁ c d) ≤ K) (hk₂ : ∀ c d, cnorm (sk.k₂ c d) ≤ K)
    (hq : 4 * noiseBound (Wd := Wd) (Wt := Wt) (N := N) hk Bχ K f + 2 < q) :
    decodeBit hN (decryptRaw mpk f sk (encrypt mpk x M r)) = M := by
  have hfx' : ((ringSetting N q k hk Attr).circ f).eval
      (fun i => bitR (R := Negacyclic (ZMod q) N) (x i)) = 0 := by
    have := Circuit.eval_bits (R := Negacyclic (ZMod q) N) x (f.1.circuit f.2)
    rw [SLP.evalBool_circuit, hfx] at this
    simp only [bitR]
    exact this.trans (by simp)
  rw [decryptRaw_eq (ringSetting_fhatCorrect hk Attr) mpk x M r f sk hsk hfx']
  have hM : (if M then (ringSetting N q k hk Attr).half else 0) =
      algebraMap (ZMod q) (Negacyclic (ZMod q) N) (encodeBit q M) := by
    cases M <;> simp [ringSetting, encodeBit]
  rw [hM]
  refine decodeBit_encodeBit_add hN M _ ?_
  have h := (zabs_coeffs_le_cnorm _ ⟨0, hN⟩).trans
    (cnorm_noise_le hk mpk x f sk r Bχ K hN hW he' he₀ he₁ hR hej hk₀ hk₁ hk₂)
  have h' : |((noise mpk x f sk r).coeffs ⟨0, hN⟩).valMinAbs| ≤
      (noiseBound (Wd := Wd) (Wt := Wt) (N := N) hk Bχ K f : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h
  omega

end Ring

end AdvancedEncryption.DualUse
