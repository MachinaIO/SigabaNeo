import PE.Impl.RingBTVW.Fresh.Scheme

/-!
# The dual-use scheme

BTVW17 §4.2 with the paper's Ring-GSW ciphertexts: the attribute ciphertexts are
`Ψᵢ = A Rᵢ + xᵢ G` with `A = [B₀; c₀]`, the row `B₀` of the public key and its BGG+ encoding
`c₀ = s B₀ + e₀` ("dual use"), and binary `Rᵢ`. The public key is `B = [B₀ | B₁]`: `B₀` is uniform
(the seed of the leftover hash lemma in the security proof), `B₁` carries the trapdoor; `Wd` and
`Wt` index their columns. A key for
`f` is `sk = (k₀, k₁, k₂)` with `B₀ k₀ + B₁ k₁ + B_f̂ k₂ = p`.

The parameters (`Setting`: gadget, bit decompositions, `f̂`, `⌊q/2⌋`) are those of
`PE.Impl.RingBTVW.Fresh.Scheme`.

**Correctness** (`decryptRaw_eq`): if `f(x) = 0` and the key is valid, `κ − κ' = M ⌊q/2⌋ + noise`.
The Ring-GSW error of `Ψᵢ` is `−e₀ Rᵢ`.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh

variable {R : Type*} [CommRing R] {k : ℕ} (S : Setting R k) (Wd Wt : Type*) [Fintype Wd] [Fintype Wt]

/-- The master public key. -/
structure MPK where
  /-- `B₀`: uniform. -/
  B₀ : Matrix (Fin 1) Wd R
  /-- `B₁`: with a trapdoor. -/
  B₁ : Matrix (Fin 1) Wt R
  /-- `B_j` for every bit `j` of the attribute ciphertexts. -/
  Bj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R
  /-- `p`. -/
  p : R

/-- The coins of encryption. -/
structure EncCoins where
  /-- The secret. -/
  s : R
  /-- The error of `c₀`. -/
  e₀ : Matrix (Fin 1) Wd R
  /-- The error of `c₁`. -/
  e₁ : Matrix (Fin 1) Wt R
  /-- The binary matrices of the Ring-GSW ciphertexts. -/
  Rm : S.Attr → Matrix Wd (Col k) R
  /-- The errors of the encodings. -/
  ej : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R
  /-- The error of `κ`. -/
  e' : R

/-- A ciphertext. -/
structure Ciphertext where
  /-- The Ring-GSW ciphertexts of the attribute bits. -/
  Ψ : S.Attr → Matrix (Fin 2) (Col k) R
  /-- `c₀ = s B₀ + e₀`. -/
  c₀ : Matrix (Fin 1) Wd R
  /-- `c₁ = s B₁ + e₁`. -/
  c₁ : Matrix (Fin 1) Wt R
  /-- The encodings of the bits of `Ψ`. -/
  cj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R
  /-- `κ`. -/
  κ : R

/-- A secret key `[k₀; k₁; k₂]`. -/
structure SecretKey where
  /-- The part against `B₀`. -/
  k₀ : Matrix Wd (Fin 1) R
  /-- The part against `B₁`. -/
  k₁ : Matrix Wt (Fin 1) R
  /-- The part against `B_f̂`. -/
  k₂ : Matrix (Col k) (Fin 1) R

variable {S Wd Wt}

/-- `A = [B₀; c₀]`. -/
def gswPK (B₀ c₀ : Matrix (Fin 1) Wd R) : Matrix (Fin 2) Wd R :=
  Matrix.of fun a c => if a = 0 then B₀ 0 c else c₀ 0 c

/-- The Ring-GSW ciphertexts `Ψᵢ = A Rᵢ + xᵢ G`. -/
def gswCts (mpk : MPK S Wd Wt) (x : S.Attr → Bool) (r : EncCoins S Wd Wt) :
    S.Attr → Matrix (Fin 2) (Col k) R :=
  fun i => gswPK mpk.B₀ (scalar r.s * mpk.B₀ + r.e₀) * r.Rm i + bitR (R := R) (x i) • S.Γ.G

/-- **Enc.** -/
def encrypt (mpk : MPK S Wd Wt) (x : S.Attr → Bool) (M : Bool) (r : EncCoins S Wd Wt) :
    Ciphertext S Wd Wt :=
  { Ψ := gswCts mpk x r
    c₀ := scalar r.s * mpk.B₀ + r.e₀
    c₁ := scalar r.s * mpk.B₁ + r.e₁
    cj := fun j => scalar r.s * (mpk.Bj j - bitsOf S (gswCts mpk x r) j • S.Γ₁.G) + r.ej j
    κ := r.s * mpk.p + r.e' + (if M then S.half else 0) }

/-- `B_f̂ = ∑_b EvalF(f̂_b, B) · G̲⁻¹(V_b)`. -/
def keyMatrix (mpk : MPK S Wd Wt) (f : S.Pred) : Matrix (Fin 1) (Col k) R :=
  ∑ b, slpPK S.Γ₁ mpk.Bj (S.fhat f).1 ((S.fhat f).2 b) * S.Γ₁.ginv (S.rowBits.V b)

/-- A valid key: `B₀ k₀ + B₁ k₁ + B_f̂ k₂ = p`. -/
def ValidKey (mpk : MPK S Wd Wt) (f : S.Pred) (sk : SecretKey Wd Wt (R := R) (k := k)) : Prop :=
  mpk.B₀ * sk.k₀ + mpk.B₁ * sk.k₁ + keyMatrix mpk f * sk.k₂ = scalar mpk.p

/-- `c_f̂ = ∑_b EvalFX(f̂_b, ψ, c) · G̲⁻¹(V_b) + Ψ̄_f`. -/
def evalCiphertext (mpk : MPK S Wd Wt) (f : S.Pred) (ct : Ciphertext S Wd Wt) :
    Matrix (Fin 1) (Col k) R :=
  ∑ b, slpEnc S.Γ₁ mpk.Bj (bitsOf S ct.Ψ) ct.cj (S.fhat f).1 ((S.fhat f).2 b) *
      S.Γ₁.ginv (S.rowBits.V b) +
    botRow (evalMat S.Γ ct.Ψ (S.circ f))

/-- **Dec**, before rounding: `κ − [c₀ | c₁ | c_f̂] sk`. -/
def decryptRaw (mpk : MPK S Wd Wt) (f : S.Pred) (sk : SecretKey Wd Wt (R := R) (k := k))
    (ct : Ciphertext S Wd Wt) : R :=
  ct.κ - (ct.c₀ * sk.k₀ + ct.c₁ * sk.k₁ + evalCiphertext mpk f ct * sk.k₂) 0 0

/-- The noise of decryption: `e' − [e₀ | e₁ | E_BGG − E_GSW] sk`. -/
def noise (mpk : MPK S Wd Wt) (x : S.Attr → Bool) (f : S.Pred) (sk : SecretKey Wd Wt (R := R) (k := k))
    (r : EncCoins S Wd Wt) : R :=
  let eBgg := ∑ b, slpEnc S.Γ₁ mpk.Bj (bitsOf S (gswCts mpk x r)) r.ej (S.fhat f).1
    ((S.fhat f).2 b) * S.Γ₁.ginv (S.rowBits.V b)
  let eGsw := evalErr S.Γ (gswCts mpk x r) (fun i => bitR (R := R) (x i))
    (fun i => -(r.e₀ * r.Rm i)) (S.circ f)
  r.e' - (r.e₀ * sk.k₀ + r.e₁ * sk.k₁ + (eBgg - eGsw) * sk.k₂) 0 0

omit [Fintype Wd] in
theorem gswSecret_mul_gswPK (s : R) (B₀ e₀ : Matrix (Fin 1) Wd R) :
    gswSecret s * gswPK B₀ (scalar s * B₀ + e₀) = -e₀ := by
  ext a c
  fin_cases a
  simp [gswSecret, gswPK, RingBTVW.Fresh.scalar, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Correctness, exactly.** If `f(x) = 0`, the key is valid and `f̂` computes the Ring-GSW
evaluation, then `κ − κ' = M ⌊q/2⌋ + noise`. -/
theorem decryptRaw_eq (hfhat : S.FhatCorrect) (mpk : MPK S Wd Wt) (x : S.Attr → Bool) (M : Bool)
    (r : EncCoins S Wd Wt) (f : S.Pred) (sk : SecretKey Wd Wt (R := R) (k := k))
    (hsk : ValidKey mpk f sk) (hfx : (S.circ f).eval (fun i => bitR (R := R) (x i)) = 0) :
    decryptRaw mpk f sk (encrypt mpk x M r) = (if M then S.half else 0) + noise mpk x f sk r := by
  set Ψ := gswCts mpk x r with hΨ
  have hinv : ∀ i, gswSecret r.s * Ψ i =
      bitR (R := R) (x i) • (gswSecret r.s * S.Γ.G) + -(r.e₀ * r.Rm i) := by
    intro i
    rw [hΨ, gswCts, Matrix.mul_add, ← Matrix.mul_assoc, gswSecret_mul_gswPK, Matrix.mul_smul,
      Matrix.neg_mul]
    abel
  have hgsw := gsw_invariant S.Γ (gswSecret r.s) Ψ (fun i => bitR (R := R) (x i))
    (fun i => -(r.e₀ * r.Rm i)) hinv (S.circ f)
  rw [hfx, zero_smul, zero_add] at hgsw
  have hbgg : ∀ b, slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) (encrypt mpk x M r).cj (S.fhat f).1
      ((S.fhat f).2 b) =
      scalar r.s * (slpPK S.Γ₁ mpk.Bj (S.fhat f).1 ((S.fhat f).2 b) -
          S.rowBits.bits (topRow (evalMat S.Γ Ψ (S.circ f))) b • S.Γ₁.G) +
        slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f).1 ((S.fhat f).2 b) := by
    intro b
    rw [← hfhat f Ψ b]
    exact slp_enc_key_relation S.Γ₁ (scalar r.s) mpk.Bj (bitsOf S Ψ) _ r.ej (fun j => rfl) _ _
  have hmat := matrix_key_relation_bits S.Γ₁ S.rowBits (scalar r.s)
    (fun b => slpPK S.Γ₁ mpk.Bj (S.fhat f).1 ((S.fhat f).2 b)) (topRow (evalMat S.Γ Ψ (S.circ f)))
    (fun b => slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) (encrypt mpk x M r).cj (S.fhat f).1 ((S.fhat f).2 b))
    (fun b => slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f).1 ((S.fhat f).2 b)) hbgg
  have hcf : evalCiphertext mpk f (encrypt mpk x M r) =
      scalar r.s * keyMatrix mpk f +
        (∑ b, slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f).1 ((S.fhat f).2 b) *
          S.Γ₁.ginv (S.rowBits.V b) -
          evalErr S.Γ Ψ (fun i => bitR (R := R) (x i)) (fun i => -(r.e₀ * r.Rm i)) (S.circ f)) := by
    have ht := gswSecret_mul r.s (evalMat S.Γ Ψ (S.circ f))
    rw [hgsw] at ht
    simp only [evalCiphertext, encrypt, keyMatrix] at hmat ⊢
    rw [hmat, Matrix.mul_sub]
    rw [show botRow (evalMat S.Γ Ψ (S.circ f)) = scalar r.s * topRow (evalMat S.Γ Ψ (S.circ f)) -
        evalErr S.Γ Ψ (fun i => bitR (R := R) (x i)) (fun i => -(r.e₀ * r.Rm i)) (S.circ f) by
      rw [ht]; abel]
    abel
  have hsk' := congrArg (fun m => (scalar r.s * m) 0 0) hsk
  simp only [Matrix.mul_add, ← Matrix.mul_assoc] at hsk'
  simp only [decryptRaw, noise, hcf]
  simp only [encrypt, Matrix.add_mul, Matrix.add_apply] at hsk' ⊢
  simp only [RingBTVW.Fresh.scalar, Matrix.mul_apply, Matrix.of_apply, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton] at hsk' ⊢
  simp only [Matrix.sub_apply] at hsk' ⊢
  rw [← hsk']
  simp only [mul_assoc]
  ring

end AdvancedEncryption.RingBTVW
