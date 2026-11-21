import SigabaNeo.Lib.Lattices.Homomorphic
import SigabaNeo.Lib.Lattices.Decode

/-!
# The ring variant of the BTVW17 §4.2 predicate encryption

The weakly attribute-hiding predicate encryption of Brakerski–Tsabary–Vaikuntanathan–Wee
(ePrint 2017/795, §4.2, the "dual use" technique) over a ring, with the LWE dimension `n = 1`:
over `R_q = ℤ_q[X]/(X^N + 1)` (`ringSetting`) it rests on Ring-LWE. The same secret `s` is the
Ring-GSW secret of the attribute ciphertexts `Ψᵢ` and the BGG+ secret of the encodings of their bits.

With columns `W = Fin 2 × Fin k`, the Ring-GSW gadget `G ∈ R^{2×W}` and its top row `G̲ ∈ R^{1×W}`:

* `Setup`: a matrix `B ∈ R^{1×W}` with a trapdoor, `B_j ∈ R^{1×W}` for every bit `j` of the
  attribute ciphertexts, and `p ∈ R` (`MPK`).
* `Enc(mpk, x, M)` (`encrypt`, coins `EncCoins`): `Ψᵢ = [B; sB + e] Rᵢ + xᵢ G`; with `ψ` the bits of
  `Ψ`, `c₀ = sB + e₀`, `c_j = s(B_j − ψ_j G̲) + e_j` and `κ = s p + e' + M ⌊q/2⌋`.
* `KeyGen(msk, f)`: `B_f̂ = ∑_b EvalF(f̂_b, B) · G̲⁻¹(V_b)` (`keyMatrix`), where `f̂_b` computes the bit
  `b` of the top row of `Ψ_f = FHE.Eval(f, Ψ)` from the bits of `Ψ`, and a short `sk` with
  `[B | B_f̂] sk = p` sampled with the trapdoor (`ValidKey`).
* `Dec(sk, f, ct)` (`decryptRaw`): `c_f̂ = ∑_b EvalFX(f̂_b, ψ, c) · G̲⁻¹(V_b) + Ψ̄_f` with `Ψ̄_f` the
  bottom row of `Ψ_f`, `κ' = [c₀ | c_f̂] sk`, and `κ − κ'`, decoded at the constant coefficient
  (`decrypt`).

**Correctness** (BTVW17 Theorem 4.1). If `f(x) = 0`, then `κ − κ' = M ⌊q/2⌋ + noise` with the noise
given explicitly (`decryptRaw_eq`): it is `e'` minus `[e₀ | E_BGG − E_GSW] sk`, with `E_BGG` the
BGG+ evaluation error and `E_GSW` the Ring-GSW evaluation error. Over `R_q`, decryption returns `M`
when the constant coefficient of the noise is below `q/4` (`decrypt_correct`), and so does the
whole scheme for any coins of `Setup`, `KeyGen` and `Enc` (`scheme_correct`).

**Constructed.** Over `R_q` (`ringSetting`): the gadget digits and the bit decompositions; the
circuits `f̂` by truth tables (`truthTableFhat`, proved correct by `ringSetting_fhatCorrect`); the
trapdoor `B = [A₀ | g − A₀ T]` with exact preimages (`setup`, `keyGen`, `keyGen_valid`); the laws
of the coins (`PE.Impl.RingBTVW.Laws`).

**Security** (BTVW17 Theorem 4.2, Ring-LWE). The algebra of the simulation is proved: `Enc*`
(`encodings_sim`), `KeyGen*` (`keyMatrix_sim`) and the keys the simulator answers without the
trapdoor (`simKey_valid`).

**Not formalized here.**

* The statistical steps of the security proof: the leftover hash lemma for `A Rᵢ` and `B W'_j`,
  Gaussian preimages that hide the trapdoor (`keyGen` solves exactly, which is enough for
  correctness but reveals `T`), and noise flooding.
* The Ring-LWE step (`c = sB + e` against uniform) and the concrete security of `PE`.
* A bound on the noise (a hypothesis of `decrypt_correct`), and polynomial-size circuits `f̂`
  (`truthTableFhat` has exponential size).
* Machines: the algorithms are Lean functions, not the Turing machines of an `Impl`.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix

/-- The columns of the gadget matrices: two blocks of `k` digits. -/
abbrev Col (k : ℕ) := Fin 2 × Fin k

/-- The public parameters of the scheme: the gadget digits, the attribute positions, the bit
decompositions of Ring-GSW ciphertexts (the inputs of `f̂`) and of rows (the outputs of `f̂`), the
circuits `f̂`, and `⌊q/2⌋`. -/
structure Setting (R : Type*) [CommRing R] (k : ℕ) where
  /-- The gadget digits. -/
  D : GadgetDigits R k
  /-- The positions of the attribute bits. -/
  Attr : Type
  /-- The bits of a Ring-GSW ciphertext. -/
  ctBits : MatrixBits R (Fin 2) (Col k)
  /-- The bits of a row. -/
  rowBits : MatrixBits R (Fin 1) (Col k)
  /-- `f̂_b`: the bit `b` of the top row of `FHE.Eval(f, Ψ)`, from the bits of `Ψ`. -/
  fhat : Circuit Attr → rowBits.Index → Circuit (Attr × ctBits.Index)
  /-- `⌊q/2⌋`. -/
  half : R

variable {R : Type*} [CommRing R] {k : ℕ} (S : Setting R k)

/-- The Ring-GSW gadget. -/
abbrev Setting.Γ : GadgetMatrix R (Fin 2) (Col k) := gswGadget S.D

/-- The BGG+ gadget `G̲`. -/
abbrev Setting.Γ₁ : GadgetMatrix R (Fin 1) (Col k) := topRowGadget S.D

/-- The top row of a Ring-GSW ciphertext. -/
def topRow (Ψ : Matrix (Fin 2) (Col k) R) : Matrix (Fin 1) (Col k) R := Matrix.of fun _ c => Ψ 0 c

/-- The bottom row of a Ring-GSW ciphertext. -/
def botRow (Ψ : Matrix (Fin 2) (Col k) R) : Matrix (Fin 1) (Col k) R := Matrix.of fun _ c => Ψ 1 c

/-- The bits of the attribute ciphertexts, as BGG+ attributes. -/
def bitsOf (Ψ : S.Attr → Matrix (Fin 2) (Col k) R) : S.Attr × S.ctBits.Index → R :=
  fun j => S.ctBits.bits (Ψ j.1) j.2

/-- `f̂` computes the bits of the top row of the Ring-GSW evaluation. -/
def Setting.FhatCorrect : Prop :=
  ∀ (f : Circuit S.Attr) (Ψ : S.Attr → Matrix (Fin 2) (Col k) R) (b : S.rowBits.Index),
    (S.fhat f b).eval (bitsOf S Ψ) = S.rowBits.bits (topRow (evalMat S.Γ Ψ f)) b

/-- The master public key. -/
structure MPK where
  /-- `B`, generated with a trapdoor. -/
  B : Matrix (Fin 1) (Col k) R
  /-- `B_j` for every bit `j` of the attribute ciphertexts. -/
  Bj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R
  /-- `p`. -/
  p : R

/-- The coins of encryption. -/
structure EncCoins where
  /-- The secret. -/
  s : R
  /-- The error of the Ring-GSW ciphertexts. -/
  e : Matrix (Fin 1) (Col k) R
  /-- The error of `c₀`. -/
  e₀ : Matrix (Fin 1) (Col k) R
  /-- The errors of the encodings. -/
  ej : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R
  /-- The error of `κ`. -/
  e' : R
  /-- The Ring-GSW randomness, a `0/1` matrix for each attribute bit. -/
  Rm : S.Attr → Matrix (Col k) (Col k) R

/-- A ciphertext. -/
structure Ciphertext where
  /-- The Ring-GSW ciphertexts of the attribute bits. -/
  Ψ : S.Attr → Matrix (Fin 2) (Col k) R
  /-- `c₀`. -/
  c₀ : Matrix (Fin 1) (Col k) R
  /-- The encodings of the bits of `Ψ`. -/
  cj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R
  /-- `κ`. -/
  κ : R

/-- A secret key: `[k₁; k₂]`. -/
structure SecretKey where
  /-- The part against `B`. -/
  k₁ : Matrix (Col k) (Fin 1) R
  /-- The part against `B_f̂`. -/
  k₂ : Matrix (Col k) (Fin 1) R

/-- A scalar as a `1 × 1` matrix. -/
def scalar (a : R) : Matrix (Fin 1) (Fin 1) R := Matrix.of fun _ _ => a

/-- A bit as `0/1`. -/
def bitR (b : Bool) : R := if b then 1 else 0

variable {S}

/-- `[B; sB + e]`. -/
def stackKey (B e : Matrix (Fin 1) (Col k) R) (s : R) : Matrix (Fin 2) (Col k) R :=
  Matrix.of fun a c => if a = 0 then B 0 c else s * B 0 c + e 0 c

/-- **Enc.** -/
def encrypt (mpk : MPK S) (x : S.Attr → Bool) (M : Bool) (r : EncCoins S) : Ciphertext S :=
  let Ψ := fun i => stackKey mpk.B r.e r.s * r.Rm i + bitR (R := R) (x i) • S.Γ.G
  { Ψ := Ψ
    c₀ := scalar r.s * mpk.B + r.e₀
    cj := fun j => scalar r.s * (mpk.Bj j - bitsOf S Ψ j • S.Γ₁.G) + r.ej j
    κ := r.s * mpk.p + r.e' + (if M then S.half else 0) }

/-- `B_f̂ = ∑_b EvalF(f̂_b, B) · G̲⁻¹(V_b)`. -/
def keyMatrix (mpk : MPK S) (f : Circuit S.Attr) : Matrix (Fin 1) (Col k) R :=
  ∑ b, evalMat S.Γ₁ mpk.Bj (S.fhat f b) * S.Γ₁.ginv (S.rowBits.V b)

/-- **KeyGen** produces a key with `[B | B_f̂] sk = p` (sampled with the trapdoor of `B`). -/
def ValidKey (mpk : MPK S) (f : Circuit S.Attr) (sk : SecretKey (R := R) (k := k)) : Prop :=
  mpk.B * sk.k₁ + keyMatrix mpk f * sk.k₂ = scalar mpk.p

/-- `c_f̂ = ∑_b EvalFX(f̂_b, ψ, c) · G̲⁻¹(V_b) + Ψ̄_f`. -/
def evalCiphertext (mpk : MPK S) (f : Circuit S.Attr) (ct : Ciphertext S) :
    Matrix (Fin 1) (Col k) R :=
  ∑ b, evalEnc S.Γ₁ mpk.Bj (bitsOf S ct.Ψ) ct.cj (S.fhat f b) * S.Γ₁.ginv (S.rowBits.V b) +
    botRow (evalMat S.Γ ct.Ψ f)

/-- **Dec**, before rounding: `κ − [c₀ | c_f̂] sk`. -/
def decryptRaw (mpk : MPK S) (f : Circuit S.Attr) (sk : SecretKey (R := R) (k := k))
    (ct : Ciphertext S) : R :=
  ct.κ - (ct.c₀ * sk.k₁ + evalCiphertext mpk f ct * sk.k₂) 0 0

/-- The Ring-GSW secret `t = [s | −1]`. -/
def gswSecret (s : R) : Matrix (Fin 1) (Fin 2) R := Matrix.of fun _ a => if a = 0 then s else -1

/-- The noise of decryption: `e' − [e₀ | E_BGG − E_GSW] sk`. -/
def noise (mpk : MPK S) (x : S.Attr → Bool) (f : Circuit S.Attr) (sk : SecretKey (R := R) (k := k))
    (r : EncCoins S) : R :=
  let Ψ := fun i => stackKey mpk.B r.e r.s * r.Rm i + bitR (R := R) (x i) • S.Γ.G
  let eBgg := ∑ b, evalErr S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f b) * S.Γ₁.ginv (S.rowBits.V b)
  let eGsw := evalErr S.Γ Ψ (fun i => bitR (R := R) (x i)) (fun i => -(r.e * r.Rm i)) f
  r.e' - (r.e₀ * sk.k₁ + (eBgg - eGsw) * sk.k₂) 0 0

/-! ### Setup and KeyGen with the gadget trapdoor -/

/-- The master secret key: the gadget trapdoor `T` of `B = [A₀ | g − A₀ T]`. -/
abbrev MSK (k : ℕ) (R : Type*) [CommRing R] := Matrix (Fin k) (Fin k) R

/-- **Setup**, from its coins: `A₀`, the short `T`, the `B_j` and `p`. -/
def setup (S : Setting R k) (A₀ : Fin k → R) (T : MSK k R)
    (Bj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) (p : R) : MPK S × MSK k R :=
  ({ B := gTrapdoorMatrix S.D A₀ T, Bj := Bj, p := p }, T)

/-- **KeyGen**, from its coin `k₂`: `k₁ = [T; I] g⁻¹(p − B_f̂ k₂)`. -/
def keyGen (mpk : MPK S) (T : MSK k R) (f : Circuit S.Attr) (k₂ : Matrix (Col k) (Fin 1) R) :
    SecretKey (R := R) (k := k) :=
  { k₁ := gTrapdoorSolve S.D T (mpk.p - (keyMatrix mpk f * k₂) 0 0), k₂ := k₂ }

/-- Keys generated with the trapdoor are valid. -/
theorem keyGen_valid (A₀ : Fin k → R) (T : MSK k R)
    (Bj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) (p : R) (f : Circuit S.Attr)
    (k₂ : Matrix (Col k) (Fin 1) R) :
    ValidKey (setup S A₀ T Bj p).1 f (keyGen (setup S A₀ T Bj p).1 T f k₂) := by
  simp only [ValidKey, setup, keyGen]
  rw [gTrapdoorMatrix_mul_solve]
  ext a b
  fin_cases a; fin_cases b
  simp [scalar]

/-! ### The circuits `f̂` -/

/-- A bit decomposition whose bits are `0/1`, given by a Boolean function. -/
def IsBoolean {r : Type*} (β : MatrixBits R r (Col k))
    (bool : Matrix r (Col k) R → β.Index → Bool) : Prop :=
  ∀ Y b, β.bits Y b = bitR (bool Y b)

open Classical in
/-- `f̂` by truth tables: the bit `b` of the top row of `FHE.Eval(f, Ψ)`, as a function of the bits
of `Ψ` (`Circuit.ofFun`). Correct for every `f` (`truthTableFhat_correct`), but of exponential
size. -/
noncomputable def truthTableFhat (D : GadgetDigits R k) (Attr : Type) [Fintype Attr]
    (ctBits : MatrixBits R (Fin 2) (Col k)) (rowBits : MatrixBits R (Fin 1) (Col k))
    (boolRow : Matrix (Fin 1) (Col k) R → rowBits.Index → Bool) :
    Circuit Attr → rowBits.Index → Circuit (Attr × ctBits.Index) := fun f b =>
  Circuit.ofFun fun z =>
    boolRow (topRow (evalMat (gswGadget D) (fun i => ∑ j, bitR (R := R) (z (i, j)) • ctBits.V j) f)) b

/-- **`f̂` computes the Ring-GSW evaluation**, for `0/1` bit decompositions. -/
theorem truthTableFhat_correct (S : Setting R k) [Fintype S.Attr]
    (boolCt : Matrix (Fin 2) (Col k) R → S.ctBits.Index → Bool)
    (boolRow : Matrix (Fin 1) (Col k) R → S.rowBits.Index → Bool)
    (hct : IsBoolean S.ctBits boolCt) (hrow : IsBoolean S.rowBits boolRow)
    (hS : S.fhat = truthTableFhat S.D S.Attr S.ctBits S.rowBits boolRow) : S.FhatCorrect := by
  classical
  intro f Ψ b
  have hbits : bitsOf S Ψ = fun z => bitR (R := R) (boolCt (Ψ z.1) z.2) := by
    funext z; exact hct _ _
  have hrec : (fun i => ∑ j, bitR (R := R) (boolCt (Ψ i) j) • S.ctBits.V j) = Ψ := by
    funext i
    conv_rhs => rw [← S.ctBits.recompose (Ψ i)]
    exact Finset.sum_congr rfl fun j _ => by rw [hct]
  rw [hS, hbits, hrow]
  have := Circuit.eval_bits (R := R) (fun z => boolCt (Ψ z.1) z.2)
    (truthTableFhat S.D S.Attr S.ctBits S.rowBits boolRow f b)
  simp only [bitR] at this ⊢
  rw [this]
  unfold truthTableFhat
  rw [Circuit.evalBool_ofFun]
  simp only [bitR] at hrec
  simp only [bitR, hrec]

/-! ### Correctness -/

theorem gswSecret_mul_stackKey (B e : Matrix (Fin 1) (Col k) R) (s : R) :
    gswSecret s * stackKey B e s = -e := by
  ext a c
  fin_cases a
  simp [gswSecret, stackKey, Matrix.mul_apply, Fin.sum_univ_two]

theorem gswSecret_mul (s : R) (Ψ : Matrix (Fin 2) (Col k) R) :
    gswSecret s * Ψ = scalar s * topRow Ψ - botRow Ψ := by
  ext a c
  fin_cases a
  simp [gswSecret, scalar, topRow, botRow, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

/-- **Correctness, exactly.** If `f(x) = 0`, `[B | B_f̂] sk = p` and `f̂` computes the Ring-GSW
evaluation, then `κ − κ' = M ⌊q/2⌋ + noise`. -/
theorem decryptRaw_eq (hfhat : S.FhatCorrect) (mpk : MPK S) (x : S.Attr → Bool) (M : Bool)
    (r : EncCoins S) (f : Circuit S.Attr) (sk : SecretKey (R := R) (k := k))
    (hsk : ValidKey mpk f sk) (hfx : f.eval (fun i => bitR (R := R) (x i)) = 0) :
    decryptRaw mpk f sk (encrypt mpk x M r) =
      (if M then S.half else 0) + noise mpk x f sk r := by
  set Ψ := fun i => stackKey mpk.B r.e r.s * r.Rm i + bitR (R := R) (x i) • S.Γ.G with hΨ
  -- The Ring-GSW invariant of the attribute ciphertexts.
  have hinv : ∀ i, gswSecret r.s * Ψ i =
      bitR (R := R) (x i) • (gswSecret r.s * S.Γ.G) + -(r.e * r.Rm i) := by
    intro i
    rw [hΨ, Matrix.mul_add, ← Matrix.mul_assoc, gswSecret_mul_stackKey, Matrix.mul_smul,
      Matrix.neg_mul]
    abel
  have hgsw := gsw_invariant S.Γ (gswSecret r.s) Ψ (fun i => bitR (R := R) (x i)) (fun i => -(r.e * r.Rm i)) hinv f
  rw [hfx, zero_smul, zero_add] at hgsw
  -- The BGG+ evaluation of every bit of the top row of `Ψ_f`.
  have hbgg : ∀ b, evalEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) (encrypt mpk x M r).cj (S.fhat f b) =
      scalar r.s * (evalMat S.Γ₁ mpk.Bj (S.fhat f b) -
          S.rowBits.bits (topRow (evalMat S.Γ Ψ f)) b • S.Γ₁.G) +
        evalErr S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f b) := by
    intro b
    rw [← hfhat f Ψ b]
    exact bgg_key_relation S.Γ₁ (scalar r.s) mpk.Bj (bitsOf S Ψ) _ r.ej (fun j => rfl) _
  have hmat := matrix_key_relation_bits S.Γ₁ S.rowBits (scalar r.s)
    (fun b => evalMat S.Γ₁ mpk.Bj (S.fhat f b)) (topRow (evalMat S.Γ Ψ f))
    (fun b => evalEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) (encrypt mpk x M r).cj (S.fhat f b))
    (fun b => evalErr S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f b)) hbgg
  -- `c_f̂ = s B_f̂ − t Ψ_f + E_BGG = s B_f̂ + E_BGG − E_GSW`.
  have hcf : evalCiphertext mpk f (encrypt mpk x M r) =
      scalar r.s * keyMatrix mpk f +
        (∑ b, evalErr S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f b) * S.Γ₁.ginv (S.rowBits.V b) -
          evalErr S.Γ Ψ (fun i => bitR (R := R) (x i)) (fun i => -(r.e * r.Rm i)) f) := by
    have ht := gswSecret_mul r.s (evalMat S.Γ Ψ f)
    rw [hgsw] at ht
    simp only [evalCiphertext, encrypt, keyMatrix] at hmat ⊢
    rw [hmat, Matrix.mul_sub]
    rw [show botRow (evalMat S.Γ Ψ f) = scalar r.s * topRow (evalMat S.Γ Ψ f) -
        evalErr S.Γ Ψ (fun i => bitR (R := R) (x i)) (fun i => -(r.e * r.Rm i)) f by rw [ht]; abel]
    abel
  -- `κ' = s p + [e₀ | E_BGG − E_GSW] sk`.
  have hsk' := congrArg (fun m => (scalar r.s * m) 0 0) hsk
  simp only [Matrix.mul_add, ← Matrix.mul_assoc] at hsk'
  simp only [decryptRaw, noise, hcf]
  simp only [encrypt, Matrix.add_mul, Matrix.add_apply] at hsk' ⊢
  simp only [scalar, Matrix.mul_apply, Matrix.of_apply, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton] at hsk' ⊢
  simp only [Matrix.sub_apply] at hsk' ⊢
  rw [← hsk']
  simp only [mul_assoc]
  ring

/-! ### The simulation of the security proof (BTVW17 Theorem 4.2)

The algebra of the hybrids `H1`, `H2`: in `Setup*` the `B_j = B W'_j + ψ*_j G̲` are built from the
bits `ψ*` of the challenge ciphertexts `Ψ*ᵢ = A Rᵢ + x*ᵢ G`, `A = [B; c]`. Then

* `Enc*` gives the encodings as `c_j = c W'_j` (`encodings_sim`): with `c = sB + e`, these are real
  encodings with errors `e W'_j`;
* `B_f̂ = B (W'_f̂ + R_f) + f(x*) G̲` (`keyMatrix_sim`);
* for an unauthorized `f` (`f(x*) = 1`) this is `[B | B W + G̲]`, for which `(−W u, u)` with
  `G̲ u = p` is a key, without the trapdoor of `B` (`simKey_valid`, the [ABB10] trick).

The statistical steps (leftover hash lemma for `A Rᵢ` and `B W'_j`, the distribution of Gaussian
preimages, noise flooding) and the Ring-LWE step (`c = sB + e` against uniform) are not formalized
here. -/

theorem topRow_stackKey_mul (B e : Matrix (Fin 1) (Col k) R) (s : R)
    (M : Matrix (Col k) (Col k) R) : topRow (stackKey B e s * M) = B * M := by
  ext a c
  fin_cases a
  simp [topRow, stackKey, Matrix.mul_apply]

theorem topRow_add (X Y : Matrix (Fin 2) (Col k) R) : topRow (X + Y) = topRow X + topRow Y := by
  ext a c; simp [topRow]

theorem topRow_smul (a : R) (X : Matrix (Fin 2) (Col k) R) : topRow (a • X) = a • topRow X := by
  ext b c; simp [topRow]

theorem topRow_gswGadget (D : GadgetDigits R k) : topRow (gswGadget D).G = (topRowGadget D).G := by
  ext a c
  fin_cases a
  simp [topRow, gswGadget, topRowGadget, gadgetOf]

/-- **`Enc*`.** With `B_j = B W'_j + ψ_j G̲`, the encoding `s(B_j − ψ_j G̲) + e W'_j` is `c W'_j` for
`c = sB + e`. -/
theorem encodings_sim (B e : Matrix (Fin 1) (Col k) R) (s y : R) (W' : Matrix (Col k) (Col k) R) :
    scalar s * ((B * W' + y • S.Γ₁.G) - y • S.Γ₁.G) + e * W' = (scalar s * B + e) * W' := by
  rw [add_sub_cancel_right, Matrix.add_mul, Matrix.mul_assoc]

/-- The Ring-GSW evaluation of the challenge: `Ψ*_f = A R_f + f(x*) G`. -/
theorem gsw_sim (B e : Matrix (Fin 1) (Col k) R) (s : R) (x : S.Attr → Bool)
    (Rm : S.Attr → Matrix (Col k) (Col k) R) (f : Circuit S.Attr) :
    evalMat S.Γ (fun i => stackKey B e s * Rm i + bitR (R := R) (x i) • S.Γ.G) f =
      stackKey B e s * evalSim S.Γ (fun i => stackKey B e s * Rm i + bitR (R := R) (x i) • S.Γ.G)
          (fun i => bitR (R := R) (x i)) Rm f +
        f.eval (fun i => bitR (R := R) (x i)) • S.Γ.G :=
  sim_relation S.Γ _ _ _ Rm (fun _ => rfl) f

/-- The simulation trapdoor of `B_f̂`: `W'_f̂ + R_f`. -/
def simTrapdoor (B e : Matrix (Fin 1) (Col k) R) (s : R) (x : S.Attr → Bool)
    (Rm : S.Attr → Matrix (Col k) (Col k) R) (W' : S.Attr × S.ctBits.Index → Matrix (Col k) (Col k) R)
    (mpk : MPK S) (f : Circuit S.Attr) : Matrix (Col k) (Col k) R :=
  let Ψ := fun i => stackKey B e s * Rm i + bitR (R := R) (x i) • S.Γ.G
  ∑ b, evalSim S.Γ₁ mpk.Bj (bitsOf S Ψ) W' (S.fhat f b) * S.Γ₁.ginv (S.rowBits.V b) +
    evalSim S.Γ Ψ (fun i => bitR (R := R) (x i)) Rm f

/-- **`KeyGen*`.** Under `Setup*`, `B_f̂ = B (W'_f̂ + R_f) + f(x*) G̲`. -/
theorem keyMatrix_sim (hfhat : S.FhatCorrect) (B e : Matrix (Fin 1) (Col k) R) (s : R)
    (x : S.Attr → Bool) (Rm : S.Attr → Matrix (Col k) (Col k) R)
    (W' : S.Attr × S.ctBits.Index → Matrix (Col k) (Col k) R) (mpk : MPK S) (hB : mpk.B = B)
    (hBj : ∀ j, mpk.Bj j = B * W' j +
      bitsOf S (fun i => stackKey B e s * Rm i + bitR (R := R) (x i) • S.Γ.G) j • S.Γ₁.G)
    (f : Circuit S.Attr) :
    keyMatrix mpk f =
      mpk.B * simTrapdoor B e s x Rm W' mpk f + f.eval (fun i => bitR (R := R) (x i)) • S.Γ₁.G := by
  set Ψ := fun i => stackKey B e s * Rm i + bitR (R := R) (x i) • S.Γ.G with hΨ
  have hsim : ∀ b, evalMat S.Γ₁ mpk.Bj (S.fhat f b) =
      B * evalSim S.Γ₁ mpk.Bj (bitsOf S Ψ) W' (S.fhat f b) +
        S.rowBits.bits (topRow (evalMat S.Γ Ψ f)) b • S.Γ₁.G := by
    intro b
    rw [← hfhat f Ψ b]
    exact sim_relation S.Γ₁ B mpk.Bj (bitsOf S Ψ) W' hBj _
  have htop : topRow (evalMat S.Γ Ψ f) =
      B * evalSim S.Γ Ψ (fun i => bitR (R := R) (x i)) Rm f + f.eval (fun i => bitR (R := R) (x i)) • S.Γ₁.G := by
    rw [gsw_sim, topRow_add, topRow_stackKey_mul, topRow_smul, topRow_gswGadget]
  have hsum : keyMatrix mpk f = B * ∑ b, evalSim S.Γ₁ mpk.Bj (bitsOf S Ψ) W' (S.fhat f b) *
      S.Γ₁.ginv (S.rowBits.V b) + topRow (evalMat S.Γ Ψ f) := by
    simp only [keyMatrix, hsim, Matrix.add_mul, Finset.sum_add_distrib, Matrix.smul_mul,
      S.Γ₁.mul_ginv, Matrix.mul_sum, Matrix.mul_assoc, S.rowBits.recompose]
  rw [hsum, htop, hB, simTrapdoor, Matrix.mul_add]
  abel

/-- A short preimage of `p` under `G̲`: the digits of `p` in the first block. -/
def gadgetPreimage (D : GadgetDigits R k) (p : R) : Matrix (Col k) (Fin 1) R :=
  Matrix.of fun c _ => if c.1 = 0 then D.d p c.2 else 0

theorem topRowGadget_mul_gadgetPreimage (D : GadgetDigits R k) (p : R) :
    (topRowGadget D).G * gadgetPreimage D p = scalar p := by
  have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
  ext a b
  fin_cases a; fin_cases b
  simp only [topRowGadget, gadgetOf, gadgetPreimage, scalar, Matrix.mul_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue, ite_true, h10, ite_false, mul_zero,
    Finset.sum_const_zero, add_zero]
  exact D.recompose p

/-- The simulated key `(−W u, u)` with `G̲ u = p`. -/
def simKey (Wsim : Matrix (Col k) (Col k) R) (D : GadgetDigits R k) (p : R) :
    SecretKey (R := R) (k := k) :=
  { k₁ := -(Wsim * gadgetPreimage D p), k₂ := gadgetPreimage D p }

/-- **The simulator answers unauthorized key queries without the trapdoor** ([ABB10]). Under
`Setup*`, for `f(x*) = 1` the key `(−W u, u)` with `W = W'_f̂ + R_f` is valid. -/
theorem simKey_valid (hfhat : S.FhatCorrect) (B e : Matrix (Fin 1) (Col k) R) (s : R)
    (x : S.Attr → Bool) (Rm : S.Attr → Matrix (Col k) (Col k) R)
    (W' : S.Attr × S.ctBits.Index → Matrix (Col k) (Col k) R) (mpk : MPK S) (hB : mpk.B = B)
    (hBj : ∀ j, mpk.Bj j = B * W' j +
      bitsOf S (fun i => stackKey B e s * Rm i + bitR (R := R) (x i) • S.Γ.G) j • S.Γ₁.G)
    (f : Circuit S.Attr) (hfx : f.eval (fun i => bitR (R := R) (x i)) = 1) :
    ValidKey mpk f (simKey (simTrapdoor B e s x Rm W' mpk f) S.D mpk.p) := by
  simp only [ValidKey, simKey]
  rw [keyMatrix_sim hfhat B e s x Rm W' mpk hB hBj f, hfx, one_smul, Matrix.add_mul,
    Matrix.mul_neg, ← Matrix.mul_assoc, topRowGadget_mul_gadgetPreimage]
  abel

/-! ### Over `R_q = ℤ_q[X]/(X^N + 1)` -/

section Ring

open Cslib

variable {N q : ℕ} [NeZero q]

/-- The bits of the coefficients, as Booleans. -/
def coeffBool {r : Type} (Y : Matrix r (Col k) (Negacyclic (ZMod q) N))
    (b : r × Col k × Fin k × Fin N) : Bool :=
  ((Y b.1 b.2.1).coeffs b.2.2.2).val.testBit b.2.2.1

theorem coeffBits_isBoolean (hk : q ≤ 2 ^ k) (r : Type) [Fintype r] [DecidableEq r] :
    IsBoolean (coeffBits N q k hk r (Col k)) coeffBool := by
  intro Y b
  simp only [coeffBits, bitR, coeffBool]
  split_ifs with h <;> simp [h]

/-- The setting over `R_q`: binary digits (`q ≤ 2^k`), the bits of the coefficients, and the
truth-table circuits `f̂`. -/
noncomputable def ringSetting (N q k : ℕ) [NeZero q] (hk : q ≤ 2 ^ k) (Attr : Type)
    [Fintype Attr] : Setting (Negacyclic (ZMod q) N) k where
  D := binaryDigits N q k hk
  Attr := Attr
  ctBits := coeffBits N q k hk (Fin 2) (Col k)
  rowBits := coeffBits N q k hk (Fin 1) (Col k)
  fhat := truthTableFhat (binaryDigits N q k hk) Attr _ _ coeffBool
  half := algebraMap (ZMod q) _ (encodeBit q true)

theorem ringSetting_fhatCorrect (hk : q ≤ 2 ^ k) (Attr : Type) [Fintype Attr] :
    (ringSetting N q k hk Attr).FhatCorrect :=
  @truthTableFhat_correct _ _ _ (ringSetting N q k hk Attr) ‹Fintype Attr› coeffBool coeffBool
    (coeffBits_isBoolean hk _) (coeffBits_isBoolean hk _) rfl

/-- **Correctness over `R_q`** (BTVW17 Theorem 4.1). If `f(x) = 0`, the key is valid, `f̂`
computes the Ring-GSW evaluation and the constant coefficient `ν₀` of the noise has
`4|ν₀| + 2 < q`, decryption returns `M`. -/
theorem decrypt_correct {k : ℕ} (hk : q ≤ 2 ^ k) {Attr : Type} [Fintype Attr] (hN : 0 < N)
    (mpk : MPK (ringSetting N q k hk Attr)) (x : Attr → Bool) (M : Bool)
    (r : EncCoins (ringSetting N q k hk Attr)) (f : Circuit Attr) (sk : SecretKey)
    (hsk : ValidKey mpk f sk) (hfx : f.evalBool x = false)
    (hν : 4 * |((noise mpk x f sk r).coeffs ⟨0, hN⟩).valMinAbs| + 2 < q) :
    decodeBit hN (decryptRaw mpk f sk (encrypt mpk x M r)) = M := by
  have hfx' : f.eval (fun i => bitR (R := Negacyclic (ZMod q) N) (x i)) = 0 := by
    have := Circuit.eval_bits (R := Negacyclic (ZMod q) N) x f
    simpa [bitR, hfx] using this
  rw [decryptRaw_eq (ringSetting_fhatCorrect hk Attr) mpk x M r f sk hsk hfx']
  have hM : (if M then (ringSetting N q k hk Attr).half else 0) =
      algebraMap (ZMod q) (Negacyclic (ZMod q) N) (encodeBit q M) := by
    cases M <;> simp [ringSetting, encodeBit]
  rw [hM]
  exact decodeBit_encodeBit_add hN M _ hν

/-- **Correctness of the whole scheme over `R_q`.** For any coins of `Setup`, `KeyGen` and `Enc`, if
`f(x) = 0` and the constant coefficient `ν₀` of the noise has `4|ν₀| + 2 < q`, then
`Dec(KeyGen(msk, f), Enc(mpk, x, M)) = M`. -/
theorem scheme_correct {k : ℕ} (hk : q ≤ 2 ^ k) {Attr : Type} [Fintype Attr] (hN : 0 < N)
    (A₀ : Fin k → Negacyclic (ZMod q) N) (T : MSK k (Negacyclic (ZMod q) N))
    (Bj : Attr × (coeffBits N q k hk (Fin 2) (Col k)).Index →
      Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N))
    (p : Negacyclic (ZMod q) N) (f : Circuit Attr)
    (k₂ : Matrix (Col k) (Fin 1) (Negacyclic (ZMod q) N)) (x : Attr → Bool) (M : Bool)
    (r : EncCoins (ringSetting N q k hk Attr)) (hfx : f.evalBool x = false)
    (hν : 4 * |((noise (setup (ringSetting N q k hk Attr) A₀ T Bj p).1 x f
        (keyGen (setup (ringSetting N q k hk Attr) A₀ T Bj p).1 T f k₂) r).coeffs
          ⟨0, hN⟩).valMinAbs| + 2 < q) :
    decodeBit hN (decryptRaw (setup (ringSetting N q k hk Attr) A₀ T Bj p).1 f
      (keyGen (setup (ringSetting N q k hk Attr) A₀ T Bj p).1 T f k₂)
      (encrypt (setup (ringSetting N q k hk Attr) A₀ T Bj p).1 x M r)) = M :=
  decrypt_correct hk hN (setup (ringSetting N q k hk Attr) A₀ T Bj p).1 x M r f
    (keyGen (setup (ringSetting N q k hk Attr) A₀ T Bj p).1 T f k₂)
    (keyGen_valid (S := ringSetting N q k hk Attr) A₀ T Bj p f k₂) hfx hν

end Ring

end AdvancedEncryption.RingBTVW
