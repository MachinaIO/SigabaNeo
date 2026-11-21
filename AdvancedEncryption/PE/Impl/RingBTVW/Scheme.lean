import SigabaNeo.Lib.Lattices.Homomorphic
import SigabaNeo.Lib.Lattices.Decode

/-!
# The ring variant of the BTVW17 §4.2 predicate encryption

The weakly attribute-hiding predicate encryption of Brakerski–Tsabary–Vaikuntanathan–Wee
(ePrint 2017/795, §4.2, the "dual use" technique) over a ring, with the LWE dimension `n = 1`:
over `R_q = ℤ_q[X]/(X^N + 1)` (`ringSetting`) it rests on Ring-LWE. The same secret `s` is the
Ring-GSW secret of the attribute ciphertexts `Ψᵢ` and the BGG+ secret of the encodings of their bits.

With columns `W = Fin 2 × Fin k`, the Ring-GSW gadget `G ∈ R^{2×W}` and its top row `G̲ ∈ R^{1×W}`:

* `Setup`: `B ∈ R^{1×W}`, `B_j ∈ R^{1×W}` for every bit `j` of the attribute ciphertexts, and
  `p ∈ R`, all uniform (`MPK`, `setupLaw`).
* `Enc(mpk, x, M)` (`encrypt`, coins `EncCoins`): with a fresh secret `s`, the Ring-GSW ciphertexts
  `Ψᵢ = [aᵢ; s aᵢ + eᵢ] + xᵢ G` with fresh uniform `aᵢ`; with `ψ` the bits of `Ψ`, `c₀ = sB + e₀`,
  `c_j = s(B_j − ψ_j G̲) + e_j` and `κ = s p + e' + M ⌊q/2⌋`.
* `KeyGen(msk, f)`: `B_f̂ = ∑_b EvalF(f̂_b, B) · G̲⁻¹(V_b)` (`keyMatrix`), where the program `f̂`
  (a straight-line program of NAND gates) computes the bits `b` of the top row of
  `Ψ_f = FHE.Eval(f, Ψ)` from the bits of `Ψ`, and a key `sk` with
  `[B | B_f̂] sk = p` (`ValidKey`) from a key sampler whose law depends on `(B, B_f̂, p)` only
  (`KeySampler`, `keyGenLaw`).
* `Dec(sk, f, ct)` (`decryptRaw`): `c_f̂ = ∑_b EvalFX(f̂_b, ψ, c) · G̲⁻¹(V_b) + Ψ̄_f` with `Ψ̄_f` the
  bottom row of `Ψ_f`, `κ' = [c₀ | c_f̂] sk`, and `κ − κ'`, decoded at the constant coefficient
  (`decodeBit`).

The paper encrypts the attribute under `Ψᵢ = A Rᵢ + xᵢ G` with `A = [B; sB + e]` and binary `Rᵢ`,
which needs the leftover hash lemma; here, as in mxx's predicate encryption (`crates/pe`, attribute
ciphertexts `[a_t; s a_t + e_t] + … G` with fresh `a_t`), every `Ψᵢ` uses fresh Ring-LWE samples
under the same `s`, and Ring-LWE alone hides `x` (`PE.Impl.RingBTVW.Security`).

**Correctness** (BTVW17 Theorem 4.1). If `f(x) = 0`, then `κ − κ' = M ⌊q/2⌋ + noise` with the noise
given explicitly (`decryptRaw_eq`): it is `e'` minus `[e₀ | E_BGG − E_GSW] sk`, with `E_BGG` the
BGG+ evaluation error and `E_GSW` the Ring-GSW evaluation error. Over `R_q`, decryption returns `M`
when the constant coefficient of the noise is below `q/4` (`decrypt_correct`, `scheme_correct`).

**Security** (BTVW17 Theorem 4.2): under Ring-LWE alone, with no statistical step
(`PE.Impl.RingBTVW.Security.attributeHiding`).

**Constructed.** Over `R_q` (`ringSetting`): the gadget digits and the bit decompositions; the
polynomial-size program `f̂` of the Ring-GSW evaluation (`fhatProgram`: modular arithmetic on the
bits of the coefficients, proved correct by `ringSetting_fhatCorrect`); a key
samplers (`gaussKeySampler`: the discrete Gaussian on the coset of the keys; `canonicalKeySampler`);
the gadget trapdoor `B = [A₀ | g − A₀ T]`, whose exact preimages
show that valid keys exist for such `B` (`trapdoorKey_valid`, `keyGenLaw_valid`); the laws of the
coins (`PE.Impl.RingBTVW.Laws`).

**Not formalized here.**

* The efficient trapdoor sampler that approximates `gaussKeySampler` (with `B` from a trapdoor
  generation, close to uniform).
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
  /-- `f̂`: a program on the bits of the attribute ciphertexts, and its output wire for each bit
  `b` of the top row of `FHE.Eval(f, Ψ)`. -/
  fhat : Circuit Attr → SLP (Attr × ctBits.Index) × (rowBits.Index → Wire (Attr × ctBits.Index))
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
    SLP.eval (bitsOf S Ψ) (S.fhat f).1 ((S.fhat f).2 b) =
      S.rowBits.bits (topRow (evalMat S.Γ Ψ f)) b

/-- The master public key. -/
structure MPK where
  /-- `B`. -/
  B : Matrix (Fin 1) (Col k) R
  /-- `B_j` for every bit `j` of the attribute ciphertexts. -/
  Bj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R
  /-- `p`. -/
  p : R

/-- The coins of encryption. -/
structure EncCoins where
  /-- The secret. -/
  s : R
  /-- The fresh top rows `aᵢ` of the Ring-GSW ciphertexts. -/
  a : S.Attr → Matrix (Fin 1) (Col k) R
  /-- The errors of the Ring-GSW ciphertexts. -/
  eΨ : S.Attr → Matrix (Fin 1) (Col k) R
  /-- The error of `c₀`. -/
  e₀ : Matrix (Fin 1) (Col k) R
  /-- The errors of the encodings. -/
  ej : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R
  /-- The error of `κ`. -/
  e' : R

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

/-- `[a; sa + e]`. -/
def stackKey (B e : Matrix (Fin 1) (Col k) R) (s : R) : Matrix (Fin 2) (Col k) R :=
  Matrix.of fun a c => if a = 0 then B 0 c else s * B 0 c + e 0 c

/-- **Enc.** -/
def encrypt (mpk : MPK S) (x : S.Attr → Bool) (M : Bool) (r : EncCoins S) : Ciphertext S :=
  let Ψ := fun i => stackKey (r.a i) (r.eΨ i) r.s + bitR (R := R) (x i) • S.Γ.G
  { Ψ := Ψ
    c₀ := scalar r.s * mpk.B + r.e₀
    cj := fun j => scalar r.s * (mpk.Bj j - bitsOf S Ψ j • S.Γ₁.G) + r.ej j
    κ := r.s * mpk.p + r.e' + (if M then S.half else 0) }

/-- `B_f̂ = ∑_b EvalF(f̂_b, B) · G̲⁻¹(V_b)`. -/
def keyMatrix (mpk : MPK S) (f : Circuit S.Attr) : Matrix (Fin 1) (Col k) R :=
  ∑ b, slpPK S.Γ₁ mpk.Bj (S.fhat f).1 ((S.fhat f).2 b) * S.Γ₁.ginv (S.rowBits.V b)

/-- **KeyGen** produces a key with `[B | B_f̂] sk = p` (sampled with the trapdoor of `B`). -/
def ValidKey (mpk : MPK S) (f : Circuit S.Attr) (sk : SecretKey (R := R) (k := k)) : Prop :=
  mpk.B * sk.k₁ + keyMatrix mpk f * sk.k₂ = scalar mpk.p

/-- `c_f̂ = ∑_b EvalFX(f̂_b, ψ, c) · G̲⁻¹(V_b) + Ψ̄_f`. -/
def evalCiphertext (mpk : MPK S) (f : Circuit S.Attr) (ct : Ciphertext S) :
    Matrix (Fin 1) (Col k) R :=
  ∑ b, slpEnc S.Γ₁ mpk.Bj (bitsOf S ct.Ψ) ct.cj (S.fhat f).1 ((S.fhat f).2 b) *
      S.Γ₁.ginv (S.rowBits.V b) +
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
  let Ψ := fun i => stackKey (r.a i) (r.eΨ i) r.s + bitR (R := R) (x i) • S.Γ.G
  let eBgg := ∑ b, slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f).1 ((S.fhat f).2 b) *
    S.Γ₁.ginv (S.rowBits.V b)
  let eGsw := evalErr S.Γ Ψ (fun i => bitR (R := R) (x i)) (fun i => -r.eΨ i) f
  r.e' - (r.e₀ * sk.k₁ + (eBgg - eGsw) * sk.k₂) 0 0

/-! ### Setup and KeyGen with the gadget trapdoor -/

/-- The master secret key: the gadget trapdoor `T` of `B = [A₀ | g − A₀ T]`. -/
abbrev MSK (k : ℕ) (R : Type*) [CommRing R] := Matrix (Fin k) (Fin k) R

/-- **Setup**, from its coins: `A₀`, the short `T`, the `B_j` and `p`. -/
def setup (S : Setting R k) (A₀ : Fin k → R) (T : MSK k R)
    (Bj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) (p : R) : MPK S × MSK k R :=
  ({ B := gTrapdoorMatrix S.D A₀ T, Bj := Bj, p := p }, T)

/-- An exact key from the trapdoor: `k₁ = [T; I] g⁻¹(p − B_f̂ k₂)`. It shows that keys exist
(`trapdoorKey_valid`); it reveals `T`, so it is not the key generation of the scheme (`keyGenLaw`). -/
def trapdoorKey (mpk : MPK S) (T : MSK k R) (f : Circuit S.Attr) (k₂ : Matrix (Col k) (Fin 1) R) :
    SecretKey (R := R) (k := k) :=
  { k₁ := gTrapdoorSolve S.D T (mpk.p - (keyMatrix mpk f * k₂) 0 0), k₂ := k₂ }

/-- Keys solved with the trapdoor are valid. -/
theorem trapdoorKey_valid (A₀ : Fin k → R) (T : MSK k R)
    (Bj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) (p : R) (f : Circuit S.Attr)
    (k₂ : Matrix (Col k) (Fin 1) R) :
    ValidKey (setup S A₀ T Bj p).1 f (trapdoorKey (setup S A₀ T Bj p).1 T f k₂) := by
  simp only [ValidKey, setup, trapdoorKey]
  rw [gTrapdoorMatrix_mul_solve]
  ext a b
  fin_cases a; fin_cases b
  simp [scalar]

/-- A key sampler: a law on the keys `sk` with `[B | B_f̂] sk = p` that depends on `(B, B_f̂, p)`
only, in particular not on any trapdoor. Its support is in the valid keys whenever one exists. The
intended one is the discrete Gaussian on this coset ([GPV08]), which MP12's sampler approximates
from a trapdoor of `B`. -/
structure KeySampler (R : Type*) [CommRing R] (k : ℕ) where
  /-- The law of the key for `(B, B_f̂, p)`. -/
  law : Matrix (Fin 1) (Col k) R → Matrix (Fin 1) (Col k) R → R → PMF (SecretKey (R := R) (k := k))
  /-- Its keys are valid when valid keys exist. -/
  valid : ∀ B Bf p, (∃ sk : SecretKey (R := R) (k := k), B * sk.k₁ + Bf * sk.k₂ = scalar p) →
    ∀ sk ∈ (law B Bf p).support, B * sk.k₁ + Bf * sk.k₂ = scalar p

/-- **KeyGen**: the key sampler at `(B, B_f̂, p)`. -/
noncomputable def keyGenLaw (ks : KeySampler R k) (mpk : MPK S) (f : Circuit S.Attr) :
    PMF (SecretKey (R := R) (k := k)) :=
  ks.law mpk.B (keyMatrix mpk f) mpk.p

/-- Every key that `KeyGen` outputs after `Setup` is valid. -/
theorem keyGenLaw_valid (ks : KeySampler R k) (A₀ : Fin k → R) (T : MSK k R)
    (Bj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) (p : R) (f : Circuit S.Attr) :
    ∀ sk ∈ (keyGenLaw ks (setup S A₀ T Bj p).1 f).support, ValidKey (setup S A₀ T Bj p).1 f sk :=
  ks.valid _ _ _ ⟨_, trapdoorKey_valid A₀ T Bj p f 0⟩

open Classical in
/-- A key sampler: a fixed valid key when one exists. It shows that key samplers exist; its keys
need not be short. -/
noncomputable def canonicalKeySampler : KeySampler R k where
  law B Bf p := if h : ∃ sk : SecretKey (R := R) (k := k), B * sk.k₁ + Bf * sk.k₂ = scalar p
    then PMF.pure (Classical.choose h) else PMF.pure ⟨0, 0⟩
  valid B Bf p h sk hsk := by
    rw [dite_eq_left_of_eq_true (eq_true h), PMF.support_pure, Set.mem_singleton_iff] at hsk
    rw [hsk]
    exact Classical.choose_spec h

/-! ### The circuits `f̂` -/

/-- A bit decomposition whose bits are `0/1`, given by a Boolean function. -/
def IsBoolean {r : Type*} (β : MatrixBits R r (Col k))
    (bool : Matrix r (Col k) R → β.Index → Bool) : Prop :=
  ∀ Y b, β.bits Y b = bitR (bool Y b)

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
  set Ψ := fun i => stackKey (r.a i) (r.eΨ i) r.s + bitR (R := R) (x i) • S.Γ.G with hΨ
  -- The Ring-GSW invariant of the attribute ciphertexts.
  have hinv : ∀ i, gswSecret r.s * Ψ i =
      bitR (R := R) (x i) • (gswSecret r.s * S.Γ.G) + -r.eΨ i := by
    intro i
    rw [hΨ, Matrix.mul_add, gswSecret_mul_stackKey, Matrix.mul_smul]
    abel
  have hgsw := gsw_invariant S.Γ (gswSecret r.s) Ψ (fun i => bitR (R := R) (x i)) (fun i => -r.eΨ i) hinv f
  rw [hfx, zero_smul, zero_add] at hgsw
  -- The BGG+ evaluation of every bit of the top row of `Ψ_f`.
  have hbgg : ∀ b, slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) (encrypt mpk x M r).cj (S.fhat f).1
      ((S.fhat f).2 b) =
      scalar r.s * (slpPK S.Γ₁ mpk.Bj (S.fhat f).1 ((S.fhat f).2 b) -
          S.rowBits.bits (topRow (evalMat S.Γ Ψ f)) b • S.Γ₁.G) +
        slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f).1 ((S.fhat f).2 b) := by
    intro b
    rw [← hfhat f Ψ b]
    exact slp_enc_key_relation S.Γ₁ (scalar r.s) mpk.Bj (bitsOf S Ψ) _ r.ej (fun j => rfl) _ _
  have hmat := matrix_key_relation_bits S.Γ₁ S.rowBits (scalar r.s)
    (fun b => slpPK S.Γ₁ mpk.Bj (S.fhat f).1 ((S.fhat f).2 b)) (topRow (evalMat S.Γ Ψ f))
    (fun b => slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) (encrypt mpk x M r).cj (S.fhat f).1 ((S.fhat f).2 b))
    (fun b => slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f).1 ((S.fhat f).2 b)) hbgg
  -- `c_f̂ = s B_f̂ − t Ψ_f + E_BGG = s B_f̂ + E_BGG − E_GSW`.
  have hcf : evalCiphertext mpk f (encrypt mpk x M r) =
      scalar r.s * keyMatrix mpk f +
        (∑ b, slpEnc S.Γ₁ mpk.Bj (bitsOf S Ψ) r.ej (S.fhat f).1 ((S.fhat f).2 b) *
          S.Γ₁.ginv (S.rowBits.V b) -
          evalErr S.Γ Ψ (fun i => bitR (R := R) (x i)) (fun i => -r.eΨ i) f) := by
    have ht := gswSecret_mul r.s (evalMat S.Γ Ψ f)
    rw [hgsw] at ht
    simp only [evalCiphertext, encrypt, keyMatrix] at hmat ⊢
    rw [hmat, Matrix.mul_sub]
    rw [show botRow (evalMat S.Γ Ψ f) = scalar r.s * topRow (evalMat S.Γ Ψ f) -
        evalErr S.Γ Ψ (fun i => bitR (R := R) (x i)) (fun i => -r.eΨ i) f by rw [ht]; abel]
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

/-! ### Over `R_q = ℤ_q[X]/(X^N + 1)` -/

section Ring

open Cslib

variable {N q : ℕ} [NeZero q]

/-- The row `[B | B_f̂]`, indexed by the block and the column. -/
def keyRow (B Bf : Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N)) :
    Fin 2 × Col k → Negacyclic (ZMod q) N :=
  fun bc => if bc.1 = 0 then B 0 bc.2 else Bf 0 bc.2

/-- A key as a vector indexed by the block and the column. -/
def keyVec (sk : SecretKey (R := Negacyclic (ZMod q) N) (k := k)) :
    Fin 2 × Col k → Negacyclic (ZMod q) N :=
  fun bc => if bc.1 = 0 then sk.k₁ bc.2 0 else sk.k₂ bc.2 0

/-- The key of a vector. -/
def keyOf (z : Fin 2 × Col k → Negacyclic (ZMod q) N) :
    SecretKey (R := Negacyclic (ZMod q) N) (k := k) :=
  ⟨Matrix.of fun c _ => z (0, c), Matrix.of fun c _ => z (1, c)⟩

omit [NeZero q] in
theorem keyVec_keyOf (z : Fin 2 × Col k → Negacyclic (ZMod q) N) : keyVec (keyOf z) = z := by
  funext bc
  obtain ⟨b, c⟩ := bc
  fin_cases b <;> rfl

omit [NeZero q] in
/-- `[B | B_f̂] sk = p` is the row equation `∑ [B | B_f̂]_bc sk_bc = p`. -/
theorem validKey_iff (B Bf : Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N))
    (p : Negacyclic (ZMod q) N) (sk : SecretKey (R := Negacyclic (ZMod q) N) (k := k)) :
    B * sk.k₁ + Bf * sk.k₂ = scalar p ↔ ∑ bc, keyRow B Bf bc * keyVec sk bc = p := by
  have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [keyRow, keyVec, Fin.isValue, ite_true, h10, ite_false]
  constructor
  · intro h
    have := congrFun (congrFun h 0) 0
    simpa [scalar, Matrix.mul_apply] using this
  · intro h
    funext a b
    fin_cases a; fin_cases b
    simpa [scalar, Matrix.mul_apply] using h

open Classical in
/-- **The Gaussian key sampler**: the discrete Gaussian of width `τ` on the keys `sk` with
`[B | B_f̂] sk = p` (`gaussPreimage`), or the zero key when there is none. -/
noncomputable def gaussKeySampler (τ : ℝ) (hτ : 0 < τ) : KeySampler (Negacyclic (ZMod q) N) k where
  law B Bf p := match gaussPreimage (keyRow B Bf) p τ hτ with
    | some d => d.map keyOf
    | none => PMF.pure ⟨0, 0⟩
  valid B Bf p hex sk hsk := by
    obtain ⟨sk₀, hsk₀⟩ := hex
    have hsome := gaussPreimage_isSome (keyRow B Bf) p hτ
      ⟨keyVec sk₀, (validKey_iff B Bf p sk₀).mp hsk₀⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hsome
    simp only [hd, PMF.support_map] at hsk
    obtain ⟨z, hz, rfl⟩ := hsk
    rw [validKey_iff, keyVec_keyOf]
    exact gaussPreimage_mem _ _ hτ hd hz

/-- The bits of the coefficients, as Booleans. -/
def coeffBool {r : Type} (Y : Matrix r (Col k) (Negacyclic (ZMod q) N))
    (b : r × Col k × Fin k × Fin N) : Bool :=
  ((Y b.1 b.2.1).coeffs b.2.2.2).val.testBit b.2.2.1

theorem coeffBits_isBoolean (hk : q ≤ 2 ^ k) (r : Type) [Fintype r] [DecidableEq r] :
    IsBoolean (coeffBits N q k hk r (Col k)) coeffBool := by
  intro Y b
  simp only [coeffBits, bitR, coeffBool]
  split_ifs with h <;> simp [h]

/-- The setting over `R_q`: binary digits (`q < 2^k`), the bits of the coefficients, and the
polynomial-size program `f̂` of the Ring-GSW evaluation (`fhatProgram`). -/
noncomputable def ringSetting (N q k : ℕ) [NeZero q] (hk : q < 2 ^ k) (Attr : Type) :
    Setting (Negacyclic (ZMod q) N) k where
  D := binaryDigits N q k hk.le
  Attr := Attr
  ctBits := coeffBits N q k hk.le (Fin 2) (Col k)
  rowBits := coeffBits N q k hk.le (Fin 1) (Col k)
  fhat f := ((fhatProgram (N := N) hk f).1,
    fun b => (fhatProgram (N := N) hk f).2 (0, b.2.1, b.2.2.1, b.2.2.2))
  half := algebraMap (ZMod q) _ (encodeBit q true)

/-- **`f̂` computes the Ring-GSW evaluation** over `R_q` (`fhatProgram_spec`). -/
theorem ringSetting_fhatCorrect (hk : q < 2 ^ k) (Attr : Type) :
    (ringSetting N q k hk Attr).FhatCorrect := by
  intro f Ψ b
  have hbits : bitsOf (ringSetting N q k hk Attr) Ψ =
      fun j => if coeffBool (Ψ j.1) j.2 then (1 : Negacyclic (ZMod q) N) else 0 := by
    funext j
    exact coeffBits_isBoolean hk.le (Fin 2) (Ψ j.1) j.2
  rw [hbits, SLP.eval_bits]
  erw [coeffBits_isBoolean hk.le (Fin 1)]
  have h := fhatProgram_spec (N := N) hk (fun j => coeffBool (Ψ j.1) j.2) Ψ
    (fun i a c b j => rfl) f 0 b.2.1 b.2.2.1 b.2.2.2
  have h' : SLP.evalBool (fun j => coeffBool (Ψ j.1) j.2) ((ringSetting N q k hk Attr).fhat f).1
      (((ringSetting N q k hk Attr).fhat f).2 b) =
      coeffBool (topRow (evalMat (ringSetting N q k hk Attr).Γ Ψ f)) b := h
  simp only [bitR, h']

/-- **Correctness over `R_q`** (BTVW17 Theorem 4.1). If `f(x) = 0`, the key is valid, `f̂`
computes the Ring-GSW evaluation and the constant coefficient `ν₀` of the noise has
`4|ν₀| + 2 < q`, decryption returns `M`. -/
theorem decrypt_correct {k : ℕ} (hk : q < 2 ^ k) {Attr : Type} (hN : 0 < N)
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

/-- **Correctness of the whole scheme over `R_q`.** For any `mpk` for which `f` has a valid key
(for instance every `B = [A₀ | g − A₀ T]`, `keyGenLaw_valid`), any key that `KeyGen` outputs and any
coins of `Enc`: if `f(x) = 0` and the constant coefficient `ν₀` of the noise has `4|ν₀| + 2 < q`, then
`Dec(sk, Enc(mpk, x, M)) = M`. -/
theorem scheme_correct {k : ℕ} (hk : q < 2 ^ k) {Attr : Type} (hN : 0 < N)
    (ks : KeySampler (Negacyclic (ZMod q) N) k) (mpk : MPK (ringSetting N q k hk Attr))
    (f : Circuit Attr) (hex : ∃ sk : SecretKey, ValidKey mpk f sk) (sk : SecretKey)
    (hsk : sk ∈ (keyGenLaw ks mpk f).support) (x : Attr → Bool) (M : Bool)
    (r : EncCoins (ringSetting N q k hk Attr)) (hfx : f.evalBool x = false)
    (hν : 4 * |((noise mpk x f sk r).coeffs ⟨0, hN⟩).valMinAbs| + 2 < q) :
    decodeBit hN (decryptRaw mpk f sk (encrypt mpk x M r)) = M :=
  decrypt_correct hk hN mpk x M r f sk (ks.valid _ _ _ hex sk hsk) hfx hν

end Ring

end AdvancedEncryption.RingBTVW
