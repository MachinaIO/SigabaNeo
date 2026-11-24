import PE.Impl.ExpLUT.SimEval
import SigabaNeo.Lib.Lattices.LeftoverHash

/-!
# The views of the hybrids

The pair `(mpk, ct)` seen by the adversary in the hybrids H1–H4 of the proof of Theorem 2
(ePrint 2026/2539, Appendix A), as deterministic functions of their inputs (the laws are in
`PE.Impl.ExpLUT.Hybrid*`). The challenge is for the message `0`; other messages are a shift of
`c_m` (`shiftCT`).

* `PubData`: the public data other than the programmed matrices: `B̄ = [Ā; B̄⁽²⁾]` (the `Ā` columns
  of `B`, the seed of the leftover hash lemma), the gadget columns of `B⁽¹⁾` and `B⁽²⁾`, the `H_k` and
  `d`.
* `PrI`: the programming columns: `Z_t`, `R₀`, `R^in_{t,d}`, `R^aut_{t,d}`, each a binary vector
  `zr i ∈ {0,1}^{m̄}` on the `Ā` columns (`progOf`); their hashes `B̄ · zr i` (`hpOf`).
* `progMPK`: **the programmed public key** of hybrid H1: `a_t = Ā Z_t + X^{w x_t} G⁽¹⁾`,
  `A₀ = B R₀ + G`, `A^in_{t,d} = B R + d G` (digits of `C^in_t`), `A^aut_{t,d} = σ_{g_t}(B) R + d G`
  (digits of `C_{g_t}`), from the hash values; `programmed_progMPK`: it is `Programmed` (so
  Corollary 1 applies).
* `view1`: **H1**: the programmed public key and `Enc`'s ciphertext.
* `view2`: **H2**: the ciphertext computed from `b` (`c₀ = b̄ R₀ + e₀`, digit encodings `σ_i(b̄) R + e'`,
  `C^in_t = [a_t; (B̄⁽²⁾ − b̄) Z_t + e_t + X^{w x_t} G⁽²⁾]`), from the core values `(b, h_k, c_m)`
  (`Core`) and the flooding errors (`FloodV`).
* `view1_eq_view2`: **H1 = H2 up to a shift of the flooding errors** by `±ē_b R`, `ē_b Z_t`
  (`floodShift`), exactly.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type} [CommRing R] {S : Setting R} {Wb J Pos : Type} [Fintype Wb] [Fintype J]

variable (S Wb J) in
/-- The public data other than the programmed matrices. -/
structure PubData where
  /-- `B̄ = [Ā; B̄⁽²⁾]`: the `Ā` columns of `B`. -/
  Bb : Matrix (Fin 2) Wb R
  /-- The gadget columns of `B⁽¹⁾`. -/
  Bg1 : Fin S.τ → R
  /-- The gadget columns of `B⁽²⁾`. -/
  B2g : Fin S.τ → R
  /-- `H_k`. -/
  H : J → Matrix (Fin 2) (Col S.τ) R
  /-- `d`. -/
  d : Fin 2 → R

/-- `B` from its parts. -/
def PubData.B (P : PubData S Wb J) : Matrix (Fin 2) (BCol Wb S.τ) R :=
  Matrix.of ![Sum.elim (P.Bb 0) P.Bg1, Sum.elim (P.Bb 1) P.B2g]

variable (S Pos) in
/-- The programming columns: `Z_t`, `R₀`, `R^in_{t,d}`, `R^aut_{t,d}`. -/
abbrev PrI := (Pos × Col S.τ) ⊕ Col S.τ ⊕ (Pos × Dig S.τ × Col S.τ) ⊕ (Fin S.b × Dig S.τ × Col S.τ)

/-- The binary vector `zr i` as a vector of ring elements. -/
def bv (z : Wb → Bool) : Wb → R := fun w => bitVal (z w)

/-- The programming matrices of the binary vectors `zr`. -/
def progOf (zr : PrI S Pos → Wb → Bool) : Prog S Wb J Pos where
  Z t := Matrix.of fun w c => bitVal (zr (.inl (t, c)) w)
  R0 := Matrix.of fun w c => bitVal (zr (.inr (.inl c)) w)
  Rin t d := Matrix.of fun w c => bitVal (zr (.inr (.inr (.inl (t, d, c)))) w)
  Raut t d := Matrix.of fun w c => bitVal (zr (.inr (.inr (.inr (t, d, c)))) w)

/-- The hashes `B̄ · zr i`. -/
def hpOf (Bb : Matrix (Fin 2) Wb R) (zr : PrI S Pos → Wb → Bool) : PrI S Pos → Fin 2 → R :=
  fun i => binaryHash Bb (zr i)

variable (M : HelperMap S J) (w : ℕ)

/-- The programmed `a_t = Ā Z_t + X^{w x_t} G⁽¹⁾`, from the hash values. -/
def progA (x : Pos → ℕ) (hp : PrI S Pos → Fin 2 → R) : Pos → Col S.τ → R :=
  fun t c => hp (.inl (t, c)) 0 + S.E.X ^ (w * x t) * S.G 0 c

/-- **The programmed public key** (H1), from the hash values `hp`, the helpers `h` (for the digits of
`C_{g_t}`) and the bottom rows `cb` of the `C^in_t` (for their digits). -/
def progMPK (P : PubData S Wb J) (x : Pos → ℕ) (hp : PrI S Pos → Fin 2 → R) (h : J → Col S.τ → R)
    (cb : Pos → Col S.τ → R) : MPK S Wb J Pos where
  B := P.B
  H := P.H
  a := progA w x hp
  A0 := Matrix.of fun ρ c => hp (.inr (.inl c)) ρ + S.G ρ c
  Ain t d := Matrix.of fun ρ c => hp (.inr (.inr (.inl (t, d, c)))) ρ +
    digits S (cinMat (progA w x hp t) (cb t)) d * S.G ρ c
  Aaut t d := Matrix.of fun ρ c => S.E.σ (S.kf t) (hp (.inr (.inr (.inr (t, d, c)))) ρ) +
    digits S (autGC M P.H h t) d * S.G ρ c
  d := P.d

/-! ### H1: `Enc` with a programmed public key -/

/-- The helpers `h_k = s H_k − s_k G + e_k`. -/
def helpersOf (H : J → Matrix (Fin 2) (Col S.τ) R) (r : EncCoins S Wb J Pos) : J → Col S.τ → R :=
  fun k => sec r.s ᵥ* H k - sec (S.E.σ (S.idx (M.je k)) r.s) ᵥ* S.G + r.eh k

/-- The bottom rows of `C^in_t`: `−s̄ a_t + X^{w x_t} s G + e_t`. -/
def cinBotsOf (a : Pos → Col S.τ → R) (x : Pos → ℕ) (r : EncCoins S Wb J Pos) : Pos → Col S.τ → R :=
  fun t => -(r.s • a t) + (S.E.X ^ (w * x t) • sec r.s) ᵥ* S.G + r.ein t

/-- The programmed public key of H1. -/
def mpk1 (P : PubData S Wb J) (x : Pos → ℕ) (hp : PrI S Pos → Fin 2 → R) (r : EncCoins S Wb J Pos) :
    MPK S Wb J Pos :=
  progMPK M w P x hp (helpersOf M P.H r) (cinBotsOf w (progA w x hp) x r)

/-- **The view of H1**: the programmed public key and `Enc`'s ciphertext of `0`. -/
def view1 (half : R) (P : PubData S Wb J) (x : Pos → ℕ) (hp : PrI S Pos → Fin 2 → R)
    (r : EncCoins S Wb J Pos) : MPK S Wb J Pos × Ciphertext S Wb J Pos :=
  (mpk1 M w P x hp r, encrypt M w half (mpk1 M w P x hp r) x 0 r)

/-! ### H2: the ciphertext from `b` -/

variable (S Wb J) in
/-- The core values of the ciphertext, which depend on `s̄` directly: `b`, the helpers `h_k`, `c_m`. -/
abbrev Core := (BCol Wb S.τ → R) × (J → Col S.τ → R) × R

variable (S Pos) in
/-- The flooding errors: of the digit encodings of `C_{g_t}`, of the `C^in_t`, of their digit
encodings, of `c₀`. -/
abbrev FloodV := (Fin S.b → Dig S.τ → Col S.τ → R) × (Pos → Col S.τ → R) ×
  (Pos → Dig S.τ → Col S.τ → R) × (Col S.τ → R)

/-- The ciphertext data from `b`, for given bottom rows `cb` of the `C^in_t`. -/
def ct2 (zr : PrI S Pos → Wb → Bool) (core : Core S Wb J) (fl : FloodV S Pos)
    (cb : Pos → Col S.τ → R) : Ciphertext S Wb J Pos where
  b := core.1
  h := core.2.1
  caut t d c := S.E.σ (S.kf t) ((fun w => core.1 (.inl w)) ⬝ᵥ bv (zr (.inr (.inr (.inr (t, d, c)))))) +
    fl.1 t d c
  cinBot := cb
  cin t d c := (fun w => core.1 (.inl w)) ⬝ᵥ bv (zr (.inr (.inr (.inl (t, d, c))))) + fl.2.2.1 t d c
  c0 c := (fun w => core.1 (.inl w)) ⬝ᵥ bv (zr (.inr (.inl c))) + fl.2.2.2 c
  cm := core.2.2

/-- The bottom rows of the `C^in_t` from `b`: `(B̄⁽²⁾ − b̄) Z_t + e_t + X^{w x_t} G⁽²⁾`. -/
def cb2 (P : PubData S Wb J) (x : Pos → ℕ) (zr : PrI S Pos → Wb → Bool) (core : Core S Wb J)
    (fl : FloodV S Pos) : Pos → Col S.τ → R :=
  fun t c => (P.Bb 1 - fun w => core.1 (.inl w)) ⬝ᵥ bv (zr (.inl (t, c))) + fl.2.1 t c +
    S.E.X ^ (w * x t) * S.G 1 c

/-- **The view of H2**. -/
def view2 (P : PubData S Wb J) (x : Pos → ℕ) (zr : PrI S Pos → Wb → Bool) (core : Core S Wb J)
    (fl : FloodV S Pos) : MPK S Wb J Pos × Ciphertext S Wb J Pos :=
  (progMPK M w P x (hpOf P.Bb zr) core.2.1 (cb2 w P x zr core fl),
    ct2 zr core fl (cb2 w P x zr core fl))

/-- The core values of `Enc`'s coins. -/
def coreOf (P : PubData S Wb J) (r : EncCoins S Wb J Pos) : Core S Wb J :=
  (sec r.s ᵥ* P.B + r.eb, helpersOf M P.H r, sec r.s ⬝ᵥ P.d + r.em)

/-- The flooding errors of `Enc`'s coins. -/
def floodOf (r : EncCoins S Wb J Pos) : FloodV S Pos := (r.eaut, r.ein, r.edin, r.e0)

/-- The shift of the flooding errors between H1 and H2: `−σ_{g_t}(ē_b R)`, `ē_b Z_t`, `−ē_b R`,
`−ē_b R₀`. -/
def floodShift (eb : BCol Wb S.τ → R) (zr : PrI S Pos → Wb → Bool) : FloodV S Pos :=
  (fun (t : Fin S.b) d c =>
      -S.E.σ (S.kf t) ((fun w => eb (.inl w)) ⬝ᵥ bv (zr (.inr (.inr (.inr (t, d, c)))))),
    (fun t c => (fun w => eb (.inl w)) ⬝ᵥ bv (zr (.inl (t, c)))),
    (fun t d c => -((fun w => eb (.inl w)) ⬝ᵥ bv (zr (.inr (.inr (.inl (t, d, c))))))),
    (fun c => -((fun w => eb (.inl w)) ⬝ᵥ bv (zr (.inr (.inl c))))))

/-! ### H1 = H2 up to flooding -/

omit [Fintype J] in
theorem hpOf_apply (Bb : Matrix (Fin 2) Wb R) (zr : PrI S Pos → Wb → Bool) (i : PrI S Pos)
    (ρ : Fin 2) : hpOf Bb zr i ρ = Bb ρ ⬝ᵥ bv (zr i) := rfl

omit [Fintype Wb] [Fintype J] in
/-- `b̄ = s̄ Ā + B̄⁽²⁾ + ē_b`. -/
theorem bbar_coreOf (P : PubData S Wb J) (r : EncCoins S Wb J Pos) :
    (fun w => (coreOf M P r).1 (.inl w)) = r.s • P.Bb 0 + P.Bb 1 + fun w => r.eb (.inl w) := by
  funext v
  simp [coreOf, Matrix.vecMul, dotProduct, Fin.sum_univ_two, sec, PubData.B]

omit [Fintype Wb] [Fintype J] in
theorem vecMul_sec_G (s ν : R) (c : Col S.τ) :
    ((ν • sec s) ᵥ* S.G) c = ν * (s * S.G 0 c + S.G 1 c) := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, sec]; ring

omit [Fintype Wb] [Fintype J] in
theorem vecMul_sec_apply (s : R) (A : Matrix (Fin 2) (Col S.τ) R) (c : Col S.τ) :
    (sec s ᵥ* A) c = s * A 0 c + A 1 c := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, sec]

omit [Fintype J] in
/-- The bottom rows of the `C^in_t` agree. -/
theorem cinBotsOf_eq_cb2 (P : PubData S Wb J) (x : Pos → ℕ) (zr : PrI S Pos → Wb → Bool)
    (r : EncCoins S Wb J Pos) :
    cinBotsOf w (progA w x (hpOf P.Bb zr)) x r =
      cb2 w P x zr (coreOf M P r) (floodOf r + floodShift r.eb zr) := by
  funext t c
  have hb := bbar_coreOf M P r
  simp only [cinBotsOf, cb2, progA, hpOf_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, vecMul_sec_G, hb, floodOf, floodShift, Prod.snd_add, Prod.fst_add, sub_dotProduct,
    add_dotProduct, smul_dotProduct]
  ring

omit [Fintype J] in
/-- **H1 = H2 up to flooding**: the view of H1 is the view of H2 for the core values of the coins
and the flooding errors shifted by `floodShift`. -/
theorem view1_eq_view2 (half : R) (P : PubData S Wb J) (x : Pos → ℕ) (zr : PrI S Pos → Wb → Bool)
    (r : EncCoins S Wb J Pos) :
    view1 M w half P x (hpOf P.Bb zr) r =
      view2 M w P x zr (coreOf M P r) (floodOf r + floodShift r.eb zr) := by
  have hb := bbar_coreOf M P r
  have hcb := cinBotsOf_eq_cb2 M w P x zr r
  have hm : mpk1 M w P x (hpOf P.Bb zr) r =
      progMPK M w P x (hpOf P.Bb zr) (coreOf M P r).2.1
        (cb2 w P x zr (coreOf M P r) (floodOf r + floodShift r.eb zr)) := by
    unfold mpk1; rw [hcb]; rfl
  unfold view1 view2
  rw [hm]
  refine Prod.ext rfl ?_
  have hh : helpers M (progMPK M w P x (hpOf P.Bb zr) (coreOf M P r).2.1
      (cb2 w P x zr (coreOf M P r) (floodOf r + floodShift r.eb zr))) r = (coreOf M P r).2.1 := rfl
  have hc : cinBots w (progMPK M w P x (hpOf P.Bb zr) (coreOf M P r).2.1
      (cb2 w P x zr (coreOf M P r) (floodOf r + floodShift r.eb zr))) x r =
      cb2 w P x zr (coreOf M P r) (floodOf r + floodShift r.eb zr) := hcb
  simp only [encrypt, ct2, Ciphertext.mk.injEq, hh, hc]
  refine ⟨by trivial, by trivial, ?_, by trivial, ?_, ?_, ?_⟩
  · funext t d c
    simp only [progMPK, Pi.add_apply, Pi.sub_apply, vecMul_sec_apply, vecMul_sec_G,
      Matrix.of_apply, hpOf_apply, Pi.smul_apply, smul_eq_mul, floodOf, floodShift, Prod.fst_add, hb,
      add_dotProduct, smul_dotProduct, map_add, map_mul, map_neg, Matrix.smul_vecMul]
    ring
  · funext t d c
    simp only [progMPK, Pi.add_apply, Pi.sub_apply, vecMul_sec_apply, vecMul_sec_G,
      Matrix.of_apply, hpOf_apply, Pi.smul_apply, smul_eq_mul, floodOf, floodShift, Prod.fst_add,
      Prod.snd_add, hb, add_dotProduct, smul_dotProduct, Pi.neg_apply, Matrix.smul_vecMul]
    ring
  · funext c
    simp only [progMPK, Pi.add_apply, Pi.sub_apply, vecMul_sec_apply, vecMul_sec_G,
      Matrix.of_apply, hpOf_apply, Pi.smul_apply, smul_eq_mul, floodOf, floodShift, Prod.snd_add, hb,
      add_dotProduct, smul_dotProduct, Pi.neg_apply]
    ring
  · simp [coreOf, progMPK]

/-! ### The programmed public key is programmed -/

omit [Fintype Wb] [Fintype J] in
theorem σ_bitVal (k : ℕ) (b : Bool) : S.E.σ k (bitVal b : R) = bitVal b := by
  cases b <;> simp [bitVal]

omit [Fintype J] in
/-- **The public key of H2 (and of H1) is `Programmed`** with the programming matrices of `zr`, so
Corollary 1 and Lemma 11 apply to it. -/
theorem programmed_view2 (P : PubData S Wb J) (x : Pos → ℕ) (zr : PrI S Pos → Wb → Bool)
    (core : Core S Wb J) (fl : FloodV S Pos) :
    Programmed M w (view2 M w P x zr core fl).1 (view2 M w P x zr core fl).2 x (progOf zr) where
  a t := by
    funext c
    simp [view2, progMPK, progA, hpOf_apply, abarOf, progOf, PubData.B, Matrix.vecMul, dotProduct,
      bv]
  A0 := by
    funext c
    simp [view2, progMPK, hpOf_apply, abarOf, progOf, PubData.B, Matrix.vecMul, dotProduct, bv]
  Ain t d := by
    funext c
    simp [view2, progMPK, hpOf_apply, abarOf, progOf, PubData.B, Matrix.vecMul, dotProduct, bv, ct2]
  Aaut t d := by
    funext c
    simp [view2, progMPK, hpOf_apply, abarOf, progOf, PubData.B, Matrix.vecMul, dotProduct, bv, ct2,
      map_sum, σ_bitVal]

end AdvancedEncryption.ExpLUT
