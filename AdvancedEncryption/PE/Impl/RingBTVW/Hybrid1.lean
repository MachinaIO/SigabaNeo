import PE.Impl.RingBTVW.Scheme
import SigabaNeoStd.Lattices.LeftoverHash

/-!
# Hybrid 1: simulated public keys of the encodings

In the real setup the public keys `B_j` of the encodings are uniform. In hybrid 1 they are
`B_j = B₀ W_j + ψ_j G̲` with binary `W_j`, where `ψ` are the bits of the attribute ciphertexts
(which depend on `B₀` and the coins of `Enc` only). The laws of `(mpk, ct)` are within
`|J| · |W| · √(|R| · 2^{−|Wd|}) / 2` (`hybrid1`): every column `B₀ w` is close to uniform by the
leftover hash lemma (`SigabaNeo.Lattices.closeTo_binaryHash_bind`), and a uniform `B_j` shifted by
`ψ_j G̲` is uniform.

The statement holds over any finite ring, for any law of the trapdoor part `B₁`, of `p` and of the
coins of `Enc`.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {k : ℕ} {S : Setting R k}
  {Wd Wt : Type} [Fintype Wd] [Fintype Wt] [DecidableEq Wd] [Nonempty Wd]
  [Fintype S.Attr] [DecidableEq S.Attr] [DecidableEq S.ctBits.Index]

/-- The positions of the columns of the encodings' public keys. -/
abbrev JC (S : Setting R k) := (S.Attr × S.ctBits.Index) × Col k

/-- The attribute ciphertexts depend on `B₀` and the coins only. -/
def gswOf (B₀ : Matrix (Fin 1) Wd R) (x : S.Attr → Bool) (r : EncCoins S Wd Wt) :
    S.Attr → Matrix (Fin 2) (Col k) R :=
  fun i => gswPK B₀ (scalar r.s * B₀ + r.e₀) * r.Rm i + bitR (R := R) (x i) • S.Γ.G

/-- The public keys of the encodings from the columns `h`, shifted by `ψ G̲`. -/
def bjOf (B₀ : Matrix (Fin 1) Wd R) (x : S.Attr → Bool) (r : EncCoins S Wd Wt)
    (h : JC S → (Fin 1 → R)) : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R :=
  fun j => Matrix.of (fun a c => h (j, c) a) + bitsOf S (gswOf B₀ x r) j • S.Γ₁.G

variable (lawB₁ : PMF (Matrix (Fin 1) Wt R)) (lawP : PMF R) (lawR : PMF (EncCoins S Wd Wt))

/-- The experiment after `B₀` and the columns `h`: `(mpk, ct)`. -/
noncomputable def contOf (x : S.Attr → Bool) (M : Bool) (B₀ : Matrix (Fin 1) Wd R)
    (h : JC S → (Fin 1 → R)) : PMF (MPK S Wd Wt × Ciphertext S Wd Wt) := do
  let B₁ ← lawB₁
  let p ← lawP
  let r ← lawR
  let mpk : MPK S Wd Wt := ⟨B₀, B₁, bjOf B₀ x r h, p⟩
  pure (mpk, encrypt mpk x M r)

/-- `H0`: the real `(mpk, ct)`, with uniform `B₀` and `B_j`. -/
noncomputable def realView (x : S.Attr → Bool) (M : Bool) :
    PMF (MPK S Wd Wt × Ciphertext S Wd Wt) := do
  let B₀ ← PMF.uniformOfFintype (Matrix (Fin 1) Wd R)
  let B₁ ← lawB₁
  let Bj ← PMF.uniformOfFintype (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R)
  let p ← lawP
  let r ← lawR
  let mpk : MPK S Wd Wt := ⟨B₀, B₁, Bj, p⟩
  pure (mpk, encrypt mpk x M r)

/-- `H1`: the public keys of the encodings are `B₀ W_j + ψ_j G̲` for binary `W_j`. -/
noncomputable def hyb1View (x : S.Attr → Bool) (M : Bool) :
    PMF (MPK S Wd Wt × Ciphertext S Wd Wt) :=
  (PMF.uniformOfFintype (Matrix (Fin 1) Wd R)).bind fun B₀ =>
    (Cslib.Probability.PMF.pi fun _ : JC S =>
      (PMF.uniformOfFintype (Wd → Bool)).map (binaryHash B₀)).bind
      (contOf lawB₁ lawP lawR x M B₀)

/-- The columns `h` as the public keys of the encodings, shifted by `ψ G̲`: a bijection. -/
def bjEquiv (B₀ : Matrix (Fin 1) Wd R) (x : S.Attr → Bool) (r : EncCoins S Wd Wt) :
    (JC S → (Fin 1 → R)) ≃ (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) where
  toFun := bjOf B₀ x r
  invFun Bj jc a := (Bj jc.1 - bitsOf S (gswOf B₀ x r) jc.1 • S.Γ₁.G) a jc.2
  left_inv h := by
    funext jc a
    simp [bjOf]
  right_inv Bj := by
    funext j
    ext a c
    simp [bjOf]

omit [Fintype R] [DecidableEq R] in
theorem bind_uniform_equiv {α β γ : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (g : β → PMF γ) :
    (PMF.uniformOfFintype α).bind (fun a => g (e a)) = (PMF.uniformOfFintype β).bind g := by
  rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv e, PMF.bind_map]
  rfl

omit [DecidableEq R] [Fintype Wt] [Nonempty Wd] in
/-- With uniform columns, the experiment is the real one. -/
theorem uniform_cont_eq_real (x : S.Attr → Bool) (M : Bool) :
    ((PMF.uniformOfFintype (Matrix (Fin 1) Wd R)).bind fun B₀ =>
      (Cslib.Probability.PMF.pi fun _ : JC S => PMF.uniformOfFintype (Fin 1 → R)).bind
        (contOf lawB₁ lawP lawR x M B₀)) = realView lawB₁ lawP lawR x M := by
  classical
  unfold realView contOf
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure]
  congr 1
  funext B₀
  rw [Cslib.Probability.PMF.pi_uniformOfFintype]
  -- move the columns after `B₁`, `p` and the coins
  rw [PMF.bind_comm]
  congr 1
  funext B₁
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext p
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext r
  exact bind_uniform_equiv (bjEquiv B₀ x r) (fun Bj =>
    PMF.pure ((⟨B₀, B₁, Bj, p⟩ : MPK S Wd Wt), encrypt ⟨B₀, B₁, Bj, p⟩ x M r))
/-- **Hybrid 1.** -/
theorem hybrid1 (x : S.Attr → Bool) (M : Bool) :
    CloseTo (hyb1View lawB₁ lawP lawR x M) (realView lawB₁ lawP lawR x M)
      (ENNReal.ofReal (Fintype.card (JC S) *
        (Real.sqrt (Fintype.card (Fin 1 → R) * (2 ^ Fintype.card Wd : ℝ)⁻¹) / 2))) := by
  classical
  rw [← uniform_cont_eq_real]
  exact closeTo_binaryHash_bind (R := R) (rr := Fin 1) (mm := Wd) (I := JC S)
    (contOf lawB₁ lawP lawR x M)

end AdvancedEncryption.RingBTVW
