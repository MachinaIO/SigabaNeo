import PE.Impl.DualUse.Hybrid1

/-!
# Hybrid 4: encodings from `c₀` (noise flooding)

After hybrid 1, `B_j = B₀ W_j + ψ_j G̲`, so the encodings are `c_j = s(B_j − ψ_j G̲) + e_j =
s B₀ W_j + e_j`. In hybrid 4 they are `c₀ W_j + e_j = s B₀ W_j + e₀ W_j + e_j`: computable from
`c₀ = s B₀ + e₀` without `s`, as the Ring-LWE reduction of hybrid 5 needs. The two differ by the
shift `e₀ W_j` of the errors `e_j`; if the law of `(e_j)_j` hides every such shift up to `ε`
(noise flooding, `SigabaNeo.Lattices.closeTo_floodLaw_add`), the views are `ε`-close (`hybrid4`).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {k : ℕ} {S : Setting R k}
  {Wd Wt : Type} [Fintype Wd] [Fintype Wt] [DecidableEq Wd] [Nonempty Wd]
  [Fintype S.Attr] [DecidableEq S.Attr] [DecidableEq S.ctBits.Index]

/-- The coins of `Enc` other than the errors of the encodings: `(s, e₀, e₁, Rᵢ, e')`. -/
abbrev Rest (S : Setting R k) (Wd Wt : Type) :=
  R × Matrix (Fin 1) Wd R × Matrix (Fin 1) Wt R × (S.Attr → Matrix Wd (Col k) R) × R

/-- The coins of `Enc`. -/
def coinsOf (rest : Rest S Wd Wt) (e : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) :
    EncCoins S Wd Wt :=
  ⟨rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1, e, rest.2.2.2.2⟩

/-- The binary matrices `W_j` from their columns. -/
def wMat (w : JC S → (Wd → Bool)) (j : S.Attr × S.ctBits.Index) : Matrix Wd (Col k) R :=
  Matrix.of fun a c => bitVal (w (j, c) a)

/-- The hashed columns `B₀ w`. -/
def hashCols (B₀ : Matrix (Fin 1) Wd R) (w : JC S → (Wd → Bool)) : JC S → (Fin 1 → R) :=
  fun jc => binaryHash B₀ (w jc)

omit [DecidableEq R] [Fintype R] [DecidableEq Wd] [Nonempty Wd] [Fintype S.Attr]
  [DecidableEq S.Attr] [DecidableEq S.ctBits.Index] [Fintype Wt] in
theorem of_hashCols (B₀ : Matrix (Fin 1) Wd R) (w : JC S → (Wd → Bool)) (j) :
    (Matrix.of fun a c => hashCols B₀ w (j, c) a) = B₀ * wMat (k := k) w j := by
  ext a c
  simp [hashCols, binaryHash, wMat, Matrix.mulVec, dotProduct, Matrix.mul_apply]

variable (lawB₁ : PMF (Matrix (Fin 1) Wt R)) (lawP : PMF R) (lawRest : PMF (Rest S Wd Wt))
  (lawE : PMF (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R))

/-- The coins of `Enc` from `(s, e₀, e₁, Rᵢ, e')` and the errors of the encodings. -/
noncomputable def lawCoins : PMF (EncCoins S Wd Wt) :=
  lawRest.bind fun rest => lawE.map (coinsOf rest)

/-- The view of hybrid 1 with the binary columns `w` drawn explicitly; `cj` gives the encodings
from `(B₀, w, coins)`. -/
noncomputable def viewW (x : S.Attr → Bool) (M : Bool)
    (cj : Matrix (Fin 1) Wd R → (JC S → (Wd → Bool)) → EncCoins S Wd Wt →
      S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) :
    PMF (MPK S Wd Wt × Ciphertext S Wd Wt) :=
  (PMF.uniformOfFintype (Matrix (Fin 1) Wd R)).bind fun B₀ =>
    (Cslib.Probability.PMF.pi fun _ : JC S => PMF.uniformOfFintype (Wd → Bool)).bind fun w =>
      lawB₁.bind fun B₁ => lawP.bind fun p => lawRest.bind fun rest => lawE.bind fun e =>
        let r := coinsOf rest e
        let mpk : MPK S Wd Wt := ⟨B₀, B₁, bjOf B₀ x r (hashCols B₀ w), p⟩
        PMF.pure (mpk, { encrypt mpk x M r with cj := cj B₀ w r })

/-- The real encodings `s (B_j − ψ_j G̲) + e_j`. -/
def realCj (x : S.Attr → Bool) (B₀ : Matrix (Fin 1) Wd R) (w : JC S → (Wd → Bool))
    (r : EncCoins S Wd Wt) : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R :=
  fun j => scalar r.s * (bjOf B₀ x r (hashCols B₀ w) j - bitsOf S (gswOf B₀ x r) j • S.Γ₁.G) +
    r.ej j

/-- The encodings of hybrid 4: `c₀ W_j + e_j`. -/
def floodCj (B₀ : Matrix (Fin 1) Wd R) (w : JC S → (Wd → Bool)) (r : EncCoins S Wd Wt) :
    S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R :=
  fun j => (scalar r.s * B₀ + r.e₀) * wMat w j + r.ej j

omit [DecidableEq R] [Fintype Wt] [Nonempty Wd] [DecidableEq S.Attr]
  [DecidableEq S.ctBits.Index] in
/-- **Hybrid 4.** -/
theorem hybrid4 (x : S.Attr → Bool) (M : Bool) {ε : ℝ≥0∞}
    (hflood : ∀ rest ∈ lawRest.support, ∀ w : JC S → (Wd → Bool),
      CloseTo (lawE.map fun e j => e j + rest.2.1 * wMat w j) lawE ε) :
    CloseTo (viewW lawB₁ lawP lawRest lawE x M floodCj)
      (viewW lawB₁ lawP lawRest lawE x M (realCj x)) ε := by
  unfold viewW
  refine CloseTo.bind_right _ fun B₀ _ => CloseTo.bind_right _ fun w _ =>
    CloseTo.bind_right _ fun B₁ _ => CloseTo.bind_right _ fun p _ =>
    CloseTo.bind_right _ fun rest hrest => ?_
  set V : (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) →
      MPK S Wd Wt × Ciphertext S Wd Wt := fun e =>
    (⟨B₀, B₁, bjOf B₀ x (coinsOf rest e) (hashCols B₀ w), p⟩,
      { encrypt ⟨B₀, B₁, bjOf B₀ x (coinsOf rest e) (hashCols B₀ w), p⟩ x M (coinsOf rest e) with
        cj := realCj x B₀ w (coinsOf rest e) })
  have hL : (lawE.bind fun e =>
      PMF.pure ((⟨B₀, B₁, bjOf B₀ x (coinsOf rest e) (hashCols B₀ w), p⟩ : MPK S Wd Wt),
        { encrypt ⟨B₀, B₁, bjOf B₀ x (coinsOf rest e) (hashCols B₀ w), p⟩ x M (coinsOf rest e) with
          cj := floodCj B₀ w (coinsOf rest e) })) =
      (lawE.map fun e j => e j + rest.2.1 * wMat w j).map V := by
    rw [PMF.map_comp, PMF.map]
    congr 1
    funext e
    simp only [Function.comp_apply, V]
    have hcj : floodCj B₀ w (coinsOf rest e) =
        realCj x B₀ w (coinsOf rest (fun j => e j + rest.2.1 * wMat w j)) := by
      funext j
      simp only [floodCj, realCj, bjOf, of_hashCols, coinsOf, add_sub_cancel_right,
        Matrix.add_mul, Matrix.mul_assoc]
      abel
    rw [hcj]
    rfl
  have hR : (lawE.bind fun e => PMF.pure (V e)) = lawE.map V := rfl
  rw [hL]
  exact (hflood rest hrest w).map V

omit [Nonempty Wd] [DecidableEq R] [Fintype Wt] [DecidableEq S.Attr]
  [DecidableEq S.ctBits.Index] in
/-- The view with the real encodings is the view of hybrid 1. -/
theorem viewW_real_eq (x : S.Attr → Bool) (M : Bool) :
    viewW lawB₁ lawP lawRest lawE x M (realCj x) =
      hyb1View lawB₁ lawP (lawCoins lawRest lawE) x M := by
  unfold viewW hyb1View contOf lawCoins
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure]
  congr 1
  funext B₀
  rw [Cslib.Probability.PMF.pi_map, PMF.bind_map]
  congr 1
  funext w
  congr 1; funext B₁
  congr 1; funext p
  simp only [PMF.bind_bind, PMF.bind_map]
  rfl

end AdvancedEncryption.DualUse
