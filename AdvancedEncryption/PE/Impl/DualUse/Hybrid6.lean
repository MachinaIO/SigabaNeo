import PE.Impl.DualUse.Hybrid1

/-!
# Hybrid 6: the view no longer depends on the challenge

After the computational hybrids, `A = [B₀; c₀]` is uniform, `Ψᵢ = A Rᵢ + xᵢ G`, the public keys
and encodings of the bits `ψ` are `(B_j, c_j) = (B₀ W_j + ψ_j G̲, c₀ W_j + e_j)` and `κ` is uniform
plus `M ⌊q/2⌋` (`h5View`). By the leftover hash lemma with the seed `A` (two rows), every column of
`A Rᵢ` and `A W_j` may be replaced by a uniform one (`hybrid6`), and then the view does not depend
on `(x, M)` (`finalView_indep`): uniform values shifted by `xᵢ G`, `ψ_j G̲` or `M ⌊q/2⌋` are
uniform.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {k : ℕ} {S : Setting R k}
  {Wd Wt : Type} [Fintype Wd] [Fintype Wt] [DecidableEq Wd] [DecidableEq Wt] [Nonempty Wd]
  [Fintype S.Attr] [DecidableEq S.Attr] [DecidableEq S.ctBits.Index]

/-- The hashed columns: those of every `Rᵢ` and every `W_j`. -/
abbrev HC (S : Setting R k) := (S.Attr × Col k) ⊕ ((S.Attr × S.ctBits.Index) × Col k)

/-- A matrix from its columns. -/
def colMat {r : Type} (h : Col k → (r → R)) : Matrix r (Col k) R := Matrix.of fun a c => h c a

variable (lawB₁ : PMF (Matrix (Fin 1) Wt R)) (lawE : PMF (S.Attr × S.ctBits.Index →
  Matrix (Fin 1) (Col k) R))

/-- The view from `A` and the columns `h` (of `A Rᵢ` and `A W_j`, or uniform). -/
noncomputable def viewOf (x : S.Attr → Bool) (M : Bool) (A : Matrix (Fin 2) Wd R)
    (h : HC S → (Fin 2 → R)) : PMF (MPK S Wd Wt × Ciphertext S Wd Wt) := do
  let B₁ ← lawB₁
  let c₁ ← PMF.uniformOfFintype (Matrix (Fin 1) Wt R)
  let p ← PMF.uniformOfFintype R
  let κ₀ ← PMF.uniformOfFintype R
  let e ← lawE
  let Ψ : S.Attr → Matrix (Fin 2) (Col k) R :=
    fun i => colMat (fun c => h (.inl (i, c))) + bitR (R := R) (x i) • S.Γ.G
  let Bj := fun j => topRow (colMat (fun c => h (.inr (j, c)))) + bitsOf S Ψ j • S.Γ₁.G
  let cj := fun j => botRow (colMat (fun c => h (.inr (j, c)))) + e j
  pure (⟨Matrix.of fun _ c => A 0 c, B₁, Bj, p⟩,
    ⟨Ψ, Matrix.of fun _ c => A 1 c, c₁, cj, κ₀ + (if M then S.half else 0)⟩)

/-- `H5`: the view with `A Rᵢ` and `A W_j` for binary `Rᵢ`, `W_j`. -/
noncomputable def h5View (x : S.Attr → Bool) (M : Bool) :
    PMF (MPK S Wd Wt × Ciphertext S Wd Wt) :=
  (PMF.uniformOfFintype (Matrix (Fin 2) Wd R)).bind fun A =>
    (Cslib.Probability.PMF.pi fun _ : HC S =>
      (PMF.uniformOfFintype (Wd → Bool)).map (binaryHash A)).bind (viewOf lawB₁ lawE x M A)

/-- The final view: uniform columns. -/
noncomputable def finalView (x : S.Attr → Bool) (M : Bool) :
    PMF (MPK S Wd Wt × Ciphertext S Wd Wt) :=
  (PMF.uniformOfFintype (Matrix (Fin 2) Wd R)).bind fun A =>
    (Cslib.Probability.PMF.pi fun _ : HC S => PMF.uniformOfFintype (Fin 2 → R)).bind
      (viewOf lawB₁ lawE x M A)

/-- **Hybrid 6.** -/
theorem hybrid6 (x : S.Attr → Bool) (M : Bool) :
    CloseTo (h5View (Wd := Wd) lawB₁ lawE x M) (finalView (Wd := Wd) lawB₁ lawE x M)
      (ENNReal.ofReal (Fintype.card (HC S) *
        (Real.sqrt (Fintype.card (Fin 2 → R) * (2 ^ Fintype.card Wd : ℝ)⁻¹) / 2))) := by
  classical
  exact closeTo_binaryHash_bind (R := R) (rr := Fin 2) (mm := Wd) (I := HC S)
    (viewOf lawB₁ lawE x M)

/-- The view from shifted columns and `κ`: no challenge. -/
noncomputable def rawOf (A : Matrix (Fin 2) Wd R) (h : HC S → (Fin 2 → R)) (κ : R) :
    PMF (MPK S Wd Wt × Ciphertext S Wd Wt) := do
  let B₁ ← lawB₁
  let c₁ ← PMF.uniformOfFintype (Matrix (Fin 1) Wt R)
  let p ← PMF.uniformOfFintype R
  let e ← lawE
  pure (⟨Matrix.of fun _ c => A 0 c, B₁, fun j => topRow (colMat (fun c => h (.inr (j, c)))), p⟩,
    ⟨fun i => colMat (fun c => h (.inl (i, c))), Matrix.of fun _ c => A 1 c, c₁,
      fun j => botRow (colMat (fun c => h (.inr (j, c)))) + e j, κ⟩)

/-- The shift of the columns by the challenge: `xᵢ G` on `Rᵢ`'s, `ψ_j G̲` on the top of `W_j`'s,
where `ψ` are the bits of the shifted `Ψ`. -/
def shiftCols (x : S.Attr → Bool) (h : HC S → (Fin 2 → R)) : HC S → (Fin 2 → R)
  | .inl (i, c) => fun a => h (.inl (i, c)) a + (bitR (R := R) (x i) • S.Γ.G) a c
  | .inr (j, c) => fun a => h (.inr (j, c)) a +
      if a = 0 then (bitsOf S (fun i => colMat (fun c => h (.inl (i, c))) +
        bitR (R := R) (x i) • S.Γ.G) j • S.Γ₁.G) 0 c else 0

/-- The shift is a bijection. -/
def shiftEquiv (x : S.Attr → Bool) : (HC S → (Fin 2 → R)) ≃ (HC S → (Fin 2 → R)) where
  toFun := shiftCols x
  invFun h'
    | .inl (i, c) => fun a => h' (.inl (i, c)) a - (bitR (R := R) (x i) • S.Γ.G) a c
    | .inr (j, c) => fun a => h' (.inr (j, c)) a -
        if a = 0 then (bitsOf S (fun i => colMat (fun c => h' (.inl (i, c)))) j • S.Γ₁.G) 0 c
        else 0
  left_inv h := by
    funext b a
    rcases b with ⟨i, c⟩ | ⟨j, c⟩
    · simp [shiftCols]
    · have : (fun i => colMat (fun c => shiftCols x h (.inl (i, c)))) =
          fun i => colMat (fun c => h (.inl (i, c))) + bitR (R := R) (x i) • S.Γ.G := by
        funext i; ext a c; simp [shiftCols, colMat]
      simp only [this]
      simp [shiftCols]
  right_inv h' := by
    funext b a
    rcases b with ⟨i, c⟩ | ⟨j, c⟩
    · simp [shiftCols]
    · have : (fun i => colMat (fun c => (fun hc : HC S => match hc with
            | .inl (i, c) => fun a => h' (.inl (i, c)) a - (bitR (R := R) (x i) • S.Γ.G) a c
            | .inr (j, c) => fun a => h' (.inr (j, c)) a -
                if a = 0 then (bitsOf S (fun i => colMat (fun c => h' (.inl (i, c)))) j •
                  S.Γ₁.G) 0 c else 0) (.inl (i, c))) + bitR (R := R) (x i) • S.Γ.G) =
          fun i => colMat (fun c => h' (.inl (i, c))) := by
        funext i; ext a c; simp [colMat]
      simp only [shiftCols, this]
      simp

omit [DecidableEq R] [Fintype Wd] [DecidableEq Wd] [Nonempty Wd] [Fintype S.Attr]
  [DecidableEq S.Attr] [DecidableEq S.ctBits.Index] in
theorem viewOf_eq (x : S.Attr → Bool) (M : Bool) (A : Matrix (Fin 2) Wd R)
    (h : HC S → (Fin 2 → R)) :
    viewOf (Wd := Wd) lawB₁ lawE x M A h = (PMF.uniformOfFintype R).bind fun κ₀ =>
      rawOf (Wd := Wd) lawB₁ lawE A (shiftEquiv x h) (κ₀ + if M then S.half else 0) := by
  unfold viewOf rawOf
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure]
  -- move `κ₀` after `B₁`, `c₁` and `p`
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext B₁
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext c₁
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext p
  congr 1; funext κ₀
  congr 1; funext e
  congr 3
  funext j; ext a c; fin_cases a; simp [shiftEquiv, shiftCols, colMat, botRow]

omit [DecidableEq R] [Nonempty Wd] in
/-- The final view from uniform `A`, columns and `κ`. -/
theorem finalView_eq_raw (x : S.Attr → Bool) (M : Bool) :
    finalView (Wd := Wd) lawB₁ lawE x M =
      (PMF.uniformOfFintype (Matrix (Fin 2) Wd R)).bind fun A =>
        (PMF.uniformOfFintype (HC S → (Fin 2 → R))).bind fun h =>
          (PMF.uniformOfFintype R).bind fun κ => rawOf (Wd := Wd) lawB₁ lawE A h κ := by
  classical
  unfold finalView
  congr 1
  funext A
  rw [Cslib.Probability.PMF.pi_uniformOfFintype]
  have hv : viewOf (Wd := Wd) lawB₁ lawE x M A = fun h =>
      (PMF.uniformOfFintype R).bind fun κ₀ =>
        rawOf (Wd := Wd) lawB₁ lawE A (shiftEquiv x h) (κ₀ + if M then S.half else 0) :=
    funext (viewOf_eq lawB₁ lawE x M A)
  rw [hv, bind_uniform_equiv (shiftEquiv x) (fun h => (PMF.uniformOfFintype R).bind fun κ₀ =>
    rawOf (Wd := Wd) lawB₁ lawE A h (κ₀ + if M then S.half else 0))]
  congr 1
  funext h
  exact bind_uniform_equiv (Equiv.addRight (if M then S.half else 0))
    (fun κ => rawOf (Wd := Wd) lawB₁ lawE A h κ)

omit [DecidableEq R] [Nonempty Wd] in
/-- **The final view does not depend on the challenge.** -/
theorem finalView_indep (x x' : S.Attr → Bool) (M M' : Bool) :
    finalView (Wd := Wd) lawB₁ lawE x M = finalView (Wd := Wd) lawB₁ lawE x' M' := by
  rw [finalView_eq_raw lawB₁ lawE x M, finalView_eq_raw lawB₁ lawE x' M']

end AdvancedEncryption.DualUse
