import PE.Impl.RingBTVW.FinalView

/-!
# The views of the ideal experiment

In the ideal experiment of attribute hiding the ciphertext is the simulator's uniform `ctU`,
independent of the public key (`idealView`). To answer key queries without the trapdoor of `B₁`,
the reduction of the ideal side needs `B_j = B₀ W_j + ψ_j G̲` for binary `W_j`, where `ψ` are the
bits of an internal Ring-GSW encryption `Ψ` of the selected attribute, never shown (`hybI1`). The
leftover hash lemma relates the two (`hybridI1`), and `B₁` can be drawn first (`hybI1_bind_B₁`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib.Probability

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {k : ℕ} {S : Setting R k}
  {Wd Wt : Type} [Fintype Wd] [Fintype Wt] [DecidableEq Wd] [DecidableEq Wt] [Nonempty Wd]
  [Fintype S.Attr] [DecidableEq S.Attr] [DecidableEq S.ctBits.Index]

variable (lawB₁ : PMF (Matrix (Fin 1) Wt R)) (lawP : PMF R) (lawR : PMF (EncCoins S Wd Wt))

/-- The ideal view: the public key and an independent uniform ciphertext. -/
noncomputable def idealView : PMF (MPK S Wd Wt × Ciphertext S Wd Wt) :=
  (mpkU S Wd Wt lawB₁).bind fun mpk => (ctU S Wd Wt).map (mpk, ·)

/-- The ideal experiment after `B₀` and the columns `h`, with internal coins `r`. -/
noncomputable def contI (x : S.Attr → Bool) (B₀ : Matrix (Fin 1) Wd R)
    (h : JC S → (Fin 1 → R)) : PMF (MPK S Wd Wt × Ciphertext S Wd Wt) := do
  let B₁ ← lawB₁
  let p ← lawP
  let r ← lawR
  let ct ← ctU S Wd Wt
  pure (⟨B₀, B₁, bjOf B₀ x r h, p⟩, ct)

/-- `I1`: the public keys of the encodings are `B₀ W_j + ψ_j G̲` for binary `W_j`. -/
noncomputable def hybI1 (x : S.Attr → Bool) : PMF (MPK S Wd Wt × Ciphertext S Wd Wt) :=
  (PMF.uniformOfFintype (Matrix (Fin 1) Wd R)).bind fun B₀ =>
    (Cslib.Probability.PMF.pi fun _ : JC S =>
      (PMF.uniformOfFintype (Wd → Bool)).map (binaryHash B₀)).bind (contI lawB₁ lawP lawR x B₀)

omit [DecidableEq R] [Nonempty Wd] in
/-- With uniform columns, the experiment is the ideal one. -/
theorem uniform_contI_eq (x : S.Attr → Bool) :
    ((PMF.uniformOfFintype (Matrix (Fin 1) Wd R)).bind fun B₀ =>
      (Cslib.Probability.PMF.pi fun _ : JC S => PMF.uniformOfFintype (Fin 1 → R)).bind
        (contI lawB₁ (PMF.uniformOfFintype R) lawR x B₀)) =
      idealView (S := S) (Wd := Wd) lawB₁ := by
  classical
  unfold idealView contI mpkU
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
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
  conv_rhs => rw [← PMF.bind_const lawR (PMF.bind _ _)]
  congr 1
  funext r
  exact bind_uniform_equiv (bjEquiv B₀ x r) (fun Bj =>
    (ctU S Wd Wt).bind fun ct => PMF.pure ((⟨B₀, B₁, Bj, p⟩ : MPK S Wd Wt), ct))

omit [DecidableEq R] in
/-- **Hybrid I1** (leftover hash lemma). -/
theorem hybridI1 (x : S.Attr → Bool) :
    CloseTo (hybI1 lawB₁ (PMF.uniformOfFintype R) lawR x) (idealView (S := S) (Wd := Wd) lawB₁)
      (ENNReal.ofReal (Fintype.card (JC S) *
        (Real.sqrt (Fintype.card (Fin 1 → R) * (2 ^ Fintype.card Wd : ℝ)⁻¹) / 2))) := by
  classical
  rw [← uniform_contI_eq]
  exact closeTo_binaryHash_bind (R := R) (rr := Fin 1) (mm := Wd) (I := JC S)
    (contI lawB₁ (PMF.uniformOfFintype R) lawR x)

omit [DecidableEq R] [Nonempty Wd] in
/-- `B₁` may be drawn first. -/
theorem hybI1_bind_B₁ (x : S.Attr → Bool) :
    hybI1 lawB₁ lawP lawR x = lawB₁.bind fun B₁ => hybI1 (PMF.pure B₁) lawP lawR x := by
  unfold hybI1 contI
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.pure_bind]
  conv_lhs => enter [2, B₀]; rw [PMF.bind_comm]
  conv_lhs => rw [PMF.bind_comm]

omit [DecidableEq R] [Nonempty Wd] in
/-- The ideal view with the law of `B₁` of the final view is the final view. -/
theorem idealView_eq_final (lawE : PMF (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R))
    (x : S.Attr → Bool) (M : Bool) :
    idealView (S := S) (Wd := Wd) lawB₁ = finalView (Wd := Wd) lawB₁ lawE x M :=
  (finalView_prod lawB₁ lawE x M).symm

end AdvancedEncryption.RingBTVW
