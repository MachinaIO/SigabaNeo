import PE.Impl.ExpLUT.Reduction

/-!
# Hybrid H5: the programmed matrices and their encodings uniform

In H4 the core values `(b, h_k, c_m)` are uniform, so `b̄` (the `Ā` columns of `b`) is a uniform
row independent of `B̄`, and every programmed pair `(B̄ R + d G, b̄ R + e)` is a hash of the binary
vector `R` by the **3-row seed** `B₃ = [B̄; b̄]` (Appendix A, H5). The view of H4 depends on the
programming only through these hashes (`view2_eq_viewH`, `viewH`), so the leftover hash lemma
replaces them by uniform values (`hybrid45_close`, within `|PrI| · √(|R|³ 2^{−m̄})/2`).

* `viewH`: H2's view from the hash values `hp` (rows of `B̄ R`) and `hb` (`b̄ R`).
* `hyb5`: **H5**: uniform 3-row hash values.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J] [Fintype Pos]
  [DecidableEq Pos] (M : HelperMap S J) (w : ℕ) (χfl : PMF R)

/-- The bottom rows of the `C^in_t` from hash values: `B̄⁽²⁾ Z_t − b̄ Z_t + e_t + X^{w x_t} G⁽²⁾`. -/
def cbH (x : Pos → ℕ) (hp : PrI S Pos → Fin 2 → R) (hb : PrI S Pos → R) (fl : FloodV S Pos) :
    Pos → Col S.τ → R :=
  fun t c => hp (.inl (t, c)) 1 - hb (.inl (t, c)) + fl.2.1 t c + S.E.X ^ (w * x t) * S.G 1 c

/-- The ciphertext from hash values. -/
def ctH (core : Core S Wb J) (hb : PrI S Pos → R) (fl : FloodV S Pos) (cb : Pos → Col S.τ → R) :
    Ciphertext S Wb J Pos where
  b := core.1
  h := core.2.1
  caut t d c := S.E.σ (S.kf t) (hb (.inr (.inr (.inr (t, d, c))))) + fl.1 t d c
  cinBot := cb
  cin t d c := hb (.inr (.inr (.inl (t, d, c)))) + fl.2.2.1 t d c
  c0 c := hb (.inr (.inl c)) + fl.2.2.2 c
  cm := core.2.2

/-- **The view of H2–H4 from the hash values.** -/
def viewH (P : PubData S Wb J) (x : Pos → ℕ) (hp : PrI S Pos → Fin 2 → R) (hb : PrI S Pos → R)
    (core : Core S Wb J) (fl : FloodV S Pos) : MPK S Wb J Pos × Ciphertext S Wb J Pos :=
  (progMPK M w P x hp core.2.1 (cbH w x hp hb fl), ctH core hb fl (cbH w x hp hb fl))

theorem view2_eq_viewH (P : PubData S Wb J) (x : Pos → ℕ) (zr : PrI S Pos → Wb → Bool)
    (core : Core S Wb J) (fl : FloodV S Pos) :
    view2 M w P x zr core fl =
      viewH M w P x (hpOf P.Bb zr) (fun i => (fun v => core.1 (.inl v)) ⬝ᵥ bv (zr i)) core fl := by
  have hcb : cb2 w P x zr core fl = cbH w x (hpOf P.Bb zr) (fun i => (fun v => core.1 (.inl v)) ⬝ᵥ bv (zr i)) fl := by
    funext t c
    simp only [cb2, cbH, hpOf_apply, sub_dotProduct]
  unfold view2 viewH
  rw [hcb]
  rfl

/-- The 3-row seed `B₃ = [B̄; b̄]`. -/
def rows3Equiv (Wb : Type) : Matrix (Fin 2) Wb R × (Wb → R) ≃ Matrix (Fin 3) Wb R where
  toFun p := Matrix.of ![p.1 0, p.1 1, p.2]
  invFun B := (Matrix.of ![B 0, B 1], B 2)
  left_inv p := by
    obtain ⟨B, b⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    ext i j; fin_cases i <;> rfl
  right_inv B := by ext i j; fin_cases i <;> rfl

theorem uniform_rows3_bind {β : Type} (g : Matrix (Fin 2) Wb R → (Wb → R) → PMF β) :
    (PMF.uniformOfFintype (Matrix (Fin 2) Wb R)).bind (fun Bb =>
      (PMF.uniformOfFintype (Wb → R)).bind (g Bb)) =
    (PMF.uniformOfFintype (Matrix (Fin 3) Wb R)).bind fun B3 =>
      g (Matrix.of ![B3 0, B3 1]) (B3 2) := by
  rw [← bind_uniform_equiv (rows3Equiv Wb), uniform_prod_bind]
  refine congrArg (PMF.bind _) (funext fun B => congrArg (PMF.bind _) (funext fun b => ?_))
  have : (Matrix.of ![(rows3Equiv Wb (B, b)) 0, (rows3Equiv Wb (B, b)) 1] : Matrix (Fin 2) Wb R) =
      B := by
    ext i j; fin_cases i <;> rfl
  rw [this]
  rfl

/-- The rows of `B̄ R` among the 3-row hash values. -/
def hp3 (h3 : PrI S Pos → Fin 3 → R) : PrI S Pos → Fin 2 → R := fun i ρ => h3 i ρ.castSucc

/-- The row `b̄ R` among the 3-row hash values. -/
def hb3 (h3 : PrI S Pos → Fin 3 → R) : PrI S Pos → R := fun i => h3 i 2

variable (S J Pos) in
/-- The coins of H4 other than `B₃` and the programming: the gadget columns of `B⁽¹⁾`, the rest of
the public data, the gadget columns of `b`, the helpers, `c_m`, the flooding errors. -/
abbrev Mid5 := (Fin S.τ → R) × RestPub S J × (Fin S.τ → R) × (J → Col S.τ → R) × R × FloodV S Pos

variable (S J Pos) in
/-- Their law. -/
noncomputable def mid5Law : PMF (Mid5 S J Pos) :=
  (PMF.uniformOfFintype (Fin S.τ → R)).bind fun Bg1 => (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
  (PMF.uniformOfFintype (Fin S.τ → R)).bind fun bg => (PMF.uniformOfFintype (J → Col S.τ → R)).bind fun h =>
  (PMF.uniformOfFintype R).bind fun cm => (floodLaw S Pos χfl).map fun fl => (Bg1, rp, bg, h, cm, fl)

/-- The view of H4/H5 from `B₃`, the other coins and the 3-row hash values. -/
def view5 (x : Pos → ℕ) (B3 : Matrix (Fin 3) Wb R) (c : Mid5 S J Pos) (h3 : PrI S Pos → Fin 3 → R) :
    MPK S Wb J Pos × Ciphertext S Wb J Pos :=
  viewH M w (pubOf (Matrix.of ![B3 0, B3 1]) c.1 c.2.1) x (hp3 h3) (hb3 h3)
    (Sum.elim (B3 2) c.2.2.1, c.2.2.2.1, c.2.2.2.2.1) c.2.2.2.2.2

/-- **H4 in hash form**: the seed `B₃`, the other coins, the 3-row hashes. -/
noncomputable def hyb4L (x : Pos → ℕ) : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (PMF.uniformOfFintype (Matrix (Fin 3) Wb R)).bind fun B3 => (mid5Law S J Pos χfl).bind fun c =>
  (PMF.pi fun _ : PrI S Pos => (PMF.uniformOfFintype (Wb → Bool)).map (binaryHash B3)).bind fun h3 =>
    PMF.pure (view5 M w x B3 c h3)

/-- **H5**: uniform 3-row hash values. -/
noncomputable def hyb5 (x : Pos → ℕ) : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (PMF.uniformOfFintype (Matrix (Fin 3) Wb R)).bind fun B3 => (mid5Law S J Pos χfl).bind fun c =>
  (PMF.pi fun _ : PrI S Pos => PMF.uniformOfFintype (Fin 3 → R)).bind fun h3 =>
    PMF.pure (view5 M w x B3 c h3)

theorem hyb4_eq_L (x : Pos → ℕ) : hyb4 (Wb := Wb) M w χfl x = hyb4L M w χfl x := by
  unfold hyb4 hyb4L mid5Law
  simp only [uniform_prod_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [uniform_sum_bind]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0]; rw [PMF.bind_comm]
  rw [uniform_rows3_bind]
  refine congrArg (PMF.bind _) (funext fun B3 => ?_)
  refine congrArg (PMF.bind _) (funext fun Bg1 => ?_)
  refine congrArg (PMF.bind _) (funext fun B2g => ?_)
  refine congrArg (PMF.bind _) (funext fun H => ?_)
  refine congrArg (PMF.bind _) (funext fun d => ?_)
  refine congrArg (PMF.bind _) (funext fun bg => ?_)
  refine congrArg (PMF.bind _) (funext fun h => ?_)
  refine congrArg (PMF.bind _) (funext fun cm => ?_)
  refine congrArg (PMF.bind _) (funext fun fl => ?_)
  unfold zrLaw
  rw [Cslib.Probability.PMF.pi_map, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun zr => ?_)
  simp only [Function.comp_apply, view5]
  rw [view2_eq_viewH]
  congr 2
  · funext i ρ; fin_cases ρ <;> rfl

variable (S Wb Pos) in
/-- The statistical distance of H5: `|PrI| · √(|R|³ 2^{−m̄})/2`. -/
noncomputable def delta5 : ℝ≥0∞ :=
  ENNReal.ofReal (Fintype.card (PrI S Pos) *
    (Real.sqrt (Fintype.card (Fin 3 → R) * (2 ^ Fintype.card Wb : ℝ)⁻¹) / 2))

/-- **H4 ≈ H5** (leftover hash lemma with the 3-row seed `[B̄; b̄]`). -/
theorem hybrid45_close (x : Pos → ℕ) :
    CloseTo (hyb4L (Wb := Wb) M w χfl x) (hyb5 M w χfl x) (delta5 S Wb Pos) :=
  closeTo_binaryHash_bind_mid (R := R) (rr := Fin 3) (mm := Wb) (I := PrI S Pos)
    (fun _ => mid5Law S J Pos χfl) (fun B3 c h3 => PMF.pure (view5 M w x B3 c h3))

end AdvancedEncryption.ExpLUT
