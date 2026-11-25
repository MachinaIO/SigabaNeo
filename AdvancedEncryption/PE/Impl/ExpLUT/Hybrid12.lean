import PE.Impl.ExpLUT.HybView
import PE.Impl.ExpLUT.HybLaws

/-!
# Hybrids H1 (programming) and H2 (encodings from `b`)

The laws of the views of `PE.Impl.ExpLUT.HybView` (ePrint 2026/2539, Appendix A), with the binary
trapdoor `T` (TrapGen: `B⁽¹⁾ = [Ā | g − Ā T]`) and binary programming matrices, all supported on the
`Ā` columns:

* `hyb1`: **H1**: the seed `B̄ = [Ā; B̄⁽²⁾]`, the trapdoor hashes `B̄ T` (`thLaw`), the rest of the
  public data, `Enc`'s coins, and the binary programming `zr`; the programmed public key and `Enc`'s
  ciphertext. `hyb1u`: the same with uniform values in place of the programming hashes `B̄ · zr i`.
  `hybrid1_close`: **H1 ≈ H1u**, within `|PrI| · √(|R|² 2^{−m̄})/2` (leftover hash lemma, seed `B̄`,
  `closeTo_binaryHash_bind_mid`).
* `hyb2`: **H2**: the ciphertext from `b`. `hybrid2_close`: **H1 ≈ H2** within the flooding distance
  `ε` of the flooding errors' law under the shifts `floodShift` (`view1_eq_view2`), for every `ē_b`
  in the support of the error law (the hypothesis `hflood`, discharged at the concrete parameters by
  `SigabaNeo.Lattices.closeTo_floodLaw_add`).
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J] [Fintype Pos]
  [DecidableEq Pos]

variable (S J) in
/-- The rest of the public data: the gadget columns of `B⁽²⁾`, the `H_k`, `d`. -/
abbrev RestPub := (Fin S.τ → R) × (J → Matrix (Fin 2) (Col S.τ) R) × (Fin 2 → R)

/-- The gadget columns of `B⁽¹⁾ = [Ā | g − Ā T]` from the trapdoor hashes `B̄ T`. -/
def bg1Of (th : Fin S.τ → Fin 2 → R) : Fin S.τ → R := fun c => S.D.g c - th c 0

/-- The public data from its parts. -/
def pubOf (Bb : Matrix (Fin 2) Wb R) (Bg1 : Fin S.τ → R) (rp : RestPub S J) : PubData S Wb J :=
  ⟨Bb, Bg1, rp.1, rp.2.1, rp.2.2⟩

variable (S) in
/-- The trapdoor hashes `B̄ T` for a uniform binary `T`. -/
noncomputable def thLaw (Bb : Matrix (Fin 2) Wb R) : PMF (Fin S.τ → Fin 2 → R) :=
  PMF.pi fun _ : Fin S.τ => (PMF.uniformOfFintype (Wb → Bool)).map (binaryHash Bb)

variable (S Wb Pos) in
/-- The binary programming vectors. -/
noncomputable def zrLaw : PMF (PrI S Pos → Wb → Bool) :=
  PMF.pi fun _ : PrI S Pos => PMF.uniformOfFintype (Wb → Bool)

variable (M : HelperMap S J) (w : ℕ) (half : R) (χs χ χfl : PMF R)

/-- **H1**: the programmed public key and `Enc`'s ciphertext of `0`. -/
noncomputable def hyb1 (x : Pos → ℕ) : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (PMF.uniformOfFintype (Matrix (Fin 2) Wb R)).bind fun Bb =>
  (thLaw S Bb).bind fun th => (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
  (encCoinsLaw S Wb J Pos χs χ χfl).bind fun r =>
  (zrLaw S Wb Pos).map fun zr => view1 M w half (pubOf Bb (bg1Of th) rp) x (hpOf Bb zr) r

/-- **H1u**: H1 with uniform values in place of the programming hashes. -/
noncomputable def hyb1u (x : Pos → ℕ) : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (PMF.uniformOfFintype (Matrix (Fin 2) Wb R)).bind fun Bb =>
  (thLaw S Bb).bind fun th => (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
  (encCoinsLaw S Wb J Pos χs χ χfl).bind fun r =>
  (PMF.pi fun _ : PrI S Pos => PMF.uniformOfFintype (Fin 2 → R)).map fun hp =>
    view1 M w half (pubOf Bb (bg1Of th) rp) x hp r

/-- **H2**: the ciphertext from `b`. -/
noncomputable def hyb2 (x : Pos → ℕ) : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (PMF.uniformOfFintype (Matrix (Fin 2) Wb R)).bind fun Bb =>
  (thLaw S Bb).bind fun th => (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
  (encCoinsLaw S Wb J Pos χs χ χfl).bind fun r =>
  (zrLaw S Wb Pos).map fun zr =>
    view2 M w (pubOf Bb (bg1Of th) rp) x zr (coreOf M (pubOf Bb (bg1Of th) rp) r) (floodOf r)

/-- The statistical distance of hybrid H1: `|PrI| · √(|R|² 2^{−m̄})/2`. -/
noncomputable def delta1 (S : Setting R) (Wb Pos : Type) [Fintype Wb] [Fintype Pos] :
    ℝ≥0∞ :=
  ENNReal.ofReal (Fintype.card (PrI S Pos) *
    (Real.sqrt (Fintype.card (Fin 2 → R) * (2 ^ Fintype.card Wb : ℝ)⁻¹) / 2))

/-- **Hybrid H1** (programming, leftover hash lemma with seed `B̄`). -/
theorem hybrid1_close (x : Pos → ℕ) :
    CloseTo (hyb1 (Wb := Wb) M w half χs χ χfl x) (hyb1u (Wb := Wb) M w half χs χ χfl x)
      (delta1 S Wb Pos) := by
  have h := closeTo_binaryHash_bind_mid (R := R) (rr := Fin 2) (mm := Wb) (I := PrI S Pos)
    (fun Bb => (thLaw S Bb).bind fun th => (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
      (encCoinsLaw S Wb J Pos χs χ χfl).map fun r => (th, rp, r))
    (fun Bb c hp => PMF.pure (view1 M w half (pubOf Bb (bg1Of c.1) c.2.1) x hp c.2.2))
  unfold hyb1 hyb1u delta1
  convert h using 2
  · funext Bb
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.bind_pure_comp]
    refine congrArg (PMF.bind _) (funext fun th => congrArg (PMF.bind _) (funext fun rp =>
      congrArg (PMF.bind _) (funext fun r => ?_)))
    unfold zrLaw
    rw [Cslib.Probability.PMF.pi_map, PMF.bind_map]
    rfl
  · funext Bb
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.bind_pure_comp]
    rfl

/-! ### H2: flooding -/

variable (S Pos) in
/-- The law of the flooding errors, as `Enc` draws them. -/
noncomputable def floodLaw : PMF (FloodV S Pos) :=
  (iidFam χfl (Fin S.b × Dig S.τ) (Col S.τ)).bind fun eaut =>
  (iidFam χfl Pos (Col S.τ)).bind fun ein =>
  (iidFam χfl (Pos × Dig S.τ) (Col S.τ)).bind fun edin =>
  (iidLaw χfl (Col S.τ)).map fun e0 => ((fun t d => eaut (t, d)), ein, (fun t d => edin (t, d)), e0)

omit [DecidableEq R] [DecidableEq Wb] [Nonempty Wb] [DecidableEq J] [DecidableEq Pos] in
/-- `Enc`'s coins with the flooding errors drawn together. -/
theorem encCoinsLaw_eq :
    encCoinsLaw S Wb J Pos χs χ χfl =
      χs.bind fun s => (iidLaw χ (BCol Wb S.τ)).bind fun eb => (iidFam χ J (Col S.τ)).bind fun eh =>
      (floodLaw S Pos χfl).bind fun fl => χ.map fun em =>
        (⟨s, eb, eh, fl.1, fl.2.1, fl.2.2.1, fl.2.2.2, em⟩ : EncCoins S Wb J Pos) := by
  unfold encCoinsLaw floodLaw
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

omit [Fintype R] [DecidableEq R] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J]
  [Fintype Pos] [DecidableEq Pos] in
theorem view1_pubOf (Bb : Matrix (Fin 2) Wb R) (Bg1 : Fin S.τ → R) (rp : RestPub S J) (x : Pos → ℕ)
    (zr : PrI S Pos → Wb → Bool) (r : EncCoins S Wb J Pos) :
    view1 M w half (pubOf Bb Bg1 rp) x (hpOf Bb zr) r =
      view2 M w (pubOf Bb Bg1 rp) x zr (coreOf M (pubOf Bb Bg1 rp) r) (floodOf r + floodShift r.eb zr) :=
  view1_eq_view2 M w half (pubOf Bb Bg1 rp) x zr r

omit [DecidableEq R] [Nonempty Wb] [DecidableEq Pos] in
/-- **Hybrid H2** (encodings from `b`, noise flooding): H1 and H2 are within `ε` when the flooding
errors' law moves by at most `ε` under every shift `floodShift ē_b zr` with `ē_b` in the support of
the error law. -/
theorem hybrid2_close (x : Pos → ℕ) {ε : ℝ≥0∞}
    (hflood : ∀ eb ∈ (iidLaw χ (BCol Wb S.τ)).support, ∀ zr : PrI S Pos → Wb → Bool,
      CloseTo ((floodLaw S Pos χfl).map (· + floodShift eb zr)) (floodLaw S Pos χfl) ε) :
    CloseTo (hyb1 (Wb := Wb) M w half χs χ χfl x) (hyb2 (Wb := Wb) M w χs χ χfl x) ε := by
  unfold hyb1 hyb2
  simp only [view1_pubOf]
  refine CloseTo.bind_right _ fun Bb _ => CloseTo.bind_right _ fun th _ =>
    CloseTo.bind_right _ fun rp _ => ?_
  set P := pubOf Bb (bg1Of th) rp
  simp only [PMF.map, Function.comp_def]
  rw [PMF.bind_comm (encCoinsLaw S Wb J Pos χs χ χfl),
    PMF.bind_comm (encCoinsLaw S Wb J Pos χs χ χfl)]
  refine CloseTo.bind_right _ fun zr _ => ?_
  rw [encCoinsLaw_eq]
  simp only [PMF.bind_bind, PMF.map_bind, PMF.bind_map, Function.comp_def]
  refine CloseTo.bind_right _ fun s _ => CloseTo.bind_right _ fun eb heb =>
    CloseTo.bind_right _ fun eh _ => ?_
  have h := (hflood eb heb zr).bind_left fun fl => (χ.map fun em =>
    (⟨s, eb, eh, fl.1, fl.2.1, fl.2.2.1, fl.2.2.2, em⟩ : EncCoins S Wb J Pos)).bind fun r =>
      PMF.pure (view2 M w P x zr (coreOf M P r) (floodOf r))
  simp only [PMF.bind_map, Function.comp_def] at h
  convert h using 2
  funext fl
  rfl

end AdvancedEncryption.ExpLUT
