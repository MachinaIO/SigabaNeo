import PE.Impl.ExpLUT.Hybrid5U

/-!
# Hybrid H6: `B⁽¹⁾` from TrapGen again — the ideal view

In H5 the ciphertext is uniform and independent of the public key, whose `B⁽¹⁾` has uniform gadget
columns. H6 draws `B⁽¹⁾ = [Ā | g − Ā T]` with a binary `T` again (leftover hash lemma, as in
`hybrid23_close`): `hybrid56_close`, within `deltaT`. H6 is **the view of the ideal experiment**
with the simulator's uniform ciphertext `ctU` (`idealView_eq`): `Setup`'s public key (C's
`setupLaw` with the binary trapdoor law) and an independent uniform ciphertext.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J] [Fintype Pos]
  [DecidableEq Pos]

/-- The public key of H6: TrapGen's `B⁽¹⁾`, the other components uniform. -/
noncomputable def mpkT : PMF (MPK S Wb J Pos) :=
  (PMF.uniformOfFintype (Matrix (Fin 2) Wb R)).bind fun Bb =>
  (thLaw S Bb).bind fun th =>
  (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
  (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun a =>
  (PMF.uniformOfFintype (Matrix (Fin 2) (Col S.τ) R)).bind fun A0 =>
  (PMF.uniformOfFintype (Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Ain =>
  (PMF.uniformOfFintype (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).map fun Aaut =>
    mpkOf (pubOf Bb (bg1Of th) rp) a A0 Ain Aaut

/-- **H6**: TrapGen's public key and the uniform ciphertext. -/
noncomputable def final6 : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (mpkT (S := S) (Wb := Wb) (J := J) (Pos := Pos)).bind fun mpk =>
    (ctU S Wb J Pos).map fun ct => (mpk, ct)

/-- **H5 ≈ H6** (`B⁽¹⁾` from TrapGen), within `deltaT`. -/
theorem hybrid56_close :
    CloseTo (final5 (S := S) (Wb := Wb) (J := J) (Pos := Pos)) final6 (deltaT S Wb) := by
  have h := closeTo_binaryHash_bind (R := R) (rr := Fin 2) (mm := Wb) (I := Fin S.τ)
    (fun Bb th => (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
      (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun a =>
      (PMF.uniformOfFintype (Matrix (Fin 2) (Col S.τ) R)).bind fun A0 =>
      (PMF.uniformOfFintype (Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Ain =>
      (PMF.uniformOfFintype (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Aaut =>
      (ctU S Wb J Pos).map fun ct => (mpkOf (pubOf Bb (bg1Of th) rp) a A0 Ain Aaut, ct))
  unfold final5 final6 mpkU mpkT deltaT
  simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
  refine (CloseTo.symm ?_)
  convert h using 2
  · rfl
  funext Bb
  exact (uniform_bg1Of_bind (fun Bg1 => (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
      (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun a =>
      (PMF.uniformOfFintype (Matrix (Fin 2) (Col S.τ) R)).bind fun A0 =>
      (PMF.uniformOfFintype (Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Ain =>
      (PMF.uniformOfFintype (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Aaut =>
      (ctU S Wb J Pos).map fun ct => (mpkOf (pubOf Bb Bg1 rp) a A0 Ain Aaut, ct))).symm

/-- **The view of the ideal experiment**: `Setup`'s public key and the simulator's uniform
ciphertext. -/
noncomputable def idealView : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (setupLaw S Wb J Pos bitLaw).bind fun v => (ctU S Wb J Pos).map fun ct => (v.1, ct)

/-- **H6 is the ideal view.** -/
theorem idealView_eq : idealView (S := S) (Wb := Wb) (J := J) (Pos := Pos) = final6 := by
  unfold idealView final6 mpkT setupLaw setupCoinsLaw
  simp only [PMF.bind_bind, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
    PMF.pure_bind, iidFam_bitLaw]
  rw [uniform_rows_bind]
  refine congrArg (PMF.bind _) (funext fun Ab => ?_)
  unfold thLaw
  simp only [uniform_sum_bind, Cslib.Probability.PMF.pi_map, PMF.bind_map, Function.comp_def,
    uniform_prod_bind]
  conv_lhs => rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  rfl

end AdvancedEncryption.ExpLUT
