import PE.Impl.ExpLUT.Hybrid0

/-!
# Hybrid H3′: `B⁽¹⁾` uniform

In H2 the keys are answered without the trapdoor (`keyLaw_sim_eq_ideal`, Lemma 11), so the
trapdoor `T` of `B⁽¹⁾ = [Ā | g − Ā T]` is used by nothing else: `(Ā, Ā T)` with binary `T` is close
to `(Ā, u)` with uniform `u` by the leftover hash lemma (seed `B̄ = [Ā; B̄⁽²⁾]`, `τ` columns), and
`g − u` is uniform (`hybrid23_close`, within `deltaT = τ · √(|R|² 2^{−m̄})/2`).

`hyb3`: **H3′**: H2 with uniform gadget columns of `B⁽¹⁾`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J] [Fintype Pos]
  [DecidableEq Pos] (M : HelperMap S J) (w : ℕ) (χs χ χfl : PMF R)

/-- **H3′**: H2 with uniform gadget columns of `B⁽¹⁾`. -/
noncomputable def hyb3 (x : Pos → ℕ) : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (PMF.uniformOfFintype (Matrix (Fin 2) Wb R)).bind fun Bb =>
  (PMF.uniformOfFintype (Fin S.τ → R)).bind fun Bg1 =>
  (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
  (encCoinsLaw S Wb J Pos χs χ χfl).bind fun r =>
  (zrLaw S Wb Pos).map fun zr =>
    view2 M w (pubOf Bb Bg1 rp) x zr (coreOf M (pubOf Bb Bg1 rp) r) (floodOf r)

variable (S Wb) in
/-- The statistical distance of the trapdoor step: `τ · √(|R|² 2^{−m̄})/2`. -/
noncomputable def deltaT : ℝ≥0∞ :=
  ENNReal.ofReal (Fintype.card (Fin S.τ) *
    (Real.sqrt (Fintype.card (Fin 2 → R) * (2 ^ Fintype.card Wb : ℝ)⁻¹) / 2))

omit [DecidableEq R] [Fintype J] [DecidableEq J] [Fintype Pos] [DecidableEq Pos] in
/-- `g − u` for uniform `u`: uniform. -/
theorem uniform_bg1Of_bind {β : Type} (K : (Fin S.τ → R) → PMF β) :
    (PMF.pi fun _ : Fin S.τ => PMF.uniformOfFintype (Fin 2 → R)).bind (fun th => K (bg1Of th)) =
      (PMF.uniformOfFintype (Fin S.τ → R)).bind K := by
  have hrow : (PMF.pi fun _ : Fin S.τ => PMF.uniformOfFintype (Fin 2 → R)).map (fun h i => h i 0) =
      PMF.uniformOfFintype (Fin S.τ → R) := by
    rw [← Cslib.Probability.PMF.pi_map (fun _ => PMF.uniformOfFintype (Fin 2 → R)) (fun _ u => u 0)]
    simp only [uniform_fin2_row0]
    exact Cslib.Probability.PMF.pi_uniformOfFintype
  have hg : bg1Of (S := S) = (Equiv.subLeft (S.D.g : Fin S.τ → R)) ∘ (fun h i => h i 0) := by
    funext th; rfl
  rw [show (fun th => K (bg1Of th)) = K ∘ bg1Of from rfl, ← PMF.bind_map, hg, ← PMF.map_comp, hrow,
    uniform_map_equiv]

/-- **H2 ≈ H3′** (`B⁽¹⁾` uniform), within `deltaT`. -/
theorem hybrid23_close (x : Pos → ℕ) :
    CloseTo (hyb2 (Wb := Wb) M w χs χ χfl x) (hyb3 M w χs χ χfl x) (deltaT S Wb) := by
  have h := closeTo_binaryHash_bind (R := R) (rr := Fin 2) (mm := Wb) (I := Fin S.τ)
    (fun Bb th => (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
      (encCoinsLaw S Wb J Pos χs χ χfl).bind fun r => (zrLaw S Wb Pos).map fun zr =>
        view2 M w (pubOf Bb (bg1Of th) rp) x zr (coreOf M (pubOf Bb (bg1Of th) rp) r) (floodOf r))
  unfold hyb2 hyb3 deltaT
  convert h using 2
  · rfl
  funext Bb
  exact (uniform_bg1Of_bind (fun Bg1 => (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
      (encCoinsLaw S Wb J Pos χs χ χfl).bind fun r => (zrLaw S Wb Pos).map fun zr =>
        view2 M w (pubOf Bb Bg1 rp) x zr (coreOf M (pubOf Bb Bg1 rp) r) (floodOf r))).symm

end AdvancedEncryption.ExpLUT
