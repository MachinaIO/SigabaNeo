import PE.Impl.ExpLUT.HybView
import PE.Impl.ExpLUT.SimTrap
import PE.Impl.ExpLUT.HybLaws

/-!
# The key oracles of the hybrids

In every hybrid the key oracle answers with the ideal key law `idealKeyLaw` of `M_F`, a function of
`mpk` and `F` only (`PE.Impl.ExpLUT.GameChain`, `KGi`). This file states why each challenger may do
so:

* **the real `KeyGen`** (`keyGenLaw_eq_ideal`): on the support of `Setup`, the box sampler with the
  TrapGen trapdoor `blockdiag σ_i(T)` has the ideal law (`realTrap_good`, `keyLaw_eq_ideal`), when
  the boxes cover its shifts;
* **the reduction** (`redKeyLaw_eq_ideal`, hybrid H3 of Appendix A): for the programmed public key
  of H2–H4 (`view2`, `programmed_view2`) and every unauthorized `F` (`F(x*) = 1`), the box sampler
  with the gadget trapdoor `T_sim` of Lemma 11, computed from the reduction's own programming
  (`redKeyLaw`: `R̂_F = simKey`, Corollary 1), has the ideal law, when the boxes cover its shifts
  (`rowBnd_simTrap` and `matBnd_simKey` bound them).

So the reduction answers key queries efficiently (no trapdoor of `B⁽¹⁾`), and its answers agree
with the hybrids' on every admissible query.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [DecidableEq Wb] [Fintype J] [DecidableEq J] [Fintype Pos] [DecidableEq Pos]
  (Big Small : Finset (PIdx Wb J S.τ S.E.W → R)) (hBig : Big.Nonempty)
  (dec : (Fin S.E.W → R) → ZIdx S.τ S.E.W → R) (M : HelperMap S J)

/-- **The real keys have the ideal law**, on the support of `Setup`, when the boxes cover the
shifts of the TrapGen trapdoor. -/
theorem keyGenLaw_eq_ideal (hdec : ∀ y, gadZ (dec y) = y) {χT : PMF R}
    {v : MPK S Wb J Pos × MSK S Wb J Pos} (hv : v ∈ (setupLaw S Wb J Pos χT).support) (F : BP Pos)
    (hcov : ∀ x ∈ Small, ∀ y, x + realTrap v.2.T (dec y) ∈ Big) :
    keyGenLaw Big Small hBig dec M v.2 F =
      (idealKeyLaw Big Small hBig dec M v.1 F).map keyOfOutput := by
  obtain ⟨hm, hT, -⟩ := mem_support_setupLaw hv
  unfold keyGenLaw
  rw [hm, keyLaw_eq_ideal Big Small hBig dec hdec M v.1 F _ (realTrap_good M v.1 F v.2.T hT) hcov]

variable (w : ℕ)

/-- **The reduction's key law**: one try of box rejection with the gadget trapdoor of Lemma 11,
computed from the programming `zr` of the view `view2`. -/
noncomputable def redKeyLaw (P : PubData S Wb J) (x : Pos → ℕ) (zr : PrI S Pos → Wb → Bool)
    (core : Core S Wb J) (fl : FloodV S Pos) (F : BP Pos) :
    PMF (Option ((PIdx Wb J S.τ S.E.W → R) × (ZIdx S.τ S.E.W → R))) :=
  keyLaw Big Small hBig dec M (view2 M w P x zr core fl).1 F
    (simTrap M (view2 M w P x zr core fl).1 F
      (simKey M (view2 M w P x zr core fl).1 F (view2 M w P x zr core fl).2 x (progOf zr)))

/-- **The reduction's keys have the ideal law** for every unauthorized `F` (`F(x) = 1`, `x` the
programmed attribute), when the boxes cover the shifts of `T_sim`. -/
theorem redKeyLaw_eq_ideal (hdec : ∀ y, gadZ (dec y) = y) (h8 : Lemma8 S) (F : BP Pos)
    (hF : F.WF S.E.W) (hw : F.w = w) (P : PubData S Wb J) (x : Pos → ℕ) (hx : ∀ t, x t < F.nsym)
    (hFx : F.eval x = 1) (zr : PrI S Pos → Wb → Bool) (core : Core S Wb J) (fl : FloodV S Pos)
    (hcov : ∀ x' ∈ Small, ∀ y, x' + simTrap M (view2 M w P x zr core fl).1 F
      (simKey M (view2 M w P x zr core fl).1 F (view2 M w P x zr core fl).2 x (progOf zr)) (dec y) ∈ Big) :
    redKeyLaw Big Small hBig dec M w P x zr core fl F =
      idealKeyLaw Big Small hBig dec M (view2 M w P x zr core fl).1 F := by
  subst hw
  have hP := programmed_view2 M F.w P x zr core fl
  have hS := corollary1 M h8 F hF hx hP
  rw [hFx, Nat.cast_one] at hS
  exact keyLaw_sim_eq_ideal M Big Small hBig dec hdec _ F hS hcov

/-- The programming matrices of `zr` are binary: entries of norm at most `‖1‖`, so
`matBnd_simKey` bounds `R̂_F` by `(stepBound S 1 1 1)^[T] 1` when `‖1‖ ≤ 1`. -/
theorem progBnd_progOf (N : NormSpec S) (h1 : N.nrm 1 ≤ 1) (zr : PrI S Pos → Wb → Bool) :
    ProgBnd (N := N) (progOf (J := J) zr) 1 1 := by
  have hb : ∀ b : Bool, N.nrm (bitVal b : R) ≤ 1 := by
    intro b; cases b
    · simp [bitVal, N.nrm_zero]
    · simpa [bitVal] using h1
  exact ⟨fun t i j => hb _, fun i j => hb _, fun t d i j => hb _, fun t d i j => hb _⟩

end AdvancedEncryption.ExpLUT
