import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseCoordinates

/-! Measurable transverse transport over the punctured mark space. -/
noncomputable section
open MeasureTheory SigabaNeo.Rogers Matrix Matrix.SpecialLinearGroup
namespace SigabaNeo.Wall1

def markAction {n : ℕ} (a : SL n) (x : E n) : E n := WithLp.toLp 2 (a • WithLp.ofLp x)

theorem markAction_mul {n : ℕ} (a b : SL n) (x : E n) :
    markAction (a*b) x = markAction a (markAction b x) := by simp [markAction, mul_smul]

theorem markedColumn_mul {n : ℕ} (hn : 2 ≤ n) (a g : SL n) :
    markedColumn hn (a*g) = markAction a (markedColumn hn g) := by
  simp [markedColumn, latticePoint, markAction, mul_smul]

private def rot {m : ℕ} (i : Fin m) (x : E (m+1)) : SL (m+1) :=
  let b := (EuclideanSpace.basisFun (Fin (m+1)) ℝ).toBasis
  ⟨LinearMap.toMatrix b b (transverseRotation i x).toLinearMap, by
    rw [LinearMap.det_toMatrix, transverseRotation_det]⟩

private theorem rot_apply {m : ℕ} (i : Fin m) (x y : E (m+1)) :
    markAction (rot i x) y = transverseRotation i x y := by
  let b := (EuclideanSpace.basisFun (Fin (m+1)) ℝ).toBasis
  exact congrArg (WithLp.toLp 2)
    (LinearMap.toMatrix_mulVec_repr b b (transverseRotation i x).toLinearMap y)

private theorem rot_meas {m : ℕ} (i : Fin m) : Measurable (rot i) := by
  let : BorelSpace (SL (m+1)) := ⟨rfl⟩
  change @Measurable _ _ _ (@borel _ (TopologicalSpace.induced Subtype.val _)) _
  rw [borel_comap, ← BorelSpace.measurable_eq (α := Matrix (Fin (m+1)) (Fin (m+1)) ℝ)]
  apply Measurable.subtype_mk
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro k
  change Measurable fun x ↦ transverseRotation i x (basisVector k) j
  exact (PiLp.continuous_apply 2 _ j).measurable.comp
    ((measurable_transverseRotation i).comp (measurable_id.prodMk measurable_const))

private def radiusUnit {n : ℕ} (x : E n) := if x = 0 then 1 else ‖x‖

private theorem radiusUnit_ne {n : ℕ} (x : E n) : radiusUnit x ≠ 0 := by
  by_cases hx : x = 0 <;> simp [radiusUnit, hx]

/-- A measurable determinant-one completion of each nonzero first column. -/
def markSection {m : ℕ} (i : Fin m) (x : E (m+1)) : SL (m+1) :=
  (rot i x)⁻¹ * diag2n (Fin.succ_ne_zero i |>.symm) (radiusUnit x) (radiusUnit_ne x)

theorem measurable_markSection {m : ℕ} (i : Fin m) : Measurable (markSection i) := by
  let : BorelSpace (SL (m+1)) := ⟨rfl⟩
  let : PolishSpace (Matrix (Fin (m+1)) (Fin (m+1)) ℝ) := inferInstanceAs (PolishSpace (Fin (m+1) → Fin (m+1) → ℝ))
  let : PolishSpace (SL (m+1)) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  apply (rot_meas i).inv.mul
  change @Measurable _ _ _ (@borel _ (TopologicalSpace.induced Subtype.val _)) _
  rw [borel_comap, ← BorelSpace.measurable_eq (α := Matrix (Fin (m+1)) (Fin (m+1)) ℝ)]
  apply Measurable.subtype_mk
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro k
  have hr : Measurable (@radiusUnit (m+1)) :=
    Measurable.ite (measurableSet_singleton 0) measurable_const measurable_id.norm
  simp only [diagonal_apply]
  split_ifs <;> first | exact hr | exact hr.inv | exact measurable_const

theorem markSection_spec {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1) {x : E (m+1)} (hx : x ≠ 0) :
    markedColumn hn (markSection i x) = x := by
  have hcol (g : SL (m+1)) : markedColumn hn g = markAction g (basisVector 0) := by
    change WithLp.toLp 2 (g.val.mulVec _) = WithLp.toLp 2 (g.val.mulVec _)
    congr 2
    ext k
    by_cases h : k = 0 <;> simp [Pi.single_apply, PiLp.single_apply, h]
  apply (transverseRotation i x).injective
  rw [hcol, ← rot_apply, ← markAction_mul, markSection, mul_inv_cancel_left,
    transverseRotation_mark]
  change WithLp.toLp 2 ((diag2n _ _ _).val.mulVec _) = _
  ext j
  simp [diag2n_coe, Matrix.mulVec_diagonal, PiLp.smul_apply, PiLp.single_apply, radiusUnit, hx]
  split_ifs <;> simp_all

theorem markAction_ne_zero {n : ℕ} (a : SL n) {x : E n} (hx : x ≠ 0) :
    markAction a x ≠ 0 := by
  intro h
  have e := congrArg (markAction a⁻¹) h
  rw [← markAction_mul, inv_mul_cancel] at e
  apply hx
  simpa [markAction, Matrix.SpecialLinearGroup.smul_def] using e

theorem markedColumn_nonzero {n : ℕ} (hn : 2 ≤ n) (g : SL n) : markedColumn hn g ≠ 0 := by
  rw [← mul_one g, markedColumn_mul]
  apply markAction_ne_zero
  intro hz
  have e := congrArg (fun y : E n ↦ y ⟨0, by omega⟩) hz
  simp [markedColumn, latticePoint, Pi.single_apply] at e

/-- The transverse frame change for a parent transformation at a prescribed mark. -/
def transverseCocycle {m : ℕ} (i : Fin m) (a : SL (m+1)) (x : E (m+1)) : SL m :=
  if x = 0 then 1 else transverseFrame i (a * markSection i x) *
    (transverseFrame i (markSection i x))⁻¹

theorem measurable_transverseCocycle {m : ℕ} (i : Fin m) :
    Measurable fun p : SL (m+1) × E (m+1) ↦ transverseCocycle i p.1 p.2 := by
  let pol (n : ℕ) : PolishSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (PolishSpace (Fin n → Fin n → ℝ))
  let pol' (n : ℕ) : PolishSpace (SL n) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let bor (n : ℕ) : BorelSpace (SL n) := ⟨rfl⟩
  unfold transverseCocycle
  apply Measurable.ite (measurable_snd (measurableSet_singleton 0)) measurable_const
  have hs : Measurable (fun p : SL (m+1) × E (m+1) ↦ markSection i p.2) :=
    (measurable_markSection i).comp measurable_snd
  exact ((measurable_transverseFrame i).comp (measurable_fst.mul hs)).mul
    ((measurable_transverseFrame i).comp hs).inv

theorem transverseCocycle_frame {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1) (a g : SL (m+1)) :
    transverseFrame i (a*g) = transverseCocycle i a (markedColumn hn g) * transverseFrame i g := by
  let x := markedColumn hn g
  have hx := markedColumn_nonzero hn g
  have hs := markSection_spec i hn hx
  obtain ⟨h, hh⟩ := transverseFrame_transport i hn a (markSection i x)
  rw [hh g hs.symm]
  simp [transverseCocycle, hx, hh (markSection i x) rfl, x] at *

theorem transverseCocycle_mul {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (a b : SL (m+1)) (x : E (m+1)) :
    transverseCocycle i (a*b) x = transverseCocycle i a (markAction b x) * transverseCocycle i b x := by
  by_cases hx : x = 0
  · simp [hx, transverseCocycle, markAction]
  let g := markSection i x
  have hg : markedColumn hn g = x := markSection_spec i hn hx
  apply mul_right_cancel (b := transverseFrame i g)
  rw [← hg, ← transverseCocycle_frame, mul_assoc, mul_assoc, ← transverseCocycle_frame,
    ← markedColumn_mul, ← transverseCocycle_frame]

theorem transverseCocycle_stabilizer {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (x : E (m+1)) (hx : x ≠ 0) (h : SL m) :
    ∃ a : SL (m+1), markAction a x = x ∧ transverseCocycle i a x = h := by
  let g := markSection i x
  have hg : markedColumn hn g = x := markSection_spec i hn hx
  obtain ⟨a, ha⟩ := transverseFrame_stabilizer_surjective i hn g h
  obtain ⟨hfix, hframe⟩ := ha g rfl
  rw [markedColumn_mul, hg] at hfix
  rw [transverseCocycle_frame i hn, hg] at hframe
  exact ⟨a, hfix, mul_right_cancel hframe⟩

#print axioms measurable_transverseCocycle
#print axioms transverseCocycle_frame
#print axioms transverseCocycle_mul
#print axioms transverseCocycle_stabilizer
end SigabaNeo.Wall1
