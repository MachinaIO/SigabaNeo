import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoMinimumBound
import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseKernelLaw

/-! Transport of a twice-normalized frame over its two physical columns. -/
noncomputable section
open Matrix MeasureTheory SigabaNeo.Rogers
namespace SigabaNeo.Wall1.RankTwo

def column {n : ℕ} (g : SL n) (k : Fin n) : E n := WithLp.toLp 2 (g.val.col k)

theorem column_zero {m : ℕ} (hn : 2 ≤ m+1) (g : SL (m+1)) :
    column g 0 = markedColumn hn g := by
  change WithLp.toLp 2 _ = WithLp.toLp 2 (g.val.mulVec _)
  congr 1
  rw [← Matrix.mulVec_single_one g.val 0]
  congr 1
  ext k
  by_cases hk : k = 0 <;> simp [Pi.single_apply,hk]

theorem column_mul {n : ℕ} (a g : SL n) (k : Fin n) :
    column (a*g) k = markAction a (column g k) :=
  congrArg (WithLp.toLp 2) (Matrix.col_mul_eq_mulVec_col ..)

def normalizedTail {m : ℕ} (i : Fin m) (x : E (m+1)) : E (m+1) →ₗ[ℝ] E m where
  toFun y := WithLp.toLp 2 fun k ↦ ‖x‖ ^ (m : ℝ)⁻¹ * transverseRotation i x y k.succ
  map_add' u v := by ext k; simp [mul_add, PiLp.add_apply]
  map_smul' t v := by ext k; simp [PiLp.smul_apply]; ring

theorem normalizedTail_self {m : ℕ} (i : Fin m) (x : E (m+1)) :
    normalizedTail i x x = 0 := by
  ext k
  simp [normalizedTail, transverseRotation_mark, PiLp.smul_apply]

theorem normalizedTail_col {m : ℕ} (i : Fin m) (g : SL (m+1)) (k : Fin m) :
    normalizedTail i (column g 0) (column g k.succ) = column (transverseFrame i g) k := by
  rfl

theorem normalizedTail_mulVec {m : ℕ} (i : Fin m) (g : SL (m+1)) (v : Fin (m+1) → ℝ) :
    normalizedTail i (column g 0) (WithLp.toLp 2 (g • v)) =
      WithLp.toLp 2 (transverseFrame i g • fun k ↦ v k.succ) := by
  have expand {d : ℕ} (t : SL d) (w : Fin d → ℝ) :
      WithLp.toLp 2 (t • w) = ∑ k, w k • column t k := by
    ext k
    simp [column, Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct,
      mul_comm]
  rw [expand, map_sum, Fin.sum_univ_succ, map_smul, normalizedTail_self, smul_zero, zero_add,
    expand]
  simp only [map_smul, normalizedTail_col]

theorem normalizedTail_covariant {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1) (a : SL (m+1))
    (x y : E (m+1)) :
    normalizedTail i (markAction a x) (markAction a y) =
      markAction (transverseCocycle i a x) (normalizedTail i x y) := by
  by_cases hx : x = 0
  · have hzero : (0 : ℝ) ^ (m : ℝ)⁻¹ = 0 := Real.zero_rpow (inv_ne_zero (by
      have := i.isLt; exact_mod_cast (by omega : m ≠ 0)))
    subst x
    ext k
    simp [markAction, normalizedTail, transverseCocycle, hzero]
  let g := markSection i x
  have hg : column g 0 = x := (column_zero hn g).trans (markSection_spec i hn hx)
  obtain ⟨v,hv⟩ := (MulAction.surjective g) (WithLp.ofLp y)
  have hy : WithLp.toLp 2 (g • v) = y := congrArg (WithLp.toLp 2) hv
  rw [← hg, ← hy, ← column_mul]
  change normalizedTail i _ (WithLp.toLp 2 (a • g • v)) = _
  rw [← mul_smul, normalizedTail_mulVec, normalizedTail_mulVec, transverseCocycle_frame i hn,
    column_zero hn g]
  exact congrArg (WithLp.toLp 2) (mul_smul ..)

variable {r : ℕ} (i : Fin (r+1)) (j : Fin r)
local notation "n" => (r+2)

def columns (g : SL n) : Frames n := ![column g 0, column g (0 : Fin (r+1)).succ]

def frameAction (a : SL n) (x : Frames n) : Frames n := fun k ↦ markAction a (x k)

theorem columns_mul (a g : SL n) : columns (a*g) = frameAction a (columns g) := by
  funext k; fin_cases k <;> exact column_mul ..

def outerCocycle (a : SL n) (x : Frames n) : SL r :=
  transverseCocycle j (transverseCocycle i a (x 0)) (normalizedTail i (x 0) (x 1))

theorem outerCocycle_mul (a b : SL n) (x : Frames n) :
    outerCocycle i j (a*b) x = outerCocycle i j a (frameAction b x) * outerCocycle i j b x := by
  have hr : 2 ≤ r+1 := by have := j.isLt; omega
  simp only [outerCocycle, frameAction, transverseCocycle_mul i (by omega),
    transverseCocycle_mul j hr, normalizedTail_covariant i (by omega)]

def iteratedFrame (g : SL n) := transverseFrame j (transverseFrame i g)

theorem iteratedFrame_mul (a g : SL n) :
    iteratedFrame i j (a*g) = outerCocycle i j a (columns g) * iteratedFrame i j g := by
  have hr : 2 ≤ r+1 := by have := j.isLt; omega
  unfold iteratedFrame
  rw [transverseCocycle_frame i (by omega) a g, transverseCocycle_frame j hr]
  simp [outerCocycle, columns, ← column_zero]
  rfl

/-- Extend a transverse basis change by a free axial shear. -/
def extend {R : Type*} [CommRing R] {m : ℕ} (w : Fin m → R) (h : SpecialLinearGroup (Fin m) R) :
    SpecialLinearGroup (Fin (m+1)) R :=
  let M : Matrix (Fin (m+1)) (Fin (m+1)) R :=
    Matrix.of (Fin.cons (Fin.cons 1 w) (fun k ↦ Fin.cons 0 (h.val k)))
  ⟨M, by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hz (k : Fin m) : M k.succ 0 = 0 := rfl
    have hm : M.submatrix Fin.succ Fin.succ = h.val := rfl
    simp [hz,hm,show M 0 0 = 1 from rfl,h.property]⟩

theorem column_extend_zero {m : ℕ} (g : SL (m+1)) (w : Fin m → ℝ) (h : SL m) :
    column (g * extend w h) 0 = column g 0 := by
  unfold column
  rw [show (g * extend w h).val = g.val * (extend w h).val from rfl,
    Matrix.col_mul_eq_mulVec_col]
  have he : (extend w h).val.col 0 = Pi.single 0 1 := by
    funext k; refine Fin.cases ?_ (fun k ↦ ?_) k <;> simp [extend, Matrix.col_apply]
  rw [he, Matrix.mulVec_single_one]

theorem transverseFrame_extend {m : ℕ} (k : Fin m) (g : SL (m+1)) (w : Fin m → ℝ) (h : SL m) :
    transverseFrame k (g * extend w h) = transverseFrame k g * h := by
  apply Subtype.ext
  ext a b
  have he := normalizedTail_col k (g * extend w h) b
  rw [column_extend_zero, column_mul] at he
  change normalizedTail k (column g 0) (WithLp.toLp 2 (g • _)) = _ at he
  rw [normalizedTail_mulVec] at he
  exact congrArg (fun v : E m ↦ v a) he.symm

def adaptedFrame (p : Core (r+1)) (g : SL n) : SL n :=
  (primitiveTranslate (by omega) p.1 • g) *
    extend (Pi.single 0 (p.2.1 : ℝ)) (primitiveTranslate (by have := j.isLt; omega) p.2.2).val.unop

theorem adaptedFrame_columns (p : Core (r+1)) (g : SL n) :
    columns (adaptedFrame j p g) = physical (by have := j.isLt; omega) g 0 0 p := by
  let f := primitiveFrame (by omega : 2 ≤ n) p.1
  let t := primitiveFrame (by have := j.isLt; omega : 2 ≤ r+1) p.2.2
  have translate (z : IV n) :
      latticePoint (primitiveTranslate (by omega) p.1 • g) z = latticePoint g (f • z) := by
    change WithLp.toLp 2 ((_ * _) • _) = WithLp.toLp 2 (_ • _)
    rw [mul_smul]
    congr 2
    exact funext fun k ↦ (RingHom.map_mulVec (Int.castRingHom ℝ) f.val z k).symm
  funext k; fin_cases k
  · change column (_ * extend _ _) 0 = _
    rw [column_extend_zero, column_zero (by omega)]
    change latticePoint _ (Pi.single 0 1) = _
    rw [translate, show f • (Pi.single 0 1 : IV n) = p.1.val.val from primitiveFrame_column _ p.1]
    simp [physical, first, scaled_val]
  · change column (_ * extend _ _) (0 : Fin (r+1)).succ = _
    rw [column_mul]
    have ht : t.val.col 0 = p.2.2.val.val := (Matrix.mulVec_single_one t.val 0).symm.trans
      (primitiveFrame_column _ _)
    let v : IV n := Fin.cons p.2.1 p.2.2.val.val
    have he : column (extend (Pi.single 0 (p.2.1 : ℝ)) (primitiveTranslate (by have := j.isLt; omega) p.2.2).val.unop)
        (0 : Fin (r+1)).succ = WithLp.toLp 2 (fun k ↦ (v k : ℝ)) := by
      ext k
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · simp [column, extend,v, Matrix.col_apply]
      · exact congrArg Int.cast (congrFun ht k)
    rw [he]
    change latticePoint _ v = _
    rw [translate]
    simp [physical, second, completion, scaled_val, v, f, SpecialLinearGroup.toLin'_apply]
    rfl

theorem adaptedFrame_outer (p : Core (r+1)) (g : SL n) :
    iteratedFrame i j (adaptedFrame j p g) = outerFrame i j p g := by
  unfold iteratedFrame adaptedFrame outerFrame
  rw [transverseFrame_extend]
  rfl

/-- Every change of outer frame is realized over the same ordered physical columns. -/
theorem outerCocycle_stabilizer (g : SL n) (h : SL r) :
    ∃ a : SL n, frameAction a (columns g) = columns g ∧ outerCocycle i j a (columns g) = h := by
  let s := iteratedFrame i j g
  let b := extend (0 : Fin r → ℝ) (s⁻¹ * h * s)
  let u := extend (0 : Fin (r+1) → ℝ) b
  let a := g * u * g⁻¹
  have hag : a*g = g*u := by simp [a, mul_assoc]
  have hb : column u (0 : Fin (r+1)).succ = basisVector (0 : Fin (r+1)).succ := by
    ext k
    refine Fin.cases ?_ (fun k ↦ ?_) k
    · simp [column,u,extend,Matrix.col_apply]
    · refine Fin.cases ?_ (fun k ↦ ?_) k <;> simp [column,u,b,extend,PiLp.single_apply,
        Matrix.col_apply]
      exact fun e ↦ Fin.succ_ne_zero k (Fin.succ_injective _ (show k.succ.succ = (0 : Fin (r+1)).succ from e))
  refine ⟨a, ?_, ?_⟩
  · rw [← columns_mul, hag]
    funext k; fin_cases k
    · exact column_extend_zero ..
    · change column (g*u) (0 : Fin (r+1)).succ = _
      rw [column_mul,hb]
      exact congrArg (WithLp.toLp 2) (Matrix.mulVec_single_one ..)
  · apply mul_right_cancel (b := s)
    rw [show outerCocycle i j a (columns g) * s = iteratedFrame i j (a*g) from
      (iteratedFrame_mul ..).symm, hag]
    change transverseFrame j (transverseFrame i (g * extend _ _)) = _
    rw [transverseFrame_extend, show b = extend _ _ from rfl, transverseFrame_extend]
    change s * (s⁻¹ * h * s) = _
    group

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.outerCocycle_mul
#print axioms SigabaNeo.Wall1.RankTwo.adaptedFrame_columns
#print axioms SigabaNeo.Wall1.RankTwo.adaptedFrame_outer
#print axioms SigabaNeo.Wall1.RankTwo.outerCocycle_stabilizer
