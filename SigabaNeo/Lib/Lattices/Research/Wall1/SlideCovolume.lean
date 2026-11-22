module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AttackLattice
public import SigabaNeo.Lib.Lattices.Research.Wall1.GramProduct
public import SigabaNeo.Lib.Lattices.Research.Wall1.RetainedCovolume
import Mathlib.Tactic

/-! # Physical covolume and exact slide steps (Part 143)

Columns are integral basis vectors in orthonormal physical coordinates. At volume one
the orthogonal projector has integer entries. Its diagonal entries equal the sums of
squares of their respective rows, forcing it to be a coordinate projection. -/

public section

namespace SigabaNeo.Wall1.Slide

open Matrix
open scoped Matrix

variable {N k : ℕ}

/-- Euclidean covolume in the span of an independent frame. -/
noncomputable def volume {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ι → E) : ℝ :=
  Real.sqrt (Matrix.gram ℝ v).det

/-- The Gram convention agrees with Mathlib's Haar covolume of the integer
span in basis coordinates. For a lower-rank lattice take E to be its real span. -/
theorem volume_eq_covolume {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b : Module.Basis (Fin k) ℝ E) :
    volume b = ZLattice.covolume (Submodule.span ℤ (Set.range b)) := by
  let e := (stdOrthonormalBasis ℝ E).reindex (finCongr (by simpa using Module.finrank_eq_card_basis b))
  have hG : Matrix.gram ℝ b = (e.toBasis.toMatrix b)ᵀ * e.toBasis.toMatrix b := by
    rw [Matrix.gram_eq_conjTranspose_mul e, Matrix.conjTranspose_eq_transpose_of_trivial]
    congr 1
  rw [volume, hG, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs,
    ZLattice.covolume_eq_measure_fundamentalDomain _ MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b MeasureTheory.volume),
    ZSpan.measureReal_fundamentalDomain b MeasureTheory.volume e.toBasis]
  simp [MeasureTheory.measureReal_def, MeasureTheory.measure_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped e.toBasis MeasureTheory.volume),
    e.volume_parallelepiped, Module.Basis.det_apply]

/-- In particular, removing a primitive head divides physical covolume by its length. -/
theorem volume_projected_tail {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Module.Basis (Fin (k+1)) ℝ E) :
    volume (fun i : Fin k ↦ (ℝ ∙ b 0)ᗮ.starProjection (b i.succ)) = volume b / ‖b 0‖ :=
  projected_tail_covolume b

/-- Squared physical covolume, computed over the integers. -/
@[expose] def gramDet (B : Matrix (Fin N) (Fin k) ℤ) : ℤ := (Bᵀ * B).det

noncomputable abbrev frame (B : Matrix (Fin N) (Fin k) ℤ) (j : Fin k) :=
  AttackLattice.intEmb N (B.col j)

theorem gramDet_cast (B : Matrix (Fin N) (Fin k) ℤ) :
    (gramDet B : ℝ) = (Matrix.gram ℝ (frame B)).det := by
  rw [gramDet, Int.cast_det]
  congr 1
  ext i j
  simp [Matrix.gram_apply, PiLp.inner_apply, frame, Matrix.mul_apply, mul_comm]

/-- Changing the column basis scales squared covolume by the square of its determinant. -/
theorem gramDet_mul (B : Matrix (Fin N) (Fin k) ℤ) (T : Matrix (Fin k) (Fin k) ℤ) :
    gramDet (B * T) = T.det^2 * gramDet B := by
  have h : (B*T)ᵀ * (B*T) = Tᵀ * ((Bᵀ * B) * T) := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  simp only [gramDet, h, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem gramDet_nonneg (B : Matrix (Fin N) (Fin k) ℤ) : 0 ≤ gramDet B := by
  have h : (0 : ℝ) ≤ gramDet B := by
    rw [gramDet_cast, det_gram_eq_prod_norm_sq]
    positivity
  exact_mod_cast h

theorem one_le_volume (B : Matrix (Fin N) (Fin k) ℤ) (h : LinearIndependent ℝ (frame B)) :
    1 ≤ volume (frame B) := by
  have hn := (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)).2 h
  rw [← gramDet_cast] at hn
  have hn' : gramDet B ≠ 0 := by exact_mod_cast hn
  have h1 : (1 : ℤ) ≤ gramDet B := by have := gramDet_nonneg B; omega
  rw [volume, ← gramDet_cast]
  exact (Real.one_le_sqrt).2 (by exact_mod_cast h1)

/-- Integer linear independence, as supplied by an integer lattice basis, suffices. -/
theorem integer_sublattice_volume (B : Matrix (Fin N) (Fin k) ℤ)
    (h : LinearIndependent ℤ B.col) : 1 ≤ volume (frame B) := by
  have hp := (Matrix.PosDef.conjTranspose_mul_self B (Matrix.mulVec_injective_iff.mpr h)).det_pos
  have hp' : 0 < gramDet B := by simpa [gramDet, Matrix.conjTranspose_eq_transpose_of_trivial] using hp
  rw [volume, ← gramDet_cast, Real.one_le_sqrt]
  exact_mod_cast (show (1 : ℤ) ≤ gramDet B by omega)

theorem frame_independent (B : Matrix (Fin N) (Fin k) ℤ) (h : LinearIndependent ℤ B.col) :
    LinearIndependent ℝ (frame B) := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero (𝕜 := ℝ)
  intro hz
  have hv := integer_sublattice_volume B h
  norm_num [volume, hz] at hv

/-- The lower bound directly for Haar covolume of the integer span, measured
inside the real span with its induced Euclidean metric. -/
theorem one_le_intrinsic_covolume (B : Matrix (Fin N) (Fin k) ℤ)
    (h : LinearIndependent ℤ B.col) :
    let b := Module.Basis.span (frame_independent B h)
    1 ≤ ZLattice.covolume (Submodule.span ℤ (Set.range b)) := by
  let b := Module.Basis.span (frame_independent B h)
  change 1 ≤ ZLattice.covolume (Submodule.span ℤ (Set.range b))
  rw [← volume_eq_covolume]
  have hg : Matrix.gram ℝ b = Matrix.gram ℝ (frame B) := by
    ext i j
    change inner ℝ ((b i).val) ((b j).val) = _
    simp [b, Module.Basis.span_apply]
  simpa only [volume, hg] using (show 1 ≤ volume (frame B) from integer_sublattice_volume B h)

theorem volume_eq_one_iff (B : Matrix (Fin N) (Fin k) ℤ) :
    volume (frame B) = 1 ↔ gramDet B = 1 := by
  rw [volume, ← gramDet_cast]
  constructor
  · intro h
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ gramDet B by exact_mod_cast gramDet_nonneg B)
    rw [h, one_pow] at hs
    exact_mod_cast hs.symm
  · intro h
    simp [h]

private theorem integral_projection {P : Matrix (Fin N) (Fin N) ℤ}
    (hs : Pᵀ = P) (hp : P * P = P) :
    (∀ i, P i i = 0 ∨ P i i = 1) ∧ P = diagonal (fun i ↦ P i i) := by
  have row (i : Fin N) : ∑ j, (P i j) ^ 2 = P i i := by
    have sym (j : Fin N) : P j i = P i j := congrFun (congrFun hs i) j
    simpa [Matrix.mul_apply, sym, pow_two] using congrFun (congrFun hp i) i
  have diag (i : Fin N) : P i i = 0 ∨ P i i = 1 := by
    have h := Finset.single_le_sum (f := fun j ↦ (P i j)^2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
    rw [row] at h
    by_contra! hh
    rcases lt_or_ge (P i i) 0 with hl | hl
    · nlinarith [sq_nonneg (P i i)]
    · have : 2 ≤ P i i := by omega
      nlinarith [mul_nonneg (show 0 ≤ P i i - 2 by omega) hl]
  refine ⟨diag, Matrix.ext fun i j ↦ ?_⟩
  by_cases hij : i = j
  · subst j; simp
  rw [diagonal_apply_ne _ hij]
  have h := Finset.sum_erase_add (s := Finset.univ) (fun a ↦ (P i a)^2) (Finset.mem_univ i)
  change (∑ a ∈ Finset.univ.erase i, (P i a)^2) + (P i i)^2 = ∑ j, (P i j)^2 at h
  rw [row] at h
  have hz : ∑ a ∈ Finset.univ.erase i, (P i a)^2 = 0 := by
    have hi : (P i i)^2 = P i i := by rcases diag i with he | he <;> rw [he] <;> decide
    rw [hi] at h
    exact add_right_cancel (h.trans (zero_add _).symm)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ sq_nonneg (P i a))).1 hz j
    (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩)
  exact by simpa using hj

/-- Equality characterizes an integral change of basis onto an entire coordinate lattice.
The left inverse gives integral coordinates, and the composite in ambient coordinates
is the diagonal projection onto precisely the selected axes. -/
theorem gramDet_one_iff_coordinate (B : Matrix (Fin N) (Fin k) ℤ) :
    gramDet B = 1 ↔ ∃ (C : Matrix (Fin k) (Fin N) ℤ) (d : Fin N → ℤ),
      C * B = 1 ∧ B * C = diagonal d ∧ ∀ i, d i = 0 ∨ d i = 1 := by
  constructor
  · intro h
    let G := Bᵀ * B
    let C := G.adjugate * Bᵀ
    have hi : C * B = 1 := by
      change (G.adjugate * Bᵀ) * B = 1
      rw [Matrix.mul_assoc]
      change G.adjugate * G = 1
      simp [Matrix.adjugate_mul, show G.det = 1 from h]
    have hs : (B * C)ᵀ = B * C := by
      simp [C, G, Matrix.transpose_mul, Matrix.adjugate_transpose, Matrix.mul_assoc]
    have hp : (B * C) * (B * C) = B * C := by
      calc _ = B * ((C * B) * C) := by simp only [Matrix.mul_assoc]
           _ = _ := by rw [hi, Matrix.one_mul]
    obtain ⟨hd, he⟩ := integral_projection hs hp
    exact ⟨C, _, hi, he, hd⟩
  · rintro ⟨C, d, hi, hc, _⟩
    have hs : (B * C)ᵀ = B * C := by simp [hc]
    have hR : (Bᵀ * B) * (C * Cᵀ) = 1 := by
      calc _ = Bᵀ * ((B * C) * Cᵀ) := by simp only [Matrix.mul_assoc]
           _ = Bᵀ * ((C * (B * C))ᵀ) := by rw [Matrix.transpose_mul, hs]
           _ = (C * B)ᵀ := by rw [show C * (B * C) = C by rw [← Matrix.mul_assoc, hi, Matrix.one_mul], Matrix.transpose_mul]
           _ = 1 := by simp [hi]
    have hv := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_one] at hv
    have hu : IsUnit (gramDet B) := isUnit_iff_dvd_one.mpr ⟨_, hv.symm⟩
    rcases Int.isUnit_iff.mp hu with h | h
    · exact h
    · have := gramDet_nonneg B; omega

/-- The old extension remains eligible at the accepted prefix. Minimization over
all eligible extensions therefore gives weak descent even when the oracle ties. -/
theorem accepted_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℕ} (p p' : Fin r → E) (Q Q' : Fin (r+1) → E)
    (eligible : (Fin r → E) → (Fin (r+1) → E) → Prop)
    (accept : (Matrix.gram ℝ p').det < (Matrix.gram ℝ p).det)
    (oldEligible : eligible p' Q)
    (minimum : ∀ T, eligible p' T → (Matrix.gram ℝ Q').det ≤ (Matrix.gram ℝ T).det) :
    volume p' < volume p ∧ volume Q' ≤ volume Q := by
  have hp : 0 ≤ (Matrix.gram ℝ p').det := by rw [det_gram_eq_prod_norm_sq]; positivity
  exact ⟨(Real.sqrt_lt_sqrt_iff hp).2 accept, Real.sqrt_le_sqrt (minimum Q oldEligible)⟩

end SigabaNeo.Wall1.Slide

#print axioms SigabaNeo.Wall1.Slide.volume_eq_covolume
#print axioms SigabaNeo.Wall1.Slide.volume_projected_tail
#print axioms SigabaNeo.Wall1.Slide.gramDet_cast
#print axioms SigabaNeo.Wall1.Slide.one_le_intrinsic_covolume
#print axioms SigabaNeo.Wall1.Slide.integer_sublattice_volume
#print axioms SigabaNeo.Wall1.Slide.one_le_volume
#print axioms SigabaNeo.Wall1.Slide.volume_eq_one_iff
#print axioms SigabaNeo.Wall1.Slide.gramDet_one_iff_coordinate
#print axioms SigabaNeo.Wall1.Slide.accepted_step
