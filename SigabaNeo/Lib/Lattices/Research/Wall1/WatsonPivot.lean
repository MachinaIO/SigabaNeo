import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonGramVertices

/-! Local optimality certificates for the ten off-diagonal Gram coordinates. -/

namespace SigabaNeo.Wall1.Watson.Pivot

open Matrix Finset
abbrev E := Fin 10 → ℝ
abbrev V := Fin 10 → ℤ
abbrev Z := Fin 5 → ℤ

def left : Fin 10 → Fin 5 := ![0,0,0,0,1,1,1,2,2,3]
def right : Fin 10 → Fin 5 := ![1,2,3,4,2,3,4,3,4,4]
def normal (z : Z) : V := fun i ↦ z (left i) * z (right i)
def lift (v : V) : E := fun i ↦ v i

/-- An unrolled dot product keeps certificate reduction independent of finset enumeration. -/
def dot (v w : V) : ℤ :=
  v 0*w 0 + v 1*w 1 + v 2*w 2 + v 3*w 3 + v 4*w 4 +
  v 5*w 5 + v 6*w 6 + v 7*w 7 + v 8*w 8 + v 9*w 9

theorem dot_cast (v w : V) : (dot v w : ℝ) = lift v ⬝ᵥ lift w := by
  simp [dot, dotProduct, lift, Fin.sum_univ_succ]
  ring

theorem lift_sub (v w : V) : lift (v - w) = lift v - lift w := by
  ext i
  simp [lift]

/-- The ten dual evaluations give the coordinates in a primal basis of feasible directions. -/
theorem frame_bound (rows dirs : Fin 10 → E) (x : E) (f : E →ₗ[ℝ] ℝ)
    (diag : ∀ i, 0 < rows i ⬝ᵥ dirs i)
    (off : ∀ i j, i ≠ j → rows i ⬝ᵥ dirs j = 0)
    (slack : ∀ i, 0 ≤ rows i ⬝ᵥ x) (step : ∀ i, f (dirs i) ≤ 0) : f x ≤ 0 := by
  classical
  let g (i : Fin 10) : E →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ (rows i)
  have coord (c : Fin 10 → ℝ) (i : Fin 10) :
      g i (∑ j, c j • dirs j) = c i * (rows i ⬝ᵥ dirs i) := by
    simp only [map_sum, map_smul, smul_eq_mul]
    apply sum_eq_single i
    · intro j _ h
      change c j * (rows i ⬝ᵥ dirs j) = 0
      rw [off _ _ h.symm, mul_zero]
    · simp
  have indep : LinearIndependent ℝ dirs := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have h := coord c i
    rw [hc, map_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right (diag i).ne'
  let B := basisOfLinearIndependentOfCardEqFinrank indep (by simp)
  have be : ⇑B = dirs := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have expansion := B.sum_repr x
  simp only [be] at expansion
  have nonneg (i : Fin 10) : 0 ≤ B.repr x i := by
    have h := coord (fun j ↦ B.repr x j) i
    rw [expansion] at h
    exact nonneg_of_mul_nonneg_left (h ▸ slack i) (diag i)
  rw [← expansion, map_sum]
  exact sum_nonpos fun i _ ↦ by simpa using mul_nonpos_of_nonneg_of_nonpos (nonneg i) (step i)

/-- A perturbed vertex lists one tight test and one destination per basis coordinate. -/
structure Frame where
  offset : Array ℤ
  tests : Array Nat
  dest : Array Nat
  deriving Inhabited

structure Image where
  edges : Array ℤ
  rep : Fin 24
  perm : Array (Fin 5)
  signs : Array Bool
  deriving Inhabited

structure Block where
  tests : Array (Array ℤ)
  images : Array Image
  frames : Array Frame
  deriving Inhabited

def unpack {n : ℕ} (a : Array ℤ) (i : Fin n) : ℤ := a[i.val]?.getD 0
def frame (b : Block) (j : Nat) := b.frames[j]?.getD default
def offset (b : Block) (j : Nat) : V := unpack (frame b j).offset
def dest (b : Block) (j : Nat) (i : Fin 10) := (frame b j).dest[i.val]?.getD 0
def row (b : Block) (j : Nat) (i : Fin 10) : Z :=
  unpack (b.tests[((frame b j).tests[i.val]?.getD 0)]?.getD #[])
def imageAt (b : Block) (u : Nat) := b.images[u]?.getD default
def dir (p : V) (b : Block) (j : Nat) (i : Fin 10) : V :=
  let t := dest b j i
  if t < b.frames.size then offset b t - offset b j
  else unpack (imageAt b (t - b.frames.size)).edges - p

def checkFrame (p : V) (b : Block) (j : Nat) : Prop :=
  ∀ i l : Fin 10, if i = l then 0 < dot (normal (row b j i)) (dir p b j l)
    else dot (normal (row b j i)) (dir p b j l) = 0

instance (p : V) (b : Block) (j : Nat) : Decidable (checkFrame p b j) :=
  by unfold checkFrame; infer_instance

/-- Choose the best perturbation for the objective. Its ten neighboring directions
all have nonpositive objective, so complementary slackness gives the bound. -/
theorem block_bound (p : V) (b : Block) (f : E →ₗ[ℝ] ℝ) (x : E)
    (nonempty : 0 < b.frames.size)
    (cert : ∀ j : Fin b.frames.size, checkFrame p b j)
    (slacks : ∀ (j : Fin b.frames.size) i,
      0 ≤ lift (normal (row b j i)) ⬝ᵥ (x - lift p))
    (outer : ∀ (j : Fin b.frames.size) i, b.frames.size ≤ dest b j i →
      f (lift (unpack (imageAt b (dest b j i - b.frames.size)).edges)) ≤ f (lift p)) :
    f x ≤ f (lift p) := by
  classical
  letI : Nonempty (Fin b.frames.size) := ⟨⟨0,nonempty⟩⟩
  obtain ⟨j, _, best⟩ := exists_max_image univ
    (fun j : Fin b.frames.size ↦ f (lift (offset b j))) univ_nonempty
  have h := frame_bound (fun i ↦ lift (normal (row b j i))) (fun i ↦ lift (dir p b j i))
    (x - lift p) f (fun i ↦ by
      rw [← dot_cast]
      apply Int.cast_pos.mpr
      simpa only [↓reduceIte] using cert j i i)
    (fun i l ne ↦ by
      rw [← dot_cast]
      rw [show dot (normal (row b j i)) (dir p b j l) = 0 by simpa only [ne, ↓reduceIte] using cert j i l]
      simp)
    (slacks j) (fun i ↦ by
      unfold dir
      dsimp only
      split_ifs with h
      · rw [lift_sub, map_sub, sub_nonpos]
        exact best ⟨_,h⟩ (mem_univ _)
      · rw [lift_sub, map_sub, sub_nonpos]
        exact outer j i (by omega))
  rwa [map_sub, sub_nonpos] at h

end SigabaNeo.Wall1.Watson.Pivot

#print axioms SigabaNeo.Wall1.Watson.Pivot.frame_bound

#print axioms SigabaNeo.Wall1.Watson.Pivot.block_bound
