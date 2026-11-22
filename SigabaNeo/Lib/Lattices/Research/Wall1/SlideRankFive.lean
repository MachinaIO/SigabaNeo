module

public import SigabaNeo.Lib.Lattices.Research.Wall1.SlideCovolume
import all SigabaNeo.Lib.Lattices.Research.Wall1.SlideCovolume
import Mathlib.Tactic

/-! # Exact certificates for the two terminal flags of Part 143

Every prefix contains the marked vector e₀. Its coefficient in another generator
drops out of the Gram determinant. The other four coefficients run over all of ℤ⁴.
The suffix compares rank-three extensions, and the dual compares rank-two prefixes
inside that extension containing e₀. -/

public section

namespace SigabaNeo.Wall1.Slide.RankFive

open Matrix
open scoped Matrix

abbrev Vec := Fin 5 → ℤ

@[expose] def e : Vec := ![1,0,0,0,0]
@[expose] def v (x y z t : ℤ) : Vec := ![0,x,y,z,t]
@[expose] def axis (x y : ℤ) := v x y 0 0

/-- Coefficients of the four unmarked starting basis vectors, in their specified order. -/
def latticeVec (i j k l : ℤ) : Fin 5 → ℤ := v (10*i + 10*j + 5*k) (10*i) (9*k) (20*l)

def prefixSq (p : Fin 5 → ℤ) := gramDet (![e,p] : Matrix (Fin 2) (Fin 5) ℤ)ᵀ
def extensionSq (p w : Fin 5 → ℤ) := gramDet (![e,p,w] : Matrix (Fin 3) (Fin 5) ℤ)ᵀ

private theorem prefix_formula (x y z t : ℤ) :
    prefixSq (v x y z t) = x^2 + y^2 + z^2 + t^2 := by
  let M : Matrix (Fin 2) (Fin 5) ℤ := ![e, v x y z t]
  have g : M * Mᵀ = !![1, 0; 0, x^2+y^2+z^2+t^2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
      dsimp [M, e, v, Matrix.transpose] <;> first | (solve | simp) | (simp; ring)
  change (Mᵀᵀ * Mᵀ).det = _
  rw [Matrix.transpose_transpose, g, Matrix.det_fin_two]
  simp

private theorem extension_formula (a b x y z t : ℤ) :
    extensionSq (v a b 0 0) (v x y z t) =
      (a*y-b*x)^2 + (a^2+b^2)*(z^2+t^2) := by
  let M : Matrix (Fin 3) (Fin 5) ℤ := ![e, v a b 0 0, v x y z t]
  have g : M * Mᵀ = !![1,0,0; 0,a^2+b^2,a*x+b*y; 0,a*x+b*y,x^2+y^2+z^2+t^2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
      dsimp [M, e, v, Matrix.transpose] <;> simp <;> ring
  change (Mᵀᵀ * Mᵀ).det = _
  rw [Matrix.transpose_transpose, g, Matrix.det_fin_three]
  simp
  ring

private theorem unit_sq (a : ℤ) (h : a ≠ 0) : 1 ≤ a^2 := by
  have := sq_pos_of_ne_zero h
  omega

private theorem tilted_min (a b : ℤ) (hn : a ≠ 0 ∨ b ≠ 0) :
    100 ≤ (10*a+5*b)^2 + (9*b)^2 := by
  by_cases h : b = 0
  · subst b
    have ha := unit_sq a (hn.resolve_right (by simp))
    nlinarith
  by_cases hb : b = 1 ∨ b = -1
  · have ho : 2*a+b ≠ 0 := by omega
    have hs := unit_sq _ ho
    have hb1 : b^2 = 1 := by rcases hb with hb | hb <;> simp [hb]
    nlinarith
  have h4 : 4 ≤ b^2 := by
    rcases le_or_gt b 0 with h0 | h0
    · have h2 : b ≤ -2 := by omega
      nlinarith [mul_nonneg_of_nonpos_of_nonpos (by omega : b+2 ≤ 0) (by omega : b-2 ≤ 0)]
    · have h2 : 2 ≤ b := by omega
      nlinarith [mul_nonneg (by omega : 0 ≤ b-2) (by omega : 0 ≤ b+2)]
  nlinarith [sq_nonneg (10*a+5*b)]

/-- Shortest suffix line, expressed by minimum positive Gram determinant. -/
def SuffixMinimum (p w : Fin 5 → ℤ) : Prop :=
  (∃ i j k l, w = latticeVec i j k l) ∧ 0 < extensionSq p w ∧ ∀ i j k l, 0 < extensionSq p (latticeVec i j k l) →
    extensionSq p w ≤ extensionSq p (latticeVec i j k l)

/-- Minimum prefix containing the marked vector in the plane generated modulo it by p,w. -/
def PrefixMinimum (p w winner : Fin 5 → ℤ) : Prop :=
  (∃ a b : ℤ, winner = a • p + b • w) ∧ 0 < prefixSq winner ∧
    ∀ a b : ℤ, 0 < prefixSq (a • p + b • w) → prefixSq winner ≤ prefixSq (a • p + b • w)

private theorem comb (a b x y z t X Y Z T : ℤ) :
    a • v x y z t + b • v X Y Z T = v (a*x+b*X) (a*y+b*Y) (a*z+b*Z) (a*t+b*T) := by
  ext i; fin_cases i <;> simp [v]

private theorem square_floor (x y : ℤ) (h : 0 < (10*x)^2+(10*y)^2) :
    100 ≤ (10*x)^2+(10*y)^2 := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by rintro rfl; simp [hx] at h
    nlinarith [unit_sq y hy, sq_nonneg x]
  · nlinarith [unit_sq x hx, sq_nonneg y]

/-- The stated five generators have unique integer coefficients. -/
theorem start_injective : Function.Injective (fun c : Fin 5 → ℤ ↦
    c 0 • e + latticeVec (c 1) (c 2) (c 3) (c 4)) := by
  intro c d h
  have hh := congrFun h
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have h4 := hh 4
  simp [e, latticeVec, v] at h0 h1 h2 h3 h4
  funext i; fin_cases i <;> dsimp <;> omega

/-- The marked unit attains the ambient integer minimum, hence the prefix minimum
in every displayed prefix containing it. -/
theorem marked_shortest : (∑ i, (e i)^2) = 1 ∧
    ∀ z : Fin 5 → ℤ, z ≠ 0 → 1 ≤ ∑ i, (z i)^2 := by
  refine ⟨by norm_num [e, Fin.sum_univ_succ], fun z hn ↦ ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by by_contra! hh; exact hn (funext hh)
  exact (unit_sq _ hi).trans (Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j)) (Finset.mem_univ i))

/-- Both exact branches, including suffix and marked-hyperplane minima at each stop. -/
theorem two_terminal_flags :
    let p := axis 10 10
    let x := axis 10 0
    let y := axis 0 10
    let w := v 5 0 9 0
    SuffixMinimum p x ∧ PrefixMinimum p x x ∧ PrefixMinimum p x y ∧
    SuffixMinimum x w ∧ PrefixMinimum x w x ∧
    SuffixMinimum y x ∧ PrefixMinimum y x y ∧
    prefixSq p = 200 ∧ prefixSq x = 100 ∧ prefixSq y = 100 ∧
    extensionSq x w = 90^2 ∧ extensionSq y x = 100^2 := by
  dsimp only
  have s0 : SuffixMinimum (axis 10 10) (axis 10 0) := by
    refine ⟨⟨0,1,0,0,by norm_num [axis, latticeVec]⟩, by norm_num [axis, extension_formula], ?_⟩
    intro i j k l h
    simp only [latticeVec, extension_formula, axis] at h ⊢
    by_cases hl : l = 0
    · by_cases hk : k = 0
      · have hj : j ≠ 0 := by rintro rfl; simp [hk, hl] at h
        subst k; subst l; nlinarith [unit_sq j hj]
      · nlinarith [unit_sq k hk, sq_nonneg (10*j+5*k), sq_nonneg l]
    · nlinarith [unit_sq l hl, sq_nonneg (10*j+5*k), sq_nonneg k]
  have square (a b : ℤ) : prefixSq (a • axis 10 10 + b • axis 10 0) =
      (10*(a+b))^2+(10*a)^2 := by rw [axis, axis, comb, prefix_formula]; ring
  have m0 (z : Vec) (hz : prefixSq z = 100)
      (hz' : ∃ a b : ℤ, z = a • axis 10 10 + b • axis 10 0) :
      PrefixMinimum (axis 10 10) (axis 10 0) z := by
    refine ⟨hz', by omega, fun a b h ↦ ?_⟩
    rw [hz, square]; rw [square] at h
    exact square_floor _ _ h
  have sx : SuffixMinimum (axis 10 0) (v 5 0 9 0) := by
    refine ⟨⟨0,0,1,0,by norm_num [latticeVec]⟩, by norm_num [axis, extension_formula], ?_⟩
    intro i j k l h
    simp only [axis, latticeVec, extension_formula] at h ⊢
    by_cases hl : l = 0
    · by_cases hk : k = 0
      · have hi : i ≠ 0 := by rintro rfl; norm_num [hl,hk] at h
        nlinarith [unit_sq i hi, sq_nonneg k, sq_nonneg l]
      · nlinarith [unit_sq k hk, sq_nonneg i, sq_nonneg l]
    · nlinarith [unit_sq l hl, sq_nonneg i, sq_nonneg k]
  have mx : PrefixMinimum (axis 10 0) (v 5 0 9 0) (axis 10 0) := by
    refine ⟨⟨1,0,by simp⟩, by norm_num [axis, prefix_formula], fun a b h ↦ ?_⟩
    simp only [axis, comb, prefix_formula] at h ⊢
    have hn : a ≠ 0 ∨ b ≠ 0 := by by_contra! h0; norm_num [h0.1,h0.2] at h
    nlinarith [tilted_min a b hn]
  have sy : SuffixMinimum (axis 0 10) (axis 10 0) := by
    refine ⟨⟨0,1,0,0,by norm_num [axis, latticeVec]⟩, by change 0 < extensionSq (axis 0 10) (v 10 0 0 0); norm_num [axis, extension_formula], ?_⟩
    intro i j k l h
    change extensionSq (axis 0 10) (v 10 0 0 0) ≤ _
    simp only [axis, latticeVec, extension_formula] at h ⊢
    by_cases hl : l = 0
    · have hn : i+j ≠ 0 ∨ k ≠ 0 := by
        by_contra! h0
        have he : 10*i + 10*j = 0 := by omega
        norm_num [h0.2,hl,he] at h
      nlinarith [tilted_min (i+j) k hn, sq_nonneg l]
    · nlinarith [unit_sq l hl, sq_nonneg (10*i+10*j+5*k), sq_nonneg k]
  have my : PrefixMinimum (axis 0 10) (axis 10 0) (axis 0 10) := by
    refine ⟨⟨1,0,by simp⟩, by norm_num [axis, prefix_formula], fun a b h ↦ ?_⟩
    simp only [axis, comb, prefix_formula] at h ⊢
    nlinarith [square_floor b a (by nlinarith)]
  refine ⟨s0, m0 (axis 10 0) (by norm_num [axis, prefix_formula]) ⟨0,1,by simp⟩,
    m0 (axis 0 10) (by norm_num [axis, prefix_formula]) ⟨1,-1,?_⟩, sx, mx, sy, my, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [axis, comb]; norm_num
  all_goals norm_num [axis, prefix_formula, extension_formula]

/-- Physical terminal covolumes, with the square root taken in ℝ. -/
theorem terminal_volumes :
    volume (frame (![e, axis 10 0, v 5 0 9 0] : Matrix (Fin 3) (Fin 5) ℤ)ᵀ) = 90 ∧
    volume (frame (![e, axis 0 10, axis 10 0] : Matrix (Fin 3) (Fin 5) ℤ)ᵀ) = 100 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hx,hy⟩ := two_terminal_flags
  change gramDet _ = _ at hx hy
  constructor
  · rw [volume, ← gramDet_cast, hx]; norm_num
  · rw [volume, ← gramDet_cast, hy]; norm_num

end SigabaNeo.Wall1.Slide.RankFive

#print axioms SigabaNeo.Wall1.Slide.RankFive.start_injective
#print axioms SigabaNeo.Wall1.Slide.RankFive.marked_shortest
#print axioms SigabaNeo.Wall1.Slide.RankFive.two_terminal_flags
#print axioms SigabaNeo.Wall1.Slide.RankFive.terminal_volumes
