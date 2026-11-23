module

public import SigabaNeo.Lib.Lattices.Research.Wall1.QaryMembership
public import SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionBall
import all SigabaNeo.Lib.Lattices.Research.Wall1.QaryMembership
import all SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionBall
import Mathlib.Tactic

/-! Part 236 in residual coordinates. An affine point (u,v) satisfies u + Av = y.
Its squared norm is the squared distance from (y,0) to (y-u,v) in the graph lattice,
for an arbitrary integer lift of y. This presentation needs no chosen lift of y. -/

public section
namespace SigabaNeo.Wall1.Width638
open QaryMembership SigabaNeo.SampleDeletion Finset Matrix

abbrev Grid (r n : ℕ) := (Fin r ⊕ Fin n) → ℤ
variable {r n q : ℕ} [Fact q.Prime]
def output (A : Design r n q) (w : Grid r n) : Fin r → ZMod q :=
  (fun i ↦ (w (.inl i) : ZMod q)) + A *ᵥ (fun j ↦ (w (.inr j) : ZMod q))

/-- Ties with the plant count as bad for every tie-breaking convention. -/
def Bad (p : Grid r n) (A : Design r n q) : Prop :=
  ∃ w, w ≠ p ∧ normSq w ≤ normSq p ∧ output A w = output A p

/-- Oracle for the squared Euclidean distance on the graph. Its function depends on
the public matrix and observed residue only. -/
structure CVPOracle (r n q : ℕ) [Fact q.Prime] where
  closest : Design r n q → (Fin r → ZMod q) → Grid r n
  feasible : ∀ A y, output A (closest A y) = y
  minimal : ∀ A y w, output A w = y → normSq (closest A y) ≤ normSq w

theorem closest_of_good (O : CVPOracle r n q) (A : Design r n q) (p : Grid r n)
    (h : ¬ Bad p A) : O.closest A (output A p) = p := by
  by_contra hn
  exact h ⟨_, hn, O.minimal _ _ _ rfl, O.feasible ..⟩

def difference (w p : Grid r n) : Point r n :=
  (fun i ↦ w (.inl i) - p (.inl i), fun j ↦ w (.inr j) - p (.inr j))

theorem output_eq_iff (w p : Grid r n) (A : Design r n q) :
    output A w = output A p ↔ kernel A (difference w p) := by
  have red {d : ℕ} (f g : Fin d → ℤ) :
      reduce q (fun i ↦ f i - g i) = reduce q f - reduce q g := by
    ext i
    simp [reduce]
  simp only [kernel, difference, red, mulVec_sub, neg_sub]
  have rearrange (a b c d : Fin r → ZMod q) : a+b=c+d ↔ b-d=c-a := by
    constructor <;> intro h <;> linear_combination (norm := abel) h
  exact rearrange _ _ _ _

private theorem coord_bound (w : Grid r n) (i) : (w i).natAbs^2 ≤ normSq w :=
  single_le_sum (f := fun j ↦ (w j).natAbs^2) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)

private theorem no_wrap {w p : Grid r n} (h : normSq w ≤ normSq p)
    (hq : 4 * normSq p < q^2) (i) (he : ((w i - p i : ℤ) : ZMod q) = 0) : w i = p i := by
  have h1 := (coord_bound w i).trans h
  have h2 := coord_bound p i
  have a : 2*(w i).natAbs < q := by nlinarith only [h1,hq]
  have b : 2*(p i).natAbs < q := by nlinarith only [h2,hq]
  have hab : |w i - p i| < (q : ℤ) := by
    have hsum : |w i - p i| ≤ |w i| + |p i| := by
      simpa [sub_eq_add_neg] using abs_add_le (w i) (-p i)
    rw [← Int.natCast_natAbs (w i), ← Int.natCast_natAbs (p i)] at hsum
    omega
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp he) hab)

theorem competitor_count (w p : Grid r n) (hw : w ≠ p) (hle : normSq w ≤ normSq p)
    (hq : 4 * normSq p < q^2) :
    (designs (fun A : Design r n q ↦ output A w = output A p)).card * q^r ≤
      Fintype.card (Design r n q) := by
  simp_rw [output_eq_iff]
  by_cases h : reduce q (difference w p).2 = 0
  · have impossible (A : Design r n q) : ¬ kernel A (difference w p) := by
      intro ha
      have hx : reduce q (difference w p).1 = 0 := by simpa [kernel, h, eq_comm] using ha
      apply hw
      funext i
      cases i with
      | inl i => exact no_wrap hle hq _ (congrFun hx i)
      | inr j => exact no_wrap hle hq _ (congrFun h j)
    classical simp [designs, impossible]
  · simpa only [card_univ] using (kernel_fixed (difference w p) h).le

/-- For fixed planting, the uniform-design failure count is bounded by the number of
nonplanted integer points in the closed ball times the one-point incidence probability. -/
theorem translated_ball (p : Grid r n) (hq : 4 * normSq p < q^2) :
    (designs (q := q) (Bad p)).card * q^r ≤
      (ballCount (r+n) (normSq p) - 1) * Fintype.card (Design r n q) := by
  classical
  let P := Points (Fin r ⊕ Fin n) (normSq p)
  let : Fintype P := Fintype.ofFinite P
  let p₀ : P := ⟨p, le_rfl⟩
  let S := univ.erase p₀
  let event (w : P) := designs (fun A : Design r n q ↦ output A w.val = output A p)
  have cover : designs (q := q) (Bad p) ⊆ S.biUnion event := by
    intro A h
    obtain ⟨w, hn, hl, he⟩ := (mem_filter.mp h).2
    exact mem_biUnion.mpr ⟨⟨w,hl⟩, mem_erase.mpr ⟨fun e ↦ hn (congrArg Subtype.val e),
      mem_univ _⟩, (mem_designs _ _).mpr he⟩
  have count : S.card = ballCount (r+n) (normSq p) - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, ← Nat.card_eq_fintype_card]
    change Nat.card (Points (Fin r ⊕ Fin n) _) - 1 = _
    rw [card_points]
    simp
  calc
    _ ≤ (∑ w ∈ S, (event w).card) * q^r :=
      Nat.mul_le_mul_right _ ((card_le_card cover).trans card_biUnion_le)
    _ = ∑ w ∈ S, (event w).card * q^r := sum_mul ..
    _ ≤ ∑ _w ∈ S, Fintype.card (Design r n q) := sum_le_sum fun w hw ↦
      competitor_count w.val p (fun e ↦ (mem_erase.mp hw).1 (Subtype.ext e)) w.property hq
    _ = _ := by simp [count]

end SigabaNeo.Wall1.Width638

#print axioms SigabaNeo.Wall1.Width638.closest_of_good
#print axioms SigabaNeo.Wall1.Width638.translated_ball
