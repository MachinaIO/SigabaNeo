module

public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Graph
public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Averaging
public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Numeric
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Groups
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Graph
import all SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockAttack
import Mathlib.Tactic

/-! Part 236: one iid LWE sample, four predetermined rank-638 exact CVP queries,
coordinatewise lifting, and the first candidate accepted by four reserved rows. -/

public section
noncomputable section
namespace SigabaNeo.Wall1.Width638
open MultiBlock QaryMembership SigabaNeo.SampleDeletion Matrix
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

abbrev Secret := Fin 511 → ℤ
abbrev Sample := Design 512 511 3329
abbrev Observation := Fin 512 → ZMod 3329
abbrev Oracle := GraphOracle 127 511 3329

/-- For a proposed secret, lift each output residue to the integer nearest the target.
The same formula fills every discarded coordinate. -/
def lift (A : Sample) (y : Observation) (d : Secret) (i : Fin 512) : ℤ :=
  ((y i).val : ℤ) - (y i - A i ⬝ᵥ fun j ↦ (d j : ZMod 3329)).valMinAbs

theorem lift_residue (A : Sample) (y : Observation) (d : Secret) (i : Fin 512) :
    (lift A y d i : ZMod 3329) = A i ⬝ᵥ fun j ↦ (d j : ZMod 3329) := by
  simp [lift]

/-- Every competing lift at least as close to the target equals the centered lift.
The modulus is odd, so this coordinatewise lifting step has no ties. -/
theorem lift_unique (A : Sample) (y : Observation) (d : Secret) (i : Fin 512) (u : ℤ)
    (hu : (u : ZMod 3329) = A i ⬝ᵥ fun j ↦ (d j : ZMod 3329))
    (h : (((y i).val : ℤ) - u).natAbs ≤ (((y i).val : ℤ) - lift A y d i).natAbs) :
    u = lift A y d i := by
  let a := y i - A i ⬝ᵥ fun j ↦ (d j : ZMod 3329)
  have small : (((y i).val : ℤ) - u).natAbs ≤ 1664 :=
    (show _ ≤ a.valMinAbs.natAbs by simpa [lift, a] using h).trans a.natAbs_valMinAbs_le
  have e := Attack.valMinAbs_small (η := 1664) (q := 3329) (by decide) _ small
  rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, hu] at e
  unfold lift
  omega

theorem lift_planted (A : Sample) (s : Fin 511 → Digit 3) (e : Fin 512 → Digit 3) (i : Fin 512) :
    lift A (Attack.lweSample A s e) (centered ∘ s) i =
      (((Attack.lweSample A s e i).val : ℤ) - centered (e i)) := by
  exact congrArg (fun a : ℤ ↦ ((Attack.lweSample A s e i).val : ℤ) - a)
    (lift_discarded A s e (by decide) i)

/-- Public-data formulation. Tie breaking is local to the CVP oracle. The proof only
credits a block when the planted point is the unique closest point. -/
def firstValidated (O : Oracle) (b : Fin 4 → Fin 127 → Fin 512) (c : Fin 4 → Fin 512)
    (A : Sample) (y : Observation) : Option Secret :=
  (List.finRange 4).findSome? fun i ↦
    let g := O.closest (fun j ↦ A (b i j)) (fun j ↦ ((y (b i j)).val : ℤ))
    (Attack.decode 3 3329 (fun j ↦ g (.inr j))).filter (fun d ↦ decide
      (∀ j, (((y (c j)).val : ℤ) - lift A y d (c j)).natAbs ≤ 3))

private theorem accepts (z : ZMod 3329) : z.valMinAbs.natAbs ≤ 3 ↔ accept z := by
  constructor
  · intro h
    exact ⟨z.valMinAbs, by omega, by omega, z.coe_valMinAbs⟩
  · rintro ⟨t, ht, ht', rfl⟩
    have he : t.natAbs ≤ 3 := by omega
    rw [Attack.valMinAbs_small (q := 3329) (η := 3) (by decide) t he]
    exact he

/-- Extend the supplied rank-638 oracle to the arity-polymorphic list interface.
All four actual calls use its 127-row branch. -/
private def family (O : Oracle) (k : ℕ) : CVPOracle k 511 3329 :=
  if h : k = 127 then h ▸ affineOracle O
  else affineOracle (Classical.choice graphOracle_nonempty)

private theorem first_eq (O : Oracle) (b : Fin 4 → Fin 127 → Fin 512) (c : Fin 4 → Fin 512)
    (A : Sample) (y : Observation) :
    firstValidated O b c A y = Attack.attack 3 (asBlockOracle (family O)) (fun _ ↦ 127) b c A y := by
  unfold firstValidated Attack.attack
  apply congrArg (fun f : Fin 4 → Option Secret ↦ (List.finRange 4).findSome? f)
  funext i
  simp only [Attack.candidate, asBlockOracle, family, dite_eq_left rfl, affineOracle, switch,
    Sum.elim_inr, Sum.elim_inl, true_or, ↓reduceIte, one_mul]
  have tests : (fun d : Secret ↦ decide (∀ j, (((y (c j)).val : ℤ) - lift A y d (c j)).natAbs ≤ 3)) =
      fun d ↦ decide (Attack.passes A y c d) := by
    funext d
    have sameTest {P Q : Prop} (a : Decidable P) (b : Decidable Q) (h : P ↔ Q) :
        @decide P a = @decide Q b := by
      obtain rfl := propext h
      rw [Subsingleton.elim a b]
    apply sameTest
    simp [lift, Attack.passes, accepts]
  rw [tests]

/-- The width is the integer rank of each queried graph submodule. -/
theorem query_rank (A : Design 127 511 3329) : Module.finrank ℤ (graph A) = 638 :=
  graph_rank A

/-- On the iid CBD(3) / uniform-design law, every rank-638 exact oracle and every
fixed disjoint partition as specified recovers the common secret with this probability. -/
theorem recovery (O : Oracle) (b : Fin 4 → Fin 127 → Fin 512) (c : Fin 4 → Fin 512)
    (disjointRows : Function.Injective (Sum.elim (fun p : (Σ _ : Fin 4, Fin 127) ↦ b p.1 p.2) c)) :
    (643162094166 / 10^12 : ℚ) < Attack.lweProb 512 511 3329 3 (fun s e A ↦
      firstValidated O b c A (Attack.lweSample A s e) = some (centered ∘ s)) := by
  simp_rw [first_eq]
  have hn := shell_certificate
  rw [← gain_eq] at hn
  exact hn.trans_le ((sub_le_sub_right average_bound _).trans
    (success_lower b c disjointRows (family O) (by decide)))

def blockRow (i : Fin 4) (j : Fin 127) : Fin 512 := ⟨127*i.val+j.val, by omega⟩
def reservedRow (j : Fin 4) : Fin 512 := ⟨508+j.val, by omega⟩

theorem disjoint_std :
    Function.Injective (Sum.elim (fun p : (Σ _ : Fin 4, Fin 127) ↦ blockRow p.1 p.2) reservedRow) := by
  rintro (⟨i,a⟩ | j) (⟨i',a'⟩ | j') h <;>
    simp only [Sum.elim_inl, Sum.elim_inr, blockRow, reservedRow, Fin.ext_iff] at h
  · have hi : i = i' := by ext; omega
    subst i'
    have ha : a = a' := by ext; omega
    subst a'
    rfl
  · omega
  · omega
  · congr 1; ext; omega

theorem recovery_std (O : Oracle) :
    (643162094166 / 10^12 : ℚ) < Attack.lweProb 512 511 3329 3 (fun s e A ↦
      firstValidated O blockRow reservedRow A (Attack.lweSample A s e) = some (centered ∘ s)) :=
  recovery O blockRow reservedRow disjoint_std

end SigabaNeo.Wall1.Width638

#print axioms SigabaNeo.Wall1.Width638.lift_unique
#print axioms SigabaNeo.Wall1.Width638.lift_planted
#print axioms SigabaNeo.Wall1.Width638.query_rank
#print axioms SigabaNeo.Wall1.Width638.recovery
#print axioms SigabaNeo.Wall1.Width638.recovery_std
