import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.List.GetD

/-!
# Straight-line programs of NAND gates

A straight-line program (`SLP ι`) is a list of NAND gates; each gate reads two wires, an input
(indexed by `ι`), the constant `1`, or an earlier gate (`Wire`). Unlike a tree (`Circuit`), gates
are shared, so a program's size counts each gate once.

A program runs over any type of values (`SLP.values`): given the values of the inputs and of `1`
and a two-argument `step`, it computes the value of every gate in order; a wire to a gate not yet
computed reads the value of `1`. One run serves every interpretation:

* `SLP.evalBool` and `SLP.eval` (in a ring, `NAND(a, b) = 1 − a·b`) give the Boolean semantics;
* homomorphic evaluation runs on matrices (`SLP.Homomorphic`).

`SLP.values_invariant`: a property of the inputs and of `1` that `step` preserves holds at every
wire. `SLP.values_map`: running on images is the image of the run, so a joint run on tuples projects
to the runs of its components.
-/

namespace SigabaNeo.Lattices

/-- A wire: an input, the constant `1`, or the output of the gate with the given index. -/
inductive Wire (ι : Type*) where
  /-- An input. -/
  | input (i : ι)
  /-- The constant `1`. -/
  | one
  /-- The output of a gate. -/
  | gate (n : ℕ)

/-- A NAND gate reading two wires. -/
structure Gate (ι : Type*) where
  /-- The left wire. -/
  a : Wire ι
  /-- The right wire. -/
  b : Wire ι

/-- A straight-line program: NAND gates in order. -/
abbrev SLP (ι : Type*) := List (Gate ι)

namespace SLP

variable {ι α β : Type*}

/-- The value of a wire, from the input values, the value of `1`, and the gates computed so far. -/
def wireVal (inp : ι → α) (one : α) (vals : List α) : Wire ι → α
  | .input i => inp i
  | .one => one
  | .gate n => vals.getD n one

/-- Run the gates after those already computed (`acc`). -/
def run (inp : ι → α) (one : α) (step : α → α → α) : SLP ι → List α → List α
  | [], acc => acc
  | g :: p, acc =>
    run inp one step p (acc ++ [step (wireVal inp one acc g.a) (wireVal inp one acc g.b)])

/-- The values of all gates. -/
def values (inp : ι → α) (one : α) (step : α → α → α) (p : SLP ι) : List α :=
  run inp one step p []

/-- The value of a wire after the whole program. -/
def valueOf (inp : ι → α) (one : α) (step : α → α → α) (p : SLP ι) (w : Wire ι) : α :=
  wireVal inp one (values inp one step p) w

/-- **Invariants.** A property of the inputs and of `1` preserved by `step` holds at every wire. -/
theorem valueOf_invariant (inp : ι → α) (one : α) (step : α → α → α) (P : α → Prop)
    (hinp : ∀ i, P (inp i)) (hone : P one) (hstep : ∀ a b, P a → P b → P (step a b))
    (p : SLP ι) (w : Wire ι) : P (valueOf inp one step p w) := by
  have hrun : ∀ (p : SLP ι) (acc : List α), (∀ v ∈ acc, P v) → ∀ v ∈ run inp one step p acc, P v := by
    have hw : ∀ (acc : List α), (∀ v ∈ acc, P v) → ∀ w, P (wireVal inp one acc w) := by
      intro acc hacc w
      cases w with
      | input i => exact hinp i
      | one => exact hone
      | gate n =>
        simp only [wireVal]
        by_cases h : n < acc.length
        · rw [List.getD_eq_getElem _ _ h]; exact hacc _ (List.getElem_mem h)
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]; exact hone
    intro p
    induction p with
    | nil => intro acc hacc; exact hacc
    | cons g p ih =>
      intro acc hacc
      apply ih
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hacc v hv
      · rw [List.mem_singleton] at hv
        rw [hv]
        exact hstep _ _ (hw acc hacc g.a) (hw acc hacc g.b)
  unfold valueOf
  cases w with
  | input i => exact hinp i
  | one => exact hone
  | gate n =>
    simp only [wireVal]
    by_cases h : n < (values inp one step p).length
    · rw [List.getD_eq_getElem _ _ h]
      exact hrun p [] (by simp) _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]; exact hone

/-- **Images.** Running on images under a map that commutes with `step` is the image of the run. -/
theorem valueOf_map (inp : ι → α) (one : α) (step : α → α → α) (inp' : ι → β) (one' : β)
    (step' : β → β → β) (f : α → β) (hinp : ∀ i, f (inp i) = inp' i) (hone : f one = one')
    (hstep : ∀ a b, f (step a b) = step' (f a) (f b)) (p : SLP ι) (w : Wire ι) :
    f (valueOf inp one step p w) = valueOf inp' one' step' p w := by
  have hw : ∀ (acc : List α) (w : Wire ι),
      f (wireVal inp one acc w) = wireVal inp' one' (acc.map f) w := by
    intro acc w
    cases w with
    | input i => exact hinp i
    | one => exact hone
    | gate n =>
      simp only [wireVal]
      by_cases h : n < acc.length
      · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h),
          List.getElem_map]
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h), hone]
  have hrun : ∀ (p : SLP ι) (acc : List α),
      (run inp one step p acc).map f = run inp' one' step' p (acc.map f) := by
    intro p
    induction p with
    | nil => intro acc; rfl
    | cons g p ih =>
      intro acc
      simp only [run]
      rw [ih, List.map_append, List.map_singleton, hstep, hw, hw]
  unfold valueOf values
  rw [hw, hrun]
  rfl

/-- Boolean evaluation. -/
def evalBool (x : ι → Bool) (p : SLP ι) (w : Wire ι) : Bool :=
  valueOf x true (fun a b => !(a && b)) p w

/-- Evaluation in a commutative ring, with `NAND(a, b) = 1 − a·b`. -/
def eval {R : Type*} [CommRing R] (x : ι → R) (p : SLP ι) (w : Wire ι) : R :=
  valueOf x 1 (fun a b => 1 - a * b) p w

/-- On bits, the ring evaluation is the Boolean one. -/
theorem eval_bits {R : Type*} [CommRing R] (x : ι → Bool) (p : SLP ι) (w : Wire ι) :
    eval (fun i => if x i then (1 : R) else 0) p w = if evalBool x p w then 1 else 0 := by
  symm
  refine valueOf_map x true _ _ 1 _ (fun b => if b then (1 : R) else 0) (fun i => rfl) (by simp)
    ?_ p w
  intro a b
  cases a <;> cases b <;> simp

end SLP

end SigabaNeo.Lattices
