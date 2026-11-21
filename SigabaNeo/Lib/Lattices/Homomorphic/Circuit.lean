import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Dedup

/-!
# Boolean circuits

Circuits of NAND gates over input bits indexed by `ι` and the constant `1`. `Circuit.eval` evaluates a circuit
in any commutative ring with `NAND(a, b) = 1 − a·b`, which on `0/1` values is the Boolean NAND
(`Circuit.evalBool`, `Circuit.eval_bits`). Every Boolean function of finitely many bits is a circuit
(`Circuit.ofFun`, `Circuit.evalBool_ofFun`, by Shannon expansion; its size is exponential).
Homomorphic evaluation (`SigabaNeo.Lib.Lattices.Homomorphic.Eval`) evaluates them on
BGG+ encodings and Ring-GSW ciphertexts.
-/

namespace SigabaNeo.Lattices

/-- A circuit of NAND gates over inputs indexed by `ι`. -/
inductive Circuit (ι : Type*) where
  /-- An input bit. -/
  | input (i : ι)
  /-- The constant `1`. -/
  | one
  /-- `NAND(a, b)`. -/
  | nand (a b : Circuit ι)

namespace Circuit

variable {ι : Type*}

/-- Evaluation in a commutative ring, with `NAND(a, b) = 1 − a·b`. -/
def eval {R : Type*} [CommRing R] (x : ι → R) : Circuit ι → R
  | input i => x i
  | one => 1
  | nand a b => 1 - a.eval x * b.eval x

/-- Boolean evaluation. -/
def evalBool (x : ι → Bool) : Circuit ι → Bool
  | input i => x i
  | one => true
  | nand a b => !(a.evalBool x && b.evalBool x)

/-- On bits, the ring evaluation is the Boolean one. -/
theorem eval_bits {R : Type*} [CommRing R] (x : ι → Bool) (c : Circuit ι) :
    c.eval (fun i => if x i then (1 : R) else 0) = if c.evalBool x then 1 else 0 := by
  induction c with
  | input i => rfl
  | one => simp [eval, evalBool]
  | nand a b iha ihb =>
    simp only [eval, evalBool, iha, ihb]
    rcases Bool.eq_false_or_eq_true (a.evalBool x) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (b.evalBool x) with hb | hb <;> simp [ha, hb]

/-! ### Every Boolean function is a circuit -/

/-- The constant `0`. -/
def zero : Circuit ι := nand one one

/-- `¬a`. -/
def not (a : Circuit ι) : Circuit ι := nand a a

/-- `if s then a else b`. -/
def mux (s a b : Circuit ι) : Circuit ι := nand (nand s a) (nand (not s) b)

@[simp] theorem evalBool_zero (x : ι → Bool) : (zero : Circuit ι).evalBool x = false := rfl

@[simp] theorem evalBool_mux (x : ι → Bool) (s a b : Circuit ι) :
    (mux s a b).evalBool x = if s.evalBool x then a.evalBool x else b.evalBool x := by
  simp only [mux, not, evalBool]
  cases s.evalBool x <;> cases a.evalBool x <;> cases b.evalBool x <;> rfl

variable [DecidableEq ι]

/-- The Shannon expansion of `F` along the variables `l`. -/
def shannon : List ι → ((ι → Bool) → Bool) → Circuit ι
  | [], F => if F (fun _ => false) then one else zero
  | i :: l, F => mux (input i) (shannon l fun x => F (Function.update x i true))
      (shannon l fun x => F (Function.update x i false))

/-- The Shannon expansion computes `F` when `F` reads only the variables in `l`. -/
theorem evalBool_shannon (l : List ι) (F : (ι → Bool) → Bool)
    (hF : ∀ x y, (∀ i ∈ l, x i = y i) → F x = F y) (x : ι → Bool) :
    (shannon l F).evalBool x = F x := by
  induction l generalizing F with
  | nil =>
    have h := hF (fun _ => false) x (by simp)
    simp only [shannon]
    split_ifs with hc <;> simp_all [evalBool]
  | cons i l ih =>
    simp only [shannon, evalBool_mux, evalBool]
    have hb : ∀ b, (shannon l fun x => F (Function.update x i b)).evalBool x =
        F (Function.update x i b) := fun b =>
      ih _ (fun y z hyz => hF _ _ fun j hj => by
        by_cases hji : j = i
        · subst hji; simp
        · simp only [Function.update_of_ne hji]
          exact hyz j ((List.mem_cons.mp hj).resolve_left hji))
    rw [hb, hb]
    have hx : Function.update x i (x i) = x := Function.update_eq_self i x
    rcases Bool.eq_false_or_eq_true (x i) with hxi | hxi <;>
      simp only [hxi, Bool.false_eq_true, ite_false, ite_true] <;> conv_rhs => rw [← hx, hxi]

variable [Fintype ι]

/-- A circuit computing `F` (its truth table, by Shannon expansion). -/
noncomputable def ofFun (F : (ι → Bool) → Bool) : Circuit ι := shannon Finset.univ.toList F

/-- **Every Boolean function is a circuit.** -/
theorem evalBool_ofFun (F : (ι → Bool) → Bool) (x : ι → Bool) : (ofFun F).evalBool x = F x :=
  evalBool_shannon _ F (fun _y _z h => congrArg F (funext fun i => h i (Finset.mem_toList.mpr
    (Finset.mem_univ i)))) x

end Circuit

end SigabaNeo.Lattices
