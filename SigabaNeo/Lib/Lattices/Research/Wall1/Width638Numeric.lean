module

public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Arithmetic
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Arithmetic
import Mathlib.Tactic

public section
namespace SigabaNeo.Wall1.Width638
open Finset SigabaNeo.SampleDeletion

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem integer_certificate :
    643162094166 * denominator * 3329^4 + 10^12 * denominator * 4 * 7^4 <
      10^12 * gain * 3329^4 := by decide +kernel

attribute [local irreducible] gain denominator

/-- The exact finite shell sum after paying the four validation charges. -/
theorem shell_certificate :
    (643162094166 / 10^12 : ℚ) <
      ((∑ t ∈ range 955, shell 3 511 t * (D^4 - (D - credit t)^4) : ℕ) : ℚ) /
        (denominator : ℚ) - 4*(7/3329 : ℚ)^4 := by
  rw [← gain_eq]
  have hd : 0 < (denominator : ℚ) := by unfold denominator D H; positivity
  have h := (Nat.cast_lt (α := ℚ)).mpr integer_certificate
  push_cast at h
  rw [lt_sub_iff_add_lt, lt_div_iff₀ hd]
  linarith only [h]

end SigabaNeo.Wall1.Width638
#print axioms SigabaNeo.Wall1.Width638.integer_certificate
#print axioms SigabaNeo.Wall1.Width638.shell_certificate
