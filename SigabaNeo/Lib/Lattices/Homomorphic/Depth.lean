import SigabaNeo.Lib.Lattices.Homomorphic.SLPEval

/-!
# The depth of a straight-line program and its noise

`SLP.depth p w`: `0` at the inputs and at `1`, one more than the deeper input at a gate. The noise
bound of homomorphic evaluation (`slpBound`, `WN · E_a + E_b` at a gate) is at most
`(WN + 1)^depth · E` (`slpBound_le_depth`): the modulus needed grows exponentially in the depth
only.
-/

namespace SigabaNeo.Lattices

namespace SLP

variable {ι : Type*}

/-- The depth of a wire. -/
def depth (p : SLP ι) (w : Wire ι) : ℕ := valueOf (fun _ => 0) 0 (fun a b => max a b + 1) p w

end SLP

/-- **The noise bound is exponential in the depth only.** -/
theorem slpBound_le_depth {ι : Type*} (WN E : ℕ) (p : SLP ι) (w : Wire ι) :
    slpBound WN E p w ≤ (WN + 1) ^ SLP.depth p w * E := by
  let step : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ := fun a b => (WN * a.1 + b.1, max a.2 b.2 + 1)
  have h1 : (SLP.valueOf (fun _ => (E, 0)) (0, 0) step p w).1 = slpBound WN E p w :=
    SLP.valueOf_map _ _ _ _ _ _ Prod.fst (fun _ => rfl) rfl (fun _ _ => rfl) p w
  have h2 : (SLP.valueOf (fun _ => (E, 0)) (0, 0) step p w).2 = SLP.depth p w :=
    SLP.valueOf_map _ _ _ _ _ _ Prod.snd (fun _ => rfl) rfl (fun _ _ => rfl) p w
  have hinv := SLP.valueOf_invariant (fun _ : ι => (E, 0)) (0, 0) step
    (fun u => u.1 ≤ (WN + 1) ^ u.2 * E) (fun _ => by simp) (by simp)
    (fun a b ha hb => by
      show WN * a.1 + b.1 ≤ (WN + 1) ^ (max a.2 b.2 + 1) * E
      have ha' : a.1 ≤ (WN + 1) ^ max a.2 b.2 * E :=
        ha.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (le_max_left _ _)))
      have hb' : b.1 ≤ (WN + 1) ^ max a.2 b.2 * E :=
        hb.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (le_max_right _ _)))
      calc WN * a.1 + b.1 ≤ WN * ((WN + 1) ^ max a.2 b.2 * E) + (WN + 1) ^ max a.2 b.2 * E :=
            Nat.add_le_add (Nat.mul_le_mul_left _ ha') hb'
        _ = (WN + 1) ^ (max a.2 b.2 + 1) * E := by ring) p w
  rw [← h1, ← h2]
  exact hinv

end SigabaNeo.Lattices
