import SigabaNeo.Lib.Lattices.Homomorphic.SLPEval
import SigabaNeo.Lib.Lattices.Homomorphic.SLPCircuit
import SigabaNeo.Lib.Lattices.Homomorphic.NoiseBound

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

namespace SLP

variable {ι : Type*}

/-- **The depth is at most the number of gates.** -/
theorem depth_le_length (p : SLP ι) (w : Wire ι) : depth p w ≤ p.length := by
  have hrun : ∀ (p : SLP ι) (acc : List ℕ), (∀ v ∈ acc, v ≤ acc.length) →
      ∀ v ∈ run (fun _ => 0) 0 (fun a b => max a b + 1) p acc, v ≤ acc.length + p.length := by
    intro p
    induction p with
    | nil => intro acc h v hv; simpa using h v hv
    | cons g p ih =>
      intro acc h v hv
      have hw : ∀ w : Wire ι, wireVal (fun _ => 0) 0 acc w ≤ acc.length := by
        intro w
        cases w with
        | input i => exact Nat.zero_le _
        | one => exact Nat.zero_le _
        | gate n =>
          simp only [wireVal]
          by_cases hn : n < acc.length
          · rw [List.getD_eq_getElem _ _ hn]; exact h _ (List.getElem_mem hn)
          · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hn)]; exact Nat.zero_le _
      have := ih _ (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · simp only [List.length_append, List.length_singleton]; exact (h u hu).trans (by omega)
        · simp only [List.mem_singleton] at hu
          subst hu
          simp only [List.length_append, List.length_singleton]
          exact Nat.succ_le_succ (max_le (hw g.a) (hw g.b))) v hv
      simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at this ⊢
      omega
  unfold depth valueOf
  cases w with
  | input i => exact Nat.zero_le _
  | one => exact Nat.zero_le _
  | gate n =>
    simp only [wireVal, values]
    by_cases hn : n < (run (fun _ => 0) 0 (fun a b => max a b + 1) p []).length
    · rw [List.getD_eq_getElem _ _ hn]
      simpa using hrun p [] (by simp) _ (List.getElem_mem hn)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hn)]; exact Nat.zero_le _

end SLP

/-- The noise bound of the circuit of a wire is that of the program. -/
theorem errBound_circuit {ι : Type*} (WN E : ℕ) (p : SLP ι) (w : Wire ι) :
    errBound WN E (p.circuit w) = slpBound WN E p w :=
  SLP.valueOf_map _ _ _ _ _ _ (errBound WN E) (fun _ => rfl) rfl (fun _ _ => rfl) p w

/-- The noise bound is at most `(WN + 1)^n · E` for `n` gates. -/
theorem slpBound_le_length {ι : Type*} (WN E : ℕ) (p : SLP ι) (w : Wire ι) :
    slpBound WN E p w ≤ (WN + 1) ^ p.length * E :=
  (slpBound_le_depth WN E p w).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (SLP.depth_le_length p w)))

end SigabaNeo.Lattices
