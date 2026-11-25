import SigabaNeoStd.Machines.FromPolyTime
import SigabaNeoStd.Machines.LengthGuard
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Ite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.TidyZeroSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic

/-!
# Guarded algorithms

A deterministic algorithm with a polynomial-time certificate, guarded by the length of its input:
on inputs at most `L` long it computes `f`, on longer inputs it outputs a fixed `d`
(`guarded`). The guard (`lenGuard`) reads at most `L + 1` cells, so one constant clock bounds
every run (`computable_guarded`), and the machine computes the guarded function on every input
(`Machine.exists_guarded`).
-/

namespace SigabaNeo

open Turing Turing.MultiTapeTM

/-- `f` on inputs at most `L` long, `d` on longer ones. -/
def guarded {α β : Type} (encIn : α ↪ List Bool) (L : ℕ) (f : α → β) (d : β) (a : α) : β :=
  if (encIn a).length ≤ L then f a else d

/-- **Guarded algorithms run in constant time.** -/
theorem computable_guarded {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (hf : ComputableTidilyInPolyTime f encIn encOut) (L : ℕ) (d : β) :
    ∃ (T : ℕ) (s : α → ℕ),
      ComputableInTimeAndSpace (guarded encIn L f d) encIn encOut (fun _ => T) s := by
  obtain ⟨t, s, ht, -, hcert⟩ := hf
  obtain ⟨c, e, hb⟩ := ht.exists_le
  have hc := computable_lenGuard encIn L
  have hF := hcert.restrict (fun a => decide ((encIn a).length ≤ L) = true)
  obtain ⟨c₀, hconst⟩ := computableInTimeAndSpace_of_const
    (encIn := (Function.Embedding.subtype
      (fun a => decide ((encIn a).length ≤ L) = false)).trans encIn) (encOut := encOut) d
  have hG := hconst.computableTidilyInTimeAndSpace
  obtain ⟨k, hite⟩ := ComputableTidilyInTimeAndSpace.ite (c := fun a => decide ((encIn a).length ≤ L))
    (f := f) (g := fun _ => d) (tg := fun _ => 2 * c₀ + 2) (sg := fun _ => 0) hc hF hG
  refine ⟨2 * L + 2 + (c * (L + 1) ^ e + (2 * c₀ + 2)) + k,
    fun x => (0 + if decide ((encIn x).length ≤ L) = true then s x else 0) + k, ?_⟩
  have heq : (fun a => if decide ((encIn a).length ≤ L) = true then f a else d) =
      guarded encIn L f d := by
    funext a; simp [guarded]
  rw [← heq]
  refine (hite.mono (fun a => ?_) (fun _ => le_rfl)).computableInTimeAndSpace
  by_cases ha : (encIn a).length ≤ L
  · rw [ite_eq_left_iff.mpr (fun h => absurd (by simpa using ha) h)]
    have h1 := hb a
    have h2 : c * ((encIn a).length + 1) ^ e ≤ c * (L + 1) ^ e :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  · rw [ite_eq_right_iff.mpr (fun h => absurd h (by simpa using ha))]
    omega

/-- **The machine of a guarded algorithm**: deterministic, computing the guarded function on
every input. -/
theorem Machine.exists_guarded {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (hf : ComputableTidilyInPolyTime f encIn encOut) (L : ℕ) (d : β) :
    ∃ M : Machine, M.Deterministic ∧
      ∀ a, M.run (encIn a) = PMF.pure (encOut (guarded encIn L f d a)) := by
  obtain ⟨T, s, h⟩ := computable_guarded hf L d
  obtain ⟨k, S, hS, tm, htm⟩ := Machine.exists_of_computable h
  exact ⟨Machine.ofTM tm T, Machine.deterministic_ofTM tm T, fun a => htm T a le_rfl⟩

end SigabaNeo
