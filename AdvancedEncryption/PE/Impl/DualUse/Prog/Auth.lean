import PE.Impl.DualUse.Prog.Layout
import PE.Impl.Gates.WindowTest

/-!
# The authorization bit as an algorithm

The flag of the reductions' challengers is `authI hk c C x = decide (Authorized … C x)`, a
classical decision. Here it is restated as explicit Boolean computations:

* `authI_eq_test`: for any configuration, `authI` is the test of `Eval` for window predicates
  (`winEvalMachine c.L`): the length of the input word of `Eval` is at most `c.L`, `C` is a window
  predicate (`inClassW`, the explicit class test) and its last gate is `false` on `x`
  (`evalGates`, `parse`);
* `authI_eq_winAuth`: when `dateBound ≤ c.L` (e.g. `confP`), the length test always passes on
  window predicates, and the last gate of `winWord w` on `x` is `!accepts w x`, so `authI C x` is
  the finite search `winAuth C x`: some pair of dates `p` is a window with `pairWord p = C` whose
  acceptance test (`valid x`, `p.1 ≤ x ≤ p.2`) passes. It only compares `C` with the explicit words
  `pairWord p` and the date `x` with the dates `p.1`, `p.2`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The test of `Eval`** for window predicates, as a Boolean computation. -/
def authTest (L : ℕ) (C : List Bool) (x : Date) : Bool :=
  decide ((encodeTuple [paramsWord dateUniverse params, C, encDate x]).length ≤ L) &&
    inClassW C && !evalGates (encDate x, parse C)

/-- **`authI` is the test of `Eval`.** -/
theorem authI_eq_test (C : List Bool) (x : Date) : authI hk c C x = authTest c.L C x := by
  classical
  have h := win_authorized_iff (impl hk c (SEMachines.finite hk c)) (L := c.L) rfl C x
  unfold authI authTest
  rw [Bool.eq_iff_iff, decide_eq_true_iff, h, Bool.and_eq_true, Bool.and_eq_true,
    decide_eq_true_iff, inClassW_iff, Bool.not_eq_true']
  exact and_assoc.symm

/-- The acceptance of a pair of dates. -/
def acceptsP (p : Date × Date) (x : Date) : Bool := valid x && dateLe p.1 x && dateLe x p.2

/-- **The authorization by finite search**: some window `p` has the predicate `C` and accepts
`x`. -/
def winAuth (C : List Bool) (x : Date) : Bool :=
  (allDates ×ˢ allDates).any fun p => isWindow p && decide (pairWord p = C) && acceptsP p x

theorem winAuth_iff (C : List Bool) (x : Date) :
    winAuth C x = true ↔ ∃ w : Window, winWord w = C ∧ accepts w x = true := by
  unfold winAuth
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, -, hp⟩
    simp only [isWindow, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
    exact ⟨⟨p, h1, h2, h3⟩, h4, h5⟩
  · rintro ⟨w, rfl, hw⟩
    refine ⟨w.1, List.pair_mem_product.mpr ⟨mem_allDates _, mem_allDates _⟩, ?_⟩
    obtain ⟨p, h1, h2, h3⟩ := w
    have he : pairWord p = winWord ⟨p, h1, h2, h3⟩ := (winWord_eq_pairWord ⟨p, h1, h2, h3⟩).symm
    have hw' : acceptsP p x = true := hw
    simp only [isWindow, Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, he⟩, hw'⟩

/-- **`authI` by finite search**, when the bound of `Eval` covers the window predicates. -/
theorem authI_eq_winAuth (hL : dateBound ≤ c.L) (C : List Bool) (x : Date) :
    authI hk c C x = winAuth C x := by
  rw [authI_eq_test, Bool.eq_iff_iff, winAuth_iff]
  unfold authTest
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', inClassW_iff]
  constructor
  · rintro ⟨⟨-, w, rfl⟩, h⟩
    refine ⟨w, rfl, ?_⟩
    rw [winWord, parse_unparse, evalGates_winGates] at h
    simpa using h
  · rintro ⟨w, rfl, hw⟩
    refine ⟨⟨?_, w, rfl⟩, ?_⟩
    · exact (Finset.le_sup (f := fun wx : Window × Date =>
        (encodeTuple [paramsWord dateUniverse params, winWord wx.1,
          dateUniverse.encAttr wx.2]).length) (Finset.mem_univ (w, x))).trans hL
    · rw [winWord, parse_unparse, evalGates_winGates, hw]; rfl

end AdvancedEncryption.DualUse.Prog
