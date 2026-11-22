import PE.Impl.Gates.DateWindow

/-!
# Testing whether a word is a window predicate

`inClassW C` decides whether `C` is the predicate `winWord w` of some window, by running through
the explicit list of pairs of dates (`inClassW_iff`). It is the class test of `KeyGen` and
`Eval` as an explicit algorithm: at most `2^20` comparisons of `C` with a window predicate.
-/

namespace AdvancedEncryption.PE.Gates.DateWindow

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.SLP AdvancedEncryption.PE.DateWindow

/-- The predicate of a pair of dates (a window when the pair is one). -/
def pairWord (p : Date × Date) : List Bool :=
  unparse (predGates (compile [] (winExp p.1 p.2)).1 (compile [] (winExp p.1 p.2)).2)

theorem winWord_eq_pairWord (w : Window) : winWord w = pairWord w.1 := by
  unfold winWord winGates pairWord; rfl

/-- All dates, explicitly. -/
def allDates : List Date := List.finRange 32 ×ˢ List.finRange 32

theorem mem_allDates (x : Date) : x ∈ allDates :=
  List.pair_mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩

/-- Whether a pair of dates is a window. -/
def isWindow (p : Date × Date) : Bool := valid p.1 && valid p.2 && dateLe p.1 p.2

/-- **The class test.** -/
def inClassW (C : List Bool) : Bool :=
  (allDates ×ˢ allDates).any fun p => isWindow p && decide (pairWord p = C)

theorem inClassW_iff (C : List Bool) : inClassW C = true ↔ ∃ w : Window, winWord w = C := by
  unfold inClassW
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, -, hp⟩
    simp only [isWindow, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    exact ⟨⟨p, h1, h2, h3⟩, h4⟩
  · rintro ⟨w, rfl⟩
    refine ⟨w.1, List.pair_mem_product.mpr ⟨mem_allDates _, mem_allDates _⟩, ?_⟩
    obtain ⟨p, h1, h2, h3⟩ := w
    have hw : isWindow p = true := by
      unfold isWindow; rw [Bool.and_eq_true, Bool.and_eq_true]; exact ⟨⟨h1, h2⟩, h3⟩
    rw [Bool.and_eq_true]
    refine ⟨hw, decide_eq_true ?_⟩
    exact (winWord_eq_pairWord ⟨p, h1, h2, h3⟩).symm

end AdvancedEncryption.PE.Gates.DateWindow
