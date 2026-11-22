import PE.Impl.Gates.WindowTest
import SigabaNeo.Lib.Lattices.ProgAlgo.GateListLayout
import SigabaNeo.Lib.Machines.Prog.Lookup

/-!
# The window class test, the parse and the authorization test as tape programs

A query `C` may be as long as the adversary's time, so every program first **cuts** `C` at `n + 1`
bits (`SigabaNeo.Tape.Prog.cutLook`: the length test `|C| ≤ n` and the key `padW n C`, which
determines `C` when `|C| ≤ n`), in `20 |C|` steps plus a constant; everything after the cut runs in
a time independent of `|C|`. What follows is a **table lookup** on the key over the finitely many
window predicates of at most `n` bits (`winsN n`, the windows of `windows` whose predicate
`pairWord p` is that short), a membership test as `inClassW` (which compares `C` with all
`pairWord p`).

* `frontV n W C`: what the simulated key oracle `KGsim` needs of a query: `[]` when `|C| > n`,
  `[false]` when `C` is short but no window predicate, and `true :: gsW W (parse C)` (the gate list
  of `C` in the layout of the `f̂` generator, `SigabaNeo.Tape.Prog.gsW`) for a window predicate
  (`frontV_long`, `frontV_short_not`, `frontV_win`). **`law_frontP`**: `frontP n W` computes it.
* `authN nA C x = decide (|C| ≤ nA) && inClassW C && !evalGates (encDate x, parse C)`: the
  authorization test with its length bound (the window class, then the evaluation of the gate list
  on the date bits). **`law_authP`**: `authP nA` computes `[authN nA C x]` from `C` and `encDate x`;
  the table holds the pairs (short window predicate, date it accepts) (`lookupV_authTbl`, through
  `evalGates_pairWord`: a window predicate evaluates to the negated acceptance).

Both programs are components on eight tapes (`io2`): inputs on tapes `0`, `1`, output on tape `0`,
the other tapes blank; time `20 T + const` for queries of at most `T` bits (`timeBoundT_frontP`,
`timeBoundT_authP`). The constants are those of the tables (`lookCount`): one comparison per short
window predicate (and per accepted date for `authP`).
-/

namespace AdvancedEncryption.PE.Gates.DateWindow

open SigabaNeo SigabaNeo.Lattices AdvancedEncryption.PE.DateWindow SigabaNeo.Tape SigabaNeo.Tape.Prog

/-! ### The windows -/

/-- The windows, explicitly. -/
def windows : List (Date × Date) := (allDates ×ˢ allDates).filter isWindow

theorem mem_windows {p : Date × Date} : p ∈ windows ↔ isWindow p = true := by
  rw [windows, List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨List.pair_mem_product.mpr ⟨mem_allDates _, mem_allDates _⟩, h⟩⟩

theorem inClassW_iff_windows (C : List Bool) : inClassW C = true ↔ ∃ p ∈ windows, pairWord p = C := by
  unfold inClassW
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, hp, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨p, mem_windows.mpr h.1, h.2⟩
  · rintro ⟨p, hp, h⟩
    refine ⟨p, List.pair_mem_product.mpr ⟨mem_allDates _, mem_allDates _⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨mem_windows.mp hp, h⟩

/-- The windows whose predicate has at most `n` bits. -/
def winsN (n : ℕ) : List (Date × Date) := windows.filter fun p => decide ((pairWord p).length ≤ n)

theorem mem_winsN {n : ℕ} {p : Date × Date} :
    p ∈ winsN n ↔ p ∈ windows ∧ (pairWord p).length ≤ n := by
  rw [winsN, List.mem_filter, decide_eq_true_iff]

/-- The window of a pair of dates that is one. -/
def winOf (p : Date × Date) (h : isWindow p = true) : Window := by
  refine ⟨p, ?_⟩
  simp only [isWindow, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Acceptance of a pair of dates. -/
def accP (p : Date × Date) (x : Date) : Bool := valid x && dateLe p.1 x && dateLe x p.2

/-- **A window predicate evaluates to its negated acceptance.** -/
theorem evalGates_pairWord {p : Date × Date} (h : isWindow p = true) (x : Date) :
    evalGates (encDate x, parse (pairWord p)) = !accP p x := by
  have := evalGates_winGates (winOf p h) x
  have e : pairWord p = winWord (winOf p h) := (winWord_eq_pairWord (winOf p h)).symm
  have ha : accepts (winOf p h) x = accP p x := rfl
  rw [e, winWord, parse_unparse, this, ha]

theorem pairWord_ne_nil (p : Date × Date) : pairWord p ≠ [] := by
  intro h
  have hp : parse (pairWord p) = [] := by rw [h]; rfl
  rw [pairWord, parse_unparse, predGates, toGates] at hp
  simp at hp

theorem not_inClassW_nil : inClassW [] = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨p, -, hp⟩ := (inClassW_iff_windows []).mp h
  exact pairWord_ne_nil p hp

/-! ### The front end of the key query -/

/-- **What the key query needs of `C`.** -/
def frontV (n W : ℕ) (C : List Bool) : List Bool :=
  if C.length ≤ n then (if inClassW C then true :: gsW W (parse C) else [false]) else []

theorem frontV_long {n W : ℕ} {C : List Bool} (h : ¬ C.length ≤ n) : frontV n W C = [] := by
  simp [frontV, h]

theorem frontV_short_not {n W : ℕ} {C : List Bool} (h : C.length ≤ n)
    (hw : ¬ ∃ w : Window, winWord w = C) : frontV n W C = [false] := by
  have : inClassW C = false := by
    rw [Bool.eq_false_iff]; exact fun h' => hw ((inClassW_iff C).mp h')
  simp [frontV, h, this]

theorem frontV_win {n W : ℕ} {C : List Bool} (h : C.length ≤ n) (hw : ∃ w : Window, winWord w = C) :
    frontV n W C = true :: gsW W (parse C) := by
  simp [frontV, h, (inClassW_iff C).mpr hw]

/-- The table of the front end. -/
def frontTbl (n W : ℕ) : List (List Bool × List Bool) :=
  (winsN n).map fun p => (padW n (pairWord p), true :: gsW W (parse (pairWord p)))

theorem lookupV_frontTbl {n W : ℕ} {C : List Bool} (h : C.length ≤ n) :
    lookupV (frontTbl n W) [false] (padW n C) = frontV n W C := by
  unfold frontV frontTbl
  rw [if_pos h]
  by_cases hc : inClassW C = true
  · rw [if_pos hc]
    obtain ⟨p, hp, rfl⟩ := (inClassW_iff_windows _).mp hc
    refine lookupV_det _ _ _ _ _ _ (fun a ha e => ?_) ⟨p, mem_winsN.mpr ⟨hp, h⟩, rfl⟩
    rw [padW_inj (mem_winsN.mp ha).2 h e]
  · rw [if_neg hc]
    refine lookupV_none _ _ _ _ _ (fun a ha e => hc ?_)
    rw [← padW_inj (mem_winsN.mp ha).2 h e]
    exact (inClassW_iff_windows _).mpr ⟨a, (mem_winsN.mp ha).1, rfl⟩

/-- **The front end of the key query**: input `C` on tape `0`, output `frontV n W C`. -/
def frontP (n W : ℕ) : XProg 8 := cutLook n 0 (frontTbl n W) [false] []

theorem law_frontP (n W : ℕ) (C : List Bool) :
    (frontP n W).law (io2 (R := 6) C [] []) = PMF.pure (io2 (R := 6) (frontV n W C) [] []) := by
  have e : cutLookV n 0 (frontTbl n W) [false] [] C [] = frontV n W C := by
    unfold cutLookV
    split_ifs with h
    · rw [List.take_nil, List.append_nil, lookupV_frontTbl h]
    · rw [frontV_long h]
  rw [frontP, law_cutLook n 0 _ _ _ C [] le_rfl, e]

theorem wf_frontP (n W : ℕ) : (frontP n W).WF := wf_cutLook _ _ _ _ _

theorem timeBoundT_frontP (n W T : ℕ) :
    (frontP n W).timeBoundT (io2 (R := 6) T 0 0) ≤
      20 * T + ((n + 2) * (2 * (n + 2) + 5) + 10 * (2 * (n + 11) + 5) +
        (lookCount (frontTbl n W) [false] + 12) *
          (2 * (n + 1 + (lookCount (frontTbl n W) [false] + 12)) + 5)) := by
  have := timeBoundT_cutLook n 0 (frontTbl n W) [false] [] T 0
  simpa [frontP] using this

theorem lenBoundT_frontP (n W T : ℕ) :
    (frontP n W).lenBoundT (io2 (R := 6) T 0 0) ≤
      io2 (R := 6) (n + 1 + (lookCount (frontTbl n W) [false] + 12)) 0 0 := by
  have := lenBoundT_cutLook n 0 (frontTbl n W) [false] [] T 0
  simpa [frontP] using this

/-! ### The authorization test -/

/-- **The authorization test** with the length bound `nA`: the window class, then the evaluation of
the gate list on the date bits. -/
def authN (nA : ℕ) (C : List Bool) (x : Date) : Bool :=
  decide (C.length ≤ nA) && inClassW C && !evalGates (encDate x, parse C)

/-- The table of the authorization test: the short window predicates with the dates they accept. -/
def authTbl (nA : ℕ) : List (List Bool × List Bool) :=
  (((winsN nA) ×ˢ allDates).filter fun q => accP q.1 q.2).map
    fun q => (padW nA (pairWord q.1) ++ encDate q.2, [true])

theorem lookupV_authTbl {nA : ℕ} {C : List Bool} (h : C.length ≤ nA) (x : Date) :
    lookupV (authTbl nA) [false] (padW nA C ++ encDate x) = [authN nA C x] := by
  unfold authTbl
  rw [lookupV_const]
  have key : (∃ q ∈ ((winsN nA) ×ˢ allDates).filter (fun q => accP q.1 q.2),
      padW nA (pairWord q.1) ++ encDate q.2 = padW nA C ++ encDate x) ↔ authN nA C x = true := by
    constructor
    · rintro ⟨⟨p, x'⟩, hq, e⟩
      rw [List.mem_filter] at hq
      obtain ⟨hpx, hacc⟩ := hq
      have hp := (List.pair_mem_product.mp hpx).1
      obtain ⟨e1, e2⟩ := List.append_inj e (by simp)
      have hpc := padW_inj (mem_winsN.mp hp).2 h e1
      have hx : x' = x := encDate.injective e2
      subst hpc hx
      have hw := mem_windows.mp (mem_winsN.mp hp).1
      simp only [authN, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      refine ⟨⟨h, (inClassW_iff_windows _).mpr ⟨p, (mem_winsN.mp hp).1, rfl⟩⟩, ?_⟩
      rw [evalGates_pairWord hw]
      simpa using hacc
    · intro ha
      simp only [authN, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ha
      obtain ⟨⟨-, hc⟩, hev⟩ := ha
      obtain ⟨p, hp, rfl⟩ := (inClassW_iff_windows _).mp hc
      refine ⟨(p, x), ?_, rfl⟩
      rw [List.mem_filter]
      refine ⟨List.pair_mem_product.mpr ⟨mem_winsN.mpr ⟨hp, h⟩, mem_allDates x⟩, ?_⟩
      rw [evalGates_pairWord (mem_windows.mp hp)] at hev
      simpa using hev
  by_cases ha : authN nA C x = true
  · rw [if_pos (key.mpr ha), ha]
  · rw [if_neg (fun h' => ha (key.mp h'))]
    simp only [Bool.not_eq_true] at ha
    rw [ha]

/-- **The authorization test as a program**: inputs `C` and `encDate x` on tapes `0`, `1`, output
`[authN nA C x]`. -/
def authP (nA : ℕ) : XProg 8 := cutLook nA 10 (authTbl nA) [false] [false]

theorem law_authP (nA : ℕ) (C : List Bool) (x : Date) :
    (authP nA).law (io2 (R := 6) C (encDate x) []) =
      PMF.pure (io2 (R := 6) [authN nA C x] [] []) := by
  have e : cutLookV nA 10 (authTbl nA) [false] [false] C (encDate x) = [authN nA C x] := by
    unfold cutLookV
    rw [List.take_of_length_le (by rw [length_encDate])]
    split_ifs with h
    · rw [lookupV_authTbl h]
    · simp [authN, h]
  rw [authP, law_cutLook nA 10 _ _ _ C (encDate x) (by rw [length_encDate]), e]

theorem wf_authP (nA : ℕ) : (authP nA).WF := wf_cutLook _ _ _ _ _

theorem timeBoundT_authP (nA T : ℕ) :
    (authP nA).timeBoundT (io2 (R := 6) T 10 0) ≤
      20 * T + ((nA + 2) * (2 * (nA + 2) + 5) + 10 * (2 * (nA + 11) + 5) +
        (2 * 10 + lookCount (authTbl nA) [false] + 1 + 12) *
          (2 * (nA + 1 + 10 + (2 * 10 + lookCount (authTbl nA) [false] + 1 + 12)) + 5)) :=
  timeBoundT_cutLook nA 10 (authTbl nA) [false] [false] T 10

theorem lenBoundT_authP (nA T : ℕ) :
    (authP nA).lenBoundT (io2 (R := 6) T 10 0) ≤
      io2 (R := 6) (nA + 1 + 10 + (2 * 10 + lookCount (authTbl nA) [false] + 1 + 12)) 0 0 :=
  lenBoundT_cutLook nA 10 (authTbl nA) [false] [false] T 10

end AdvancedEncryption.PE.Gates.DateWindow
