import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

namespace SigabaNeo

open Turing Turing.MultiTapeTM

abbrev GateList := List (ℕ × ℕ)

abbrev encGate : ℕ × ℕ ↪ List Bool := encPair encUnary encUnary
abbrev encGates : GateList ↪ List Bool := encList encGate

/-- Parser state: gates read, the current count, the pending count and whether it is set. -/
abbrev PState := (GateList × ℕ) × (ℕ × Bool)
abbrev encPState : PState ↪ List Bool :=
  encPair (encPair encGates encUnary) (encPair encUnary encBool)

def pstep (s : PState) (b : Bool) : PState :=
  if b then ((s.1.1, s.1.2 + 1), s.2)
  else if s.2.2 then ((s.1.1 ++ [(s.2.1, s.1.2)], 0), (0, false))
  else ((s.1.1, 0), (s.1.2, true))

def parse (w : List Bool) : GateList := (w.foldl pstep (([], 0), (0, false))).1.1

open ComputableTidilyInPolyTime

theorem pstep_polyTime : ComputableTidilyInPolyTime (fun p : PState × Bool => pstep p.1 p.2)
    (encPair encPState encBool) encPState := by
  unfold pstep
  fun_prop

/-- The parser's invariant after `m` bits. -/
def PInv (m : ℕ) (s : PState) : Prop :=
  s.1.1.length ≤ m ∧ (∀ g ∈ s.1.1, g.1 ≤ m ∧ g.2 ≤ m) ∧ s.1.2 ≤ m ∧ s.2.1 ≤ m

theorem PInv.mono {m m' : ℕ} {s : PState} (h : PInv m s) (hm : m ≤ m') : PInv m' s :=
  ⟨h.1.trans hm, fun g hg => ⟨((h.2.1 g hg).1).trans hm, ((h.2.1 g hg).2).trans hm⟩,
    h.2.2.1.trans hm, h.2.2.2.trans hm⟩

theorem PInv.step {m : ℕ} {s : PState} (h : PInv m s) (b : Bool) : PInv (m + 1) (pstep s b) := by
  obtain ⟨⟨gs, c⟩, ⟨p, f⟩⟩ := s
  obtain ⟨h1, h2, h3, h4⟩ := h
  dsimp only at h1 h2 h3 h4
  have h2' : ∀ g ∈ gs, g.1 ≤ m + 1 ∧ g.2 ≤ m + 1 := fun g hg =>
    ⟨(h2 g hg).1.trans (by omega), (h2 g hg).2.trans (by omega)⟩
  cases b <;> cases f
  · exact ⟨by simp [pstep]; omega, h2', by simp [pstep], by simp [pstep]; omega⟩
  · refine ⟨by simp [pstep]; omega, fun g hg => ?_, by simp [pstep], by simp [pstep]⟩
    simp only [pstep, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h2' g hg
    · exact ⟨by omega, by omega⟩
  · exact ⟨by simp [pstep]; omega, h2', by simp [pstep]; omega, by simp [pstep]; omega⟩
  · exact ⟨by simp [pstep]; omega, h2', by simp [pstep]; omega, by simp [pstep]; omega⟩

theorem length_encGates_le {m : ℕ} (gs : GateList) (hg : ∀ g ∈ gs, g.1 ≤ m ∧ g.2 ≤ m) :
    (encGates gs).length ≤ gs.length * (6 * m + 3) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have := hg g (by simp)
    have ih := ih (fun g' h' => hg g' (by simp [h']))
    simp only [encList_cons, List.length_append, length_frame, length_encPair, encUnary_apply,
      List.length_replicate, List.length_cons] at ih ⊢
    nlinarith

theorem PInv.length_le {m : ℕ} {s : PState} (h : PInv m s) :
    (encPState s).length ≤ 30 * (m + 1) ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hg := length_encGates_le s.1.1 h2
  have : s.1.1.length * (6 * m + 3) ≤ m * (6 * m + 3) := Nat.mul_le_mul_right _ h1
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBool_apply, List.length_singleton] at hg ⊢
  simp
  nlinarith

theorem parse_polyTime : ComputableTidilyInPolyTime parse encBits encGates := by
  have h := (foldl_spec (encA := encBool) (encL := encBits) (encB := encPState)
    (list := fun w : List Bool => w) (init := fun _ => (([], 0), (0, false))) (step := pstep)
    (id' (encIn := encBits)) (const _) pstep_polyTime
    (fun _ consumed s => PInv consumed.length s)
    (fun _ => by simp [PInv])
    (fun _ consumed s b _ hs => by simpa using hs.step b)
    (size := fun w => 30 * (w.length + 1) ^ 2)
    (PolyBounded.of_forall_le 30 2 (fun w => by simp))
    (fun w consumed s hpre hs => (hs.mono hpre.length_le).length_le)).1
  unfold parse
  fun_prop

/-! ### Evaluation -/

/-- One gate: the NAND of two wires (a wire not yet computed reads `true`). -/
def estep (s : List Bool × Bool) (g : ℕ × ℕ) : List Bool × Bool :=
  let v := !(s.1.getD g.1 true && s.1.getD g.2 true)
  (s.1 ++ [v], v)

/-- The output of the last gate of `gs` on the wires `true :: x`, or `true` if there is none. -/
def evalGates (p : List Bool × GateList) : Bool :=
  (p.2.foldl estep (true :: p.1, true)).2

theorem estep_polyTime : ComputableTidilyInPolyTime
    (fun p : (List Bool × Bool) × (ℕ × ℕ) => estep p.1 p.2)
    (encPair (encPair encBits encBool) encGate) (encPair encBits encBool) := by
  unfold estep
  fun_prop

theorem evalGates_polyTime :
    ComputableTidilyInPolyTime evalGates (encPair encBits encGates) encBool := by
  have h := foldl_of_bounded_growth (encA := encGate) (encL := encGates)
    (encB := encPair encBits encBool)
    (list := fun p : List Bool × GateList => p.2) (init := fun p => (true :: p.1, true))
    (step := estep) (snd _ _) (by fun_prop) estep_polyTime (growth := 2)
    (fun s g => by simp [estep, encBool_apply]; omega)
  unfold evalGates
  fun_prop

end SigabaNeo

namespace SigabaNeo

/-! ### The format of gate lists -/

/-- The word of a gate list: each index in unary, ended by `false`. -/
def unparse (gs : GateList) : List Bool :=
  gs.flatMap fun g => List.replicate g.1 true ++ [false] ++ List.replicate g.2 true ++ [false]

theorem foldl_pstep_replicate (n : ℕ) (gs : GateList) (c p : ℕ) (f : Bool) :
    (List.replicate n true).foldl pstep ((gs, c), (p, f)) = ((gs, c + n), (p, f)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons]
    simp only [pstep, ite_true]
    rw [ih]; congr 2; omega

theorem foldl_pstep_unparse (gs acc : GateList) :
    (unparse gs).foldl pstep ((acc, 0), (0, false)) = ((acc ++ gs, 0), (0, false)) := by
  induction gs generalizing acc with
  | nil => simp [unparse]
  | cons g gs ih =>
    have : unparse (g :: gs) = List.replicate g.1 true ++ [false] ++ List.replicate g.2 true ++
        [false] ++ unparse gs := by simp [unparse]
    rw [this]
    simp only [List.foldl_append, foldl_pstep_replicate, List.foldl_cons, List.foldl_nil]
    simp only [pstep, Bool.false_eq_true, ↓reduceIte, zero_add, foldl_pstep_replicate]
    rw [ih]; simp

theorem parse_unparse (gs : GateList) : parse (unparse gs) = gs := by
  simp [parse, foldl_pstep_unparse]

theorem length_unparse (gs : GateList) :
    (unparse gs).length = (gs.map fun g => g.1 + g.2 + 2).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [unparse] at ih ⊢; rw [ih]; omega

end SigabaNeo
