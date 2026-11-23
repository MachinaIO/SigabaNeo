import PE.Impl.DualUse.ImplBase

/-!
# The dual-use implementation for the relaxed problem (width 8)

The problem (`PE/BranchingProgram.lean`) asks for branching programs on 14-bit states, with the
symbol width chosen by the submission. The dual-use implementation chooses the width `w8` (16
symbols of 8 bits) and keeps its own predicates, the programs on 32-bit states of
`PE/Impl/Gates/BP32.lean`:

* `univ w8` and `bpUniverse` have the same attributes, messages, encodings and description
  (`correct_iff`, `attributeHiding_iff`: the propositions are the same);
* every required program on 14-bit states is a program on 32-bit states with the same output
  (`liftBP`, `output_liftBP`), so expressiveness for `bpUniverse` gives expressiveness for
  `univ w8` (`expressive_of`).
-/

namespace AdvancedEncryption.DualUse.Relaxed

open SigabaNeo Cslib AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-- Correctness for `univ w8` is correctness for `bpUniverse`. -/
theorem correct_iff (impl : Impl sig) :
    Correct (univ w8) params impl ↔ Correct bpUniverse params impl := Iff.rfl

/-- A state of the experiment for `univ w8` as one for `bpUniverse` (the same fields). -/
def gsMap (s : GameState (univ w8)) : GameState bpUniverse :=
  { attr := s.attr, mpk := s.mpk, msk := s.msk, msg := s.msg, bad := s.bad }

theorem oracle_gsMap (impl : Impl sig)
    (ch : List Bool → (univ w8).Attr → (univ w8).Msg → PMF (List Bool))
    (q : Fin 3 × List Bool) (s : GameState (univ w8)) :
    (oracle params impl ch q s).map (fun r => (r.1, gsMap r.2)) =
      oracle (U := bpUniverse) params impl ch q (gsMap s) := by
  rcases s with ⟨attr, mpk, msk, msg, bad⟩
  by_cases hq : q.1 = selectOp
  · rcases attr with _ | x
    · rcases hd : decode (univ w8).encAttr q.2 with _ | x
      · have hd' : decode bpUniverse.encAttr q.2 = none := hd
        simp [oracle, hq, hd, hd', gsMap]
      · have hd' : decode bpUniverse.encAttr q.2 = some x := hd
        simp only [oracle, hq, hd, hd', if_true, PMF.map_comp, gsMap]
        rfl
    · simp [oracle, hq, gsMap]
  · by_cases hk : q.1 = keyGenOp
    · rcases attr with _ | x <;>
        (simp [oracle, hq, hk, gsMap, PMF.map_comp, Function.comp_def, selectOp, keyGenOp]) <;> rfl
    · rcases attr with _ | x <;> rcases msg with _ | μ <;>
        rcases hd : decode (univ w8).encMsg q.2 with _ | μ' <;>
        · have hd' : decode bpUniverse.encMsg q.2 = decode (univ w8).encMsg q.2 := rfl
          (simp [oracle, hq, hk, hd, hd', gsMap, PMF.map_comp, Function.comp_def]) <;> rfl

theorem game_gsMap (impl : Impl sig)
    (ch : List Bool → (univ w8).Attr → (univ w8).Msg → PMF (List Bool)) (A : Machine 3) :
    (game params impl ch A).map (fun r => (r.1, gsMap r.2)) =
      game (U := bpUniverse) params impl ch A := by
  unfold game Machine.runWith
  exact ProbOracleComp.runWith_map_state _ _ gsMap (oracle_gsMap impl ch) _ {}

theorem real_gsMap (impl : Impl sig) (A : Machine 3) :
    (real (univ w8) params impl A).map (fun r => (r.1, gsMap r.2)) =
      real bpUniverse params impl A := game_gsMap impl _ A

theorem ideal_gsMap (impl : Impl sig) (Sim : Machine) (A : Machine 3) :
    (ideal (univ w8) params impl Sim A).map (fun r => (r.1, gsMap r.2)) =
      ideal bpUniverse params impl Sim A := game_gsMap impl _ A

theorem view_real (impl : Impl sig) (A : Machine 3) :
    (real (univ w8) params impl A).map view = (real bpUniverse params impl A).map view := by
  rw [← real_gsMap, PMF.map_comp]; rfl

theorem view_ideal (impl : Impl sig) (Sim : Machine) (A : Machine 3) :
    (ideal (univ w8) params impl Sim A).map view = (ideal bpUniverse params impl Sim A).map view := by
  rw [← ideal_gsMap, PMF.map_comp]; rfl

theorem admissible_iff (impl : Impl sig) (Sim : Machine) (A : Machine 3) :
    Admissible (univ w8) params impl Sim A ↔ Admissible bpUniverse params impl Sim A := by
  unfold Admissible
  rw [← real_gsMap, ← ideal_gsMap]
  simp only [PMF.support_map, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  exact Iff.rfl

/-- Attribute hiding for `univ w8` is attribute hiding for `bpUniverse`. -/
theorem attributeHiding_iff (impl : Impl sig) :
    AttributeHiding (univ w8) params impl ↔ AttributeHiding bpUniverse params impl := by
  unfold AttributeHiding
  simp only [admissible_iff, view_real, view_ideal]

/-- A 14-bit state as a 32-bit state. -/
def up (z : ProgState) : State := Fin.castLE (Nat.pow_le_pow_right (by norm_num) (by norm_num)) z

/-- A 32-bit state cut to its low 14 bits. -/
def down (z : State) : ProgState := ⟨z.val % 2 ^ stateBits, Nat.mod_lt _ (by norm_num)⟩

theorem down_up (z : ProgState) : down (up z) = z := by
  apply Fin.ext; simp [down, up, Nat.mod_eq_of_lt z.isLt]

/-- A program on 14-bit states as a program on 32-bit states. -/
def liftBP (F : Program w8) : BP where
  step i z a := up (F.step i (down z) a)
  out z a := F.out (down z) a

theorem foldl_up (m : ℕ) (f : ProgState → Fin m → ProgState) (a : ProgState) :
    Fin.foldl m (fun z i => up (f (down z) i)) (up a) = up (Fin.foldl m f a) := by
  induction m generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ m ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last, ih (fun z i => f z i.castSucc) a, down_up]

theorem run_liftBP (F : Program w8) (x : Attr) : run (liftBP F) x = up (F.run x) :=
  foldl_up 15 (fun z (i : Fin 15) => F.step (show Fin (w8.len - 1) from i) z (x i.castSucc)) 0

theorem output_liftBP (F : Program w8) (x : Attr) : output (liftBP F) x = F.output x := by
  have h1 : output (liftBP F) x = F.out (down (run (liftBP F) x)) (x (Fin.last 15)) := rfl
  rw [h1, run_liftBP, down_up]
  rfl

/-- Expressiveness for `bpUniverse` gives expressiveness for `univ w8`. -/
theorem expressive_of {impl : Impl sig} (h : Expressive bpUniverse params impl) :
    Expressive (univ w8) params impl := by
  intro (F : Program w8)
  obtain ⟨C, hC⟩ := h (liftBP F)
  refine ⟨C, fun x => ?_⟩
  have := hC x
  show Authorized params impl C x ↔ F.output x = false
  rw [← output_liftBP F x]
  exact this

end AdvancedEncryption.DualUse.Relaxed
