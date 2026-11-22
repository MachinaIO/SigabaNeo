import SigabaNeo.Lib.Machines.Inline.Oracle

/-!
# Fixing the input of an oracle machine

`Inline.fixInput M w` runs the oracle machine `M` on the fixed word `w`, whatever its own input:
the input head of `M` is kept in the control state (`SA × Fin (w.length + 2)`), the symbols it
reads are looked up in `w` (`inSym`), and the real input head never moves. Each step of `M` is one
step of `fixInput M w`, so the running time, the work tapes and the channels are unchanged.

* `Inline.lawA_fixInput`: the run law of `fixInput M w` from the image (`fixCfg`) of a
  configuration of `M` on `w` is the image of that of `M`;
* `Machine.fixInput`, `Machine.runWith_fixInput`: as a `Machine ops` with the clock of `A`, its
  oracle law on any input is that of `A` on `w`;
* `Machine.states_fixInput`, `Machine.cost_fixInput_le`: `A.states * (|w| + 2)` states, and
  `cost ≤ fixFactor |w| * A.cost` with `fixFactor l = (l + 2) * (Nat.size (l + 2) + 1)`.
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops : ℕ} {SA : Type}

/-- The symbol under the input head at `p` on the input `w`. -/
def inSym (w : List Bool) (p : Fin (w.length + 2)) : Option Bool :=
  if p.val = 0 then none else w[p.val - 1]?

theorem inputSymbol_eq_inSym {k : ℕ} {S : Type} {w : List Bool} (c : Cfg k Bool S w) :
    c.inputSymbol = inSym w c.inputPos := by
  unfold Cfg.inputSymbol inSym
  have := c.inputPos.isLt
  by_cases h0 : c.inputPos = 0
  · simp [h0]
  · have h0' : c.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
    rw [dite_eq_right_of_eq_false (eq_false h0)]
    simp only [h0', ↓reduceIte]
    by_cases h1 : c.inputPos = w.length + 1
    · rw [dite_eq_left_of_eq_true (eq_true h1)]
      have : c.inputPos.val = w.length + 1 := by
        rw [h1]
      simp [this]
    · rw [dite_eq_right_of_eq_false (eq_false h1), List.getElem?_eq_getElem]

/-- An instruction of `M` with its input move kept in the control state. -/
def fixAct (w : List Bool) (p : Fin (w.length + 2)) :
    MultiTapeMachine.Action kA Bool SA (Fin ops) →
      MultiTapeMachine.Action kA Bool (SA × Fin (w.length + 2)) (Fin ops)
  | .step a sy mv =>
    .step ⟨0, a.workTapes, a.output, a.state.map fun q => (q, moveInputPos p a.inputTape)⟩ sy mv
  | .query o nx => .query o (nx, p)

/-- **`M` on the fixed input `w`.** -/
def fixInput (M : MultiTapePTM kA Bool SA (Fin ops)) (w : List Bool) :
    MultiTapePTM kA Bool (SA × Fin (w.length + 2)) (Fin ops) where
  initial := (M.initial, 1)
  tr q _ work ans := fun bit => fixAct w q.2 (M.tr q.1 (inSym w q.2) work ans bit)

/-- The configuration of `fixInput M w` (on any input `x`) simulating a configuration of `M` on
`w`. -/
def fixCfg {w x : List Bool} (c : Config kA Bool SA (Fin ops) w) :
    Config kA Bool (SA × Fin (w.length + 2)) (Fin ops) x :=
  ⟨⟨c.tapes.state.map (fun q => (q, c.tapes.inputPos)), 1, c.tapes.workTapes,
    c.tapes.workTapePos, c.tapes.output⟩, c.channels⟩

variable {w x : List Bool}

@[simp] theorem fixCfg_output (c : Config kA Bool SA (Fin ops) w) :
    (fixCfg (x := x) c).tapes.output = c.tapes.output := rfl

theorem fixCfg_initial (M : MultiTapePTM kA Bool SA (Fin ops)) :
    fixCfg (x := x) (M.initialConfig w) = (fixInput M w).initialConfig x := rfl

theorem fixCfg_step (c : Config kA Bool SA (Fin ops) w) (a : Turing.Action kA Bool SA)
    (sy : Fin ops → Option Bool) (mv : Fin ops → SignType) :
    (fixCfg (x := x) c).step
        ⟨0, a.workTapes, a.output, a.state.map fun q => (q, moveInputPos c.tapes.inputPos a.inputTape)⟩
        sy mv = fixCfg (c.step a sy mv) := by
  simp only [fixCfg, Config.step, Turing.Action.apply, moveInputPos_zero]

theorem fixCfg_receive (c : Config kA Bool SA (Fin ops) w) (o : Fin ops) (nx : SA)
    (a : List Bool) :
    (fixCfg (x := x) c).receive o (nx, c.tapes.inputPos) a = fixCfg (c.receive o nx a) := rfl

variable (M : MultiTapePTM kA Bool SA (Fin ops))

/-- One step of `fixInput M w` is one step of `M`. -/
theorem fixInput_one {Query : Type} {spec : OracleSpec.{0, 0} Query}
    (coin : OracleComp spec Bool) (query : Fin ops → List Bool → OracleComp spec (List Bool))
    (c : Config kA Bool SA (Fin ops) w) :
    MultiTapeMachine.runConfigFrom (fixInput M w) (fun choices => choices <$> coin) query 1
        (fixCfg (x := x) c) =
      fixCfg <$> MultiTapeMachine.runConfigFrom M (fun choices => choices <$> coin) query 1 c := by
  cases hs : c.tapes.state with
  | none =>
    have hs' : (fixCfg (x := x) c).tapes.state = none := by simp [fixCfg, hs]
    simp [MultiTapeMachine.runConfigFrom, hs, hs']
  | some q =>
    have hs' : (fixCfg (x := x) c).tapes.state = some (q, c.tapes.inputPos) := by
      simp [fixCfg, hs]
    simp only [MultiTapeMachine.runConfigFrom, hs, hs', map_bind]
    have htr : ((fixInput M w).tr (q, c.tapes.inputPos) (fixCfg (x := x) c).tapes.inputSymbol
        (fixCfg (x := x) c).tapes.workTapeSymbols (fixCfg (x := x) c).answerSymbols) <$> coin =
        fixAct w c.tapes.inputPos <$>
          (M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols <$> coin) := by
      rw [inputSymbol_eq_inSym c.tapes, Functor.map_map]
      rfl
    rw [htr, bind_map_left]
    congr 1
    funext act
    rcases act with ⟨a, sy, mv⟩ | ⟨o, nx⟩
    · simp only [fixAct, map_pure]
      rw [fixCfg_step]
    · simp only [fixAct, map_bind, map_pure]
      rfl

/-- **The law of `M` on the fixed input**, through `fixCfg`. -/
theorem lawA_fixInput {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (n : ℕ) (c : Config kA Bool SA (Fin ops) w) (s : σ) :
    lawA (fixInput M w) oracle n (fixCfg (x := x) c) s =
      (lawA M oracle n c s).map (fun r => (fixCfg r.1, r.2)) := by
  unfold lawA
  have h : (fixInput M w).runOracleConfigFrom n (fixCfg (x := x) c) =
      fixCfg <$> M.runOracleConfigFrom n c :=
    MultiTapeMachine.runConfigFrom_map (spec := probOracleSpec (fun _ : Fin ops × List Bool => List Bool))
      M (fixInput M w)
      (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word => ProbOracleComp.query (op, word)) (fun op word => ProbOracleComp.query (op, word))
      fixCfg (fun c => by exact fixInput_one M _ _ c) n c
  rw [h, ProbOracleComp.runWith_map]
  rfl

end SigabaNeo.Inline

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Inline

variable {ops : ℕ}

/-- **`A` on the fixed input `w`**, with the clock of `A`. -/
noncomputable def Machine.fixInput (A : Machine ops) (w : List Bool) : Machine ops :=
  Machine.ofPTMOps (Inline.fixInput A.machine w) A.time

@[simp] theorem Machine.tapes_fixInput (A : Machine ops) (w : List Bool) :
    (A.fixInput w).tapes = A.tapes := rfl

@[simp] theorem Machine.time_fixInput (A : Machine ops) (w : List Bool) :
    (A.fixInput w).time = A.time := rfl

theorem Machine.states_fixInput (A : Machine ops) (w : List Bool) :
    (A.fixInput w).states = A.states * (w.length + 2) := by
  simp [Machine.fixInput]

/-- **The oracle law of `A` on the fixed input `w`**, whatever the input. -/
theorem Machine.runWith_fixInput {σ : Type} (A : Machine ops) (w : List Bool)
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (x : List Bool) (s : σ) :
    (A.fixInput w).runWith oracle x s = A.runWith oracle w s := by
  rw [Machine.fixInput, Machine.runWith_ofPTMOps, MultiTapePTM.runOracle_eq_map,
    ProbOracleComp.runWith_map, ← fixCfg_initial]
  have := lawA_fixInput (x := x) A.machine oracle A.time (A.machine.initialConfig w) s
  unfold lawA at this
  rw [this, PMF.map_comp]
  unfold Machine.runWith
  rw [MultiTapePTM.runOracle_eq_map, ProbOracleComp.runWith_map]
  rfl

/-- The cost factor of fixing an input of length `l`. -/
def fixFactor (l : ℕ) : ℕ := (l + 2) * (Nat.size (l + 2) + 1)

theorem Machine.descLen_fixInput_le (A : Machine ops) (w : List Bool) :
    (A.fixInput w).descLen ≤ fixFactor w.length * A.descLen := by
  have hd : (A.fixInput w).descLen = 6 * (A.states * (w.length + 2)) * 3 ^ A.tapes * 3 ^ ops *
      Machine.entryBits A.tapes (A.states * (w.length + 2)) ops := by
    rw [Machine.descLen, Machine.states_fixInput, Machine.tapes_fixInput]
  have he : Machine.entryBits A.tapes (A.states * (w.length + 2)) ops ≤
      (Nat.size (w.length + 2) + 1) * Machine.entryBits A.tapes A.states ops := by
    have := size_mul_le' A.states (w.length + 2)
    simp only [Machine.entryBits] at this ⊢
    nlinarith
  rw [hd, Machine.descLen, fixFactor]
  calc 6 * (A.states * (w.length + 2)) * 3 ^ A.tapes * 3 ^ ops *
        Machine.entryBits A.tapes (A.states * (w.length + 2)) ops
      ≤ 6 * (A.states * (w.length + 2)) * 3 ^ A.tapes * 3 ^ ops *
        ((Nat.size (w.length + 2) + 1) * Machine.entryBits A.tapes A.states ops) :=
        Nat.mul_le_mul_left _ he
    _ = _ := by ring

/-- **Cost of fixing the input**: `cost ≤ fixFactor |w| * A.cost`. -/
theorem Machine.cost_fixInput_le (A : Machine ops) (w : List Bool) :
    (A.fixInput w).cost ≤ fixFactor w.length * A.cost := by
  have hd := A.descLen_fixInput_le w
  have h1 : 1 ≤ fixFactor w.length := Nat.mul_pos (by omega) (by omega)
  rw [Machine.cost, Machine.cost, Machine.time_fixInput]
  nlinarith

end SigabaNeo
