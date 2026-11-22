import SigabaNeo.Lib.Machines.Inline.InitDefs

/-!
# Inlining an oracle handler for a reduction: the phases

* `lawM_seq`: the run law of `first.seq second` when `first` halts within `t` steps and `second`
  within `n` steps from every handoff (random stopping times);
* `lawM_clock`: the first phase (`machineLin H haltM (T + 1)`) reaches, deterministically, the
  blank tapes with a clock of `T + 1` cells, its head on cell `T - 1`;
* `lawM_copy`: the copy phase erases the extra cell and copies the input onto `st`, in
  `2 |x| + 4` steps;
* `lawM_out`: the output phase appends `false :: true :: dbl u` for the word `u` on `st`, in
  `2 |u| + 3` steps.
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {x : List Bool}

/-! ### Sequencing -/

section Seq

variable {k : ℕ} {S₀ S₁ : Type} (first : MultiTapePTM k Bool S₀ (Fin 0))
  (second : MultiTapePTM k Bool S₁ (Fin 0))

/-- **Sequencing** with halting bounds for both phases. -/
theorem lawM_seq (t n : ℕ) (c : Config k Bool S₀ (Fin 0) x)
    (h1 : ∀ r ∈ (lawM first t c).support, r.1.tapes.state = none)
    (h2 : ∀ r ∈ (lawM first t c).support, ∀ f ∈ (lawM second n
      (Sequential.start second r.1)).support, f.1.tapes.state = none) :
    lawM (first.seq second) (t + n) (Sequential.left second c) =
      (lawM first t c).bind (fun r => (lawM second n (Sequential.start second r.1)).map
        (fun f => (Sequential.right f.1, f.2))) := by
  unfold lawM at h1 h2 ⊢
  exact MultiTapeMachine.run_interpret_runConfigFrom_seq
    (spec := probOracleSpec (fun _ : Fin 0 × List Bool => List Bool)) first second
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun _ _ => by rw [Functor.map_map]; rfl)
    (fun op word => ProbOracleComp.query (op, word))
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
      (fun e : Fin 0 × List Bool => e.1.elim0)) c t n () h1 h2

/-- The configurations reached by a sequence whose second phase halts are halted. -/
theorem halted_of_bind {S : Type} (μ : PMF S) (g : S → PMF (Config k Bool S₁ (Fin 0) x × Unit))
    (hg : ∀ r ∈ μ.support, ∀ f ∈ (g r).support, f.1.tapes.state = none) :
    ∀ f ∈ (μ.bind (fun r => (g r).map (fun f => (Sequential.right (State₀ := S₀) f.1, f.2)))).support,
      f.1.tapes.state = none := by
  intro f hf
  obtain ⟨r, hr, hf⟩ := (PMF.mem_support_bind_iff _ _ _).mp hf
  obtain ⟨f', hf', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hf
  simp [Sequential.right, hg r hr f' hf']

end Seq

/-! ### Named configurations -/

theorem idx_kind (i : Fin (nTapes kA ops m)) : (kind (kA := kA) (ops := ops) (m := m) i).idx = i := by
  have := i.isLt
  unfold kind
  split_ifs <;> ext <;> simp [Tape.idx] <;> omega

/-- Every configuration is a named one. -/
theorem mkR_eta {S : Type} (c : Config (nTapes kA ops m) Bool S (Fin 0) x) :
    c = mkR c.tapes.state c.tapes.inputPos (fun t => c.tapes.workTapes t.idx)
      (fun t => c.tapes.workTapePos t.idx) c.tapes.output := by
  refine Config.ext ?_ (funext fun e => e.elim0)
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> simp [mkR, idx_kind]

theorem start_mkR {S S' : Type} (Mc : MultiTapePTM (nTapes kA ops m) Bool S' (Fin 0))
    (q : Option S) (ip : Fin (x.length + 2)) (F : Tape kA ops m → ℤ → Option Bool)
    (P : Tape kA ops m → ℤ) (out : List Bool) :
    Sequential.start Mc (mkR q ip F P out) = mkR (some Mc.initial) ip F P out := rfl

theorem lawM_halted' {k : ℕ} {S : Type} (Mc : MultiTapePTM k Bool S (Fin 0)) (N : ℕ)
    (c : Config k Bool S (Fin 0) x) (h : c.tapes.state = none) : lawM Mc N c = PMF.pure (c, ()) :=
  law_halted _ _ _ _ _ h

/-! ### The clock -/

section Clock

variable (H : Fin ops → Routine (m + 3)) (T : ℕ)

/-- The configuration after the first phase: blank tapes but a clock of `T + 1` cells, its head
on cell `T - 1`. -/
abbrev clkCfg {S : Type} : Config (nTapes kA ops m) Bool S (Fin 0) x :=
  mkR none 1 (lF [] (T + 1)) (lP 0 ((T : ℤ) - 1)) []

/-- The number of steps of the first phase. -/
abbrev clkTime (kA T : ℕ) : ℕ := 4 * (T + 1) + 4 * (clockDigits kA (T + 1)).length + 5

/-- **The first phase.** -/
theorem lawM_clock :
    lawM (machineLin H (haltM (kA := kA) (ops := ops)) (T + 1)) (clkTime kA T)
      ((machineLin H (haltM (kA := kA) (ops := ops)) (T + 1)).initialConfig x) =
      PMF.pure (clkCfg (m := m) T, ()) := by
  obtain ⟨t, ht, hprep⟩ := lawLin_prep (x := x) (m := m) H (haltM (kA := kA) (ops := ops)) (T + 1)
  have hle : t + 1 ≤ clkTime kA T := by unfold clkTime; omega
  rw [show clkTime kA T = t + ((clkTime kA T - t - 1) + 1) by omega, hprep]
  unfold finCfg
  have hclk : lF (kA := kA) (ops := ops) (m := m) [] (T + 1) .clock
      (lP (kA := kA) (ops := ops) (m := m) 0 (((T + 1 : ℕ) : ℤ) - 1) .clock) = some true := by
    simp only [lF, lP]
    rw [show (((T + 1 : ℕ) : ℤ) - 1) = ((T : ℕ) : ℤ) by push_cast; ring]
    simp
  have htr : ∀ inp bit, (machineLin (m := m) H (haltM (kA := kA) (ops := ops)) (T + 1)).tr
      (.inr (ctl0 H (haltM (kA := kA) (ops := ops)))) inp
      (fun i => lF (kA := kA) (ops := ops) (m := m) [] (T + 1) (kind i)
        (lP 0 (((T + 1 : ℕ) : ℤ) - 1) (kind i))) (fun e => e.elim0) bit =
      stepR (mkAct 0 (simW (kA := kA) (m := m) (SA := Unit) (fun _ => .empty) ⟨0, fun _ => (none, 0), none, none⟩
        (fun _ => none) (fun _ => 0)) none none) := by
    intro inp bit
    unfold machineLin simM machine
    simp only [ctl0, simAct, kind_idx, hclk, ne_eq, not_true_eq_false, ite_false, haltM]
    rfl
  rw [lawM_det _ _ _ 1 _ _ [] 0 _ none none (fun bit => htr _ bit), lawM_halted' _ _ _ rfl]
  unfold clkCfg
  congr 3
  all_goals (funext t; rcases t with i | o | o | _ | _ | j <;> simp [simW, lP, sub_eq_add_neg])

end Clock

end SigabaNeo.Inline
