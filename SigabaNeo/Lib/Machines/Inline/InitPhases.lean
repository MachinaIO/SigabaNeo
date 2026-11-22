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

/-! ### The copy -/

section Copy

/-- The tapes of the copy phase: a clock of `c` cells and the word `u` on `st`. -/
def cpF (c : ℕ) (u : List Bool) : Tape kA ops m → ℤ → Option Bool
  | .clock => tapeOfList (List.replicate c true)
  | .st => tapeOfList u
  | _ => fun _ => none

/-- The heads of the copy phase. -/
def cpP (pc ps : ℤ) : Tape kA ops m → ℤ
  | .clock => pc
  | .st => ps
  | _ => 0

/-- A configuration of the copy phase. -/
abbrev cpCfg (q : Option CStep) (ip : Fin (x.length + 2)) (c : ℕ) (u : List Bool) (pc ps : ℤ) :
    Config (nTapes kA ops m) Bool CStep (Fin 0) x :=
  mkR q ip (cpF c u) (cpP pc ps) []

theorem cp_lF (T : ℕ) : lF (kA := kA) (ops := ops) (m := m) [] (T + 1) = cpF (T + 1) [] := by
  funext t
  rcases t with i | o | o | _ | _ | j <;> simp [lF, cpF]

theorem cp_lP (p : ℤ) : lP (kA := kA) (ops := ops) (m := m) 0 p = cpP p 0 := by
  funext t
  rcases t with i | o | o | _ | _ | j <;> rfl

theorem cp_mv_clock (c : ℕ) (u : List Bool) (pc ps : ℤ) (d : SignType) :
    (fun t => wr (cpF (kA := kA) (ops := ops) (m := m) c u t) (cpP pc ps t)
      (mv1 .clock none d t).1) = cpF c u ∧
    (fun t => cpP (kA := kA) (ops := ops) (m := m) pc ps t + ((mv1 .clock none d t).2 : ℤ)) =
      cpP (pc + d) ps := by
  constructor <;> funext t <;> rcases t with i | o | o | _ | _ | j <;> simp [mv1, cpP]

theorem cp_mv_st (c : ℕ) (u : List Bool) (pc ps : ℤ) (d : SignType) :
    (fun t => wr (cpF (kA := kA) (ops := ops) (m := m) c u t) (cpP pc ps t)
      (mv1 .st none d t).1) = cpF c u ∧
    (fun t => cpP (kA := kA) (ops := ops) (m := m) pc ps t + ((mv1 .st none d t).2 : ℤ)) =
      cpP pc (ps + d) := by
  constructor <;> funext t <;> rcases t with i | o | o | _ | _ | j <;> simp [mv1, cpP]

theorem cp_write (c : ℕ) (u : List Bool) (pc : ℤ) (b : Bool) :
    (fun t => wr (cpF (kA := kA) (ops := ops) (m := m) c u t) (cpP pc u.length t)
      (mv1 .st (some (some b)) 1 t).1) = cpF c (u ++ [b]) := by
  funext t
  rcases t with i | o | o | _ | _ | j <;> simp [mv1, cpF, cpP, wr, tapeOfList_append_single]

theorem mip_eq {n : ℕ} (p : Fin (n + 2)) (d : SignType) (q : Fin (n + 2))
    (h : (q.val : ℤ) = p.val + d) : moveInputPos p d = q := by
  apply Fin.ext
  have := val_moveInputPos_eq p d
  have := q.isLt
  omega

variable (T : ℕ)

/-- The configuration after the copy: the clock of `T` cells, `x` on `st`, the heads back. -/
abbrev cpEnd : Config (nTapes kA ops m) Bool CStep (Fin 0) x :=
  cpCfg none 1 T x ((T : ℤ) - 1) 0

theorem copyM_tr (q : CStep) inp work ans bit :
    (copyM (kA := kA) (ops := ops) (m := m)).tr q inp work ans bit = stepR (cpAct q inp work) :=
  rfl

/-- Rewinding `st` and the input head. -/
theorem lawM_rew (N : ℕ) : ∀ j (hj : j ≤ x.length),
    lawM (copyM (kA := kA) (ops := ops) (m := m)) (N + j + 1)
      (cpCfg (x := x) (some .rew) ⟨j, by omega⟩ T x ((T : ℤ) - 1) ((j : ℤ) - 1)) =
      lawM copyM N (cpEnd T) := by
  intro j
  induction j with
  | zero =>
    intro _
    have hst : cpF (kA := kA) (ops := ops) (m := m) T x .st (cpP (kA := kA) (ops := ops) (m := m) ((T : ℤ) - 1) (((0 : ℕ) : ℤ) - 1) .st)
        = none := by simp [cpF, cpP, tapeOfList_eq_none_iff]
    rw [Nat.add_zero, lawM_det _ N _ _ _ _ [] 1 (mv1 .st none 1) none none (fun bit => by
      rw [copyM_tr]; simp only [cpAct, kind_idx, hst])]
    obtain ⟨h1, h2⟩ := cp_mv_st (kA := kA) (ops := ops) (m := m) T x ((T : ℤ) - 1) (((0 : ℕ) : ℤ) - 1) 1
    rw [h1, h2]
    congr 3
  | succ j ih =>
    intro hj
    have hst : cpF (kA := kA) (ops := ops) (m := m) T x .st (cpP (kA := kA) (ops := ops) (m := m) ((T : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) .st)
        = some x[j] := by simp [cpF, cpP]
    rw [show N + (j + 1) + 1 = (N + j + 1) + 1 by omega,
      lawM_det _ _ _ _ _ _ [] (-1) (mv1 .st none (-1)) none (some .rew) (fun bit => by
      rw [copyM_tr]; simp only [cpAct, kind_idx, hst])]
    obtain ⟨h1, h2⟩ := cp_mv_st (kA := kA) (ops := ops) (m := m) T x ((T : ℤ) - 1)
      (((j + 1 : ℕ) : ℤ) - 1) (-1)
    rw [h1, h2, ← ih (by omega)]
    congr 3
    · exact mip_eq _ _ _ (by simp)
    · simp; ring

/-- Copying the input onto `st`. -/
theorem lawM_cp (N : ℕ) : ∀ k i (hk : i + k = x.length),
    lawM (copyM (kA := kA) (ops := ops) (m := m)) (N + k)
      (cpCfg (x := x) (some .copy) ⟨1 + i, by omega⟩ T (x.take i) ((T : ℤ) - 1) i) =
      lawM copyM N (cpCfg (x := x) (some .copy) ⟨x.length + 1, by omega⟩ T x ((T : ℤ) - 1) x.length) := by
  intro k
  induction k with
  | zero =>
    intro i hk
    obtain rfl : i = x.length := by omega
    rw [List.take_length, Nat.add_zero]
    congr 3
    omega
  | succ k ih =>
    intro i hk
    have hi : i < x.length := by omega
    have hinp : (cpCfg (kA := kA) (ops := ops) (m := m) (x := x) (some .copy) ⟨1 + i, by omega⟩ T
        (x.take i) ((T : ℤ) - 1) i).tapes.inputSymbol = some x[i] :=
      inputSymbolInner i rfl hi
    rw [show N + (k + 1) = (N + k) + 1 by omega,
      lawM_det _ _ _ _ _ _ [] 1 (mv1 .st (some (some x[i])) 1) none (some .copy) (fun bit => by
      rw [copyM_tr, hinp]; rfl)]
    have hlen : (x.take i).length = i := by simp; omega
    have hw := cp_write (kA := kA) (ops := ops) (m := m) T (x.take i) ((T : ℤ) - 1) x[i]
    rw [hlen, ← List.take_succ_eq_append_getElem hi] at hw
    have h2' : (fun t => cpP (kA := kA) (ops := ops) (m := m) ((T : ℤ) - 1) i t +
        ((mv1 .st (some (some x[i])) 1 t).2 : ℤ)) = cpP ((T : ℤ) - 1) (i + 1) := by
      funext t; rcases t with i' | o | o | _ | _ | j <;> simp [mv1, cpP]
    rw [hw, h2', ← ih (i + 1) (by omega)]
    congr 3
    exact mip_eq _ _ _ (by simp; ring)

/-- **The copy phase**: from the end of the first phase, the clock of `T` cells, `x` on `st`,
within `2 |x| + 4` steps. -/
theorem lawM_copy {S : Type} (N : ℕ) :
    lawM (copyM (kA := kA) (ops := ops) (m := m)) (2 * x.length + 4 + N)
      (Sequential.start copyM (clkCfg (x := x) (S := S) T)) =
      lawM copyM N (cpEnd T) := by
  rw [start_mkR, cp_lF, cp_lP]
  -- step onto the extra cell
  rw [show 2 * x.length + 4 + N = (2 * x.length + 3 + N) + 1 by omega,
    lawM_det _ _ _ _ _ _ [] 0 (mv1 .clock none 1) none (some .clkE) (fun bit => rfl)]
  obtain ⟨h1, h2⟩ := cp_mv_clock (kA := kA) (ops := ops) (m := m) (T + 1) [] ((T : ℤ) - 1) 0 1
  rw [h1, h2, moveInputPos_zero, Option.toList_none, List.append_nil]
  -- erase it
  rw [show 2 * x.length + 3 + N = (2 * x.length + 2 + N) + 1 by omega,
    lawM_det _ _ _ _ _ _ [] 0 (mv1 .clock (some none) (-1)) none (some .copy) (fun bit => rfl)]
  have hF : (fun t => wr (cpF (kA := kA) (ops := ops) (m := m) (T + 1) [] t)
      (cpP ((T : ℤ) - 1 + ((1 : SignType) : ℤ)) 0 t) (mv1 .clock (some none) (-1) t).1) =
      cpF T (x.take 0) := by
    funext t
    rcases t with i | o | o | _ | _ | j <;> simp [mv1, cpF, cpP, wr]
    rw [List.replicate_succ', ← tapeOfList_erase_last (List.replicate T true) true]
    simp
  have hP : (fun t => cpP (kA := kA) (ops := ops) (m := m) ((T : ℤ) - 1 + ((1 : SignType) : ℤ)) 0 t +
      ((mv1 .clock (some none) (-1) t).2 : ℤ)) = cpP ((T : ℤ) - 1) ((0 : ℕ) : ℤ) := by
    funext t
    rcases t with i | o | o | _ | _ | j <;> simp [mv1, cpP, sub_eq_add_neg]
  rw [hF, hP, moveInputPos_zero, Option.toList_none, List.append_nil]
  -- copy
  rw [show 2 * x.length + 2 + N = ((N + x.length + 1) + 1) + x.length by omega]
  have h1 : (1 : Fin (x.length + 2)) = ⟨1 + 0, by omega⟩ := Fin.ext (by simp)
  rw [h1, lawM_cp T _ x.length 0 (by omega)]
  -- the end of the input
  have hinp : (cpCfg (kA := kA) (ops := ops) (m := m) (x := x) (some .copy)
      ⟨x.length + 1, by omega⟩ T x ((T : ℤ) - 1) x.length).tapes.inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr rfl)
  rw [lawM_det _ _ _ _ _ _ [] (-1) (mv1 .st none (-1)) none (some .rew) (fun bit => by
    rw [copyM_tr, hinp]; rfl)]
  obtain ⟨h1, h2⟩ := cp_mv_st (kA := kA) (ops := ops) (m := m) T x ((T : ℤ) - 1) x.length (-1)
  rw [h1, h2, Option.toList_none, List.append_nil, ← lawM_rew T N x.length le_rfl]
  congr 3
  · exact mip_eq _ _ _ (by simp)

end Copy

end SigabaNeo.Inline
