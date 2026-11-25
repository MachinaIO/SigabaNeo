import SigabaNeoStd.Machines.Inline.Phases

/-!
# Inlining an oracle handler: the handler phase

While the handler `H o` runs, the inlined machine simulates it step by step on the tapes `qry o`,
`ans o`, `st` and the scratch tapes (`hTape`), with a frozen input head and no output; when the
handler halts, the inlined machine goes on to erase the query. `lawR_handler`: if the handler
realizes the law `μ` on its words (`Routine.Runs`), then `time + N` steps from the start of the
handler phase are a draw from `μ` followed by `N` steps from the configuration with the drawn
words.
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {SA : Type} (H : Fin ops → Routine (m + 3))
  (M : MultiTapePTM kA Bool SA (Fin ops)) (T : ℕ) (w : List Bool) {x : List Bool}

/-- The words of the handler: the query, the answer, the state, blank scratch tapes. -/
def layout (b a s : List Bool) (j : Fin (m + 3)) : List Bool :=
  if j.val = 0 then b else if j.val = 1 then a else if j.val = 2 then s else []

section

variable (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (ip : Fin (x.length + 2))
  (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool)

/-- The tapes with those of the handler of `o` replaced. -/
def withH (tp : Fin (m + 3) → ℤ → Option Bool) : Tape kA ops m → ℤ → Option Bool :=
  fun t => match hPre o t with
    | some j => tp j
    | none => F t

/-- The heads with those of the handler of `o` replaced. -/
def withHP (pp : Fin (m + 3) → ℤ) : Tape kA ops m → ℤ :=
  fun t => match hPre o t with
    | some j => pp j
    | none => P t

/-- The inlined machine while the handler runs. -/
def embH (c : Config (m + 3) Bool (H o).State Empty []) :
    Config (nTapes kA ops m) Bool (RState SA H T w) (Fin 0) x :=
  mkR (c.tapes.state.map (hS H T w q fl o)) ip (withH o F c.tapes.workTapes)
    (withHP o P c.tapes.workTapePos) out

/-- The inlined machine once the handler has halted. -/
def exitH (c : Config (m + 3) Bool (H o).State Empty []) :
    Config (nTapes kA ops m) Bool (RState SA H T w) (Fin 0) x :=
  mkR (some (qS H T w q fl o .qToEnd)) ip (withH o F c.tapes.workTapes)
    (withHP o P c.tapes.workTapePos) out

theorem withH_hTape (tp : Fin (m + 3) → ℤ → Option Bool) (j : Fin (m + 3)) :
    withH o F tp (hTape o j) = tp j := by
  simp [withH]

theorem withHP_hTape (pp : Fin (m + 3) → ℤ) (j : Fin (m + 3)) :
    withHP o P pp (hTape o j) = pp j := by
  simp [withHP]

/-- One step of the handler is one step of the inlined machine. -/
theorem lawR_embH_one (c : Config (m + 3) Bool (H o).State Empty []) (hc : c.tapes.state ≠ none)
    (s : Unit) :
    lawR H M T w 1 (embH H T w q fl o ip F P out c) =
      ((H o).law 1 c).map (fun r => (simOrExit (embH H T w q fl o ip F P out)
        (exitH H T w q fl o ip F P out) r.1, s)) := by
  obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hc
  cases s
  unfold lawR Routine.law
  rw [law_succ_live _ _ 0 _ () (q := hS H T w q fl o h) (by simp [embH, hh]),
    law_succ_live _ _ 0 _ () hh, PMF.map_bind]
  congr 1 with bit : 1
  have hsym : (fun j => (embH H T w q fl o ip F P out c).tapes.workTapeSymbols (hTape o j).idx) =
      c.tapes.workTapeSymbols := by
    funext j
    simp [embH, mkR, withH, withHP, Cfg.workTapeSymbols]
  have hinp : c.tapes.inputSymbol = none := inputSymbol_nil _
  have hans : c.answerSymbols = fun e => e.elim := funext fun e => e.elim
  simp only [machine, hS, hAct]
  rw [hsym, hinp, hans]
  cases hH : (H o).machine.tr h none c.tapes.workTapeSymbols (fun e => e.elim) bit with
  | query e _ => exact e.elim
  | step a sy mv =>
    simp only [stepR, stepLaw, law_zero, PMF.pure_map]
    congr 2
    rw [embH, step_mkR]
    have hF : (fun t => wr (withH o F c.tapes.workTapes t) (withHP o P c.tapes.workTapePos t)
        (hW H o a t).1) = withH o F (c.step a sy mv).tapes.workTapes := by
      funext t
      simp only [withH, withHP, hW]
      cases hp : hPre o t with
      | none => rfl
      | some j =>
        simp only [Config.step, Turing.Action.apply]
        cases (a.workTapes j).1 <;> rfl
    have hP : (fun t => withHP o P c.tapes.workTapePos t + ((hW H o a t).2 : ℤ)) =
        withHP o P (c.step a sy mv).tapes.workTapePos := by
      funext t
      simp only [withHP, hW]
      cases hp : hPre o t with
      | none => simp
      | some j => rfl
    rw [hF, hP]
    simp only [simOrExit, moveInputPos_zero, Option.toList_none, List.append_nil]
    cases hs : a.state with
    | none =>
      have : (c.step a sy mv).tapes.state = none := by simp [Config.step, hs]
      simp only [this, ite_true, exitH]
    | some h' =>
      have : (c.step a sy mv).tapes.state = some h' := by simp [Config.step, hs]
      simp only [this, reduceCtorEq, ite_false, embH, Option.map_some]
      rfl

/-- **The handler phase.** -/
theorem lawR_handler (b s : List Bool) (μ : PMF (Fin (m + 3) → List Bool))
    (hspec : (H o).Runs (layout b [] s) μ)
    (hF : ∀ j, F (hTape o j) = tapeOfList (layout b [] s j)) (hP : ∀ j, P (hTape o j) = 0)
    (N : ℕ)
    (hgood : ∀ ws ∈ μ.support, ∀ g ∈ (lawR H M T w N (mkR (some (qS H T w q fl o .qToEnd)) ip
      (withH o F (fun j => tapeOfList (ws j))) (withHP o P (fun _ => 0)) out)).support,
        g.1.tapes.state = none) :
    lawR H M T w ((H o).time + N) (mkR (some (hS H T w q fl o (H o).machine.initial)) ip F P out) =
      μ.bind (fun ws => lawR H M T w N (mkR (some (qS H T w q fl o .qToEnd)) ip
        (withH o F (fun j => tapeOfList (ws j))) (withHP o P (fun _ => 0)) out)) := by
  have hstart : mkR (some (hS H T w q fl o (H o).machine.initial)) ip F P out =
      simOrExit (embH H T w q fl o ip F P out) (exitH H T w q fl o ip F P out)
        ((H o).startCfg (layout b [] s)) := by
    simp only [simOrExit, Routine.startCfg, wordsCfg_state, reduceCtorEq, ite_false, embH,
      Option.map_some]
    congr 1
    · funext t
      simp only [withH]
      cases hp : hPre o t with
      | none => rfl
      | some j => rw [← hTape_of_hPre hp, hF]; rfl
    · funext t
      simp only [withHP, wordsCfg_workTapePos]
      cases hp : hPre o t with
      | none => rfl
      | some j => rw [← hTape_of_hPre hp, hP]
  -- the exit depends only on the final words, the heads being at the start
  have hexit : ∀ f ∈ ((H o).law (H o).time ((H o).startCfg (layout b [] s))).support,
      exitH H T w q fl o ip F P out f.1 = mkR (some (qS H T w q fl o .qToEnd)) ip
        (withH o F f.1.tapes.workTapes) (withHP o P (fun _ => 0)) out := by
    intro f hf
    simp only [exitH]
    rw [show f.1.tapes.workTapePos = fun _ => 0 from funext (hspec.1 f hf).2]
  have hwords : ∀ f ∈ ((H o).law (H o).time ((H o).startCfg (layout b [] s))).support,
      ∃ ws ∈ μ.support, f.1.tapes.workTapes = fun j => tapeOfList (ws j) := by
    intro f hf
    have : f.1.tapes.workTapes ∈ (μ.map (fun ws i => tapeOfList (ws i))).support := by
      rw [← hspec.2]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨f, hf, rfl⟩
    obtain ⟨ws, hws, he⟩ := (PMF.mem_support_map_iff _ _ _).mp this
    exact ⟨ws, hws, he.symm⟩
  rw [hstart]
  unfold lawR
  rw [law_simExit (H o).machine (machine H M T w)
    (fun e : Fin 0 × List Bool => e.1.elim0) (embH H T w q fl o ip F P out)
    (exitH H T w q fl o ip F P out)
    (fun c hc s => lawR_embH_one H M T w q fl o ip F P out c hc s) N (H o).time _ ()
    (fun f hf => (hspec.1 f hf).1) (by
      intro f hf g hg
      obtain ⟨ws, hws, he⟩ := hwords f hf
      rw [hexit f hf, he] at hg
      exact hgood ws hws g hg)]
  calc ((H o).law (H o).time ((H o).startCfg (layout b [] s))).bind
        (fun f => lawR H M T w N (exitH H T w q fl o ip F P out f.1))
      = ((H o).law (H o).time ((H o).startCfg (layout b [] s))).bind
        (fun f => lawR H M T w N (mkR (some (qS H T w q fl o .qToEnd)) ip
          (withH o F f.1.tapes.workTapes) (withHP o P (fun _ => 0)) out)) := by
        apply Probability.PMF.bind_congr_on_support
        intro f hf
        rw [hexit f hf]
    _ = (((H o).law (H o).time ((H o).startCfg (layout b [] s))).map
          (fun f => f.1.tapes.workTapes)).bind
        (fun tp => lawR H M T w N (mkR (some (qS H T w q fl o .qToEnd)) ip
          (withH o F tp) (withHP o P (fun _ => 0)) out)) := by
        rw [PMF.bind_map]; rfl
    _ = _ := by
        rw [hspec.2, PMF.bind_map]; rfl

end

end SigabaNeo.Inline
