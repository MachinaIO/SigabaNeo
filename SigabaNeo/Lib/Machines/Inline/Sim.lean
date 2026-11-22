import SigabaNeo.Lib.Machines.Inline.Handler

/-!
# Inlining an oracle handler: the simulation relation

`embA c fl s n` is the configuration of the inlined machine that simulates the configuration `c` of
the oracle machine, with flags `fl`, the encoded handler state `s` on `st` and `n` steps left on
the clock: the query buffer of `o` on `qry o` with the head at its end, the answer of `o` on
`ans o` with the head at the answer head (at `0` while the answer is empty).

* `embA_step`: a simulated ordinary step is one ordinary step of the oracle machine;
* `FlagOK`, `FlagOK.step`: the flags tell the side of the answer when the head reads a blank;
* `lawR_query`: a query on `o` is answered, within explicit time, by the law of the handler.
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {SA : Type} (H : Fin ops → Routine (m + 3))
  (M : MultiTapePTM kA Bool SA (Fin ops)) (T : ℕ) (w : List Bool) {x : List Bool}

/-- The tapes simulating a configuration of the oracle machine. -/
def frameF (c : Config kA Bool SA (Fin ops) x) (s : List Bool) : Tape kA ops m → ℤ → Option Bool
  | .work i => c.tapes.workTapes i
  | .qry o => tapeOfList (c.channels o).queryBuffer
  | .ans o => tapeOfList (c.channels o).answer
  | .clock => tapeOfList (List.replicate T true)
  | .st => tapeOfList s
  | .scr _ => fun _ => none

/-- The heads simulating a configuration of the oracle machine, `n` steps left on the clock. -/
def frameP (c : Config kA Bool SA (Fin ops) x) (n : ℕ) : Tape kA ops m → ℤ
  | .work i => c.tapes.workTapePos i
  | .qry o => (c.channels o).queryBuffer.length
  | .ans o => if (c.channels o).answer = [] then 0 else (c.channels o).answerPos
  | .clock => (n : ℤ) - 1
  | .st => 0
  | .scr _ => 0

/-- **The simulation relation.** -/
def embA (c : Config kA Bool SA (Fin ops) x) (fl : Fin ops → AFlag) (s : List Bool) (n : ℕ) :
    Config (nTapes kA ops m) Bool (RState SA H T w) (Fin 0) x :=
  mkR (c.tapes.state.map fun q => simS H T w q fl) c.tapes.inputPos (frameF T c s) (frameP c n)
    c.tapes.output

/-- The answer symbol read on the simulating tape is the one the oracle machine reads. -/
theorem answer_read (a : List Bool) (p : ℤ) :
    tapeOfList a (if a = [] then 0 else p) = ({ answer := a, answerPos := p } : Channel Bool).answerSymbol := by
  simp only [Channel.answerSymbol]
  by_cases ha : a = []
  · subst ha; simp
  · rw [ite_eq_right ha]
    rcases p with p | p
    · simp
    · simp

theorem answer_read' (ch : Channel Bool) :
    tapeOfList ch.answer (if ch.answer = [] then 0 else ch.answerPos) = ch.answerSymbol :=
  answer_read ch.answer ch.answerPos

/-- The flags are correct: `empty` exactly on empty answers, and on a blank cell the flag of a
nonempty answer tells on which side of it the head is. -/
def FlagOK (c : Config kA Bool SA (Fin ops) x) (fl : Fin ops → AFlag) : Prop :=
  ∀ o, (fl o = .empty ↔ (c.channels o).answer = []) ∧
    ((c.channels o).answer ≠ [] → tapeOfList (c.channels o).answer (c.channels o).answerPos = none →
      (fl o = .left ↔ (c.channels o).answerPos < 0))

/-- The flag of one channel after a simulated step. -/
def newFl1 (f : AFlag) (r : Option Bool) (d : SignType) : AFlag :=
  match f with
  | .empty => .empty
  | g => if r = none then g else if d = -1 then .left else .right

theorem newFl_eq (fl : Fin ops → AFlag) (rd : Fin ops → Option Bool) (mv : Fin ops → SignType)
    (o : Fin ops) : newFl fl rd mv o = newFl1 (fl o) (rd o) (mv o) := by
  unfold newFl newFl1; cases fl o <;> rfl

theorem flag_step (f : AFlag) (a : List Bool) (p : ℤ) (d : SignType)
    (he : f = .empty ↔ a = []) (hs : a ≠ [] → tapeOfList a p = none → (f = .left ↔ p < 0)) :
    (newFl1 f (tapeOfList a (if a = [] then 0 else p)) d = .empty ↔ a = []) ∧
      (a ≠ [] → tapeOfList a (p + d) = none →
        (newFl1 f (tapeOfList a (if a = [] then 0 else p)) d = .left ↔ p + d < 0)) := by
  have hlen : a = [] ∨ 0 < a.length := by cases a <;> simp
  rcases d with _ | _ | _ <;> rcases f with _ | _ | _ <;>
    by_cases hr : tapeOfList a p = none <;>
    simp_all [newFl1, tapeOfList_eq_none_iff] <;> (try split_ifs) <;> (try simp_all) <;> omega

/-- The flags after a simulated step are correct. -/
theorem FlagOK.step {c : Config kA Bool SA (Fin ops) x} {fl : Fin ops → AFlag} (h : FlagOK c fl)
    (act : Turing.Action kA Bool SA) (sy : Fin ops → Option Bool) (mv : Fin ops → SignType) :
    FlagOK (c.step act sy mv) (newFl fl (fun o => tapeOfList (c.channels o).answer
      (if (c.channels o).answer = [] then 0 else (c.channels o).answerPos)) mv) := by
  intro o
  simp only [Config.step, newFl_eq]
  exact flag_step (fl o) _ _ (mv o) (h o).1 (h o).2

/-- **A simulated ordinary step** is one ordinary step of the oracle machine. -/
theorem embA_step (qq : Option (RState SA H T w)) (c : Config kA Bool SA (Fin ops) x)
    (fl : Fin ops → AFlag)
    (hfl : ∀ o, fl o = .empty ↔ (c.channels o).answer = []) (s : List Bool) (n : ℕ)
    (act : Turing.Action kA Bool SA) (sy : Fin ops → Option Bool) (mv : Fin ops → SignType)
    (fl' : Fin ops → AFlag) :
    (mkR qq c.tapes.inputPos (frameF T c s) (frameP c (n + 1)) c.tapes.output).step
        (mkAct act.inputTape (simW fl act sy mv) act.output
          (act.state.map fun q' => simS H T w q' fl')) (fun _ => none) (fun _ => 0) =
      embA H T w (c.step act sy mv) fl' s n := by
  rw [step_mkR]
  unfold embA
  congr 1
  · funext t
    rcases t with i | o | o | _ | _ | j <;> simp only [frameF, frameP, simW, Config.step,
      Turing.Action.apply, wr_none]
    · cases (act.workTapes i).1 <;> rfl
    · cases sy o with
      | none => simp
      | some b => simp [wr, tapeOfList_append_single]
  · funext t
    rcases t with i | o | o | _ | _ | j <;> simp only [frameP, simW, Config.step,
      Turing.Action.apply]
    · cases sy o with
      | none => simp
      | some b => simp
    · by_cases ha : (c.channels o).answer = []
      · simp [ha, (hfl o).mpr ha]
      · have : fl o ≠ .empty := fun h => ha ((hfl o).mp h)
        simp [ha, this]
    · simp; ring
    · simp
    · simp

@[simp] theorem layout_zero (b a s : List Bool) : layout (m := m) b a s 0 = b := by
  simp [layout]

@[simp] theorem layout_one (b a s : List Bool) : layout (m := m) b a s 1 = a := by
  simp [layout]

@[simp] theorem layout_two (b a s : List Bool) : layout (m := m) b a s 2 = s := by
  simp [layout, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)]

@[simp] theorem layout_scr (b a s : List Bool) (j : Fin m) :
    layout (m := m) b a s ⟨j.val + 3, by omega⟩ = [] := by
  simp [layout]

/-- The configuration after a query is the simulation of the configuration that received the
answer. -/
theorem after_query (c : Config kA Bool SA (Fin ops) x) (fl : Fin ops → AFlag) (n : ℕ)
    (o : Fin ops) (nx : SA) (ws a s' : List Bool) :
    mkR (some (simS H T w nx (Function.update fl o
        (if withH o (Function.update (frameF (m := m) T c ws) (Tape.ans o) (fun _ => none))
            (fun j => tapeOfList (layout (c.channels o).queryBuffer a s' j)) (.ans o)
            (withHP o (Function.update (Function.update (frameP (m := m) c n) (Tape.ans o) 0)
              (Tape.qry o) 0) (fun _ => 0) (.ans o)) = none then .empty else .right))))
      c.tapes.inputPos
      (Function.update (withH o (Function.update (frameF (m := m) T c ws) (Tape.ans o) (fun _ => none))
        (fun j => tapeOfList (layout (c.channels o).queryBuffer a s' j))) (.qry o) (fun _ => none))
      (Function.update (withHP o (Function.update (Function.update (frameP (m := m) c n) (Tape.ans o) 0)
        (Tape.qry o) 0) (fun _ => 0)) (.qry o) 0)
      c.tapes.output =
    embA H T w (c.receive o nx a) (Function.update fl o (if a = [] then .empty else .right)) s' n := by
  have hans : withH o (Function.update (frameF (m := m) T c ws) (Tape.ans o) (fun _ => none))
      (fun j => tapeOfList (layout (c.channels o).queryBuffer a s' j)) (.ans o) = tapeOfList a := by
    simp [withH, hPre]
  have hansP : withHP o (Function.update (Function.update (frameP (m := m) c n) (Tape.ans o) 0)
      (Tape.qry o) 0) (fun _ => (0 : ℤ)) (.ans o) = 0 := by
    simp [withHP, hPre]
  rw [hans, hansP, tapeOfList_zero]
  unfold embA
  congr 1
  · simp only [Config.receive, Option.map_some]
    congr 3
    cases a <;> simp
  · funext t
    rcases t with i | o' | o' | _ | _ | j
    · simp [withH, hPre, frameF, Config.receive]
    · by_cases h : o' = o
      · subst h; simp [Config.receive, frameF]
      · simp [withH, hPre, frameF, Config.receive, h]
    · by_cases h : o' = o
      · subst h; simp [withH, hPre, frameF, Config.receive, layout]
      · simp [withH, hPre, frameF, Config.receive, h]
    · simp [withH, hPre, frameF]
    · simp [withH, hPre, frameF]
    · simp [withH, hPre, frameF]
  · funext t
    rcases t with i | o' | o' | _ | _ | j
    · simp [withHP, hPre, frameP, Config.receive]
    · by_cases h : o' = o
      · subst h; simp [Config.receive, frameP]
      · simp [withHP, hPre, frameP, Config.receive, h]
    · by_cases h : o' = o
      · subst h; simp [withHP, hPre, frameP, Config.receive]
      · simp [withHP, hPre, frameP, Config.receive, h]
    · simp [withHP, hPre, frameP]
    · simp [withHP, hPre, frameP]
    · simp [withHP, hPre, frameP]

/-- **A query** on `o` with next state `nx`, from the configuration `c` that submits it, is answered
within `|p| + 2 |a| + 3 |b| + 7 + time` steps (`p` the answer head, `a` the old answer, `b` the
query) by the law of the handler, after which the simulation resumes from `c` having received the
answer. -/
theorem lawR_query {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (s : σ) (c : Config kA Bool SA (Fin ops) x) (fl : Fin ops → AFlag)
    (n : ℕ) (o : Fin ops) (nx : SA) (hfl : FlagOK c fl)
    (hspec : (H o).Runs (layout (c.channels o).queryBuffer [] (enc s))
      ((oracle (o, (c.channels o).queryBuffer) s).map
        (fun r => layout (c.channels o).queryBuffer r.1 (enc r.2)))) :
    ∃ j ≤ (if (c.channels o).answer = [] then 0 else (c.channels o).answerPos.natAbs) +
        2 * (c.channels o).answer.length + 3 * (c.channels o).queryBuffer.length + 7 + (H o).time,
      ∀ N, (∀ r ∈ (oracle (o, (c.channels o).queryBuffer) s).support,
        ∀ g ∈ (lawR H M T w N (embA H T w (c.receive o nx r.1)
          (Function.update fl o (if r.1 = [] then .empty else .right)) (enc r.2) n)).support,
          g.1.tapes.state = none) →
      lawR H M T w (j + N) (mkR (some (qS H T w nx fl o .cleanStart)) c.tapes.inputPos
          (frameF T c (enc s)) (frameP c n) c.tapes.output) =
        (oracle (o, (c.channels o).queryBuffer) s).bind (fun r => lawR H M T w N
          (embA H T w (c.receive o nx r.1)
            (Function.update fl o (if r.1 = [] then .empty else .right)) (enc r.2) n)) := by
  obtain ⟨jc, hjc, hclean⟩ := lawR_clean H M T w nx fl o c.tapes.inputPos (frameF T c (enc s))
    (frameP c n) c.tapes.output (c.channels o).answer (c.channels o).answerPos rfl rfl
    (hfl o).1 (hfl o).2
  set b := (c.channels o).queryBuffer with hb
  refine ⟨jc + (b.length + 2 + ((H o).time + (2 * b.length + 2))), by omega, fun N hgood => ?_⟩
  rw [show jc + (b.length + 2 + ((H o).time + (2 * b.length + 2))) + N =
    jc + (b.length + 2 + ((H o).time + (2 * b.length + 2 + N))) by omega, hclean]
  rw [lawR_rewind H M T w nx fl o _ _ _ _ b (by simp [frameF, hb]) (by simp [frameP, hb])]
  have key : ∀ r : List Bool × σ, lawR H M T w (2 * b.length + 2 + N)
      (mkR (some (qS H T w nx fl o .qToEnd)) c.tapes.inputPos
        (withH o (Function.update (frameF T c (enc s)) (Tape.ans o) (fun _ => none))
          (fun j => tapeOfList (layout b r.1 (enc r.2) j)))
        (withHP o (Function.update (Function.update (frameP c n) (Tape.ans o) 0) (Tape.qry o) 0)
          (fun _ => 0)) c.tapes.output) =
      lawR H M T w N (embA H T w (c.receive o nx r.1)
        (Function.update fl o (if r.1 = [] then .empty else .right)) (enc r.2) n) := by
    intro r
    rw [lawR_eraseQuery H M T w nx fl o _ _ _ _ b (by simp [withH, hPre])
      (by simp [withHP, hPre])]
    exact congrArg _ (after_query H T w c fl n o nx (enc s) r.1 (enc r.2))
  have hF : ∀ j, Function.update (frameF (m := m) T c (enc s)) (Tape.ans o) (fun _ => none)
      (hTape o j) =
      tapeOfList (layout b [] (enc s) j) := by
    intro j
    unfold hTape layout
    split_ifs with h0 h1 h2 <;> simp [frameF, hb]
  have hP : ∀ j, Function.update (Function.update (frameP (m := m) c n) (Tape.ans o) 0)
      (Tape.qry o) 0
      (hTape o j) = 0 := by
    intro j
    unfold hTape
    split_ifs with h0 h1 h2 <;> simp [frameP]
  rw [lawR_handler H M T w nx fl o _ _ _ _ b (enc s) _ hspec hF hP _ (by
    intro ws hws g hg
    obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hws
    rw [key r] at hg
    exact hgood r hr g hg)]
  rw [PMF.bind_map]
  congr 1
  funext r
  exact key r

end SigabaNeo.Inline
