import PE.Impl.DualUse.Prog.Sd3

/-!
# Flipping one bit of a word under a flag, as a block

`cflipP : Prog 10` (tapes `0` output, `1` the word `w`, `2` the flag, templates `3 4 5` of
lengths `P`, `Q`, `P + 1 + Q`; scratch `6 … 9`): the word with its bit `P` flipped if the first bit
of the flag is set (`run_cflipP`, `cflip_eq`). `flipB P L : XProg 11` builds the templates
(`law_flipB`); placed by `vFl` (`plc_flipB'`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Prog
open scoped Prog

def fvA : Fin 5 → Fin 10 := ![6, 0, 8, 9, 3]
def fvB : Fin 5 → Fin 10 := ![6, 0, 8, 9, 4]
theorem fvA_inj : Function.Injective fvA := by decide
theorem fvB_inj : Function.Injective fvB := by decide

/-- **Flip the bit `P` of the word `1` if the flag `2` is set.** -/
def cflipP : Prog 10 :=
  cp 0 5 ⨾ cp 6 1 ⨾ map fvA mvP ⨾ pp 6 7 ⨾ ifBit 2 (ifBit 7 (sin false 0) (sin true 0)) (push 0 7) ⨾
    map fvB mvP ⨾ clr 6 ⨾ clr 7

theorem noGrow_cflipP : cflipP.NoGrow := rfl
theorem wf_cflipP : cflipP.WF := wf_of_wfB (by decide)

/-- The flipped bit. -/
def flipBit (f b : Bool) : Bool := if f then !b else b

theorem run_flipStep {k : ℕ} (T : Store k) (o f b : Fin k) :
    run (ifBit f (ifBit b (sin false o) (sin true o)) (push o b)) T =
      Function.update T o ((T o ++ [flipBit (hd (T f)) (hd (T b))]).tail) := by
  simp only [run_ifBit, run_push]
  cases hf : hd (T f) <;> cases hb : hd (T b) <;> simp [flipBit, hf, hb]

theorem flip_key (T A C : List Bool) (b : Bool) (hT : T.length = A.length + 1 + C.length) :
    (((T ++ A).drop A.length ++ [b]).tail ++ C).drop C.length = A ++ [b] ++ C := by
  rw [← List.drop_one]
  have e1 := drop_append_drop T A [b]
  rw [List.length_singleton] at e1
  rw [e1]
  have e2 := drop_append_drop T (A ++ [b]) C
  rw [List.length_append, List.length_singleton] at e2
  rw [e2, List.drop_left' hT]

set_option maxHeartbeats 1000000 in
theorem run_cflipP (S : Store 10) (hS : ∀ i : Fin 10, 6 ≤ i.val → S i = [])
    (hT : (S 5).length = (S 3).length + 1 + (S 4).length) :
    run cflipP S = Function.update S 0 (takeD (S 3).length (S 1) ++
      [flipBit (hd (S 2)) (hd ((S 1).drop (S 3).length))] ++
      takeD (S 4).length ((S 1).drop (S 3).length).tail) := by
  have hh : ∀ l : List Bool, hd (l.take 1) = hd l := by intro l; cases l <;> rfl
  simp only [cflipP, run_seq, run_copy, run_clear]
  rw [run_mvP_map fvA_inj _ (by simp [fvA, hS]) (by simp [fvA, hS])]
  simp only [run_pop, run_flipStep]
  rw [run_mvP_map fvB_inj _ (by simp [fvA, fvB, hS]) (by simp [fvA, fvB, hS])]
  have key := flip_key (S 5) (takeD (S 3).length (S 1)) (takeD (S 4).length ((S 1).drop (S 3).length).tail)
    (flipBit (hd (S 2)) (hd ((S 1).drop (S 3).length))) (by simp [hT])
  simp only [length_takeD] at key
  funext t
  fin_cases t <;> simp [fvA, fvB, hS, hh] <;> simpa using key

theorem flipAt_split {P : ℕ} {w : List Bool} (hP : P < w.length) :
    flipAt P w = w.take P ++ [!(w.drop P).head!] ++ (w.drop P).tail := by
  obtain ⟨u, v, rfl, hu⟩ : ∃ u v, w = u ++ v ∧ u.length = P := ⟨w.take P, w.drop P, by simp, by simp; omega⟩
  subst hu
  have hv : v ≠ [] := by rintro rfl; simp at hP
  obtain ⟨b, v', rfl⟩ := List.exists_cons_of_ne_nil hv
  have := flipAt_append_right u (b :: v') 0
  rw [Nat.add_zero] at this
  rw [this, flipAt_zero_cons]
  simp

/-- **The value of the flip.** -/
theorem cflip_eq (f : Bool) {P Q : ℕ} {w : List Bool} (hw : w.length = P + 1 + Q) :
    takeD P w ++ [flipBit f (hd (w.drop P))] ++ takeD Q (w.drop P).tail =
      if f then flipAt P w else w := by
  have hP : P < w.length := by omega
  rw [takeD_eq_take (by omega), takeD_of_length' (by simp; omega)]
  have hd' : hd (w.drop P) = (w.drop P).head! := by
    cases h : w.drop P with
    | nil => simp at h; omega
    | cons b v => rfl
  cases f
  · simp only [flipBit, Bool.false_eq_true, ite_false, hd']
    conv_rhs => rw [← List.take_append_drop P w]
    have hne : w.drop P ≠ [] := by simp; omega
    obtain ⟨b, v, hb⟩ := List.exists_cons_of_ne_nil hne
    rw [hb]; simp
  · simp only [flipBit, ite_true, hd']
    rw [flipAt_split hP]

def flU : Fin 10 → Fin 11 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
theorem flU_inj : Function.Injective flU := by decide

/-- **The flip block**: bit `P` of a word of `L` bits. -/
def flipB (P L : ℕ) : XProg 11 :=
  seq (natP 3 10 P) <| seq (natP 4 10 (L - P - 1)) <| seq (natP 5 10 L) <|
  seq (prog (Prog.map flU cflipP)) <| clearL [3, 4, 5]

theorem wf_flipB (P L : ℕ) : (flipB P L).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_progMap flU_inj wf_cflipP, wf_clearL _⟩

set_option maxHeartbeats 1000000 in
theorem law_flipB (P L : ℕ) (S : Store 11) (hS : ∀ i : Fin 11, 3 ≤ i.val → S i = [])
    (hL : (S 1).length = L) (hP : P < L) :
    (flipB P L).law S = PMF.pure (Function.update S 0
      (if hd (S 2) then flipAt P (S 1) else S 1)) := by
  unfold flipB
  rw [XProg.law_seq, law_natP (by decide) _ _ (hS 10 (by decide)), PMF.pure_bind]
  rw [XProg.law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [XProg.law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [XProg.law_seq, law_progMap flU_inj _ noGrow_cflipP _ 0 _ (run_cflipP _
    (fun i hi => by fin_cases i <;> first | (simp at hi; done) | simp [flU, hS])
    (by simp [flU]; omega)), PMF.pure_bind, law_clearL]
  congr 1
  funext t
  fin_cases t <;> simp [flU, hS]
  simpa using cflip_eq (hd (S 2)) (P := P) (Q := L - P - 1) (w := S 1) (by omega)

def timeFlipB (P L M : ℕ) : ℕ :=
  (2 * P + 1) * (4 * M + 12) + (2 * (L - P - 1) + 1) * (4 * M + 12) + (2 * L + 1) * (4 * M + 12) +
    Prog.timeBound cflipP M + ([3, 4, 5].length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem ub_flipB (P L M : ℕ) (hM : P + L ≤ M) : UB (flipB P L) M (timeFlipB P L M) M := by
  have u := (ub_natP (t := (3 : Fin 11)) (c := 10) (by decide) (n := P) (M := M) (by omega)).seq <|
    (ub_natP (t := (4 : Fin 11)) (c := 10) (by decide) (n := L - P - 1) (M := M) (by omega)).seq <|
    (ub_natP (t := (5 : Fin 11)) (c := 10) (by decide) (n := L) (M := M) (by omega)).seq <|
    (ub_progMap flU _ noGrow_cflipP M).seq <| ub_clearL M [3, 4, 5]
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeFlipB, Nat.add_assoc, List.length_cons, List.length_nil]

/-- Output `o`, word `a`, flag `b`; scratch from `20`. -/
def vFl (o a b : Fin 82) (j : Fin 11) : Fin 82 :=
  if j.val = 0 then o else if j.val = 1 then a else if j.val = 2 then b
  else ⟨j.val + 17, by have := j.isLt; omega⟩

theorem vFl_scr (o a b : Fin 82) (i : Fin 11) (hi : 3 ≤ i.val) : 20 ≤ (vFl o a b i).val := by
  unfold vFl; split_ifs <;> (try dsimp only) <;> omega

theorem plc_flipB' (o a b : Fin 82) (h : Function.Injective (vFl o a b)) (P L : ℕ) (S : Store 82)
    (hS : Blank20 S) {W F v : List Bool} (ha : S a = W) (hb : S b = F) (hL : W.length = L)
    (hP : P < L) (hv : (if hd F then flipAt P W else W) = v) :
    (frame ⟨vFl o a b, h⟩ (flipB P L)).law S = PMF.pure (Function.update S o v) := by
  rw [law_frame_upd _ _ S 0 _ (law_flipB P L _ (fun i hi => hS _ (vFl_scr o a b i hi))
    (by show (S a).length = L; rw [ha, hL]) hP)]
  show PMF.pure (Function.update S o (if hd (S b) then flipAt P (S a) else S a)) = _
  rw [ha, hb, hv]

end AdvancedEncryption.DualUse.Prog
