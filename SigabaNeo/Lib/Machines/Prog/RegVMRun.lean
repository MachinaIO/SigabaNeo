import SigabaNeo.Lib.Machines.Prog.RegVM

/-!
# The register machine on tapes: instructions

The tape program of each instruction of `RegVM.Code` and its law on encoded states
(`run_*P`): `run P (enc E σ ctr) = enc E (exec E c σ) ctr`. The scratch tapes `X0`, `X1` hold
intermediate words and `X7` counts the macro loops; all are blank afterwards.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Tape

namespace RegVM

open Prog
open scoped Prog

abbrev X0 : Fin K := tX 0
abbrev X1 : Fin K := tX 1
abbrev X7 : Fin K := tX 7

variable (E : Env) (σ : St) (ctr : Fin nD → List Bool)

/-! ### Scalar instructions -/

def oneP (d : SR) : Prog K := cp (tR d) tN
def zeroP (d : SR) : Prog K := clr (tR d)
def movP (d a : SR) : Prog K := cp (tR d) (tR a)
def subP (d a : SR) : Prog K := dropBy (tR d) (tR a) X7
def incP (d : SR) : Prog K :=
  cp X0 tT ⨾ dropBy X0 (tR d) X7 ⨾ tl X0 ⨾ cp (tR d) tT ⨾ dropBy (tR d) X0 X7 ⨾ clr X0
def addP (d a : SR) : Prog K :=
  cp X0 tT ⨾ dropBy X0 (tR d) X7 ⨾ dropBy X0 (tR a) X7 ⨾ cp (tR d) tT ⨾ dropBy (tR d) X0 X7 ⨾
    clr X0

theorem run_oneP (d : SR) : run (oneP d) (enc E σ ctr) = enc E (exec E (.one d) σ) ctr := by
  rw [exec, enc_sc]; rfl

theorem run_zeroP (d : SR) : run (zeroP d) (enc E σ ctr) = enc E (exec E (.zero d) σ) ctr := by
  rw [exec, enc_sc]; rfl

theorem run_movP (d a : SR) : run (movP d a) (enc E σ ctr) = enc E (exec E (.mov d a) σ) ctr := by
  rw [exec, enc_sc]; simp [movP]

theorem run_subP (d a : SR) : run (subP d a) (enc E σ ctr) = enc E (exec E (.sub d a) σ) ctr := by
  rw [exec, enc_sc, subP, run_dropBy _ _ _ (by simp)]
  simp [enc_upd_X, List.drop_replicate]

theorem run_incP (d : SR) : run (incP d) (enc E σ ctr) = enc E (exec E (.inc d) σ) ctr := by
  rw [exec, enc_sc]
  simp only [incP, run_seq, run_copy, run_tail, run_clear, run_dropBy _ _ _ (by simp : X7 ≠ X0),
    run_dropBy _ _ _ (by simp : X7 ≠ tR d)]
  have e : E.M - (E.M - σ.sc d - 1) = min (σ.sc d + 1) E.M := by omega
  enc_ext <;> simp [List.drop_replicate, e]

theorem run_addP (d a : SR) : run (addP d a) (enc E σ ctr) = enc E (exec E (.add d a) σ) ctr := by
  rw [exec, enc_sc]
  simp only [addP, run_seq, run_copy, run_tail, run_clear, run_dropBy _ _ _ (by simp : X7 ≠ X0),
    run_dropBy _ _ _ (by simp : X7 ≠ tR d)]
  have e : E.M - (E.M - σ.sc d - σ.sc a) = min (σ.sc d + σ.sc a) E.M := by omega
  enc_ext <;> simp [List.drop_replicate, e]

/-! ### Emitting a gate -/

/-- `X1 :=` the emitted position of the register `r`. -/
def fixP (r : SR) : Prog K :=
  cp X0 tT ⨾ dropBy X0 (tR r) X7 ⨾ dropBy X0 tCO X7 ⨾ ifBlank X0 (cp X1 tN) (cp X1 (tR r)) ⨾ clr X0

/-- Shift the unary word of `|X1|` on `W` bits into the output. -/
def emitX1 : Prog K :=
  shiftIn true tOUT X1 X7 ⨾ dropBy tOC X1 X7 ⨾ cp X0 tW ⨾ dropBy X0 X1 X7 ⨾
    shiftIn false tOUT X0 X7 ⨾ dropBy tOC X0 X7 ⨾ clr X0 ⨾ clr X1

/-- Emit the position of the register `r`. -/
def emitP (r : SR) : Prog K := fixP r ⨾ emitX1

theorem run_fixP (r : SR) : run (fixP r) (enc E σ ctr) =
    Function.update (enc E σ ctr) X1 (List.replicate (fixv E σ.t (σ.sc r)) true) := by
  simp only [fixP, run_seq, run_copy, run_clear, run_dropBy _ _ _ (by simp : X7 ≠ X0)]
  rw [run_ifBlank]
  have key : (E.M - σ.sc r - (E.M - (E.n + 1 + σ.t)) = 0) ↔ min (E.n + 1 + σ.t) E.M ≤ σ.sc r := by
    omega
  by_cases hc : min (E.n + 1 + σ.t) E.M ≤ σ.sc r
  · rw [if_pos (by simp [List.drop_replicate]; omega)]
    simp only [fixv, hc, ite_true]
    enc_ext
  · rw [if_neg (by simp [List.drop_replicate]; omega)]
    simp only [fixv, hc, ite_false]
    enc_ext

theorem length_uw' (W j : ℕ) : (uw W j).length = j + (W - j) := by simp [uw]

theorem run_emitX1 (v : ℕ) : run emitX1 (Function.update (enc E σ ctr) X1 (List.replicate v true)) =
    enc E { σ with out := σ.out ++ uw E.W v } ctr := by
  rw [enc_out]
  simp only [emitX1, run_seq, run_copy, run_clear, run_dropBy _ _ _ (by simp : X7 ≠ X0),
    run_dropBy _ _ _ (by simp : X7 ≠ tOC), run_shiftIn _ _ _ _ (by simp : X7 ≠ tOUT)]
  have hout : ((((E.pad ++ σ.out).drop σ.out.length ++ List.replicate v true).drop v ++
      List.replicate (E.W - v) false).drop (E.W - v)) =
      (E.pad ++ (σ.out ++ uw E.W v)).drop (σ.out ++ uw E.W v).length := by
    have h1 : ((E.pad ++ σ.out).drop σ.out.length ++ List.replicate v true).drop v =
        (E.pad ++ (σ.out ++ List.replicate v true)).drop (σ.out.length + v) := by
      simpa using drop_append_drop E.pad σ.out (List.replicate v true)
    have h2 : ((E.pad ++ (σ.out ++ List.replicate v true)).drop (σ.out.length + v) ++
        List.replicate (E.W - v) false).drop (E.W - v) = (E.pad ++ ((σ.out ++ List.replicate v true)
          ++ List.replicate (E.W - v) false)).drop (σ.out.length + v + (E.W - v)) := by
      simpa using drop_append_drop E.pad (σ.out ++ List.replicate v true)
        (List.replicate (E.W - v) false)
    rw [h1, h2]
    simp only [uw, List.append_assoc, List.length_append, List.length_replicate, Nat.add_assoc]
  enc_ext
  all_goals (simp only [length_uw']; omega)

theorem run_emitP (r : SR) : run (emitP r) (enc E σ ctr) =
    enc E { σ with out := σ.out ++ uw E.W (fixv E σ.t (σ.sc r)) } ctr := by
  rw [emitP, run_seq, run_fixP, run_emitX1]

/-- `nand d a b`: emit the two positions, then `d :=` the new gate's position. -/
def nandP (d a b : SR) : Prog K :=
  emitP a ⨾ emitP b ⨾ cp (tR d) tT ⨾ dropBy (tR d) tCO X7 ⨾ tl tCO

theorem run_nandP (d a b : SR) : run (nandP d a b) (enc E σ ctr) =
    enc E (exec E (.nand d a b) σ) ctr := by
  simp only [nandP, run_seq, run_emitP]
  simp only [run_copy, run_tail, run_dropBy _ _ _ (by simp : X7 ≠ tR d)]
  rw [exec]
  have e2 : E.M - (E.M - (E.n + 1 + σ.t)) = min (E.n + 1 + σ.t) E.M := by omega
  enc_ext
  all_goals omega

/-! ### The list encoding -/

/-- The invariant of the list registers and of the source. -/
def Inv (E : Env) (σ : St) : Prop :=
  (∀ l, (σ.ls l).length ≤ E.C ∧ ∀ x ∈ σ.ls l, x ≤ E.M) ∧ ∀ x ∈ σ.src, x ≤ E.W

theorem length_blk {M x : ℕ} (h : x ≤ M) : (blk M x).length = M + 1 := by
  simp [blk, uw]; omega

theorem length_flatten_blk {M : ℕ} : ∀ (L : List ℕ), (∀ x ∈ L, x ≤ M) →
    ((L.map (blk M)).flatten).length = L.length * (M + 1)
  | [], _ => by simp
  | x :: L, h => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    rw [length_blk (h x (by simp)), length_flatten_blk L (fun y hy => h y (by simp [hy]))]
    ring

theorem length_lenc {L : List ℕ} (h1 : L.length ≤ E.C) (h2 : ∀ x ∈ L, x ≤ E.M) :
    (lenc E L).length = E.C * (E.M + 1) := by
  rw [lenc, List.length_append, List.length_replicate, length_flatten_blk L h2, ← Nat.add_mul,
    Nat.sub_add_cancel h1]

theorem lead_replicate_append (b : Bool) (J : ℕ) (w : List Bool) :
    lead b (List.replicate J b ++ w) = J + lead b w := by
  induction J with
  | zero => simp
  | succ J ih => simp [List.replicate_succ, lead, ih]; omega

theorem lead_le_length (b : Bool) : ∀ w : List Bool, lead b w ≤ w.length
  | [] => le_rfl
  | x :: w => by
    unfold lead; split_ifs
    · have := lead_le_length b w; simp; omega
    · simp

theorem min_lead_uw {M x : ℕ} (hx : x ≤ M) (D : List Bool) :
    min M (lead true (uw M x ++ D)) = x := by
  rw [uw, List.append_assoc, lead_replicate_append]
  rcases Nat.lt_or_ge x M with h | h
  · obtain ⟨j, hj⟩ : ∃ j, M - x = j + 1 := ⟨M - x - 1, by omega⟩
    rw [hj, List.replicate_succ]
    simp [lead]; omega
  · have : x = M := by omega
    subst this; omega

theorem lenc_cons (x : ℕ) (L : List ℕ) : lenc E (x :: L) =
    List.replicate ((E.C - (x :: L).length) * (E.M + 1)) false ++ (true :: (uw E.M x ++
      (L.map (blk E.M)).flatten)) := by
  simp [lenc, blk]

theorem lead_false_lenc_cons (x : ℕ) (L : List ℕ) :
    lead false (lenc E (x :: L)) = (E.C - (x :: L).length) * (E.M + 1) := by
  rw [lenc_cons, lead_replicate_append]; simp [lead]

theorem lenc_push {L : List ℕ} {x : ℕ} (hx : x ≤ E.M) (h1 : L.length ≤ E.C)
    (h2 : L.length < E.C ∨ L = []) :
    (lenc E L ++ blk E.M x).drop (E.M + 1) =
      lenc E (if L.length < E.C then L ++ [x] else L) := by
  split_ifs with h
  · obtain ⟨j, hj⟩ : ∃ j, E.C - L.length = j + 1 := ⟨E.C - L.length - 1, by omega⟩
    have hj' : E.C - (L ++ [x]).length = j := by simp; omega
    have e : (E.C - L.length) * (E.M + 1) = (E.M + 1) + j * (E.M + 1) := by rw [hj]; ring
    rw [lenc, lenc, e, hj', List.replicate_add, List.append_assoc, List.append_assoc,
      List.drop_left' (by simp)]
    simp
  · obtain rfl : L = [] := h2.resolve_left h
    have hC : E.C = 0 := by simp at h; omega
    simp only [lenc, hC, List.length_nil, Nat.sub_self, Nat.zero_mul, List.replicate_zero,
      List.map_nil, List.flatten_nil, List.nil_append]
    rw [List.drop_of_length_le (by rw [length_blk hx])]

theorem hd_lenc {L : List ℕ} (h : L.length < E.C) : hd (lenc E L) = false := by
  obtain ⟨j, hj⟩ : ∃ j, E.C - L.length = j + 1 := ⟨E.C - L.length - 1, by omega⟩
  have e : (E.C - L.length) * (E.M + 1) = (j * (E.M + 1) + E.M) + 1 := by rw [hj]; ring
  rw [lenc, e, List.replicate_succ', List.append_assoc]
  rcases j * (E.M + 1) + E.M with _ | m <;> simp [List.replicate_succ]

theorem hd_lenc_cons {x : ℕ} {L : List ℕ} (h : ¬ (x :: L).length < E.C) :
    hd (lenc E (x :: L)) = true := by
  rw [lenc_cons, show E.C - (x :: L).length = 0 by omega]; simp

/-! ### List instructions -/

def lnilP (l : LR) : Prog K := setZero (tL l)
def lmovP (l l' : LR) : Prog K := cp (tL l) (tL l')

theorem run_lnilP (hI : Inv E σ) (l : LR) :
    run (lnilP l) (enc E σ ctr) = enc E (exec E (.lnil l) σ) ctr := by
  rw [exec, enc_ls, lnilP, run_setZero, enc_L, length_lenc E (hI.1 l).1 (hI.1 l).2]
  simp [lenc]

theorem run_lmovP (l l' : LR) :
    run (lmovP l l') (enc E σ ctr) = enc E (exec E (.lmov l l') σ) ctr := by
  rw [exec, enc_ls]; simp [lmovP]

/-- Shift the element `min (s a) M` into the list `l`. -/
def pushBodyP (l : LR) (a : SR) : Prog K :=
  cp X0 tT ⨾ dropBy X0 (tR a) X7 ⨾ cp X1 tT ⨾ dropBy X1 X0 X7 ⨾ sin true (tL l) ⨾
    shiftIn true (tL l) X1 X7 ⨾ cp X0 tT ⨾ dropBy X0 X1 X7 ⨾ shiftIn false (tL l) X0 X7 ⨾ clr X0 ⨾
    clr X1

def lpushP (l : LR) (a : SR) : Prog K := ifBit (tL l) (nop (tL l)) (pushBodyP l a)

theorem shift_blk (w : List Bool) {M x : ℕ} (hx : x ≤ M) :
    (((((w ++ [true]).tail ++ List.replicate x true).drop x) ++ List.replicate (M - x) false).drop
      (M - x)) = (w ++ blk M x).drop (M + 1) := by
  have h0 : (w ++ [true]).tail = (w ++ [true]).drop 1 := List.drop_one.symm
  rw [h0]
  have h1 := drop_append_drop w [true] (List.replicate x true)
  simp only [List.length_replicate, List.length_singleton] at h1
  rw [h1]
  have h2 := drop_append_drop w ([true] ++ List.replicate x true) (List.replicate (M - x) false)
  simp only [List.length_replicate, List.length_append, List.length_singleton] at h2
  rw [h2]
  simp only [blk, uw, List.cons_append, List.singleton_append, List.append_assoc]
  congr 1; omega

theorem run_pushBodyP (l : LR) (a : SR) : run (pushBodyP l a) (enc E σ ctr) =
    Function.update (enc E σ ctr) (tL l)
      ((lenc E (σ.ls l) ++ blk E.M (min (σ.sc a) E.M)).drop (E.M + 1)) := by
  simp only [pushBodyP, run_seq, run_copy, run_clear, run_sin,
    run_dropBy _ _ _ (by simp : X7 ≠ X0), run_dropBy _ _ _ (by simp : X7 ≠ X1),
    run_shiftIn _ _ _ _ (by simp : X7 ≠ tL l)]
  have hm : E.M - (E.M - σ.sc a) = min (σ.sc a) E.M := by omega
  have key := shift_blk (lenc E (σ.ls l)) (min_le_right (σ.sc a) E.M)
  enc_ext

theorem run_lpushP (hI : Inv E σ) (l : LR) (a : SR) :
    run (lpushP l a) (enc E σ ctr) = enc E (exec E (.lpush l a) σ) ctr := by
  rw [exec, enc_ls, lpushP, run_ifBit, enc_L]
  have h1 := (hI.1 l).1
  by_cases hh : hd (lenc E (σ.ls l)) = true
  · rw [if_pos hh, run_nop]
    have : ¬ (σ.ls l).length < E.C := fun h => by
      rw [hd_lenc E h] at hh; exact absurd hh (by simp)
    rw [if_neg this]
    symm; exact Function.update_eq_self_iff.mpr (enc_L E σ ctr l).symm
  · rw [if_neg hh, run_pushBodyP, lenc_push E (min_le_right _ _) h1]
    by_cases hc : (σ.ls l).length < E.C
    · exact Or.inl hc
    · right
      rcases hL : σ.ls l with _ | ⟨y, L⟩
      · rfl
      · rw [hL] at hc hh; exact absurd (hd_lenc_cons E hc) hh

/-- Pop the first element of `l` into `d`. -/
def lpopP (d : SR) (l : LR) : Prog K :=
  cp X0 (tL l) ⨾ skipZ X0 (tL l) X7 ⨾ tl X0 ⨾ cp X1 tT ⨾ countOnes X0 X1 tT X7 ⨾ cp (tR d) tT ⨾
    dropBy (tR d) X1 X7 ⨾ dropBy X0 X1 X7 ⨾ clr X1 ⨾ setZero (tL l) ⨾ moveBits (tL l) X0 X7

theorem lenc_nil : lenc E [] = List.replicate (E.C * (E.M + 1)) false := by simp [lenc]

theorem lead_replicate (b : Bool) (n : ℕ) : lead b (List.replicate n b) = n := by
  simpa using lead_replicate_append b n []

theorem run_lpopP (hI : Inv E σ) (d : SR) (l : LR) :
    run (lpopP d l) (enc E σ ctr) = enc E (exec E (.lpop d l) σ) ctr := by
  rw [exec, enc_sc_ls]
  have hC := (hI.1 l).1
  have hM := (hI.1 l).2
  simp only [lpopP, run_seq, run_copy, run_clear, run_tail, run_setZero,
    run_skipZ _ _ _ (by simp : X7 ≠ X0), run_countOnes _ _ _ _ (by simp : X7 ≠ X0)
      (by simp : X7 ≠ X1) (by simp : X0 ≠ X1),
    run_dropBy _ _ _ (by simp : X7 ≠ tR d), run_dropBy _ _ _ (by simp : X7 ≠ X0),
    run_moveBits _ _ _ (by simp : X7 ≠ tL l) (by simp : X7 ≠ X0) (by simp : tL l ≠ X0)]
  rcases hL : σ.ls l with _ | ⟨x, rest⟩
  · rw [hL] at hC
    have e1 : lead false (lenc E []) = (lenc E []).length := by rw [lenc_nil, lead_replicate]; simp
    have e2 : min (lenc E []).length (lenc E []).length = (lenc E []).length := min_self _
    enc_ext0
    all_goals (simp only [hL, e1, e2, List.drop_length, lead_replicate, min_self, Nat.zero_min,
      Nat.sub_zero, List.tail_nil, lead_nil, List.drop_nil,
      Nat.min_zero, List.drop_zero, List.length_replicate, List.drop_replicate, Nat.sub_self,
      List.replicate_zero, List.headD_nil, List.tail_nil, List.append_nil, List.length_nil,
      lenc_nil])
  · rw [hL] at hC hM
    have hx : x ≤ E.M := hM x (by simp)
    have hr : ∀ y ∈ rest, y ≤ E.M := fun y hy => hM y (by simp [hy])
    obtain ⟨D, hD⟩ : ∃ D, D = (rest.map (blk E.M)).flatten := ⟨_, rfl⟩
    have e1 : (lenc E (x :: rest)).drop (min (lenc E (x :: rest)).length
        (lead false (lenc E (x :: rest)))) = true :: (uw E.M x ++ D) := by
      rw [lead_false_lenc_cons, min_eq_right (by rw [lenc_cons]; simp), lenc_cons,
        List.drop_left' (by simp), hD]
    have e2 : min (List.replicate E.M true).length (lead true (uw E.M x ++ D)) = x := by
      rw [List.length_replicate]; exact min_lead_uw hx D
    have e3 : (uw E.M x ++ D).drop x = List.replicate (E.M - x) false ++ D := by
      simp [uw, List.append_assoc]
    have e4 : (List.replicate (E.M - x) false ++ D).drop (List.replicate E.M true |>.drop x).length
        = D := List.drop_left' (by simp)
    have e5 : (List.replicate ((lenc E (x :: rest)).length) false ++ D).drop D.length =
        lenc E rest := by
      rw [length_lenc E hC hM, hD, length_flatten_blk rest hr]
      have : E.C * (E.M + 1) = rest.length * (E.M + 1) + (E.C - rest.length) * (E.M + 1) := by
        simp at hC; rw [← Nat.add_mul]; congr 1; omega
      rw [this, List.replicate_add, List.append_assoc, List.drop_left' (by simp)]
      simp [lenc]
    have e6 : (List.replicate E.M true).drop (List.replicate E.M true |>.drop x).length =
        List.replicate x true := by simp [List.drop_replicate]; omega
    enc_ext0
    all_goals (simp only [hL, e1, List.tail_cons, e2, e3, e4, e5, e6, List.headD_cons])

/-! ### Reading the source -/

/-- `d :=` the next value of the source. -/
def rdsrcP (d : SR) : Prog K :=
  cp X0 tSRC ⨾ cp X1 tT ⨾ countOnes X0 X1 tW X7 ⨾ cp (tR d) tT ⨾ dropBy (tR d) X1 X7 ⨾
    dropBy tSRC tW X7 ⨾ clr X0 ⨾ clr X1

theorem run_rdsrcP (hI : Inv E σ) (hWM : E.W ≤ E.M) (d : SR) :
    run (rdsrcP d) (enc E σ ctr) = enc E (exec E (.rdsrc d) σ) ctr := by
  rw [exec, enc_sc_src]
  simp only [rdsrcP, run_seq, run_copy, run_clear,
    run_countOnes _ _ _ _ (by simp : X7 ≠ X0) (by simp : X7 ≠ X1) (by simp : X0 ≠ X1),
    run_dropBy _ _ _ (by simp : X7 ≠ tR d), run_dropBy _ _ _ (by simp : X7 ≠ tSRC)]
  rcases hS : σ.src with _ | ⟨x, rest⟩
  · enc_ext0
    all_goals (simp [hS, senc, List.drop_replicate])
  · have hx : x ≤ E.W := hI.2 x (by simp [hS])
    have e1 : min (List.replicate E.W true).length (lead true (uw E.W x ++ senc E rest)) = x := by
      rw [List.length_replicate]; exact min_lead_uw hx _
    have e2 : (List.replicate E.M true).drop
        ((List.replicate E.M true).drop x).length = List.replicate x true := by
      simp [List.drop_replicate]; omega
    have e3 : (uw E.W x ++ senc E rest).drop (List.replicate E.W true).length = senc E rest := by
      rw [List.length_replicate, List.drop_left' (length_uw hx)]
    have e4 : senc E (x :: rest) = uw E.W x ++ senc E rest := by simp [senc]
    enc_ext0
    all_goals (simp only [hS, e4, e1, e2, e3, List.headD_cons, List.tail_cons])

/-! ### Branching -/

/-- `X0 :=` `|b| - |a|`, cleared before the branch. -/
def ltTestP (a b : SR) : Prog K := cp X0 (tR b) ⨾ dropBy X0 (tR a) X7

theorem run_ltTestP (a b : SR) : run (ltTestP a b) (enc E σ ctr) =
    Function.update (enc E σ ctr) X0 (List.replicate (σ.sc b - σ.sc a) true) := by
  simp only [ltTestP, run_seq, run_copy, run_dropBy _ _ _ (by simp : X7 ≠ X0)]
  enc_ext <;> simp [List.drop_replicate]

end RegVM

end SigabaNeo.Tape
