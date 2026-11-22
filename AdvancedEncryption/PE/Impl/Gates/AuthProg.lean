import PE.Impl.Gates.AuthGen
import SigabaNeo.Lib.Machines.Prog.Lookup

/-!
# The authorization test as a tape program

`authMain : Prog 40` computes `winAuth C x` (whether some window with predicate `C` accepts the
date `x`) from `C` on tape `0` and `encDate x` on tape `1`, leaving `[winAuth C x]` alone on
tape `0`. It runs through the valid dates `a` in order (`validL`, a literal list) and, for each,
through the valid dates `b ≥ a`, noting whether `x` has been met since `a`; for a pair with
`a ≤ x ≤ b` it writes the predicate `pairWord (a, b)` (`genPred`) and compares it with `C`.
-/

namespace AdvancedEncryption.PE.Gates.DateWindow

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.GateGen
  AdvancedEncryption.PE.DateWindow
open scoped Prog

/-! ### Helpers -/

/-- The `n` first bits of `src` appended to `dst`, dropped from `src` (through `Z`). -/
def takeN (src dst : Fin 40) : ℕ → Prog 40
  | 0 => prim (.copy dst dst)
  | n + 1 => takeN src dst n ⨾ pp src Z ⨾ prim (.snocHead dst Z)

theorem run_takeN {src dst : Fin 40} (h1 : src ≠ dst) (h2 : src ≠ Z) (h3 : dst ≠ Z) :
    ∀ (n : ℕ) (s : Store 40), ∃ z, run (takeN src dst n) s =
      Function.update (Function.update (Function.update s dst (s dst ++ (s src).take n)) src
        ((s src).drop n)) Z z
  | 0, s => ⟨s Z, by funext t; simp [takeN, Function.update_apply]; split_ifs <;> simp_all⟩
  | n + 1, s => by
    obtain ⟨z, hz⟩ := run_takeN h1 h2 h3 n s
    refine ⟨((s src).drop n).take 1, ?_⟩
    rw [takeN, run_seq, run_seq, hz, run_pop, run_prim]
    funext t
    simp only [Prim.apply, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [List.take_add, List.tail_drop, List.append_assoc]

/-- `dst :=` the first `10` bits of `src`, dropped from `src`. -/
def take10 (src dst : Fin 40) : Prog 40 := clr dst ⨾ takeN src dst 10 ⨾ clr Z

theorem run_take10 {src dst : Fin 40} (h1 : src ≠ dst) (h2 : src ≠ Z) (h3 : dst ≠ Z)
    (s : Store 40) : run (take10 src dst) s =
      Function.update (Function.update (Function.update s dst ((s src).take 10)) src
        ((s src).drop 10)) Z [] := by
  obtain ⟨z, hz⟩ := run_takeN h1 h2 h3 10 (run (clr dst) s)
  rw [take10, run_seq, run_seq, hz, run_clear]
  funext t
  simp only [run_clear, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- Reverse the first `n` bits of tape `1` onto tape `24`. -/
def revN : ℕ → Prog 40
  | 0 => prim (.copy 24 24)
  | n + 1 => revN n ⨾ pp 1 Z ⨾ prim (.consHead 24 Z)

theorem run_revN : ∀ (n : ℕ) (s : Store 40), ∃ z, run (revN n) s =
    Function.update (Function.update (Function.update s 24 (((s 1).take n).reverse ++ s 24)) 1
      ((s 1).drop n)) Z z
  | 0, s => ⟨s Z, by funext t; simp [revN, Function.update_apply]; split_ifs <;> simp_all⟩
  | n + 1, s => by
    obtain ⟨z, hz⟩ := run_revN n s
    refine ⟨((s 1).drop n).take 1, ?_⟩
    rw [revN, run_seq, run_seq, hz, run_pop, run_prim]
    funext t
    simp only [Prim.apply, Function.update_apply, GateGen.Z]
    have e1 : ∀ l : List Bool, (l.take 1).reverse = l.take 1 := fun l => by cases l <;> simp
    split_ifs <;> simp_all [List.take_add, List.tail_drop, List.append_assoc, List.reverse_append, e1]

/-- Clear the tapes of a list. -/
def clearList : List (Fin 40) → Prog 40
  | [] => prim (.copy 0 0)
  | t :: l => clr t ⨾ clearList l

theorem run_clearList : ∀ (l : List (Fin 40)) (s : Store 40),
    run (clearList l) s = fun t => if t ∈ l then [] else s t
  | [], s => by funext t; simp [clearList, Prim.apply]
  | t :: l, s => by
    rw [clearList, run_seq, run_clearList l]
    funext u
    simp only [run_clear, Function.update_apply, List.mem_cons]
    by_cases h1 : u = t <;> by_cases h2 : u ∈ l <;> simp [h1, h2]

/-- Doing nothing. -/
abbrev nopP : Prog 40 := prim (.copy 0 0)

@[simp] theorem run_nopP (s : Store 40) : run nopP s = s := by simp [Prim.apply]

/-! ### The program -/

/-- The valid dates, in order. -/
def validL : List Date := allDates.filter valid

/-- A list of dates as a word: each date reversed (least significant bit first). -/
def flatW (l : List Date) : List Bool := l.flatMap fun d => (encDate d).reverse

/-- The tapes of the generator, cleared after each predicate. -/
def genL : List (Fin 40) :=
  [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27, 29]

/-- Write `pairWord (a, b)` and compare it with `C`; set the flag `34` if equal. -/
def genCmp : Prog 40 :=
  cp 26 32 ⨾ cp 27 33 ⨾ genPred ⨾ prim (.eq O 0 Z) ⨾ ifBit Z (putW 34 [true]) nopP ⨾ clearList genL

/-- One `b`: read it, note whether it is `x`, compare when `x` was met. -/
def innerBody : Prog 40 :=
  (take10 31 33 ⨾ prim (.eq 33 24 Z) ⨾ ifBit Z (putW 35 [true]) nopP ⨾ clr Z) ⨾
    ifBlank 33 nopP (ifBit 35 genCmp nopP) ⨾ clr 33

/-- One `a`: the `b` from `a` on. -/
def outerBody : Prog 40 :=
  (cp 37 36 ⨾ cp 31 30 ⨾ take10 30 32 ⨾ prim (.tail 36) ⨾ putW 35 [false]) ⨾
    forN 39 37 innerBody ⨾ clearList [31, 32, 35, 37]

/-- The tapes `1 … 39`. -/
def allButZero : List (Fin 40) := (List.finRange 40).filter fun t => t ≠ 0

/-- **The authorization test**: `C` on tape `0`, `encDate x` on tape `1`. -/
def authMain : Prog 40 :=
  (clr 24 ⨾ revN 10 ⨾ clr Z ⨾ putW 30 (flatW validL) ⨾
    putW 36 (List.replicate validL.length true) ⨾ putW 34 [false]) ⨾ forN 38 36 outerBody ⨾
    cp 0 34 ⨾ clearList allButZero

/-! ### What it computes -/

section Spec

variable (C : List Bool) (x : Date)

/-- The pairs `(a, b)` with `b` from the list (`got`: `x` was met since `a`). -/
def innerV (a : Date) : Bool → List Date → Bool
  | _, [] => false
  | got, b :: bs => ((got || decide (b = x)) && decide (pairWord (a, b) = C)) ||
      innerV a (got || decide (b = x)) bs

/-- All pairs `a ≤ b` of the list. -/
def outerV : List Date → Bool
  | [] => false
  | a :: as => innerV C x a false (a :: as) || outerV as

end Spec

/-! ### One comparison -/

theorem R_mem_genL {j : ℕ} (hj : j < 16) : GateGen.R j ∈ genL := by
  interval_cases j <;> decide

theorem predTapes_genL {u : Fin 40} (h : predTapes u) : u ∈ genL := by
  rcases h with (h | h | ⟨j, -, hj, rfl⟩ | h) | h
  · rcases h with h | h | h | h | h <;> subst h <;> decide
  · subst h; decide
  · exact R_mem_genL hj
  · simp [winD, validD, eqD, DExp.srcs] at h; rcases h with h | h <;> subst h <;> decide
  · subst h; decide

theorem run_genCmp (S : Store 40) (a b : Date) (h32 : S 32 = (encDate a).reverse)
    (h33 : S 33 = (encDate b).reverse) (hgen : ∀ t ∈ genL, S t = []) :
    run genCmp S = Function.update S 34 (if pairWord (a, b) = S 0 then [true] else S 34) := by
  set S1 := run (cp 27 33) (run (cp 26 32) S)
  have h26 : S1 26 = (encDate a).reverse := by simp [S1, h32]
  have h27 : S1 27 = (encDate b).reverse := by simp [S1, h33]
  obtain ⟨hO, hf⟩ := run_genPred a b S1 h26 h27
  set S2 := run genPred S1
  have hS2 : ∀ t, t ∉ genL → S2 t = S t := fun t ht => by
    rw [hf t (fun hp => ht (predTapes_genL hp))]
    have h1 : t ≠ 26 := fun e => ht (by subst e; decide)
    have h2 : t ≠ 27 := fun e => ht (by subst e; decide)
    simp [S1, Function.update_of_ne h1, Function.update_of_ne h2]
  have h0 : S2 0 = S 0 := hS2 0 (by decide)
  have erun : run genCmp S = run (clearList genL) (run (ifBit Z (putW 34 [true]) nopP)
      (run (prim (.eq O 0 Z)) S2)) := rfl
  rw [erun, run_clearList]
  funext t
  have hZ : t ∉ genL → t ≠ Z := fun ht e => ht (by rw [e]; decide)
  by_cases ht : t ∈ genL
  · have h34 : t ≠ 34 := fun e => by rw [e] at ht; revert ht; decide
    rw [if_pos ht, Function.update_of_ne h34, hgen t ht]
  · rw [if_neg ht]
    simp only [run_ifBit, run_prim, Prim.apply, Function.update_self, hd_cons, hO, h0]
    by_cases hpw : pairWord (a, b) = S 0
    · simp only [hpw, decide_true, ↓reduceIte, run_putW, Function.update_apply]
      split_ifs with h34 hz
      · rfl
      · exact absurd hz (hZ ht)
      · exact hS2 t ht
    · have hZ' := hZ ht
      have h34 : S2 34 = S 34 := hS2 34 (by decide)
      have hSt := hS2 t ht
      simp only [hpw, decide_false, Bool.false_eq_true, ↓reduceIte, run_prim, Prim.apply,
        Function.update_apply]
      split_ifs <;> simp_all

/-! ### The loop stores -/

/-- The store between two `a`: the query, `x` reversed, the remaining dates, their count, the
flag. -/
def Gout (C xr : List Bool) (F : Bool) (rest : List Date) : Store 40 := fun t =>
  if t = 0 then C else if t = 24 then xr else if t = 30 then flatW rest
  else if t = 36 then List.replicate rest.length true else if t = 34 then [F] else []

/-- The store between two `b`: also `a`, the remaining `b`, whether `x` was met, the count of
`a :: rest` and the outer counter. -/
def Gin (C xr : List Bool) (F got : Bool) (a : Date) (rest bs : List Date) (w38 : List Bool) :
    Store 40 := fun t =>
  if t = 32 then (encDate a).reverse else if t = 31 then flatW bs else if t = 35 then [got]
  else if t = 37 then List.replicate (rest.length + 1) true else if t = 38 then w38
  else Gout C xr F rest t

/-- One `b`. -/
def innerStep (C : List Bool) (x a : Date) : Bool × Bool × List Date → Bool × Bool × List Date
  | (F, got, []) => (F, got, [])
  | (F, got, b :: bs) => (F || ((got || decide (b = x)) && decide (pairWord (a, b) = C)),
      got || decide (b = x), bs)

theorem flatW_cons (d : Date) (l : List Date) : flatW (d :: l) = (encDate d).reverse ++ flatW l := rfl

theorem take_flatW (d : Date) (l : List Date) : (flatW (d :: l)).take 10 = (encDate d).reverse := by
  rw [flatW_cons, List.take_append_of_le_length (by simp [length_encDate])]
  exact List.take_of_length_le (by simp [length_encDate])

theorem drop_flatW (d : Date) (l : List Date) : (flatW (d :: l)).drop 10 = flatW l := by
  rw [flatW_cons]; exact List.drop_left' (by simp [length_encDate])

theorem rev_enc_inj {b x : Date} : (encDate b).reverse = (encDate x).reverse ↔ b = x := by
  rw [List.reverse_inj]; exact encDate.injective.eq_iff

/-- Reading `b` and noting whether it is `x`. -/
def readB : Prog 40 := take10 31 33 ⨾ prim (.eq 33 24 Z) ⨾ ifBit Z (putW 35 [true]) nopP ⨾ clr Z

theorem run_readB (C : List Bool) (x a b : Date) (rest bs : List Date) (w38 w : List Bool)
    (F got : Bool) :
    run readB (Function.update (Gin C (encDate x).reverse F got a rest (b :: bs) w38) 39 w) =
      Function.update (Function.update (Gin C (encDate x).reverse F (got || decide (b = x)) a rest bs
        w38) 39 w) 33 (encDate b).reverse := by
  set S0 := Function.update (Gin C (encDate x).reverse F got a rest (b :: bs) w38) 39 w
  have h31 : S0 31 = flatW (b :: bs) := by simp [S0, Gin]
  have h24 : S0 24 = (encDate x).reverse := by simp [S0, Gin, Gout]
  rw [readB, run_seq, run_take10 (by decide) (by decide) (by decide), run_seq, run_prim, run_seq,
    run_ifBit]
  set S1 := Function.update (Function.update (Function.update S0 33 ((S0 31).take 10)) 31
    ((S0 31).drop 10)) Z []
  have e33 : S1 33 = (encDate b).reverse := by simp [S1, h31, take_flatW, Function.update_apply, GateGen.Z]
  have e24 : S1 24 = (encDate x).reverse := by simp [S1, h24, Function.update_apply, GateGen.Z]
  simp only [Prim.apply, Function.update_self, hd_cons, e33, e24, decide_eq_true_eq, rev_enc_inj]
  by_cases hbx : b = x
  · simp only [hbx, if_true, run_putW, run_clear, S1, h31, take_flatW, drop_flatW, decide_true,
      Bool.or_true]
    funext t; fin_cases t <;> simp [S0, Gin, Gout, Function.update_apply, GateGen.Z]
  · simp only [hbx, if_false, run_prim, Prim.apply, run_clear, S1, h31, take_flatW, drop_flatW,
      decide_false, Bool.or_false]
    funext t; fin_cases t <;> simp [S0, Gin, Gout, Function.update_apply, GateGen.Z]

theorem run_readB_nil (C : List Bool) (x a : Date) (rest : List Date) (w38 w : List Bool)
    (F got : Bool) :
    run readB (Function.update (Gin C (encDate x).reverse F got a rest [] w38) 39 w) =
      Function.update (Gin C (encDate x).reverse F got a rest [] w38) 39 w := by
  set S0 := Function.update (Gin C (encDate x).reverse F got a rest [] w38) 39 w
  have h31 : S0 31 = [] := by simp [S0, Gin, flatW]
  have h24 : S0 24 = (encDate x).reverse := by simp [S0, Gin, Gout]
  have hne : ([] : List Bool) ≠ (encDate x).reverse := fun h => by
    have := congrArg List.length h; simp [length_encDate] at this
  rw [readB, run_seq, run_take10 (by decide) (by decide) (by decide), run_seq, run_prim, run_seq,
    run_ifBit]
  simp only [Prim.apply, Function.update_self, hd_cons, h31, List.take_nil, List.drop_nil]
  have e : ∀ v, Function.update (Function.update (Function.update S0 33 []) 31 []) Z v 33 = [] :=
    fun v => by simp [Function.update_apply, GateGen.Z]
  have e2 : ∀ v, Function.update (Function.update (Function.update S0 33 []) 31 []) Z v 24 =
      (encDate x).reverse := fun v => by simp [Function.update_apply, GateGen.Z, h24]
  simp only [e, e2, decide_eq_true_eq, hne, decide_false, Bool.false_eq_true, ↓reduceIte, run_prim,
    Prim.apply, run_clear]
  funext t; fin_cases t <;> simp [S0, Gin, Gout, flatW, Function.update_apply, GateGen.Z]

theorem run_innerBody (C : List Bool) (x a : Date) (rest : List Date) (w38 w : List Bool)
    (F got : Bool) (bs : List Date) :
    run innerBody (Function.update (Gin C (encDate x).reverse F got a rest bs w38) 39 w) =
      Function.update (Gin C (encDate x).reverse (innerStep C x a (F, got, bs)).1
        (innerStep C x a (F, got, bs)).2.1 a rest (innerStep C x a (F, got, bs)).2.2 w38) 39 w := by
  have hinner : innerBody = readB ⨾ ifBlank 33 nopP (ifBit 35 genCmp nopP) ⨾ clr 33 := rfl
  rw [hinner, run_seq, run_seq]
  cases bs with
  | nil =>
    rw [run_readB_nil, run_ifBlank, if_pos (by simp [Gin, Gout]), run_nopP, run_clear]
    funext t; fin_cases t <;> simp [innerStep, Gin, Gout, Function.update_apply]
  | cons b bs =>
    rw [run_readB, run_ifBlank, if_neg (by simp [length_encDate, ← List.length_eq_zero_iff]),
      run_ifBit]
    set g := got || decide (b = x)
    set SA := Function.update (Function.update (Gin C (encDate x).reverse F g a rest bs w38) 39 w) 33
      (encDate b).reverse
    have h35 : hd (SA 35) = g := by simp [SA, Gin]
    rw [h35]
    by_cases hg : g = true
    · have hg' : (got || decide (b = x)) = true := hg
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hg'
      rw [if_pos hg, run_genCmp SA a b (by simp [SA, Gin]) (by simp [SA])
        (fun t ht => by
          revert ht; fin_cases t <;> simp [SA, Gin, Gout, genL, Function.update_apply])]
      have h0 : SA 0 = C := by simp [SA, Gin, Gout]
      have h34 : SA 34 = [F] := by simp [SA, Gin, Gout]
      rw [h0, h34, run_clear]
      by_cases hpw : pairWord (a, b) = C
      · simp only [hpw, if_true]
        funext t; fin_cases t <;> simp [innerStep, SA, Gin, Gout, Function.update_apply, g, hg', hpw]
      · simp only [hpw, if_false]
        funext t; fin_cases t <;> simp [innerStep, SA, Gin, Gout, Function.update_apply, g, hg', hpw]
    · rw [if_neg hg, run_nopP, run_clear]
      have hg' : (got || decide (b = x)) = false := by
        cases h : g
        · exact h
        · exact absurd h hg
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hg'
      funext t; fin_cases t <;> simp [innerStep, SA, Gin, Gout, Function.update_apply, g, hg']

theorem iter_innerStep (C : List Bool) (x a : Date) : ∀ (bs : List Date) (F got : Bool),
    ∃ g, (innerStep C x a)^[bs.length] (F, got, bs) = (F || innerV C x a got bs, g, [])
  | [], F, got => ⟨got, by simp [innerV]⟩
  | b :: bs, F, got => by
    obtain ⟨g, hg⟩ := iter_innerStep C x a bs (F || ((got || decide (b = x)) &&
      decide (pairWord (a, b) = C))) (got || decide (b = x))
    refine ⟨g, ?_⟩
    rw [List.length_cons, Function.iterate_succ_apply, innerStep, hg, innerV, Bool.or_assoc]

/-- One `a`. -/
def outerStep (C : List Bool) (x : Date) : Bool × List Date → Bool × List Date
  | (F, []) => (F, [])
  | (F, a :: rest) => (F || innerV C x a false (a :: rest), rest)

theorem iter_outerStep (C : List Bool) (x : Date) : ∀ (l : List Date) (F : Bool),
    (outerStep C x)^[l.length] (F, l) = (F || outerV C x l, [])
  | [], F => by simp [outerV]
  | a :: l, F => by
    rw [List.length_cons, Function.iterate_succ_apply, outerStep, iter_outerStep C x l, outerV,
      Bool.or_assoc]

theorem run_outerPre (C : List Bool) (x a : Date) (F : Bool) (rest : List Date) (w : List Bool) :
    run (cp 37 36 ⨾ cp 31 30 ⨾ take10 30 32 ⨾ prim (.tail 36) ⨾ putW 35 [false])
      (Function.update (Gout C (encDate x).reverse F (a :: rest)) 38 w) =
      Gin C (encDate x).reverse F false a rest (a :: rest) w := by
  rw [run_seq, run_seq, run_seq, run_seq, run_copy, run_copy,
    run_take10 (by decide) (by decide) (by decide), run_tail, run_putW]
  have h30 : (flatW (a :: rest)).take 10 = (encDate a).reverse := take_flatW a rest
  have h30' : (flatW (a :: rest)).drop 10 = flatW rest := drop_flatW a rest
  funext t; fin_cases t <;>
    simp [Gin, Gout, Function.update_apply, h30, h30', List.replicate_succ, GateGen.Z]

theorem run_innerLoop (C : List Bool) (x a : Date) (F : Bool) (rest : List Date) (w : List Bool) :
    ∃ g, run (forN 39 37 innerBody) (Gin C (encDate x).reverse F false a rest (a :: rest) w) =
      Function.update (Gin C (encDate x).reverse (F || innerV C x a false (a :: rest)) g a rest []
        w) 39 [] := by
  obtain ⟨g, hg⟩ := iter_innerStep C x a (a :: rest) F false
  refine ⟨g, ?_⟩
  have h := run_forN (39 : Fin 40) 37 innerBody
    (fun σ : Bool × Bool × List Date => Gin C (encDate x).reverse σ.1 σ.2.1 a rest σ.2.2 w)
    (innerStep C x a) (fun σ w' => run_innerBody C x a rest w w' σ.1 σ.2.1 σ.2.2)
    (F, false, a :: rest) (Gin C (encDate x).reverse F false a rest (a :: rest) w) rfl
  have hlen : ((Gin C (encDate x).reverse F false a rest (a :: rest) w) 37).length =
      (a :: rest).length := by simp [Gin]
  rw [h, hlen, hg]

theorem run_outerBody (C : List Bool) (x : Date) (F : Bool) (rest : List Date) (w : List Bool) :
    run outerBody (Function.update (Gout C (encDate x).reverse F rest) 38 w) =
      Function.update (Gout C (encDate x).reverse (outerStep C x (F, rest)).1
        (outerStep C x (F, rest)).2) 38 w := by
  rw [outerBody, run_seq, run_seq]
  cases rest with
  | nil =>
    rw [run_seq, run_seq, run_seq, run_seq, run_copy, run_copy,
      run_take10 (by decide) (by decide) (by decide), run_tail, run_putW, forN, run_seq, run_copy,
      run_loop, run_clearList]
    have h0 : ∀ v : Store 40, (Function.update v 39 (v 37)) 39 = v 37 := fun v => by simp
    rw [h0]
    have h37 : ∀ z : Store 40, (Function.update z 35 [false]) 37 = z 37 := fun z => by simp
    simp only [h37]
    funext t; fin_cases t <;> simp [Gout, outerStep, Function.update_apply, flatW, GateGen.Z]
  | cons a rest =>
    rw [run_outerPre]
    obtain ⟨g, hg⟩ := run_innerLoop C x a F rest w
    rw [hg, run_clearList]
    funext t; fin_cases t <;> simp [Gin, Gout, outerStep, Function.update_apply, flatW]

/-- The input store: `C` on tape `0`, `encDate x` on tape `1`. -/
def inStore (C : List Bool) (x : Date) : Store 40 := fun t =>
  if t = 0 then C else if t = 1 then encDate x else []

/-- **What `authMain` computes.** -/
theorem run_authPre (C : List Bool) (x : Date) :
    run (clr 24 ⨾ revN 10 ⨾ clr Z ⨾ putW 30 (flatW validL) ⨾
      putW 36 (List.replicate validL.length true) ⨾ putW 34 [false]) (inStore C x) =
      Gout C (encDate x).reverse false validL := by
  obtain ⟨z, hz⟩ := run_revN 10 (run (clr 24) (inStore C x))
  rw [run_seq, run_seq, hz, run_seq, run_seq, run_seq, run_clear, run_putW, run_putW, run_putW]
  have h1 : (encDate x).take 10 = encDate x := List.take_of_length_le (by simp [length_encDate])
  have h2 : (encDate x).drop 10 = [] := List.drop_of_length_le (by simp [length_encDate])
  funext t; fin_cases t <;> simp [inStore, Gout, Function.update_apply, h1, h2, GateGen.Z]

/-- **What `authMain` computes.** -/
theorem run_authMain (C : List Bool) (x : Date) :
    run authMain (inStore C x) = fun t => if t = 0 then [outerV C x validL] else [] := by
  rw [authMain, run_seq, run_authPre, run_seq,
    run_forN 38 36 outerBody (fun σ : Bool × List Date => Gout C (encDate x).reverse σ.1 σ.2)
      (outerStep C x) (fun σ w => run_outerBody C x σ.1 σ.2 w) (false, validL)
      (Gout C (encDate x).reverse false validL) rfl]
  have hlen : (Gout C (encDate x).reverse false validL 36).length = validL.length := by simp [Gout]
  rw [hlen, iter_outerStep, run_seq, run_copy, run_clearList]
  funext t; fin_cases t <;> simp [Gout, allButZero, Function.update_apply]

/-! ### The search is the window search -/

/-- The order key of a date. -/
def dkey (d : Date) : ℕ := 32 * d.1.val + d.2.val

theorem innerV_iff (C : List Bool) (x a : Date) : ∀ (got : Bool) (bs : List Date),
    bs.Pairwise (fun u v => dkey u < dkey v) →
    (innerV C x a got bs = true ↔
      ∃ b ∈ bs, pairWord (a, b) = C ∧ (got = true ∨ (x ∈ bs ∧ dkey x ≤ dkey b)))
  | got, [], _ => by simp [innerV]
  | got, b0 :: bs, hs => by
    rw [List.pairwise_cons] at hs
    have hg : ((got || decide (b0 = x)) = true) ↔ (got = true ∨ b0 = x) := by simp
    rw [innerV, Bool.or_eq_true, Bool.and_eq_true, innerV_iff C x a _ bs hs.2, hg,
      decide_eq_true_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨b, hb, h1, h2⟩)
      · refine ⟨b0, List.mem_cons_self .., h2, ?_⟩
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨by rw [h1]; exact List.mem_cons_self .., by rw [h1]⟩
      · refine ⟨b, List.mem_cons_of_mem _ hb, h1, ?_⟩
        rcases h2 with (h2 | h2) | ⟨h2, h3⟩
        · exact Or.inl h2
        · exact Or.inr ⟨by rw [← h2]; exact List.mem_cons_self .., by rw [← h2]; exact (hs.1 b hb).le⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ h2, h3⟩
    · rintro ⟨b, hb, h1, h2⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · refine Or.inl ⟨?_, h1⟩
        rcases h2 with h2 | ⟨h2, h3⟩
        · exact Or.inl h2
        · rcases List.mem_cons.mp h2 with h2 | h2
          · exact Or.inr h2.symm
          · exact absurd (hs.1 x h2) (not_lt.mpr h3)
      · refine Or.inr ⟨b, hb, h1, ?_⟩
        rcases h2 with h2 | ⟨h2, h3⟩
        · exact Or.inl (Or.inl h2)
        · rcases List.mem_cons.mp h2 with h2 | h2
          · exact Or.inl (Or.inr h2.symm)
          · exact Or.inr ⟨h2, h3⟩

theorem outerV_iff (C : List Bool) (x : Date) : ∀ (l : List Date),
    l.Pairwise (fun u v => dkey u < dkey v) →
    (outerV C x l = true ↔ ∃ a ∈ l, ∃ b ∈ l, dkey a ≤ dkey b ∧ pairWord (a, b) = C ∧ x ∈ l ∧
      dkey a ≤ dkey x ∧ dkey x ≤ dkey b)
  | [], _ => by simp [outerV]
  | a0 :: l, hs => by
    have hs' := hs
    rw [List.pairwise_cons] at hs'
    rw [outerV, Bool.or_eq_true, innerV_iff C x a0 false _ hs, outerV_iff C x l hs'.2]
    have hle : ∀ d ∈ a0 :: l, dkey a0 ≤ dkey d := by
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact le_rfl
      · exact (hs'.1 d hd).le
    constructor
    · rintro (⟨b, hb, h1, h2⟩ | ⟨a, ha, b, hb, h⟩)
      · rcases h2 with h2 | ⟨h2, h3⟩
        · exact absurd h2 Bool.false_ne_true
        · exact ⟨a0, List.mem_cons_self .., b, hb, hle b hb, h1, h2, hle x h2, h3⟩
      · exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, h.1, h.2.1,
          List.mem_cons_of_mem _ h.2.2.1, h.2.2.2⟩
    · rintro ⟨a, ha, b, hb, hab, h1, hx, hax, hxb⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl ⟨b, hb, h1, Or.inr ⟨hx, hxb⟩⟩
      · have ha0 := hs'.1 a ha
        refine Or.inr ⟨a, ha, b, ?_, hab, h1, ?_, hax, hxb⟩
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact absurd hab (not_le.mpr ha0)
          · exact hb
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact absurd hax (not_le.mpr ha0)
          · exact hx

theorem validL_sorted : validL.Pairwise (fun u v => dkey u < dkey v) :=
  List.isChain_iff_pairwise.mp (by decide +kernel)

theorem mem_validL (d : Date) : d ∈ validL ↔ valid d = true := by
  simp [validL, mem_allDates]

theorem dateLe_dkey (a b : Date) : dateLe a b = true ↔ dkey a ≤ dkey b := by
  rw [dateLe_iff, decide_eq_true_iff]; rfl

theorem length_validL : validL.length = 366 := by decide +kernel

end AdvancedEncryption.PE.Gates.DateWindow
