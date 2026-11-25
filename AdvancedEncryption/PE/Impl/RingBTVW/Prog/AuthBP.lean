import PE.Impl.RingBTVW.Prog.BpCompLaw
import SigabaNeo.Lib.Machines.Prog.LenEq
import SigabaNeo.Lib.Machines.Prog.CoinFreeX

/-!
# The authorization program of branching programs

`authBP` (`Prog 16`; `BP_PLAN.md` §5.2): from the predicate word `C` on tape `0` and the attribute
bits `xs` on tape `1`, it writes `[authA C xs]` on tape `0`, every other tape blank:
`authA C xs = decide (|C| = 211 · 2^22) && !lastBit C xs`, where the program is run on the table
word directly: the state `z` (14 bits, most significant first) starts at `0`; step `i < 15` reads
the entry `256 z + a` (`a` the next 8 bits of `xs`) of table `i`, the `14` bits at
`i · tblW + 14 (256 z + a)` (`tblW = 14 · 2^22`); the result is the bit at
`15 · tblW + 256 z₁₅ + a₁₅` (`zA`, `lastBit`).

The entry offset is built in unary by doubling along the bits of `z ‖ a` (`offP`), so no number
is ever converted. **`run_authBP`**, **`law_authBP`**; `good_authBP`: coin-free, well formed.

**`authA_encAttr`**: on attribute bits, `authA C (encAttr x) = decide (|C| = bpLen) &&
!output (tablesOf C) x` (the states `zA` are the bits of `zs (tablesOf C) x`, `zA_encAttr`), hence
**`law_authBPC`**.
-/

namespace AdvancedEncryption.RingBTVW.BpComp

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices
open AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates.BPCircuit
  AdvancedEncryption.PE.Gates.BPWord
open scoped Prog

/-! ### The specification -/

/-- Bits as a number, most significant first. -/
def numB (l : List Bool) : ℕ := l.foldl (fun acc b => 2 * acc + b.toNat) 0

/-- The length of a predicate word. -/
def bpLenA : ℕ := 211 * 2 ^ 22

/-- One step: the 14 bits of entry `numB (z ++ a)` of table `i`. -/
def stepZ (C : List Bool) (i : ℕ) (z a : List Bool) : List Bool :=
  ((C.drop (i * tblW)).drop (14 * numB (z ++ a))).take 14

/-- The symbol bits of step `i`. -/
def symA (xs : List Bool) (i : ℕ) : List Bool := (xs.drop (8 * i)).take 8

/-- The states. -/
def zA (C xs : List Bool) : ℕ → List Bool
  | 0 => List.replicate 14 false
  | i + 1 => stepZ C i (zA C xs i) (symA xs i)

/-- The output bit: entry `numB (z₁₅ ++ a₁₅)` of the output table. -/
def lastBit (C xs : List Bool) : Bool :=
  hd ((C.drop (15 * tblW)).drop (numB (zA C xs 15 ++ symA xs 15)))

/-- **The authorization bit.** -/
def authA (C xs : List Bool) : Bool := decide (C.length = bpLenA) && !lastBit C xs

/-! ### Tapes -/

abbrev tC : Fin 16 := 0
abbrev tX : Fin 16 := 1
abbrev tCU : Fin 16 := 2
abbrev tZB : Fin 16 := 3
abbrev tK : Fin 16 := 4
abbrev tU : Fin 16 := 5
abbrev tE : Fin 16 := 6
abbrev tT2 : Fin 16 := 7
abbrev tA2 : Fin 16 := 8
abbrev tB2 : Fin 16 := 9
abbrev tKC : Fin 16 := 10
abbrev tS2 : Fin 16 := 11
abbrev tTB : Fin 16 := 12
abbrev tBit : Fin 16 := 13
abbrev tLT : Fin 16 := 14
abbrev tF : Fin 16 := 15

/-! ### The program -/

/-- The entry offset of `z ‖ a`: `K := z ++ 8` bits of `X`, then `U := |E| · numB K` by doubling. -/
def offP : Prog 16 :=
  cp tK tZB ⨾ iter tK (pp tX tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 8 ⨾ clr tU ⨾
    forN tKC tK (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾ ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾
      clr tBit)

/-- One step: the next state from table `i` (at `CUR`), then the next table. -/
def stepA : Prog 16 :=
  offP ⨾ cp tT2 tCU ⨾ dropT tT2 tU tA2 ⨾ clr tZB ⨾
    iter tT2 (pp tT2 tBit ⨾ prim (.snocHead tZB tBit) ⨾ clr tBit) 14 ⨾ clr tT2 ⨾
    dropT tCU tTB tA2 ⨾ clr tU

/-- The length test on `C`, into `F` (`lenEqP` on the tapes `C, F, LT, T2, A, B`). -/
def uL : Fin 6 → Fin 16 := ![tC, tF, tLT, tT2, tA2, tB2]

theorem uL_inj : Function.Injective uL := by decide

/-- The tables and the start: `TB := 1^tblW`, `E := 1^14`, `CUR := C`, `z := 0`, 15 steps. -/
def initA : Prog 16 :=
  natU tTB tA2 tB2 tblW ⨾ natU tE tA2 tB2 14 ⨾ cp tCU tC ⨾ clr tZB ⨾ snocN tZB false 14 ⨾
    natU tS2 tA2 tB2 15

/-- The last step: the bit of the output table into `Bit`. -/
def lastA : Prog 16 :=
  clr tE ⨾ prim (.snoc tE true) ⨾ offP ⨾ cp tT2 tCU ⨾ dropT tT2 tU tA2 ⨾ pp tT2 tBit

/-- The output bit: the length flag and the negated table bit. -/
def outA' : Prog 16 := clr tC ⨾ ifBit tF (ifBit tBit (setB tC false) (setB tC true)) (setB tC false)

/-- Blank the work tapes. -/
def clrA : Prog 16 :=
  clr tX ⨾ clr tCU ⨾ clr tZB ⨾ clr tK ⨾ clr tU ⨾ clr tE ⨾ clr tT2 ⨾ clr tTB ⨾ clr tBit ⨾ clr tF

/-- **The authorization program.** -/
def authBP : Prog 16 :=
  Prog.map uL (lenEqP bpLenA) ⨾ initA ⨾ loop tS2 stepA ⨾ lastA ⨾ outA' ⨾ clrA

/-! ### The store -/

/-- The tapes of the authorization program. -/
structure AV where
  c : List Bool
  x : List Bool
  cur : List Bool
  zb : List Bool
  k : List Bool
  u : List Bool
  e : List Bool
  tt : List Bool
  a : List Bool
  b : List Bool
  kc : List Bool
  sc : List Bool
  tbl : List Bool
  t : List Bool
  lt : List Bool
  f : List Bool

/-- Its store. -/
def AV.enc (v : AV) : Store 16 := fun t =>
  if t = tC then v.c else
  if t = tX then v.x else
  if t = tCU then v.cur else
  if t = tZB then v.zb else
  if t = tK then v.k else
  if t = tU then v.u else
  if t = tE then v.e else
  if t = tT2 then v.tt else
  if t = tA2 then v.a else
  if t = tB2 then v.b else
  if t = tKC then v.kc else
  if t = tS2 then v.sc else
  if t = tTB then v.tbl else
  if t = tBit then v.t else
  if t = tLT then v.lt else
  if t = tF then v.f else []

theorem AV.enc_c (v : AV) : v.enc tC = v.c := by unfold AV.enc; rfl
theorem AV.enc_x (v : AV) : v.enc tX = v.x := by unfold AV.enc; rfl
theorem AV.enc_cur (v : AV) : v.enc tCU = v.cur := by unfold AV.enc; rfl
theorem AV.enc_zb (v : AV) : v.enc tZB = v.zb := by unfold AV.enc; rfl
theorem AV.enc_k (v : AV) : v.enc tK = v.k := by unfold AV.enc; rfl
theorem AV.enc_u (v : AV) : v.enc tU = v.u := by unfold AV.enc; rfl
theorem AV.enc_e (v : AV) : v.enc tE = v.e := by unfold AV.enc; rfl
theorem AV.enc_tt (v : AV) : v.enc tT2 = v.tt := by unfold AV.enc; rfl
theorem AV.enc_a (v : AV) : v.enc tA2 = v.a := by unfold AV.enc; rfl
theorem AV.enc_b (v : AV) : v.enc tB2 = v.b := by unfold AV.enc; rfl
theorem AV.enc_kc (v : AV) : v.enc tKC = v.kc := by unfold AV.enc; rfl
theorem AV.enc_sc (v : AV) : v.enc tS2 = v.sc := by unfold AV.enc; rfl
theorem AV.enc_tbl (v : AV) : v.enc tTB = v.tbl := by unfold AV.enc; rfl
theorem AV.enc_t (v : AV) : v.enc tBit = v.t := by unfold AV.enc; rfl
theorem AV.enc_lt (v : AV) : v.enc tLT = v.lt := by unfold AV.enc; rfl
theorem AV.enc_f (v : AV) : v.enc tF = v.f := by unfold AV.enc; rfl
theorem AV.upd_c (v : AV) (y : List Bool) :
    Function.update v.enc tC y = { v with c := y }.enc := by
  funext t; by_cases h : t = tC
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_x (v : AV) (y : List Bool) :
    Function.update v.enc tX y = { v with x := y }.enc := by
  funext t; by_cases h : t = tX
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_cur (v : AV) (y : List Bool) :
    Function.update v.enc tCU y = { v with cur := y }.enc := by
  funext t; by_cases h : t = tCU
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_zb (v : AV) (y : List Bool) :
    Function.update v.enc tZB y = { v with zb := y }.enc := by
  funext t; by_cases h : t = tZB
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_k (v : AV) (y : List Bool) :
    Function.update v.enc tK y = { v with k := y }.enc := by
  funext t; by_cases h : t = tK
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_u (v : AV) (y : List Bool) :
    Function.update v.enc tU y = { v with u := y }.enc := by
  funext t; by_cases h : t = tU
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_e (v : AV) (y : List Bool) :
    Function.update v.enc tE y = { v with e := y }.enc := by
  funext t; by_cases h : t = tE
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_tt (v : AV) (y : List Bool) :
    Function.update v.enc tT2 y = { v with tt := y }.enc := by
  funext t; by_cases h : t = tT2
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_a (v : AV) (y : List Bool) :
    Function.update v.enc tA2 y = { v with a := y }.enc := by
  funext t; by_cases h : t = tA2
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_b (v : AV) (y : List Bool) :
    Function.update v.enc tB2 y = { v with b := y }.enc := by
  funext t; by_cases h : t = tB2
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_kc (v : AV) (y : List Bool) :
    Function.update v.enc tKC y = { v with kc := y }.enc := by
  funext t; by_cases h : t = tKC
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_sc (v : AV) (y : List Bool) :
    Function.update v.enc tS2 y = { v with sc := y }.enc := by
  funext t; by_cases h : t = tS2
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_tbl (v : AV) (y : List Bool) :
    Function.update v.enc tTB y = { v with tbl := y }.enc := by
  funext t; by_cases h : t = tTB
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_t (v : AV) (y : List Bool) :
    Function.update v.enc tBit y = { v with t := y }.enc := by
  funext t; by_cases h : t = tBit
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_lt (v : AV) (y : List Bool) :
    Function.update v.enc tLT y = { v with lt := y }.enc := by
  funext t; by_cases h : t = tLT
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]
theorem AV.upd_f (v : AV) (y : List Bool) :
    Function.update v.enc tF y = { v with f := y }.enc := by
  funext t; by_cases h : t = tF
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, AV.enc.eq_1, AV.enc.eq_1]; simp only [h, ite_false]

/-- Normalize updates of the store. -/
macro "encA" : tactic => `(tactic| simp only [AV.upd_c, AV.upd_x, AV.upd_cur, AV.upd_zb, AV.upd_k, AV.upd_u, AV.upd_e, AV.upd_tt, AV.upd_a, AV.upd_b, AV.upd_kc, AV.upd_sc, AV.upd_tbl, AV.upd_t, AV.upd_lt, AV.upd_f, AV.enc_c, AV.enc_x, AV.enc_cur, AV.enc_zb, AV.enc_k, AV.enc_u, AV.enc_e, AV.enc_tt, AV.enc_a, AV.enc_b, AV.enc_kc, AV.enc_sc, AV.enc_tbl, AV.enc_t, AV.enc_lt, AV.enc_f])

/-! ### Laws -/

/-- `n` rounds of moving the first bit of `src` to the end of `dst` (`t` scratch, blank). -/
theorem run_iter_mv (src dst t z : Fin 16) (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t) :
    ∀ (n : ℕ) (s : Store 16), s t = [] →
      run (iter z (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) n) s =
        Function.update (Function.update s src ((s src).drop n)) dst (s dst ++ (s src).take n)
  | 0, s, _ => by
    rw [run_iter]; simp
  | n + 1, s, ht => by
    rw [run_iter, Function.iterate_succ_apply, ← run_iter]
    have h1 : run (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) s =
        Function.update (Function.update s src (s src).tail) dst (s dst ++ (s src).take 1) := by
      simp only [run_seq, run_prim, Prim.apply]
      funext u; simp only [Function.update_apply]
      split_ifs <;> simp_all
    rw [h1, run_iter_mv src dst t z hsd hst hdt n _ (by
      rw [Function.update_of_ne (Ne.symm hdt), Function.update_of_ne (Ne.symm hst)]; exact ht)]
    funext u; simp only [Function.update_apply]
    split_ifs <;> simp_all [take_one_append_take_tail]

theorem hd_take1 (l : List Bool) : hd (l.take 1) = hd l := by cases l <;> rfl

/-- One round of the doubling. -/
def dblStep (E : List Bool) (p : List Bool × List Bool) : List Bool × List Bool :=
  (p.1 ++ p.1 ++ (if hd p.2 = true then E else []), p.2.tail)

theorem iterate_dblStep (e : ℕ) : ∀ (k : List Bool) (n : ℕ),
    (dblStep (List.replicate e true))^[k.length] (List.replicate (e * n) true, k) =
      (List.replicate (e * k.foldl (fun acc b => 2 * acc + b.toNat) n) true, [])
  | [], n => by simp
  | b :: k, n => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have h : dblStep (List.replicate e true) (List.replicate (e * n) true, b :: k) =
        (List.replicate (e * (2 * n + b.toNat)) true, k) := by
      simp only [dblStep, hd_cons, List.tail_cons, List.replicate_append_replicate]
      cases b <;> simp [List.replicate_append_replicate] <;> ring_nf
    rw [h, iterate_dblStep e k (2 * n + b.toNat), List.foldl_cons]

theorem numB_eq (k : List Bool) : numB k = k.foldl (fun acc b => 2 * acc + b.toNat) 0 := rfl

/-- **The entry offset.** -/
theorem run_offP (v : AV) (e : ℕ) (he : v.e = List.replicate e true) (ht : v.t = [])
    (hkc : v.kc = []) (ha : v.a = []) (hb : v.b = []) :
    run offP v.enc = AV.enc
      { v with k := [], x := v.x.drop 8,
               u := List.replicate (e * numB (v.zb ++ v.x.take 8)) true } := by
  simp only [offP, run_seq]
  rw [run_copy]; encA
  rw [run_iter_mv tX tK tBit tK (by decide) (by decide) (by decide) 8 _ (by encA; exact ht)]
  encA
  rw [run_clear]; encA
  let G : List Bool × List Bool → Store 16 := fun p =>
    AV.enc { v with k := p.2, x := v.x.drop 8, u := p.1 }
  have hstep : ∀ p w, run (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾ ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾
      clr tBit) (Function.update (G p) tKC w) =
      Function.update (G (dblStep (List.replicate e true) p)) tKC w := by
    intro p w
    simp only [G]
    encA
    simp only [run_seq, run_pop]
    encA
    rw [run_appT_blank (by decide) (by decide) (by decide) _ (by encA; exact ha) (by encA; exact hb)]
    encA
    rw [run_ifBit]
    encA
    simp only [dblStep, hd_take1]
    split_ifs with h
    · rw [run_appT_blank (by decide) (by decide) (by decide) _ (by encA; exact ha)
        (by encA; exact hb), run_clear]
      encA
      simp [he, ht]
    · rw [run_nop, run_clear]
      encA
      simp [ht]
  rw [run_forN tKC tK _ G (dblStep (List.replicate e true)) hstep
    (List.replicate (e * 0) true, v.zb ++ List.take 8 v.x) _ (by
      simp only [G]; encA; simp)]
  encA
  rw [iterate_dblStep]
  simp only [G]
  encA
  rw [hkc]; rfl

/-- The store before step `i`. -/
def aSt (C xs : List Bool) (fl : Bool) (i : ℕ) (w : List Bool) : AV :=
  ⟨C, xs.drop (8 * i), C.drop (i * tblW), zA C xs i, [], [], List.replicate 14 true, [], [], [], [],
    w, List.replicate tblW true, [], [], [fl]⟩

/-- **One step.** -/
theorem run_stepA (C xs : List Bool) (fl : Bool) (i : ℕ) (w : List Bool) :
    run stepA (aSt C xs fl i w).enc = (aSt C xs fl (i + 1) w).enc := by
  simp only [stepA, run_seq]
  rw [run_offP _ 14 rfl rfl rfl rfl rfl]
  rw [run_copy]; encA
  rw [run_dropT_blank (t := tT2) (x := tU) (by decide) _ ?h1]; encA
  rw [run_clear (i := tZB)]; encA
  rw [run_iter_mv tT2 tZB tBit tT2 (by decide) (by decide) (by decide) 14 _ ?h2]; encA
  rw [run_clear (i := tT2)]; encA
  rw [run_dropT_blank (t := tCU) (x := tTB) (by decide) _ ?h3]; encA
  rw [run_clear]; encA
  · congr 1
    simp only [aSt, AV.mk.injEq]
    refine ⟨trivial, ?_, ?_, ?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial, trivial⟩
    · rw [List.drop_drop, Nat.mul_succ, Nat.add_comm]
    · rw [List.length_replicate, List.drop_drop, Nat.succ_mul]
    · rw [List.length_replicate, List.nil_append]; rfl
  case h1 => encA; rfl
  case h2 => encA; rfl
  case h3 => encA; rfl

/-- **The steps.** -/
theorem run_stepsA (C xs : List Bool) (fl : Bool) :
    run (loop tS2 stepA) (aSt C xs fl 0 (List.replicate 15 true)).enc = (aSt C xs fl 15 []).enc := by
  have e : ∀ i w, { aSt C xs fl i [] with sc := w } = aSt C xs fl i w := fun _ _ => rfl
  have h := run_loop_count tS2 stepA (fun i => (aSt C xs fl i []).enc) 15
    (fun i _ w => by
      simp only [AV.upd_sc]
      rw [e, e]
      exact run_stepA C xs fl i w) (List.replicate 15 true) 0 (by simp)
  simp only [AV.upd_sc, List.length_replicate, Nat.zero_add] at h
  rw [e, e] at h
  exact h

/-- The input store: `C` on tape `0`, the attribute bits on tape `1`. -/
def inA (C xs : List Bool) : Store 16 :=
  AV.enc ⟨C, xs, [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩

/-- The output store: the bit on tape `0`. -/
def outA (b : Bool) : Store 16 :=
  AV.enc ⟨[b], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩

theorem run_lenA (C xs : List Bool) :
    run (Prog.map uL (lenEqP bpLenA)) (inA C xs) =
      AV.enc ⟨C, xs, [], [], [], [], [], [], [], [], [], [], [], [], [], [decide (C.length = bpLenA)]⟩ := by
  have hs : inA C xs ∘ uL = in0 C := by
    funext j; fin_cases j <;> rfl
  rw [run_map_eq_update uL_inj (lenEqP bpLenA) _ 1 [decide (C.length = bpLenA)]
    (by rw [hs]; exact run_lenEqP bpLenA C), show uL 1 = tF from rfl, inA]
  encA

theorem run_initA (C xs : List Bool) (fl : Bool) :
    run initA (AV.enc ⟨C, xs, [], [], [], [], [], [], [], [], [], [], [], [], [], [fl]⟩) =
      (aSt C xs fl 0 (List.replicate 15 true)).enc := by
  simp only [initA, run_seq]
  rw [run_natU (o := tTB) (by decide) (by decide) (by decide) _ _ rfl rfl]; encA
  rw [run_natU (o := tE) (by decide) (by decide) (by decide) _ _ rfl rfl]; encA
  rw [run_copy (i := tCU)]; encA
  rw [run_clear (i := tZB)]; encA
  rw [run_snocN (o := tZB)]; encA
  rw [run_natU (o := tS2) (by decide) (by decide) (by decide) _ _ rfl rfl]; encA
  simp only [aSt, zA, List.nil_append, Nat.mul_zero, List.drop_zero, Nat.zero_mul]

/-- The bits read by the last step. -/
def lastTT (C xs : List Bool) : List Bool :=
  (C.drop (15 * tblW)).drop (numB (zA C xs 15 ++ symA xs 15))

theorem run_lastA (C xs : List Bool) (fl : Bool) :
    run lastA (aSt C xs fl 15 []).enc =
      AV.enc ⟨C, (xs.drop (8 * 15)).drop 8, C.drop (15 * tblW), zA C xs 15, [],
        List.replicate (numB (zA C xs 15 ++ symA xs 15)) true, [true], (lastTT C xs).tail, [], [], [],
        [], List.replicate tblW true, (lastTT C xs).take 1, [], [fl]⟩ := by
  simp only [lastA, run_seq]
  rw [run_clear (i := tE)]; encA
  rw [run_prim (Prim.snoc tE true)]; simp only [Prim.apply]; encA
  rw [run_offP _ 1 rfl rfl rfl rfl rfl]
  rw [run_copy (i := tT2)]; encA
  rw [run_dropT_blank (t := tT2) (x := tU) (by decide) _ (by rfl)]; encA
  rw [run_pop (i := tT2)]; encA
  simp only [aSt, List.length_replicate, Nat.one_mul, lastTT, symA]
  rfl

/-- **The law of the authorization program** (pure semantics). -/
theorem run_authBP (C xs : List Bool) : run authBP (inA C xs) = outA (authA C xs) := by
  rw [authBP]
  repeat rw [run_seq]
  rw [run_lenA, run_initA, run_stepsA, run_lastA]
  simp only [outA', run_seq, run_clear]
  encA
  rw [run_ifBit]; encA
  have hlb : hd (List.take 1 (lastTT C xs)) = lastBit C xs := by rw [hd_take1]; rfl
  simp only [hd_cons]
  unfold authA
  cases hl : decide (C.length = bpLenA)
  · simp only [Bool.false_eq_true, ite_false, run_setB, Bool.false_and]
    encA
    simp only [clrA, run_seq, run_clear]
    encA
    rfl
  · simp only [ite_true, run_ifBit]
    encA
    rw [hlb]
    cases lastBit C xs
    · simp only [Bool.false_eq_true, ite_false, run_setB]
      encA
      simp only [clrA, run_seq, run_clear]
      encA
      rfl
    · simp only [ite_true, run_setB]
      encA
      simp only [clrA, run_seq, run_clear]
      encA
      rfl

/-! ### Coin-freeness and well-formedness -/

/-- Coin-free, well formed, writing only the tapes of `S`. -/
def GoodA (S : Fin 16 → Prop) (p : Prog 16) : Prop := p.CoinFree ∧ p.WF ∧ WritesIn S p

theorem GoodA.seq {S : Fin 16 → Prop} {p q : Prog 16} (hp : GoodA S p) (hq : GoodA S q) :
    GoodA S (p ⨾ q) := ⟨hp.1.seq' hq.1, ⟨hp.2.1, hq.2.1⟩, hp.2.2.seq hq.2.2⟩

theorem GoodA.prim {S : Fin 16 → Prop} (q : Prim 16) (h : ∀ i ∈ q.writes, S i) : GoodA S (prim q) :=
  ⟨rfl, trivial, WritesIn.prim q h⟩

theorem GoodA.iter {S : Fin 16 → Prop} {z : Fin 16} (hz : S z) {p : Prog 16} (hp : GoodA S p) :
    ∀ n, GoodA S (iter z p n)
  | 0 => GoodA.prim _ (by simp [Prim.writes, hz])
  | n + 1 => hp.seq (GoodA.iter hz hp n)

theorem goodA_appT {S : Fin 16 → Prop} {o x : Fin 16} (ho : S o) (ha : S tA2) (hb : S tB2)
    (hoa : o ≠ tA2) : GoodA S (appT o x tA2 tB2) :=
  ⟨coinFree_appT _ _ _ _, wf_appT hoa (by decide), writesIn_appT ho ha hb⟩

theorem goodA_dropT {S : Fin 16 → Prop} {t x : Fin 16} (ht : S t) (ha : S tA2) (hta : t ≠ tA2) :
    GoodA S (dropT t x tA2) := ⟨coinFree_dropT _ _ _, wf_dropT hta, writesIn_dropT ht ha⟩

theorem goodA_natU {S : Fin 16 → Prop} {o : Fin 16} (ho : S o) (ha : S tA2) (hb : S tB2)
    (hoa : o ≠ tA2) (hob : o ≠ tB2) : ∀ n, GoodA S (natU o tA2 tB2 n)
  | 0 => by rw [natU]; exact GoodA.prim _ (by simp [Prim.writes, ho])
  | n + 1 => by
    rw [natU]; split_ifs
    · exact (goodA_natU ho ha hb hoa hob _).seq (goodA_appT ho ha hb hoa)
    · exact (goodA_natU ho ha hb hoa hob n).seq (GoodA.prim _ (by simp [Prim.writes, ho]))
  decreasing_by all_goals omega

/-- All tapes but the step counter. -/
abbrev SA (t : Fin 16) : Prop := t ≠ tS2

theorem goodA_offP : GoodA SA offP := by
  have hb : GoodA (fun t => SA t ∧ t ≠ tKC) (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾
      ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾ clr tBit) :=
    (GoodA.prim _ (by simp +decide)).seq <| (goodA_appT (by decide) (by decide) (by decide) (by decide)).seq <|
      GoodA.seq (⟨CoinFree.ifBit' (coinFree_appT tU tE tA2 tB2) (CoinFree.prim' (.copy tU tU)),
        ⟨wf_appT (by decide) (by decide), (trivial : (prim (Prim.copy tU tU)).WF)⟩,
        WritesIn.ifBit (writesIn_appT (by decide) (by decide) (by decide))
          (WritesIn.prim (.copy tU tU) (by simp +decide))⟩ :
        GoodA (fun t => SA t ∧ t ≠ tKC) (ifBit tBit (appT tU tE tA2 tB2) (nop tU)))
        (GoodA.prim _ (by simp +decide))
  refine (GoodA.prim _ (by simp +decide)).seq <|
    (GoodA.iter (by decide) ((GoodA.prim _ (by simp +decide)).seq <|
      (GoodA.prim _ (by simp +decide)).seq (GoodA.prim _ (by simp +decide))) 8).seq <|
    (GoodA.prim _ (by simp +decide)).seq ?_
  exact (GoodA.prim _ (by simp +decide)).seq
    ⟨hb.1.loop', ⟨hb.2.1, hb.2.2 tKC (by simp)⟩, WritesIn.loop (by decide)
      (hb.2.2.mono fun t ht => ht.1)⟩

theorem goodA_stepA : GoodA SA stepA :=
  goodA_offP.seq <| (GoodA.prim _ (by simp +decide)).seq <|
    (goodA_dropT (by decide) (by decide) (by decide)).seq <| (GoodA.prim _ (by simp +decide)).seq <|
    (GoodA.iter (by decide) ((GoodA.prim _ (by simp +decide)).seq <|
      (GoodA.prim _ (by simp +decide)).seq (GoodA.prim _ (by simp +decide))) 14).seq <|
    (GoodA.prim _ (by simp +decide)).seq <| (goodA_dropT (by decide) (by decide) (by decide)).seq
      (GoodA.prim _ (by simp +decide))

/-- **The authorization program is coin-free and well formed.** -/
theorem good_authBP : authBP.CoinFree ∧ authBP.WF := by
  let T : Fin 16 → Prop := fun _ => True
  have hL : GoodA T (Prog.map uL (lenEqP bpLenA)) :=
    ⟨coinFree_mapP uL (coinFree_lenEqP _), WF.map uL_inj (wf_lenEqP _), fun i hi => absurd trivial hi⟩
  have hI : GoodA T initA :=
    (goodA_natU trivial trivial trivial (by decide) (by decide) _).seq <|
      (goodA_natU trivial trivial trivial (by decide) (by decide) _).seq <|
      (GoodA.prim _ (by simp [T])).seq <| (GoodA.prim _ (by simp [T])).seq <|
        GoodA.seq (⟨coinFree_snocN _ _ _, wf_snocN _ _ _,
        writesIn_snocN trivial _ _⟩ : GoodA T (snocN tZB false 14))
        (goodA_natU trivial trivial trivial (by decide) (by decide) _)
  have hS : GoodA T (loop tS2 stepA) :=
    ⟨goodA_stepA.1.loop', ⟨goodA_stepA.2.1, goodA_stepA.2.2 tS2 (by simp)⟩,
      fun i hi => absurd trivial hi⟩
  have hLa : GoodA T lastA :=
    (GoodA.prim _ (by simp [T])).seq <| (GoodA.prim _ (by simp [T])).seq <|
      GoodA.seq (⟨goodA_offP.1, goodA_offP.2.1, fun i hi => absurd trivial hi⟩ : GoodA T offP) <|
      (GoodA.prim _ (by simp [T])).seq <| (goodA_dropT trivial trivial (by decide)).seq
        (GoodA.prim _ (by simp [T]))
  have hO : GoodA T outA' :=
    (GoodA.prim _ (by simp [T])).seq ⟨CoinFree.ifBit' (CoinFree.ifBit' (coinFree_setB _ _)
      (coinFree_setB _ _)) (coinFree_setB _ _), ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩,
      ⟨trivial, trivial⟩⟩, fun i hi => absurd trivial hi⟩
  have hC : GoodA T clrA := by
    unfold clrA
    repeat (first | exact GoodA.prim _ (by simp [T]) | refine (GoodA.prim _ (by simp [T])).seq ?_)
  have h := hL.seq (hI.seq (hS.seq (hLa.seq (hO.seq hC))))
  exact ⟨h.1, h.2.1⟩

/-- **The law of the authorization program**: the point mass at the store with the bit
`authA C xs` on tape `0`. -/
theorem law_authBP (C xs : List Bool) :
    authBP.law (inA C xs) = PMF.pure (outA (authA C xs)) := by
  rw [law_eq_run_of_coinFree _ good_authBP.1, run_authBP]

/-! ### The authorization bit is the program's output -/

theorem take_drop_eq_ofFn (l : List Bool) (p n : ℕ) (h : p + n ≤ l.length) :
    (l.drop p).take n = List.ofFn fun k : Fin n => l.getD (p + k) false := by
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp at h2; omega)]

/-- `n` bits of `v`, most significant first. -/
def bitsN (v n : ℕ) : List Bool := List.ofFn fun k : Fin n => v.testBit (n - 1 - k)

theorem numB_cons (b : Bool) (l : List Bool) : numB (b :: l) = b.toNat * 2 ^ l.length + numB l := by
  have key : ∀ (l : List Bool) (acc : ℕ), l.foldl (fun acc b => 2 * acc + b.toNat) acc =
      acc * 2 ^ l.length + l.foldl (fun acc b => 2 * acc + b.toNat) 0 := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons c l ih =>
      intro acc
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, ih (2 * 0 + c.toNat)]; ring
  simp only [numB, List.foldl_cons]
  rw [key]; simp

theorem numB_append (l₁ l₂ : List Bool) : numB (l₁ ++ l₂) = numB l₁ * 2 ^ l₂.length + numB l₂ := by
  induction l₁ with
  | nil => simp [numB]
  | cons b l ih =>
    rw [List.cons_append, numB_cons, numB_cons, ih, List.length_append]; ring

theorem numB_bitsN (v : ℕ) : ∀ n, numB (bitsN v n) = v % 2 ^ n
  | 0 => by simp [bitsN, numB, Nat.mod_one]
  | n + 1 => by
    have e : bitsN v (n + 1) = v.testBit n :: bitsN v n := by
      apply List.ext_getElem (by simp [bitsN])
      intro k h1 h2
      cases k with
      | zero => simp [bitsN]
      | succ k => simp only [bitsN, List.getElem_ofFn, List.getElem_cons_succ]; congr 1; omega
    rw [e, numB_cons, numB_bitsN v n, show (bitsN v n).length = n by simp [bitsN]]
    rw [Nat.pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ n) with h | h
    · simp [h]
    · simp [h]; omega

theorem symA_encAttr (x : Attr) (i : ℕ) (hi : i < 16) :
    symA (encAttr x) i = bitsN (x ⟨i, hi⟩).val 8 := by
  rw [symA, take_drop_eq_ofFn _ _ _ (by rw [length_encAttr]; omega)]
  apply List.ext_getElem (by simp [bitsN])
  intro k h1 h2
  simp only [List.getElem_ofFn, bitsN]
  rw [getD_encAttr x hi (by simp at h1; omega)]

theorem bitsN_14 (C : List Bool) (p : ℕ) :
    bitsN (readNum C p).val 14 = List.ofFn fun k : Fin 14 => C.getD (p + k) false := by
  apply List.ext_getElem (by simp [bitsN])
  intro k h1 h2
  simp only [bitsN, List.getElem_ofFn, readNum, MuxTree.testBit_idx]
  have hk : k < 14 := by simpa [bitsN] using h1
  simp only [show 14 - 1 - k < 14 by omega, decide_true, Bool.true_and]
  congr 1; omega

/-- **The states of the authorization program** are those of the program of the word. -/
theorem zA_encAttr (C : List Bool) (hC : C.length = bpLen) (x : Attr) :
    ∀ i, i ≤ 15 → zA C (encAttr x) i = bitsN (zs (tablesOf C) x i).val 14
  | 0, _ => by
    simp only [zA, zs]
    apply List.ext_getElem (by simp [bitsN]); intro k h1 h2; simp [bitsN]
  | i + 1, hi => by
    rw [zA, zA_encAttr C hC x i (by omega), symA_encAttr x i (by omega), zs]
    simp only [show i < 15 from by omega, dite_true]
    simp only [tablesOf]
    rw [bitsN_14, stepZ, numB_append, numB_bitsN, numB_bitsN, List.drop_drop,
      take_drop_eq_ofFn _ _ _ ?_]
    · congr 1; funext k; congr 1
      have hz := (zs (tablesOf C) x i).isLt
      have ha := (x ⟨i, by omega⟩).isLt
      simp only [entryIdx, tblW, bitsN, List.length_ofFn]
      omega
    · have hz := (zs (tablesOf C) x i).isLt
      have ha := (x ⟨i, by omega⟩).isLt
      simp only [hC, bpLen, tblW, bitsN, List.length_ofFn]
      omega

/-- **The authorization bit is the negated output of the program**, within the class. -/
theorem authA_encAttr (C : List Bool) (x : Attr) :
    authA C (encAttr x) = (decide (C.length = bpLen) && !output (tablesOf C) x) := by
  by_cases hC : C.length = bpLen
  · have hl : lastBit C (encAttr x) = output (tablesOf C) x := by
      rw [lastBit, zA_encAttr C hC x 15 le_rfl, symA_encAttr x 15 (by omega), numB_append, numB_bitsN,
        numB_bitsN, List.drop_drop, hd_drop, output, run_eq_zs]
      simp only [tablesOf]
      congr 1
      simp only [outOff, tblW, bitsN, List.length_ofFn]
      generalize (zs _ x 15) = z
      have hz := z.isLt
      have ha := (x ⟨15, by omega⟩).isLt
      have e : (x ⟨15, by omega⟩).val % 2 ^ 8 = (x (Fin.last 15)).val := Nat.mod_eq_of_lt ha
      rw [Nat.mod_eq_of_lt hz, e]
      omega
    rw [authA, hl, show bpLenA = bpLen from rfl]
  · rw [authA, show bpLenA = bpLen from rfl]; simp [hC]

/-- **The authorization program** of the reductions and the handlers. -/
def authBPC : Prog 16 := authBP

/-- **The law of the authorization program**: from the predicate word `C` and the attribute bits
`encAttr x`, the bit `decide (|C| = bpLen) && !output (tablesOf C) x` on tape `0`. -/
theorem law_authBPC (C : List Bool) (x : Attr) :
    authBPC.law (inA C (encAttr x)) =
      PMF.pure (outA (decide (C.length = bpLen) && !output (tablesOf C) x)) := by
  rw [authBPC, law_authBP, authA_encAttr]

end AdvancedEncryption.RingBTVW.BpComp
