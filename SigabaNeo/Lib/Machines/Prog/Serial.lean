import SigabaNeo.Lib.Machines.Prog.Det

/-!
# Bit-serial transducers on tape words

Words here are read **from their first bit**, as the little-endian encodings of
`SigabaNeo.Encode.zmodEnc` (least significant bit first). The primitive `carry` of the tape
language combines words from their *last* digit, so it does not add little-endian words; instead a
word algorithm streams its inputs bit by bit: pop the first bit of each input, update a one-bit
state, and shift the output bit in at the end of a register (`Prog.sin`, `Prog.push`), whose width
never changes. After `n` shifts a register of width `n` holds exactly the `n` shifted bits
(`shiftIn_iter`).

* `serF g c xs ys`, `serC g c xs ys`: the output word and the final state of the transducer
  `g : Bool → Bool → Bool → Bool × Bool` (input bits and state to output bit and new state) from the
  state `c`, over the bits of `xs` (missing bits of `ys` read as `false`).
* `Prog.zipP g c₀ : Prog 11`: the transducer as a program over 11 tapes: `0` output, `1` final
  state, `2`, `3` inputs, `4 … 10` scratch (blank before and after). `run_zipP`: it writes
  `serF g c₀ (s 2) (s 3)` on tape `0` and `[serC g c₀ (s 2) (s 3)]` on tape `1` (nothing if
  `s 2 = []`). `zipW g c₀` also clears tape `1`.
-/

namespace SigabaNeo.Tape

variable {k n : ℕ}

@[simp] theorem hd_take_one (w : List Bool) : hd (w.take 1) = hd w := by cases w <;> rfl

theorem tail_append_drop (w : List Bool) (o : Bool) (T : List Bool) (m : ℕ) :
    ((w ++ [o]).tail ++ T).drop m = (w ++ o :: T).drop (m + 1) := by
  cases w <;> simp

/-- Shifting the bits `bs` in at the end of a register, one at a time. -/
theorem shiftIn_iter (r bs : List Bool) :
    bs.foldl (fun r b => (r ++ [b]).tail) r = (r ++ bs).drop bs.length := by
  induction bs generalizing r with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, List.length_cons, ← tail_append_drop]

/-- A bit-serial transducer: input bits and state to output bit and new state. -/
abbrev SerOp := Bool → Bool → Bool → Bool × Bool

/-- The output word of a transducer over the bits of `xs`. -/
def serF (g : SerOp) : Bool → List Bool → List Bool → List Bool
  | _, [], _ => []
  | c, x :: xs, ys => (g x (hd ys) c).1 :: serF g (g x (hd ys) c).2 xs ys.tail

/-- The final state of a transducer over the bits of `xs`. -/
def serC (g : SerOp) : Bool → List Bool → List Bool → Bool
  | c, [], _ => c
  | c, x :: xs, ys => serC g (g x (hd ys) c).2 xs ys.tail

@[simp] theorem length_serF (g : SerOp) (c : Bool) (xs ys : List Bool) :
    (serF g c xs ys).length = xs.length := by
  induction xs generalizing c ys with
  | nil => rfl
  | cons x xs ih => simp [serF, ih]

/-- One round of the transducer on the abstract state (state, input, input, register). -/
def zstep (g : SerOp) : Bool × List Bool × List Bool × List Bool → Bool × List Bool × List Bool × List Bool
  | (c, xs, ys, r) => ((g (hd xs) (hd ys) c).2, xs.tail, ys.tail, (r ++ [(g (hd xs) (hd ys) c).1]).tail)

theorem zstep_iter (g : SerOp) : ∀ (xs : List Bool) (c : Bool) (ys r : List Bool),
    (zstep g)^[xs.length] (c, xs, ys, r) =
      (serC g c xs ys, [], ys.drop xs.length, (r ++ serF g c xs ys).drop xs.length)
  | [], c, ys, r => by simp [serC, serF]
  | x :: xs, c, ys, r => by
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [zstep, hd_cons, List.tail_cons]
    rw [zstep_iter g xs]
    simp only [serC, serF, tail_append_drop, List.drop_tail]

namespace Prog

/-- Sequencing. -/
scoped infixr:60 " ⨾ " => Prog.seq

/-- Branch on the first bit of tape `f`. -/
def br (f : Fin k) (P : Bool → Prog k) : Prog k := ifBit f (P true) (P false)

@[simp] theorem run_br (f : Fin k) (P : Bool → Prog k) (s : Store k) :
    run (br f P) s = run (P (hd (s f))) s := by
  simp only [br, run_ifBit]; cases hd (s f) <;> rfl

/-- `i := s j`. -/
abbrev cp (i j : Fin k) : Prog k := prim (.copy i j)
/-- `i := []`. -/
abbrev clr (i : Fin k) : Prog k := prim (.clear i)
/-- `i := tail`, `j := (s i).take 1`. -/
abbrev pp (i j : Fin k) : Prog k := prim (.pop i j)
/-- `i := tail`. -/
abbrev tl (i : Fin k) : Prog k := prim (.tail i)

/-! ### The transducer program -/

/-- Tapes: `0` output, `1` final state, `2` `3` inputs; scratch `4` X, `5` Y, `6` R (register),
`7` C (state), `8` `9` the popped bits, `10` the counter. -/
def zipInit (c₀ : Bool) : Prog 11 :=
  cp 4 2 ⨾ cp 5 3 ⨾ cp 6 2 ⨾ cp 10 2 ⨾ takeHead 7 2 ⨾ sin c₀ 7

/-- One round: pop a bit of each input, branch on the bits and the state, shift the output bit
into the register, set the state. -/
def zipBody (g : SerOp) : Prog 11 :=
  pp 4 8 ⨾ pp 5 9 ⨾
    br 8 (fun x => br 9 fun y => br 7 fun c => sin (g x y c).1 6 ⨾ sin (g x y c).2 7) ⨾
    clr 8 ⨾ clr 9

/-- Write the register and the state out; blank the scratch. -/
def zipFin : Prog 11 := cp 0 6 ⨾ cp 1 7 ⨾ clr 4 ⨾ clr 5 ⨾ clr 6 ⨾ clr 7

/-- **The bit-serial transducer** `g` from the state `c₀`. -/
def zipP (g : SerOp) (c₀ : Bool) : Prog 11 := zipInit c₀ ⨾ loop 10 (zipBody g) ⨾ zipFin

/-- The transducer, discarding its final state. -/
def zipW (g : SerOp) (c₀ : Bool) : Prog 11 := zipP g c₀ ⨾ clr 1

/-- The scratch tapes of `zipP` are blank. -/
def ZipClean (s : Store 11) : Prop := ∀ i : Fin 11, 4 ≤ i.val → s i = []

/-- The abstract store of a round. -/
def zipG (s : Store 11) : Bool × List Bool × List Bool × List Bool → Store 11
  | (c, xs, ys, r) =>
    Function.update (Function.update (Function.update (Function.update s 4 xs) 5 ys) 6 r) 7 [c]

theorem run_zipBody (g : SerOp) (s : Store 11) (hs : ZipClean s) (a) (w : List Bool) :
    run (zipBody g) (Function.update (zipG s a) 10 w) = Function.update (zipG s (zstep g a)) 10 w := by
  obtain ⟨c, xs, ys, r⟩ := a
  have h8 := hs 8 (by decide)
  have h9 := hs 9 (by decide)
  funext t
  simp only [zipBody, zipG, zstep, run_seq, run_pop, run_br, run_sin, run_clear]
  fin_cases t <;> simp [h8, h9]

theorem run_zipP (g : SerOp) (c₀ : Bool) (s : Store 11) (hs : ZipClean s) :
    run (zipP g c₀) s = Function.update (Function.update s 0 (serF g c₀ (s 2) (s 3))) 1
      (if s 2 = [] then [] else [serC g c₀ (s 2) (s 3)]) := by
  have h4 := hs 4 (by decide)
  have h5 := hs 5 (by decide)
  have h6 := hs 6 (by decide)
  have h7 := hs 7 (by decide)
  have h10 := hs 10 (by decide)
  rcases hx : s 2 with _ | ⟨x, xs⟩
  · funext t
    simp only [zipP, zipInit, zipFin, run_seq, run_copy, run_takeHead, run_sin, run_clear,
      run_loop]
    fin_cases t <;> simp [hx, h4, h5, h6, h7, h10, serF]
  · have hinit : run (zipInit c₀) s = Function.update (zipG s (c₀, x :: xs, s 3, x :: xs)) 10 (x :: xs) := by
      funext t
      simp only [zipInit, zipG, run_seq, run_copy, run_takeHead, run_sin]
      fin_cases t <;> simp [hx]
    have hloop := run_loop_iter 10 (zipBody g) (zipG s) (zstep g) (fun _ => True)
      (fun a w _ => run_zipBody g s hs a w) (fun _ _ => trivial) (x :: xs) (c₀, x :: xs, s 3, x :: xs)
      trivial
    rw [zipP, run_seq, run_seq, hinit, hloop, zstep_iter, List.drop_left' (by simp)]
    funext t
    simp only [zipFin, zipG, run_seq, run_copy, run_clear]
    fin_cases t <;> simp [h4, h5, h6, h7, h10]

theorem run_zipW (g : SerOp) (c₀ : Bool) (s : Store 11) (hs : ZipClean s) (h1 : s 1 = []) :
    run (zipW g c₀) s = Function.update s 0 (serF g c₀ (s 2) (s 3)) := by
  rw [zipW, run_seq, run_zipP g c₀ s hs, run_clear, Function.update_idem]
  funext t
  by_cases ht : t = 1
  · subst ht; simp [h1]
  · simp [ht]

theorem noGrow_zipP (g : SerOp) (c₀ : Bool) : (zipP g c₀).NoGrow := rfl
theorem noGrow_zipW (g : SerOp) (c₀ : Bool) : (zipW g c₀).NoGrow := rfl
theorem wf_zipW (g : SerOp) (c₀ : Bool) : (zipW g c₀).WF := wf_of_wfB rfl
theorem wf_zipP (g : SerOp) (c₀ : Bool) : (zipP g c₀).WF := wf_of_wfB rfl

end Prog

end SigabaNeo.Tape
