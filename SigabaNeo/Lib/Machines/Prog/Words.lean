import SigabaNeo.Lib.Machines.Prog.Serial
import SigabaNeo.Lib.Lattices.Algo.Words

/-!
# Fixed-width binary arithmetic as tape programs

Words are little-endian, as `SigabaNeo.Encode.zmodEnc` and the word algorithms of
`SigabaNeo.Lattices.Algo` (`val`, `addW`, `subW`, `shl`, `mulW`), so these programs compute those
functions **on the encodings themselves**, with no reversal. Each program is written over a fixed
set of tapes (`Prog n` for a small `n`) and placed on any distinct tapes of a larger machine by
`Prog.map`; its scratch tapes are blank before and after.

* `addP`, `subP`, `shlP`, `ltP` (`Prog 11`; tapes `0` output, `2` `3` inputs, `1` and `4 … 10`
  scratch): `addW`, `subW` (subtraction with borrow; on words of equal length), `shl`, and the
  comparison `[decide (val x < val y)]` (the final borrow).
* `mulP` (`Prog 18`; `0` output, `1` `2` inputs, `3 … 17` scratch): shift-and-add multiplication
  `mulW x y` on the width of `x`, by `|y|` rounds of a conditional addition and a doubling.
* `forN t c body` (the counter idiom `for i < |s t|`): copy the template `t` to the counter `c`,
  then loop.

Every program is in the fragment `NoGrow` (deterministic, never lengthening a word), so its law is a
point mass (`law_eq_run`), its length bound is the identity, and its time is at most
`tbC p * (L + 1) ^ tbD p`, with the constants computed here.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k n : ℕ}

/-! ### Words with equal residues -/

theorem eq_of_dec_eq {K : ℕ} {v w : List Bool} (hv : v.length = K) (hw : w.length = K)
    (h : dec K v = dec K w) : v = w := by
  rw [← enc_dec hv, ← enc_dec hw, h]

/-! ### The transducers of arithmetic -/

/-- The full adder. -/
def faOp : SerOp := fun x y c => (xor (xor x y) c, (x && y) || (c && (x || y)))

/-- The full subtractor (state: the borrow). -/
def fsOp : SerOp := fun x y c => (xor (xor x y) c, (!x && y) || (c && !(xor x y)))

/-- Shift by one bit (state: the previous bit). -/
def shlOp : SerOp := fun x _ c => (c, x)

theorem serF_faOp (c : Bool) (x y : List Bool) : serF faOp c x y = addc c x y := by
  induction x generalizing c y with
  | nil => rfl
  | cons a x ih =>
    cases y with
    | nil =>
      simp only [serF, hd_nil, List.tail_nil, addc, ih]
      congr 2 <;> cases a <;> cases c <;> rfl
    | cons b y => simp only [serF, hd_cons, List.tail_cons, addc, ih, faOp]

theorem serF_shlOp (c : Bool) (x y : List Bool) : serF shlOp c x y = (c :: x).take x.length := by
  induction x generalizing c y with
  | nil => rfl
  | cons a x ih => simp [serF, shlOp, ih]

theorem serF_shlOp_false (x y : List Bool) : serF shlOp false x y = shl x := serF_shlOp _ _ _

/-- **Subtraction with borrow**, on words of equal length. -/
theorem val_serF_fsOp (c : Bool) (x y : List Bool) (h : x.length = y.length) :
    (val (serF fsOp c x y) : ℤ) =
      val x - val y - c.toNat + 2 ^ x.length * (serC fsOp c x y).toNat := by
  induction x generalizing c y with
  | nil =>
    cases y with
    | nil => cases c <;> simp [serF, serC]
    | cons => simp at h
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      have h' : x.length = y.length := by simpa using h
      simp only [serF, serC, hd_cons, List.tail_cons, val_cons, List.length_cons]
      push_cast
      rw [ih _ y h', pow_succ]
      generalize serC fsOp (fsOp a b c).2 x y = C
      cases a <;> cases b <;> cases c <;> simp [fsOp] <;> ring

theorem serF_fsOp {x y : List Bool} (h : x.length = y.length) : serF fsOp false x y = subW x y := by
  apply eq_of_dec_eq (K := x.length) (by simp) (by simp)
  rw [dec_subW _ rfl h.symm]
  have hv := val_serF_fsOp false x y h
  simp only [Bool.toNat_false, Nat.cast_zero, sub_zero] at hv
  have hz : ((2 : ZMod (2 ^ x.length)) ^ x.length) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 ^ x.length)
  have := congrArg (fun z : ℤ => (z : ZMod (2 ^ x.length))) hv
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat, hz, zero_mul, add_zero] at this
  simp only [dec]
  exact this

/-- **The final borrow is the comparison.** -/
theorem serC_fsOp {x y : List Bool} (h : x.length = y.length) :
    serC fsOp false x y = decide (val x < val y) := by
  have hv := val_serF_fsOp false x y h
  have h1 := val_lt (serF fsOp false x y)
  have h2 := val_lt x
  have h3 := val_lt y
  rw [length_serF] at h1
  rw [← h] at h3
  have hP : (0 : ℤ) < 2 ^ x.length := by positivity
  have h1' : (val (serF fsOp false x y) : ℤ) < 2 ^ x.length := by exact_mod_cast h1
  have h2' : (val x : ℤ) < 2 ^ x.length := by exact_mod_cast h2
  have h3' : (val y : ℤ) < 2 ^ x.length := by exact_mod_cast h3
  simp only [Bool.toNat_false, Nat.cast_zero, sub_zero] at hv
  cases hC : serC fsOp false x y
  · simp only [hC, Bool.toNat_false, Nat.cast_zero, mul_zero, add_zero] at hv
    simp only [Bool.false_eq, decide_eq_false_iff_not, not_lt]
    have : (0 : ℤ) ≤ val (serF fsOp false x y) := by positivity
    exact_mod_cast (show (val y : ℤ) ≤ val x by linarith)
  · simp only [hC, Bool.toNat_true, Nat.cast_one, mul_one] at hv
    simp only [Bool.true_eq, decide_eq_true_eq]
    exact_mod_cast (show (val x : ℤ) < val y by linarith)

namespace Prog

/-! ### Relabelled programs with an update specification -/

theorem run_zipW_map {u : Fin 11 → Fin k} (hu : Function.Injective u) (g : SerOp) (c₀ : Bool)
    (s : Store k) (hs : ∀ i : Fin 11, 4 ≤ i.val → s (u i) = []) (h1 : s (u 1) = []) :
    run (map u (zipW g c₀)) s = Function.update s (u 0) (serF g c₀ (s (u 2)) (s (u 3))) :=
  run_map_eq_update hu _ s 0 _ (run_zipW g c₀ (s ∘ u) hs h1)

/-! ### Addition, subtraction, shift, comparison -/

/-- `0 := addW (s 2) (s 3)`. -/
def addP : Prog 11 := zipW faOp false
/-- `0 := subW (s 2) (s 3)` (inputs of equal length). -/
def subP : Prog 11 := zipW fsOp false
/-- `0 := shl (s 2)`. -/
def shlP : Prog 11 := zipW shlOp false
/-- `0 := [decide (val (s 2) < val (s 3))]` (inputs of equal positive length). -/
def ltP : Prog 11 := zipP fsOp false ⨾ cp 0 1 ⨾ clr 1

/-- The scratch tapes `1, 4, …, 10` of the arithmetic programs are blank. -/
def Clean11 (s : Store 11) : Prop := s 1 = [] ∧ ZipClean s

theorem run_addP (s : Store 11) (hs : Clean11 s) :
    run addP s = Function.update s 0 (addW (s 2) (s 3)) := by
  rw [addP, run_zipW _ _ s hs.2 hs.1, serF_faOp]; rfl

theorem run_subP (s : Store 11) (hs : Clean11 s) (h : (s 2).length = (s 3).length) :
    run subP s = Function.update s 0 (subW (s 2) (s 3)) := by
  rw [subP, run_zipW _ _ s hs.2 hs.1, serF_fsOp h]

theorem run_shlP (s : Store 11) (hs : Clean11 s) :
    run shlP s = Function.update s 0 (shl (s 2)) := by
  rw [shlP, run_zipW _ _ s hs.2 hs.1, serF_shlOp_false]

theorem run_ltP (s : Store 11) (hs : Clean11 s) (h : (s 2).length = (s 3).length) (h0 : s 2 ≠ []) :
    run ltP s = Function.update s 0 [decide (val (s 2) < val (s 3))] := by
  rw [ltP, run_seq, run_seq, run_zipP _ _ s hs.2, serC_fsOp h]
  simp only [h0, ↓reduceIte]
  funext t
  simp only [run_copy, run_clear, Function.update_apply]
  by_cases h0' : t = 0
  · subst h0'; simp
  · by_cases h1 : t = 1
    · subst h1; simp [hs.1]
    · simp [h0', h1]

/-! ### Multiplication -/

/-- The tapes of the adder inside `mulP`: `8 := addW (s 3) (s 4)`. -/
def mvAdd : Fin 11 → Fin 18 := ![8, 10, 3, 4, 11, 12, 13, 14, 15, 16, 17]
/-- The tapes of the doubling inside `mulP`: `8 := shl (s 4)`. -/
def mvShl : Fin 11 → Fin 18 := ![8, 10, 4, 9, 11, 12, 13, 14, 15, 16, 17]

theorem mvAdd_inj : Function.Injective mvAdd := by decide
theorem mvShl_inj : Function.Injective mvShl := by decide

/-- Tapes: `0` output, `1` `x`, `2` `y`; scratch `3` accumulator, `4` the shifted `x`, `5` the bits
of `y`, `6` a bit, `7` the counter, `8` a result, `9` blank, `10 … 17` the adder's scratch. -/
def mulInit : Prog 18 := cp 3 1 ⨾ setZero 3 ⨾ cp 4 1 ⨾ cp 5 2 ⨾ cp 7 2

/-- One round: if the next bit of `y` is set, add the shifted `x` to the accumulator; double the
shifted `x`. -/
def mulBody : Prog 18 :=
  pp 5 6 ⨾ ifBit 6 (map mvAdd addP ⨾ cp 3 8) (nop 3) ⨾ map mvShl shlP ⨾ cp 4 8 ⨾
    clr 6 ⨾ clr 8

def mulFin : Prog 18 := cp 0 3 ⨾ clr 3 ⨾ clr 4 ⨾ clr 5

/-- **Shift-and-add multiplication**: `0 := mulW (s 1) (s 2)`. -/
def mulP : Prog 18 := mulInit ⨾ loop 7 mulBody ⨾ mulFin

/-- The scratch tapes `3 … 17` of `mulP` are blank. -/
def MulClean (s : Store 18) : Prop := ∀ i : Fin 18, 3 ≤ i.val → s i = []

/-- The abstract round of `mulP`: (accumulator, shifted `x`, remaining bits of `y`). -/
def mstep : List Bool × List Bool × List Bool → List Bool × List Bool × List Bool
  | (acc, xs, ys) => (cond (hd ys) (addW acc xs) acc, shl xs, ys.tail)

def mulG (s : Store 18) : List Bool × List Bool × List Bool → Store 18
  | (acc, xs, ys) => Function.update (Function.update (Function.update s 3 acc) 4 xs) 5 ys

theorem mstep_iter {K : ℕ} : ∀ (ys acc xs : List Bool), acc.length = K → xs.length = K →
    ((mstep)^[ys.length] (acc, xs, ys)).1.length = K ∧
      dec K ((mstep)^[ys.length] (acc, xs, ys)).1 = dec K acc + dec K xs * (val ys : ZMod (2 ^ K))
  | [], acc, xs, ha, _ => by simp [ha]
  | y :: ys, acc, xs, ha, hx => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hacc : (cond y (addW acc xs) acc).length = K := by cases y <;> simp [ha]
    obtain ⟨h1, h2⟩ := mstep_iter ys (cond y (addW acc xs) acc) (shl xs) hacc (by simp [hx])
    simp only [mstep, hd_cons, List.tail_cons]
    refine ⟨h1, ?_⟩
    rw [h2, dec_shl K hx, val_cons]
    cases y
    · simp; ring
    · simp only [Bool.cond_true, dec_addW K ha, Bool.toNat_true]; push_cast; ring

theorem run_mulBody (s : Store 18) (hs : MulClean s) (a) (w : List Bool) :
    run mulBody (Function.update (mulG s a) 7 w) = Function.update (mulG s (mstep a)) 7 w := by
  obtain ⟨acc, xs, ys⟩ := a
  have hc : ∀ i : Fin 18, 6 ≤ i.val → i ≠ 7 → s i = [] := fun i hi _ => hs i (by omega)
  have hadd : ∀ t : Store 18, (∀ i : Fin 11, 4 ≤ i.val → t (mvAdd i) = []) → t (mvAdd 1) = [] →
      run (map mvAdd addP) t = Function.update t 8 (addW (t 3) (t 4)) := fun t h h1 =>
    (run_zipW_map mvAdd_inj _ _ t h h1).trans (by rw [serF_faOp]; rfl)
  have hshl : ∀ t : Store 18, (∀ i : Fin 11, 4 ≤ i.val → t (mvShl i) = []) → t (mvShl 1) = [] →
      run (map mvShl shlP) t = Function.update t 8 (shl (t 4)) := fun t h h1 =>
    (run_zipW_map mvShl_inj _ _ t h h1).trans (by rw [serF_shlOp_false]; rfl)
  simp only [mulBody, run_seq, run_pop, run_ifBit]
  split_ifs with hb
  · have hy : hd ys = true := by simpa [mulG] using hb
    rw [hadd _ ?_ ?_, hshl _ ?_ ?_]
    · funext t
      simp only [run_copy, run_clear, mulG, mstep, hy, Bool.cond_true]
      fin_cases t <;> simp [hc]
    all_goals first
      | (intro i hi; fin_cases i <;> simp_all [mvShl, mvAdd, mulG])
      | simp [mvShl, mvAdd, mulG, hc]
  · have hy : hd ys = false := by simpa [mulG] using hb
    simp only [run_nop]
    rw [hshl _ ?_ ?_]
    · funext t
      simp only [run_copy, run_clear, mulG, mstep, hy, Bool.cond_false]
      fin_cases t <;> simp [hc]
    all_goals first
      | (intro i hi; fin_cases i <;> simp_all [mvShl, mvAdd, mulG])
      | simp [mvShl, mulG, hc]

theorem run_mulP (s : Store 18) (hs : MulClean s) :
    run mulP s = Function.update s 0 (mulW (s 1) (s 2)) := by
  have hc : ∀ i : Fin 18, 3 ≤ i.val → s i = [] := hs
  have hinit : run mulInit s = Function.update (mulG s (zeroW (s 1).length, s 1, s 2)) 7 (s 2) := by
    funext t
    simp only [mulInit, mulG, run_seq, run_copy, run_setZero]
    fin_cases t <;> simp [zeroW]
  have hloop := run_loop_iter 7 mulBody (mulG s) mstep (fun _ => True)
    (fun a w _ => run_mulBody s hs a w) (fun _ _ => trivial) (s 2) (zeroW (s 1).length, s 1, s 2)
    trivial
  obtain ⟨hl, hd⟩ := mstep_iter (K := (s 1).length) (s 2) (zeroW (s 1).length) (s 1) (by simp) rfl
  have hres : ((mstep)^[(s 2).length] (zeroW (s 1).length, s 1, s 2)).1 = mulW (s 1) (s 2) := by
    apply eq_of_dec_eq hl (by simp)
    rw [hd, dec_mulW _ rfl, dec_zeroW, zero_add]; rfl
  rw [mulP, run_seq, run_seq, hinit, hloop]
  generalize hF : (mstep)^[(s 2).length] (zeroW (s 1).length, s 1, s 2) = F at hres
  obtain ⟨acc, xs, ys⟩ := F
  simp only at hres
  subst hres
  funext t
  simp only [mulFin, mulG, run_seq, run_copy, run_clear]
  fin_cases t <;> simp [hc]

/-! ### Membership in the fragment, bounds -/

theorem noGrow_addP : addP.NoGrow := rfl
theorem noGrow_subP : subP.NoGrow := rfl
theorem noGrow_shlP : shlP.NoGrow := rfl
theorem noGrow_ltP : ltP.NoGrow := rfl
theorem noGrow_mulP : mulP.NoGrow := rfl

theorem wf_addP : addP.WF := wf_of_wfB (by decide)
theorem wf_subP : subP.WF := wf_of_wfB (by decide)
theorem wf_shlP : shlP.WF := wf_of_wfB (by decide)
theorem wf_ltP : ltP.WF := wf_of_wfB (by decide)
theorem wf_mulP : mulP.WF := wf_of_wfB (by decide)

theorem bounds_addP (L : ℕ) : lenBound addP L = L ∧ timeBound addP L ≤ 113 * (L + 1) ^ 2 ∧
    size addP = 1270 := bounds_of _ noGrow_addP rfl rfl rfl L
theorem bounds_subP (L : ℕ) : lenBound subP L = L ∧ timeBound subP L ≤ 113 * (L + 1) ^ 2 ∧
    size subP = 1270 := bounds_of _ noGrow_subP rfl rfl rfl L
theorem bounds_shlP (L : ℕ) : lenBound shlP L = L ∧ timeBound shlP L ≤ 113 * (L + 1) ^ 2 ∧
    size shlP = 1270 := bounds_of _ noGrow_shlP rfl rfl rfl L
theorem bounds_ltP (L : ℕ) : lenBound ltP L = L ∧ timeBound ltP L ≤ 116 * (L + 1) ^ 2 ∧
    size ltP = 1306 := bounds_of _ noGrow_ltP rfl rfl rfl L
theorem bounds_mulP (L : ℕ) : lenBound mulP L = L ∧ timeBound mulP L ≤ 276 * (L + 1) ^ 3 ∧
    size mulP = 3120 := bounds_of _ noGrow_mulP rfl rfl rfl L

/-! ### Placed on any distinct tapes

`map u p` runs `p` on the tapes `u 0, u 1, …` of a machine with `k` tapes; every other tape is
preserved (`preserves_map_of_not_mem`). -/

section Placed

variable {u : Fin 11 → Fin k} (hu : Function.Injective u) (s : Store k)
  (hs : ∀ i : Fin 11, (i = 1 ∨ 4 ≤ i.val) → s (u i) = [])
include hu hs

omit hu in
theorem clean11_comp : Clean11 (s ∘ u) :=
  ⟨hs 1 (Or.inl rfl), fun i hi => hs i (Or.inr hi)⟩

/-- `u 0 := addW (s (u 2)) (s (u 3))`. -/
theorem law_addP_map :
    law (map u addP) s = PMF.pure (Function.update s (u 0) (addW (s (u 2)) (s (u 3)))) :=
  law_map_eq_update hu _ noGrow_addP s 0 _ (run_addP _ (clean11_comp s hs))

/-- `u 0 := subW (s (u 2)) (s (u 3))`. -/
theorem law_subP_map (h : (s (u 2)).length = (s (u 3)).length) :
    law (map u subP) s = PMF.pure (Function.update s (u 0) (subW (s (u 2)) (s (u 3)))) :=
  law_map_eq_update hu _ noGrow_subP s 0 _ (run_subP _ (clean11_comp s hs) h)

/-- `u 0 := shl (s (u 2))`. -/
theorem law_shlP_map :
    law (map u shlP) s = PMF.pure (Function.update s (u 0) (shl (s (u 2)))) :=
  law_map_eq_update hu _ noGrow_shlP s 0 _ (run_shlP _ (clean11_comp s hs))

/-- `u 0 := [decide (val (s (u 2)) < val (s (u 3)))]`. -/
theorem law_ltP_map (h : (s (u 2)).length = (s (u 3)).length) (h0 : s (u 2) ≠ []) :
    law (map u ltP) s =
      PMF.pure (Function.update s (u 0) [decide (val (s (u 2)) < val (s (u 3)))]) :=
  law_map_eq_update hu _ noGrow_ltP s 0 _ (run_ltP _ (clean11_comp s hs) h h0)

end Placed

/-- `u 0 := mulW (s (u 1)) (s (u 2))`. -/
theorem law_mulP_map {u : Fin 18 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 18, 3 ≤ i.val → s (u i) = []) :
    law (map u mulP) s = PMF.pure (Function.update s (u 0) (mulW (s (u 1)) (s (u 2)))) :=
  law_map_eq_update hu _ noGrow_mulP s 0 _ (run_mulP _ hs)

end Prog

end SigabaNeo.Tape
