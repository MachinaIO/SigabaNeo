import SigabaNeoStd.Lattices.ProgAlgo.Blocks
import SigabaNeoStd.Lattices.Algo.MersenneWords

/-!
# One's-complement residues modulo `2^K − 1` as tape programs

Residues are `K`-bit words read by `SigabaNeo.Lattices.Algo.decM` (any representative). Programs:

* `addGP g : Prog 12` (`0` output, `1` `2` inputs, scratch `3 … 11`): the transducer `g` twice, the
  second time with the final state of the first as initial state. With the full adder `faOp`,
  `addMP`: **`addMW x y`**, the addition with end-around carry (`run_addMP`); with `subOp` (the
  full adder on `x` and `¬y`), `subMP`: **`subMW x y`** (`run_subMP`).
* `notP : Prog 11` (`0` output, `1` input, scratch `2 … 10`): **`notW x`**, the negation
  (`run_notP`).
* `rotJP : Prog 5` (`0` output, `1` the word, `2` a word of length `j`; scratch `3` `4`):
  **`rot1^[j] x`**, the multiplication by `2^{−j}` (`run_rotJP`).
* `mulMB : Prog 18` (`0` output, `1` `2` inputs, scratch `3 … 17`): **`mulMW x y`**, the product
  (`run_mulMB`): per bit of `y`, a conditional `addMP` and a rotation.

The block programs (`BlockSpec`, for `bzip`): `addMB`, `subMB`, `rot1B`, `mulMB`.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-! ### The transducers -/

/-- The full adder on `x` and `¬y`. -/
def subOp : SerOp := fun x y c => faOp x (!y) c

/-- Bitwise NOT of the first input. -/
def notOp : SerOp := fun x _ c => (!x, c)

theorem val_addc_serC (c : Bool) (x y : List Bool) (h : x.length = y.length) :
    val (addc c x y) + 2 ^ x.length * (serC faOp c x y).toNat = val x + val y + c.toNat := by
  induction x generalizing c y with
  | nil =>
    cases y with
    | nil => cases c <;> simp [addc, serC]
    | cons => simp at h
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      have h' : x.length = y.length := by simpa using h
      have := ih ((a && b) || (c && (a || b))) y h'
      simp only [addc, serC, hd_cons, List.tail_cons, val_cons, List.length_cons, faOp, pow_succ]
      generalize 2 ^ x.length = P at this ⊢
      cases a <;> cases b <;> cases c <;> simp at this ⊢ <;> nlinarith

/-- **The final state of the adder is the carry.** -/
theorem serC_faOp {x y : List Bool} (h : x.length = y.length) :
    serC faOp false x y = carryW x y := by
  have hv := val_addc_serC false x y h
  have hr := val_lt (addc false x y)
  rw [length_addc] at hr
  unfold carryW
  cases hC : serC faOp false x y
  · simp [hC] at hv
    simp only [Bool.false_eq, decide_eq_false_iff_not, not_le]
    omega
  · simp [hC] at hv
    simp only [Bool.true_eq, decide_eq_true_eq]
    omega

theorem serF_subOp (c : Bool) {x y : List Bool} (h : x.length ≤ y.length) :
    serF subOp c x y = serF faOp c x (notW y) := by
  induction x generalizing c y with
  | nil => rfl
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp only [serF, subOp, hd_cons, List.tail_cons, notW, List.map_cons]
      rw [ih _ (by simpa using h)]
      rfl

theorem serC_subOp (c : Bool) {x y : List Bool} (h : x.length ≤ y.length) :
    serC subOp c x y = serC faOp c x (notW y) := by
  induction x generalizing c y with
  | nil => rfl
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp only [serC, subOp, hd_cons, List.tail_cons, notW, List.map_cons]
      rw [ih _ (by simpa using h)]
      rfl

theorem serF_notOp (c : Bool) (x y : List Bool) : serF notOp c x y = notW x := by
  induction x generalizing c y with
  | nil => rfl
  | cons a x ih => simp [serF, notOp, ih, notW]

namespace Prog

open scoped Prog

/-! ### Addition and subtraction with end-around carry -/

def uA : Fin 11 → Fin 12 := ![0, 3, 1, 2, 4, 5, 6, 7, 8, 9, 10]
def uB : Fin 11 → Fin 12 := ![0, 11, 1, 2, 4, 5, 6, 7, 8, 9, 10]
theorem uA_inj : Function.Injective uA := by decide
theorem uB_inj : Function.Injective uB := by decide

/-- The transducer `g` from the state `false`, then again from its final state (tape `3`). -/
def addGP (g : SerOp) : Prog 12 :=
  map uA (zipP g false) ⨾ br 3 (fun c => map uB (zipW g c)) ⨾ clr 3

/-- The scratch tapes `3 … 11` are blank. -/
def Clean12 (s : Store 12) : Prop := ∀ i : Fin 12, 3 ≤ i.val → s i = []

theorem run_addGP (g : SerOp) (s : Store 12) (hs : Clean12 s) :
    run (addGP g) s =
      Function.update s 0 (serF g (serC g false (s 1) (s 2)) (s 1) (s 2)) := by
  have hz : run (map uA (zipP g false)) s = Function.update (Function.update s 0
      (serF g false (s 1) (s 2))) 3 (if s 1 = [] then [] else [serC g false (s 1) (s 2)]) := by
    rw [run_map uA_inj, run_zipP _ _ _ (fun i hi => by fin_cases i <;> simp_all [uA, Clean12]),
      extend_update uA_inj, extend_update uA_inj, extend_comp_self]
    rfl
  simp only [addGP, run_seq, hz, run_br]
  set c := hd (Function.update (Function.update s 0 (serF g false (s 1) (s 2))) 3
    (if s 1 = [] then [] else [serC g false (s 1) (s 2)]) 3)
  rw [run_zipW_map uB_inj _ _ _ (fun i hi => by fin_cases i <;> simp_all [uB, Clean12])
    (by simp [uB, hs 11 (by decide)])]
  have hc : serF g c (s 1) (s 2) = serF g (serC g false (s 1) (s 2)) (s 1) (s 2) := by
    by_cases h1 : s 1 = []
    · rw [h1]; rfl
    · simp [c, h1]
  funext t
  simp only [run_clear]
  fin_cases t <;> simp [uB, hc, hs 3 (by decide)]

/-- **Addition with end-around carry.** -/
def addMP : Prog 12 := addGP faOp
/-- **Subtraction**: `x + ¬y` with end-around carry. -/
def subMP : Prog 12 := addGP subOp

theorem run_addMP (s : Store 12) (hs : Clean12 s) (h : (s 1).length = (s 2).length) :
    run addMP s = Function.update s 0 (addMW (s 1) (s 2)) := by
  rw [addMP, run_addGP _ _ hs, serC_faOp h, serF_faOp]; rfl

theorem run_subMP (s : Store 12) (hs : Clean12 s) (h : (s 1).length = (s 2).length) :
    run subMP s = Function.update s 0 (subMW (s 1) (s 2)) := by
  rw [subMP, run_addGP _ _ hs, serC_subOp _ h.le, serF_subOp _ h.le,
    serC_faOp (by simp [h]), serF_faOp]; rfl

theorem run_addMP_map {u : Fin 12 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 12, 3 ≤ i.val → s (u i) = []) (h : (s (u 1)).length = (s (u 2)).length) :
    run (map u addMP) s = Function.update s (u 0) (addMW (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_addMP _ hs h)

theorem run_subMP_map {u : Fin 12 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 12, 3 ≤ i.val → s (u i) = []) (h : (s (u 1)).length = (s (u 2)).length) :
    run (map u subMP) s = Function.update s (u 0) (subMW (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_subMP _ hs h)

/-! ### Negation -/

def uN : Fin 11 → Fin 11 := ![0, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10]
theorem uN_inj : Function.Injective uN := by decide

/-- **Negation**: `0 := notW (s 1)` (scratch `2 … 10`). -/
def notP : Prog 11 := map uN (zipW notOp false)

theorem run_notP (s : Store 11) (hs : ∀ i : Fin 11, 2 ≤ i.val → s i = []) :
    run notP s = Function.update s 0 (notW (s 1)) := by
  rw [notP, run_zipW_map uN_inj _ _ _ (fun i hi => by fin_cases i <;> simp_all [uN])
    (by simp [uN, hs 2 (by decide)]), serF_notOp]
  rfl

theorem run_notP_map {u : Fin 11 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 11, 2 ≤ i.val → s (u i) = []) :
    run (map u notP) s = Function.update s (u 0) (notW (s (u 1))) :=
  run_map_eq_update hu _ s 0 _ (run_notP _ hs)

/-! ### Rotations -/

theorem push_take_one (w : List Bool) : (w ++ [hd w]).tail = rot1 w := by
  cases w <;> simp [rot1]

/-- One rotation of tape `0` in place (tape `1` a blank bit). -/
def rotStep : Prog 2 := takeHead 1 0 ⨾ push 0 1 ⨾ clr 1

theorem run_rotStep (s : Store 2) (h1 : s 1 = []) :
    run rotStep s = Function.update s 0 (rot1 (s 0)) := by
  funext t
  simp only [rotStep, run_seq, run_takeHead, run_push, run_clear]
  fin_cases t <;> simp [h1, push_take_one]

theorem run_rotStep_map {u : Fin 2 → Fin k} (hu : Function.Injective u) (s : Store k)
    (h1 : s (u 1) = []) :
    run (map u rotStep) s = Function.update s (u 0) (rot1 (s (u 0))) :=
  run_map_eq_update hu _ s 0 _ (run_rotStep _ h1)

def vRot : Fin 2 → Fin 5 := ![0, 4]
theorem vRot_inj : Function.Injective vRot := by decide

/-- **`0 := rot1^[|s 2|] (s 1)`**, the multiplication by `2^{−j}` (scratch `3` `4`). -/
def rotJP : Prog 5 := cp 0 1 ⨾ forN 3 2 (map vRot rotStep)

theorem run_rotJP (s : Store 5) (h3 : s 3 = []) (h4 : s 4 = []) :
    run rotJP s = Function.update s 0 (rot1^[(s 2).length] (s 1)) := by
  have h := run_forN 3 2 (map vRot rotStep) (fun w => Function.update s 0 w) rot1
    (fun w c => by
      rw [run_rotStep_map vRot_inj _ (by simp [vRot, h4])]
      funext t; fin_cases t <;> simp [vRot]) (s 1) (Function.update s 0 (s 1))
    (by funext t; fin_cases t <;> simp)
  rw [rotJP, run_seq, run_copy, h]
  funext t; fin_cases t <;> simp [h3]

theorem run_rotJP_map {u : Fin 5 → Fin k} (hu : Function.Injective u) (s : Store k)
    (h3 : s (u 3) = []) (h4 : s (u 4) = []) :
    run (map u rotJP) s = Function.update s (u 0) (rot1^[(s (u 2)).length] (s (u 1))) :=
  run_map_eq_update hu _ s 0 _ (run_rotJP _ h3 h4)

/-! ### Multiplication -/

/-- The tapes of the adder inside `mulMB`: `7 := addMW (s 3) (s 1)`. -/
def vAM : Fin 12 → Fin 18 := ![7, 3, 1, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def vRM : Fin 2 → Fin 18 := ![3, 17]
theorem vAM_inj : Function.Injective vAM := by decide
theorem vRM_inj : Function.Injective vRM := by decide

/-- Tapes: `0` output, `1` `x`, `2` `y`; scratch `3` the accumulator, `4` the bits of `y`, `5` the
counter, `6` a bit, `7` a sum, `8 … 16` the adder's scratch, `17` a bit. -/
def mulInitM : Prog 18 := cp 3 1 ⨾ setZero 3 ⨾ cp 4 2 ⨾ cp 5 2

/-- One round: if the next bit of `y` is set, add `x` to the accumulator; rotate it. -/
def mulBodyM : Prog 18 :=
  pp 4 6 ⨾ ifBit 6 (map vAM addMP ⨾ cp 3 7 ⨾ clr 7) (nop 3) ⨾ map vRM rotStep ⨾ clr 6

def mulFinM : Prog 18 := cp 0 3 ⨾ clr 3 ⨾ clr 4

/-- **One's-complement multiplication**: `0 := mulMW (s 1) (s 2)`. -/
def mulMB : Prog 18 := mulInitM ⨾ loop 5 mulBodyM ⨾ mulFinM

/-- The abstract round: (accumulator, remaining bits of `y`). -/
def mstepM (x : List Bool) : List Bool × List Bool → List Bool × List Bool
  | (acc, ys) => (rot1 (cond (hd ys) (addMW acc x) acc), ys.tail)

def mulMG (s : Store 18) : List Bool × List Bool → Store 18
  | (acc, ys) => Function.update (Function.update s 3 acc) 4 ys

theorem mstepM_iter (x : List Bool) : ∀ (ys acc : List Bool),
    (mstepM x)^[ys.length] (acc, ys) = (mulAcc x acc ys, [])
  | [], acc => rfl
  | b :: ys, acc => by
    rw [List.length_cons, Function.iterate_succ_apply]
    exact mstepM_iter x ys _

set_option linter.unusedSimpArgs false in
theorem run_mulBodyM (s : Store 18) (hs : MulClean s) (a) (ha : a.1.length = (s 1).length)
    (w : List Bool) :
    run mulBodyM (Function.update (mulMG s a) 5 w) =
      Function.update (mulMG s (mstepM (s 1) a)) 5 w := by
  obtain ⟨acc, ys⟩ := a
  simp only at ha
  have hc : ∀ i : Fin 18, 6 ≤ i.val → i ≠ 5 → s i = [] := fun i hi _ => hs i (by omega)
  simp only [mulBodyM, run_seq, run_pop, run_ifBit]
  split_ifs with hb
  · have hy : hd ys = true := by simpa [mulMG] using hb
    rw [run_addMP_map vAM_inj _ ?_ ?_, run_rotStep_map vRM_inj _ ?_]
    · funext t
      simp only [run_copy, run_clear, mulMG, mstepM, hy, Bool.cond_true]
      fin_cases t <;> simp [hc, vAM, vRM]
    all_goals first
      | (intro i hi; fin_cases i <;> simp_all [vAM, vRM, mulMG])
      | simp [vAM, vRM, mulMG, hc, ha]
  · have hy : hd ys = false := by simpa [mulMG] using hb
    simp only [run_nop]
    rw [run_rotStep_map vRM_inj _ ?_]
    · funext t
      simp only [run_clear, mulMG, mstepM, hy, Bool.cond_false]
      fin_cases t <;> simp [hc, vRM]
    simp [vRM, mulMG, hc]

theorem run_mulMB (s : Store 18) (hs : MulClean s) :
    run mulMB s = Function.update s 0 (mulMW (s 1) (s 2)) := by
  have hc : ∀ i : Fin 18, 3 ≤ i.val → s i = [] := hs
  have hinit : run mulInitM s =
      Function.update (mulMG s (zeroW (s 1).length, s 2)) 5 (s 2) := by
    funext t
    simp only [mulInitM, mulMG, run_seq, run_copy, run_setZero]
    fin_cases t <;> simp [zeroW]
  have hloop := run_loop_iter 5 mulBodyM (mulMG s) (mstepM (s 1))
    (fun a => a.1.length = (s 1).length) (fun a w ha => run_mulBodyM s hs a ha w)
    (fun a ha => by
      obtain ⟨acc, ys⟩ := a
      simp only [mstepM, length_rot1] at ha ⊢
      cases hd ys <;> simp [ha])
    (s 2) (zeroW (s 1).length, s 2) (by simp)
  rw [mulMB, run_seq, run_seq, hinit, hloop, mstepM_iter]
  funext t
  simp only [mulFinM, mulMG, run_seq, run_copy, run_clear]
  fin_cases t <;> simp [hc, mulMW]

theorem run_mulMB_map {u : Fin 18 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 18, 3 ≤ i.val → s (u i) = []) :
    run (map u mulMB) s = Function.update s (u 0) (mulMW (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_mulMB _ hs)

/-! ### Block programs -/

/-- `Fin 12` inside `Fin 18`. -/
def e12 : Fin 12 → Fin 18 := Fin.castLE (by decide)
theorem e12_inj : Function.Injective e12 := Fin.castLE_injective _

def addMB : Prog 18 := map e12 addMP
def subMB : Prog 18 := map e12 subMP
/-- `0 := rot1 (s 1)`. -/
def rot1B : Prog 18 := cp 0 1 ⨾ map ![0, 3] rotStep

theorem blockSpec_addMB (K : ℕ) : BlockSpec K addMB addMW := fun t ht h1 h2 =>
  run_addMP_map e12_inj t (fun i hi => ht _ (by simp [e12]; omega)) (by simp [e12, h1, h2])

theorem blockSpec_subMB (K : ℕ) : BlockSpec K subMB subMW := fun t ht h1 h2 =>
  run_subMP_map e12_inj t (fun i hi => ht _ (by simp [e12]; omega)) (by simp [e12, h1, h2])

theorem blockSpec_mulMB (K : ℕ) : BlockSpec K mulMB mulMW := fun t ht _ _ => run_mulMB t ht

theorem blockSpec_rot1B (K : ℕ) : BlockSpec K rot1B (fun x _ => rot1 x) := fun t ht _ _ => by
  rw [rot1B, run_seq, run_copy, run_rotStep_map (by decide) _ (by simp [ht 3 (by decide)])]
  funext i; fin_cases i <;> simp

/-! ### Membership in the fragment -/

theorem noGrow_addMP : addMP.NoGrow := rfl
theorem noGrow_subMP : subMP.NoGrow := rfl
theorem noGrow_notP : notP.NoGrow := rfl
theorem noGrow_rotJP : rotJP.NoGrow := rfl
theorem noGrow_mulMB : mulMB.NoGrow := rfl
theorem wf_addMP : addMP.WF := wf_of_wfB (by decide)
theorem wf_subMP : subMP.WF := wf_of_wfB (by decide)
theorem wf_notP : notP.WF := wf_of_wfB (by decide)
theorem wf_rotJP : rotJP.WF := wf_of_wfB (by decide)
theorem wf_mulMB : mulMB.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
