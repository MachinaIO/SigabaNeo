import PE.Impl.Gates.BPCircuit
import PE.Impl.Gates.Eval
import Mathlib.Data.Set.Finite.List

/-!
# The predicate word of a branching program, and `Eval`

**The word** (`bpWord F`, `bpLen = 15 · 2^40 · 32 + 2^40 = 481 · 2^40` bits): the 15 transition
tables, then the output table. Entry `(z, a)` of table `i` is at index `2^40 i + 256 z + a`, as 32
bits, most significant first (`entryIdx`); the output bit `(z, a)` is at
`outOff + 256 z + a`, `outOff = 15 · 2^45`. `tablesOf C` reads a word back (`tablesOf_bpWord`),
and every word of `bpLen` bits is the word of the program it reads (`bpWord_tablesOf`).

**Attributes.** `attrOf w` reads 16 symbols of 8 bits, most significant first: the inverse of
`encAttr` (`attrOf_encAttr`), onto the words of 128 bits (`encAttr_onto`). `card_attr`:
`2^128` attributes.

**`Eval`** (`bpEvalMachine`): on `(pw, C, x)`, `[true]` iff `C` has `bpLen` bits, `x` has 128
bits and `output (tablesOf C) (attrOf x) = false`; it is constant outside finitely many inputs,
so a machine by `Machine.exists_of_almostConst`. `bp_authorized_iff`: `C` is authorized for `x` iff
`C.length = bpLen` and `output (tablesOf C) x = false`. `expressive_bp`: the implementation is
expressive, with `bpWord F` for `F`.
-/

namespace AdvancedEncryption.PE.Gates.BPWord

open SigabaNeo SigabaNeo.Lattices AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates

/-! ### The word -/

/-- The length of a predicate word. -/
def bpLen : ℕ := 481 * 2 ^ 40

/-- The offset of the output table. -/
def outOff : ℕ := 15 * 2 ^ 45

/-- The index of entry `(z, a)` of table `i`. -/
def entryIdx (i : Fin 15) (z : State) (a : Sym) : ℕ := 2 ^ 40 * i.val + 256 * z.val + a.val

/-- The 32-bit number at bit `p`, most significant first. -/
def readNum (C : List Bool) (p : ℕ) : State :=
  ⟨MuxTree.idx (fun ℓ => C.getD (p + (32 - ℓ)) false) 32, MuxTree.idx_lt _ _⟩

/-- **The program of a word.** -/
def tablesOf (C : List Bool) : BP where
  step i z a := readNum C (32 * entryIdx i z a)
  out z a := C.getD (outOff + 256 * z.val + a.val) false

/-- Bit `k` of the word of `F`. -/
def wordBit (F : BP) (k : ℕ) : Bool :=
  if h : k < outOff then
    F.step ⟨k / 32 / 2 ^ 40, by unfold outOff at h; omega⟩
      ⟨k / 32 % 2 ^ 40 / 256, by omega⟩ ⟨k / 32 % 256, by omega⟩ |>.val.testBit (31 - k % 32)
  else if h' : k - outOff < 2 ^ 40 then
    F.out ⟨(k - outOff) / 256, by omega⟩ ⟨(k - outOff) % 256, by omega⟩
  else false

/-- **The word of a program.** -/
def bpWord (F : BP) : List Bool := List.ofFn fun k : Fin bpLen => wordBit F k

theorem length_bpWord (F : BP) : (bpWord F).length = bpLen := List.length_ofFn

theorem getD_bpWord (F : BP) {k : ℕ} (hk : k < bpLen) : (bpWord F).getD k false = wordBit F k := by
  rw [bpWord, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn]

theorem readNum_bpWord (F : BP) (i : Fin 15) (z : State) (a : Sym) :
    readNum (bpWord F) (32 * entryIdx i z a) = F.step i z a := by
  have hi := i.isLt; have hz := z.isLt; have ha := a.isLt
  apply Fin.ext
  simp only [readNum]
  rw [MuxTree.idx_congr _ (fun ℓ => (F.step i z a).val.testBit (ℓ - 1)) 32 (fun ℓ h1 h2 => ?_),
    MuxTree.idx_testBit, Nat.mod_eq_of_lt (F.step i z a).isLt]
  have hk : 32 * entryIdx i z a + (32 - ℓ) < outOff := by unfold entryIdx outOff; omega
  rw [getD_bpWord F (by unfold bpLen; unfold outOff at hk; omega), wordBit, dif_pos hk]
  have e1 : (32 * entryIdx i z a + (32 - ℓ)) / 32 = entryIdx i z a := by omega
  have e2 : (32 * entryIdx i z a + (32 - ℓ)) % 32 = 32 - ℓ := by omega
  simp only [e1, e2]
  have f1 : entryIdx i z a / 2 ^ 40 = i.val := by unfold entryIdx; omega
  have f2 : entryIdx i z a % 2 ^ 40 / 256 = z.val := by unfold entryIdx; omega
  have f3 : entryIdx i z a % 256 = a.val := by unfold entryIdx; omega
  simp only [f1, f2, f3, show 31 - (32 - ℓ) = ℓ - 1 by omega]

/-- **A word reads back its program.** -/
theorem tablesOf_bpWord (F : BP) : tablesOf (bpWord F) = F := by
  obtain ⟨step, out⟩ := F
  simp only [tablesOf, BP.mk.injEq]
  refine ⟨funext fun i => funext fun z => funext fun a => readNum_bpWord ⟨step, out⟩ i z a,
    funext fun z => funext fun a => ?_⟩
  have hz := z.isLt; have ha := a.isLt
  have hk : outOff + 256 * z.val + a.val < bpLen := by unfold outOff bpLen; omega
  rw [getD_bpWord _ hk, wordBit, dif_neg (by omega), dif_pos (by omega)]
  exact congrArg₂ out
    (Fin.ext (show (outOff + 256 * z.val + a.val - outOff) / 256 = z.val by omega))
    (Fin.ext (show (outOff + 256 * z.val + a.val - outOff) % 256 = a.val by omega))

/-- **Every word of `bpLen` bits is the word of a program.** -/
theorem bpWord_tablesOf (C : List Bool) (hC : C.length = bpLen) : bpWord (tablesOf C) = C := by
  apply List.ext_getElem (by rw [length_bpWord, hC])
  intro k h1 h2
  have hk : k < bpLen := hC ▸ h2
  rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem C false h2, getD_bpWord _ hk]
  unfold wordBit
  split_ifs with ha hb
  · simp only [tablesOf, readNum, MuxTree.testBit_idx]
    have he : entryIdx ⟨k / 32 / 2 ^ 40, by unfold outOff at ha; omega⟩
        ⟨k / 32 % 2 ^ 40 / 256, by omega⟩ ⟨k / 32 % 256, by omega⟩ = k / 32 := by
      unfold entryIdx; simp only; omega
    rw [he]
    simp only [show 31 - k % 32 < 32 by omega, decide_true, Bool.true_and]
    exact congrArg (C.getD · false) (show 32 * (k / 32) + (32 - (31 - k % 32 + 1)) = k by omega)
  · simp only [tablesOf]
    exact congrArg (C.getD · false)
      (show outOff + 256 * ((k - outOff) / 256) + (k - outOff) % 256 = k by omega)
  · exfalso; unfold bpLen at hk; unfold outOff at ha hb; omega

/-! ### Attributes -/

/-- The attribute of a word: 16 symbols of 8 bits, most significant first. -/
def attrOf (w : List Bool) : Attr := fun i =>
  ⟨MuxTree.idx (fun ℓ => w.getD (8 * i.val + (8 - ℓ)) false) 8, MuxTree.idx_lt _ _⟩

theorem getD_encAttr (x : Attr) {i m : ℕ} (hi : i < 16) (hm : m < 8) :
    (encAttr x).getD (8 * i + m) false = (x ⟨i, hi⟩).val.testBit (7 - m) := by
  have := bitsOfBP_inIdx x hi hm
  unfold bitsOfBP at this
  rwa [show (inIdx i m).val = 8 * i + m by simp only [inIdx]; omega] at this

theorem attrOf_encAttr (x : Attr) : attrOf (encAttr x) = x := by
  funext i
  apply Fin.ext
  simp only [attrOf]
  rw [MuxTree.idx_congr _ (fun ℓ => (x i).val.testBit (ℓ - 1)) 8 (fun ℓ h1 h2 => ?_),
    MuxTree.idx_testBit, Nat.mod_eq_of_lt (show (x i).val < 2 ^ 8 from (x i).isLt)]
  rw [getD_encAttr x i.isLt (by omega), show 7 - (8 - ℓ) = ℓ - 1 by omega]

/-- **Every word of 128 bits is an attribute.** -/
theorem encAttr_onto (w : List Bool) (hw : w.length = 128) : encAttr (attrOf w) = w := by
  apply List.ext_getElem (by rw [length_encAttr, hw])
  intro k h1 h2
  rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2]
  have hk : k < 128 := hw ▸ h2
  have e : k = 8 * (k / 8) + k % 8 := by omega
  rw [e, getD_encAttr _ (by omega) (by omega)]
  simp only [attrOf, MuxTree.testBit_idx]
  simp only [show 7 - k % 8 < 8 by omega, decide_true, Bool.true_and]
  congr 1; omega

theorem encAttr_surj (w : List Bool) (hw : w.length = 128) : ∃ x : Attr, encAttr x = w :=
  ⟨attrOf w, encAttr_onto w hw⟩

/-- `2^128` attributes. -/
theorem card_attr : Fintype.card Attr = 2 ^ 128 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; norm_num

/-! ### `Eval` -/

/-- `Eval` on `(pw, C, x)`: authorized iff `C` has `bpLen` bits, `x` has 128 bits, and the
program of `C` outputs `0` on the attribute of `x`. -/
def bpEvalFun (xs : List (List Bool)) : List (List Bool) :=
  [[decide (xs = [paramsWord bpUniverse params, xs.getD 1 [], xs.getD 2 []]) &&
    decide ((xs.getD 1 []).length = bpLen) && decide ((xs.getD 2 []).length = 128) &&
    !output (tablesOf (xs.getD 1 [])) (attrOf (xs.getD 2 []))]]

theorem bpEvalFun_almostConst : ∃ b, {xs | bpEvalFun xs ≠ b}.Finite := by
  refine ⟨[[false]], Set.Finite.subset
    (((List.finite_length_le Bool bpLen).prod (List.finite_length_le Bool 128)).image
      fun p => [paramsWord bpUniverse params, p.1, p.2]) fun xs hxs => ?_⟩
  by_cases h : xs = [paramsWord bpUniverse params, xs.getD 1 [], xs.getD 2 []] ∧
      (xs.getD 1 []).length = bpLen ∧ (xs.getD 2 []).length = 128
  · exact ⟨(xs.getD 1 [], xs.getD 2 []), ⟨h.2.1.le, h.2.2.le⟩, h.1.symm⟩
  · exfalso; apply hxs
    have hf : (decide (xs = [paramsWord bpUniverse params, xs.getD 1 [], xs.getD 2 []]) &&
        decide ((xs.getD 1 []).length = bpLen) && decide ((xs.getD 2 []).length = 128)) = false := by
      rw [← Bool.decide_and, ← Bool.decide_and]
      exact decide_eq_false (fun h' => h ⟨h'.1.1, h'.1.2, h'.2⟩)
    unfold bpEvalFun
    rw [hf, Bool.false_and]

/-- **The machine of `Eval`** for branching programs. -/
noncomputable def bpEvalMachine : Machine :=
  Classical.choose (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    bpEvalFun_almostConst)

theorem bpEvalMachine_deterministic : bpEvalMachine.Deterministic :=
  (Classical.choose_spec (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    bpEvalFun_almostConst)).1

theorem bpEvalMachine_run (xs : List (List Bool)) :
    bpEvalMachine.run (encodeTuple xs) = PMF.pure (encodeTuple (bpEvalFun xs)) :=
  (Classical.choose_spec (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    bpEvalFun_almostConst)).2 xs

/-- **Authorization**: `C` is authorized for `x` iff it is a predicate word and its program
outputs `0` on `x`. -/
theorem bp_authorized_iff (impl : Impl sig) (h : impl.machine .eval = bpEvalMachine)
    (C : List Bool) (x : Attr) : Authorized (U := bpUniverse) params impl C x ↔
      C.length = bpLen ∧ output (tablesOf C) x = false := by
  have he : eval (U := bpUniverse) params impl C x =
      PMF.pure ((bpEvalFun [paramsWord bpUniverse params, C, encAttr x]).getD 0 []) := by
    unfold eval Impl.run
    rw [h, bpEvalMachine_run, PMF.pure_map, PMF.pure_map]
    have : (sig Alg.eval).outputs.length =
        (bpEvalFun [paramsWord bpUniverse params, C, encAttr x]).length := rfl
    rw [this]
    exact congrArg (fun l => PMF.pure (List.getD l 0 []))
      (decodeTuple_encodeTuple (bpEvalFun [paramsWord bpUniverse params, C, encAttr x]))
  unfold Authorized
  rw [he, PMF.pure_apply]
  have hx : (encAttr x).length = 128 := length_encAttr x
  simp only [bpEvalFun, List.getD_cons_zero, List.getD_cons_succ, hx, attrOf_encAttr,
    decide_true, Bool.and_true, Bool.true_and]
  by_cases hC : C.length = bpLen
  · by_cases ho : output (tablesOf C) x = false
    · simp [hC, ho]
    · simp [hC, ho]
  · simp [hC]

/-- **Expressiveness**: the word of `F` is authorized exactly where `F` outputs `0`. -/
theorem expressive_bp (impl : Impl sig) (h : impl.machine .eval = bpEvalMachine) :
    Expressive bpUniverse params impl := by
  intro (F : BP)
  refine ⟨bpWord F, fun (x : Attr) => ?_⟩
  rw [bp_authorized_iff impl h, tablesOf_bpWord]
  exact ⟨fun h => h.2, fun h' => ⟨length_bpWord F, h'⟩⟩

/-- The circuit of the program of a word computes its output. -/
theorem evalBool_bpPred_tablesOf (C : List Bool) (x : Attr) :
    SLP.evalBool (bitsOfBP x) (bpPred (tablesOf C)).1 (bpPred (tablesOf C)).2 =
      output (tablesOf C) x :=
  evalBool_bpPred _ x

end AdvancedEncryption.PE.Gates.BPWord
