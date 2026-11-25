import SigabaNeoStd.Lattices.ProgAlgo.FhatGenSub

/-!
# Generating gate tapes: index arithmetic and list access

`maddC d m c t` (`d := d · m + c`), `fetchC d l i lt` (`d :=` the element `i` of the list `l`),
`sliceC dst l s cnt lt` (`dst :=` the elements `s … s + cnt - 1` of `l`). All are nand-free.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP

variable {E : Env}

/-! ### `d := d · m + c` -/

/-- `d := d · m + c`, with the scratch `t`. -/
def maddC (d m c t : SR) : Code :=
  .seq (.mov t d) (.seq (.zero d) (.seq (.rep m (.add d t)) (.add d c)))

theorem iter_add (d t : SR) (hdt : d ≠ t) : ∀ (j : ℕ) (σ : St), σ.sc d + j * σ.sc t ≤ E.M →
    (exec E (.add d t))^[j] σ = { σ with sc := Function.update σ.sc d (σ.sc d + j * σ.sc t) }
  | 0, σ, _ => by simp
  | j + 1, σ, h => by
    rw [Function.iterate_succ_apply]
    have e : exec E (.add d t) σ = { σ with sc := Function.update σ.sc d (σ.sc d + σ.sc t) } := by
      simp only [exec]; rw [min_eq_left (by nlinarith)]
    rw [e, iter_add d t hdt j _ (by simp [Function.update_of_ne hdt.symm]; nlinarith)]
    simp only [Function.update_self, Function.update_of_ne hdt.symm, Function.update_idem]
    rw [show σ.sc d + σ.sc t + j * σ.sc t = σ.sc d + (j + 1) * σ.sc t by ring]

theorem exec_maddC (d m c t : SR) (hdm : d ≠ m) (hdc : d ≠ c) (hdt : d ≠ t) (htm : t ≠ m)
    (htc : t ≠ c) (σ : St) (hM : σ.sc d * σ.sc m + σ.sc c ≤ E.M) :
    exec E (maddC d m c t) σ = setSL σ (Function.update (Function.update σ.sc t (σ.sc d)) d
      (σ.sc d * σ.sc m + σ.sc c)) σ.ls := by
  simp only [maddC, exec_seq]
  have e1 : exec E (.zero d) (exec E (.mov t d) σ) =
      { σ with sc := Function.update (Function.update σ.sc t (σ.sc d)) d 0 } := rfl
  rw [e1, exec_rep]
  simp only [Function.update_of_ne hdm.symm, Function.update_of_ne htm.symm]
  rw [iter_add d t hdt _ _ (by simp [Function.update_of_ne hdt.symm]; nlinarith)]
  simp only [exec, Function.update_self, Function.update_of_ne hdt.symm, Function.update_idem,
    Function.update_of_ne hdc.symm, Function.update_of_ne htc.symm, Nat.zero_add]
  rw [min_eq_left (by nlinarith)]
  simp only [setSL]
  rw [Nat.mul_comm (σ.sc m)]

/-! ### Dropping, fetching, slicing -/

/-- Drop `|i|` elements of `lt` (through the register `41`). -/
def dropC (i : SR) (lt : LR) : Code := .rep i (.lpop 41 lt)

theorem iter_drop (lt : LR) : ∀ (j : ℕ) (σ : St), ∃ sc',
    (exec E (.lpop 41 lt))^[j] σ = setSL σ sc' (Function.update σ.ls lt ((σ.ls lt).drop j)) ∧
      Fr [41] σ.sc sc'
  | 0, σ => ⟨σ.sc, by simp [setSL], Fr.refl _ _⟩
  | j + 1, σ => by
    obtain ⟨sc', h, f⟩ := iter_drop lt j (exec E (.lpop 41 lt) σ)
    refine ⟨sc', ?_, fun r hr => (f r hr).trans ?_⟩
    · rw [Function.iterate_succ_apply, h]
      simp [exec, setSL, List.drop_tail, Nat.add_comm]
    · simp only [exec]; exact Function.update_of_ne (by simpa using hr) _ _

/-- `d :=` the element `i` of `l` (`0` if none), through the scratch list `lt`. -/
def fetchC (d : SR) (l : LR) (i : SR) (lt : LR) : Code :=
  .seq (.lmov lt l) (.seq (dropC i lt) (.lpop d lt))

theorem exec_fetchC (d : SR) (l : LR) (i : SR) (lt : LR) (σ : St) :
    ∃ sc', exec E (fetchC d l i lt) σ = setSL σ sc'
        (Function.update σ.ls lt (((σ.ls l).drop (σ.sc i)).tail)) ∧
      sc' d = (σ.ls l).getD (σ.sc i) 0 ∧ Fr [41, d] σ.sc sc' := by
  simp only [fetchC, exec_seq, dropC, exec_rep]
  obtain ⟨sc', h, f⟩ := iter_drop (E := E) lt (σ.sc i) (exec E (.lmov lt l) σ)
  rw [show (exec E (.lmov lt l) σ).sc i = σ.sc i from rfl, h]
  refine ⟨Function.update sc' d ((σ.ls l).getD (σ.sc i) 0), ?_, by simp, ?_⟩
  · simp [exec, setSL, List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
  · intro r hr
    simp only [List.mem_cons, not_or] at hr
    rw [Function.update_of_ne hr.2.1, f r (by simp [hr.1])]; rfl

/-- `dst :=` the elements `s … s + cnt - 1` of `l`, through the scratch list `lt`. -/
def sliceC (dst l : LR) (s cnt : SR) (lt : LR) : Code :=
  .seq (.lmov lt l) (.seq (dropC s lt) (.seq (.lnil dst) (takeC cnt lt dst)))

theorem exec_sliceC (dst l : LR) (s cnt : SR) (lt : LR) (hlt : lt ≠ dst) (σ : St)
    (hI : Inv E σ) (hn : σ.sc cnt + σ.sc s ≤ (σ.ls l).length) (hcnt : cnt ≠ 41)
    (hC : σ.sc cnt ≤ E.C) :
    ∃ sc', exec E (sliceC dst l s cnt lt) σ = setSL σ sc'
        (Function.update (Function.update σ.ls lt (((σ.ls l).drop (σ.sc s)).drop (σ.sc cnt))) dst
          (((σ.ls l).drop (σ.sc s)).take (σ.sc cnt))) ∧
      Fr [41] σ.sc sc' := by
  simp only [sliceC, exec_seq, dropC, exec_rep]
  obtain ⟨sc1, h1, f1⟩ := iter_drop (E := E) lt (σ.sc s) (exec E (.lmov lt l) σ)
  have hs : (exec E (.lmov lt l) σ).sc s = σ.sc s := rfl
  rw [hs, h1]
  set D := (σ.ls l).drop (σ.sc s)
  have hI1 : Inv E (exec E (.lnil dst) (setSL (exec E (.lmov lt l) σ) sc1
      (Function.update (exec E (.lmov lt l) σ).ls lt (((exec E (.lmov lt l) σ).ls lt).drop
        (σ.sc s))))) := by
    have := inv_exec E (.seq (.lmov lt l) (.seq (dropC s lt) (.lnil dst))) σ hI
    simp only [exec_seq, dropC, exec_rep, hs, h1] at this; exact this
  obtain ⟨sc2, h2, f2⟩ := exec_takeC (E := E) (n := cnt) (lA := lt) (lR := dst) hlt
    (D.take (σ.sc cnt)) (D.drop (σ.sc cnt)) [] _ hI1
    (by simp [exec, setSL, Function.update_of_ne hlt, D])
    (by simp [exec, setSL]) (by simp [exec, setSL, f1 cnt (by simp [hcnt]), D]; omega)
    (by simp; omega)
  rw [h2]
  refine ⟨sc2, ?_, fun r hr => (f2 r hr).trans (f1 r hr)⟩
  simp [exec, setSL, D]
  funext x; simp only [Function.update_apply]; split_ifs <;> simp_all

end FhatGen

end SigabaNeo.Lattices
