import SigabaNeoStd.Lattices.ProgAlgo.SpecT
import SigabaNeoStd.Lattices.ProgAlgo.Hash
import SigabaNeoStd.Lattices.ProgAlgo.Transpose
import SigabaNeoStd.Machines.Prog.Split
import SigabaNeoStd.Machines.Prog.VecBound

/-!
# Certificates of the word programs with unbounded inputs

The certificates of `SpecT` fix the lengths of the inputs. Here the input and output tapes are
only bounded by the top size (`pTop`), the templates are variables (`vv i`, the value of the
`i`-th variable), the scratch tapes are blank, and no bound on the tapes afterwards is claimed
(they are at most the top size, `VB.checkMap`): the number of sweeps depends only on the
templates, since every loop counts along a template.

| program | templates (variables) | sweeps |
|---|---|---|
| `splitP` | `4 ↦ 1`, `5 ↦ 2` | `11 + 6 v₁ + 6 v₂` |
| `joinP` | `4 5 6 7 ↦ 1 2 3 4` | `11 + 6 v₁ + 6 v₂ + 6 v₃` |
| `addRWP`, `subRWP` | `3 ↦ 2` (`K`), `4 ↦ 1` (`N`) | `wAdd` |
| `matMulP` | as `SpecT.σMat` | `wMat` |
| `gadP` | `1 ↦ 2`, `2 ↦ 1`, `3 ↦ 3`, `4 ↦ 4`, `5 ↦ 5` | `wGadZ` |
| `trP` | `2 … 7 ↦ 1 … 6` | `wTrZ` |
| `bitSelP` | `4 5 6 ↦ 1 2 3` | `5 + 9 v₂ + 6 v₁ v₂` |
| `hashP` | `4 ↦ 2`, `5 ↦ 1`, `6 7 8 9 ↦ 3 4 5 6` | `wHashZ` |
-/

namespace SigabaNeo.Tape.Prog.SpecZ

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT

/-- The `i`-th variable. -/
def vv (i : ℕ) : Poly := [(List.replicate i 0 ++ [1], 1)]

theorem pEval_vv (ρ : List ℕ) (i : ℕ) : pEval ρ (vv i) = ρ.getD i 0 := by
  induction i generalizing ρ with
  | zero => cases ρ <;> simp [vv, pEval, mEval]
  | succ i ih =>
    cases ρ with
    | nil =>
      have := ih []
      simp only [vv, pEval, mEval, List.replicate_succ, List.cons_append] at this ⊢
      simpa using this
    | cons a ρ =>
      have := ih ρ
      simp only [vv, pEval, mEval, List.replicate_succ, List.cons_append] at this ⊢
      simpa using this

theorem pEval_pTop (ρ : List ℕ) : pEval ρ pTop = top ρ := by
  cases ρ <;> simp [pTop, pEval, mEval, top]

def T : Poly := pTop

def σSplit : Asg := [T, T, T, T, vv 1, vv 2]
def wSplit : Poly := [([], 11), ([0, 1], 6), ([0, 0, 1], 6)]
def σJoin : Asg := [T, T, T, T, vv 1, vv 2, vv 3, vv 4]
def wJoin : Poly := [([], 11), ([0, 1], 6), ([0, 0, 1], 6), ([0, 0, 0, 1], 6)]
def σAdd : Asg := [T, T, T, vv 2, vv 1]
def σMatZ : Asg := [T, T, T, pK, pN, pNK, pm, pn, pl, pmlNK]
def σGad : Asg := [T, vv 2, vv 1, vv 3, vv 4, vv 5]
def wGadZ : Poly :=
  [([], 24), ([0, 0, 1], 11), ([0, 0, 0, 0, 1], 34), ([0, 1, 0, 0, 1], 9), ([0, 1, 1, 0, 1], 6),
    ([0, 0, 0, 1, 1], 9), ([0, 0, 1, 0, 1], 11)]
def σTr : Asg := [T, T, vv 1, vv 2, vv 3, vv 4, vv 5, vv 6]
def wTrZ : Poly :=
  [([], 5), ([0, 0, 0, 0, 1], 10), ([0, 0, 0, 1, 1], 8), ([0, 0, 1, 1, 1], 12), ([0, 1, 1, 1, 1], 9),
    ([0, 0, 1, 2, 1], 4), ([0, 1, 1, 2, 1], 3), ([0, 1, 0, 1, 1], 3), ([0, 0, 1, 0, 1], 4),
    ([0, 0, 0, 0, 1, 1], 3)]
def σSel : Asg := [T, T, T, T, vv 1, vv 2, vv 3]
def wSel : Poly := [([], 5), ([0, 0, 1], 9), ([0, 1, 1], 6)]
def σHash : Asg := [T, T, T, T, vv 2, vv 1, vv 3, vv 4, vv 5, vv 6]
def wHashZ : Poly :=
  [([], 7), ([0, 0, 0, 0, 0, 1], 23), ([0, 0, 0, 0, 1, 1], 18), ([0, 0, 0, 1, 1, 1], 6),
    ([0, 1, 0, 0, 1, 1], 28), ([0, 1, 1, 0, 1, 1], 29), ([0, 0, 0, 1, 0, 1], 12),
    ([0, 1, 0, 0, 0, 1], 28), ([0, 1, 1, 0, 0, 1], 29)]

set_option maxRecDepth 100000

theorem check_splitP : check 8 splitP σSplit [] wSplit = true := by decide +kernel
theorem check_joinP : check 8 joinP σJoin [] wJoin = true := by decide +kernel
theorem check_addRWP : check 8 addRWP σAdd [] wAdd = true := by decide +kernel
theorem check_subRWP : check 8 subRWP σAdd [] wAdd = true := by decide +kernel
theorem check_matMulP : check 8 matMulP σMatZ [] wMat = true := by decide +kernel
theorem check_gadP : check 8 gadP σGad [] wGadZ = true := by decide +kernel
theorem check_trP : check 8 trP σTr [] wTrZ = true := by decide +kernel
theorem check_bitSelP : check 8 bitSelP σSel [] wSel = true := by decide +kernel
theorem check_hashP : check 8 hashP σHash [] wHashZ = true := by decide +kernel

end SigabaNeo.Tape.Prog.SpecZ
