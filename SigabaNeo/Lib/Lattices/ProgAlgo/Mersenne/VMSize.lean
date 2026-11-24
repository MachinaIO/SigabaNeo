import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.RingVM
import SigabaNeo.Lib.Machines.Prog.FrameSize

/-!
# The state count of compiled ring-word codes

`XProg.size (compile c)` (the number of states of the compiled machine, `XProg.card_state`) is
the explicit recursive sum **`vmSize c`** (`size_compile`): each instruction contributes the sizes
of its programs (certified constants: `addRMP`, `subRMP` 4906, `mulRMP` 13341, `canonRP` 1312,
`notP` 1270, `digitRWP` 3751, `rotBP` 1495, `autMP` 5859, `rhoJP` 367, the loads/stores `inP` 400,
`outP` 144, `cp` 36), a loop `39` more than its body, a branch `1` more than its two arms.
So `vmSize c ≤ 15000 · (number of instructions) + 39 · (loops) + (branches)` (`vmSize_le`).

The description length of `XProg.toMachineB p i₀ o n` is
`6 (size p + n + 5) · 3^k · entryBits k (size p + n + 5) 0` (`descLen_toMachineB`), `k` the number
of tapes (`247` for `compile`, more with a front end): the factor `3^k` dominates.
-/

namespace SigabaNeo.Tape

namespace RingVM

open Prog

/-- **The state count of a compiled code.** -/
def vmSize : Code → ℕ
  | .add .. | .sub .. => 400 + 400 + 4906 + 144
  | .mul .. => 400 + 400 + 13341 + 144
  | .canon .. => 400 + 1312 + 144
  | .neg .. => 400 + 1270 + 144
  | .digit .. => 400 + 36 + 3751 + 144
  | .rotB .. => 400 + 36 + 1495 + 144
  | .aut .. => 400 + 36 + 5859 + 144
  | .rhoJ .. => 400 + 36 + 367 + 144
  | .mv d s c => if d = s ∨ d = c ∨ s = c then 36 else 292
  | .cp _ _ => 36
  | .drop t c => if t = c then 36 else 147
  | .clr _ | .tl _ | .nop => 36
  | .rep _ b => vmSize b + 39
  | .seq p q => vmSize p + vmSize q
  | .ifb _ p q => vmSize p + vmSize q + 1

theorem size_inP : ValVM.inP.size = 400 := by decide
theorem size_outP : ValVM.outP.size = 144 := by decide
theorem size_mvPc : ValVM.mvPc.size = 292 := by decide
theorem size_dropPc : ValVM.dropPc.size = 147 := by decide
theorem size_cp01 : (Prog.cp 0 1 : Prog 2).size = 36 := by decide
theorem size_clr0 : (Prog.clr 0 : Prog 1).size = 36 := by decide
theorem size_tl0 : (Prog.tl 0 : Prog 1).size = 36 := by decide
theorem size_nop0 : (nop 0 : Prog 1).size = 36 := by decide
theorem size_addRMP : addRMP.size = 4906 := by decide +kernel
theorem size_subRMP : subRMP.size = 4906 := by decide +kernel
theorem size_mulRMP : mulRMP.size = 13341 := by decide +kernel
theorem size_canonRP : canonRP.size = 1312 := by decide +kernel
theorem size_notP : notP.size = 1270 := by decide +kernel
theorem size_digitRWP : digitRWP.size = 3751 := by decide +kernel
theorem size_rotBP : rotBP.size = 1495 := by decide +kernel
theorem size_autMP : autMP.size = 5859 := by decide +kernel
theorem size_rhoJP : rhoJP.size = 367 := by decide +kernel

/-- **`XProg.size (compile c) = vmSize c`.** -/
theorem size_compile : ∀ c : Code, (compile c).size = vmSize c
  | .add .. => by
    simp only [compile, opBin, loadA, store, XProg.size_seq, XProg.size_frame, XProg.size_prog,
      size_inP, size_addRMP, size_outP, vmSize]
  | .sub .. => by
    simp only [compile, opBin, loadA, store, XProg.size_seq, XProg.size_frame, XProg.size_prog,
      size_inP, size_subRMP, size_outP, vmSize]
  | .mul .. => by
    simp only [compile, opBin, loadA, store, XProg.size_seq, XProg.size_frame, XProg.size_prog,
      size_inP, size_mulRMP, size_outP, vmSize]
  | .canon .. => by
    simp only [compile, opUn, loadA, store, XProg.size_seq, XProg.size_frame, XProg.size_prog,
      size_inP, size_canonRP, size_outP, vmSize]
  | .neg .. => by
    simp only [compile, opUn, loadA, store, XProg.size_seq, XProg.size_frame, XProg.size_prog,
      size_inP, size_notP, size_outP, vmSize]
  | .digit .. => by
    simp only [compile, opTm, loadA, loadT, store, XProg.size_seq, XProg.size_frame,
      XProg.size_prog, size_inP, size_cp01, size_digitRWP, size_outP, vmSize]
  | .rotB .. => by
    simp only [compile, opTm, loadA, loadT, store, XProg.size_seq, XProg.size_frame,
      XProg.size_prog, size_inP, size_cp01, size_rotBP, size_outP, vmSize]
  | .aut .. => by
    simp only [compile, opTm, loadA, loadT, store, XProg.size_seq, XProg.size_frame,
      XProg.size_prog, size_inP, size_cp01, size_autMP, size_outP, vmSize]
  | .rhoJ .. => by
    simp only [compile, opTm, loadA, loadT, store, XProg.size_seq, XProg.size_frame,
      XProg.size_prog, size_inP, size_cp01, size_rhoJP, size_outP, vmSize]
  | .mv d s c => by
    simp only [compile, vmSize]
    split_ifs <;> simp [nopX, size_nop0, size_mvPc]
  | .cp d s => by
    simp only [compile, vmSize]
    split_ifs <;> simp [nopX, size_nop0, size_cp01]
  | .drop t c => by
    simp only [compile, vmSize]
    split_ifs <;> simp [nopX, size_nop0, size_dropPc]
  | .clr _ => by simp [compile, vmSize, size_clr0]
  | .tl _ => by simp [compile, vmSize, size_tl0]
  | .nop => by simp [compile, vmSize, nopX, size_nop0]
  | .rep _ b => by simp [compile, vmSize, size_compile b]
  | .seq p q => by simp [compile, vmSize, size_compile p, size_compile q]
  | .ifb _ p q => by simp [compile, vmSize, size_compile p, size_compile q]

/-- The number of instructions, loops and branches of a code. -/
def vmCount : Code → ℕ
  | .rep _ b => vmCount b + 1
  | .seq p q => vmCount p + vmCount q
  | .ifb _ p q => vmCount p + vmCount q + 1
  | _ => 1

/-- **A crude bound**: at most `15000` states per instruction, loop and branch. -/
theorem vmSize_le : ∀ c : Code, vmSize c ≤ 15000 * vmCount c
  | .rep _ b => by have := vmSize_le b; simp only [vmSize, vmCount]; omega
  | .seq p q => by have := vmSize_le p; have := vmSize_le q; simp only [vmSize, vmCount]; omega
  | .ifb _ p q => by have := vmSize_le p; have := vmSize_le q; simp only [vmSize, vmCount]; omega
  | .add .. | .sub .. | .mul .. | .canon .. | .neg .. | .digit .. | .rotB .. | .aut .. | .rhoJ ..
  | .cp .. | .clr _ | .tl _ | .nop => by simp [vmSize, vmCount]
  | .mv d s c => by simp only [vmSize, vmCount]; split_ifs <;> omega
  | .drop t c => by simp only [vmSize, vmCount]; split_ifs <;> omega

end RingVM

end SigabaNeo.Tape
