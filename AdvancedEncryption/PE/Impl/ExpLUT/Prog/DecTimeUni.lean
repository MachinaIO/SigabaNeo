import PE.Impl.ExpLUT.Prog.DecTimeVM
import PE.Impl.ExpLUT.Prog.DecMachineCode

/-!
# A uniform clock of the compiled `Dec` code (package F4)

Instead of tracking every register (`DecTimeVM`), bound **every** register and the operation
area by one cap `M` (`Mo = M`, `B = fun _ => M`). Then the bounds are trivially closed under any
code (`duClosed`), every instruction costs at most one constant `I` (`duInstr_le`), and a code of
`n` nodes and loop depth `d` costs at most `n · I · M^d` (`duVmTime_le`). The code of `Dec` has
`443757` nodes and loop depth `4` (`duNodes_decCode`, a kernel evaluation of a few seconds), so

**`duVM_decCode`**: from `encB M N K (fun _ => M)` (`M = 2^110`, `N = 2^24`, `K = 2^16`), the
compiled `decCode` takes at most `2^726` steps and keeps the bounds.
-/

namespace AdvancedEncryption.ExpLUT.Prog.DecT

set_option autoImplicit false

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.MersenneT
  SigabaNeo.Tape.Prog.SpecT

/-! ### Nodes and loop depth -/

/-- The number of nodes of a code. -/
def duNodes : Code → ℕ
  | .rep _ b => duNodes b + 1
  | .seq p q => duNodes p + duNodes q + 1
  | .ifb _ p q => duNodes p + duNodes q + 1
  | _ => 1

/-- The loop depth of a code. -/
def duDepth : Code → ℕ
  | .rep _ b => duDepth b + 1
  | .seq p q => max (duDepth p) (duDepth q)
  | .ifb _ p q => max (duDepth p) (duDepth q)
  | _ => 0

set_option maxRecDepth 100000 in
theorem duNodes_decCode : duNodes decCode = 443757 ∧ duDepth decCode = 4 := by decide +kernel

/-! ### Uniform bounds are closed -/

theorem duClosed (Mo N K M : ℕ) (hNK : N * K ≤ M) (hMo : M ≤ Mo) :
    ∀ c : Code, Closed Mo N K (fun _ => M) c
  | .add .. | .sub .. | .mul .. | .canon .. | .neg .. => hNK
  | .digit .. | .rotB .. | .aut .. | .rhoJ .. => ⟨hNK, hMo⟩
  | .cp .. => le_rfl
  | .mv .. | .drop .. | .clr _ | .tl _ | .nop => trivial
  | .rep _ b => duClosed Mo N K M hNK hMo b
  | .seq p q | .ifb _ p q => ⟨duClosed Mo N K M hNK hMo p, duClosed Mo N K M hNK hMo q⟩

/-! ### The clock from nodes and depth -/

theorem duVmTime_le (Mo N K : ℕ) (B : Fin 200 → ℕ) (tc : Code → ℕ) (M I : ℕ) (hM : 1 ≤ M)
    (hB : ∀ x, B x ≤ M) (hI : ∀ c, tc c ≤ I) (hS : 2 * supB (encB Mo N K B) + 6 ≤ I) :
    ∀ c : Code, vmTime Mo N K B tc c ≤ duNodes c * I * M ^ duDepth c
  | .rep t b => by
    have ih := duVmTime_le Mo N K B tc M I hM hB hI hS b
    show B t * (2 * supB (encB Mo N K B) + 3 + vmTime Mo N K B tc b + 1) + 2 ≤
      (duNodes b + 1) * I * M ^ (duDepth b + 1)
    set v := vmTime Mo N K B tc b
    set X := I * M ^ duDepth b
    have hX : I ≤ X := Nat.le_mul_of_pos_right _ (Nat.pow_pos hM)
    have e : (duNodes b + 1) * I * M ^ (duDepth b + 1) = M * (duNodes b * X) + M * X := by
      simp only [X, pow_succ]; ring
    rw [e]
    have h1 : B t * (2 * supB (encB Mo N K B) + 3 + v + 1) ≤
        M * (2 * supB (encB Mo N K B) + 4) + M * v :=
      (Nat.mul_le_mul_right _ (hB t)).trans (by rw [← Nat.mul_add]; exact le_of_eq (by ring_nf))
    have h2 : M * v ≤ M * (duNodes b * X) := Nat.mul_le_mul_left _ (by
      simpa [X, Nat.mul_assoc] using ih)
    have h3 : M * (2 * supB (encB Mo N K B) + 4) + 2 ≤ M * X := by
      have : M * (2 * supB (encB Mo N K B) + 6) ≤ M * X := Nat.mul_le_mul_left _ (hS.trans hX)
      have : M * (2 * supB (encB Mo N K B) + 6) = M * (2 * supB (encB Mo N K B) + 4) + 2 * M := by
        ring
      omega
    omega
  | .seq p q => by
    have ihp := duVmTime_le Mo N K B tc M I hM hB hI hS p
    have ihq := duVmTime_le Mo N K B tc M I hM hB hI hS q
    show vmTime Mo N K B tc p + vmTime Mo N K B tc q ≤
      (duNodes p + duNodes q + 1) * I * M ^ max (duDepth p) (duDepth q)
    have hp : M ^ duDepth p ≤ M ^ max (duDepth p) (duDepth q) :=
      Nat.pow_le_pow_right hM (le_max_left _ _)
    have hq : M ^ duDepth q ≤ M ^ max (duDepth p) (duDepth q) :=
      Nat.pow_le_pow_right hM (le_max_right _ _)
    have a := ihp.trans (Nat.mul_le_mul_left (duNodes p * I) hp)
    have b := ihq.trans (Nat.mul_le_mul_left (duNodes q * I) hq)
    have e : (duNodes p + duNodes q + 1) * I * M ^ max (duDepth p) (duDepth q) =
        duNodes p * I * M ^ max (duDepth p) (duDepth q) +
          duNodes q * I * M ^ max (duDepth p) (duDepth q) +
          I * M ^ max (duDepth p) (duDepth q) := by ring
    omega
  | .ifb x p q => by
    have ihp := duVmTime_le Mo N K B tc M I hM hB hI hS p
    have ihq := duVmTime_le Mo N K B tc M I hM hB hI hS q
    show max (vmTime Mo N K B tc p) (vmTime Mo N K B tc q) + 1 ≤
      (duNodes p + duNodes q + 1) * I * M ^ max (duDepth p) (duDepth q)
    have hp : M ^ duDepth p ≤ M ^ max (duDepth p) (duDepth q) :=
      Nat.pow_le_pow_right hM (le_max_left _ _)
    have hq : M ^ duDepth q ≤ M ^ max (duDepth p) (duDepth q) :=
      Nat.pow_le_pow_right hM (le_max_right _ _)
    have a := ihp.trans (Nat.mul_le_mul_left (duNodes p * I) hp)
    have b := ihq.trans (Nat.mul_le_mul_left (duNodes q * I) hq)
    have h1 : 1 ≤ I * M ^ max (duDepth p) (duDepth q) :=
      Nat.mul_pos (by omega) (Nat.pow_pos hM)
    have e : (duNodes p + duNodes q + 1) * I * M ^ max (duDepth p) (duDepth q) =
        duNodes p * I * M ^ max (duDepth p) (duDepth q) +
          duNodes q * I * M ^ max (duDepth p) (duDepth q) +
          I * M ^ max (duDepth p) (duDepth q) := by ring
    have : max (vmTime Mo N K B tc p) (vmTime Mo N K B tc q) ≤
        duNodes p * I * M ^ max (duDepth p) (duDepth q) +
          duNodes q * I * M ^ max (duDepth p) (duDepth q) := max_le (by omega) (by omega)
    omega
  | .add .. | .sub .. | .mul .. | .canon .. | .neg .. | .digit .. | .rotB .. | .aut .. | .rhoJ ..
  | .mv .. | .cp .. | .drop .. | .clr _ | .tl _ | .nop => by
    simp only [vmTime, duNodes, duDepth, pow_zero, Nat.mul_one, Nat.one_mul]; exact hI _

/-! ### The instruction cost at the concrete sizes -/

/-- The cap of every register and of the operation area. -/
abbrev duM : ℕ := 2 ^ 110
/-- The cost cap of one instruction. -/
abbrev duI : ℕ := 2 ^ 267

set_option exponentiation.threshold 2000 in
theorem duInstr_le (c : Code) : instrTime duM (2 ^ 24) (2 ^ 16) (fun _ => duM) c ≤ duI := by
  cases c <;>
    simp only [instrTime, binTime, unTime, tmTime, max_self, pEval, mEval, ρLd, wMulRM, wCanon,
      wNotM, wDigitM, wDigit, wRotB, wAut, wRhoJ, List.headD, List.tail, List.cons_append,
      List.nil_append] <;>
    norm_num

theorem duSupB_le : supB (encB duM (2 ^ 24) (2 ^ 16) (fun _ => duM)) ≤ duM :=
  (supB_encB_le _ _ _ _ duM (by norm_num) (by norm_num) (by norm_num) fun _ => le_rfl).trans
    (by simp)

set_option exponentiation.threshold 2000 in
/-- **The uniform clock of the compiled `Dec` code.** -/
theorem duVM_decCode :
    XProg.timeBoundT (compile decCode) (encB duM (2 ^ 24) (2 ^ 16) (fun _ => duM)) ≤ 2 ^ 726 ∧
      XProg.lenBoundT (compile decCode) (encB duM (2 ^ 24) (2 ^ 16) (fun _ => duM)) ≤
        encB duM (2 ^ 24) (2 ^ 16) (fun _ => duM) := by
  have hc := compile_time duM (2 ^ 24) (2 ^ 16) (fun _ => duM) (by norm_num) (by norm_num)
    (by norm_num) decCode (duClosed _ _ _ _ (by norm_num) le_rfl decCode)
  refine ⟨hc.1.trans ?_, hc.2⟩
  have hv := duVmTime_le duM (2 ^ 24) (2 ^ 16) (fun _ => duM) _ duM duI (by norm_num)
    (fun _ => le_rfl) duInstr_le (by have := duSupB_le; simp only [duI, duM] at *; omega) decCode
  rw [duNodes_decCode.1, duNodes_decCode.2] at hv
  exact hv.trans (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.DecT
