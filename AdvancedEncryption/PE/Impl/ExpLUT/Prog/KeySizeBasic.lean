import PE.Impl.ExpLUT.Prog.KeyMachine
import SigabaNeo.Lib.Machines.Prog.FrameSize

/-! Syntax-size certificates for the actual Mersenne VM KeyGen implementation. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

/-- Count instructions and control nodes; sequences contribute the sum of their children. -/
def codeWeight : Code → ℕ
  | .seq p q => codeWeight p + codeWeight q
  | .rep _ p => codeWeight p + 1
  | .ifb _ p q => codeWeight p + codeWeight q + 1
  | _ => 1

theorem size_compile_op_le (o : Op) (d a b : Fin 64) :
    (compile (.op o d a b)).size ≤ 100000 := by
  cases o <;> simp only [compile, XProg.size_seq, XProg.size_frame, XProg.size_prog]
  all_goals decide +kernel

/-- A uniform leaf-size bound, including actual arithmetic operation code and compiler framing. -/
theorem size_compile_weight : ∀ c : Code, (compile c).size ≤ 100000 * codeWeight c
  | .op o d a b => size_compile_op_le o d a b
  | .mv d s c => by
    simp only [compile, codeWeight, Nat.mul_one]
    split_ifs <;> simp only [nopX, XProg.size_frame, XProg.size_prog] <;> decide +kernel
  | .mvR d s => by
    simp only [compile, codeWeight, Nat.mul_one]
    split_ifs <;> simp only [nopX, XProg.size_frame, XProg.size_prog] <;> decide +kernel
  | .cp d s => by
    simp only [compile, codeWeight, Nat.mul_one]
    split_ifs <;> simp only [nopX, XProg.size_frame, XProg.size_prog] <;> decide +kernel
  | .drop t c => by
    simp only [compile, codeWeight, Nat.mul_one]
    split_ifs <;> simp only [nopX, XProg.size_frame, XProg.size_prog] <;> decide +kernel
  | .clr t => by simp only [compile, codeWeight, XProg.size_frame, XProg.size_prog]; decide
  | .tl t => by simp only [compile, codeWeight, XProg.size_frame, XProg.size_prog]; decide
  | .app d s => by
    simp only [compile, codeWeight, Nat.mul_one]
    split_ifs <;> simp only [XProg.size_frame, XProg.size_prog] <;> decide +kernel
  | .eqb f a b => by
    simp only [compile, codeWeight, Nat.mul_one]
    split_ifs <;> simp only [nopX, XProg.size_frame, XProg.size_prog] <;> decide +kernel
  | .nop => by simp only [compile, codeWeight, nopX, XProg.size_frame, XProg.size_prog]; decide
  | .seq p q => by
    have hp := size_compile_weight p
    have hq := size_compile_weight q
    simp only [compile, XProg.size_seq, codeWeight]
    omega
  | .rep r p => by
    have hp := size_compile_weight p
    simp only [compile, XProg.size, codeWeight]
    omega
  | .ifb r p q => by
    have hp := size_compile_weight p
    have hq := size_compile_weight q
    simp only [compile, XProg.size, codeWeight]
    omega

/-- Coarse linear bound for binary-doubling constants, sufficient even for huge fixed templates. -/
theorem weight_natC (r u : Fin 64) : ∀ n, codeWeight (natC r u n) ≤ 3 * n + 1
  | 0 => by simp [natC, codeWeight]
  | n + 1 => by
    rw [natC]
    have ih := weight_natC r u ((n + 1) / 2)
    split_ifs <;> simp only [codeWeight] <;> omega
  decreasing_by omega

theorem weight_emitBitsC (dst : Fin 64) : ∀ bs,
    codeWeight (emitBitsC dst bs) = bs.length + 1
  | [] => rfl
  | b :: bs => by simp [emitBitsC, codeWeight, weight_emitBitsC dst bs]; omega

def TemplateWord.weightBound : TemplateWord → ℕ
  | .zeros n => 3 * n + 1
  | .bits bs => bs.length + 2

theorem weight_templateWord (dst : Fin 64) (a : TemplateWord) :
    codeWeight (a.code dst) ≤ a.weightBound := by
  cases a with
  | zeros n => exact weight_natC dst rB1 n
  | bits bs => simp [TemplateWord.code, codeWeight, weight_emitBitsC, TemplateWord.weightBound]; omega

theorem weight_templateOpsC : ∀ ops,
    codeWeight (templateOpsC ops) ≤ 1 + (ops.map (fun op ↦ op.2.weightBound)).sum
  | [] => by simp [templateOpsC, codeWeight]
  | (dst, a) :: ops => by
    have ha := weight_templateWord dst a
    have ih := weight_templateOpsC ops
    simp only [templateOpsC, codeWeight, List.map_cons, List.sum_cons]
    omega

theorem weight_readFieldC (src dst : Fin 64) (off len : ℕ) :
    codeWeight (readFieldC src dst off len) ≤ 3 * off + 3 * len + 6 := by
  have ho := weight_natC 30 rB1 off
  have hl := weight_natC 30 rB1 len
  simp only [readFieldC, takeC, codeWeight]
  omega

/-- State count of the actual constant initializer, keeping the precise template list visible. -/
theorem size_evalInitC (D : Dims) :
    (compile (evalInitC D)).size ≤
      100000 * (6 + ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum) := by
  apply (size_compile_weight _).trans
  apply Nat.mul_le_mul_left
  have h := weight_templateOpsC (evalInitOps D)
  simp only [evalInitC, bitsC, codeWeight]
  omega

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open Params

/-- Eliminate codec terms before specializing dimensions, avoiding expansion of literal ring words. -/
theorem size_evalInitC_poly (D : Dims) : (compile (evalInitC D)).size ≤
    100000 * (3 * (gD D + D.b + 16 * D.K ^ 3 * (D.N * D.K) + D.K + (D.K - 1) +
      D.N * D.K + 2 * D.K + 7 * D.K * (D.N * D.K) + 4 * D.K + 2 ^ D.b + tlK) +
      3 * (D.N * D.K) + 118) := by
  apply (size_evalInitC D).trans
  simp only [evalInitOps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    TemplateWord.weightBound, length_encRM]
  ring_nf
  exact le_rfl

/-- Concrete state bound for all EvalPK constant initialization, including literal ring words. -/
theorem size_evalInitC_Dc : (compile (evalInitC Dc)).size ≤ 2 ^ 112 := by
  apply (size_evalInitC_poly Dc).trans
  norm_num [Dc, Kc, gD, gGen, tlK]

/-- The evaluator's loop bounds are data; its static instruction tree is small. -/
theorem weight_evalC : codeWeight evalC ≤ 2 ^ 20 := by decide +kernel

theorem size_evalC : (compile evalC).size ≤ 2 ^ 37 := by
  exact (size_compile_weight evalC).trans
    ((Nat.mul_le_mul_left 100000 weight_evalC).trans (by norm_num))

end AdvancedEncryption.ExpLUT.Prog
