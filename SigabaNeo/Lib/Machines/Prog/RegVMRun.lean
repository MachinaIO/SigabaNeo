import SigabaNeo.Lib.Machines.Prog.RegVM

/-!
# The register machine on tapes: instructions

The tape program of each instruction of `RegVM.Code` and its law on encoded states
(`run_*P`): `run P (enc E σ ctr) = enc E (exec E c σ) ctr`. The scratch tapes `X0`, `X1` hold
intermediate words and `X7` counts the macro loops; all are blank afterwards.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Tape

namespace RegVM

open Prog
open scoped Prog

abbrev X0 : Fin K := tX 0
abbrev X1 : Fin K := tX 1
abbrev X7 : Fin K := tX 7

variable (E : Env) (σ : St) (ctr : Fin nD → List Bool)

/-! ### Scalar instructions -/

def oneP (d : SR) : Prog K := cp (tR d) tN
def zeroP (d : SR) : Prog K := clr (tR d)
def movP (d a : SR) : Prog K := cp (tR d) (tR a)
def subP (d a : SR) : Prog K := dropBy (tR d) (tR a) X7
def incP (d : SR) : Prog K :=
  cp X0 tT ⨾ dropBy X0 (tR d) X7 ⨾ tl X0 ⨾ cp (tR d) tT ⨾ dropBy (tR d) X0 X7 ⨾ clr X0
def addP (d a : SR) : Prog K :=
  cp X0 tT ⨾ dropBy X0 (tR d) X7 ⨾ dropBy X0 (tR a) X7 ⨾ cp (tR d) tT ⨾ dropBy (tR d) X0 X7 ⨾
    clr X0

theorem run_oneP (d : SR) : run (oneP d) (enc E σ ctr) = enc E (exec E (.one d) σ) ctr := by
  rw [exec, enc_sc]; rfl

theorem run_zeroP (d : SR) : run (zeroP d) (enc E σ ctr) = enc E (exec E (.zero d) σ) ctr := by
  rw [exec, enc_sc]; rfl

theorem run_movP (d a : SR) : run (movP d a) (enc E σ ctr) = enc E (exec E (.mov d a) σ) ctr := by
  rw [exec, enc_sc]; simp [movP]

theorem run_subP (d a : SR) : run (subP d a) (enc E σ ctr) = enc E (exec E (.sub d a) σ) ctr := by
  rw [exec, enc_sc, subP, run_dropBy _ _ _ (by simp)]
  simp [enc_upd_X, List.drop_replicate]

theorem run_incP (d : SR) : run (incP d) (enc E σ ctr) = enc E (exec E (.inc d) σ) ctr := by
  rw [exec, enc_sc]
  simp only [incP, run_seq, run_copy, run_tail, run_clear, run_dropBy _ _ _ (by simp : X7 ≠ X0),
    run_dropBy _ _ _ (by simp : X7 ≠ tR d)]
  have e : E.M - (E.M - σ.sc d - 1) = min (σ.sc d + 1) E.M := by omega
  enc_ext <;> simp [List.drop_replicate, e]

theorem run_addP (d a : SR) : run (addP d a) (enc E σ ctr) = enc E (exec E (.add d a) σ) ctr := by
  rw [exec, enc_sc]
  simp only [addP, run_seq, run_copy, run_tail, run_clear, run_dropBy _ _ _ (by simp : X7 ≠ X0),
    run_dropBy _ _ _ (by simp : X7 ≠ tR d)]
  have e : E.M - (E.M - σ.sc d - σ.sc a) = min (σ.sc d + σ.sc a) E.M := by omega
  enc_ext <;> simp [List.drop_replicate, e]

/-! ### Emitting a gate -/

/-- `X1 :=` the emitted position of the register `r`. -/
def fixP (r : SR) : Prog K :=
  cp X0 tT ⨾ dropBy X0 (tR r) X7 ⨾ dropBy X0 tCO X7 ⨾ ifBlank X0 (cp X1 tN) (cp X1 (tR r)) ⨾ clr X0

/-- Shift the unary word of `|X1|` on `W` bits into the output. -/
def emitX1 : Prog K :=
  shiftIn true tOUT X1 X7 ⨾ dropBy tOC X1 X7 ⨾ cp X0 tW ⨾ dropBy X0 X1 X7 ⨾
    shiftIn false tOUT X0 X7 ⨾ dropBy tOC X0 X7 ⨾ clr X0 ⨾ clr X1

/-- Emit the position of the register `r`. -/
def emitP (r : SR) : Prog K := fixP r ⨾ emitX1

theorem run_fixP (r : SR) : run (fixP r) (enc E σ ctr) =
    Function.update (enc E σ ctr) X1 (List.replicate (fixv E σ.t (σ.sc r)) true) := by
  simp only [fixP, run_seq, run_copy, run_clear, run_dropBy _ _ _ (by simp : X7 ≠ X0)]
  rw [run_ifBlank]
  have key : (E.M - σ.sc r - (E.M - (E.n + 1 + σ.t)) = 0) ↔ min (E.n + 1 + σ.t) E.M ≤ σ.sc r := by
    omega
  by_cases hc : min (E.n + 1 + σ.t) E.M ≤ σ.sc r
  · rw [if_pos (by simp [List.drop_replicate]; omega)]
    simp only [fixv, hc, ite_true]
    enc_ext
  · rw [if_neg (by simp [List.drop_replicate]; omega)]
    simp only [fixv, hc, ite_false]
    enc_ext

theorem length_uw' (W j : ℕ) : (uw W j).length = j + (W - j) := by simp [uw]

theorem run_emitX1 (v : ℕ) : run emitX1 (Function.update (enc E σ ctr) X1 (List.replicate v true)) =
    enc E { σ with out := σ.out ++ uw E.W v } ctr := by
  rw [enc_out]
  simp only [emitX1, run_seq, run_copy, run_clear, run_dropBy _ _ _ (by simp : X7 ≠ X0),
    run_dropBy _ _ _ (by simp : X7 ≠ tOC), run_shiftIn _ _ _ _ (by simp : X7 ≠ tOUT)]
  have hout : ((((E.pad ++ σ.out).drop σ.out.length ++ List.replicate v true).drop v ++
      List.replicate (E.W - v) false).drop (E.W - v)) =
      (E.pad ++ (σ.out ++ uw E.W v)).drop (σ.out ++ uw E.W v).length := by
    have h1 : ((E.pad ++ σ.out).drop σ.out.length ++ List.replicate v true).drop v =
        (E.pad ++ (σ.out ++ List.replicate v true)).drop (σ.out.length + v) := by
      simpa using drop_append_drop E.pad σ.out (List.replicate v true)
    have h2 : ((E.pad ++ (σ.out ++ List.replicate v true)).drop (σ.out.length + v) ++
        List.replicate (E.W - v) false).drop (E.W - v) = (E.pad ++ ((σ.out ++ List.replicate v true)
          ++ List.replicate (E.W - v) false)).drop (σ.out.length + v + (E.W - v)) := by
      simpa using drop_append_drop E.pad (σ.out ++ List.replicate v true)
        (List.replicate (E.W - v) false)
    rw [h1, h2]
    simp only [uw, List.append_assoc, List.length_append, List.length_replicate, Nat.add_assoc]
  enc_ext
  all_goals (simp only [length_uw']; omega)

theorem run_emitP (r : SR) : run (emitP r) (enc E σ ctr) =
    enc E { σ with out := σ.out ++ uw E.W (fixv E σ.t (σ.sc r)) } ctr := by
  rw [emitP, run_seq, run_fixP, run_emitX1]

/-- `nand d a b`: emit the two positions, then `d :=` the new gate's position. -/
def nandP (d a b : SR) : Prog K :=
  emitP a ⨾ emitP b ⨾ cp (tR d) tT ⨾ dropBy (tR d) tCO X7 ⨾ tl tCO

theorem run_nandP (d a b : SR) : run (nandP d a b) (enc E σ ctr) =
    enc E (exec E (.nand d a b) σ) ctr := by
  simp only [nandP, run_seq, run_emitP]
  simp only [run_copy, run_tail, run_dropBy _ _ _ (by simp : X7 ≠ tR d)]
  rw [exec]
  have e2 : E.M - (E.M - (E.n + 1 + σ.t)) = min (E.n + 1 + σ.t) E.M := by omega
  enc_ext
  all_goals omega

end RegVM

end SigabaNeo.Tape
