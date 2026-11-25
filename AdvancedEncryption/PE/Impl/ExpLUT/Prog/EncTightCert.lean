import PE.Impl.ExpLUT.Prog.EncTightInit
/-!
# Certificates of the four encryption phases (tight encryption clock, part 3)

The abstract interpreter (`Sym.absRun`) is run on each whole phase program (`mrowP`, `hBlkP`,
`autBlkP`, `tailP`) from per-tape inputs in the variables `top, N, K, g, W, C` (`C` the number
of columns of `B`), and the result is checked numerically at the concrete values `ρE`
(`checkAt`, by `decide +kernel`): `top = 2^99` (every tape of the machine, the public stream
included), `N = 2^24`, `K = 2^16`, `g = 9`, `W = 2^22`, `C = 2^42`. Every loop is charged its
actual counter (a template of `K`, `N`, `N K`, `2 K`, … bits), every primitive `2 · 2^99 + 3`.
Streams, the output register and scratch are bounded by the top only.
-/

namespace AdvancedEncryption.ExpLUT.Prog.EncTight

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT
open AdvancedEncryption.ExpLUT.Prog.EncW

/-- The values of the variables `top, N, K, g, W, C`. -/
def ρE : List ℕ := [2 ^ 99, 2 ^ 24, 2 ^ 16, 9, 2 ^ 22, 2 ^ 42]

theorem top_ρE : top ρE = 2 ^ 99 := rfl

/-- The inputs of the `b` row (`mrowP` with `L = C` columns). -/
def σME : Asg := [pTop, pNK, pNK, pNK, pTop, pTop, pK, pN, pNK, mo 1 [0, 0, 0, 0, 1], pK,
  mo 2 [1, 2], mo 1 [1, 1, 0, 0, 1], mo 2 [1, 1, 0, 0, 1]] ++ List.replicate 52 pTop

/-- The inputs of a helper pair (`hBlkP`; tapes `5`, `6` the exponent templates, at most `W`). -/
def σHE : Asg := [pTop, pNK, pTop, pTop, pm, pn, pn, pNK, pK, pN, pNK, mo 2 [0, 1], pK,
  mo 2 [1, 2], mo 2 [1, 2], mo 4 [1, 2]] ++ List.replicate 53 pTop

/-- The inputs of an automorphism block (`autBlkP`; tapes `7`, `8` the exponent templates). -/
def σAE : Asg := [pTop, pNK, pTop, pTop, pTop, pTop, pm, pn, pn, pNK, pK, pN, pNK, mo 2 [0, 1], pK,
  mo 2 [1, 2], mo 2 [1, 2], mo 4 [1, 2], pC 1, mo 4 [0, 1]] ++ List.replicate 65 pTop

/-- The inputs of the last phases (`tailP`). -/
def σTE : Asg := [pTop, pNK, pTop, pTop, pTop, pTop, pTop, pTop, pTop, pTop, pTop, pTop, pTop, pTop,
  pTop, pC 1, pNK, mo 2 [1], mo 2 [1], mo 2 [1], mo 2 [1], mo 2 [1], mo 2 [1], mo 2 [1], mo 2 [1],
  pK, pN, pNK, mo 2 [0, 1], pK, mo 2 [1, 2], mo 2 [1, 2], mo 4 [1, 2], pC 1, mo 4 [0, 1], pC 16,
  pC 1, pNK, mo 2 [1, 1]] ++ List.replicate 65 pTop

theorem length_σHE : σHE.length = 69 := rfl
theorem length_σAE : σAE.length = 85 := rfl

set_option maxRecDepth 100000 in
/-- **The `b` row**: at most `2^228` steps. -/
theorem cert_mrowE : checkAt ρE mrowP σME [pTop] (2 ^ 228) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **A helper pair**: at most `2^203` steps, its inputs restored. -/
theorem cert_hBlkE : checkAt ρE hBlkP σHE σHE (2 ^ 203) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **An automorphism block**: at most `2^236` steps, its inputs restored. -/
theorem cert_autBlkE : checkAt ρE autBlkP σAE σAE (2 ^ 236) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The last phases**: at most `2^240` steps (sixteen attribute digit encodings). -/
theorem cert_tailE : checkAt ρE tailP σTE [pTop] (2 ^ 240) = true := by decide +kernel

theorem tb_mrowE : TB mrowP ρE σME ([pTop] ++ List.replicate 66 pTop) (2 ^ 228) :=
  TB.of_checkAt cert_mrowE

theorem tb_hBlkE : TB hBlkP ρE σHE σHE (2 ^ 203) :=
  (TB.of_checkAt cert_hBlkE).mono (fun _ => le_rfl)
    (fun j => (bnd_append_of_length _ _ _ length_σHE j).le) le_rfl

theorem tb_autBlkE : TB autBlkP ρE σAE σAE (2 ^ 236) :=
  (TB.of_checkAt cert_autBlkE).mono (fun _ => le_rfl)
    (fun j => (bnd_append_of_length _ _ _ length_σAE j).le) le_rfl

theorem tb_tailE : TB tailP ρE σTE ([pTop] ++ List.replicate 104 pTop) (2 ^ 240) :=
  TB.of_checkAt cert_tailE

end AdvancedEncryption.ExpLUT.Prog.EncTight
