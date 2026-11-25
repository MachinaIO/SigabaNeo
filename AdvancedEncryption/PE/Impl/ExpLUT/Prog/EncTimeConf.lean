import PE.Impl.ExpLUT.Prog.EncOutputTime

/-! # The clock and total cost of the concrete package-P encryption machine -/
namespace AdvancedEncryption.ExpLUT.Prog.EncConf
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Params EncW

/-- A scalar bound for the typed public queue. -/
theorem publicLength_le : publicLength Dc ≤ 2 ^ 98 := by
  simp only [publicLength, fixedSize, BCol, Wb, Jh, Col, Dig, Pos,
    Enum.length_prod, len_sum, len_fin]
  norm_num [Dc, Kc, mbar, PE.BranchingProgram.w8, PE.BranchingProgram.Width.len]

theorem pwW_length_le : pwW.length ≤ 2 ^ 11 := by
  have h := nInS_le
  simp only [nInS, encodeTuple_cons, encodeTuple_nil, List.length_append, length_frame,
    List.length_nil] at h
  omega

theorem encInputLength_le : encInputLength Dc ≤ 2 ^ 100 := by
  have hp : fixedSize (mpkEnc Dc) ≤ 2 ^ 98 :=
    (Nat.le_add_right _ 129).trans publicLength_le
  have hw := Nat.add_le_add_right (Nat.mul_le_mul_left 2 pwW_length_le) 1
  have hk := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 1
  have h := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hw hk) 257) 3
  exact h.trans (by norm_num)

/-- Composition follows the actual randomized program, including queue normalization. -/
theorem bounds_encProgram : XBound (encProgram Dc 16 6 eFl) (2 ^ 100)
    ((2 ^ 301 + 2 ^ 816) + 2 ^ 205) (2 ^ 101) := by
  have hs : XBound (.prog (.seq relocateP (.seq (normalizeInputsP Dc) (cleanCoreP Dc))))
      (2 ^ 110) (2 ^ 816) (2 ^ 99) := fun _ h => time_encryptionSuffix h
  exact (bounds_widePrepare.seq hs).seq bounds_frameCiphertextP

theorem time_encMP_le (D : Dims) (η L e T : ℕ)
    (h : XProg.totalTimeT (encProgram D η L e) 0 0 (encInputLength D) ≤ T) :
    (encMP D η L e).time ≤ T := h
 theorem machine_cost_lt (M : Machine) {T B C : ℕ}
    (ht : M.time ≤ T) (hb : M.descLen ≤ B) (hnum : T + B < C) : M.cost < C :=
  (Nat.add_le_add ht hb).trans_lt hnum

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
/-- Complete compiler clock: input loader, parser/sampler, normalized core, frame, and emitter. -/
theorem time_encMachine : encMachine.time ≤ 2 ^ 817 := by
  have h := bounds_encProgram.total (0 : Fin 326) 0 encInputLength_le
  exact time_encMP_le Dc 16 6 eFl (2 ^ 817) (h.trans (by norm_num))

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
/-- The concrete encryption machine's clock plus description is strictly below `2^818`. -/
theorem cost_encMachine_lt : encMachine.cost < 2 ^ 818 := by
  exact machine_cost_lt encMachine time_encMachine descLen_encMachine (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.EncConf
