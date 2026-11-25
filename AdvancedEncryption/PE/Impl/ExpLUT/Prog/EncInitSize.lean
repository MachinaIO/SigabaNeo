import PE.Impl.ExpLUT.Prog.EncSizeConf
/-! # Literal initialization and deterministic core state budgets -/
namespace AdvancedEncryption.ExpLUT.Prog.EncConf
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Params EncW

set_option maxRecDepth 100000 in
theorem size_mrowP : mrowP.size ≤ 2 ^ 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem size_hBlkP : hBlkP.size ≤ 2 ^ 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem size_autBlkP : autBlkP.size ≤ 2 ^ 32 := by decide +kernel
set_option maxRecDepth 100000 in
theorem size_tailP : tailP.size ≤ 2 ^ 36 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The deterministic encryption phases, including the helper exponent literals. -/
theorem size_core : (encCoreP Dc).size ≤ 2 ^ 40 := by
  rw [size_encCoreP]
  have hm := size_mrowP
  have hh := size_hBlkP
  have ha := size_autBlkP
  have ht := size_tailP
  change mrowP.size + (36 + 22 * (hBlkP.size + 144 + 60 * 2 ^ 22)) +
    (36 + 22 * (autBlkP.size + 144 + 60 * 2 ^ 22)) + tailP.size ≤ 2 ^ 40
  calc
    _ ≤ 2 ^ 24 + (36 + 22 * (2 ^ 28 + 144 + 60 * 2 ^ 22)) +
        (36 + 22 * (2 ^ 32 + 144 + 60 * 2 ^ 22)) + 2 ^ 36 := by gcongr
    _ ≤ 2 ^ 40 := by norm_num

set_option maxRecDepth 100000 in
theorem cost_public_tight : ((publicInitOps Dc).map InitOp.cost).sum ≤ 20 * 2 ^ 99 := by
  have hm : mvP.size = 220 := by decide +kernel
  simp only [publicInitOps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    InitOp.cost, fixedSize, BCol, Wb, Jh, AdvancedEncryption.ExpLUT.Col, Dig, Pos, Enum.length_prod, len_sum, len_fin]
  norm_num [hm, Dc, Kc, mbar, PE.BranchingProgram.w8, PE.BranchingProgram.Width.len]

set_option maxRecDepth 100000 in
theorem cost_coins_tight : ((coinInitOps Dc).map InitOp.cost).sum ≤ 10 * 2 ^ 99 := by
  have hm : mvP.size = 220 := by decide +kernel
  simp only [coinInitOps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    InitOp.cost, fixedSize, BCol, Wb, Jh, AdvancedEncryption.ExpLUT.Col, Dig, Pos, Enum.length_prod, len_sum, len_fin]
  norm_num [hm, Dc, Kc, mbar, PE.BranchingProgram.w8, PE.BranchingProgram.Width.len]

def rotationSum (D : Dims) : ℕ :=
  rotationLength D 0 + rotationLength D 1 + rotationLength D 2 + rotationLength D 3 +
  rotationLength D 4 + rotationLength D 5 + rotationLength D 6 + rotationLength D 7

theorem rotationSum_le (D : Dims) : rotationSum D ≤ 16 * D.N := by
  have hr (i : Fin 8) : rotationLength D i ≤ 2 * D.N := by
    rw [rotationLength_eq]; exact Nat.sub_le _ _
  have := hr 0; have := hr 1; have := hr 2; have := hr 3
  have := hr 4; have := hr 5; have := hr 6; have := hr 7
  unfold rotationSum
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem cost_templates_formula (D : Dims) :
    ((templateInitOps D).map InitOp.cost).sum = 2016 + 60 *
      (fixedSize (ctEnc D) + 12 * (D.N * D.K) + 18 * D.K + 4 * D.N + (D.mb + D.K) +
        4 * (D.K - 1) + 26 * D.K * (D.N * D.K) + 3 * (D.mb + D.K) * (D.N * D.K) +
        2 * gD D + 19 + rotationSum D) := by
  simp only [templateInitOps, finRange8, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, zeroInit, InitOp.cost,
    List.length_replicate, length_wd, fixedSize, BCol, Wb, Jh,
    AdvancedEncryption.ExpLUT.Col, Dig, Pos, Enum.length_prod, len_sum, len_fin,
    rotationSum]
  ring

set_option maxRecDepth 100000 in
theorem cost_templates_tight : ((templateInitOps Dc).map InitOp.cost).sum ≤ 10 * 2 ^ 99 := by
  rw [cost_templates_formula]
  have hr := rotationSum_le Dc
  generalize rotationSum Dc = r at *
  norm_num [fixedSize, BCol, Wb, Jh, AdvancedEncryption.ExpLUT.Col, Dig, Pos,
    Enum.length_prod, len_sum, len_fin, Dc, Kc, mbar,
    PE.BranchingProgram.w8, PE.BranchingProgram.Width.len, gD, SigabaNeo.Lattices.gGen] at *
  omega

theorem cost_public : ((publicInitOps Dc).map InitOp.cost).sum ≤ 2 ^ 108 :=
  cost_public_tight.trans (by norm_num)

theorem cost_coins : ((coinInitOps Dc).map InitOp.cost).sum ≤ 2 ^ 108 :=
  cost_coins_tight.trans (by norm_num)

theorem cost_templates : ((templateInitOps Dc).map InitOp.cost).sum ≤ 2 ^ 108 :=
  cost_templates_tight.trans (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.EncConf
