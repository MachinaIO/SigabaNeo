import PE.Impl.ExpLUT.Prog.EncDescConf
import PE.Impl.ExpLUT.Prog.DescTightBase
/-!
# Tight description length of the concrete encryption machine

The state count of `encProgram Dc 16 6 eFl` is dominated by the unrolled literal readers
(`60` states per bit, `InitOp.cost`) and by the input normalization (`60` states per bit of the
coin and public words, `size_normalizeInputsP`). In units of `2^91` bits: the public word is
`≈ 76.003`, the coin word `≈ 38.001`, the ciphertext template `≈ 38.001`; so the program has
`≈ 60 · (76 + 38 + 38 + 114) · 2^91 ≈ 2^104.96` states.

Bounds used: public reads `≤ 20 · 2^99`, coin reads `≤ 10 · 2^99`, templates `≤ 10 · 2^99`
(`EncConf.cost_*_tight`), normalization lengths `≤ 115 · 2^91` (`normalization_lengths_tight`),
so `size + 4 ≤ 2^105 + 2^101` (`size_encProgram_tight`), and with entry width
`4 + 4·326 + 106`:
**`descLen_encMachine_tight : encMachine.descLen ≤ 2^635`**
(`log₂(6 · (2^105 + 2^101) · 3^326 · 1414) ≈ 634.84`; the true value is `≈ 2^634.7`, so `635` is
the optimal integer exponent for this machine).
-/

set_option autoImplicit false

namespace AdvancedEncryption.ExpLUT.Prog.EncConf
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape
open AdvancedEncryption.ExpLUT.Params EncW
open AdvancedEncryption.ExpLUT.Prog.DescTight

/-- The complete coin and public queues: `≈ 114.004 · 2^91` bits. -/
theorem normalization_lengths_tight : coinLength Dc + publicLength Dc ≤ 115 * 2 ^ 91 := by
  simp only [coinLength, publicLength, fixedSize, BCol, Wb, Jh, Col, Dig, Pos,
    Enum.length_prod, len_sum, len_fin]
  norm_num [Dc, Kc, mbar, PE.BranchingProgram.w8, PE.BranchingProgram.Width.len]

theorem size_normalization_tight : (normalizeInputsP Dc).size ≤ 20000 + 60 * (115 * 2 ^ 91) :=
  (size_normalizeInputsP Dc).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 60 normalization_lengths_tight) 20000)

theorem cost_initialization_tight : ((encInitOps Dc).map InitOp.cost).sum ≤ 40 * 2 ^ 99 := by
  simp only [encInitOps, List.map_append, List.sum_append]
  have h := Nat.add_le_add (Nat.add_le_add cost_public_tight cost_coins_tight) cost_templates_tight
  exact h.trans (by norm_num)

theorem size_encProgram_tight_num :
    2 ^ 22 + 40 * 2 ^ 99 + 2 ^ 40 + (20000 + 60 * (115 * 2 ^ 91)) + 21916 + 4 ≤
      2 ^ 105 + 2 ^ 101 := by
  norm_num

/-- **State count of the complete encryption program**: at most `2^105 + 2^101`. -/
theorem size_encProgram_tight : (encProgram Dc 16 6 eFl).size + 4 ≤ 2 ^ 105 + 2 ^ 101 := by
  have h := Nat.add_le_add_right (size_encProgram_le Dc 16 6 eFl) 4
  have hb := Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add size_prepare cost_initialization_tight) size_core)
      size_normalization_tight) 21916) 4
  exact h.trans (hb.trans size_encProgram_tight_num)

theorem descLen_encMP_eq_tight (D : Dims) (η L e : ℕ) : (encMP D η L e).descLen =
    6 * ((encProgram D η L e).size + 4) * 3 ^ 326 * 3 ^ 0 *
      Machine.entryBits 326 ((encProgram D η L e).size + 4) 0 := by
  rw [Machine.descLen, encMP, XProg.states_toMachineT, XProg.card_state]
  rfl

set_option exponentiation.threshold 2000 in
theorem descTight_enc_num : 6 * (2 ^ 105 + 2 ^ 101) * 3 ^ 326 * (4 + 4 * 326 + 106) ≤ 2 ^ 635 := by
  norm_num

/-- **The compiled encryption machine has a description of at most `2^635` bits.** -/
theorem descLen_encMachine_tight : encMachine.descLen ≤ 2 ^ 635 := by
  show (encMP Dc 16 6 eFl).descLen ≤ _
  rw [descLen_encMP_eq_tight]
  exact (descTight_arith size_encProgram_tight
    (by norm_num : (2 : ℕ) ^ 105 + 2 ^ 101 < 2 ^ 106)).trans descTight_enc_num

end AdvancedEncryption.ExpLUT.Prog.EncConf
