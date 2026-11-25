import PE.Impl.RingBTVW.ImplP
import PE.Impl.RingBTVW.Prog.CfX
import PE.Impl.RingBTVW.Prog.WfB2SCoinFree
import PE.Impl.RingBTVW.Prog.WfRCert
import PE.Impl.RingBTVW.Prog.KeyCfgP
import PE.Impl.RingBTVW.Prog.SetupEncCost
import PE.Impl.RingBTVW.Params.Stat

/-!
# The compiled implementation at `confP`

`implC`: the implementation with the compiled machines of `Setup`, `Enc` (`chiSamplerP`),
`KeyGen` and `Dec` (the shells with the front end `frontBP confP.L`, `ShellsBP`), the key-row block
`bfX` and the `c_f̂` block `cfX` around the stream block `wfB2S` at the store width `512` and the
instruction bound `2^50` (`WfSpecS` from `wfSpecR_wfB2S`, `wfSpecS_of_wfSpecR`), the key try of
`cfP`.

* **`correct_implC`**: `Correct PUniv BranchingProgram.params implC` (from `correct_conf`, which holds for any
  machines meeting the specifications);
* **`expressive_implC`**: `Expressive PUniv BranchingProgram.params implC`.
-/

namespace AdvancedEncryption.RingBTVW.Sub

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape AdvancedEncryption.PE
open AdvancedEncryption.RingBTVW.Prog AdvancedEncryption.RingBTVW.Params

theorem confP_d3 : 3 ≤ confP.d := by show 3 ≤ dp; rw [dp_def]; norm_num

theorem hK2 : 2 ≤ Kp := by rw [Kp_def]; norm_num

theorem Kp_pos : 0 < Kp := by rw [Kp_def]; norm_num

/-- The room for the stash of `KeyGen`: the trapdoor and the bit `f(0)` in `d − 1` rows. -/
theorem hSB : lenT Np Kp kp + 1 ≤ lenZ confP := by
  show RingBTVW.rowL Np Kp kp + Np * Kp + 1 ≤ (dp - 1) * RingBTVW.rowL Np Kp kp
  have hr : Np * Kp + 1 ≤ RingBTVW.rowL Np Kp kp := by
    simp only [RingBTVW.rowL, kp]
    have : 1 ≤ Np * Kp := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero Np_pos.ne' Kp_pos.ne')
    nlinarith
  have hd : 2 ≤ dp - 1 := by rw [dp_def]; norm_num
  have := Nat.mul_le_mul_right (RingBTVW.rowL Np Kp kp) hd
  omega

/-- The stream block at `confP`. -/
noncomputable abbrev wfC : XProg 256 := wfB2S hkp confP WB2.Icn WB2.Wn

theorem wfSpecS_wfC : WfSpecS hkp confP wfC 512 :=
  wfSpecS_of_wfSpecR (wfSpecR_wfB2S hkp confP WB2.Icn WB2.Wn Np_pos Kp_pos) (by decide)
    le_rfl

theorem len_AttrP :
    (Encode.Enum.list (α := (Sdw (N := Np) hkp).Attr)).length = nA := Algo.len_fin _

/-- The room for the stash of `Dec`: the key, `Ψ`, `c₀`, `c₁`, `κ` and the bit `f(0)`. -/
theorem hSC : lenKA hkp confP + Np * Kp + 1 ≤ lenZ confP := by
  simp only [lenKA, lenZ, RingBTVW.rowL, lPsi, fixLen, fencLen, Encode.Enum.length_prod,
    Algo.len_fin, Algo.len_col, Algo.len_trapCol, len_AttrP]
  show _ ≤ (dp - 1) * _
  have hQ : 1 ≤ Np * Kp := Nat.mul_pos Np_pos Kp_pos
  have hdp : confP.d = dp := rfl
  rw [hdp]
  generalize Np * Kp = Q at *
  have hk2 : 2 ≤ kp := by rw [kp, Kp_def]; norm_num
  have hkle : kp ≤ 2 ^ 27 := kp_le
  have hd62 : dp = 2 ^ 62 := dp_def
  obtain ⟨D, hD⟩ : ∃ D, dp = D + 1 := ⟨dp - 1, by omega⟩
  rw [hD, Nat.add_sub_cancel]
  have hDk : 522 * kp + 6 ≤ 2 * D := by omega
  have h1 : 4 * D * Q ≤ 2 * kp * D * Q := by
    have := Nat.mul_le_mul_right (D * Q) (show 4 ≤ 2 * kp by omega)
    nlinarith
  have h2 : (2 * D + 522 * kp + 6) * Q ≤ 4 * D * Q := by
    have := Nat.mul_le_mul_right Q (show 2 * D + 522 * kp + 6 ≤ 4 * D by omega)
    linarith
  nlinarith

/-- The key-row block at `confP`. -/
noncomputable abbrev bfC : XProg 256 := bfX hkp confP wfC

/-- The `c_f̂` block at `confP`. -/
noncomputable abbrev cfC : XProg 256 := cfX hkp confP wfC

theorem bfSpec_C : BfSpec hkp confP bfC 512 := bfSpec_bfX confP_d3 hSB wfSpecS_wfC

theorem cfSpec_C : CfSpec hkp confP cfC 512 :=
  cfSpec_cfX confP_d3 hSC wfSpecS_wfC (coinFree_wfB2S hkp confP _ _)

/-- The machines of `implC`. -/
noncomputable abbrev msC : Machines hkp confP :=
  machinesP hkp confP chiSamplerP bfSpec_C cfSpec_C cfP cfP_valid hK2

/-- **The compiled implementation** at `confP`. -/
noncomputable def implC : Impl PE.sig := impl hkp confP msC

theorem implC_eq : implC = impl hkp confP msC := rfl


/-- **Correctness of the compiled implementation.** -/
theorem correct_implC : Correct PUniv BranchingProgram.params implC := by
  rw [implC_eq]; exact correct_conf (ms := msC)

/-- **Expressiveness of the compiled implementation.** -/
theorem expressive_implC : Expressive PUniv BranchingProgram.params implC := by
  rw [implC_eq]; exact expressive_conf (ms := msC)

end AdvancedEncryption.RingBTVW.Sub
