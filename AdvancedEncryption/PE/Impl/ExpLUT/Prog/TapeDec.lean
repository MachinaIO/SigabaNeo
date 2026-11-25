import SigabaNeoStd.Machines.Pack.Leaves
import PE.Impl.ExpLUT.Prog.DecTight
import PE.Impl.ExpLUT.Prog.DescTightDec
/-!
# The packed decryption machine (fewer physical tapes)

`decMachineP := packMachineT 37 8 (decProgram Dc) 255 0 (decInputLength Dc predLen)`: the `Dec`
program compiled by the packing translation onto `5 + 37 + 8 = 50` physical tapes instead of `256`.
Every instruction of the ring-word machine is a sequence of frames on at most `37` tapes, so it runs
as leaf groups; only the machine's control (sequences, branches, `rep` loops) is packed.

* **`decSpec_decMachineP : DecSpec Dc predLen decMachineP`**: deterministic (the program is
  coin-free, `deterministic_packMachineT`) with the output law of `DecM.decMP`
  (`run_packMachineT`);
* `okX_decProgram`: the wide loops nest at most `8` deep;
* **`descLen_decMachineP : decMachineP.descLen ≤ 2 ^ 137`**.
-/

namespace AdvancedEncryption.ExpLUT.Prog.TapeDec

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Pack AdvancedEncryption.ExpLUT.Params
open AdvancedEncryption.ExpLUT.Prog.DecM

/-- The workspace width. -/
abbrev wD : ℕ := 37
/-- The nesting depth of the wide loops. -/
abbrev dD : ℕ := 8

/-- **The packed decryption machine**, `50` tapes. -/
noncomputable def decMachineP : Machine :=
  packMachineT wD dD (decProgram Dc) 255 0 (decInputLength Dc predLen)

theorem tapes_decMachineP : decMachineP.tapes = 50 := rfl

/-! ### The depth condition -/

theorem loopDepth_natP {k : ℕ} (t c : Fin k) :
    ∀ n, Pack.XProg.loopDepth (XProg.natP t c n) ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [XProg.natP, Pack.XProg.loopDepth, Pack.Prog.loopDepth]
    · have h := ih ((n + 1) / 2) (by omega)
      rw [XProg.natP]
      split_ifs <;>
        simp only [Pack.XProg.loopDepth, XProg.dblP, XProg.forN, XProg.bitAp,
          Pack.Prog.loopDepth] <;> omega

theorem loopDepth_tmplsP {k : ℕ} (c : Fin k) :
    ∀ l : List (Fin k × ℕ), Pack.XProg.loopDepth (tmplsP c l) ≤ 1
  | [] => by simp [tmplsP, Pack.XProg.loopDepth, Pack.Prog.loopDepth]
  | p :: l => by
    have h1 := loopDepth_natP p.1 c p.2
    have h2 := loopDepth_tmplsP c l
    simp only [tmplsP, Pack.XProg.loopDepth]
    omega

set_option maxRecDepth 100000 in
theorem loopDepth_decCode : Pack.XProg.loopDepth (RingVM.compile decCode) ≤ 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem loopDepth_parseX : Pack.XProg.loopDepth parseX ≤ 8 := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The depth condition** of the `Dec` program. -/
theorem okX_decProgram : OkX wD dD 0 (decProgram Dc) := by
  show OkX wD dD 0 (.seq parseX (.seq lenX (.ifBit 249
    (.seq (tmplsP 250 (tmplList Dc)) (.seq (.prog DecM.constP)
      (.seq (.frame RingVM.vmE (RingVM.compile decCode)) (.prog DecM.outP)))) (.prog DecM.invP))))
  exact Or.inr ⟨okX_of_loopDepth 0 _ (by have := loopDepth_parseX; show 0 + _ ≤ 8; omega),
    Or.inr ⟨Or.inr (Or.inl (by decide)), Or.inr ⟨Or.inr ⟨okX_of_loopDepth 0 _
      (by have := loopDepth_tmplsP (250 : Fin 256) (tmplList Dc); show 0 + _ ≤ 8; omega),
      Or.inr ⟨Or.inr (okP_of_loopDepth 0 _ (by decide +kernel)),
        Or.inr ⟨Or.inr (okX_of_loopDepth 0 _
          (by have := loopDepth_decCode; show 0 + _ ≤ 8; omega)),
          Or.inr (okP_of_loopDepth 0 _ (by decide +kernel))⟩⟩⟩,
      Or.inr (okP_of_loopDepth 0 _ (by decide +kernel))⟩⟩⟩

/-! ### The specification -/

/-- **The packed decryption machine meets `DecSpec`.** -/
theorem decSpec_decMachineP : DecSpec Dc predLen decMachineP := by
  refine ⟨deterministic_packMachineT _ (coinFree_decProgram Dc) _ _ _, fun sk C ct hL => ?_⟩
  rw [decMachineP, run_packMachineT (by norm_num) _ okX_decProgram (wf_decProgram Dc) _ _ _ _
    (length_decInput Dc sk C ct hL), law_decProgram Dc rfl]

/-! ### The description length -/

set_option exponentiation.threshold 2000 in
theorem descLen_dec_num : 6 * (stA 37 256 * 2 ^ 28 + 96 * 256 + 254) * 3 ^ 50 *
    (4 + 4 * 50 + 47) ≤ 2 ^ 137 := by
  unfold stA; norm_num

set_option exponentiation.threshold 2000 in
/-- **The packed decryption machine has a description of at most `2^137` bits.** -/
theorem descLen_decMachineP : decMachineP.descLen ≤ 2 ^ 137 := by
  have hS : (decProgram Dc).size ≤ 2 ^ 28 := by
    have := DecConf.size_decProgram; omega
  have h := descLen_packMachineT_le (w := wD) (D := dD) (decProgram Dc) 255 0
    (decInputLength Dc predLen) (m := 47) hS le_rfl (by unfold stA; norm_num)
  exact h.trans descLen_dec_num

end AdvancedEncryption.ExpLUT.Prog.TapeDec
