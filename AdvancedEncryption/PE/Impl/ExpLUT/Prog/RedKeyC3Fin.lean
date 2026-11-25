import PE.Impl.ExpLUT.Prog.RedKeyC3Glue
import PE.Impl.ExpLUT.Prog.RedKeyCSize
import PE.Impl.ExpLUT.Prog.RedKeyC4
import PE.Impl.ExpLUT.Prog.RedKeyPktOk
import PE.Impl.ExpLUT.Prog.RedKeyTSpec

/-!
# Cost certificate of `mid`: the assembly M1–M2 (+ glue) + M3 + M4

* **`c3_store`**: the storage bounds `c3G` after M1/`midStA` satisfy M4's `C4Store`;
* **`c3_midBound_of_m3`**: an M3 certificate `Cert (compile pk) c3In (c4L x) T` with
  `x ≤ bx c4In` and `T ≤ 2^438` gives **`RkMidBound (mid pk) c4Out`**
  (time `2^438` (head) `+ T + 2^412` (M4) `≤ 2^440`);
* **`c3_spec`**: with the weights of the M3/M4 codes (`cs_mid`), the final `Spec`
  (`RedKeyT.spec_of_mid`) for `mid (pkOf pkt)`.

The M3 obligation (`c3In_le`: the envelope `c3In` is below the layout `c4L c3InB` at the cap
`2^150`, so `RedKeyC4A.c4Ok_cert` can be used from `bx c3InL`):
`Cert (compile (pkOf pkt)) c3In (c4L x) T`, `x ≤ bx c4In`, `T ≤ 2^438`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 2000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.RedKeyM
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid AdvancedEncryption.ExpLUT.Prog.RedKeyC4
open AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic

theorem c3_store : C4Store c3G := by
  refine ⟨fun t => (c3G_top t).trans (by norm_num), c3G_vals.2.1.le, ?_⟩
  intro t ht h1 h2 h3 h4 h5
  simp only [c3G, Function.update_of_ne h1, c1Out, h2, h3, h4, h5, if_false]

/-- The register caps of `c3In` (`0` raw secret, `1` `ctW`, `2` `mpkW`, `rCs` = `C`). -/
def c3InB : Fin 64 → ℕ := Function.update (Function.update (Function.update (Function.update
  (fun _ => 0) 0 (2 ^ 101)) 1 (2 ^ 110)) 2 (2 ^ 102)) rCs predLen

theorem c3In_le : c3In ≤ c4L c3InB := by
  have hpt := preResult_inputs (2 ^ 104) Dc.N Dc.K c2L c2L_inputs.top (by rw [c3N]; norm_num)
    (by rw [c3K]; norm_num) (by rw [c3NK]; norm_num)
  apply le_layout _ _ _ c3InB _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t
    simp only [c3In, Function.update_apply]
    have := c1_predLen
    split_ifs <;> first | exact this.trans (by norm_num) | exact (hpt.top t).trans (by norm_num) | norm_num
  · simp only [c3In, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    simpa [c3K] using hpt.templateK
  · simp only [c3In, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    simpa [c3N] using hpt.templateN
  · simp only [c3In, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    simpa [c3NK] using hpt.zeros.le
  · simp only [c3In, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    simpa [c3NK] using hpt.ones
  · intro r
    by_cases h0 : r = 0
    · subst h0
      simp only [c3In, c3InB, layout_register]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_self,
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_self]
    by_cases h1 : r = 1
    · subst h1
      simp only [c3In, c3InB, layout_register]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self]
    by_cases h2 : r = 2
    · subst h2
      simp only [c3In, c3InB, layout_register]
      rw [Function.update_of_ne (by decide), Function.update_self,
        Function.update_of_ne (by decide), Function.update_self]
    by_cases h3 : r = rCs
    · subst h3
      simp only [c3In, c3InB, layout_register]
      rw [Function.update_self, Function.update_self]
    have n0 : tR r ≠ tR 0 := fun h => h0 (tR_inj h)
    have n1 : tR r ≠ tR 1 := fun h => h1 (tR_inj h)
    have n2 : tR r ≠ tR 2 := fun h => h2 (tR_inj h)
    have n3 : tR r ≠ tR rCs := fun h => h3 (tR_inj h)
    simp only [c3In, Function.update_of_ne n0, Function.update_of_ne n1, Function.update_of_ne n2,
      Function.update_of_ne n3]
    rw [c3_blank_le c2L (fun t => c2L_inputs.top t) (tR r) (fun h => h0 (tR_inj (h.trans rfl)))
      (fun h => h1 (tR_inj (h.trans rfl))) (by simp [tR])]
    exact Nat.zero_le _

/-- **`RkMidBound` from an M3 certificate.** -/
theorem c3_midBound_of_m3 (pk : Code) (x : Fin 64 → ℕ) (hx : x ≤ bx c4In) (T : ℕ)
    (hT : T ≤ 2 ^ 438) (h3 : Cert (MVM.compile pk) c3In (c4L x) T) :
    RedKeyT.RkMidBound (mid pk) c4Out := by
  have p3 : Cert (onM pk) (c3S c3In c3G) (c4Env x c3G) T := c3_onM pk h3 c3G
  have p4 := c4_cert_m4 x hx c3G c3_store
  have hc := c3_cert_head _ _ _ (p3.seq p4)
  rw [← mid_m4P] at hc
  exact ⟨hc.time.trans (by
    calc _ ≤ 2 ^ 438 + (2 ^ 438 + 2 ^ 412) := Nat.add_le_add_left (Nat.add_le_add_right hT _) _
      _ ≤ 2 ^ 440 := by norm_num), hc.len⟩

/-- **The final statement**, from the M3 certificate and the weights of the M3/M4 codes. -/
theorem c3_spec (x : Fin 64 → ℕ) (hx : x ≤ bx c4In) (T : ℕ) (hT : T ≤ 2 ^ 438)
    (h3 : Cert (MVM.compile (pkOf RedKeyPkt.pkt)) c3In (c4L x) T)
    (hw3 : codeWeight (pkOf RedKeyPkt.pkt) ≤ 2 ^ 160)
    (hw4 : codeWeight (simKeyC Dc) + codeWeight (setXC Dc) + codeWeight simXC ≤ 2 ^ 160) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) Sub.registry
      (Sub.submissionOf TapeDec.decMachineP Sub.decMachine_det Sub.Ncost) :=
  RedKeyT.spec_of_mid (mid (pkOf RedKeyPkt.pkt)) (wf_mid RedKeyPkt.wf_pkOf_pkt)
    RedKeyPkt.rkMidOk_pkt (cs_mid _ hw3 hw4)
    ⟨c4Out, c4_tailIn, c3_midBound_of_m3 _ x hx T hT h3⟩

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
