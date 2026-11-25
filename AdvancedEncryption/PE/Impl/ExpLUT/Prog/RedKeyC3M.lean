import PE.Impl.ExpLUT.Prog.RedKeyC3MB
import PE.Impl.ExpLUT.Prog.RedKeyC3MH
import PE.Impl.ExpLUT.Prog.RedKeyC3Fin

/-!
# Cost certificate of `mid`, phase M3: `pkOf pkt`, and the closed final statement

**`m3_h3 : Cert (MVM.compile (pkOf pkt)) c3In (c4L (bx m3E9)) (2 ^ 303)`**, the M3 obligation of
`RedKeyC.c3_spec`, from the nine checked phases (`RedKeyC3MH`, analyzer `RedKeyC3MA`, mirrors
`RedKeyC3MT`/`RedKeyC3MB`), with `bx m3E9 ≤ bx c4In` (`m3_x_le`).

**`RedKeyC.c3_spec_closed`**: the final `Spec` of the Submission from the two code-weight bounds
(`hw3`, `hw4`) alone.
-/

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 2000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC3M

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.RedKeyC4
open AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

theorem m3_pkOf_eq : pkOf pkt = .seq (pkConstC Dc) (.seq (pkCfC Dc) (.seq pkMoveC
    (.seq (templateOpsC (pkSwOps Dc)) (.seq pkWalkC (.seq (templateOpsC (pkPbOps Dc))
    (.seq pbPubC (.seq (templateOpsC (pkLpOps Dc)) pkFinC))))))) := rfl

theorem m3_compile_seq (p q : Code) :
    MVM.compile (.seq p q) = .seq (MVM.compile p) (MVM.compile q) := rfl

/-- **The M3 certificate** on the layout `c4L`. -/
theorem m3_cert (x : Fin 64 → ℕ) (hx : x ≤ bx m3In) :
    Cert (MVM.compile (pkOf pkt)) (c4L x) (c4L (bx m3E9)) (2 ^ 303) := by
  have p0 := m3Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) m3_er_const m3_ok0 x hx
  have p1 := m3Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) m3_er_cf m3_ok1 _
    le_rfl
  have p2 := m3Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) (.a (.c _)) m3_ok2 _
    le_rfl
  have p3 := m3Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) m3_er_sw m3_ok3 _
    le_rfl
  have p4 := m3Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) (.a (.c _)) m3_ok4 _
    le_rfl
  have p5 := m3Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) m3_er_pb m3_ok5 _
    le_rfl
  have p6 := m3Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) (.a (.c _)) m3_ok6 _
    le_rfl
  have p7 := m3Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) m3_er_lp m3_ok7 _
    le_rfl
  have p8 := m3Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) (.a (.c _)) m3_ok8 _
    le_rfl
  rw [m3_pkOf_eq]
  simp only [m3_compile_seq]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (p7.seq p8)))))))).mono le_rfl
    le_rfl (by norm_num)

theorem m3_in_le : RedKeyC.c3InB ≤ bx m3In := by
  intro r
  simp only [RedKeyC.c3InB, bx, m3In, Function.update_apply]
  revert r
  decide +kernel

/-- **The M3 obligation of `c3_spec`.** -/
theorem m3_h3 : Cert (MVM.compile (pkOf pkt)) RedKeyC.c3In (c4L (bx m3E9)) (2 ^ 303) :=
  (m3_cert RedKeyC.c3InB m3_in_le).mono RedKeyC.c3In_le le_rfl le_rfl

theorem m3_x_le : bx m3E9 ≤ bx c4In := leL_sound m3_E9_le

end AdvancedEncryption.ExpLUT.Prog.RedKeyC3M

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.RedKeyM
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid AdvancedEncryption.ExpLUT.Prog.RedKeyC4
open AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic

/-- **The final statement**, from the weights of the M3/M4 codes alone. -/
theorem c3_spec_closed
    (hw3 : codeWeight (pkOf RedKeyPkt.pkt) ≤ 2 ^ 160)
    (hw4 : codeWeight (simKeyC Dc) + codeWeight (setXC Dc) + codeWeight simXC ≤ 2 ^ 160) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) Sub.registry
      (Sub.submissionOf DecConf.decMachine Sub.decMachine_det Sub.Ncost) :=
  c3_spec (bx RedKeyC3M.m3E9) RedKeyC3M.m3_x_le (2 ^ 303) (by norm_num) RedKeyC3M.m3_h3 hw3 hw4

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
