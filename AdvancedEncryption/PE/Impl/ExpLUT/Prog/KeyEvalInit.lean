import PE.Impl.ExpLUT.Prog.KeyEvalFront
/-! Executable initialization of the EvalPK constant templates. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

/-- Fixed words use literal bits; unary zero templates use binary doubling. -/
inductive TemplateWord where
  | zeros (n : ℕ)
  | bits (bs : List Bool)

def TemplateWord.value : TemplateWord → List Bool
  | .zeros n => List.replicate n false
  | .bits bs => bs

def TemplateWord.code (dst : Fin 64) : TemplateWord → Code
  | .zeros n => natC dst rB1 n
  | .bits bs => .seq (.clr dst) (emitBitsC dst bs)

theorem TemplateWord.wf (dst : Fin 64) (a : TemplateWord) : (a.code dst).WFc := by
  cases a with
  | zeros n => exact natC_wfc _ _ _
  | bits bs => exact ⟨trivial, wf_emitBitsC _ _⟩

theorem TemplateWord.frame (dst r : Fin 64) (a : TemplateWord) (h : r ≠ dst) :
    (a.code dst).writes r = false := by
  cases a with
  | zeros n => exact natC_writes _ _ _ _ h
  | bits bs => simp [code, Code.writes, emitBitsC_frame _ _ h, Ne.symm h]

theorem TemplateWord.exec {N K : ℕ} (dst : Fin 64) (h5 : dst ≠ 5) (h38 : dst ≠ rB1)
    (a : TemplateWord) (w : St) (ht : w 5 = [true]) (hf : w rB1 = [false]) :
    MVM.exec N K (a.code dst) w = Function.update w dst a.value := by
  cases a with
  | zeros n => exact exec_natC _ _ h38 _ _ hf
  | bits bs =>
    rw [code, exec_seq, exec_emitBitsC dst h5 h38 bs _
      (by simpa [exec_clr, h5.symm] using ht) (by simpa [exec_clr, h38.symm] using hf)]
    simp [exec_clr, value]

def templateOpsC : List (Fin 64 × TemplateWord) → Code
  | [] => .nop
  | (r, a) :: ops => .seq (a.code r) (templateOpsC ops)

def templateOpsState (ops : List (Fin 64 × TemplateWord)) (w : St) : St :=
  ops.foldl (fun v op ↦ Function.update v op.1 op.2.value) w

theorem wf_templateOpsC : ∀ ops, (templateOpsC ops).WFc
  | [] => trivial
  | (_, a) :: ops => ⟨a.wf _, wf_templateOpsC ops⟩

theorem templateOpsC_frame (r : Fin 64) : ∀ ops,
    (∀ op ∈ ops, r ≠ op.1) → (templateOpsC ops).writes r = false
  | [], _ => rfl
  | (dst, a) :: ops, h => by
    have ha := TemplateWord.frame dst r a (h (dst, a) (by simp))
    simp only [templateOpsC, Code.writes, ha,
      templateOpsC_frame r ops (by intro op hop; exact h op (by simp [hop])), Bool.or_self]

theorem exec_templateOpsC {N K : ℕ} : ∀ (ops : List (Fin 64 × TemplateWord)) (w : St),
    (∀ op ∈ ops, op.1 ≠ 5 ∧ op.1 ≠ rB1) → w 5 = [true] → w rB1 = [false] →
    exec N K (templateOpsC ops) w = templateOpsState ops w
  | [], _, _, _, _ => rfl
  | (dst, a) :: ops, w, h, ht, hf => by
    have hd := h (dst, a) (by simp)
    rw [templateOpsC, exec_seq, a.exec dst hd.1 hd.2 w ht hf,
      exec_templateOpsC ops _ (by intro op hop; exact h op (by simp [hop]))
        (by simpa [hd.1.symm] using ht) (by simpa [hd.2.symm] using hf)]
    rfl

/-- All fixed EvalPK inputs; no public-key-dependent values occur here. -/
noncomputable def evalInitOps (D : Dims) : List (Fin 64 × TemplateWord) :=
  [(rKc, .zeros (gD D)), (rBit1, .zeros 1), (rTb, .zeros D.b),
   (rTBlk, .zeros (16 * D.K ^ 3 * (D.N * D.K))),
   (rTK, .zeros D.K), (rTK1, .zeros (D.K - 1)), (rZ, .zeros (D.N * D.K)),
   (rT2K, .zeros (2 * D.K)), (rTKNK, .zeros (D.K * (D.N * D.K))),
   (rT2KNK, .zeros (2 * D.K * (D.N * D.K))),
   (rT4KNK, .zeros (2 * (2 * D.K) * (D.N * D.K))),
   (rOne, .bits (encRM D.N D.K 1)),
   (rMu0, .bits (encRM D.N D.K (xInvG (ZMod D.q) D.N))),
   (rT4K, .zeros (4 * D.K)), (rTW, .zeros (2 ^ D.b)), (rTtab, .zeros tlK),
   (rXc, .bits (encRM D.N D.K (xcK D))), (rTe, .zeros 14), (rT15, .zeros 15)]

/-- Initialize from any state, preserving the predicate and saved keys. -/
noncomputable def evalInitC (D : Dims) : Code :=
  .seq (.clr 6) <| .seq (bitsC 5 rB1 6) (templateOpsC (evalInitOps D))

theorem wf_evalInitC (D : Dims) : (evalInitC D).WFc :=
  ⟨trivial, by repeat constructor, wf_templateOpsC _⟩

theorem exec_evalInitC (D : Dims) (w : St) :
    exec D.N D.K (evalInitC D) w = templateOpsState (evalInitOps D)
      (Function.update (Function.update (Function.update w 6 []) 5 [true]) rB1 [false]) := by
  rw [evalInitC, exec_seq, exec_seq,
    exec_bitsC _ _ _ (by decide) (by decide) (by decide) _ (by simp)]
  apply exec_templateOpsC
  · simp [evalInitOps]
  · simp
  · simp

theorem evalInitC_ready (D : Dims) (w : St) :
    EvalTemplates D (exec D.N D.K (evalInitC D) w) := by
  rw [exec_evalInitC]
  constructor
  all_goals constructor
  all_goals simp [templateOpsState, evalInitOps, TemplateWord.value,
    encRM_zero, encL_replicate_zero]

theorem evalInitC_saved (D : Dims) (r : Fin 64) (hr : r = 3 ∨ r = 16 ∨ r = 17) :
    (evalInitC D).writes r = false := by
  have hf : (templateOpsC (evalInitOps D)).writes r = false := by
    apply templateOpsC_frame
    rcases hr with rfl | rfl | rfl <;> simp [evalInitOps]
  rcases hr with rfl | rfl | rfl <;> simp [evalInitC, Code.writes, bitsC, hf]

theorem evalInitC_bit (D : Dims) (w : St) : exec D.N D.K (evalInitC D) w rB1 = [false] := by
  rw [exec_evalInitC]
  simp [templateOpsState, evalInitOps, TemplateWord.value]

/-- EvalPK with its complete constant initializer. -/
noncomputable def evalReadyC (D : Dims) : Code := .seq (evalInitC D) (evalPublicC D)

theorem wf_evalReadyC (D : Dims) : (evalReadyC D).WFc :=
  ⟨wf_evalInitC D, wf_evalPublicC D⟩

theorem exec_evalReadyC (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (mpk : MPKt D) (C : List Bool) (w : St)
    (hs : w 17 = (mpkEnc D).enc mpk) (hp : w rCs = C) :
    exec D.N D.K (evalReadyC D) w rA =
      encL D.N D.K (matL (keyPK (helperMap D) mpk (bpOf (progOf C)))) := by
  rw [evalReadyC, exec_seq]
  apply exec_evalPublicC D hb hn mpk C _ _ (evalInitC_bit D w) (evalInitC_ready D w)
  · exact (exec_writes _ _ _ (evalInitC_saved D 3 (by simp))).trans hp
  · exact (exec_writes _ _ _ (evalInitC_saved D 17 (by simp))).trans hs

theorem evalReadyC_saved (D : Dims) (r : Fin 64) (hr : r = 16 ∨ r = 17) :
    (evalReadyC D).writes r = false := by
  simp only [evalReadyC, Code.writes, evalInitC_saved D r (Or.inr hr),
    evalPublicC_saved D r hr, Bool.or_self]

end AdvancedEncryption.ExpLUT.Prog
