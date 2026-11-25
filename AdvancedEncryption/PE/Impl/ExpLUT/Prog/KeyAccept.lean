import PE.Impl.ExpLUT.Prog.KeyProposal
import PE.Impl.ExpLUT.Prog.KeyBoxLoop

/-! Constant initialization and single-try acceptance of an assembled key proposal. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM encM)

/-- Append a fixed bit word using true on5 and false on rB1. -/
def emitBitsC (dst : Fin 64) : List Bool → Code
  | [] => .nop
  | b :: bs => .seq (.app dst (if b then 5 else rB1)) (emitBitsC dst bs)

theorem emitBitsC_frame (dst r : Fin 64) (hr : r ≠ dst) :
    ∀ bs, (emitBitsC dst bs).writes r = false
  | [] => rfl
  | b :: bs => by simp [emitBitsC, Code.writes, emitBitsC_frame dst r hr bs, Ne.symm hr]

theorem wf_emitBitsC (dst : Fin 64) : ∀ bs, (emitBitsC dst bs).WFc
  | [] => trivial
  | _ :: bs => ⟨trivial, wf_emitBitsC dst bs⟩

theorem exec_emitBitsC {N K : ℕ} (dst : Fin 64) (h5 : dst ≠ 5) (hb : dst ≠ rB1) :
    ∀ (bs : List Bool) (w : St), w 5 = [true] → w rB1 = [false] →
    exec N K (emitBitsC dst bs) w = Function.update w dst (w dst ++ bs)
  | [], w, _, _ => by simp [emitBitsC]
  | b :: bs, w, ht, hf => by
    rw [emitBitsC, exec_seq, exec_emitBitsC dst h5 hb bs _
      (by simpa [exec_app, h5.symm] using ht) (by simpa [exec_app, hb.symm] using hf)]
    cases b <;> simp [exec_app, ht, hf, List.append_assoc]

/-- Construct the all-coefficients radius word from one K-bit constant, repeated N times. -/
noncomputable def radiusC (N K r : ℕ) : Code :=
  .seq (.clr 7) <| .seq (bitsC 5 6 7) <| .seq (.clr rRR) <|
  .seq (emitBitsC rRR (encM K (r : ZMod (2 ^ K - 1)))) <|
  .seq (.cp 7 rRR) <| .seq (.clr rRR) <|
  .seq (natC 2 rB1 N) (repAppC 2 rRR 7)

theorem wf_radiusC (N K r : ℕ) : (radiusC N K r).WFc := by
  refine ⟨trivial, ?_, trivial, wf_emitBitsC _ _, trivial, trivial, natC_wfc _ _ _, ?_⟩
  · simp [bitsC, Code.WFc]
  · simp [repAppC, Code.WFc, Code.writes]

theorem radiusC_frame (N K r : ℕ) (j : Fin 64)
    (h : j ∉ [2, 5, 6, 7, rRR]) : (radiusC N K r).writes j = false := by
  have hj2 : j ≠ 2 := fun he ↦ h (by simp [he])
  have hj5 : j ≠ 5 := fun he ↦ h (by simp [he])
  have hj6 : j ≠ 6 := fun he ↦ h (by simp [he])
  have hj7 : j ≠ 7 := fun he ↦ h (by simp [he])
  have hjR : j ≠ rRR := fun he ↦ h (by simp [he])
  simp [radiusC, bitsC, repAppC, Code.writes, natC_writes _ _ _ j hj2,
    emitBitsC_frame _ _ hjR, Ne.symm hj2, Ne.symm hj5, Ne.symm hj6, Ne.symm hj7, Ne.symm hjR]

theorem exec_radiusC {N K : ℕ} (r : ℕ) (w : St) (hb : w rB1 = [false]) :
    exec N K (radiusC N K r) w rRR = encRM N K (allC N (r : ZMod (2 ^ K - 1))) := by
  rw [radiusC, exec_seq, exec_seq,
    exec_bitsC _ _ _ (by decide) (by decide) (by decide) _ (by simp), exec_seq, exec_seq,
    exec_emitBitsC _ (by decide) (by decide) _ _ (by simp) (by simpa using hb)]
  simp only [exec_seq]
  rw [exec_natC _ _ (by decide) _ _ (by simpa using hb),
    exec_repAppC _ _ _ (by decide) (by decide) (by decide)]
  simp only [exec_clr, exec_cp, Function.update_self, Function.update_apply,
    Fin.reduceEq, ↓reduceIte, List.nil_append, List.length_replicate]
  exact (encRM_ofCoeffs_const _).symm

/-- Install every family-test input after the proposal computation has finished. -/
noncomputable def acceptInitC (D : Dims) (B r : ℕ) : Code :=
  .seq (radiusC D.N D.K r) <|
  .seq (natC rTBk rB1 B) <| .seq (natC rTKB rB1 (D.K - B)) <|
  .seq (.cp rQa 18) (natC rQc rB1 (Enum.list (α := PIdxD D)).length)

theorem wf_acceptInitC (D : Dims) (B r : ℕ) : (acceptInitC D B r).WFc :=
  ⟨wf_radiusC _ _ _, natC_wfc _ _ _, natC_wfc _ _ _, trivial, natC_wfc _ _ _⟩

theorem exec_acceptInitC (D : Dims) (B r : ℕ) (w : St)
    (x : PIdxD D → Rg D) (hx : w 18 = encL D.N D.K (Enum.list.map x))
    (hb : w rB1 = [false]) (hz : w rZ = encRM D.N D.K 0) :
    let v := exec D.N D.K (acceptInitC D B r) w
    BoxTestReady D.N D.K B r v ∧
    v rQa = encL D.N D.K (Enum.list.map x) ∧
    v rQc = List.replicate (Enum.list (α := PIdxD D)).length false := by
  let u := exec D.N D.K (radiusC D.N D.K r) w
  have hf : ∀ j : Fin 64, j ∉ [2, 5, 6, 7, rRR] → u j = w j :=
    fun j hj ↦ exec_writes _ _ _ (radiusC_frame _ _ _ j hj)
  have ub : u rB1 = [false] := (hf _ (by decide)).trans hb
  have uz : u rZ = encRM D.N D.K 0 := (hf _ (by decide)).trans hz
  have ux : u 18 = encL D.N D.K (Enum.list.map x) := (hf _ (by decide)).trans hx
  have ur := exec_radiusC (N := D.N) (K := D.K) r w hb
  dsimp only
  rw [acceptInitC, exec_seq]
  simp only [exec_seq]
  rw [exec_natC rTBk rB1 (by decide) _ u ub]
  rw [exec_natC rTKB rB1 (by decide) _ _ (by simpa using ub)]
  rw [exec_natC rQc rB1 (by decide) _ _ (by simpa using ub)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [exec_cp, Function.update_apply, ↓reduceIte]
  · exact ur
  · rfl
  · rfl
  · exact ub
  · exact uz
  · exact ux

theorem acceptInitC_frame (D : Dims) (B r : ℕ) (j : Fin 64)
    (hj : j = 19 ∨ j = rB1) : (acceptInitC D B r).writes j = false := by
  have hr := radiusC_frame D.N D.K r j (by rcases hj with rfl | rfl <;> decide)
  have hlow := natC_writes rTBk rB1 B j (by rcases hj with rfl | rfl <;> decide)
  have hhigh := natC_writes rTKB rB1 (D.K - B) j (by rcases hj with rfl | rfl <;> decide)
  have hcount := natC_writes rQc rB1 (Enum.list (α := PIdxD D)).length j
    (by rcases hj with rfl | rfl <;> decide)
  simp only [acceptInitC, Code.writes, hr, hlow, hhigh, hcount]
  rcases hj with rfl | rfl <;> decide

theorem keyEnc_zero (D : Dims) :
    (keyEnc D).enc 0 = List.replicate (codecSize (keyEnc D)) false := by
  rw [keyEnc_eq_encL]
  change encL D.N D.K (Enum.list.map (fun _ : KColt D ↦ (0 : Rg D))) = _
  rw [List.map_const', encL_zeros]
  rfl

/-- A single test: keep proposal19 on acceptance, overwrite it with the canonical zero key otherwise. -/
noncomputable def acceptC (D : Dims) (B r : ℕ) : Code :=
  .seq (acceptInitC D B r) <| .seq boxFamilyC
    (.ifb rTx .nop (natC 19 rB1 (codecSize (keyEnc D))))

theorem wf_acceptC (D : Dims) (B r : ℕ) : (acceptC D B r).WFc :=
  ⟨wf_acceptInitC _ _ _, wf_boxFamilyC, trivial, natC_wfc _ _ _⟩

/-- Exact single-try branch semantics, including the encoded zero key on rejection. -/
theorem exec_acceptC (D : Dims) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (w : St) (x : PIdxD D → Rg D) (k : Keyt D)
    (hx : w 18 = encL D.N D.K (Enum.list.map x)) (hk : w 19 = (keyEnc D).enc k)
    (hb : w rB1 = [false]) (hz : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (acceptC D B r) w 19 =
      (keyEnc D).enc (if x ∈ (kbOf D B hB r).Small then k else 0) := by
  let v := exec D.N D.K (acceptInitC D B r) w
  obtain ⟨ready, queue, count⟩ := exec_acceptInitC D B r w x hx hb hz
  have htest := exec_boxFamilyC D B r hB hBK hr hq hcount v ready x queue count
  let u := exec D.N D.K boxFamilyC v
  have uk : u 19 = (keyEnc D).enc k := by
    rw [show u 19 = v 19 from exec_writes _ _ _ (by decide),
      show v 19 = w 19 from exec_writes _ _ _ (acceptInitC_frame D B r 19 (Or.inl rfl)), hk]
  have ub : u rB1 = [false] := by
    rw [show u rB1 = v rB1 from exec_writes _ _ _ (by decide),
      show v rB1 = w rB1 from exec_writes _ _ _ (acceptInitC_frame D B r rB1 (Or.inr rfl)), hb]
  change exec D.N D.K (.ifb rTx .nop (natC 19 rB1 (codecSize (keyEnc D)))) u 19 = _
  change u rTx = _ at htest
  simp only [exec_ifb, htest, hd_cons, decide_eq_true_eq]
  by_cases ha : x ∈ (kbOf D B hB r).Small
  · simpa only [ha, ↓reduceIte, exec_nop] using uk
  · rw [ite_eq_right ha, ite_eq_right ha, exec_natC _ _ (by decide) _ u ub, Function.update_self,
      keyEnc_zero]

theorem assembleC_frame (D : Dims) (r : Fin 64)
    (hr : r ∉ [0, 1, 2, 3, 4, 19]) : (assembleC D).writes r = false := by
  have h0 : r ≠ 0 := fun he ↦ hr (by simp [he])
  have h19 : r ≠ 19 := fun he ↦ hr (by simp [he])
  have hg (js : List ℕ) := gatherC_preserves D.N D.K js r
    (by intro he; exact hr (by simp [he])) (by intro he; exact hr (by simp [he]))
    (by intro he; exact hr (by simp [he])) (by intro he; exact hr (by simp [he]))
  simp [assembleC, saveQueueC, Code.writes, hg, Ne.symm h0, Ne.symm h19]

theorem proposalKeyC_templates (D : Dims) (r : Fin 64) (hr : r = rB1 ∨ r = rZ) :
    (proposalKeyC D).writes r = false := by
  have hp := proposalC_templates D r hr
  have ha := assembleC_frame D r (by rcases hr with rfl | rfl <;> decide)
  simp [proposalKeyC, Code.writes, hp, ha]

/-- One deterministic attempt from a sampled candidate; no retry on rejection. -/
noncomputable def tryKeyC (D : Dims) (B r : ℕ) : Code :=
  .seq (proposalKeyC D) (acceptC D B r)

theorem wf_tryKeyC (D : Dims) (B r : ℕ) : (tryKeyC D B r).WFc :=
  ⟨wf_proposalKeyC _, wf_acceptC _ _ _⟩

open Classical in
/-- Complete deterministic single-try semantics after sampling and EvalPK. -/
theorem exec_tryKeyC (D : Dims) (hK : 2 ≤ D.K) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (mpk : MPKt D) (F : BP Pos)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) (w : St)
    (hM : w 14 = (mpkEnc D).enc mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (hT : w 16 = (matE D (Wb D) (Fin D.K)).enc T)
    (hP : w 9 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    let z := gadDec (S := setting D) (keyTarget mpk - pubShort (helperMap D) mpk F p)
    let x := p - realTrap (S := setting D) (J := Jh D) T z
    exec D.N D.K (tryKeyC D B r) w 19 = (keyEnc D).enc
      (if x ∈ (kbOf D B hB r).Small then assemble (S := setting D) x z else 0) := by
  let z := gadDec (S := setting D) (keyTarget mpk - pubShort (helperMap D) mpk F p)
  let x := p - realTrap (S := setting D) (J := Jh D) T z
  let v := exec D.N D.K (proposalKeyC D) w
  have hk := exec_proposalKeyC D hK mpk F T p w hM hA hT hP h1 hZ
  have hx : v 18 = encL D.N D.K (Enum.list.map x) := by
    change exec D.N D.K (assembleC D) (exec D.N D.K (proposalC D) w) 18 = _
    rw [exec_writes _ _ _ (assembleC_frame D 18 (by decide))]
    exact (exec_proposalC D hK mpk F T p w hM hA hT hP h1 hZ).2
  have vb : v rB1 = [false] :=
    (exec_writes _ _ _ (proposalKeyC_templates D rB1 (Or.inl rfl))).trans h1
  have vz : v rZ = encRM D.N D.K 0 :=
    (exec_writes _ _ _ (proposalKeyC_templates D rZ (Or.inr rfl))).trans hZ
  let k : Keyt D := assemble (S := setting D) x z
  let x' : PIdxD D → Rg D := x
  have h := exec_acceptC D B r hB hBK hr hq hcount v x' k hx hk vb vz
  change exec D.N D.K (acceptC D B r) v 19 = (keyEnc D).enc
    (if x ∈ (kbOf D B hB r).Small then assemble (S := setting D) x z else 0)
  by_cases hm : x' ∈ (kbOf D B hB r).Small
  · rw [ite_eq_left hm] at h
    have hm' : x ∈ (kbOf D B hB r).Small := hm
    simp only [hm', ↓reduceIte]
    exact h
  · rw [ite_eq_right hm] at h
    have hm' : x ∉ (kbOf D B hB r).Small := hm
    simp only [hm', ↓reduceIte]
    exact h

end AdvancedEncryption.ExpLUT.Prog
