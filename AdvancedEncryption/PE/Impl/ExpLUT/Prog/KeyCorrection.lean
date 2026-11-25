import PE.Impl.ExpLUT.Prog.KeyTarget

/-! Wire-level loading and bounded-automorphism correction of candidate coordinates. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- Select coordinates from a saved source, placing the encoded queue in dst. -/
def loadFamilyC (N K : ℕ) (src dst : Fin 64) (js : List ℕ) : Code :=
  .seq (.cp 0 src) (saveQueueC (gatherC N K js) dst)

theorem wf_loadFamilyC (N K : ℕ) (src dst : Fin 64) (js : List ℕ) :
    (loadFamilyC N K src dst js).WFc := ⟨trivial, wf_gatherC _ _ _, trivial⟩

theorem loadFamilyC_frame (N K : ℕ) (src dst : Fin 64) (js : List ℕ) (r : Fin 64)
    (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4)
    (hd : r ≠ dst) : (loadFamilyC N K src dst js).writes r = false := by
  simp [loadFamilyC, Code.writes, Ne.symm h0,
    saveQueueC_frame _ _ _ (gatherC_preserves N K js r h1 h2 h3 h4) hd]

theorem exec_loadFamilyC {N K : ℕ} {α : Type} [Enum α] [DecidableEq α]
    (f : α → Rq N K) (is : List α) (src dst : Fin 64) (w : St)
    (hs : w src = encL N K (Enum.list.map f))
    (hb : w rB1 = [false]) (hz : w rZ = encRM N K 0) :
    exec N K (loadFamilyC N K src dst (is.map Enum.index)) w dst =
      encL N K (is.map f) := by
  rw [loadFamilyC, exec_seq, exec_saveQueueC]
  exact exec_gatherC_family f is _ (by simpa using hs)
    (by simpa using hb) (by simpa using hz)

open Classical in
noncomputable def correctionLoadC (D : Dims) (i : Fin (setting D).E.W) (row : Wb D) : Code :=
  .seq (loadFamilyC D.N D.K 16 rQa
    ((Enum.list (α := Fin D.K)).map (fun c ↦ Enum.index (row, c)))) <|
  .seq (loadFamilyC D.N D.K 17 rQb
    ((Enum.list (α := Fin (setting D).τ)).map (fun c ↦ Enum.index (i, c)))) <|
  loadFamilyC D.N D.K 9 rIa
    [Enum.index (Sum.inl (i, row) : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)]

/-- Correct one trapdoor coordinate using saved T16, z17 and candidate9. -/
noncomputable def correctionInlC (D : Dims) (i : Fin (setting D).E.W) (row : Wb D) : Code :=
  .seq (correctionLoadC D i row) <|
  .seq (natC rQc rB1 D.K) <|
  .seq (natC rQk rB1 (rowExponent D i.val)) autDotC

theorem wf_correctionInlC (D : Dims) (i : Fin (setting D).E.W) (row : Wb D) :
    (correctionInlC D i row).WFc :=
  ⟨⟨wf_loadFamilyC _ _ _ _ _, wf_loadFamilyC _ _ _ _ _, wf_loadFamilyC _ _ _ _ _⟩,
    natC_wfc _ _ _, natC_wfc _ _ _, wf_autDotC⟩

set_option maxHeartbeats 800000 in
/-- Loading supplies precisely the two dot-product rows and the original candidate coordinate. -/
theorem exec_correctionLoadC (D : Dims)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D)
    (i : Fin (setting D).E.W) (row : Wb D) (w : St)
    (ht : w 16 = (matE D (Wb D) (Fin D.K)).enc T)
    (hp : w 9 = encL D.N D.K (Enum.list.map p))
    (hzs : w 17 = encL D.N D.K (Enum.list.map z))
    (hb : w rB1 = [false]) (hz : w rZ = encRM D.N D.K 0) :
    let v := exec D.N D.K (correctionLoadC D i row) w
    v rQa = encL D.N D.K (List.ofFn (T row)) ∧
    v rQb = encL D.N D.K (List.ofFn (fun c : Fin D.K ↦ z (i, c))) ∧
    v rIa = encRM D.N D.K (p (.inl (i, row))) := by
  classical
  let ts := (Enum.list (α := Fin D.K)).map (fun c ↦ (row, c))
  let zs := (Enum.list (α := Fin (setting D).τ)).map (fun c ↦ (i, c))
  let ps : List (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) := [.inl (i, row)]
  let c1 := loadFamilyC D.N D.K 16 rQa (ts.map Enum.index)
  let c2 := loadFamilyC D.N D.K 17 rQb (zs.map Enum.index)
  let c3 := loadFamilyC D.N D.K 9 rIa (ps.map Enum.index)
  let v1 := exec D.N D.K c1 w
  let v2 := exec D.N D.K c2 v1
  have f1 : ∀ r : Fin 64, r ∉ [0, 1, 2, 3, 4, rQa] → v1 r = w r := by
    intro r hr
    apply exec_writes
    apply loadFamilyC_frame <;> intro he <;> exact hr (by simp [he])
  have f2 : ∀ r : Fin 64, r ∉ [0, 1, 2, 3, 4, rQb] → v2 r = v1 r := by
    intro r hr
    apply exec_writes
    apply loadFamilyC_frame <;> intro he <;> exact hr (by simp [he])
  have f3 : ∀ r : Fin 64, r ∉ [0, 1, 2, 3, 4, rIa] → exec D.N D.K c3 v2 r = v2 r := by
    intro r hr
    apply exec_writes
    apply loadFamilyC_frame <;> intro he <;> exact hr (by simp [he])
  have t1 : v1 rQa = encL D.N D.K (List.ofFn (T row)) := by
    have h := exec_loadFamilyC (fun rc : Wb D × Fin D.K ↦ T rc.1 rc.2) ts 16 rQa w
      (ht.trans (matE_enc_product D T)) hb hz
    have he : ts.map (fun rc : Wb D × Fin D.K ↦ T rc.1 rc.2) = List.ofFn (T row) := by
      simp only [ts, enum_map_ofFn, List.map_ofFn, Function.comp_def]
    rw [he] at h
    exact h
  have z2 : v2 rQb = encL D.N D.K (List.ofFn (fun c : Fin D.K ↦ z (i, c))) := by
    have h := exec_loadFamilyC z zs 17 rQb v1
      ((f1 _ (by decide)).trans hzs) ((f1 _ (by decide)).trans hb) ((f1 _ (by decide)).trans hz)
    have he : zs.map z = List.ofFn (fun c : Fin D.K ↦ z (i, c)) := by
      simp only [zs, enum_map_ofFn, List.map_ofFn, Function.comp_def]
      rfl
    rw [he] at h
    exact h
  have p3 : exec D.N D.K c3 v2 rIa = encRM D.N D.K (p (.inl (i, row))) := by
    have h := exec_loadFamilyC p ps 9 rIa v2
      ((f2 _ (by decide)).trans ((f1 _ (by decide)).trans hp))
      ((f2 _ (by decide)).trans ((f1 _ (by decide)).trans hb))
      ((f2 _ (by decide)).trans ((f1 _ (by decide)).trans hz))
    simp only [ps, List.map_singleton, encL_singleton] at h
    exact h
  have hc : correctionLoadC D i row = .seq c1 (.seq c2 c3) := by
    simp only [correctionLoadC, c1, c2, c3, ts, zs, ps,
      List.map_map, List.map_singleton, Function.comp_def]
  dsimp only
  rw [hc]
  change exec D.N D.K c3 v2 rQa = _ ∧ exec D.N D.K c3 v2 rQb = _ ∧ _
  exact ⟨(f3 _ (by decide)).trans ((f2 _ (by decide)).trans t1),
    (f3 _ (by decide)).trans z2, p3⟩

theorem correctionLoadC_frame (D : Dims) (i : Fin (setting D).E.W) (row : Wb D)
    (r : Fin 64) (h : r ∉ [0, 1, 2, 3, 4, rQa, rQb, rIa]) :
    (correctionLoadC D i row).writes r = false := by
  have hf (src dst : Fin 64) (js : List ℕ) (hd : r ≠ dst) :
      (loadFamilyC D.N D.K src dst js).writes r = false := by
    apply loadFamilyC_frame <;> first | exact hd | intro he; exact h (by simp [he])
  simp only [correctionLoadC, Code.writes, Bool.or_eq_false_iff]
  exact ⟨hf _ _ _ (fun he ↦ h (by simp [he])),
    hf _ _ _ (fun he ↦ h (by simp [he])), hf _ _ _ (fun he ↦ h (by simp [he]))⟩

theorem exec_correctionInlC (D : Dims)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D)
    (i : Fin (setting D).E.W) (row : Wb D) (w : St)
    (ht : w 16 = (matE D (Wb D) (Fin D.K)).enc T)
    (hp : w 9 = encL D.N D.K (Enum.list.map p))
    (hzs : w 17 = encL D.N D.K (Enum.list.map z))
    (hb : w rB1 = [false]) (hz : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (correctionInlC D i row) w rIa = encRM D.N D.K
      ((p - realTrap (S := setting D) (J := Jh D) T z) (.inl (i, row))) := by
  let v := exec D.N D.K (correctionLoadC D i row) w
  obtain ⟨ha, hbb, hi⟩ := exec_correctionLoadC D T p z i row w ht hp hzs hb hz
  have bit : v rB1 = [false] := by
    rw [show v rB1 = w rB1 from exec_writes _ _ _
      (correctionLoadC_frame D i row rB1 (by decide)), hb]
  have zero : v rZ = encRM D.N D.K 0 := by
    rw [show v rZ = w rZ from exec_writes _ _ _
      (correctionLoadC_frame D i row rZ (by decide)), hz]
  rw [correctionInlC, exec_seq]
  change exec D.N D.K _ v rIa = _
  rw [exec_seq, exec_natC _ _ (by decide) _ v bit,
    exec_seq, exec_natC _ _ (by decide) _ _ (by simpa using bit)]
  exact (exec_autDotC_corrected_bounded D T p z i row _
    (by simpa using ha) (by simpa using hbb) (by simp) (by simp)
    (by simpa using hi) (by simpa using zero)).1

open Classical in
/-- The coordinates outside the trapdoor block are read without modification. -/
noncomputable def correctionCoordC (D : Dims) :
    PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Code
  | .inl (i, row) => correctionInlC D i row
  | .inr q => loadFamilyC D.N D.K 9 rIa
      [Enum.index (.inr q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)]

theorem wf_correctionCoordC (D : Dims)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) :
    (correctionCoordC D q).WFc := by
  rcases q with ⟨i, row⟩ | q
  · exact wf_correctionInlC _ _ _
  · exact wf_loadFamilyC _ _ _ _ _

theorem exec_correctionCoordC (D : Dims)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) (w : St)
    (ht : w 16 = (matE D (Wb D) (Fin D.K)).enc T)
    (hp : w 9 = encL D.N D.K (Enum.list.map p))
    (hzs : w 17 = encL D.N D.K (Enum.list.map z))
    (hb : w rB1 = [false]) (hz : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (correctionCoordC D q) w rIa =
      encRM D.N D.K ((p - realTrap (S := setting D) (J := Jh D) T z) q) := by
  classical
  rcases q with ⟨i, row⟩ | q
  · exact exec_correctionInlC D T p z i row w ht hp hzs hb hz
  · have h := exec_loadFamilyC p [.inr q] 9 rIa w hp hb hz
    simp only [List.map_singleton, encL_singleton] at h
    rw [corrected_inr]
    exact h

/-- Preserve all correction inputs and the accumulated output. -/
theorem correctionCoordC_frame (D : Dims)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) (r : Fin 64)
    (hr : r = 9 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = rB1 ∨ r = rZ) :
    (correctionCoordC D q).writes r = false := by
  have hn (n : ℕ) (dst : Fin 64) (hd : dst = rQc ∨ dst = rQk) :=
    natC_writes dst rB1 n r (by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hd with rfl | rfl <;> decide)
  rcases q with ⟨i, row⟩ | q
  · have hl := correctionLoadC_frame D i row r
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    simp only [correctionCoordC, correctionInlC, Code.writes, hl,
      hn _ _ (Or.inl rfl), hn _ _ (Or.inr rfl), autDotC, autQC, autQBody, ipC, ipBody]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · apply loadFamilyC_frame <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Append corrected coordinates in a prescribed enumeration order. -/
noncomputable def correctionAppendC (D : Dims) :
    List (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) → Code
  | [] => .nop
  | q :: qs => .seq (correctionCoordC D q) (.seq (.app 18 rIa) (correctionAppendC D qs))

noncomputable def correctionC (D : Dims) : Code :=
  .seq (.clr 18) (correctionAppendC D Enum.list)

theorem wf_correctionAppendC (D : Dims) : ∀ qs, (correctionAppendC D qs).WFc
  | [] => trivial
  | _q :: qs => ⟨wf_correctionCoordC _ _, trivial, wf_correctionAppendC D qs⟩

theorem wf_correctionC (D : Dims) : (correctionC D).WFc :=
  ⟨trivial, wf_correctionAppendC D _⟩

theorem exec_correctionAppendC (D : Dims)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D) :
    ∀ (qs : List (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)) (w : St)
    (out : List (Rg D)),
    w 16 = (matE D (Wb D) (Fin D.K)).enc T →
    w 9 = encL D.N D.K (Enum.list.map p) →
    w 17 = encL D.N D.K (Enum.list.map z) →
    w rB1 = [false] → w rZ = encRM D.N D.K 0 → w 18 = encL D.N D.K out →
    exec D.N D.K (correctionAppendC D qs) w 18 = encL D.N D.K
      (out ++ qs.map (p - realTrap (S := setting D) (J := Jh D) T z))
  | [], w, out, _, _, _, _, _, ho => by simpa [correctionAppendC] using ho
  | q :: qs, w, out, ht, hp, hzs, hb, hz, ho => by
    let x := p - realTrap (S := setting D) (J := Jh D) T z
    let v := exec D.N D.K (.app 18 rIa) (exec D.N D.K (correctionCoordC D q) w)
    have keep : ∀ r : Fin 64, (r = 9 ∨ r = 16 ∨ r = 17 ∨ r = rB1 ∨ r = rZ) → v r = w r := by
      intro r hr
      have hne : r ≠ 18 := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      change Function.update _ 18 _ r = _
      rw [Function.update_of_ne hne]
      apply exec_writes
      apply correctionCoordC_frame
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> tauto
    have hv : v 18 = encL D.N D.K (out ++ [x q]) := by
      change exec D.N D.K (correctionCoordC D q) w 18 ++
        exec D.N D.K (correctionCoordC D q) w rIa = _
      rw [exec_writes _ _ _ (correctionCoordC_frame D q 18 (by tauto)), ho,
        exec_correctionCoordC D T p z q w ht hp hzs hb hz, encL_append, encL_singleton]
    have ih := exec_correctionAppendC D T p z qs v (out ++ [x q])
      ((keep 16 (by tauto)).trans ht) ((keep 9 (by tauto)).trans hp)
      ((keep 17 (by tauto)).trans hzs) ((keep rB1 (by tauto)).trans hb)
      ((keep rZ (by tauto)).trans hz) hv
    change exec D.N D.K (correctionAppendC D qs) v 18 = _
    simpa only [List.map_cons, List.append_assoc, List.singleton_append] using ih

/-- All coordinates of the corrected proposal, in the short-key codec order. -/
theorem exec_correctionC (D : Dims)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D) (w : St)
    (ht : w 16 = (matE D (Wb D) (Fin D.K)).enc T)
    (hp : w 9 = encL D.N D.K (Enum.list.map p))
    (hzs : w 17 = encL D.N D.K (Enum.list.map z))
    (hb : w rB1 = [false]) (hz : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (correctionC D) w 18 = encL D.N D.K
      (Enum.list.map (p - realTrap (S := setting D) (J := Jh D) T z)) := by
  rw [correctionC, exec_seq]
  simpa using exec_correctionAppendC D T p z Enum.list (exec D.N D.K (.clr 18) w) []
    (by simpa using ht) (by simpa using hp) (by simpa using hzs)
    (by simpa using hb) (by simpa using hz) (by simp)

end AdvancedEncryption.ExpLUT.Prog
