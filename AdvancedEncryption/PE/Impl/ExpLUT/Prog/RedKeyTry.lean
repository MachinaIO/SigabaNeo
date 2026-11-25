import PE.Impl.ExpLUT.Prog.RedKeyMatVec
import PE.Impl.ExpLUT.Prog.RedKeyMath
import PE.Impl.ExpLUT.Prog.KeyTryLaw
/-!
# `KGsim` on the VM (package G2, item 5): one box try with the simulated trapdoor

The real KeyGen try (`Prog/KeyAccept.lean` `tryKeyC`) with the real-trapdoor correction
`correctionC` replaced by the correction of Lemma 11 (`RedKeyPLAN.md`, module 4):

  `x = p − X · u`, `u = gadDec (M_F (0, z) − (I_W ⊗ g) z)`, `X = simX …` (rows in register `16`).

F3's `keyDigitsC` (the digits `z` of `keyTarget − pubShort p`), `assembleC` and `acceptC` are reused
verbatim. The routine computing `u` into register `20` is a parameter `uC` with a contract
(`UOk`): it reads `mpk` (register `14`) and `z` (register `17`) and keeps the registers of the try.

* `simCorrectionC uC = uC ; |21| := |ZIdx| ; |22| := |PIdx| ; mvSubC`;
* **`exec_simProposalC`**: registers `17` = `z`, `18` = `p − X u`;
* **`exec_simTryKeyC`**: register `19` = the key of one try (zero key on rejection);
* `simAttemptOutput`, **`map_uniform_simAttemptOutput`**: one uniform candidate and the attempt is
  exactly `keyLaw … (simTrap M mpk F R̂)` mapped by `keyOfOutput`, for `X = simX M (h1Of mpk) A_F R̂`;
* **`map_coins_exec_simTryKeyC`** (fair coins, `kbOf D B hB r`) and **`map_coins_exec_simTryKeyC_Dc`**.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)
open Cslib.Probability Cslib.BitString

variable (D : Dims)

/-- The short coordinates of the key at `D` (as the setting indexes them). -/
abbrev PIdxS := PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W
/-- The gadget coordinates of the key at `D`. -/
abbrev ZIdxS := ZIdx (setting D).τ (setting D).E.W

/-- The vector `u = gadDec (M_F (0, z) − (I_W ⊗ g) z)` of the simulated correction. -/
noncomputable def uVec (mpk : MPKt D) (F : BP Pos) (z : ZIdxS D → Rg D) : ZIdxS D → Rg D :=
  gadDec (S := setting D) (pubZ (helperMap D) mpk F z - gadZ z)

/-- **The contract of the `u` routine**: well formed, keeps the registers of the try, and leaves
`u` in register `20` from `mpk` in `14` and `z` in `17`. -/
structure UOk (uC : Code) : Prop where
  wf : uC.WFc
  frame : ∀ r : Fin 64, (r = 9 ∨ r = 16 ∨ r = 17 ∨ r = rB1 ∨ r = rZ) → uC.writes r = false
  exec : ∀ (mpk : MPKt D) (F : BP Pos) (z : ZIdxS D → Rg D) (w : St),
    w 14 = (mpkEnc D).enc mpk → w 17 = encL D.N D.K (Enum.list.map z) → w rB1 = [false] →
    w rZ = encRM D.N D.K 0 → exec D.N D.K uC w rVu = encL D.N D.K (Enum.list.map (uVec D mpk F z))

/-- The simulated correction: `u`, the two templates, `18 := p − X u`. -/
noncomputable def simCorrectionC (uC : Code) : Code :=
  .seq uC <| .seq (natC rVm rB1 (Enum.list (α := ZIdxS D)).length) <|
  .seq (natC rVn rB1 (Enum.list (α := PIdxS D)).length) mvSubC

/-- The proposal: the digits `z` (as F3), then the simulated correction. -/
noncomputable def simProposalC (uC : Code) : Code :=
  .seq (keyDigitsC D) (.seq (.cp 17 rDq) (simCorrectionC D uC))

/-- The proposal and the assembled key in register `19`. -/
noncomputable def simProposalKeyC (uC : Code) : Code := .seq (simProposalC D uC) (assembleC D)

/-- **One box try with the simulated trapdoor** (no retry). -/
noncomputable def simTryKeyC (uC : Code) (B r : ℕ) : Code :=
  .seq (simProposalKeyC D uC) (acceptC D B r)

variable {D}

theorem wf_simCorrectionC {uC : Code} (hu : UOk D uC) : (simCorrectionC D uC).WFc :=
  ⟨hu.wf, natC_wfc _ _ _, natC_wfc _ _ _, wf_mvSubC⟩

theorem wf_simProposalC {uC : Code} (hu : UOk D uC) : (simProposalC D uC).WFc :=
  ⟨wf_keyDigitsC _, trivial, wf_simCorrectionC hu⟩

theorem wf_simTryKeyC {uC : Code} (hu : UOk D uC) (B r : ℕ) : (simTryKeyC D uC B r).WFc :=
  ⟨⟨wf_simProposalC hu, wf_assembleC _⟩, wf_acceptC _ _ _⟩

/-- `keyDigitsC` keeps the public key. -/
theorem keyDigitsC_keeps_mpk : (keyDigitsC D).writes 14 = false := by
  have hp : (publicRowsC D).writes 14 = false := publicRowsC_frame D 14 (by tauto)
  have ht := targetC_frame D 14 (by decide) (by decide) (by decide) (by decide)
  have hc := natC_writes rQc rB1 (setting D).E.W 14 (by decide)
  have hk := natC_writes rQk rB1 D.K 14 (by decide)
  simp only [keyDigitsC, Code.writes, hp, ht, hc, hk, decRowsC, decRowBodyC,
    decRowLoadC, decomposeC, digQC, digQBody]
  decide

theorem simCorrectionC_frame {uC : Code} (hu : UOk D uC) (r : Fin 64)
    (hr : r = 16 ∨ r = 17 ∨ r = rB1 ∨ r = rZ) : (simCorrectionC D uC).writes r = false := by
  have h1 := hu.frame r (by tauto)
  have h2 := natC_writes rVm rB1 (Enum.list (α := ZIdxS D)).length r
    (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
  have h3 := natC_writes rVn rB1 (Enum.list (α := PIdxS D)).length r
    (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
  have h4 : mvSubC.writes r = false := by
    cases h : mvSubC.writes r
    · rfl
    · have := mvSubC_frame r h
      rcases hr with rfl | rfl | rfl | rfl <;> simp at this
  simp only [simCorrectionC, Code.writes, h1, h2, h3, h4, Bool.or_self]

theorem simProposalC_templates {uC : Code} (hu : UOk D uC) (r : Fin 64) (hr : r = rB1 ∨ r = rZ) :
    (simProposalC D uC).writes r = false := by
  have hd := keyDigitsC_frame D r (by rcases hr with rfl | rfl <;> tauto)
  have hc := simCorrectionC_frame hu r (by rcases hr with rfl | rfl <;> tauto)
  simp only [simProposalC, Code.writes, hd, hc, Bool.or_false]
  rcases hr with rfl | rfl <;> decide

theorem simProposalKeyC_templates {uC : Code} (hu : UOk D uC) (r : Fin 64)
    (hr : r = rB1 ∨ r = rZ) : (simProposalKeyC D uC).writes r = false := by
  have hp := simProposalC_templates hu r hr
  have ha := assembleC_frame D r (by rcases hr with rfl | rfl <;> decide)
  simp [simProposalKeyC, Code.writes, hp, ha]

/-- **The simulated proposal**: register `17` holds the digits `z` of `keyTarget − pubShort p`,
register `18` the corrected short part `p − X u`. -/
theorem exec_simProposalC (hK : 2 ≤ D.K) {uC : Code} (hu : UOk D uC) (mpk : MPKt D) (F : BP Pos)
    (X : PIdxS D → ZIdxS D → Rg D) (p : PIdxS D → Rg D) (w : St)
    (hM : w 14 = (mpkEnc D).enc mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (hX : w 16 = encL D.N D.K (rowsWord X))
    (hP : w 9 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    let z := gadDec (S := setting D) (keyTarget mpk - pubShort (helperMap D) mpk F p)
    exec D.N D.K (simProposalC D uC) w 17 = encL D.N D.K (Enum.list.map z) ∧
    exec D.N D.K (simProposalC D uC) w 18 = encL D.N D.K
      (Enum.list.map (p - Matrix.mulVec (Matrix.of X) (uVec D mpk F z))) := by
  intro z
  let v := exec D.N D.K (keyDigitsC D) w
  have hv : v rDq = encL D.N D.K (Enum.list.map z) :=
    exec_keyDigitsC D hK mpk F p w hM hA hP h1 hZ
  have keep : ∀ r : Fin 64, (r = 9 ∨ r = 16 ∨ r = rB1 ∨ r = rZ) → v r = w r :=
    fun r hr ↦ exec_writes _ _ _ (keyDigitsC_frame D r hr)
  have v14 : v 14 = w 14 := exec_writes _ _ _ keyDigitsC_keeps_mpk
  let u := exec D.N D.K (.cp 17 rDq) v
  have uf : ∀ r : Fin 64, r ≠ 17 → u r = v r := fun r hr ↦ Function.update_of_ne hr _ _
  have u17 : u 17 = encL D.N D.K (Enum.list.map z) := by
    change Function.update v 17 (v rDq) 17 = _
    rw [Function.update_self, hv]
  have u9 := (uf 9 (by decide)).trans ((keep 9 (by tauto)).trans hP)
  have u16 := (uf 16 (by decide)).trans ((keep 16 (by tauto)).trans hX)
  have u14 := (uf 14 (by decide)).trans (v14.trans hM)
  have uB := (uf rB1 (by decide)).trans ((keep rB1 (by tauto)).trans h1)
  have uZ := (uf rZ (by decide)).trans ((keep rZ (by tauto)).trans hZ)
  let a := exec D.N D.K uC u
  have akeep : ∀ r : Fin 64, (r = 9 ∨ r = 16 ∨ r = 17 ∨ r = rB1 ∨ r = rZ) → a r = u r :=
    fun r hr ↦ exec_writes _ _ _ (hu.frame r hr)
  have aU : a rVu = encL D.N D.K (Enum.list.map (uVec D mpk F z)) :=
    hu.exec mpk F z u u14 u17 uB uZ
  let b := exec D.N D.K (natC rVn rB1 (Enum.list (α := PIdxS D)).length)
    (exec D.N D.K (natC rVm rB1 (Enum.list (α := ZIdxS D)).length) a)
  have aB : a rB1 = [false] := (akeep rB1 (by tauto)).trans uB
  have hb1 : exec D.N D.K (natC rVm rB1 (Enum.list (α := ZIdxS D)).length) a =
      Function.update a rVm (List.replicate (Enum.list (α := ZIdxS D)).length false) :=
    exec_natC _ _ (by decide) _ a aB
  have hb : b = Function.update (Function.update a rVm
      (List.replicate (Enum.list (α := ZIdxS D)).length false)) rVn
      (List.replicate (Enum.list (α := PIdxS D)).length false) := by
    change exec D.N D.K (natC rVn rB1 _) _ = _
    rw [hb1]
    exact exec_natC _ _ (by decide) _ _ (by
      rw [Function.update_of_ne (by decide)]; exact aB)
  have bf : ∀ r : Fin 64, r ≠ rVm → r ≠ rVn → b r = a r := by
    intro r h1 h2; rw [hb, Function.update_of_ne h2, Function.update_of_ne h1]
  have bM : b rVm = List.replicate (Enum.list (α := ZIdxS D)).length false := by
    rw [hb, Function.update_of_ne (by decide), Function.update_self]
  have bN : b rVn = List.replicate (Enum.list (α := PIdxS D)).length false := by
    rw [hb, Function.update_self]
  have hout := exec_mvSubC_enum D.K_pos b p X (uVec D mpk F z)
    ((bf 9 (by decide) (by decide)).trans ((akeep 9 (by tauto)).trans u9))
    ((bf 16 (by decide) (by decide)).trans ((akeep 16 (by tauto)).trans u16))
    ((bf rVu (by decide) (by decide)).trans aU) bM bN
    ((bf rZ (by decide) (by decide)).trans ((akeep rZ (by tauto)).trans uZ))
  have e17 : exec D.N D.K mvSubC b 17 = encL D.N D.K (Enum.list.map z) := by
    have h : mvSubC.writes 17 = false := by
      cases h : mvSubC.writes 17
      · rfl
      · have := mvSubC_frame 17 h; simp at this
    rw [exec_writes _ _ _ h, bf 17 (by decide) (by decide), akeep 17 (by tauto), u17]
  change exec D.N D.K mvSubC b 17 = _ ∧ exec D.N D.K mvSubC b 18 = _
  refine ⟨e17, hout.trans ?_⟩
  rfl

/-- **The simulated proposal and its assembled key.** -/
theorem exec_simProposalKeyC (hK : 2 ≤ D.K) {uC : Code} (hu : UOk D uC) (mpk : MPKt D)
    (F : BP Pos) (X : PIdxS D → ZIdxS D → Rg D) (p : PIdxS D → Rg D) (w : St)
    (hM : w 14 = (mpkEnc D).enc mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (hX : w 16 = encL D.N D.K (rowsWord X))
    (hP : w 9 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    let z := gadDec (S := setting D) (keyTarget mpk - pubShort (helperMap D) mpk F p)
    exec D.N D.K (simProposalKeyC D uC) w 19 = (keyEnc D).enc (assemble (S := setting D)
      (p - Matrix.mulVec (Matrix.of X) (uVec D mpk F z)) z) ∧
    exec D.N D.K (simProposalKeyC D uC) w 18 = encL D.N D.K
      (Enum.list.map (p - Matrix.mulVec (Matrix.of X) (uVec D mpk F z))) := by
  obtain ⟨hzs, hx⟩ := exec_simProposalC hK hu mpk F X p w hM hA hX hP h1 hZ
  rw [simProposalKeyC, exec_seq]
  exact ⟨exec_assembleC D _ _ _ hx hzs
    ((exec_writes _ _ _ (simProposalC_templates hu rB1 (Or.inl rfl))).trans h1)
    ((exec_writes _ _ _ (simProposalC_templates hu rZ (Or.inr rfl))).trans hZ),
    (exec_writes _ _ _ (assembleC_frame D 18 (by decide))).trans hx⟩

open Classical in
/-- **One box try with the simulated trapdoor**: register `19` holds the key of the try (the
zero key on rejection). -/
theorem exec_simTryKeyC (hK : 2 ≤ D.K) {uC : Code} (hu : UOk D uC) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (mpk : MPKt D) (F : BP Pos)
    (X : PIdxS D → ZIdxS D → Rg D) (p : PIdxS D → Rg D) (w : St)
    (hM : w 14 = (mpkEnc D).enc mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (hX : w 16 = encL D.N D.K (rowsWord X))
    (hP : w 9 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    let z := gadDec (S := setting D) (keyTarget mpk - pubShort (helperMap D) mpk F p)
    let x := p - Matrix.mulVec (Matrix.of X) (uVec D mpk F z)
    exec D.N D.K (simTryKeyC D uC B r) w 19 = (keyEnc D).enc
      (if x ∈ (kbOf D B hB r).Small then assemble (S := setting D) x z else 0) := by
  intro z x
  let v := exec D.N D.K (simProposalKeyC D uC) w
  obtain ⟨hk, hx⟩ := exec_simProposalKeyC hK hu mpk F X p w hM hA hX hP h1 hZ
  have vb : v rB1 = [false] :=
    (exec_writes _ _ _ (simProposalKeyC_templates hu rB1 (Or.inl rfl))).trans h1
  have vz : v rZ = encRM D.N D.K 0 :=
    (exec_writes _ _ _ (simProposalKeyC_templates hu rZ (Or.inr rfl))).trans hZ
  let k : Keyt D := assemble (S := setting D) x z
  let x' : PIdxD D → Rg D := x
  have h := exec_acceptC D B r hB hBK hr hq hcount v x' k hx hk vb vz
  change exec D.N D.K (acceptC D B r) v 19 = _
  by_cases hm : x' ∈ (kbOf D B hB r).Small
  · rw [ite_eq_left hm] at h
    have hm' : x ∈ (kbOf D B hB r).Small := hm
    simp only [hm', ↓reduceIte]
    exact h
  · rw [ite_eq_right hm] at h
    have hm' : x ∉ (kbOf D B hB r).Small := hm
    simp only [hm', ↓reduceIte]
    exact h

/-! ### The law of one try -/

variable (D)

open Classical in
/-- The output of the try for a fixed candidate, with the zero key on rejection. -/
noncomputable def simAttemptOutput (kb : KeyBoxes D) (mpk : MPKt D) (F : BP Pos)
    (X : PIdxS D → ZIdxS D → Rg D) (p : PIdxS D → Rg D) : Keyt D :=
  let z := gadDec (S := setting D) (keyTarget mpk - pubShort (helperMap D) mpk F p)
  let x := p - Matrix.mulVec (Matrix.of X) (uVec D mpk F z)
  keyOfOutput (S := setting D) (if x ∈ kb.Small then some (x, z) else none)

/-- **One uniform candidate and the try is the key law of `T_sim`**, for `X = simX M (h1Of mpk) A_F R̂`. -/
theorem map_uniform_simAttemptOutput (kb : KeyBoxes D) (mpk : MPKt D) (F : BP Pos)
    (Rh : SimMat (Wb D) (Jh D) (setting D)) :
    (PMF.uniformOfFinset kb.Big kb.hBig).map (simAttemptOutput D kb mpk F
      (fun q ic => simX (helperMap D) (h1Of mpk) (keyPK (helperMap D) mpk F) Rh q ic)) =
      (keyLaw (S := setting D) kb.Big kb.Small kb.hBig gadDec (helperMap D) mpk F
        (simTrap (helperMap D) mpk F Rh)).map keyOfOutput := by
  classical
  simp only [keyLaw, boxSample, PMF.map_comp]
  congr 1

variable {D}

/-- The register contract of the try (as F3's `TryReady`, with the rows of `X` in `16`). -/
structure SimTryReady (mpk : MPKt D) (F : BP Pos) (X : PIdxS D → ZIdxS D → Rg D)
    (p : PIdxS D → Rg D) (w : St) : Prop where
  publicKey : w 14 = (mpkEnc D).enc mpk
  evaluated : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F))
  rows : w 16 = encL D.N D.K (rowsWord X)
  candidate : w 9 = encL D.N D.K (Enum.list.map p)
  bit : w rB1 = [false]
  zero : w rZ = encRM D.N D.K 0

/-- Exact output-word semantics of the try, in the notation of `simAttemptOutput`. -/
theorem exec_simTryKeyC_output (hK : 2 ≤ D.K) {uC : Code} (hu : UOk D uC) (B r : ℕ)
    (hB : 2 ^ B ≤ D.q) (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (mpk : MPKt D) (F : BP Pos) (X : PIdxS D → ZIdxS D → Rg D)
    (p : PIdxS D → Rg D) (w : St) (hw : SimTryReady mpk F X p w) :
    exec D.N D.K (simTryKeyC D uC B r) w 19 =
      (keyEnc D).enc (simAttemptOutput D (kbOf D B hB r) mpk F X p) := by
  classical
  have h := exec_simTryKeyC hK hu B r hB hBK hr hq hcount mpk F X p w hw.publicKey hw.evaluated
    hw.rows hw.candidate hw.bit hw.zero
  convert h using 1
  congr 1
  unfold simAttemptOutput
  dsimp only
  split_ifs <;> simp_all only [keyOfOutput]

/-- **Fair coins, the decoder and the try give the key law of `T_sim`** (encoded), for ready
states whose register `16` holds the rows of `X = simX M (h1Of mpk) A_F R̂`. -/
theorem map_coins_exec_simTryKeyC (hK : 2 ≤ D.K) {uC : Code} (hu : UOk D uC) (B r : ℕ)
    (hB : 2 ^ B ≤ D.q) (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (mpk : MPKt D) (F : BP Pos)
    (Rh : SimMat (Wb D) (Jh D) (setting D)) (states : (PIdxS D → Rg D) → St)
    (ready : ∀ p, SimTryReady mpk F
      (fun q ic => simX (helperMap D) (h1Of mpk) (keyPK (helperMap D) mpk F) Rh q ic) p (states p)) :
    (uniformList (nPI D * D.N * B)).map
      (fun cs ↦ exec D.N D.K (simTryKeyC D uC B r) (states (coinDec D B cs)) 19) =
    ((keyLaw (S := setting D) (kbOf D B hB r).Big (kbOf D B hB r).Small (kbOf D B hB r).hBig
      gadDec (helperMap D) mpk F (simTrap (helperMap D) mpk F Rh)).map keyOfOutput).map
      (keyEnc D).enc := by
  rw [← map_uniform_simAttemptOutput, PMF.map_comp, ← map_uniformList_coinDec_kbOf D B hB r,
    PMF.map_comp]
  congr 1
  funext cs
  exact exec_simTryKeyC_output hK hu B r hB hBK hr hq hcount mpk F _ _ _ (ready _)

open Params

/-- **The try at the concrete parameters** (box `kbDc`), all box-test conditions discharged. -/
theorem map_coins_exec_simTryKeyC_Dc {uC : Code} (hu : UOk Dc uC) (mpk : MPKt Dc) (F : BP Pos)
    (Rh : SimMat (Wb Dc) (Jh Dc) (setting Dc)) (states : (PIdxS Dc → Rg Dc) → St)
    (ready : ∀ p, SimTryReady mpk F
      (fun q ic => simX (helperMap Dc) (h1Of mpk) (keyPK (helperMap Dc) mpk F) Rh q ic) p
        (states p)) :
    (uniformList (nPI Dc * Dc.N * Bk)).map
      (fun cs ↦ exec Dc.N Dc.K (simTryKeyC Dc uC Bk rSmall) (states (coinDec Dc Bk cs)) 19) =
    ((keyLaw (S := setting Dc) kbDc.Big kbDc.Small kbDc.hBig gadDec (helperMap Dc) mpk F
      (simTrap (helperMap Dc) mpk F Rh)).map keyOfOutput).map (keyEnc Dc).enc := by
  have hk : 2 ≤ Dc.K := by change 2 ≤ Kc; rw [Kc_def]; norm_num
  have h := map_coins_exec_simTryKeyC hk hu Bk rSmall hBk_Dc Bk_lt_Kc.le
    small_test_conditions_Dc.1 small_test_conditions_Dc.2.1 small_test_conditions_Dc.2.2
    mpk F Rh states ready
  rw [← kbDc_def] at h
  exact h

end AdvancedEncryption.ExpLUT.Prog
