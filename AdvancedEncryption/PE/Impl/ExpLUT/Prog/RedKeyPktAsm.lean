import PE.Impl.ExpLUT.Prog.RedKeyPktPubD

/-!
# The packet stream, part 14: the assembled code `pktC D`

`pktC D = pkMoveC ; templates(walk) ; pkWalkC ; templates(public) ; pbPubC ; templates(loops) ;
pkFinC`:

* `pkMoveC`: `rawEnc` out of `rAinS` into `pkRaw = 30`; `5 := [true]`, `rB1 := [false]`;
* the walk's constants (`pkSwOps`), `pkWalkC`: `swOne := [true] ++ 0^{NK−1}`, `swA := rawEnc`
  (the attribute is its head), `swCcur := C`, `swLoopC`;
* the public phase's constants (`pkPbOps`: widths, `g`, the field offsets), `pbPubC`;
* the loops' constants (`pkLpOps`), `pkFinC`: `ptOne := encRM 1`, `ptZR :=` the `zr` field of
  `rawEnc`, `ptInlLoopC`, `ptZS := 0^{2b}`, `ptBT := [true]`, `ptInrLoopC`, then every scratch
  register is cleared (`pkClrC`).

All constants are built by `templateOpsC` (unary words by doubling) in registers outside
`pktKeepR`; every other phase is `natC`-free, so its footprint is checked by `decide`
(**`pktC_keeps`**). **`wf_pktC`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid

variable (D : Dims)

/-! ### Offsets of the fields -/

/-- The `H` field of the public-key word. -/
noncomputable def pbOffHv : ℕ := codecSize (matE D (Fin 2) (BCol (Wb D) D.K))
/-- The `a` field. -/
noncomputable def pbOffav : ℕ :=
  pbOffHv D + codecSize (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K)))
/-- The `A₀` field. -/
noncomputable def pbOffA0v : ℕ := pbOffav D + codecSize (FixedEnc.fun (α := Pos) (vecE D (Col D.K)))
/-- The `A^in` field. -/
noncomputable def pbOffAinv : ℕ := pbOffA0v D + codecSize (matE D (Fin 2) (Col D.K))
/-- The `A^aut` field. -/
noncomputable def pbOffAav : ℕ := pbOffAinv D +
  codecSize (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))))
/-- The `h` field of the ciphertext word. -/
noncomputable def pbOffhv : ℕ := codecSize (vecE D (BCol (Wb D) D.K))
/-- The `cinBot` field. -/
noncomputable def pbOffcbv : ℕ := pbOffhv D + codecSize (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))) +
  codecSize (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))))
/-- The `zr` field of the raw secret word. -/
noncomputable def pbOffzr : ℕ := codecSize attrEnc + codecSize (instEnc D) +
  codecSize (vecE D (BCol (Wb D) D.K)) + codecSize (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))) +
  codecSize (rEnc D) + codecSize (floodEnc D)

theorem drop_pre {α : Type*} (A X : List α) (n : ℕ) (h : A.length = n) : (A ++ X).drop n = X := by
  rw [← h, List.drop_left]

variable (mpk : MPKt D) (ct : CTt D)

theorem pkDrop_H : ((mpkEnc D).enc mpk).drop (pbOffHv D) =
    (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H ++
      ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a ++
      ((matE D (Fin 2) (Col D.K)).enc mpk.A0 ++
      ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Ain ++
      ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
        (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut ++ (vecE D (Fin 2)).enc mpk.d)))) :=
  drop_pre _ _ _ ((matE D (Fin 2) (BCol (Wb D) D.K)).length _)

theorem pkDrop_a : ((mpkEnc D).enc mpk).drop (pbOffav D) =
      (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a ++
      ((matE D (Fin 2) (Col D.K)).enc mpk.A0 ++
      ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Ain ++
      ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
        (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut ++ (vecE D (Fin 2)).enc mpk.d))) := by
  rw [pbOffav, ← List.drop_drop, pkDrop_H]
  exact drop_pre _ _ _ ((FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).length _)

theorem pkDrop_A0 : ((mpkEnc D).enc mpk).drop (pbOffA0v D) =
      (matE D (Fin 2) (Col D.K)).enc mpk.A0 ++
      ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Ain ++
      ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
        (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut ++ (vecE D (Fin 2)).enc mpk.d)) := by
  rw [pbOffA0v, ← List.drop_drop, pkDrop_a]
  exact drop_pre _ _ _ ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).length _)

theorem pkDrop_Ain : ((mpkEnc D).enc mpk).drop (pbOffAinv D) =
      (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Ain ++
      ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
        (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut ++ (vecE D (Fin 2)).enc mpk.d) := by
  rw [pbOffAinv, ← List.drop_drop, pkDrop_A0]
  exact drop_pre _ _ _ ((matE D (Fin 2) (Col D.K)).length _)

theorem pkDrop_Aa : ((mpkEnc D).enc mpk).drop (pbOffAav D) =
      (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
        (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut ++ (vecE D (Fin 2)).enc mpk.d := by
  rw [pbOffAav, ← List.drop_drop, pkDrop_Ain]
  exact drop_pre _ _ _
    ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).length _)

theorem pkDrop_h : ((ctEnc D).enc ct).drop (pbOffhv D) =
    (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc ct.h ++
      ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.caut ++
      ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot ++
      ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.cin ++
      ((vecE D (Col D.K)).enc ct.c0 ++ (rEnc D).enc ct.cm)))) :=
  drop_pre _ _ _ ((vecE D (BCol (Wb D) D.K)).length _)

theorem pkDrop_cb : ((ctEnc D).enc ct).drop (pbOffcbv D) =
      (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot ++
      ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.cin ++
      ((vecE D (Col D.K)).enc ct.c0 ++ (rEnc D).enc ct.cm)) := by
  rw [pbOffcbv, ← List.drop_drop, ← List.drop_drop, pkDrop_h]
  exact (congrArg (List.drop _) (drop_pre _ _ _
    ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).length ct.h))).trans (drop_pre _ _ _
    ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).length ct.caut))

theorem pkDrop_zr (σ : RawSec D) :
    ((rawEnc D).enc σ).drop (pbOffzr D) = (zrEnc D).enc σ.2.2.2.2.2.2 := by
  rw [pbOffzr, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop,
    ← List.drop_drop]
  show ((((((attrEnc.enc σ.1 ++ ((instEnc D).enc σ.2.1 ++ ((vecE D (BCol (Wb D) D.K)).enc σ.2.2.1 ++
    ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc σ.2.2.2.1 ++ ((rEnc D).enc σ.2.2.2.2.1 ++
    ((floodEnc D).enc σ.2.2.2.2.2.1 ++ (zrEnc D).enc σ.2.2.2.2.2.2)))))).drop _).drop _).drop _).drop
      _).drop _).drop _ = _
  rw [drop_pre _ _ (codecSize attrEnc) (attrEnc.length _),
    drop_pre _ _ (codecSize (instEnc D)) ((instEnc D).length _),
    drop_pre _ _ (codecSize (vecE D (BCol (Wb D) D.K))) ((vecE D (BCol (Wb D) D.K)).length _),
    drop_pre _ _ (codecSize (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))))
      ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).length _),
    drop_pre _ _ (codecSize (rEnc D)) ((rEnc D).length _)]
  exact drop_pre _ _ _ ((floodEnc D).length _)

/-! ### The code -/

/-- `NK − 1` zeros (walk set-up). -/
@[simp, vmreg] abbrev pkT1 : Fin 64 := 17
/-- The raw secret word. -/
@[simp, vmreg] abbrev pkRaw : Fin 64 := 30
/-- The offset of the `zr` field. -/
@[simp, vmreg] abbrev pkZoff : Fin 64 := 56

/-- `rawEnc` out of `rAinS`; `5 := [true]`, `rB1 := [false]`. -/
def pkMoveC : Code := .seq (.cp pkRaw 0) <| .seq (.clr 0) <| .seq (.clr 6) (bitsC 5 rB1 6)

/-- The constants of the walk. -/
noncomputable def pkSwOps : List (Fin 64 × TemplateWord) :=
  [(swT8, .zeros 8), (swT14, .zeros (2 ^ 14)), (swT2N, .zeros (2 * D.N)), (swOne, .bits [true]),
   (pkT1, .zeros (D.N * D.K - 1)), (swT14b, .zeros 14), (swTtab, .zeros tlK), (swB1, .bits [false]),
   (swT16, .zeros 16)]

/-- **The walk**: `swOne := [true] ++ 0^{NK−1}`, the attribute stream, the tables, `swLoopC`. -/
def pkWalkC : Code := .seq (.app swOne pkT1) <| .seq (.cp swA pkRaw) <| .seq (.cp swCcur 4) swLoopC

/-- The constants of the public phase. -/
noncomputable def pkPbOps : List (Fin 64 × TemplateWord) :=
  [(ptTB, .zeros D.b), (ptT16, .zeros 16), (ptTM, .zeros (4 * D.K * (D.N * D.K))),
   (ptTAa, .zeros (16 * D.K ^ 3 * (D.N * D.K))), (pbTN, .zeros (D.N * D.K)),
   (pbTV, .zeros (2 * D.K * (D.N * D.K))), (pbTC, .zeros (2 * D.K)), (pbKg, .zeros (gD D)),
   (pbOH, .zeros (pbOffHv D)), (pbOh, .zeros (pbOffhv D)), (pbOAa, .zeros (pbOffAav D)),
   (pbOAin, .zeros (pbOffAinv D)), (pbOa, .zeros (pbOffav D)), (pbOcb, .zeros (pbOffcbv D)),
   (pbOA0, .zeros (pbOffA0v D))]

/-- The number of rows of `Z`, `R₀`, `R^in`. -/
noncomputable abbrev pkNZ : ℕ := (Enum.list (α := Pos × Col (setting D).τ)).length
noncomputable abbrev pkNR0 : ℕ := (Enum.list (α := Col (setting D).τ)).length
noncomputable abbrev pkNRin : ℕ := (Enum.list (α := Pos × Dig (setting D).τ × Col (setting D).τ)).length

/-- The constants of the slab loops. -/
noncomputable def pkLpOps : List (Fin 64 × TemplateWord) :=
  [(ptTSP, .zeros ((16 * D.K ^ 3 + 4 * D.K + 1) * (D.N * D.K))), (ptTm, .zeros D.mb),
   (ptTC, .zeros (2 * D.K)), (ptTD, .zeros (ptND D)), (ptOne, .bits [true]),
   (4, .zeros (D.N * D.K - 1)), (ptZero, .zeros (D.N * D.K)),
   (ptZ2, .zeros (2 * D.K * (D.N * D.K))), (ptZL, .zeros ((2 ^ D.b - 1) * (2 * D.K) * (D.N * D.K))),
   (ptTZb, .zeros (pkNZ D * D.mb)), (ptTR0b, .zeros (pkNR0 D * D.mb)),
   (ptTRinb, .zeros (pkNRin D * D.mb)), (ptB1, .bits [false]), (pkZoff, .zeros (pbOffzr D)),
   (1, .zeros (2 * D.b)), (2, .bits [true])]

/-- Clear a list of registers. -/
def pkClrL : List (Fin 64) → Code
  | [] => .nop
  | r :: rs => .seq (.clr r) (pkClrL rs)

/-- The scratch registers of `pktC` (all but `rAinS` and `pktKeepR`). -/
def pkScratch : List (Fin 64) :=
  [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56]

/-- **The end**: `ptOne`, the `zr` rows, both slab loops, then every scratch register cleared. -/
def pkFinC : Code :=
  .seq (.app ptOne 4) <| .seq (.cp ptZR pkRaw) <| .seq (.drop ptZR pkZoff) <| .seq ptInlLoopC <|
  .seq (.cp ptZS 1) <| .seq (.cp ptBT 2) <| .seq ptInrLoopC (pkClrL pkScratch)

/-- **The packet-stream code.** -/
noncomputable def pktC : Code :=
  .seq pkMoveC <| .seq (templateOpsC (pkSwOps D)) <| .seq pkWalkC <|
  .seq (templateOpsC (pkPbOps D)) <| .seq pbPubC <| .seq (templateOpsC (pkLpOps D)) pkFinC

/-! ### Footprint and well-formedness -/

theorem pkSw_targets : ∀ op ∈ pkSwOps D, pktKeepR op.1 = false ∧ op.1 ≠ 5 ∧ op.1 ≠ rB1 ∧
    op.1 ≠ rAinS := by
  intro op h
  simp only [pkSwOps, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

theorem pkPb_targets : ∀ op ∈ pkPbOps D, pktKeepR op.1 = false ∧ op.1 ≠ 5 ∧ op.1 ≠ rB1 ∧
    op.1 ≠ rAinS := by
  intro op h
  simp only [pkPbOps, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> (dsimp only; decide)

theorem pkLp_targets : ∀ op ∈ pkLpOps D, pktKeepR op.1 = false ∧ op.1 ≠ 5 ∧ op.1 ≠ rB1 ∧
    op.1 ≠ rAinS := by
  intro op h
  simp only [pkLpOps, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> (dsimp only; decide)

theorem templateOpsC_keeps (ops : List (Fin 64 × TemplateWord))
    (h : ∀ op ∈ ops, pktKeepR op.1 = false ∧ op.1 ≠ 5 ∧ op.1 ≠ rB1 ∧ op.1 ≠ rAinS) (r : Fin 64)
    (hr : pktKeepR r = true) : (templateOpsC ops).writes r = false :=
  templateOpsC_frame r ops fun op hop e => by
    have := (h op hop).1; rw [← e, hr] at this; cases this

theorem pkFixed_keeps : ∀ r : Fin 64, pktKeepR r = true →
    (pkMoveC.writes r || pkWalkC.writes r || pbPubC.writes r || pkFinC.writes r) = false := by
  decide

/-- **`pktC` never writes the constants, `rCs`, the slab counter.** -/
theorem pktC_keeps (r : Fin 64) (hr : pktKeepR r = true) : (pktC D).writes r = false := by
  have h := pkFixed_keeps r hr
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [pktC, Code.writes, h1, h2, h3, h4, templateOpsC_keeps _ (pkSw_targets D) r hr,
    templateOpsC_keeps _ (pkPb_targets D) r hr, templateOpsC_keeps _ (pkLp_targets D) r hr,
    Bool.or_self]

/-- A decidable check of `Code.WFc`. -/
def pkWfB : Code → Bool
  | .rep c body => !(body.writes c) && pkWfB body
  | .seq p q => pkWfB p && pkWfB q
  | .ifb _ p q => pkWfB p && pkWfB q
  | _ => true

theorem pkWfB_wfc : ∀ c : Code, pkWfB c = true → c.WFc
  | .rep c body, h => by
    simp only [pkWfB, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨h.1, pkWfB_wfc body h.2⟩
  | .seq p q, h => by
    simp only [pkWfB, Bool.and_eq_true] at h
    exact ⟨pkWfB_wfc p h.1, pkWfB_wfc q h.2⟩
  | .ifb _ p q, h => by
    simp only [pkWfB, Bool.and_eq_true] at h
    exact ⟨pkWfB_wfc p h.1, pkWfB_wfc q h.2⟩
  | .op .., _ => trivial
  | .mv .., _ => trivial
  | .mvR .., _ => trivial
  | .cp .., _ => trivial
  | .drop .., _ => trivial
  | .clr .., _ => trivial
  | .tl .., _ => trivial
  | .app .., _ => trivial
  | .eqb .., _ => trivial
  | .nop, _ => trivial

theorem pkFixed_wfB : (pkWfB pkMoveC && pkWfB pkWalkC && pkWfB pbPubC && pkWfB pkFinC) = true := by
  decide

/-- **`pktC` is well formed.** -/
theorem wf_pktC : (pktC D).WFc := by
  have h := pkFixed_wfB
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨pkWfB_wfc _ h1, wf_templateOpsC _, pkWfB_wfc _ h2, wf_templateOpsC _, pkWfB_wfc _ h3,
    wf_templateOpsC _, pkWfB_wfc _ h4⟩

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
