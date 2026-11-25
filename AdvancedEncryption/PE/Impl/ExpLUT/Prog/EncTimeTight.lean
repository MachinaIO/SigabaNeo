import PE.Impl.ExpLUT.Prog.EncTightCore

/-!
# The tight clock of the concrete encryption machine (tight encryption clock, part 5)

The loader's per-tape bound (`initB_spec`) is below the core box `Bstar` (the inputs of the four
certified phases, `opOK_encInit`), so the certified core applies (`core_tight`), and the
production suffix (relocation, normalization, loader, core, erasure) costs at most `2^244`
steps (`suffix_tight`); the parser, sampler and emitter are added in `EncTightFront`.
-/

namespace AdvancedEncryption.ExpLUT.Prog.EncTight

set_option maxRecDepth 100000

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.Sym
  SigabaNeo.Tape.Prog.SpecT
open AdvancedEncryption.ExpLUT.Params AdvancedEncryption.ExpLUT.Prog
  AdvancedEncryption.ExpLUT.Prog.EncW

/-- The bound of each core tape the loader must establish: the four phases' inputs. -/
def Bstar (i : Fin 321) : ℕ :=
  if i.val = 0 then 2 ^ 99
  else if i.val ≤ 65 then pEval ρE (aGet σME i.val)
  else if i.val ≤ 133 then pEval ρE (aGet σHE (i.val - 65))
  else if i.val ≤ 217 then pEval ρE (aGet σAE (i.val - 133))
  else pEval ρE (aGet σTE (i.val - 217))

theorem Bstar_b : ∀ j : Fin 66, Bstar (bSlot j) ≤ bnd ρE σME j := by decide +kernel
theorem Bstar_h : ∀ j : Fin 69, Bstar (helperSlot j) ≤ bnd ρE σHE j := by decide +kernel
theorem Bstar_a : ∀ j : Fin 85, Bstar (autSlot j) ≤ bnd ρE σAE j := by decide +kernel
theorem Bstar_t : ∀ j : Fin 104, Bstar (tailSlot j) ≤ bnd ρE σTE j := by decide +kernel

/-- The destination of a loader operation. -/
def opDst : InitOp → Fin 321
  | .read _ d _ => d
  | .copy d _ => d
  | .word d _ => d

/-- The cheap check: a stream or literal into a tape bounded by the top only, or a copy into a
tape bounded at least as its source. -/
def okB : InitOp → Bool
  | .read _ d _ => Nat.beq (Bstar d) (2 ^ 99)
  | .word d _ => Nat.beq (Bstar d) (2 ^ 99)
  | .copy d s => Nat.ble (Bstar s) (Bstar d)

theorem ok_gen (op : InitOp) (h : okB op = true) (hc : op.cost ≤ 60 * 2 ^ 99) :
    opOK Bstar op := by
  cases op with
  | read s d n =>
    simp only [okB, Nat.beq_eq] at h
    simp only [InitOp.cost] at hc
    show n ≤ Bstar d; omega
  | copy d s => exact Nat.le_of_ble_eq_true h
  | word d w =>
    simp only [okB, Nat.beq_eq] at h
    simp only [InitOp.cost] at hc
    show w.length ≤ Bstar d; omega

theorem ok_len (op : InitOp) (h : opLen op ≤ Bstar (opDst op))
    (hc : (match op with | .copy _ _ => false | _ => true) = true) : opOK Bstar op := by
  cases op with
  | read s d n => exact h
  | copy d s => simp at hc
  | word d w => exact h

theorem Dc_N' : Dc.N = 2 ^ 24 := rfl
theorem Dc_K' : Dc.K = 2 ^ 16 := by show Kc = _; rw [Kc_def]
theorem Dc_mb' : Dc.mb = 3 * 2 ^ 40 + 408 := by
  show mbar = _; rw [mbar_def, Kc_def]; norm_num [en]
theorem gD_Dc' : gD Dc = 9 := by
  show Lattices.gGen Dc.N (2 ^ Dc.b) = 9
  rw [Dc_N', Dc_b]; rfl

theorem cost_encInitOps_le : ∀ op ∈ encInitOps Dc, op.cost ≤ 60 * 2 ^ 99 :=
  fun op hop => (initOp_cost_le_sum op _ hop).trans encInitOps_cost_tight

theorem cols_Dc : (Enum.list (α := BCol (Wb Dc) Dc.K)).length = 3 * 2 ^ 40 + 408 + 2 ^ 16 := by
  show (Enum.list (α := Fin Dc.mb ⊕ Fin Dc.K)).length = _
  rw [len_sum, len_fin, len_fin, Dc_mb', Dc_K']

/-- **Every loader operation respects the core box.** -/
theorem opOK_encInit : ∀ op ∈ encInitOps Dc, opOK Bstar op := by
  intro op hop
  revert op
  suffices H : ∀ op ∈ encInitOps Dc, op.cost ≤ 60 * 2 ^ 99 → opOK Bstar op from
    fun op hop => H op hop (cost_encInitOps_le op hop)
  simp only [encInitOps, publicInitOps, coinInitOps, templateInitOps, finRange8,
    List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map, List.forall_mem_nil,
    and_true]
  repeat' apply And.intro
  all_goals first
    | (intro hc; exact ok_gen _ (by decide +kernel) hc)
    | (simp; done)
    | (intro _; refine ok_len _ ?_ rfl
       simp only [opLen, opDst, zeroInit, List.length_replicate, length_wd, cols_Dc, Dc_N', Dc_K',
         gD_Dc']
       decide +kernel)

/-- The loader's clock. -/
def initT : ℕ := (60 * 2 ^ 99 + 83) * (32 * 2 ^ 99 + 32)

/-- The erasure's clock. -/
def eraseT : ℕ := (325 + 1) * 2 ^ 102

/-- **Loader, core and erasure**, from a normalized store (core tapes blank). -/
theorem cleanCore_tight (ℓ : Fin 326 → ℕ) (hM : ∀ t, ℓ t ≤ 2 ^ 99)
    (h0 : ∀ i, ℓ (coreTape i) = 0) :
    timeBoundT (cleanCoreP Dc) ℓ ≤ initT + coreT + eraseT ∧
      ∀ t, lenBoundT (cleanCoreP Dc) ℓ t ≤ 2 ^ 99 := by
  have e1 : cleanCoreP Dc = .seq (.seq (initProgram (encInitOps Dc)) (map coreTape (encCoreP Dc)))
      eraseNonoutput := rfl
  have e2 : eraseNonoutput = eraseP ((List.finRange 325).map Fin.succ) := rfl
  rw [e1, e2, timeBoundT_seqL, lenBoundT_seqL]
  obtain ⟨i1, i2, i3⟩ := initB_spec (2 ^ 99) (encInitOps Dc) cost_encInitOps_le ℓ (fun _ => 0)
    hM (fun i => (h0 i).le)
  have hB := initB_le Bstar (encInitOps Dc) (fun _ => 0) (fun _ => Nat.zero_le _) opOK_encInit
  have hc := core_tight _ i2 (fun j => (i1 _).trans ((hB _).trans (Bstar_b j)))
    (fun j => (i1 _).trans ((hB _).trans (Bstar_h j)))
    (fun j => (i1 _).trans ((hB _).trans (Bstar_a j)))
    (fun j => (i1 _).trans ((hB _).trans (Bstar_t j)))
  have he := phase_eraseP ((List.finRange 325).map Fin.succ) _ hc.2
  refine ⟨?_, he.2⟩
  have hlen : ((List.finRange 325).map Fin.succ).length = 325 := by simp
  have hs := encInitOps_cost_tight
  have hl : (encInitOps Dc).length = 82 := length_encInitOps Dc
  have hi : timeBoundT (initProgram (encInitOps Dc)) ℓ ≤ initT := by
    refine i3.trans (Nat.mul_le_mul_right _ ?_)
    rw [hl]; omega
  have h1 := hc.1
  have h2 := he.1
  rw [hlen] at h2
  unfold eraseT
  omega

set_option exponentiation.threshold 2000 in
/-- **The production suffix**: relocation, normalization, loader, core and erasure. -/
theorem suffix_tight {ℓ : Fin 326 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 110) :
    timeBoundT (.seq relocateP (.seq (normalizeInputsP Dc) (cleanCoreP Dc))) ℓ ≤ 2 ^ 242 ∧
      ∀ i, lenBoundT (.seq relocateP (.seq (normalizeInputsP Dc) (cleanCoreP Dc))) ℓ i ≤
        2 ^ 99 := by
  rw [timeBoundT_seqR, lenBoundT_seqR]
  have r1 : timeBoundT relocateP ℓ ≤ 2 ^ 115 :=
    (time_noGrow_le relocateP (by rfl) hℓ).trans (by norm_num [relocateP, tbC, tbD])
  have r2 := Sym.lenBoundT_le_const relocateP (by rfl) hℓ
  have n1 := time_normalizeInputsP r2
  have n2 := normalize_lengths (lenBoundT relocateP ℓ)
  have n0 : ∀ i, lenBoundT (normalizeInputsP Dc) (lenBoundT relocateP ℓ) (coreTape i) = 0 := by
    intro i
    rw [lenBoundT_normalizeInputsP]
    have : (coreTape i).val < 321 := i.isLt
    rw [if_neg (by intro h; rw [h] at this; simp at this),
      if_neg (by intro h; rw [h] at this; simp at this)]
  obtain ⟨c1, c2⟩ := cleanCore_tight _ n2 n0
  refine ⟨?_, c2⟩
  have : initT + coreT + eraseT ≤ 2 ^ 242 - 2 ^ 213 := by
    unfold initT coreT eraseT; norm_num
  omega

/-- Composition along the actual randomized program, with the tight suffix. -/
theorem bounds_encProgram_tight : XBound (encProgram Dc 16 6 eFl) (2 ^ 100)
    ((2 ^ 301 + 2 ^ 242) + 2 ^ 205) (2 ^ 101) := by
  have hs : XBound (.prog (.seq relocateP (.seq (normalizeInputsP Dc) (cleanCoreP Dc))))
      (2 ^ 110) (2 ^ 242) (2 ^ 99) := fun _ h => suffix_tight h
  exact (bounds_widePrepare.seq hs).seq bounds_frameCiphertextP

end AdvancedEncryption.ExpLUT.Prog.EncTight
