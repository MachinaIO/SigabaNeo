import PE.Impl.ExpLUT.Prog.TapeEnc

/-!
# The clock of the packed encryption machine

Every logical tape of the encryption program stays at most `TE = 2^110` bits long. With a
workspace of `105` tapes:

* the parser and sampler (`widePrepare`, `105` tapes) is **one** leaf group, charged its old clock
  (`≤ 2^214 + 2^252`, `EncTight.boundsP_prepare`);
* the plain suffix (normalization, loader, core, erasure) is flat at the wide level: a sequence of
  narrow leaves (each literal read or word of the loader, each clear, each trim, and each of the
  four core phases mapped on its `≤ 104` tapes), so it costs its old clock (`≤ 2^242`,
  `EncTight.suffix_tight`) plus one overhead `ovT 105 326 TE` per leaf (`fp_suffix`);
* the ciphertext framing has one wide loop (`frameApP`'s counter, at most `2^99 + 2` rounds), charged
  by `FXa.loop`.

**`time_encMachineP : encMachineP.time ≤ 2 ^ 253`** (the old clock: `2^253`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.TapeEnc

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Pack AdvancedEncryption.ExpLUT.Params
open AdvancedEncryption.ExpLUT.Prog.EncW Function

/-- The cap of every logical tape. -/
abbrev TE : ℕ := 2 ^ 110

/-- The identity placement. -/
abbrev ι : Fin 326 ↪ Fin 326 := Embedding.refl _

theorem hwE : 3 ≤ wE := by decide

/-! ### The plain suffix -/

theorem fp_eraseP : ∀ is : List (Fin 326),
    FP wE TE ι (eraseP is) (Le TE) (Le TE) (is.length + 1)
  | [] => FP.leafB ι (narrowP_prim hwE _) (bndP_noGrow rfl)
  | i :: is => (FP.seq (FP.leafB ι (narrowP_prim hwE (.clear i)) (bndP_noGrow rfl))
      (fp_eraseP is)).mono (fun _ h => h) (fun _ h => h) (by simp only [List.length_cons]; omega)

theorem fp_trimP (src tmp : Fin 326) (n : ℕ) (hn : n ≤ TE) :
    FP wE TE ι (trimP src tmp n) (Le TE) (Le TE) 1 := by
  refine FP.leafB ι (narrowP_of_subT [tmp, src] (by simp; decide) ?_) ?_
  · refine subT_seq (subT_putW _ _ (by simp)) (subT_seq (subT_prim _ (by simp [Prim.tapes]))
      (subT_seq (subT_prim _ ?_) (subT_prim _ (by simp [Prim.tapes]))))
    intro t ht
    simp only [Prim.tapes, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht ⊢
    tauto
  · intro ℓ hℓ t
    rw [lenBoundT_trimP]
    simp only [Function.update_apply]
    split_ifs
    · omega
    · exact hn
    · exact hℓ t

set_option maxRecDepth 100000 in
theorem noGrow_mvP : SigabaNeo.Tape.Prog.mvP.NoGrow := by decide +kernel

theorem fp_initOp (op : InitOp) (hop : EncTight.opLen op ≤ TE) :
    FP wE TE ι op.program (Le TE) (Le TE) 1 := by
  cases op with
  | read src dst n =>
    refine FP.leafB ι (narrowP_of_subT (323 :: coreTape dst :: (List.finRange 5).map
      (readMap src dst)) (by simp; decide) ?_) ?_
    · refine subT_seq (subT_putW _ _ (by simp)) (subT_seq (subT_prim _ (by simp [Prim.tapes]))
        (subT_seq (subT_map _ _ (fun j => by simp)) (subT_prim _ (by simp [Prim.tapes]))))
    · exact bndP_seq (bndP_putW _ _ (by simpa [EncTight.opLen] using hop)) (bndP_seq (bndP_noGrow rfl)
        (bndP_seq (bndP_noGrow (noGrow_mvP.map _)) (bndP_noGrow rfl)))
  | copy dst src => exact FP.leafB ι (narrowP_prim hwE _) (bndP_noGrow rfl)
  | word dst w =>
    exact FP.leafB ι (narrowP_of_subT [coreTape dst] (by simp) (subT_putW _ _ (by simp)))
      (bndP_putW _ _ (by simpa [EncTight.opLen] using hop))

theorem fp_initProgram : ∀ ops : List InitOp, (∀ op ∈ ops, EncTight.opLen op ≤ TE) →
    FP wE TE ι (initProgram ops) (Le TE) (Le TE) (ops.length + 1)
  | [], _ => FP.leafB ι (narrowP_prim hwE _) (bndP_noGrow rfl)
  | op :: ops, h => (FP.seq (fp_initOp op (h op (by simp)))
      (fp_initProgram ops (fun o ho => h o (by simp [ho])))).mono (fun _ h => h) (fun _ h => h)
        (by simp only [List.length_cons]; omega)

set_option maxRecDepth 100000 in
theorem noGrow_mrowP : SigabaNeo.Tape.Prog.mrowP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_hBlkP : SigabaNeo.Tape.Prog.hBlkP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_autBlkP : SigabaNeo.Tape.Prog.autBlkP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_tailP : SigabaNeo.Tape.Prog.tailP.NoGrow := by decide +kernel

theorem bndP_helperPairsP : ∀ j n : ℕ, j + n ≤ 22 → BndP TE (helperPairsP Dc j n)
  | j, 0, _ => bndP_noGrow rfl
  | j, n + 1, h => by
    have h1 : 2 ^ j ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine bndP_seq ?_ (bndP_helperPairsP (j + 1) n (by omega))
    refine bndP_seq (bndP_putW _ _ ?_) (bndP_seq (bndP_putW _ _ ?_)
      (bndP_seq (bndP_noGrow noGrow_hBlkP) (bndP_noGrow rfl)))
    · simp only [List.length_replicate]; exact h1.trans (by norm_num)
    · simp only [List.length_replicate]
      exact (Nat.sub_le _ _).trans (by show 2 ^ 22 ≤ TE; norm_num)

theorem bndP_autBlocksP : ∀ j n : ℕ, j + n ≤ 22 → BndP TE (autBlocksP Dc j n)
  | j, 0, _ => bndP_noGrow rfl
  | j, n + 1, h => by
    have h1 : 2 ^ j ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine bndP_seq ?_ (bndP_autBlocksP (j + 1) n (by omega))
    refine bndP_seq (bndP_putW _ _ ?_) (bndP_seq (bndP_putW _ _ ?_)
      (bndP_seq (bndP_noGrow noGrow_autBlkP) (bndP_noGrow rfl)))
    · simp only [List.length_replicate]; exact h1.trans (by norm_num)
    · simp only [List.length_replicate]
      exact (Nat.sub_le _ _).trans (by show 2 ^ 22 ≤ TE; norm_num)

/-- A core phase, mapped on its tapes, is one leaf group. -/
theorem fp_block {n : ℕ} (hn : n ≤ wE) (u : Fin n → Fin 321) (hu : Injective u)
    (p : SigabaNeo.Tape.Prog n) (hb : BndP TE p) :
    FP wE TE ι (Tape.Prog.map coreTape (Tape.Prog.map u p)) (Le TE) (Le TE) 1 := by
  rw [Tape.Prog.map_map]
  exact FP.leafB ι (narrowP_map hn _ p) (bndP_map ⟨coreTape ∘ u, coreTape_inj.comp hu⟩ hb)

theorem fp_core : FP wE TE ι (Tape.Prog.map coreTape (encCoreP Dc)) (Le TE) (Le TE) 4 := by
  show FP wE TE ι (.seq (Tape.Prog.map coreTape (Tape.Prog.map bSlot SigabaNeo.Tape.Prog.mrowP))
    (.seq (Tape.Prog.map coreTape (Tape.Prog.map helperSlot (helperPairsP Dc 0 Dc.b)))
      (.seq (Tape.Prog.map coreTape (Tape.Prog.map autSlot (autBlocksP Dc 0 Dc.b)))
        (Tape.Prog.map coreTape (Tape.Prog.map tailSlot SigabaNeo.Tape.Prog.tailP))))) (Le TE) (Le TE) (1 + (1 + (1 + 1)))
  exact FP.seq (fp_block (by decide) _ bSlot_inj _ (bndP_noGrow noGrow_mrowP))
    (FP.seq (fp_block (by decide) _ helperSlot_inj _ (bndP_helperPairsP 0 _ (by decide)))
      (FP.seq (fp_block (by decide) _ autSlot_inj _ (bndP_autBlocksP 0 _ (by decide)))
        (fp_block (by decide) _ tailSlot_inj _ (bndP_noGrow noGrow_tailP))))

/-- The plain suffix of the encryption program. -/
noncomputable abbrev suffixP : SigabaNeo.Tape.Prog 326 :=
  .seq relocateP (.seq (normalizeInputsP Dc) (cleanCoreP Dc))

/-- The number of its leaf groups. -/
noncomputable def nS : ℕ := 1 + ((1 + (1 + (inputScratch.length + 1))) +
  ((((encInitOps Dc).length + 1) + 4) + (((List.finRange 325).map Fin.succ).length + 1)))

theorem opLen_encInit : ∀ op ∈ encInitOps Dc, EncTight.opLen op ≤ TE := fun op hop =>
  (EncTight.opLen_le_cost op).trans ((EncTight.cost_encInitOps_le op hop).trans (by norm_num))

set_option maxRecDepth 100000 in
theorem fp_suffix : FP wE TE ι suffixP (Le TE) (Le (2 ^ 99)) nS := by
  have hc : coinLength Dc + publicLength Dc ≤ 115 * 2 ^ 91 := EncConf.normalization_lengths_tight
  have h := FP.seq (FP.leafB ι (q := relocateP) (by decide) (bndP_noGrow (by decide)))
    (FP.seq (FP.seq (fp_trimP 321 323 (coinLength Dc) (by show _ ≤ 2 ^ 110; omega))
      (FP.seq (fp_trimP 322 323 (publicLength Dc) (by show _ ≤ 2 ^ 110; omega)) (fp_eraseP inputScratch)))
      (FP.seq (FP.seq (fp_initProgram (encInitOps Dc) opLen_encInit) fp_core)
        (fp_eraseP ((List.finRange 325).map Fin.succ))))
  refine FP.post (h.mono (fun _ h => h) (fun _ h => h) le_rfl) fun L hL t => ?_
  rw [Lafter_refl]
  exact (EncTight.suffix_tight (fun i => (hL i).trans le_rfl)).2 t

set_option maxRecDepth 100000 in
theorem nS_le : nS ≤ 1000 := by
  have h1 : inputScratch.length ≤ 326 := (List.length_filter_le _ _).trans (by simp)
  have h2 : (encInitOps Dc).length ≤ 200 := by decide
  simp only [nS, List.length_map, List.length_finRange]
  omega

/-! ### Parser, sampler and suffix -/

/-- The first part: the parser and sampler, then the plain suffix. -/
noncomputable abbrev partA : XProg 326 := .seq (widePrepare Dc 16 6 eFl) (.prog suffixP)

theorem le_inputBound (n : ℕ) (hn : n ≤ 2 ^ 100) :
    Le TE (SigabaNeo.Tape.Prog.inputBound (0 : Fin 326) n) := fun t => by
  simp only [SigabaNeo.Tape.Prog.inputBound, Function.update_apply]
  split_ifs <;> [exact hn.trans (by norm_num); exact Nat.zero_le _]

theorem fx_partA (n : ℕ) (hn : n ≤ 2 ^ 100) :
    FX wE TE ι partA (fun L => L = SigabaNeo.Tape.Prog.inputBound 0 n) (Le (2 ^ 99)) (1 + nS) := by
  refine FX.seq (FX.frame (FX.leaf le_rfl _ _ fun L hL => ?_)) (FX.prog fp_suffix)
  subst hL
  have hb := EncTight.boundsP_prepare _ (EncTight.inputBound_prepareFrame n hn)
  have hA : Le TE (Lafter (prepareFrame.trans ι) (EncIO.prepare Dc 16 6 eFl)
      (SigabaNeo.Tape.Prog.inputBound 0 n)) := fun t => by
    simp only [Lafter]
    rcases embedF_cases (prepareFrame.trans ι) (SigabaNeo.Tape.Prog.inputBound 0 n)
      (XProg.lenBoundT (EncIO.prepare Dc 16 6 eFl)
        fun j => SigabaNeo.Tape.Prog.inputBound 0 n ((prepareFrame.trans ι) j)) t with
      ⟨-, h⟩ | ⟨j, -, h⟩
    · rw [h]; exact le_inputBound n hn t
    · rw [h]; exact (hb.2 j).trans (by norm_num)
  exact ⟨le_inputBound n hn, hA, hA⟩

/-- The old clock of the first part. -/
theorem time_partA (n : ℕ) (hn : n ≤ 2 ^ 100) :
    partA.timeBoundT (SigabaNeo.Tape.Prog.inputBound 0 n) ≤ 2 ^ 214 + 2 ^ 252 + 2 ^ 242 := by
  have hW := EncTight.boundsP_prepare _ (EncTight.inputBound_prepareFrame n hn)
  have hl₁ : ∀ i, XProg.lenBoundT (widePrepare Dc 16 6 eFl)
      (SigabaNeo.Tape.Prog.inputBound (0 : Fin 326) n) i ≤ 2 ^ 110 := fun i => by
    show embedF prepareFrame _ _ i ≤ _
    rcases embedF_cases prepareFrame (SigabaNeo.Tape.Prog.inputBound (0 : Fin 326) n)
      (XProg.lenBoundT (EncIO.prepare Dc 16 6 eFl)
        fun j => SigabaNeo.Tape.Prog.inputBound 0 n (prepareFrame j)) i with ⟨-, h⟩ | ⟨j, -, h⟩
    · rw [h]; exact le_inputBound n hn i
    · rw [h]; exact (hW.2 j).trans (by norm_num)
  have hS : SigabaNeo.Tape.Prog.timeBoundT suffixP _ ≤ 2 ^ 242 := (EncTight.suffix_tight hl₁).1
  show XProg.timeBoundT (EncIO.prepare Dc 16 6 eFl)
      (fun j => SigabaNeo.Tape.Prog.inputBound 0 n (prepareFrame j)) +
    SigabaNeo.Tape.Prog.timeBoundT suffixP (XProg.lenBoundT (widePrepare Dc 16 6 eFl)
      (SigabaNeo.Tape.Prog.inputBound (0 : Fin 326) n)) ≤ _
  have := hW.1
  omega

/-! ### The ciphertext framing -/

/-- The bound of the framing's input. -/
abbrev B0 : ℕ := 2 ^ 99

theorem Lafter_prim (a : Prim 326) (L : Fin 326 → ℕ) :
    Lafter ι (.prog (.prim a)) L = a.lenT L := by
  rw [Lafter_refl]; rfl

/-- One primitive raising every tape by at most one, between two caps below `TE`. -/
theorem fxa_prim (a : Prim 326) {B : ℕ} (hB : B + 1 ≤ TE) :
    FXa wE TE ι (.prog (.prim a)) (Le B) (Le (B + 1)) (2 * (TE + 1) + 3 + ovT wE 326 TE) :=
  FXa.prim hwE ι a fun L hL => by
    rw [Lafter_prim]
    exact ⟨fun t => (hL t).trans (by omega), fun t => (lenT_le_succ a hL t).trans hB,
      fun t => lenT_le_succ a hL t⟩

/-- The body of the framing loop. -/
abbrev frBody : XProg 326 :=
  .seq (.prog (.prim (.snoc 0 true))) (.seq (.prog (.prim (.snocHead 0 2))) (.prog (.prim (.tail 2))))

theorem lenBoundT_frBody (ℓ : Fin 326 → ℕ) (t : Fin 326) :
    frBody.lenBoundT (tailB 3 ℓ) t ≤ ℓ t + 2 := by
  simp only [frBody, XProg.lenBoundT, SigabaNeo.Tape.Prog.lenBoundT, Prim.lenT, tailB,
    Function.update_apply]
  split_ifs <;> simp_all <;> omega

/-- The bound after the framing loop from `Le B`: at most `3 B`. -/
theorem lafter_loop {B : ℕ} {L : Fin 326 → ℕ} (hL : Le B L) :
    Le (3 * B) (Lafter ι (.loop 3 frBody) L) := fun t => by
  rw [Lafter_refl]
  show iterSupT (fun ℓ' => frBody.lenBoundT (tailB 3 ℓ')) (L 3) L t ≤ _
  have := iterSupT_le_add (c := 2) (fun ℓ t => lenBoundT_frBody ℓ t) (L 3) L t
  have := hL t
  have := hL 3
  omega

/-- **The framing loop.** -/
theorem fxa_loop {B : ℕ} (hB : 3 * B + 3 ≤ TE) :
    FXa wE TE ι (.loop 3 frBody) (Le B) (Le (3 * B))
      ((6 * (326 * (2 * TE + 1)) + 16) +
        (B * (loopOv (326 * (2 * TE + 1)) TE + 3 * (2 * (TE + 1) + 3 + ovT wE 326 TE)) + 2)) := by
  have hb : FXa wE TE ι frBody (Le (3 * B)) (Le (3 * B + 1 + 1 + 1))
      ((2 * (TE + 1) + 3 + ovT wE 326 TE) +
        ((2 * (TE + 1) + 3 + ovT wE 326 TE) + (2 * (TE + 1) + 3 + ovT wE 326 TE))) :=
    FXa.seq (by decide) (fxa_prim _ (by omega))
      (FXa.seq (by decide) (fxa_prim _ (by omega)) (fxa_prim _ (by omega)))
  refine (FXa.loop (by decide) (fun L hL => hL 3) (fun L hL => ⟨fun t => (hL t).trans (by omega),
    fun t => (lafter_loop hL t).trans (by omega), lafter_loop hL, lafter_loop hL⟩) hb).mono
    (fun _ h => h) (fun _ h => h) (le_of_eq (by ring))

/-- The framing's first piece: `1 := 0`, `0 := []`. -/
abbrev frPre : SigabaNeo.Tape.Prog 326 := .seq (.prim (.copy 1 0)) (.prim (.clear 0))

theorem fxa_frPre : FXa wE TE ι (.prog frPre) (Le B0) (Le B0)
    (frPre.tbC * (B0 + 1) ^ frPre.tbD + ovT wE 326 TE) :=
  FXa.narrowProg ι (by decide) (fun L hL =>
      ⟨fun t => (hL t).trans (by norm_num), le_Lafter_of_bndP (w := wE) (q := frPre) (bndP_noGrow rfl)
        (fun t => (hL t).trans (by norm_num)),
        le_Lafter_of_bndP (w := wE) (q := frPre) (bndP_noGrow rfl) hL⟩)
    fun L hL => time_noGrow_le frPre rfl hL

/-- The time of a primitive leaf. -/
abbrev tP : ℕ := 2 * (TE + 1) + 3 + ovT wE 326 TE

/-- The time of the framing loop. -/
abbrev tL : ℕ := (6 * (326 * (2 * TE + 1)) + 16) +
  ((B0 + 2) * (loopOv (326 * (2 * TE + 1)) TE + 3 * tP) + 2)

/-- **The ciphertext framing.** -/
theorem fxa_frame : FXa wE TE ι frameCiphertextP (Le B0) (fun _ => True)
    ((frPre.tbC * (B0 + 1) ^ frPre.tbD + ovT wE 326 TE) +
      ((tP + ((tP + tL) + (tP + tP))) + tP)) := by
  show FXa wE TE ι (.seq (.prog frPre) (.seq (.seq (.prog (.prim (.copy 2 1)))
    (.seq (.seq (.prog (.prim (.copy 3 1))) (.loop 3 frBody))
      (.seq (.prog (.prim (.snoc 0 false))) (.prog (.prim (.clear 2))))))
    (.prog (.prim (.clear 1))))) (Le B0) (fun _ => True) _
  have hk : ¬ 326 ≤ wE := by decide
  exact FXa.seq hk fxa_frPre (FXa.seq hk (FXa.seq hk (fxa_prim _ (by norm_num))
    (FXa.seq hk (FXa.seq hk (fxa_prim _ (by norm_num)) (fxa_loop (B := B0 + 1 + 1) (by norm_num)))
      (FXa.seq hk (fxa_prim _ (by norm_num)) (fxa_prim _ (by norm_num)))))
    ((fxa_prim _ (by norm_num)).mono (fun _ h => h) (fun _ _ => trivial) le_rfl))

/-! ### The machine -/

theorem fxa_encProgram (n : ℕ) (hn : n ≤ 2 ^ 100) :
    FXa wE TE ι (encProgram Dc 16 6 eFl) (fun L => L = SigabaNeo.Tape.Prog.inputBound 0 n)
      (fun _ => True)
      (((2 ^ 214 + 2 ^ 252 + 2 ^ 242) + (1 + nS) * ovT wE 326 TE) +
        ((frPre.tbC * (B0 + 1) ^ frPre.tbD + ovT wE 326 TE) +
          ((tP + ((tP + tL) + (tP + tP))) + tP))) := by
  show FXa wE TE ι (.seq partA frameCiphertextP) _ _ _
  refine FXa.seq (by decide) (FXa.of_FX (fx_partA n hn) fun L hL => ?_) fxa_frame
  subst hL
  exact time_partA n hn

theorem frPre_tb : frPre.tbC ≤ 100 ∧ frPre.tbD ≤ 1 := by
  constructor <;> norm_num [frPre, SigabaNeo.Tape.Prog.tbC, SigabaNeo.Tape.Prog.tbD]

set_option exponentiation.threshold 2000 in
theorem arith_enc {n o x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℕ} (h1 : x5 ≤ 100 * (2 ^ 99 + 1))
    (h2 : x3 ≤ 1001 * x4) (h3 : x6 ≤ x7) (h4 : x4 ≤ 2 ^ 134) (h5 : x1 ≤ 2 ^ 236)
    (h6 : x2 ≤ 2 ^ 135) (h7 : x7 ≤ 2 ^ 110) (h8 : x8 ≤ 327 * (2 * (2 ^ 100 + 326) + 5))
    (h9 : x9 ≤ 2 ^ 122) (hn : n ≤ 2 ^ 100) (ho : o ≤ 2 ^ 101) :
    (2 * n + 2) + x8 + x6 + ((((2 ^ 214 + 2 ^ 252 + 2 ^ 242) + x3) +
      ((x5 + x4) + ((x2 + ((x2 + x1) + (x2 + x2))) + x2)))) + x9 + (2 * o + 2) ≤ 2 ^ 253 := by
  omega

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem time_enc_num (n : ℕ) (hn : n ≤ 2 ^ 100) (N : ℕ) (hN : N ≤ 1000) (c d : ℕ) (hc : c ≤ 100)
    (hd : d ≤ 1) (o : ℕ) (ho : o ≤ 2 ^ 101) :
    (2 * n + 2) + (326 + 1) * (2 * (n + 326) + 5) + putTime 326 n +
      ((((2 ^ 214 + 2 ^ 252 + 2 ^ 242) + (1 + N) * ovT wE 326 TE) +
        ((c * (B0 + 1) ^ d + ovT wE 326 TE) + ((tP + ((tP + tL) + (tP + tP))) + tP)))) +
      (6 * (326 * (2 * TE + 1)) + 16) + (2 * o + 2) ≤ 2 ^ 253 := by
  have hp : (B0 + 1) ^ d ≤ B0 + 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl <;> simp
  have h1 : c * (B0 + 1) ^ d ≤ 100 * (B0 + 1) := Nat.mul_le_mul hc hp
  have h2 : (1 + N) * ovT wE 326 TE ≤ 1001 * ovT wE 326 TE := Nat.mul_le_mul_right _ (by omega)
  have h3 : putTime 326 n ≤ putTime 326 (2 ^ 100) := putTime_mono le_rfl hn
  have h4 : ovT wE 326 TE ≤ 2 ^ 134 := by
    unfold ovT putTime; norm_num
  have h6 : tP ≤ 2 ^ 135 := by
    show 2 * (2 ^ 110 + 1) + 3 + ovT wE 326 TE ≤ 2 ^ 135
    omega
  have hlo : loopOv (326 * (2 * TE + 1)) TE ≤ 2 ^ 125 := by unfold loopOv putTime; norm_num
  have h5 : tL ≤ 2 ^ 236 := by
    show (6 * (326 * (2 * 2 ^ 110 + 1)) + 16) +
      ((2 ^ 99 + 2) * (loopOv (326 * (2 * TE + 1)) TE + 3 * tP) + 2) ≤ 2 ^ 236
    have hm : (2 ^ 99 + 2) * (loopOv (326 * (2 * TE + 1)) TE + 3 * tP) ≤
        (2 ^ 99 + 2) * (2 ^ 125 + 3 * 2 ^ 135) := Nat.mul_le_mul_left _ (by omega)
    have : (6 * (326 * (2 * 2 ^ 110 + 1)) + 16) + ((2 ^ 99 + 2) * (2 ^ 125 + 3 * 2 ^ 135) + 2) ≤
        2 ^ 236 := by norm_num
    omega
  have h7 : putTime 326 (2 ^ 100) ≤ 2 ^ 110 := by unfold putTime; norm_num
  have h8 : (326 + 1) * (2 * (n + 326) + 5) ≤ 327 * (2 * (2 ^ 100 + 326) + 5) :=
    Nat.mul_le_mul_left _ (by omega)
  have h9 : 6 * (326 * (2 * TE + 1)) + 16 ≤ 2 ^ 122 := by norm_num
  exact arith_enc h1 h2 h3 h4 h5 h6 h7 h8 h9 hn ho

set_option maxRecDepth 100000 in
/-- **The clock of the packed encryption machine**: at most `2^253` steps. -/
theorem time_encMachineP : encMachineP.time ≤ 2 ^ 253 := by
  have hn := EncConf.encInputLength_le
  have h := time_packMachineT_le' (D := dE) (encProgram Dc 16 6 eFl) 0 0 (encInputLength Dc)
    (fxa_encProgram _ hn)
  have ho : XProg.lenBoundT (encProgram Dc 16 6 eFl)
      (SigabaNeo.Tape.Prog.inputBound 0 (encInputLength Dc)) 0 ≤ 2 ^ 101 :=
    (EncTight.bounds_encProgram_tight _ (fun i => by
      simp only [SigabaNeo.Tape.Prog.inputBound, Function.update_apply]
      split_ifs <;> [exact hn; exact Nat.zero_le _])).2 0
  exact h.trans (time_enc_num _ hn _ nS_le _ _ frPre_tb.1 frPre_tb.2 _ ho)

end AdvancedEncryption.ExpLUT.Prog.TapeEnc
