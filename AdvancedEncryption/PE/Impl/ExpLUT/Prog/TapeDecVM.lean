import PE.Impl.ExpLUT.Prog.TapeDec
open SigabaNeo.Tape.RingVM.Flow
/-!
# The packed clock of the ring-word machine code of `Dec`

The compiled code (`RingVM.compile`) is packed with a workspace of `37` tapes: every instruction is
a sequence of at most four frames on at most `37` tapes running a non-lengthening program, so it is
flat (`fx_instr`); the control (`seq`, `ifb`, `rep`) is packed (`FXa.seq`, `FXa.ifBit`,
`FXa.loop`). Every logical tape stays at most `TD = 2^110` long.

`CodeOKP c B B' T`: from the register bounds `B` the packed code ends below `B'` within
`fD · T` steps, `fD = 1 + 4 · ovT 37 256 TD` (one leaf overhead per frame, the control overheads
absorbed in the factor). **`absRun_soundP`**: the abstract run of `DecT` (its clock `T`) gives
`CodeOKP`; the block certificates of `DecTight` glue as in `DecTight.dt_decCode`, so

**`dtP_decCode : CodeOKP decCode (toB dtB0) (toB dtBend) dtTvm`**, and the code framed on the
tapes `0 … 246` (`fxa_vm`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.TapeDec

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Pack SigabaNeo.Tape.RingVM Function
open SigabaNeo.Tape.RingVM.Flow (CodeOK toB absRun loopFix ble bmax lmax)
open AdvancedEncryption.ExpLUT.Prog.DecTight

/-- The cap of every logical tape. -/
abbrev TD : ℕ := 2 ^ 110
/-- The placement of the machine's tapes. -/
abbrev σv : Fin 247 ↪ Fin 256 := vmE.trans (Embedding.refl _)
/-- The slowdown factor of the code. -/
abbrev fD : ℕ := 1 + 4 * ovT wD 256 TD

theorem fD_ge : loopOv (256 * (2 * TD + 1)) TD ≤ fD ∧ 6 * (256 * (2 * TD + 1)) + 18 ≤ 2 * fD ∧
    (6 * (256 * (2 * TD + 1)) + 16) + ((2 * (256 * (2 * TD + 1)) + 3) + 1) ≤ fD := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [fD, TD, ovT, loopOv, putTime]

/-! ### Instructions are flat -/

set_option maxRecDepth 100000 in
theorem noGrow_inP : (ValVM.inP).NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_outP : (ValVM.outP).NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_mvPc : (ValVM.mvPc).NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_dropPc : (ValVM.dropPc).NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_addRMP : Prog.addRMP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_subRMP : Prog.subRMP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_mulRMP : Prog.mulRMP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_canonRP : Prog.canonRP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_notP : Prog.notP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_digitRWP : Prog.digitRWP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_rotBP : Prog.rotBP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_autMP : Prog.autMP.NoGrow := by decide +kernel
set_option maxRecDepth 100000 in
theorem noGrow_rhoJP : Prog.rhoJP.NoGrow := by decide +kernel

/-- A frame on at most `37` tapes running a non-lengthening program is one leaf group. -/
theorem fx_fr {m : ℕ} (hm : m ≤ wD) (e : Fin m ↪ Fin 247) {P : SigabaNeo.Tape.Prog m}
    (hP : P.NoGrow) : FX wD TD σv (.frame e (.prog P)) (Le TD) (Le TD) 1 :=
  FX.frame (FX.leaf hm _ _ fun L hL =>
    ⟨hL, le_Lafter_of_bndP (w := wD) (bndP_noGrow hP) hL,
      le_Lafter_of_bndP (w := wD) (bndP_noGrow hP) hL⟩)

/-- The control instructions. -/
def isCtl : Code → Bool
  | .rep _ _ | .seq _ _ | .ifb _ _ _ => true
  | _ => false

theorem fx_loadT (t : Fin 200) : FX wD TD σv (loadT t) (Le TD) (Le TD) 1 :=
  fx_fr (P := SigabaNeo.Tape.Prog.cp 0 1) (by decide) _ rfl

theorem fx_nopX : FX wD TD σv nopX (Le TD) (Le TD) 1 := fx_fr (by decide) _ rfl

theorem fx_mono4 {p : XProg 247} {n : ℕ} (h : FX wD TD σv p (Le TD) (Le TD) n) (hn : n ≤ 4) :
    FX wD TD σv p (Le TD) (Le TD) 4 := h.mono (fun _ h => h) (fun _ h => h) hn

/-- **Every instruction is flat**: at most four leaf groups. -/
theorem fx_instr : ∀ c : Code, isCtl c = false → FX wD TD σv (compile c) (Le TD) (Le TD) 4
  | .add d a b, _ => FX.seq (fx_fr (by decide) _ noGrow_inP) (FX.seq (fx_fr (by decide) _ noGrow_inP)
      (FX.seq (fx_fr (by decide) _ noGrow_addRMP) (fx_fr (by decide) _ noGrow_outP)))
  | .sub d a b, _ => FX.seq (fx_fr (by decide) _ noGrow_inP) (FX.seq (fx_fr (by decide) _ noGrow_inP)
      (FX.seq (fx_fr (by decide) _ noGrow_subRMP) (fx_fr (by decide) _ noGrow_outP)))
  | .mul d a b, _ => FX.seq (fx_fr (by decide) _ noGrow_inP) (FX.seq (fx_fr (by decide) _ noGrow_inP)
      (FX.seq (fx_fr (by decide) _ noGrow_mulRMP) (fx_fr (by decide) _ noGrow_outP)))
  | .canon d a, _ => fx_mono4 (FX.seq (fx_fr (by decide) _ noGrow_inP)
      (FX.seq (fx_fr (by decide) _ noGrow_canonRP) (fx_fr (by decide) _ noGrow_outP))) (by decide)
  | .neg d a, _ => fx_mono4 (FX.seq (fx_fr (by decide) _ noGrow_inP)
      (FX.seq (fx_fr (by decide) _ noGrow_notP) (fx_fr (by decide) _ noGrow_outP))) (by decide)
  | .digit d a t, _ => FX.seq (fx_fr (by decide) _ noGrow_inP) (FX.seq (fx_loadT t)
      (FX.seq (fx_fr (by decide) _ noGrow_digitRWP) (fx_fr (by decide) _ noGrow_outP)))
  | .rotB d a t, _ => FX.seq (fx_fr (by decide) _ noGrow_inP) (FX.seq (fx_loadT t)
      (FX.seq (fx_fr (by decide) _ noGrow_rotBP) (fx_fr (by decide) _ noGrow_outP)))
  | .aut d a t, _ => FX.seq (fx_fr (by decide) _ noGrow_inP) (FX.seq (fx_loadT t)
      (FX.seq (fx_fr (by decide) _ noGrow_autMP) (fx_fr (by decide) _ noGrow_outP)))
  | .rhoJ d a t, _ => FX.seq (fx_fr (by decide) _ noGrow_inP) (FX.seq (fx_loadT t)
      (FX.seq (fx_fr (by decide) _ noGrow_rhoJP) (fx_fr (by decide) _ noGrow_outP)))
  | .mv d s c, _ => by
    show FX wD TD σv (if h : d = s ∨ d = c ∨ s = c then nopX else
      .frame (mkE (fMv d s c) (fMv_inj h)) (.prog ValVM.mvPc)) (Le TD) (Le TD) 4
    split
    · exact fx_mono4 fx_nopX (by decide)
    · exact fx_mono4 (fx_fr (by decide) _ noGrow_mvPc) (by decide)
  | .cp d s, _ => by
    show FX wD TD σv (if h : d = s then nopX else
      .frame (mkE (fCp d s) (fCp_inj h)) (.prog (Prog.cp 0 1))) (Le TD) (Le TD) 4
    split
    · exact fx_mono4 fx_nopX (by decide)
    · exact fx_mono4 (fx_fr (by decide) _ rfl) (by decide)
  | .drop t c, _ => by
    show FX wD TD σv (if h : t = c then nopX else
      .frame (mkE (fDr t c) (fDr_inj h)) (.prog ValVM.dropPc)) (Le TD) (Le TD) 4
    split
    · exact fx_mono4 fx_nopX (by decide)
    · exact fx_mono4 (fx_fr (by decide) _ noGrow_dropPc) (by decide)
  | .clr t, _ => fx_mono4 (fx_fr (by decide) _ rfl) (by decide)
  | .tl t, _ => fx_mono4 (fx_fr (by decide) _ rfl) (by decide)
  | .nop, _ => fx_mono4 fx_nopX (by decide)

/-! ### The judgment -/

/-- The packed stores below the register bounds `B`. -/
def PB (B : Fin 200 → ℕ) (L : Fin 256 → ℕ) : Prop :=
  Le TD L ∧ ∀ j, L (σv j) ≤ encB (2 ^ 40) (2 ^ 24) (2 ^ 16) B j

theorem PB.mono {B B' : Fin 200 → ℕ} (h : B ≤ B') {L : Fin 256 → ℕ} (hL : PB B L) : PB B' L :=
  ⟨hL.1, fun j => (hL.2 j).trans (SigabaNeo.Tape.RingVM.Flow.encB_mono _ _ _ h j)⟩

/-- **The packed clock of a code**: `fD · T` from `B` to `B'`. -/
def CodeOKP (c : Code) (B B' : Fin 200 → ℕ) (T : ℕ) : Prop :=
  FXa wD TD σv (compile c) (PB B) (PB B') (fD * T)

theorem codeOKP_mono {c : Code} {A B B' A' : Fin 200 → ℕ} {T T' : ℕ} (h : CodeOKP c B B' T)
    (h0 : A ≤ B) (h1 : B' ≤ A') (hT : T ≤ T') : CodeOKP c A A' T' :=
  h.mono (fun _ hL => hL.mono h0) (fun _ hL => hL.mono h1) (Nat.mul_le_mul_left _ hT)

theorem one_le_timeBoundT : ∀ {k : ℕ} (p : XProg k) (ℓ : Fin k → ℕ), 1 ≤ p.timeBoundT ℓ
  | _, .prog (.prim _), _ => by simp only [XProg.timeBoundT, SigabaNeo.Tape.Prog.timeBoundT]; omega
  | _, .prog (.coin _), _ => by simp only [XProg.timeBoundT, SigabaNeo.Tape.Prog.timeBoundT]; omega
  | _, .prog (.seq p _), ℓ => by
    have := one_le_timeBoundT (.prog p) ℓ
    simp only [XProg.timeBoundT, SigabaNeo.Tape.Prog.timeBoundT] at this ⊢; omega
  | _, .prog (.ifBlank _ _ _), _ => by
    simp only [XProg.timeBoundT, SigabaNeo.Tape.Prog.timeBoundT]; omega
  | _, .prog (.ifBit _ _ _), _ => by
    simp only [XProg.timeBoundT, SigabaNeo.Tape.Prog.timeBoundT]; omega
  | _, .prog (.loop _ _), _ => by simp only [XProg.timeBoundT, SigabaNeo.Tape.Prog.timeBoundT]; omega
  | _, .frame _ q, ℓ => one_le_timeBoundT q _
  | _, .seq p _, ℓ => by have := one_le_timeBoundT p ℓ; simp only [XProg.timeBoundT]; omega
  | _, .ifBlank _ _ _, _ => by simp only [XProg.timeBoundT]; omega
  | _, .ifBit _ _ _, _ => by simp only [XProg.timeBoundT]; omega
  | _, .loop _ _, _ => by simp only [XProg.timeBoundT]; omega

/-- **An instruction**, from its old clock. -/
theorem codeOKP_instr {c : Code} (hc : isCtl c = false) {B B' : Fin 200 → ℕ} {T : ℕ}
    (h : CodeOK (2 ^ 40) (2 ^ 24) (2 ^ 16) c B B' T) : CodeOKP c B B' T := by
  intro L hL
  obtain ⟨-, a2, -, a4⟩ := (fx_instr c hc).2 L hL.1
  obtain ⟨ht, hl⟩ := h (fun j => L (σv j)) hL.2
  refine ⟨hL.1, a2, ⟨a2, fun j => ?_⟩, fun d M hM => (a4 d M hM).trans ?_⟩
  · rw [Lafter_apply_self]; exact hl j
  · have h1 := one_le_timeBoundT (compile c) (fun j => L (σv j))
    have : 4 * ovT wD 256 TD ≤ 4 * ovT wD 256 TD * T := Nat.le_mul_of_pos_right _ (by omega)
    show _ ≤ (1 + 4 * ovT wD 256 TD) * T
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem codeOKP_seq {p q : Code} {B B1 B2 : Fin 200 → ℕ} {T1 T2 : ℕ}
    (h1 : CodeOKP p B B1 T1) (h2 : CodeOKP q B1 B2 T2) : CodeOKP (.seq p q) B B2 (T1 + T2) := by
  have := FXa.seq (by decide) h1 h2
  rw [CodeOKP, Nat.mul_add]
  exact this

theorem codeOKP_ifb (x : Fin 200) {p q : Code} {B B1 B2 B' : Fin 200 → ℕ} {T1 T2 : ℕ}
    (h1 : CodeOKP p B B1 T1) (h2 : CodeOKP q B B2 T2) (hB1 : B1 ≤ B') (hB2 : B2 ≤ B') :
    CodeOKP (.ifb x p q) B B' (max T1 T2 + 1) := by
  refine (FXa.ifBit (i := tWd x) (Pre := PB B) (Post := PB B') (by decide) (fun L hL => ?_)
    (h1.mono (fun _ h => h) (fun _ _ => trivial) le_rfl)
    (h2.mono (fun _ h => h) (fun _ _ => trivial) le_rfl)).mono (fun _ h => h) (fun _ h => h) ?_
  rotate_left
  · have hf := fD_ge.2.2
    have hm : max (fD * T1) (fD * T2) ≤ fD * max T1 T2 :=
      max_le (Nat.mul_le_mul_left _ (le_max_left _ _)) (Nat.mul_le_mul_left _ (le_max_right _ _))
    have he : fD * (max T1 T2 + 1) = fD * max T1 T2 + fD := by ring
    show _ ≤ fD * (max T1 T2 + 1)
    rw [he]
    omega
  · obtain ⟨-, a2, a3, -⟩ := h1 L hL
    obtain ⟨-, b2, b3, -⟩ := h2 L hL
    have e : ∀ t, Lafter σv (.ifBit (tWd x) (compile p) (compile q)) L t =
        max (Lafter σv (compile p) L t) (Lafter σv (compile q) L t) := Lafter_ifBit _ _ _ _ _
    refine ⟨fun t => by rw [e]; exact max_le (a2 t) (b2 t), fun t => by rw [e]; exact max_le (a2 t) (b2 t),
      fun j => ?_⟩
    rw [e]
    exact max_le ((a3.2 j).trans (SigabaNeo.Tape.RingVM.Flow.encB_mono _ _ _ hB1 j))
      ((b3.2 j).trans (SigabaNeo.Tape.RingVM.Flow.encB_mono _ _ _ hB2 j))

/-- **A loop**, analysed at the invariant `X`. -/
theorem codeOKP_rep (t : Fin 200) {b : Code} {B X Y : Fin 200 → ℕ} {Tb : ℕ} (R : ℕ)
    (hb : CodeOKP b X Y Tb) (hBX : B ≤ X) (hYX : Y ≤ X) :
    CodeOKP (.rep t b) B X (X t * (R + Tb + 1) + 2) := by
  set g := gX σv (tWd t) (compile b)
  have hstep : ∀ L, PB X L → PB X (g L) := fun L hL => by
    have hT : PB X (tailB (σv (tWd t)) L) :=
      ⟨fun u => (tailB_le _ _ u).trans (hL.1 u), fun j => (tailB_le _ _ _).trans (hL.2 j)⟩
    exact ((hb _ hT).2.2.1).mono hYX
  have hiter : ∀ L, PB X L → ∀ m, PB X (g^[m] L) := fun L hL m => by
    induction m with
    | zero => exact hL
    | succ m ih => rw [Function.iterate_succ_apply']; exact hstep _ ih
  have hinv : ∀ L, PB X L → PB X (Lafter σv (.loop (tWd t) (compile b)) L) := fun L hL => by
    rw [← iterSupT_gX]
    exact ⟨fun u => Finset.sup_le fun m _ => (hiter L hL m).1 u,
      fun j => Finset.sup_le fun m _ => (hiter L hL m).2 j⟩
  have h := FXa.loop (Pre := PB B) (Post := PB X) (c := X t) (by decide)
    (fun L hL => (hL.2 (tWd t)).trans (by rw [encB_tWd]; exact hBX t))
    (fun L hL => have h' := hinv L (hL.mono hBX); ⟨hL.1, h'.1, h', h'⟩) hb
  refine h.mono (fun _ h => h) (fun _ h => h) ?_
  obtain ⟨h1, h2, -⟩ := fD_ge
  have hm : X t * (loopOv (256 * (2 * TD + 1)) TD + fD * Tb) ≤ X t * (fD * (R + Tb + 1)) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  calc (6 * (256 * (2 * TD + 1)) + 16) + (X t * (loopOv (256 * (2 * TD + 1)) TD + fD * Tb) + 2)
      ≤ X t * (fD * (R + Tb + 1)) + 2 * fD := by omega
    _ = fD * (X t * (R + Tb + 1) + 2) := by ring

/-! ### Soundness of the abstract run -/

/-- **Soundness of the abstract run of `DecT` for the packed clock.** -/
theorem absRun_soundP : ∀ (c : Code) (B B' T : ℕ), absRun dtP 8 c B = some (B', T) →
    CodeOKP c (toB B) (toB B') T := by
  intro c
  induction c
  case seq p q ihp ihq =>
    intro B B' T h
    simp only [absRun] at h
    rcases hp : absRun dtP 8 p B with _ | ⟨B1, T1⟩
    · simp [hp] at h
    rcases hq : absRun dtP 8 q B1 with _ | ⟨B2, T2⟩
    · simp [hp, hq] at h
    simp only [hp, hq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOKP_seq (ihp B B1 T1 hp) (ihq B1 B2 T2 hq)
  case ifb x p q ihp ihq =>
    intro B B' T h
    simp only [absRun] at h
    rcases hp : absRun dtP 8 p B with _ | ⟨B1, T1⟩ <;>
      rcases hq : absRun dtP 8 q B with _ | ⟨B2, T2⟩ <;> simp [hp, hq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOKP_ifb x (ihp B B1 T1 hp) (ihq B B2 T2 hq)
      (fun y => by rw [SigabaNeo.Tape.RingVM.Flow.toB_bmax]; exact le_max_left _ _)
      (fun y => by rw [SigabaNeo.Tape.RingVM.Flow.toB_bmax]; exact le_max_right _ _)
  case rep t b ih =>
    intro B B' T h
    simp only [absRun] at h
    rcases hl : loopFix (absRun dtP 8 b) 8 B with _ | ⟨X, Tb⟩
    · simp [hl] at h
    simp only [hl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hBX, Y, hY, hYX⟩ := SigabaNeo.Tape.RingVM.Flow.loopFix_spec _ 8 B X Tb hl
    have := codeOKP_rep t (2 * max dtP.Mo (lmax X) + 3) (ih X Y Tb hY) hBX
      (SigabaNeo.Tape.RingVM.Flow.toB_le_of_ble hYX)
    exact this
  all_goals exact fun B B' T h =>
    codeOKP_instr rfl (SigabaNeo.Tape.RingVM.Flow.absRun_sound dtP_valid 8 _ B B' T h)

/-- **A checked block.** -/
theorem dtChk_okP {c : Code} {Bin Bout T : ℕ} (h : dtChk dtP c Bin Bout T = true) :
    CodeOKP c (toB Bin) (toB Bout) T := by
  unfold dtChk at h
  rcases hr : absRun dtP 8 c Bin with _ | ⟨B', T'⟩
  · rw [hr] at h; simp at h
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  exact codeOKP_mono (absRun_soundP c Bin B' T' hr) le_rfl (SigabaNeo.Tape.RingVM.Flow.toB_le_of_ble h.1)
    (Nat.le_of_ble_eq_true h.2)

theorem codeOKP_nop (B : Fin 200 → ℕ) : CodeOKP .nop B B 3 :=
  codeOKP_instr rfl (codeOK_nopT _ _ _ _)

/-! ### The code of `Dec` -/

/-- The packed clock at packed bound vectors. -/
abbrev DOKP (c : Code) (B B' T : ℕ) : Prop := CodeOKP c (toB B) (toB B') T

theorem dtP_stepF (i : ℕ) (hi : i < 16) : DOKP (stepC i false) dtBs dtBs dtTstepF := by
  show DOKP (.seq (mulC i) (.seq (tblC i) (.seq (lutC false) (.seq (.cp 177 162)
    (.seq (.cp 176 163) .nop))))) dtBs dtBs dtTstepF
  exact codeOKP_seq (dtChk_okP (dtChk_mul i hi)) (codeOKP_seq (dtChk_okP (dtChk_tbl i hi))
    (codeOKP_seq (dtChk_okP dtChk_lutF) (dtChk_okP dtChk_tailF)))

theorem dtP_stepT : DOKP (stepC 15 true) dtBs dtBs dtTstepT := by
  show DOKP (.seq (mulC 15) (.seq (tblC 15) (.seq (lutC true) (.seq (.cp 177 162)
    (.seq (.cp 176 163) .nop))))) dtBs dtBs dtTstepT
  exact codeOKP_seq (dtChk_okP (dtChk_mul 15 (by decide))) (codeOKP_seq
    (dtChk_okP (dtChk_tbl 15 (by decide))) (codeOKP_seq (dtChk_okP dtChk_lutT)
      (dtChk_okP dtChk_tailT)))

theorem dtP_stepsN : ∀ n, n ≤ 15 → DOKP (stepsN n) dtBs dtBs (3 + n * dtTstepF)
  | 0, _ => codeOKP_mono (codeOKP_nop _) le_rfl le_rfl (by simp)
  | n + 1, h => by
    have hd : decide (n = 15) = false := decide_eq_false (by omega)
    show DOKP (.seq (stepsN n) (stepC n (decide (n = 15)))) dtBs dtBs _
    rw [hd]
    exact codeOKP_mono (codeOKP_seq (dtP_stepsN n (by omega)) (dtP_stepF n (by omega))) le_rfl
      le_rfl (by rw [Nat.succ_mul]; omega)

theorem dtP_steps16 : DOKP (stepsN 16) dtBs dtBs (3 + 15 * dtTstepF + dtTstepT) :=
  codeOKP_seq (dtP_stepsN 15 le_rfl) dtP_stepT

/-- **The compiled `Dec` code, packed.** -/
theorem dtP_decCode : DOKP decCode dtB0 dtBend dtTvm := by
  have hdev : DOKP devalC dtB3 dtBs (dtTc1 + (dtTc2 + ((3 + 15 * dtTstepF + dtTstepT) + 3))) := by
    show DOKP (.seq (.cp 177 61) (.seq (.cp 176 71) (.seq (stepsN 16) .nop))) dtB3 dtBs _
    exact codeOKP_seq (dtChk_okP dtChk_c1) (codeOKP_seq (dtChk_okP dtChk_c2)
      (codeOKP_seq dtP_steps16 (codeOKP_nop _)))
  show DOKP (.seq splitSkC (.seq splitCtC (.seq fixC (.seq devalC finC)))) dtB0 dtBend dtTvm
  exact codeOKP_seq (dtChk_okP dtChk_S1) (codeOKP_seq (dtChk_okP dtChk_S2)
    (codeOKP_seq (dtChk_okP dtChk_F) (codeOKP_seq hdev (dtChk_okP dtChk_fin))))

end AdvancedEncryption.ExpLUT.Prog.TapeDec
