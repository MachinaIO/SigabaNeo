import PE.Impl.ExpLUT.Prog.RedKeyTInv
import PE.Impl.ExpLUT.Prog.RedKeyMComp
import PE.Impl.ExpLUT.Prog.KeyTimeOutput

/-!
# Module 9 (top): the certificates of `rkKeyPT mid` and the `KeyComp` record

**The hypothesis on the middle phases, `RkMidBound mid a`** (`a : Fin 105 → ℕ`, the per-tape
bounds of the MVM store `mid` hands to the back end):

* `time : XProg.timeBoundT mid rkIn ≤ 2^440`;
* `len : XProg.lenBoundT mid rkIn ≤ rkLiftB a` — tapes `0 … 104` within `a`, **tapes `105 … 246`
  with static bound `0`** (scratch must be cleared *in the static sense*: end with `clr`, a loop's
  counter keeps its bound otherwise);

at the input bound `rkIn = io2 (2^101) predLen 0` (the component's input
`io2 (sigBound cdR (WR Dc)) predLen 0` is below it: `sigBound_cdR_le`).

**The back-end certificate, `RkTailCert a Lt Tt`** := `KeyTime.Cert (rkTailP Dc Bk rSmall) a
(outputBounds Lt) Tt` (F3's certificate form: lengths of `rkTailP` from `a` within `Lt` on tape
`0` and `0` elsewhere, time `≤ Tt`).

* **`bounds_rkKeyPT`**: with `RkMidBound mid a`, `RkTailCert a Lt Tt`, `Tt ≤ 2^449`: the static
  length bound of `rkKeyPT mid` at `io2 (sigBound cdR (WR Dc)) predLen 0` is within
  `io2 (max Lt 2^107) 0 0`, the time within `2^450`;
* **`size_rkKeyPT`**: `mid.size ≤ 2^190`, `(rkTailP Dc Bk rSmall).size ≤ 2^195` ⇒ `≤ 2^200`;
* **`keyCompOfT`**: the `Sub.KeyComp` record (with `Lk = max Lt 2^107`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic
open AdvancedEncryption.ExpLUT.Prog.RedKeyM
open AdvancedEncryption.ExpLUT.Prog.KeyTime (Cert outputBounds)
open AdvancedEncryption.ExpLUT.Params
open scoped SigabaNeo.Tape.Prog

/-- The input bound used for the middle phases. -/
def rkIn : Fin 247 → ℕ := io2 (R := 245) (2 ^ 101) predLen 0

/-- Per-tape bounds `a` on the MVM tapes `0 … 104`, `0` on the others. -/
def rkLiftB (a : Fin 105 → ℕ) : Fin 247 → ℕ := embedF rkE (fun _ => 0) a

/-- **The hypothesis on the middle phases.** -/
structure RkMidBound (mid : XProg 247) (a : Fin 105 → ℕ) : Prop where
  time : XProg.timeBoundT mid rkIn ≤ 2 ^ 440
  len : XProg.lenBoundT mid rkIn ≤ rkLiftB a

/-- **The back-end certificate** (to be supplied for `rkTailP`). -/
def RkTailCert (a : Fin 105 → ℕ) (Lt Tt : ℕ) : Prop :=
  Cert (rkTailP Dc Bk rSmall) a (outputBounds Lt) Tt

theorem rkLiftB_rkE (a : Fin 105 → ℕ) : (rkLiftB a ∘ rkE) = a := by
  funext j
  simp [rkLiftB]

theorem embedF_out_le (a : Fin 105 → ℕ) (Lt : ℕ) :
    embedF rkE (rkLiftB a) (outputBounds Lt) ≤ io2 (R := 245) Lt 0 0 := by
  intro l
  rcases embedF_cases rkE (rkLiftB a) (outputBounds Lt) l with ⟨hl, h⟩ | ⟨j, hj, h⟩
  · rw [h, rkLiftB, embedF, hl]
    exact Nat.zero_le _
  · rw [h, ← hj]
    have hv : (rkE j).val = j.val := by simp [rkE]
    simp only [outputBounds, io2, hv]
    by_cases h0 : j = 0
    · subst h0; simp
    · have : j.val ≠ 0 := fun e => h0 (Fin.ext e)
      simp [h0, this]

theorem io2_mono0 {a b : ℕ} (h : a ≤ b) : io2 (R := 245) a 0 0 ≤ io2 (R := 245) b 0 0 := fun t => by
  simp only [io2]; split_ifs <;> omega

/-! ### The branches as certificates from `gF` -/

abbrev gF0 : Fin 247 → ℕ := gF (2 ^ 101) predLen

theorem supB_gF0 : supB gF0 ≤ 2 ^ 101 :=
  SigabaNeo.Tape.Prog.supB_le_of fun t =>
    (gF_le_gE _ _ t).trans (gE_le predLen_le_101 t)

set_option maxRecDepth 100000 in
theorem cert_clr2 : Cert (.prog (clr 2)) gF0 rkIn (2 ^ 104) := by
  refine ⟨fun t => ?_, ?_⟩
  · show Prim.lenT (.clear 2) gF0 t ≤ _
    simp only [Prim.lenT, Function.update_apply, gF0, gF, rkIn, io2]
    split_ifs <;> omega
  · show 2 * (supB gF0 + 0) + 3 ≤ _
    have := supB_gF0
    omega

theorem cert_valid {mid : XProg 247} {a : Fin 105 → ℕ} {Lt Tt : ℕ} (hm : RkMidBound mid a)
    (ht : RkTailCert a Lt Tt) :
    Cert (.seq (.prog (clr 2)) (rkValidP mid)) gF0 (io2 (R := 245) Lt 0 0)
      (2 ^ 104 + (2 ^ 440 + Tt)) := by
  have cm : Cert mid rkIn (rkLiftB a) (2 ^ 440) := ⟨hm.len, hm.time⟩
  have cf : Cert (.frame rkE (rkTailP Dc Bk rSmall)) (rkLiftB a)
      (embedF rkE (rkLiftB a) (outputBounds Lt)) Tt := by
    apply KeyTime.Cert.frame
    rw [rkLiftB_rkE]
    exact ht
  exact (cert_clr2.seq (cm.seq cf)).mono le_rfl (embedF_out_le a Lt) le_rfl

theorem cert_le : Cert (.prog rkLeChkT) gF0 gF0 ((20 * predLen + 210) * (2 * 2 ^ 101 + 5)) :=
  ⟨(bounds_rkLeChkT predLen_le_101 gF0 le_rfl).2, (bounds_rkLeChkT predLen_le_101 gF0 le_rfl).1⟩

theorem cert_eq :
    Cert (.prog (clr 2 ⨾ rkEqChkT)) gF0 gF0 ((20 * predLen + 210) * (2 * 2 ^ 101 + 5)) :=
  ⟨(bounds_clrEqChkT predLen_le_101 gF0 le_rfl).2, (bounds_clrEqChkT predLen_le_101 gF0 le_rfl).1⟩

theorem cert_inv : Cert rkInvPT gF0 (io2 (R := 245) (2 ^ 107) 0 0) (2 ^ 437) :=
  ⟨(bounds_rkInvPT gF0 le_rfl).1, (bounds_rkInvPT gF0 le_rfl).2⟩

theorem cert_long : Cert (.prog rkLongP) gF0 (io2 (R := 245) 0 0 0) (2 ^ 105) :=
  ⟨(bounds_rkLongP gF0 le_rfl).1, (bounds_rkLongP gF0 le_rfl).2⟩

theorem guard_time_le : (20 * predLen + 210) * (2 * 2 ^ 101 + 5) ≤ 2 ^ 140 := by
  norm_num [predLen]

set_option exponentiation.threshold 2000 in
/-- **The length and clock certificates of `rkKeyPT mid`.** -/
theorem bounds_rkKeyPT {mid : XProg 247} {a : Fin 105 → ℕ} {Lt Tt : ℕ} (hm : RkMidBound mid a)
    (ht : RkTailCert a Lt Tt) (hTt : Tt ≤ 2 ^ 449) :
    XProg.lenBoundT (rkKeyPT mid) (io2 (R := 245) (sigBound Sub.cdR (WR Dc)) predLen 0) ≤
        io2 (R := 245) (max Lt (2 ^ 107)) 0 0 ∧
      XProg.timeBoundT (rkKeyPT mid) (io2 (R := 245) (sigBound Sub.cdR (WR Dc)) predLen 0) ≤
        2 ^ 450 := by
  set B : Fin 247 → ℕ := io2 (R := 245) (max Lt (2 ^ 107)) 0 0
  have cV := (cert_valid hm ht).mono le_rfl (io2_mono0 (le_max_left Lt (2 ^ 107))) le_rfl
  have cI := cert_inv.mono le_rfl (io2_mono0 (le_max_right Lt (2 ^ 107))) le_rfl
  have cZ := cert_long.mono le_rfl (io2_mono0 (Nat.zero_le (max Lt (2 ^ 107)))) le_rfl
  have c := cert_le.seq ((cert_eq.seq (cV.ifBit 2 cI)).ifBit 2 cZ)
  have c' := c.mono input_le_gF le_rfl le_rfl
  refine ⟨c'.len, c'.time.trans ?_⟩
  have g := guard_time_le
  have h1 : max (2 ^ 104 + (2 ^ 440 + Tt)) (2 ^ 437) ≤ 2 ^ 104 + (2 ^ 440 + 2 ^ 449) :=
    max_le (Nat.add_le_add_left (Nat.add_le_add_left hTt _) _) (by norm_num)
  have h2 : max ((20 * predLen + 210) * (2 * 2 ^ 101 + 5) +
      (max (2 ^ 104 + (2 ^ 440 + Tt)) (2 ^ 437) + 1)) (2 ^ 105) ≤
      2 ^ 140 + (2 ^ 104 + (2 ^ 440 + 2 ^ 449) + 1) :=
    max_le (Nat.add_le_add g (Nat.add_le_add_right h1 1)) (by norm_num)
  have h3 : (2 : ℕ) ^ 140 + (2 ^ 140 + (2 ^ 104 + (2 ^ 440 + 2 ^ 449) + 1) + 1) ≤ 2 ^ 450 := by
    norm_num
  exact le_trans (Nat.add_le_add g (Nat.add_le_add_right h2 1)) h3

/-! ### The state count -/

theorem size_rkLenLeP_le (n : ℕ) : Prog.size (rkLenLeP n) ≤ 500 * Nat.log2 n + 2000 := by
  have h1 := size_natU (2 : Fin 6) 4 5 n
  have h2 : Prog.size (cp (3 : Fin 6) 0 ⨾ dropT 3 2 4 ⨾ ifBlank 3 (setB 1 true) (setB 1 false) ⨾
      clr 2 ⨾ clr 3) ≤ 1500 := by decide
  show Prog.size (natU 2 4 5 n) + Prog.size (cp (3 : Fin 6) 0 ⨾ dropT 3 2 4 ⨾
    ifBlank 3 (setB 1 true) (setB 1 false) ⨾ clr 2 ⨾ clr 3) ≤ _
  omega

set_option exponentiation.threshold 2000 in
set_option maxRecDepth 100000 in
theorem size_pubP_Dc_T : (RedPubP.pubP Dc).size ≤ 2 ^ 30 := by
  have hle := RedPubP.size_pubP Dc 103 (by rw [RedPubP.pDc_K]; norm_num)
    (by rw [RedPubP.pDc_N]; norm_num) (by rw [RedPubP.pDc_K, RedPubP.pDc_N]; norm_num)
    (fun r => lt_of_le_of_lt ((RedPubP.tm_le_Dc r).trans (RedPubP.pBf_le (by norm_num)
      (by norm_num) r)) (by norm_num))
  rw [show Dc.b = 22 from rfl] at hle
  exact hle.trans (by norm_num)

theorem size_inv_gen (Pp : XProg 247) (n : ℕ) (hn : n < 2 ^ 107) (hP : Pp.size ≤ 2 ^ 30) :
    (XProg.seq (.seq (.prog (clr 1 ⨾ clr 2)) (.seq Pp (.seq (natP 1 2 n)
      (.prog (appT 0 1 2 3 ⨾ clr 1))))) (.prog (clr 2))).size ≤ 2 ^ 31 := by
  have hn' := XProg.size_natP_le (1 : Fin 247) 2 n 107 hn
  have ha := size_appT_le (0 : Fin 247) 1 2 3
  simp only [XProg.size_seq, XProg.size_prog]
  have e1 : Prog.size (clr (1 : Fin 247) ⨾ clr 2) = 72 := rfl
  have e2 : Prog.size (appT (0 : Fin 247) 1 2 3 ⨾ clr 1) =
    Prog.size (appT (0 : Fin 247) 1 2 3) + 36 := rfl
  have e3 : Prog.size (clr (2 : Fin 247)) = 36 := rfl
  rw [e1, e2, e3]
  linarith

theorem size_rkInvPT : rkInvPT.size ≤ 2 ^ 31 := by
  unfold rkInvPT rkInvP
  exact size_inv_gen _ _ (lt_of_le_of_lt accept_counts_Dc.2 (by norm_num)) size_pubP_Dc_T

set_option maxRecDepth 100000 in
theorem size_rkLeChkT : Prog.size rkLeChkT ≤ 2 ^ 40 := by
  have h := size_rkLenLeP_le predLen
  have hl := Nat.log2_le_self predLen
  show Prog.size (Prog.map rkChkMap (rkLenLeP predLen)) + (36 + 36) ≤ _
  rw [Prog.size_map]
  have : predLen ≤ 2 ^ 30 := by norm_num [predLen]
  omega

set_option maxRecDepth 100000 in
theorem size_clrEqChkT : Prog.size (clr 2 ⨾ rkEqChkT) ≤ 2 ^ 40 := by
  have h := size_lenEqP predLen
  have hl := Nat.log2_le_self predLen
  show 36 + (Prog.size (Prog.map rkChkMap (lenEqP predLen)) + (36 + 36)) ≤ _
  rw [Prog.size_map]
  have : predLen ≤ 2 ^ 30 := by norm_num [predLen]
  omega

set_option exponentiation.threshold 2000 in
theorem size_keyOf_gen (L E Z : SigabaNeo.Tape.Prog 247) (mid I : XProg 247) (T : XProg 105)
    (hL : L.size ≤ 2 ^ 40) (hE : E.size ≤ 2 ^ 40) (hZ : Z.size ≤ 2 ^ 40) (hI : I.size ≤ 2 ^ 31)
    (hm : mid.size ≤ 2 ^ 190) (hT : T.size ≤ 2 ^ 195) :
    (XProg.seq (.prog L) (.ifBit 2 (.seq (.prog E) (.ifBit 2 (.seq (.prog (clr 2))
      (.seq mid (.frame rkE T))) I)) (.prog Z))).size ≤ 2 ^ 200 := by
  simp only [XProg.size_seq, XProg.size_prog, XProg.size_ifBit, XProg.size_frame]
  have e1 : Prog.size (clr (2 : Fin 247)) = 36 := rfl
  rw [e1]
  have : (2 : ℕ) ^ 40 + (2 ^ 40 + (36 + (2 ^ 190 + 2 ^ 195)) + 2 ^ 31 + 1 + 2 ^ 40 + 1) ≤
      2 ^ 200 := by norm_num
  linarith

/-- **The state count of `rkKeyPT mid`.** -/
theorem size_rkKeyPT {mid : XProg 247} (hsm : mid.size ≤ 2 ^ 190)
    (hst : (rkTailP Dc Bk rSmall).size ≤ 2 ^ 195) : (rkKeyPT mid).size ≤ 2 ^ 200 := by
  unfold rkKeyPT rkKeyOfT rkValidP
  exact size_keyOf_gen _ _ _ _ _ _ size_rkLeChkT size_clrEqChkT
    (show Prog.size rkLongP ≤ 2 ^ 40 by rw [show Prog.size rkLongP = 108 from rfl]; norm_num)
    size_rkInvPT hsm hst

/-! ### The record -/

/-- **The `law` field of `KeyComp`** for `rkKeyPT mid`. -/
theorem law_rkKeyPT_spR {mid : XProg 247} (hm : RkMidOk mid) (σ : RawSec Dc) (C : List Bool) :
    XProg.law (rkKeyPT mid) (io2 (R := 245) (Sub.cdR.sig.enc σ) C []) =
      (Sub.spR.key σ C).map fun sk => io2 (R := 245) sk [] [] :=
  law_rkKeyPT hm σ C

/-- **The key component** from the middle phases, their bound hypothesis and the back-end
certificate. -/
noncomputable def keyCompOfT (mid : XProg 247) (hwf : mid.WF) (hm : RkMidOk mid)
    (a : Fin 105 → ℕ) (hb : RkMidBound mid a) (Lt Tt : ℕ) (ht : RkTailCert a Lt Tt)
    (hLt : Lt ≤ 2 ^ 125) (hTt : Tt ≤ 2 ^ 449) (hsm : mid.size ≤ 2 ^ 190)
    (hst : (rkTailP Dc Bk rSmall).size ≤ 2 ^ 195) : Sub.KeyComp where
  keyP := rkKeyPT mid
  wf := wf_rkKeyPT hwf
  law := law_rkKeyPT_spR hm
  Lk := max Lt (2 ^ 107)
  hLk := max_le hLt (by norm_num)
  len := (bounds_rkKeyPT hb ht hTt).1
  time := (bounds_rkKeyPT hb ht hTt).2
  size := size_rkKeyPT hsm hst

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
