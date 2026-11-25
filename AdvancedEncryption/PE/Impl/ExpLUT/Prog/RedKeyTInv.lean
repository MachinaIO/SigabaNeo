import PE.Impl.ExpLUT.Prog.RedKeyTGuard
import PE.Impl.ExpLUT.SubmissionAssembly

/-!
# Module 9: the input bound, `pubP` and the invalid/long branches of `rkKeyPT`

* **`sigBound_cdR_le`**: `sigBound Sub.cdR (WR Dc) ≤ 2^100` (so the component's input fits
  `io2 (2^101) predLen 0 ≤ gF (2^101) predLen`);
* **`time_pubP_Dc_T`**: `pubP Dc` from `io2 (2^101) 0 0` in at most `2^436` steps (the bound of
  `RedPubP.bounds_pubP` evaluated, instead of the rounded `2^450`);
* **`bounds_rkInvPT`**: from `ℓ ≤ gF (2^101) predLen`, `rkInvPT` ends within `io2 (2^107) 0 0`
  in at most `2^437` steps;
* **`bounds_rkLongP`**: `rkLongP` blanks everything (bound `io2 0 0 0`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic
open AdvancedEncryption.ExpLUT.Prog.RedKeyM AdvancedEncryption.ExpLUT.Prog.RedPubP
open AdvancedEncryption.ExpLUT.Prog.RedChal
open AdvancedEncryption.ExpLUT.Params
open scoped SigabaNeo.Tape.Prog

/-! ### The input bound -/

set_option exponentiation.threshold 2000 in
theorem rawEnc_len_Dc_T : (rawEnc Dc).len ≤ 2 ^ 99 := by
  simp only [FixedEnc.len, rawEnc, FixedEnc.prod, BCol, Wb, Jh, Col, Pos, Dig, PrI, len_sum',
    length_enum_prod, len_fin, instEnc, FixedEnc.comap, floodEnc, zrEnc, attrEnc, rEnc]
  have hr : (circParamsD Dc).rows ≤ 2 ^ 51 := rowsD_Dc_le
  have ht : (setting Dc).τ = Dc.K := rfl
  have hb : (setting Dc).b = Dc.b := rfl
  rw [ht, hb]
  generalize (circParamsD Dc).rows = r at hr
  rw [RedChal.Dc_K, RedChal.Dc_N, RedChal.Dc_b]
  have hmb := RedChal.Dc_mb
  generalize Dc.mb = m at hmb
  norm_num [w8, Width.len]
  nlinarith

set_option exponentiation.threshold 2000 in
theorem WR_Dc_le_T : WR Dc ≤ 2 ^ 93 := by
  have hr := rowsD_Dc_le
  unfold WR
  rw [RedChal.Dc_K, RedChal.Dc_N]
  generalize rowsD Dc = r at hr
  nlinarith

/-- **The input bound of the key component.** -/
theorem sigBound_cdR_le : sigBound Sub.cdR (WR Dc) ≤ 2 ^ 100 := by
  have h1 := rawEnc_len_Dc_T
  have h2 := WR_Dc_le_T
  show sigBound (w8Codes (rawEnc Dc)) (WR Dc) ≤ _
  unfold sigBound stateBound
  have : (w8Codes (rawEnc Dc)).nS = (rawEnc Dc).len := rfl
  have : (w8Codes (rawEnc Dc)).nM = 1 := rfl
  have : (w8Codes (rawEnc Dc)).nA = 128 := rfl
  simp only [*]
  omega

theorem input_le_gF :
    io2 (R := 245) (sigBound Sub.cdR (WR Dc)) predLen 0 ≤ gF (2 ^ 101) predLen := fun t => by
  have := sigBound_cdR_le
  simp only [io2, gF]; split_ifs <;> omega

theorem predLen_le_101 : predLen ≤ 2 ^ 101 := by norm_num [predLen]

/-! ### `pubP` with its evaluated clock bound -/

set_option exponentiation.threshold 2000 in
theorem time_pubP_Dc_T :
    XProg.timeBoundT (pubP Dc) (io2 (R := 245) (2 ^ 101) 0 0) ≤ 2 ^ 436 := by
  have hNK : Dc.N * Dc.K = 2 ^ 40 := by rw [pDc_N, pDc_K]; norm_num
  have hK : Dc.K ≤ 2 ^ 41 := by rw [pDc_K]; norm_num
  have hN : Dc.N ≤ 2 ^ 41 := by rw [pDc_N]; norm_num
  obtain ⟨-, ht⟩ := bounds_pubP Dc (Mo := 2 ^ 41) (Bc := 2 ^ 42) (Mb := 2 ^ 102) (La := 2 ^ 101)
    (Lb := 0) (by rw [hNK]; norm_num) hK hN (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) tm_le_Dc (by rw [hNK]; norm_num)
  refine ht.trans ?_
  rw [show Dc.b = 22 from rfl]
  unfold pIB
  norm_num

/-! ### The invalid branch -/

theorem le_io2_of {ℓ : Fin 247 → ℕ} {a b c : ℕ}
    (h : ∀ t : Fin 247, ℓ t ≤ if t.val = 0 then a else if t.val = 1 then b else c) :
    ℓ ≤ io2 (R := 245) a b c := fun t => by simpa [io2] using h t

set_option exponentiation.threshold 2000 in
/-- **The invalid branch, generic in the public-key program and the key length.** -/
theorem inv_gen (Pp : XProg 247) (n T : ℕ) (hn : n ≤ 2 ^ 106)
    (hPl : XProg.lenBoundT Pp (io2 (R := 245) (2 ^ 101) 0 0) ≤ io2 (R := 245) (2 ^ 102) 0 0)
    (hPt : XProg.timeBoundT Pp (io2 (R := 245) (2 ^ 101) 0 0) ≤ T)
    (ℓ : Fin 247 → ℕ) (hℓ : ℓ ≤ gF (2 ^ 101) predLen) :
    XProg.lenBoundT (.seq (.seq (.prog (clr 1 ⨾ clr 2)) (.seq Pp (.seq (natP 1 2 n)
      (.prog (appT 0 1 2 3 ⨾ clr 1))))) (.prog (clr 2))) ℓ ≤ io2 (R := 245) (2 ^ 102 + n) 0 0 ∧
    XProg.timeBoundT (.seq (.seq (.prog (clr 1 ⨾ clr 2)) (.seq Pp (.seq (natP 1 2 n)
      (.prog (appT 0 1 2 3 ⨾ clr 1))))) (.prog (clr 2))) ℓ ≤ T + 2 ^ 240 := by
  have hℓM : ∀ t, ℓ t ≤ 2 ^ 101 := fun t => (hℓ t).trans (gE_le predLen_le_101 t |>.trans' (gF_le_gE _ _ t))
  -- the two clears
  set ℓ1 := Prog.lenBoundT (clr (1 : Fin 247) ⨾ clr 2) ℓ
  have h1 : ℓ1 ≤ io2 (R := 245) (2 ^ 101) 0 0 := le_io2_of fun t => by
    show Prim.lenT (.clear 2) (Prim.lenT (.clear 1) ℓ) t ≤ _
    simp only [Prim.lenT, Function.update_apply]
    have := hℓ t
    simp only [gF] at this
    split_ifs at this ⊢ <;> first | omega | (subst_vars; simp_all) | simp_all
  have t1 : Prog.timeBoundT (clr (1 : Fin 247) ⨾ clr 2) ℓ ≤ 2 ^ 104 := by
    show 2 * (supB ℓ + 0) + 3 + (2 * (supB (Prim.lenT (.clear 1) ℓ) + 0) + 3) ≤ _
    have a := SigabaNeo.Tape.Prog.supB_le_of hℓM
    have b : supB (Prim.lenT (.clear (1 : Fin 247)) ℓ) ≤ 2 ^ 101 :=
      SigabaNeo.Tape.Prog.supB_le_of fun t => by
        simp only [Prim.lenT, Function.update_apply]; split_ifs
        · exact Nat.zero_le _
        · exact hℓM t
    omega
  -- the public key
  set v : Fin 247 → ℕ := io2 (R := 245) (2 ^ 102) 0 0
  set ℓ2 := XProg.lenBoundT Pp ℓ1
  have h2 : ℓ2 ≤ v := (XProg.lenBoundT_mono Pp h1).trans hPl
  have t2 : XProg.timeBoundT Pp ℓ1 ≤ T := (XProg.timeBoundT_mono Pp h1).trans hPt
  -- the zero key
  have hv : ∀ i, v i ≤ 2 ^ 106 := fun i => by simp only [v, io2]; split_ifs <;> norm_num
  have hnat := natP_bounds (t := (1 : Fin 247)) (c := 2) (by decide) n v (2 ^ 106) hv hn
  set w := natB (1 : Fin 247) 2 n v
  set ℓ3 := XProg.lenBoundT (natP 1 2 n) ℓ2
  have h3 : ℓ3 ≤ w := (XProg.lenBoundT_mono _ h2).trans hnat.1
  have t3 : XProg.timeBoundT (natP 1 2 n) ℓ2 ≤ 2 ^ 216 :=
    (XProg.timeBoundT_mono _ h2).trans (hnat.2.trans (by
      calc (2 * n + 1) * (4 * 2 ^ 106 + 12) ≤ (2 * 2 ^ 106 + 1) * (4 * 2 ^ 106 + 12) := by gcongr
        _ ≤ 2 ^ 216 := by norm_num))
  have hw : ∀ t, w t ≤ 2 ^ 107 := fun t => by
    simp only [w, natB, v, io2]; split_ifs <;> first | omega | norm_num | exact max_le (by norm_num) (by omega)
  have hw01 : w 0 + w 1 ≤ 2 ^ 107 := by simp [w, natB, v, io2]; omega
  have hap := appT_bounds (o := (0 : Fin 247)) (x := 1) (a := 2) (b := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) w hw hw01
  set ℓ4 := Prog.lenBoundT (appT (0 : Fin 247) 1 2 3) w
  have h4 : ∀ t, ℓ4 t ≤ 2 ^ 107 := fun t => (hap.2 t).trans (by
    split_ifs <;> first | exact hw01 | exact hw _ | exact Nat.zero_le _)
  have t4 : Prog.timeBoundT (appT (0 : Fin 247) 1 2 3 ⨾ clr 1) w ≤ 2 ^ 230 := by
    rw [Prog.timeBoundT_seq]
    have a := hap.1
    have b : Prog.timeBoundT (clr (1 : Fin 247)) ℓ4 ≤ 2 ^ 109 := by
      show 2 * (supB ℓ4 + 0) + 3 ≤ _
      have := SigabaNeo.Tape.Prog.supB_le_of h4
      omega
    have c : (4 * w 1 + 6) * (2 * 2 ^ 107 + 5) ≤ 2 ^ 229 := by
      have : w 1 ≤ 2 ^ 107 := hw 1
      calc _ ≤ (4 * 2 ^ 107 + 6) * (2 * 2 ^ 107 + 5) := by gcongr
        _ ≤ 2 ^ 229 := by norm_num
    show Prog.timeBoundT (appT (0 : Fin 247) 1 2 3) w + Prog.timeBoundT (clr (1 : Fin 247)) ℓ4 ≤ _
    omega
  have h5 : Prog.lenBoundT (appT (0 : Fin 247) 1 2 3 ⨾ clr 1) ℓ3 ≤
      Prog.lenBoundT (appT (0 : Fin 247) 1 2 3 ⨾ clr 1) w := Prog.lenBoundT_mono _ h3
  have t5 : Prog.timeBoundT (appT (0 : Fin 247) 1 2 3 ⨾ clr 1) ℓ3 ≤ 2 ^ 230 :=
    (Prog.timeBoundT_mono _ h3).trans t4
  set ℓ5 := Prog.lenBoundT (appT (0 : Fin 247) 1 2 3 ⨾ clr 1) ℓ3
  have h5' : ∀ t, ℓ5 t ≤ 2 ^ 107 := fun t => by
    refine (h5 t).trans ?_
    show Prim.lenT (.clear 1) ℓ4 t ≤ _
    simp only [Prim.lenT, Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact h4 t
  have t6 : Prog.timeBoundT (clr (2 : Fin 247)) ℓ5 ≤ 2 ^ 109 := by
    show 2 * (supB ℓ5 + 0) + 3 ≤ _
    have := SigabaNeo.Tape.Prog.supB_le_of h5'
    omega
  refine ⟨?_, ?_⟩
  · show Prim.lenT (.clear 2) ℓ5 ≤ _
    intro t
    have e5 := h5 t
    simp only [ℓ5] at e5 ⊢
    show Prim.lenT (.clear 2) (Prog.lenBoundT (appT (0 : Fin 247) 1 2 3 ⨾ clr 1) ℓ3) t ≤ _
    simp only [Prim.lenT, Function.update_apply]
    split_ifs with ht2
    · exact Nat.zero_le _
    · refine e5.trans ?_
      show Prim.lenT (.clear 1) ℓ4 t ≤ _
      simp only [Prim.lenT, Function.update_apply]
      split_ifs with ht1
      · exact Nat.zero_le _
      · refine (hap.2 t).trans ?_
        have v1 : t.val ≠ 1 := fun e => ht1 (Fin.ext e)
        have v2 : t.val ≠ 2 := fun e => ht2 (Fin.ext e)
        simp only [w, natB, v, io2]
        split_ifs <;> simp_all <;> omega
  · show Prog.timeBoundT (clr (1 : Fin 247) ⨾ clr 2) ℓ + (XProg.timeBoundT Pp ℓ1 +
      (XProg.timeBoundT (natP 1 2 n) ℓ2 + Prog.timeBoundT (appT (0 : Fin 247) 1 2 3 ⨾ clr 1) ℓ3)) +
      Prog.timeBoundT (clr (2 : Fin 247)) ℓ5 ≤ _
    have : (2 : ℕ) ^ 104 + 2 ^ 216 + 2 ^ 230 + 2 ^ 109 ≤ 2 ^ 240 := by norm_num
    omega

set_option exponentiation.threshold 2000 in
/-- **The invalid branch of `rkKeyPT`.** -/
theorem bounds_rkInvPT (ℓ : Fin 247 → ℕ) (hℓ : ℓ ≤ gF (2 ^ 101) predLen) :
    XProg.lenBoundT rkInvPT ℓ ≤ io2 (R := 245) (2 ^ 107) 0 0 ∧
      XProg.timeBoundT rkInvPT ℓ ≤ 2 ^ 437 := by
  have hk := accept_counts_Dc.2
  unfold rkInvPT rkInvP
  obtain ⟨hl, ht⟩ := inv_gen (pubP Dc) (codecSize (keyEnc Dc)) _ hk len_pubP_Dc time_pubP_Dc_T ℓ hℓ
  refine ⟨hl.trans fun t => ?_, ht.trans (by norm_num)⟩
  simp only [io2]; split_ifs <;> omega

/-- **The long branch** blanks the three io tapes; the others are blank after the tests. -/
theorem bounds_rkLongP (ℓ : Fin 247 → ℕ) (hℓ : ℓ ≤ gF (2 ^ 101) predLen) :
    XProg.lenBoundT (.prog rkLongP) ℓ ≤ io2 (R := 245) 0 0 0 ∧
      XProg.timeBoundT (.prog rkLongP) ℓ ≤ 2 ^ 105 := by
  have hℓM : ∀ t, ℓ t ≤ 2 ^ 101 := fun t =>
    (hℓ t).trans ((gF_le_gE _ _ t).trans (gE_le predLen_le_101 t))
  refine ⟨fun t => ?_, ?_⟩
  · show Prim.lenT (.clear 2) (Prim.lenT (.clear 1) (Prim.lenT (.clear 0) ℓ)) t ≤ _
    simp only [Prim.lenT, Function.update_apply]
    split_ifs with h2 h1 h0 <;> try exact Nat.zero_le _
    have := hℓ t
    have v0 : t.val ≠ 0 := fun e => h0 (Fin.ext e)
    have v1 : t.val ≠ 1 := fun e => h1 (Fin.ext e)
    have v2 : t.val ≠ 2 := fun e => h2 (Fin.ext e)
    simp only [gF] at this
    simp only [io2]
    split_ifs at this ⊢ <;> omega
  · show 2 * (supB ℓ + 0) + 3 + (2 * (supB (Prim.lenT (.clear 0) ℓ) + 0) + 3 +
      (2 * (supB (Prim.lenT (.clear 1) (Prim.lenT (.clear 0) ℓ)) + 0) + 3)) ≤ _
    have hc : ∀ (u : Fin 247) (ℓ' : Fin 247 → ℕ), (∀ t, ℓ' t ≤ 2 ^ 101) →
        ∀ t, Prim.lenT (.clear u) ℓ' t ≤ 2 ^ 101 := fun u ℓ' h t => by
      simp only [Prim.lenT, Function.update_apply]; split_ifs
      · exact Nat.zero_le _
      · exact h t
    have a := SigabaNeo.Tape.Prog.supB_le_of hℓM
    have b := SigabaNeo.Tape.Prog.supB_le_of (hc 0 ℓ hℓM)
    have c := SigabaNeo.Tape.Prog.supB_le_of (hc 1 _ (hc 0 ℓ hℓM))
    omega

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
