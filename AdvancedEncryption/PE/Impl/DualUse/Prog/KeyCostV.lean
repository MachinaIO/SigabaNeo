import PE.Impl.DualUse.Prog.KeyTrySimConf
import PE.Impl.DualUse.Prog.KeySize
import PE.Impl.DualUse.AHConcrete

/-!
# The key component of the reductions at `confA`, per tape

The key component is `keyR sdP = keyPF hkp confP sdP eF (frontBP confP.L) wfR cfP` (`AHConcrete`):
the SimData program, the front end for branching programs, the stream block behind `tailB`
(`wfR`), the simulated key try. Per tape (`time_keyPFV`, `ph_winRest_v`):

* the front end takes at most `2^136` steps on queries of at most `confP.L ≤ 2^49` bits;
* `wfR` takes at most `2^628 + 2^261` steps and leaves only tapes `0`, `2` nonblank, below `2^262`
  (`ph_wfR`, from `time_wfC`, `wfB2S_clear`);
* the simulated key try: its sweeps at `confA` are at most `2^224` (`pEval_wKS_conf`), the tail of
  the window branch at most `2^534` steps (`winRV_confA`);
* **`time_keyR_confV`**: for a SimData program of at most `2^520` steps leaving at most `2^259` bits,
  the key component takes at most **`2^629`** steps and leaves at most `2^263` bits on tape `0`;
* **`size_keyR_conf`**: for a SimData program of at most `2^25` states, at most
  `264 · lenPK + 2^140 ≤ 2^198 + 2^196` states (the prefixes of the public key);
* **`keyRConfA : KeyRConfA`** (`Tk = 629`, `Lk = 263`, `Sk = 2^198 + 2^196`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Algo AdvancedEncryption.DualUse.Algo.Params
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

set_option maxRecDepth 100000
set_option exponentiation.threshold 3000

/-! ### Generic bounds -/

section Gen

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The states of the key component for any front end.** -/
theorem size_keyPF_le (sdP : XProg 82) {R : ℕ} (e : Fin (R + 2) ↪ Fin 256) (fr : XProg (R + 2))
    (wfB : XProg 256) (cf : KeyCfg) (m : ℕ) (hm : ∀ x ∈ keyTmpl hk c cf, x.2 < 2 ^ m) :
    (keyPF hk c sdP e fr wfB cf).size ≤ sdP.size + fr.size + wfB.size +
      264 * lenPK hk c + 60 * (cf.sW.length + (powW K (cf.B - 1)).length +
        ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length) + 20 * (195 * m + 36) + 2 ^ 18 := by
  have h1 := size_prefP (n := 256) (lenPK hk c) 0 1 100 101
  have h2 := size_prefP (n := 256) (lenPK hk c) 0 2 100 101
  have h3 := size_putWX (4 : Fin 256) cf.sW
  have h4 := size_putWX (5 : Fin 256) (powW K (cf.B - 1))
  have h5 := size_putWX (2 : Fin 256) ((keyEnc (N := N) (K := K) c).enc (dummyKey c))
  have h6 := size_tmplP_le (120 : Fin 256) m (keyTmpl hk c cf) hm
  have h7 := size_keyTrySimCoinsP_le
  have h8 := size_clearL_le keyClr
  have h9 := size_clearL_le clrAll
  have h10 := size_clearL_le ([0] : List (Fin 256))
  have hl : (keyTmpl hk c cf).length = 20 := rfl
  have hc : keyClr.length = 25 := rfl
  have hA := length_clrAll_le
  rw [hl] at h6
  rw [hc] at h8
  simp only [keyPF, branchB, winB, dumB, longB, size_seq, size_frame, size_ifBit, size_ifBlank,
    size_prog, Prog.size_prim, Prim.pad] at *
  simp only [List.length_singleton] at h10
  omega

theorem branchTV_le {Tw TR M P D : ℕ} (hP : lenPK hk c ≤ P)
    (hD : ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length ≤ D) :
    branchTV hk c Tw TR M ≤ max ((2 * (M + 1) + 3) + Tw + TR) (max (longT M)
      ((2 * (M + 1) + 3) + prefT P M + putT D (M + 1 + P) +
        (2 * (M + 1 + P + D + 1 + 1) + 3) + (2 * (M + 1 + P + D + 1 + 1 + 1) + 3)) + 1) + 1 := by
  have := dumT_le hk c M hP hD
  unfold branchTV
  omega

theorem branchTV_mono {Tw TR M M' : ℕ} (h : M ≤ M') :
    branchTV hk c Tw TR M ≤ branchTV hk c Tw TR M' := by
  unfold branchTV dumT dumD longT prefT putT
  gcongr

/-- `time_keyPFV` with the final bounds as hypotheses (the front end's output bound a number). -/
theorem time_keyPF_bound {sdP : XProg 82} {a Ts Lsd K₀ : ℕ}
    (hsT : timeBoundT sdP (io2 (R := 80) a 0 0) ≤ Ts)
    (hsL : lenBoundT sdP (io2 (R := 80) a 0 0) ≤ io2 Lsd 0 0)
    {R : ℕ} {e : Fin (R + 2) ↪ Fin 256} (he : FrEmb e) {fr : XProg (R + 2)} {FT : ℕ → ℕ} {FL : ℕ}
    (hfr : ∀ T, Ph fr (io2 (R := R) T 0 0) (FT T) (io2 (R := R) FL 0 0))
    {wfB : XProg 256} {Tw TR GR : ℕ} {βw : Fin 256 → ℕ} (cf : KeyCfg)
    (hwT : timeBoundT wfB (wfIn Lsd FL) ≤ Tw) (hwL : lenBoundT wfB (wfIn Lsd FL) ≤ βw)
    (hR : Ph (winRest hk c cf) βw TR (fun _ => GR)) {B L : ℕ}
    (hB : Ts + FT K₀ + branchTV hk c Tw TR (keyMF hk c Lsd FL cf) +
      clrT (branchLV hk c GR (keyMF hk c Lsd FL cf)) ≤ B)
    (hL : branchLV hk c GR (keyMF hk c Lsd FL cf) ≤ L) :
    timeBoundT (keyPF hk c sdP e fr wfB cf) (io2 (R := 254) a K₀ 0) ≤ B ∧
      lenBoundT (keyPF hk c sdP e fr wfB cf) (io2 (R := 254) a K₀ 0) ≤ io2 L 0 0 := by
  obtain ⟨ht, hl⟩ := time_keyPFV hk c hsT hsL he (FL := fun _ => FL) hfr cf K₀ hwT hwL hR
  refine ⟨ht.trans hB, hl.trans fun i => ?_⟩
  simp only [io2]
  split_ifs
  · exact hL
  · exact le_rfl
  · exact le_rfl

theorem branchLV_le {GR M G' M' P D : ℕ} (hG : GR ≤ G') (hM : M ≤ M') (hP : lenPK hk c ≤ P)
    (hD : ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length ≤ D) :
    branchLV hk c GR M ≤ max G' (max M' (M' + 1 + P + D + 1 + 1)) := by
  unfold branchLV dumD
  omega

end Gen

/-! ### The block `wfR` at `confA` -/

/-- **`wfR` per tape**: the bit dropped, the stream block; only tapes `0`, `2` nonblank. -/
theorem ph_wfR {L F : ℕ} (hL : L ≤ 2 ^ 260) (hF : F ≤ 2 ^ 64) :
    Ph wfR (io2 (R := 254) L F 0) ((2 * (L + F + 1) + 3) + 2 ^ 628) (v02 (2 ^ 262)) := by
  have p1 := ph_prim (k := 256) (Prim.tail 1) (io2 (R := 254) L F 0)
  have hs : supB (io2 (R := 254) L F 0) ≤ L + F :=
    supB_le_of fun i => by simp only [io2]; split_ifs <;> omega
  have hin : (Prim.tail (1 : Fin 256)).lenT (io2 (R := 254) L F 0) ≤ io2 (R := 254) L F 0 :=
    fun t => by simp only [Prim.lenT, Function.update_apply]; split_ifs with h <;> [subst h; skip] <;> omega
  have p2 : Ph Sub.wfC ((Prim.tail (1 : Fin 256)).lenT (io2 (R := 254) L F 0)) (2 ^ 628)
      (v02 (2 ^ 262)) := fun ℓ hℓ => by
    have hℓ' := hℓ.trans hin
    obtain ⟨t1, t2⟩ := time_wfC hL hF
    refine ⟨(timeBoundT_mono _ hℓ').trans t1, fun t => ?_⟩
    simp only [v02]
    split_ifs with h
    · exact (lenBoundT_mono _ hℓ' t).trans (t2 t)
    · push Not at h
      rw [wfB2S_clear hkp confP _ _ ℓ t h.1 h.2]
  exact (p1.seq p2).mono le_rfl (by omega) le_rfl

/-! ### The tail of the window branch at `confA` -/

theorem simTop_conf : simTop hkp confP (2 ^ 262) ≤ 2 ^ 263 := by
  simp only [simTop]; rw [lenPK_eq]; norm_num

theorem simTop_ge : 2 ^ 262 ≤ simTop hkp confP (2 ^ 262) := by simp only [simTop]; omega

theorem winRV_num : prefT (2 ^ 191) (2 ^ 262) + (2 ^ 26 + 1) * (2 * (2 ^ 263 + 2 ^ 26 + 1) + 3) +
    (2 ^ 26 + 1) * (2 * (2 ^ 263 + 2 ^ 26 + 1) + 3) + 21 * ((2 * 2 ^ 263 + 1) * (4 * 2 ^ 263 + 12)) +
    (coinT (2 ^ 263) (2 ^ 130) + (2 * 2 ^ 263 + 3) * 2 ^ 224) +
    (25 * (2 * (2 ^ 263 + 1) + 3) + (2 * (2 ^ 263 + 1) + 3)) ≤ 2 ^ 534 := by
  simp only [prefT, coinT]; norm_num

/-- **The tail of the window branch at `confA`, per tape.** -/
theorem winRV_confA : winRV hkp confP (2 ^ 262) cfP (2 ^ 224) ≤ 2 ^ 534 :=
  (winRV_le hkp confP _ cfP _ Prog.lenPK_le simTop_conf (le_of_eq length_sW_cfP)
    (le_of_eq length_powW_cfP) mBp_le).trans winRV_num

theorem tmpl_simTop : ∀ x ∈ keyTmpl hkp confP cfP, x.2 ≤ simTop hkp confP (2 ^ 262) := fun x hx =>
  ((le_tmplMax _ x hx).trans tmplMax_conf).trans ((by norm_num : (2 : ℕ) ^ 192 ≤ 2 ^ 262).trans simTop_ge)

/-- **`winRest` at `confA`, per tape**, from `v02 (2^262)`. -/
theorem ph_winRest_conf :
    Ph (winRest hkp confP cfP) (v02 (2 ^ 262)) (2 ^ 534) (fun _ => simTop hkp confP (2 ^ 262)) :=
  (ph_winRest_v hkp confP (2 ^ 262) cfP pEval_wKS_conf (le_of_eq (by rw [length_sW_cfP, Kp_def]))
    (le_of_eq (by rw [length_powW_cfP, Kp_def]))
    (Kp_def.le.trans ((by norm_num : (2 : ℕ) ^ 26 ≤ 2 ^ 262).trans simTop_ge)) tmpl_simTop).mono
    le_rfl winRV_confA le_rfl

/-! ### The key component -/

theorem keyMF_conf : keyMF hkp confP (2 ^ 259) (frontBA bpLen) cfP ≤ 2 ^ 259 :=
  max_le (max_le le_rfl (frontBA_conf.trans (by norm_num))) (tmplMax_conf.trans (by norm_num))

theorem frontBTn_confR : frontBTn confP.L bpLen confP.L ≤ 2 ^ 136 :=
  (frontBTn_le (X := 2 ^ 64) le_rfl bpLen_le (Prog.confP_L_le.trans (by norm_num))
    (by have := Prog.confP_L_le; omega) le_rfl).trans (by norm_num)

theorem branchTV_confA :
    branchTV hkp confP ((2 * (2 ^ 259 + 2 ^ 63 + 1) + 3) + 2 ^ 628) (2 ^ 534) (2 ^ 259) ≤
      2 ^ 628 + 2 ^ 535 := by
  refine (branchTV_le hkp confP Prog.lenPK_le lenDummy_le).trans ?_
  simp only [longT, prefT, putT]
  norm_num

theorem branchLV_confA {M : ℕ} (hM : M ≤ 2 ^ 259) :
    branchLV hkp confP (simTop hkp confP (2 ^ 262)) M ≤ 2 ^ 263 :=
  (branchLV_le hkp confP simTop_conf hM Prog.lenPK_le lenDummy_le).trans (by
    refine max_le le_rfl (max_le (by norm_num) ?_)
    have : (2 : ℕ) ^ 191 + 2 ^ 129 + 10 ≤ 2 ^ 259 := by norm_num
    have : (2 : ℕ) ^ 263 = 2 ^ 259 * 16 := by norm_num
    omega)

theorem tw_arith {F : ℕ} (h : F ≤ 2 ^ 63) :
    (2 * (2 ^ 259 + F + 1) + 3) + 2 ^ 628 ≤ (2 * (2 ^ 259 + 2 ^ 63 + 1) + 3) + 2 ^ 628 := by omega

theorem clr_arith {B : ℕ} (h : B ≤ 2 ^ 263) : clrT B ≤ 2 ^ 273 := by
  unfold clrT
  have : 257 * (2 * (2 ^ 263 + 1) + 3) ≤ (2 : ℕ) ^ 273 := by norm_num
  omega

theorem keyR_arith {Ts Ft Bt Cl : ℕ} (hT : Ts ≤ 2 ^ 520) (hF : Ft ≤ 2 ^ 136)
    (hB : Bt ≤ 2 ^ 628 + 2 ^ 535) (hC : Cl ≤ 2 ^ 273) : Ts + Ft + Bt + Cl ≤ 2 ^ 629 := by
  have : (2 : ℕ) ^ 629 = 2 ^ 628 + 2 ^ 628 := by norm_num
  have : (2 : ℕ) ^ 520 + 2 ^ 136 + 2 ^ 535 + 2 ^ 273 ≤ 2 ^ 628 := by norm_num
  omega

/-- The arithmetic of the key component at `confA`. -/
theorem keyR_B :
    2 ^ 520 + frontBTn confP.L bpLen confP.L +
      branchTV hkp confP ((2 * (2 ^ 259 + 2 ^ 63 + 1) + 3) + 2 ^ 628) (2 ^ 534)
        (keyMF hkp confP (2 ^ 259) (frontBA bpLen) cfP) +
      clrT (branchLV hkp confP (simTop hkp confP (2 ^ 262))
        (keyMF hkp confP (2 ^ 259) (frontBA bpLen) cfP)) ≤ 2 ^ 629 :=
  keyR_arith le_rfl frontBTn_confR
    ((branchTV_mono hkp confP keyMF_conf).trans branchTV_confA)
    (clr_arith (branchLV_confA keyMF_conf))

/-- **The time and length bounds of the key component of the reductions at `confA`, per tape.** -/
theorem time_keyR_confV {sdP : XProg 82} {a : ℕ}
    (hsT : timeBoundT sdP (io2 (R := 80) a 0 0) ≤ 2 ^ 520)
    (hsL : lenBoundT sdP (io2 (R := 80) a 0 0) ≤ io2 (2 ^ 259) 0 0) :
    timeBoundT (keyR sdP) (io2 (R := 254) a confP.L 0) ≤ 2 ^ 629 ∧
      lenBoundT (keyR sdP) (io2 (R := 254) a confP.L 0) ≤ io2 (2 ^ 263) 0 0 := by
  have hA := frontBA_conf
  have hw := ph_wfR (L := 2 ^ 259) (F := frontBA bpLen) (by norm_num) (hA.trans (by norm_num))
  have hw' := hw (wfIn (2 ^ 259) (frontBA bpLen)) le_rfl
  have hwT : timeBoundT wfR (wfIn (2 ^ 259) (frontBA bpLen)) ≤
      (2 * (2 ^ 259 + 2 ^ 63 + 1) + 3) + 2 ^ 628 := hw'.1.trans (tw_arith hA)
  have hfr : ∀ T, Ph (frontBP confP.L) (io2 (R := 70) T 0 0) (frontBTn confP.L bpLen T)
      (io2 (R := 70) (frontBA bpLen) 0 0) := fun T => (frontSpec_frontBP confP.L).ph T
  exact time_keyPF_bound hkp confP hsT hsL frEmb_eF hfr cfP hwT hw'.2 ph_winRest_conf keyR_B
    (branchLV_confA keyMF_conf)

/-! ### The states -/

theorem size_wfR : wfR.size ≤ 2 ^ 25 + 100 := by
  have := size_wfC
  simp only [tailB, size_seq, size_prog, Prog.size_prim, Prim.pad]
  omega

theorem ksz_arithR {S F W P s p d : ℕ} (hS : S ≤ 2 ^ 25) (hF : F ≤ 2 ^ 57) (hW : W ≤ 2 ^ 25 + 100)
    (hP : P = 6129982437495116521683020588912456589297838140178825216) (hs : s = 2 ^ 26)
    (hp : p = 2 ^ 26) (hd : d ≤ 2 ^ 129) :
    S + F + W + 264 * P + 60 * (s + p + d) + 20 * (195 * 193 + 36) + 2 ^ 18 ≤ 2 ^ 198 + 2 ^ 196 := by
  subst hP hs hp
  omega

theorem fszR_arith {n F : ℕ} (h : n ≤ 2 ^ 49) (hF : F ≤ 36 * n + 2 ^ 56) : F ≤ 2 ^ 57 := by omega

/-- **The states of the key component of the reductions at `confA`.** -/
theorem size_keyR_conf {sdP : XProg 82} (hsd : sdP.size ≤ 2 ^ 25) :
    (keyR sdP).size ≤ 2 ^ 198 + 2 ^ 196 := by
  have hm : ∀ x ∈ keyTmpl hkp confP cfP, x.2 < 2 ^ 193 := fun x hx =>
    ((le_tmplMax _ x hx).trans tmplMax_conf).trans_lt (by norm_num)
  exact (size_keyPF_le hkp confP sdP eF (frontBP confP.L) wfR cfP 193 hm).trans
    (ksz_arithR hsd (fszR_arith Prog.confP_L_le (frontSpec_frontBP confP.L).size) size_wfR
      lenPK_eq length_sW_cfP length_powW_cfP lenDummy_le)

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse

open Prog

/-- **The cost of the reductions' key component at `confA`** (`Tk = 629`, `Lk = 263`,
`Sk = 2^198 + 2^196`). -/
theorem keyRCost_confA : KeyRCost 520 259 629 263 (2 ^ 198 + 2 ^ 196) where
  time _ hsT hsL := (time_keyR_confV hsT hsL).1
  len _ hsT hsL := (time_keyR_confV hsT hsL).2
  size hsd := size_keyR_conf hsd

/-- **`KeyRConfA`**, the hypothesis of `attributeHiding_conf_rlwe` and of the submission. -/
theorem keyRConfA : KeyRConfA :=
  ⟨629, 263, 2 ^ 198 + 2 ^ 196, keyRCost_confA, by norm_num, by norm_num, le_rfl⟩

end AdvancedEncryption.DualUse
