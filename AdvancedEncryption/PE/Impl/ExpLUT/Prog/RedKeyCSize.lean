import PE.Impl.ExpLUT.Prog.RedKeyC3Glue
import PE.Impl.ExpLUT.Prog.KeyPrepareSize
open SigabaNeo.Tape.RingVM.Handler
/-!
# The state count of `mid` (`≤ 2^190`), modulo the weights of the M3/M4 codes

* `cs_ringIOS_le`: the stash handler costs `≤ 12000` states more than `ringIO1`;
* `cs_m1P : m1P.size ≤ 2^32`; `cs_enter : midEnter.size ≤ 2^53` (the literal templates);
* `cs_m2C : codeWeight m2C ≤ 2^104` (F3's linear `natC` weights are enough);
* **`cs_mid`**: `codeWeight pk ≤ 2^160` and `codeWeight (simKeyC Dc) + codeWeight (setXC Dc) +
  codeWeight simXC ≤ 2^160` imply `(mid pk).size ≤ 2^190`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 2000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.RedKeyM
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid SigabaNeo.Tape.RingVM.Handler
open AdvancedEncryption.ExpLUT.Params
open scoped SigabaNeo.Tape.Prog

theorem cs_parkP : parkP.size ≤ 1000 := by decide
theorem cs_unparkP : unparkP.size ≤ 1000 := by decide

theorem cs_postS (ro : Fin 200) : (postS ro).size ≤ 10000 := by
  show (Prog.cp _ _).size + (clrL _).size ≤ _
  rw [RedChal.size_clrL]
  have : postTapesS.length ≤ 247 := (List.length_filter_le _ _).trans (by simp)
  have h : (Prog.cp (0 : Fin 247) (tWd ro)).size = 36 := rfl
  omega

/-- The stash handler costs at most `12000` states more than `ringIO1`. -/
theorem cs_ringIOS_le (N K : ℕ) (ra rb ro r1 : Fin 200) (tm : Fin 200 → ℕ) (c : RingVM.Code) :
    (ringIOS N K ra rb ro r1 tm c).size ≤ (ringIO1 N K ra rb ro r1 tm c).size + 12000 := by
  simp only [ringIOS, ringIO1, XProg.size_seq, XProg.size_prog]
  have h8 := cs_parkP
  have h9 := cs_unparkP
  have h10 := cs_postS ro
  omega

set_option exponentiation.threshold 2000 in
theorem cs_chalP : (RedChal.chalP Dc).size ≤ 2 ^ 30 := by
  have hb := RedChal.tmBase_Dc_le
  have hle := RedChal.size_chalP Dc 111 (by rw [RedChal.Dc_K]; norm_num)
    (by rw [RedChal.Dc_N]; norm_num)
    (by rw [RedChal.Dc_K, RedChal.Dc_N]; norm_num) (fun r => lt_of_le_of_lt
      (RedChal.tm_le_Bf Dc (Mo := 2 ^ 40) (Bc := 2 ^ 56) (Mb := 2 ^ 110)
        (by rw [RedChal.Dc_N]; norm_num) (by norm_num) RedChal.ctr_Dc RedChal.tmBase_Dc_le r
        |>.trans (RedChal.Bf_le (by norm_num) (by norm_num) r)) (by norm_num))
  rw [RedChal.Dc_b] at hle
  exact hle.trans (by norm_num)

theorem cs_pubS : (ringIOS Dc.N Dc.K RedPubP.ra RedPubP.rb RedPubP.rOut RedPubP.r1
    (RedPubP.tm Dc) (RedPubP.pubC Dc)).size ≤ 2 ^ 30 + 12000 := by
  have e : RedPubP.pubP Dc = ringIO1 Dc.N Dc.K RedPubP.ra RedPubP.rb RedPubP.rOut RedPubP.r1
    (RedPubP.tm Dc) (RedPubP.pubC Dc) := rfl
  have h := RedKeyT.size_pubP_Dc_T
  rw [e] at h
  exact (cs_ringIOS_le _ _ _ _ _ _ _ _).trans (Nat.add_le_add_right h _)

theorem cs_chalS : (ringIOS Dc.N Dc.K RedChal.ra RedChal.rb SigabaNeo.Tape.RingVM.Hash.xOut RedChal.r1
    (RedChal.tm Dc) (RedChal.chalC Dc)).size ≤ 2 ^ 30 + 12000 := by
  have e : RedChal.chalP Dc = ringIO1 Dc.N Dc.K RedChal.ra RedChal.rb SigabaNeo.Tape.RingVM.Hash.xOut RedChal.r1
    (RedChal.tm Dc) (RedChal.chalC Dc) := rfl
  have h := cs_chalP
  rw [e] at h
  exact (cs_ringIOS_le _ _ _ _ _ _ _ _).trans (Nat.add_le_add_right h _)

theorem cs_m1_gen (P C : XProg 247) :
    (XProg.seq (.prog m1InP) (.seq P (.seq (.prog m1MidP) (.seq C (.prog m1OutP))))).size =
      312 + P.size + C.size := by
  simp only [XProg.size_seq, XProg.size_prog]
  have hi : m1InP.size = 108 := rfl
  have hm : m1MidP.size = 132 := rfl
  have ho : m1OutP.size = 72 := rfl
  omega

theorem cs_m1P : m1P.size ≤ 2 ^ 32 := by
  have e := cs_m1_gen (ringIOS Dc.N Dc.K RedPubP.ra RedPubP.rb RedPubP.rOut RedPubP.r1
    (RedPubP.tm Dc) (RedPubP.pubC Dc)) (ringIOS Dc.N Dc.K RedChal.ra RedChal.rb SigabaNeo.Tape.RingVM.Hash.xOut
    RedChal.r1 (RedChal.tm Dc) (RedChal.chalC Dc))
  have hn : 312 + (2 ^ 30 + 12000) + (2 ^ 30 + 12000) ≤ 2 ^ 32 := by norm_num
  exact (e.trans_le (Nat.add_le_add (Nat.add_le_add_left cs_pubS _) cs_chalS)).trans hn

/-- The register-free template store has words of at most `N K` bits. -/
theorem cs_blank_len (N K : ℕ) (t : Fin 105) :
    (MVM.enc N K (fun _ ↦ List.replicate 0 false) t).length ≤
      N * K + N + K := by
  simp only [MVM.enc, MVM.encX]
  split_ifs <;> simp <;> omega

theorem cs_enter_gen (N K : ℕ) :
    (XProg.frame rkE (.prog (MVM.IO.pre N K (fun _ => 0)))).size ≤
      72 + (36 + 105 * (36 + 60 * (N * K + N + K))) := by
  have hp := MVM.IO.size_setList_le
    (MVM.enc N K (fun _ ↦ List.replicate 0 false))
    MVM.IO.preTapes (N * K + N + K) (fun t _ ↦ cs_blank_len N K t)
  have lp : MVM.IO.preTapes.length ≤ 105 :=
    (List.length_filter_le _ _).trans_eq List.length_finRange
  have hp' := Nat.mul_le_mul_right (36 + 60 * (N * K + N + K)) lp
  simp only [XProg.size_frame, XProg.size_prog, MVM.IO.pre, Prog.size_seq]
  have c1 : Prog.size (Prog.cp (41 : Fin 105) 0) = 36 := rfl
  have c2 : Prog.size (Prog.cp (42 : Fin 105) 1) = 36 := rfl
  omega

theorem cs_enter : midEnter.size ≤ 2 ^ 53 := by
  refine (cs_enter_gen Dc.N Dc.K).trans ?_
  rw [c3N, c3K]
  norm_num

theorem cs_onM (c : MVM.Code) : (onM c).size ≤ 100000 * codeWeight c :=
  size_compile_weight c

theorem cs_cw_seq (p q : MVM.Code) : codeWeight (.seq p q) = codeWeight p + codeWeight q := rfl

theorem cs_evalInitWeight :
    ((evalInitOps Dc).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 95 := by
  rw [evalInitWeight_eq]
  norm_num [Dc, Kc, gD, SigabaNeo.Lattices.gGen, tlK]

theorem cs_natT : codeWeight (MVM.natC 6 rB1 RedKeyMid.nT) ≤ 3 * 2 ^ 98 + 1 := by
  have h1 := weight_natC 6 rB1 RedKeyMid.nT
  have hn : RedKeyMid.nT ≤ 2 ^ 98 := c2_codec.2
  exact h1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _)

theorem cs_prep_gen (D : Dims) (A B C : ℕ) (hp : codecSize (mpkEnc D) ≤ A)
    (ht : codecSize (matE D (Wb D) (Fin D.K)) ≤ B)
    (hw : ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum ≤ C) :
    codeWeight (keyPrepareC D) ≤ 18 * A + 3 * B + C + 2 ^ 20 + 49 := by
  refine (weight_keyPrepareC D).trans ?_
  unfold keyPrepareBudget
  omega

theorem cs_prep : codeWeight (keyPrepareC Dc) ≤ 18 * 2 ^ 98 + 3 * 2 ^ 98 + 2 ^ 95 + 2 ^ 20 + 49 :=
  cs_prep_gen Dc _ _ _ c2_codec.1 c2_codec.2 cs_evalInitWeight

theorem cs_m2C_gen (n : ℕ) (k : MVM.Code) :
    codeWeight (.seq (MVM.natC 6 rB1 n) (.seq (.cp 0 2) (.seq (.app 0 6) k))) ≤
      3 * n + 1 + (1 + (1 + codeWeight k)) := by
  have h := weight_natC 6 rB1 n
  simp only [codeWeight]
  omega

theorem cs_m2C : codeWeight m2C ≤ 2 ^ 104 := by
  have h4 : 3 * 2 ^ 98 + 1 + (1 + (1 + (18 * 2 ^ 98 + 3 * 2 ^ 98 + 2 ^ 95 + 2 ^ 20 + 49))) ≤
      2 ^ 104 := by norm_num
  have hn : RedKeyMid.nT ≤ 2 ^ 98 := c2_codec.2
  exact ((cs_m2C_gen RedKeyMid.nT (keyPrepareC Dc)).trans (Nat.add_le_add
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _)
    (Nat.add_le_add_left (Nat.add_le_add_left cs_prep _) _))).trans h4

theorem cs_small : (XProg.prog midLdM2).size + (XProg.prog midStA).size +
    (XProg.prog midLdPk).size + (XProg.prog midLd14).size + (XProg.prog midFin).size ≤ 10000 := by
  simp [midLdM2, midStA, midLdPk, midLd14, midFin, Prog.size, Prim.pad]

theorem cs_seq13 (a b c d e f g h i j k l m : XProg 247) :
    (XProg.seq a (.seq b (.seq c (.seq d (.seq e (.seq f (.seq g (.seq h (.seq i (.seq j
      (.seq k (.seq l m)))))))))))).size =
      a.size + (b.size + (c.size + (d.size + (e.size + (f.size + (g.size + (h.size + (i.size +
        (j.size + (k.size + (l.size + m.size))))))))))) := by
  simp only [XProg.size_seq]

theorem cs_sum (a b c d e f g h i j k l m : ℕ) (ha : a ≤ 2 ^ 32) (hb : b ≤ 2 ^ 53)
    (hc : c + e + g + j + m ≤ 10000) (hd : d ≤ 100000 * 2 ^ 104) (hf : f ≤ 2 ^ 53)
    (hh : h ≤ 100000 * 2 ^ 160) (hikl : i + k + l ≤ 100000 * 2 ^ 160) :
    a + (b + (c + (d + (e + (f + (g + (h + (i + (j + (k + (l + m))))))))))) ≤ 2 ^ 190 := by
  have : (2 : ℕ) ^ 32 + 2 ^ 53 + 2 ^ 53 + 100000 * 2 ^ 104 + 100000 * 2 ^ 160 +
      100000 * 2 ^ 160 + 10000 ≤ 2 ^ 190 := by norm_num
  generalize (2 : ℕ) ^ 190 = Z at this ⊢
  generalize (2 : ℕ) ^ 160 = W at this hh hikl
  generalize (2 : ℕ) ^ 104 = V at this hd
  generalize (2 : ℕ) ^ 53 = U at this hb hf
  generalize (2 : ℕ) ^ 32 = S at this ha
  omega

/-- **The state count of `mid`**, from weight bounds of the M3/M4 codes. -/
theorem cs_mid (pk : MVM.Code) (hpk : codeWeight pk ≤ 2 ^ 160)
    (h4 : codeWeight (simKeyC Dc) + codeWeight (setXC Dc) + codeWeight simXC ≤ 2 ^ 160) :
    (mid pk).size ≤ 2 ^ 190 := by
  have e5 := cs_onM (simKeyC Dc)
  have e6 := cs_onM (setXC Dc)
  have e7 := cs_onM simXC
  have e9 : (onM (simKeyC Dc)).size + (onM (setXC Dc)).size + (onM simXC).size ≤
      100000 * 2 ^ 160 := by
    refine le_trans ?_ (Nat.mul_le_mul_left _ h4)
    rw [Nat.mul_add, Nat.mul_add]
    exact Nat.add_le_add (Nat.add_le_add e5 e6) e7
  have e8 := cs_small
  show (XProg.seq m1P (.seq midEnter (.seq (.prog midLdM2) (.seq (onM m2C) (.seq (.prog midStA)
    (.seq midEnter (.seq (.prog midLdPk) (.seq (onM pk) (.seq (onM (simKeyC Dc))
    (.seq (.prog midLd14) (.seq (onM (setXC Dc)) (.seq (onM simXC) (.prog midFin))))))))))))).size ≤ _
  rw [cs_seq13]
  exact cs_sum _ _ _ _ _ _ _ _ _ _ _ _ _ cs_m1P cs_enter e8
    ((cs_onM m2C).trans (Nat.mul_le_mul_left _ cs_m2C)) cs_enter
    ((cs_onM pk).trans (Nat.mul_le_mul_left _ hpk)) e9

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
