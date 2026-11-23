import PE.Impl.DualUse.Prog.WfB2Inst

/-!
# The `W_f` block of `Dec` with per-tape output bounds

`time_wfB2_conf` (`WfB2Conf`) bounds every tape after the block-structured `W_f` block uniformly
by `Mall = 2^250`. The block ends by clearing every tape but the data word (`mw SDW`, tape `0`
outside) and the output (`255`, tape `2` outside), so per tape:

* **`wfB2_out_conf`**: at `confP`, from `io2 Lsd Lg 0` (`Lsd ≤ 2^240`, `Lg ≤ 2^64`), at most
  `2^555 + 2^552` steps (the sum of the same certified parts as `time_wfB2_conf`, whose total is
  `≈ 2^555.1`), and afterwards tape `0` at most `2^240` bits, tape `2` at most `wOut2 ≈ 2^146`
  bits (`d · 2k · N K`), every other tape blank.
-/

namespace AdvancedEncryption.DualUse.Prog

namespace WB2

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST
  SigabaNeo.Tape.Prog.StepT SigabaNeo.Lattices.Algo SigabaNeo.Lattices AdvancedEncryption.DualUse.Params

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

/-- The bound of the output tape of the block. -/
def wOut2 : ℕ := 89202983452578484135974618898207566584610816

/-- The per-tape bounds after the block: the data word on tape `0`, the output on tape `2`. -/
def wOut : Fin 256 → ℕ := fun t => if t = 0 then Lb else if t = 2 then wOut2 else 0

theorem embedF_perm {k : ℕ} (e : Equiv.Perm (Fin k)) (f g : Fin k → ℕ) (t : Fin k) :
    embedF e.toEmbedding f g t = g (e.symm t) := by
  have h : t = e.toEmbedding (e.symm t) := by simp
  conv_lhs => rw [h]
  exact embedF_apply_self _ _ _ _

theorem chk_out : ∀ t, Prog.lenBoundT (clrsP finClr) v6c (swp.symm t) ≤ wOut t := by
  decide +kernel

theorem chk_sum' :
    cntT Wc (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0c) + capT2 Wc (embedF (ValVM.mkE cntE cntE_inj) (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0c) (cntOut Wc (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0c))) +
      (2 * M31c + 3) * simTmplSweeps Nc Kc kc +
      90 * uT (Mall + 6) + (2 ^ 551 + (cntT Wc (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1c) +
      capT2 Wc (embedF (ValVM.mkE cntE cntE_inj) (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1c) (cntOut Wc (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1c))) +
      (2 * M31c + 3) * simTmplSweeps Nc Kc kc + 120 * uT (Mall + 40) + (2 ^ 485 +
      (120 * uT (Mall + 100) + (2 ^ 555 + 256 * (2 * (Mall + 256) + 5)))))) ≤ 2 ^ 555 + 2 ^ 552 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The block with per-tape output bounds** (the proof of `time_wfB2_conf`, keeping the bounds
of the final cleanup per tape). -/
theorem time_wfB2_out {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (hN : N = Nc)
    (hK : K = Kc) (hd : c.d = dc) (hth : treeHeight N (K + 1) ≤ 64)
    (hoB : offB c ≤ Lb) (hoW : offW hk c ≤ Lb) (hoP : offPsi hk c ≤ Lb) (hoR : offR hk c ≤ Lb)
    (hoX : offPsi hk c + 10 * lenPsi N K (K + 1) ≤ Lb) (Lsd Lg : ℕ) (hLsd : Lsd ≤ Lb)
    (hLg : Lg ≤ Lgc) :
    XProg.timeBoundT (wfB2 hk c Wc) (io2 (R := 254) Lsd Lg 0) ≤ 2 ^ 555 + 2 ^ 552 ∧
      XProg.lenBoundT (wfB2 hk c Wc) (io2 (R := 254) Lsd Lg 0) ≤ wOut := by
  subst hN hK
  obtain ⟨s0, s2, s6, s31, sT, s1, s2G, s6G, sG, s4, sK, s6'⟩ := chk_small
  have p1 := ph_prepT hk c Wc β0c M31c (by rw [hd]; exact chk_hinT) (by rw [hd]; exact chk_htopT)
  have hTl : TLe (wordsT Nc Kc (Kc + 1) c.d Wc (offB c) (offW hk c) (offPsi hk c)) wTc := by
    rw [wordsT_eq, hd]; exact TLe_wordsTx _ _ _ _ _ hth hoB hoW hoP
  have g1 : vT hk c Wc β0c M31c ≤ encB (bsT Nc Kc kc dc) (VT Nc Kc kc dc) (gB L0c) :=
    (vT_le hk c Wc β0c M31c wTc hTl).trans (by rw [hd]; exact chk_g1)
  obtain ⟨T1, hr1, hT1⟩ := of_chkR chk_r1
  have p2 := ph_runT Nc Kc kc dc Mall 30 L0c L1c T1 lenL0c chk_V.1 chk_V.2.1 chk_V.2.2.1
    chk_V.2.2.2 hr1
  have p3 := ph_prepG hk c Wc β1c M31c (by rw [hd]; exact chk_hinG) (by rw [hd]; exact chk_htopG)
  have hGl : TLe (wordsG Nc Kc (Kc + 1) c.d Wc (offPsi hk c) (offR hk c)
      (offPsi hk c + 10 * lenPsi Nc Kc (Kc + 1))) wGc := by
    rw [hd]; exact TLe_wordsG _ _ _ _ _ hoP hoR hoX
  have g3 : vG hk c Wc β1c M31c ≤ encB (bsG Nc Kc kc dc) (VG Nc Kc kc dc) (gB L0Gc) :=
    (vG_le hk c Wc β1c M31c wGc hGl).trans (by rw [hd]; exact chk_g3)
  obtain ⟨T2, hr2, hT2⟩ := of_chkR chk_r2
  have p4 := ph_runG Nc Kc kc dc Mall 30 L0Gc L1Gc T2 lenL0Gc chk_VG.1 chk_VG.2.1 chk_VG.2.2.1
    chk_VG.2.2.2 hr2
  have p5 := ph_keyPrep Nc Kc kc dc β4c
  have hkp : keyPrep Nc Kc (Kc + 1) c.d = keyPrep Nc Kc kc dc := by rw [hd]; rfl
  rw [← hkp] at p5
  have p6 := ph_simKey v5c Msk Nc Kc dc kc (nPos Nc kc) (VT Nc Kc kc dc) (lenA Nc Kc kc 1)
    (gB L1Gc FOUT) (gB L1Gc 61) (gB L1Gc OUTW) 1 (VG Nc Kc kc dc) (lenA Nc Kc kc 2) chk_sk.1 chk_sk.2
  have p7 := ph_finClr v6c
  have body := ph_wfBody hk c Wc p1 g1 p2 p3 g3 p4 p5 p6 p7
  have hin : (fun j => io2 (R := 254) Lsd Lg 0 (eW j)) ≤ β0c := fun t => by
    obtain ⟨e0, e1, -, -⟩ := swp_eq t
    show io2 (R := 254) Lsd Lg 0 (swp t) ≤ β0c t
    simp only [io2, β0c, e0, e1]
    split_ifs <;> omega
  obtain ⟨ht, hl⟩ := ph_wfB2 hk c Wc (body.mono hin le_rfl le_rfl) _ le_rfl
  refine ⟨ht.trans ?_, fun t => (hl t).trans ?_⟩
  · have a1 := tT_le hk c Wc β0c M31c Mall s0 s2 (by rw [tmOut_eq, hd]; exact s6)
      (by rw [hd]; exact s31) (TLe_le (TLe_append (TLe_refl _) hTl) (by rw [hd]; exact sT))
    have a3 := tG_le hk c Wc β1c M31c Mall s1 s2G (by rw [tmOut_eq, hd]; exact s6G)
      (by rw [hd]; exact s31) (TLe_le (TLe_append (TLe_refl _) hGl) (by rw [hd]; exact sG))
    have a5 := tK_le Nc Kc kc dc β4c Mall s4 sK
    have a6 := chk_skT
    have a7 := tF_le v6c Mall s6'
    exact (Nat.add_le_add a1 (Nat.add_le_add hT1 (Nat.add_le_add a3 (Nat.add_le_add hT2
      (Nat.add_le_add a5 (Nat.add_le_add a6 a7)))))).trans chk_sum'
  · show embedF swp.toEmbedding _ _ t ≤ _
    rw [embedF_perm]
    exact chk_out t

/-- **The block at `confP` with per-tape output bounds.** -/
theorem wfB2_out_conf (Lsd Lg : ℕ) (hLsd : Lsd ≤ Lb) (hLg : Lg ≤ Lgc) :
    XProg.timeBoundT (wfB2 hkp confP Wc) (io2 (R := 254) Lsd Lg 0) ≤ 2 ^ 555 + 2 ^ 552 ∧
      XProg.lenBoundT (wfB2 hkp confP Wc) (io2 (R := 254) Lsd Lg 0) ≤ wOut := by
  have hth : treeHeight Np (Kp + 1) ≤ 64 := by rw [hN_conf, hK_conf]; exact treeHeight_conf
  obtain ⟨hoB, hoW, hoP, hoR, hoX, -⟩ := offs_conf hkp confP hN_conf hK_conf hd_conf
  exact time_wfB2_out hkp confP hN_conf hK_conf hd_conf hth hoB hoW hoP hoR hoX Lsd Lg hLsd hLg

end WB2

end AdvancedEncryption.DualUse.Prog
