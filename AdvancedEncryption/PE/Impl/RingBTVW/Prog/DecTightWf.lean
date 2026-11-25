import PE.Impl.RingBTVW.Prog.WfB2SConf

/-!
# The `W_f` block of `Dec` with per-tape output bounds

`time_wfB2S_conf` (`WfB2SConf`) bounds every tape after the stream block uniformly by
`Malln = 2^262`. The block ends by clearing every tape but the data word (tape `0` outside) and the
output (tape `2` outside), so per tape:

* **`time_wfB2S_out`**: at the numbers of `confA`, from `io2 Lsd Lg 0` (`Lsd ≤ 2^260`,
  `Lg ≤ 2^64`), at most `2^628` steps, and afterwards tape `0` at most `2^260` bits, tape `2` at
  most `wOut2S = d · 2k · N K` bits, every other tape blank (`wOutS`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

namespace WB2

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST
  SigabaNeo.Tape.Prog.StepT SigabaNeo.Lattices.Algo SigabaNeo.Lattices SigabaNeo.Tape.XProg

set_option maxRecDepth 100000

/-- The bound of the output tape of the stream block: `d · 2k · N K`. -/
def wOut2S : ℕ := dn * (2 * kn) * (Nn * Kn)

/-- The per-tape bounds after the stream block: the data word on tape `0`, the output on tape `2`. -/
def wOutS : Fin 256 → ℕ := fun t => if t = 0 then Lbn else if t = 2 then wOut2S else 0

theorem embedF_permS {k : ℕ} (e : Equiv.Perm (Fin k)) (f g : Fin k → ℕ) (t : Fin k) :
    embedF e.toEmbedding f g t = g (e.symm t) := by
  have h : t = e.toEmbedding (e.symm t) := by simp
  conv_lhs => rw [h]
  exact embedF_apply_self _ _ _ _

theorem chk_outS : ∀ t, Prog.lenBoundT (clrsP finClr) v6n (swp.symm t) ≤ wOutS t := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The stream block with per-tape output bounds** (the proof of `time_wfB2S_conf`, keeping
the bounds of the final cleanup per tape). -/
theorem time_wfB2S_out {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1))
    (hN : N = Nn) (hK : K = Kn) (hd : c.d = dn) (hnA : nA = nAn)
    (hth : treeHeight N (K + 1) ≤ 66)
    (hoB : offB c ≤ Lbn) (hoW : offW hk c ≤ Lbn) (hoP : offPsi hk c ≤ Lbn) (hoR : offR hk c ≤ Lbn)
    (hoX : offPsi hk c + nA * lenPsi N K (K + 1) ≤ Lbn) (Lsd Lg : ℕ) (hLsd : Lsd ≤ Lbn)
    (hLg : Lg ≤ Lgn) :
    XProg.timeBoundT (wfB2S hk c Icn Wn) (io2 (R := 254) Lsd Lg 0) ≤ 2 ^ 628 ∧
      XProg.lenBoundT (wfB2S hk c Icn Wn) (io2 (R := 254) Lsd Lg 0) ≤ wOutS := by
  subst hN hK
  obtain ⟨s0, s2, s6, s31, sT, s1, s2G, s6G, sG, s4, sK, s6'⟩ := chk_smallS
  -- the preparation of `f̂`
  have p1 := ph_prepTS hk c Wn Icn β0n M31n (by rw [hd]; exact chk_hinTS) (by rw [hd]; exact chk_htopTS)
  have hTl : TLe (wordsT Nn Kn (Kn + 1) c.d Wn (offB c) (offW hk c) (offPsi hk c)) wTn := by
    rw [wordsT_eq, hd]; exact TLe_wordsT_fixT _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnA hth hoB hoW hoP
  have g1 : vTS hk c Wn Icn β0n M31n ≤ encB (bsT Nn Kn kn dn) (VT Nn Kn kn dn) (gB L0n) :=
    (vTS_le hk c Wn Icn β0n M31n wTn hTl).trans (by rw [hd]; exact chk_g1S)
  -- the run of `f̂`
  have p2 := ph_runTR_conf
  -- the preparation of the predicate
  have p3 := ph_prepGS hk c Wn Icn β1n M31n (by rw [hd]; exact chk_hinGS) (by rw [hd]; exact chk_htopGS)
  have hGl : TLe (wordsG Nn Kn (Kn + 1) c.d Wn (offPsi hk c) (offR hk c)
      (offPsi hk c + nA * lenPsi Nn Kn (Kn + 1))) wGn := by
    rw [hd]; exact TLe_wordsG_fixT _ _ _ _ _ _ _ _ _ _ _ _ hnA hoP hoR hoX
  have g3 : vGS hk c Wn Icn β1n M31n ≤ encB (bsG Nn Kn kn dn) (VG Nn Kn kn dn) (gB L0Gn) :=
    (vGS_le hk c Wn Icn β1n M31n wGn hGl).trans (by rw [hd]; exact chk_g3S)
  -- the predicate's run
  have p4 := ph_runGR_conf
  -- the key sum
  have p5 := ph_keyPrep Nn Kn kn dn β4n
  have hkp : keyPrep Nn Kn (Kn + 1) c.d = keyPrep Nn Kn kn dn := by rw [hd]; rfl
  rw [← hkp] at p5
  have p6 := ph_simKey v5n Mskn Nn Kn dn kn (nPos Nn kn) (VT Nn Kn kn dn) (lenA Nn Kn kn 1)
    (gB L1Gn FOUT) (gB L1Gn 61) (gB L1Gn OUTW) 1 (VG Nn Kn kn dn) (lenA Nn Kn kn 2) chk_skn.1
    chk_skn.2
  have p7 := ph_finClr v6n
  have body := ph_wfBodyS hk c Wn Icn p1 g1 p2 p3 g3 p4 p5 p6 p7
  -- the input
  have hin : (fun j => io2 (R := 254) Lsd Lg 0 (eW j)) ≤ β0n := fun t => by
    obtain ⟨e0, e1, -, -⟩ := swp_eq t
    show io2 (R := 254) Lsd Lg 0 (swp t) ≤ β0n t
    simp only [io2, β0n, e0, e1]
    split_ifs <;> omega
  obtain ⟨ht, hl⟩ := ph_wfB2S hk c Wn Icn (body.mono hin le_rfl le_rfl) _ le_rfl
  refine ⟨ht.trans ?_, fun t => (hl t).trans ?_⟩
  · -- the steps
    have a1 := tTS_le hk c Wn Icn β0n M31n Malln s0 s2 (by rw [tmOut_eq, hd]; exact s6)
      (by rw [hd]; exact s31) (TLe_le (TLe_append (TLe_refl _) hTl) (by rw [hd]; exact sT))
    have a3 := tGS_le hk c Wn Icn β1n M31n Malln s1 s2G (by rw [tmOut_eq, hd]; exact s6G)
      (by rw [hd]; exact s31) (TLe_le (TLe_append (TLe_refl _) hGl) (by rw [hd]; exact sG))
    have a5 := tK_le Nn Kn kn dn β4n Malln s4 sK
    have a6 := chk_skTn
    have a7 := tF_le v6n Malln s6'
    exact (Nat.add_le_add a1 (Nat.add_le_add le_rfl (Nat.add_le_add a3 (Nat.add_le_add le_rfl
      (Nat.add_le_add a5 (Nat.add_le_add a6 a7)))))).trans chk_sumS
  · show embedF swp.toEmbedding _ _ t ≤ _
    rw [embedF_permS]
    exact chk_outS t

end WB2

end AdvancedEncryption.RingBTVW.Prog
