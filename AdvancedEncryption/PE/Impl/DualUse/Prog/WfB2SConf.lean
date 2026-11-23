import PE.Impl.DualUse.Prog.WfRCert
import PE.Impl.DualUse.Prog.WfB2STime

/-!
# The time of the `W_f` block on register streams at the numbers of `confA`

The certificate of `WfRCert` (the two runs on any instruction stream, `L1n`, `L1Gn`, the sweeps
of the key sum) completed by the phases of the preparations (`WfB2STime`) and the checks between
them, at `N = 2^36`, `K = 2^27`, `k = K + 1`, `d = 2^65`, `W = 512`, `nA = 128`, `|sdEnc|` and the
offsets `≤ 2^260`, the stream `≤ 2^64` bits, the count capped at `Icn = 2^50`:

**`time_wfB2S_conf`**: at most `2^628` steps, every tape `≤ 2^262` bits afterwards.

The statement is generic: the numbers enter through `N = Nn`, `K = Kn`, `c.d = dn`,
`nA = nAn` and the bounds of the offsets (hypotheses), so it is instantiated at the switch
(`nA := 128`). The templates of the code are compared with those of the certificate by
`TLe_wordsT_fixT`, `TLe_wordsG_fixT` (they agree when `nA = nAn`).
-/

namespace AdvancedEncryption.DualUse.Prog

namespace WB2

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST
  SigabaNeo.Tape.Prog.StepT SigabaNeo.Lattices.Algo SigabaNeo.Lattices SigabaNeo.Tape.XProg

set_option maxRecDepth 100000

/-! ### The templates of the code and of the certificate -/

theorem TLe_wordsT_fixT (N K k d W n th oB oW oP th' oB' oW' oP' : ℕ) (hn : nA = n)
    (h0 : th ≤ th') (h1 : oB ≤ oB') (h2 : oW ≤ oW') (h3 : oP ≤ oP') :
    TLe (wordsTx N K k d W th oB oW oP)
      (fixT n (nBI N K * VT N K k d) W (wordsTx N K k d W th' oB' oW' oP')) := by
  subst hn
  simp (config := {decide := true}) [wordsTx, fixT, TLe, h0, h1, h2, h3]

theorem TLe_wordsG_fixT (N K k d W n oP oR oX oP' oR' oX' : ℕ) (hn : nA = n)
    (h1 : oP ≤ oP') (h2 : oR ≤ oR') (h3 : oX ≤ oX') :
    TLe (wordsG N K k d W oP oR oX) (fixT n (VG N K k d) W (wordsG N K k d W oP' oR' oX')) := by
  subst hn
  simp (config := {decide := true}) [wordsG, fixT, TLe, h1, h2, h3]

/-! ### The checks -/

/-- The bounds after `prepTS` at the numbers. -/
def vTSnn : Fin 256 → ℕ := vTSn Nn Kn kn dn Wn Icn wTn β0n M31n

theorem chk_hinTS : (fun j => tmplB tX0 (tmpl31 Nn Kn kn dn) (Prog.lenBoundT (cp (mw GS) (mw GSC))
    (Prog.lenBoundT (clr (mw 12)) (ccVS Wn Icn (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0n)))) (tm31 j)) ≤
    Sym.bnd (tmVars M31n Nn Kn kn (lenA Nn Kn kn dn)) σTmF := by decide +kernel

theorem chk_htopTS : ∀ j, tmplB tX0 (tmpl31 Nn Kn kn dn) (Prog.lenBoundT (cp (mw GS) (mw GSC))
    (Prog.lenBoundT (clr (mw 12)) (ccVS Wn Icn (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0n)))) (tm31 j) ≤
    M31n := by decide +kernel

/-- The words before the run of `f̂` are below `L0n` (the count below `Icn`). -/
theorem chk_g1S : vTSnn ≤ encB (bsT Nn Kn kn dn) (VT Nn Kn kn dn) (gB L0n) := by decide +kernel

theorem chk_hinGS : (fun j => tmplB tX0 (tmpl31 Nn Kn kn dn) (Prog.lenBoundT (cp (mw GS) (mw GSC))
    (Prog.lenBoundT (clr (mw 12)) (ccVS Wn Icn (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC))
      β1n)))) (tm31 j)) ≤ Sym.bnd (tmVars M31n Nn Kn kn (lenA Nn Kn kn dn)) σTmF := by
  decide +kernel

theorem chk_htopGS : ∀ j, tmplB tX0 (tmpl31 Nn Kn kn dn) (Prog.lenBoundT (cp (mw GS) (mw GSC))
    (Prog.lenBoundT (clr (mw 12)) (ccVS Wn Icn (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC))
      β1n)))) (tm31 j) ≤ M31n := by decide +kernel

/-- The bounds after `prepGS` at the numbers. -/
def vGSnn : Fin 256 → ℕ := vGSn Nn Kn kn dn Wn Icn wGn β1n M31n

/-- The words before the predicate's run are below `L0Gn`. -/
theorem chk_g3S : vGSnn ≤ encB (bsG Nn Kn kn dn) (VG Nn Kn kn dn) (gB L0Gn) := by decide +kernel

def β4n : Fin 256 → ℕ := encB (bsG Nn Kn kn dn) (VG Nn Kn kn dn) (gB L1Gn)
def v5n : Fin 256 → ℕ :=
  Function.update (tmplB tX0 (keyT Nn Kn kn dn) (Prog.lenBoundT (clrsP keyClr) β4n)) (ms 87)
    (tmplB tX0 (keyT Nn Kn kn dn) (Prog.lenBoundT (clrsP keyClr) β4n) (ms 87) + 1)

/-- The top of the frame of `simKeyP`. -/
def Mskn : ℕ := 2 ^ 262

theorem chk_skn : (fun j => v5n (oK2 j)) ≤ ℓSK Mskn Nn Kn dn kn (nPos Nn kn) (VT Nn Kn kn dn)
    (lenA Nn Kn kn 1) (gB L1Gn FOUT) (gB L1Gn 61) (gB L1Gn OUTW) 1 (VG Nn Kn kn dn)
    (lenA Nn Kn kn 2) ∧ ∀ j, v5n (oK2 j) ≤ Mskn := by decide +kernel

theorem chk_skTn : (2 * Mskn + 3) * simKeySweeps Nn Kn dn kn (nPos Nn kn) (VT Nn Kn kn dn)
    (lenA Nn Kn kn 1) 1 (VG Nn Kn kn dn) (lenA Nn Kn kn 2) ≤ 2 ^ 607 :=
  (Nat.mul_le_mul_left _ sweeps_conf).trans (by decide +kernel)

/-- The bounds after the framed `simKeyP`. -/
def v6n : Fin 256 → ℕ := embedF (ValVM.mkE oK2 oK2_inj) v5n
  fun j => if j = 0 then dn * (2 * kn) * (Nn * Kn) else Mskn

theorem chk_smallS :
    (∀ t, β0n t ≤ Malln) ∧
    (∀ t, ccVS Wn Icn (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0n) t ≤ Malln) ∧
    (∀ t, tmOutN Nn Kn kn dn M31n (tmplB tX0 (tmpl31 Nn Kn kn dn) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccVS Wn Icn (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0n))))) t ≤
        Malln) ∧
    (∀ x ∈ tmpl31 Nn Kn kn dn, x.2 ≤ Malln) ∧
    (∀ x ∈ stepT Nn Kn kn dn ++ wTn, x.2 ≤ Malln) ∧
    (∀ t, β1n t ≤ Malln) ∧
    (∀ t, ccVS Wn Icn (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1n) t ≤ Malln) ∧
    (∀ t, tmOutN Nn Kn kn dn M31n (tmplB tX0 (tmpl31 Nn Kn kn dn) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccVS Wn Icn (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC))
        β1n))))) t ≤ Malln) ∧
    (∀ x ∈ stepG Nn Kn kn dn ++ wGn, x.2 ≤ Malln) ∧
    (∀ t, β4n t ≤ Malln) ∧ (∀ x ∈ keyT Nn Kn kn dn, x.2 ≤ Malln) ∧ (∀ t, v6n t ≤ Malln) := by
  decide +kernel

theorem chk_sumS :
    ccTS Wn Icn (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0n) +
      (2 * M31n + 3) * simTmplSweeps Nn Kn kn + 90 * uT (Malln + 6) +
      (2 ^ 627 + (ccTS Wn Icn (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1n) +
      (2 * M31n + 3) * simTmplSweeps Nn Kn kn + 120 * uT (Malln + 40) + (2 ^ 525 +
      (120 * uT (Malln + 100) + (2 ^ 607 + 256 * (2 * (Malln + 256) + 5)))))) ≤ 2 ^ 628 := by
  decide +kernel

/-! ### The time of the block -/

set_option maxHeartbeats 4000000 in
/-- **The time of the `W_f` block on register streams at the numbers of `confA`**: from
`sdEnc` of at most `2^260` bits on tape `0` and an instruction stream of at most `2^64` bits on
tape `1` (the count capped at `2^50`), at most `2^628` steps, every tape below `2^262`
afterwards. -/
theorem time_wfB2S_conf {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1))
    (hN : N = Nn) (hK : K = Kn) (hd : c.d = dn) (hnA : nA = nAn)
    (hth : treeHeight N (K + 1) ≤ 66)
    (hoB : offB c ≤ Lbn) (hoW : offW hk c ≤ Lbn) (hoP : offPsi hk c ≤ Lbn) (hoR : offR hk c ≤ Lbn)
    (hoX : offPsi hk c + nA * lenPsi N K (K + 1) ≤ Lbn) (Lsd Lg : ℕ) (hLsd : Lsd ≤ Lbn)
    (hLg : Lg ≤ Lgn) :
    XProg.timeBoundT (wfB2S hk c Icn Wn) (io2 (R := 254) Lsd Lg 0) ≤ 2 ^ 628 ∧
      ∀ t, XProg.lenBoundT (wfB2S hk c Icn Wn) (io2 (R := 254) Lsd Lg 0) t ≤ Malln := by
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
  · -- the lengths
    have hng : (clrsP finClr).NoGrow := by
      show (clrsP finClr).noGrowB = true
      have : ∀ l : List (Fin 256), (clrsP l).noGrowB = true := by
        intro l; induction l with
        | nil => rfl
        | cons x l ih => simp [clrsP, Prog.noGrowB, ih, Prim.noGrowB]
      exact this _
    have hf := Sym.lenBoundT_le_const (clrsP finClr) hng s6'
    rcases embedF_cases eW (io2 (R := 254) Lsd Lg 0) (Prog.lenBoundT (clrsP finClr) v6n) t with
      ⟨_, h⟩ | ⟨j, _, h⟩
    · rw [h]; simp only [io2]; split_ifs <;> simp only [Malln, Lbn, Lgn] at * <;> omega
    · rw [h]; exact hf j

end WB2

end AdvancedEncryption.DualUse.Prog
