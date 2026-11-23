import PE.Impl.DualUse.Prog.WfB2SConf
import PE.Impl.DualUse.Prog.WfB2Size

/-!
# The state count of the `W_f` block on register streams

As `WfB2Size`: `XProg.size (wfB2S hk c Ic W)` is a part that depends only on `W` and `Ic`
(`fixSzS`: the count, the cap `capN Ic` with its template by `natP`, the two runs on the register
loop, `simTmplP`, `simKeyP`, the clears) and the five template programs. At the numbers of
`confA` (`size_wfB2S_conf`): **at most `2^25` states**.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape

namespace WB2

open SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST
  SigabaNeo.Tape.Prog.StepT SigabaNeo.Lattices.Algo SigabaNeo.Lattices

set_option maxRecDepth 100000

/-- The states of `wfB2S` but the templates' (they depend on `W` and `Ic` only). -/
noncomputable def fixSzS (W Ic : ℕ) : ℕ :=
  (cp (mw GSC) (mw GS)).size + (Prog.countP (3 * W)).size + (clr (mw 1)).size +
  (XProg.capN Ic).size +
  (clr (mw 12)).size + (cp (mw GS) (mw GSC)).size + simTmplP.size + (copiesP 0).size +
  (clr ValVM.tX0).size + (putW (mw OB) [true]).size + (putW (mw ZB) [false]).size +
  runTR.size +
  (clrsP lowW ⨾ cp (mw GS) (mw GSC)).size + (Prog.countP (3 * W)).size + (clr (mw 1)).size +
  (XProg.capN Ic).size +
  (clr (mw 12)).size + (cp (mw GS) (mw GSC)).size + simTmplP.size + (copiesP 1).size +
  (clr ValVM.tX0).size + (clr (ms 92)).size +
  runGR.size +
  (clrsP keyClr).size + (putW (ms 87) [false]).size + simKeyP.size + (clrsP finClr).size

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The state count of `wfB2S`**: `fixSzS` and the templates. -/
theorem size_wfB2S (Ic W : ℕ) : (wfB2S hk c Ic W).size = fixSzS W Ic +
    (tmplP ValVM.tX0 (tmpl31 N K k c.d)).size +
    (tmplP ValVM.tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c))).size +
    (tmplP ValVM.tX0 (tmpl31 N K k c.d)).size +
    (tmplP ValVM.tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
      (offPsi hk c + nA * lenPsi N K k))).size +
    (tmplP ValVM.tX0 (keyT N K k c.d)).size := by
  simp only [wfB2S, wfBodyS, prepTS, prepGS, cntS, prepTRest, prepGRest, keyPrep, fixSzS,
    XProg.size_seq, XProg.size_frame, XProg.size_prog]
  omega

theorem chk_fixSzS : fixSzS Wn Icn ≤ 10 * 2 ^ 20 := by decide +kernel

/-- **At most `2^25` states at the numbers of `confA`.** -/
theorem size_wfB2S_conf {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1))
    (hN : N = Nn) (hK : K = Kn) (hd : c.d = dn) (hnA : nA = nAn)
    (hth : treeHeight N (K + 1) ≤ 66)
    (hoB : offB c ≤ Lbn) (hoW : offW hk c ≤ Lbn) (hoP : offPsi hk c ≤ Lbn) (hoR : offR hk c ≤ Lbn)
    (hoX : offPsi hk c + nA * lenPsi N K (K + 1) ≤ Lbn) :
    (wfB2S hk c Icn Wn).size ≤ 2 ^ 25 := by
  subst hN hK
  obtain ⟨-, -, -, s31, sT, -, -, -, sG, -, sK, -⟩ := chk_smallS
  have hTl : TLe (wordsT Nn Kn (Kn + 1) c.d Wn (offB c) (offW hk c) (offPsi hk c)) wTn := by
    rw [wordsT_eq, hd]; exact TLe_wordsT_fixT _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnA hth hoB hoW hoP
  have hGl : TLe (wordsG Nn Kn (Kn + 1) c.d Wn (offPsi hk c) (offR hk c)
      (offPsi hk c + nA * lenPsi Nn Kn (Kn + 1))) wGn := by
    rw [hd]; exact TLe_wordsG_fixT _ _ _ _ _ _ _ _ _ _ _ _ hnA hoP hoR hoX
  have hM : Malln < 2 ^ (262 + 1) := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have lt : ∀ {l : List (Fin 256 × ℕ)}, (∀ x ∈ l, x.2 ≤ Malln) → ∀ x ∈ l, x.2 < 2 ^ (262 + 1) :=
    fun h x hx => (h x hx).trans_lt hM
  have a1 := size_tmplP_leB ValVM.tX0 262 (tmpl31 Nn Kn (Kn + 1) c.d) (lt (by rw [hd]; exact s31))
  have a2 := size_tmplP_leB ValVM.tX0 262 _
    (lt (TLe_le (TLe_append (TLe_refl (stepT Nn Kn (Kn + 1) c.d)) hTl) (by rw [hd]; exact sT)))
  have a4 := size_tmplP_leB ValVM.tX0 262 _
    (lt (TLe_le (TLe_append (TLe_refl (stepG Nn Kn (Kn + 1) c.d)) hGl) (by rw [hd]; exact sG)))
  have a5 := size_tmplP_leB ValVM.tX0 262 (keyT Nn Kn (Kn + 1) c.d) (lt (by rw [hd]; exact sK))
  rw [List.length_append, length_stepT, length_wordsT] at a2
  rw [List.length_append, length_stepG, length_wordsG] at a4
  rw [length_tmpl31] at a1
  rw [length_keyT] at a5
  rw [size_wfB2S]
  have := chk_fixSzS
  omega

end WB2

end AdvancedEncryption.DualUse.Prog
