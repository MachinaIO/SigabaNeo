import PE.Impl.DualUse.Prog.WfB2Conf
import SigabaNeo.Lib.Machines.Prog.NatPSize

/-!
# The state count of the block-structured `W_f` block

`XProg.size (wfB2 hk c W)` (the number of states of its compiled machine, `XProg.card_state`) is
the sum of a part that depends only on `W` (`fixSz`: the gate counter, the two runs of the
machine, `simTmplP`, `simKeyP`, the clears) and the five template programs (`tmplP`, each value
by doubling, `size_natP_lt`). At `confP` (`size_wfB2_conf`): **at most `2^25` states**.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape

/-- **The state count of the templates**, values below `2^(B+1)`. -/
theorem size_tmplP_le {n : ℕ} (c : Fin n) (B : ℕ) : ∀ l : List (Fin n × ℕ),
    (∀ x ∈ l, x.2 < 2 ^ (B + 1)) → (tmplP c l).size ≤ l.length * ((B + 1) * 195 + 36) + 36
  | [], _ => by simp [tmplP, Prog.size, Prim.pad]
  | x :: l, h => by
    rw [tmplP, XProg.size_seq]
    have h1 := XProg.size_natP_lt x.1 c (h x (by simp))
    have h2 := size_tmplP_le c B l (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons]
    nlinarith

namespace WB2

open SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST
  SigabaNeo.Tape.Prog.StepT SigabaNeo.Lattices.Algo SigabaNeo.Lattices

set_option maxRecDepth 100000

/-- The states of `wfB2` but the templates' (they depend on `W` only). -/
noncomputable def fixSz (W : ℕ) : ℕ :=
  (cp (mw GSC) (mw GS)).size + (Prog.countP (2 * W)).size + (Prog.capP W).size +
  (clr (mw 12)).size + (cp (mw GS) (mw GSC)).size + simTmplP.size + (copiesP 0).size +
  (clr ValVM.tX0).size + (putW (mw OB) [true]).size + (putW (mw ZB) [false]).size +
  runT.size +
  (clrsP lowW ⨾ cp (mw GS) (mw GSC)).size + (Prog.countP (2 * W)).size + (Prog.capP W).size +
  (clr (mw 12)).size + (cp (mw GS) (mw GSC)).size + simTmplP.size + (copiesP 1).size +
  (clr ValVM.tX0).size + (clr (ms 92)).size +
  runG.size +
  (clrsP keyClr).size + (putW (ms 87) [false]).size + simKeyP.size + (clrsP finClr).size

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The state count of `wfB2`**: `fixSz` and the templates. -/
theorem size_wfB2 (W : ℕ) : (wfB2 hk c W).size = fixSz W +
    (tmplP ValVM.tX0 (tmpl31 N K k c.d)).size +
    (tmplP ValVM.tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c))).size +
    (tmplP ValVM.tX0 (tmpl31 N K k c.d)).size +
    (tmplP ValVM.tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
      (offPsi hk c + 10 * lenPsi N K k))).size +
    (tmplP ValVM.tX0 (keyT N K k c.d)).size := by
  simp only [wfB2, wfBody, prepT, prepG, keyPrep, fixSz, XProg.size_seq, XProg.size_frame,
    XProg.size_prog]
  omega

theorem length_tmpl31 (N K k d : ℕ) : (tmpl31 N K k d).length = 8 := rfl
theorem length_stepT (N K k d : ℕ) : (stepT N K k d).length = 19 := rfl
theorem length_stepG (N K k d : ℕ) : (stepG N K k d).length = 23 := rfl
theorem length_wordsT (N K k d W a b e : ℕ) : (wordsT N K k d W a b e).length = 41 := rfl
theorem length_wordsG (N K k d W a b e : ℕ) : (wordsG N K k d W a b e).length = 23 := rfl
theorem length_keyT (N K k d : ℕ) : (keyT N K k d).length = 18 := rfl

theorem chk_fixSz : fixSz Wc ≤ 10 * 2 ^ 20 := by decide +kernel

/-- **At most `2^25` states at `confP`.** -/
theorem size_wfB2_conf {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (hN : N = Nc)
    (hK : K = Kc) (hd : c.d = dc) (hth : treeHeight N (K + 1) ≤ 64)
    (hoB : offB c ≤ Lb) (hoW : offW hk c ≤ Lb) (hoP : offPsi hk c ≤ Lb) (hoR : offR hk c ≤ Lb)
    (hoX : offPsi hk c + 10 * lenPsi N K (K + 1) ≤ Lb) :
    (wfB2 hk c Wc).size ≤ 2 ^ 25 := by
  subst hN hK
  obtain ⟨-, -, -, s31, sT, -, -, -, sG, -, sK, -⟩ := chk_small
  have hTl : TLe (wordsT Nc Kc (Kc + 1) c.d Wc (offB c) (offW hk c) (offPsi hk c)) wTc := by
    rw [wordsT_eq, hd]; exact TLe_wordsTx _ _ _ _ _ hth hoB hoW hoP
  have hGl : TLe (wordsG Nc Kc (Kc + 1) c.d Wc (offPsi hk c) (offR hk c)
      (offPsi hk c + 10 * lenPsi Nc Kc (Kc + 1))) wGc := by
    rw [hd]; exact TLe_wordsG _ _ _ _ _ hoP hoR hoX
  have hM : Mall < 2 ^ (250 + 1) := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have lt : ∀ {l : List (Fin 256 × ℕ)}, (∀ x ∈ l, x.2 ≤ Mall) → ∀ x ∈ l, x.2 < 2 ^ (250 + 1) :=
    fun h x hx => (h x hx).trans_lt hM
  have a1 := size_tmplP_le ValVM.tX0 250 (tmpl31 Nc Kc (Kc + 1) c.d) (lt (by rw [hd]; exact s31))
  have a2 := size_tmplP_le ValVM.tX0 250 _
    (lt (TLe_le (TLe_append (TLe_refl (stepT Nc Kc (Kc + 1) c.d)) hTl) (by rw [hd]; exact sT)))
  have a4 := size_tmplP_le ValVM.tX0 250 _
    (lt (TLe_le (TLe_append (TLe_refl (stepG Nc Kc (Kc + 1) c.d)) hGl) (by rw [hd]; exact sG)))
  have a5 := size_tmplP_le ValVM.tX0 250 (keyT Nc Kc (Kc + 1) c.d) (lt (by rw [hd]; exact sK))
  rw [List.length_append, length_stepT, length_wordsT] at a2
  rw [List.length_append, length_stepG, length_wordsG] at a4
  rw [length_tmpl31] at a1
  rw [length_keyT] at a5
  rw [size_wfB2]
  have := chk_fixSz
  omega

end WB2

end AdvancedEncryption.DualUse.Prog
