import PE.Impl.RingBTVW.Prog.WfB2Time
import SigabaNeo.Lib.Machines.Prog.NatPSize

/-!
# The state count of the block-structured `W_f` block

`XProg.size (wfB2 hk c W)` (the number of states of its compiled machine, `XProg.card_state`) is
the sum of a part that depends only on `W` (`fixSz`: the gate counter, the two runs of the
machine, `simTmplP`, `simKeyP`, the clears) and the five template programs (`tmplP`, each value
by doubling, `size_natP_lt`). At `confP` (`size_wfB2_conf`): **at most `2^25` states**.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape

/-- **The state count of the templates**, values below `2^(B+1)`. -/
theorem size_tmplP_leB {n : ℕ} (c : Fin n) (B : ℕ) : ∀ l : List (Fin n × ℕ),
    (∀ x ∈ l, x.2 < 2 ^ (B + 1)) → (tmplP c l).size ≤ l.length * ((B + 1) * 195 + 36) + 36
  | [], _ => by simp [tmplP, Prog.size, Prim.pad]
  | x :: l, h => by
    rw [tmplP, XProg.size_seq]
    have h1 := XProg.size_natP_lt x.1 c (h x (by simp))
    have h2 := size_tmplP_leB c B l (fun y hy => h y (by simp [hy]))
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
      (offPsi hk c + nA * lenPsi N K k))).size +
    (tmplP ValVM.tX0 (keyT N K k c.d)).size := by
  simp only [wfB2, wfBody, prepT, prepG, prepTRest, prepGRest, keyPrep, fixSz, XProg.size_seq, XProg.size_frame,
    XProg.size_prog]
  omega

theorem length_tmpl31 (N K k d : ℕ) : (tmpl31 N K k d).length = 8 := rfl
theorem length_stepT (N K k d : ℕ) : (stepT N K k d).length = 19 := rfl
theorem length_stepG (N K k d : ℕ) : (stepG N K k d).length = 23 := rfl
theorem length_wordsT (N K k d W a b e : ℕ) : (wordsT N K k d W a b e).length = 41 := rfl
theorem length_wordsG (N K k d W a b e : ℕ) : (wordsG N K k d W a b e).length = 23 := rfl
theorem length_keyT (N K k d : ℕ) : (keyT N K k d).length = 18 := rfl

end WB2
end AdvancedEncryption.RingBTVW.Prog
