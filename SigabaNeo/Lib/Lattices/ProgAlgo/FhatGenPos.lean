import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenCompile
import SigabaNeo.Lib.Lattices.ProgAlgo.KeySum

/-!
# Generating gate tapes: the positions of the output wires

`posBody`: for the bit `(c, i, j)` (registers `47 48 49`), fetch the position of the wire of the
output representation (list `23`, index `(c N + j) k + i`), fix it against the threshold `58`
(positions not below it are read as `1`), append it to the list `19`. `iter_posBody`: the loop over
all `(c, i, j)` (odometer `odoC`) collects the positions in the order of `posW`.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {E : Env}

/-- One bit `(c, i, j)` of the output. -/
def posBody : Code :=
  .seq (.mov 50 47) (.seq (maddC 50 5 49 53) (.seq (maddC 50 2 48 53) (.seq (fetchC 51 23 50 20)
    (.seq (.ifLt 51 58 .skip (.mov 51 0)) (.lpush 19 51)))))

/-- The fixed position of the bit `(c, i, j)` of a list `R`. -/
def pfix (n thr : ℕ) (N k : ℕ) (R : List ℕ) (c i j : ℕ) : ℕ :=
  if R.getD ((c * N + j) * k + i) 0 < thr then R.getD ((c * N + j) * k + i) 0 else n

theorem exec_posBody {N k : ℕ} (hk : 0 < k) (hN : 0 < N) (σ : St) (c i j : ℕ) (R : List ℕ) (thr : ℕ) (h2 : σ.sc 2 = k)
    (h5 : σ.sc 5 = N) (h0 : σ.sc 0 = E.n) (h47 : σ.sc 47 = c) (h48 : σ.sc 48 = i)
    (h49 : σ.sc 49 = j) (h58 : σ.sc 58 = thr) (h23 : σ.ls 23 = R)
    (hM : (c * N + j) * k + i ≤ E.M) (hR : ∀ x ∈ R, x ≤ E.M) (hnM : E.n ≤ E.M)
    (hC : (σ.ls 19).length < E.C) :
    ∃ sc' ls', exec E posBody σ = setSL σ sc' ls' ∧
      ls' 19 = σ.ls 19 ++ [pfix E.n thr N k R c i j] ∧
      (∀ r : SR, r.val < 41 ∨ (41 < r.val ∧ r.val < 50) ∨ 53 < r.val → sc' r = σ.sc r) ∧
      ∀ l : LR, l ≠ 19 → l ≠ 20 → ls' l = σ.ls l := by
  have b1 : c * N + j ≤ (c * N + j) * k + i :=
    le_trans (Nat.le_mul_of_pos_right _ hk) (Nat.le_add_right _ _)
  have b0 : c ≤ c * N + j := le_trans (Nat.le_mul_of_pos_right _ hN) (Nat.le_add_right _ _)
  set s1 := setSL σ (Function.update σ.sc 50 c) σ.ls
  have e1 : exec E (.mov 50 47) σ = s1 := by simp [exec, s1, setSL, h47]
  have q2 := exec_maddC (E := E) 50 5 49 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s1 (by simp [s1, setSL, h5, h49]; nlinarith)
  set s2 := setSL s1 (Function.update (Function.update s1.sc 53 (s1.sc 50)) 50
    (s1.sc 50 * s1.sc 5 + s1.sc 49)) s1.ls
  have q3 := exec_maddC (E := E) 50 2 48 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s2 (by simp [s2, s1, setSL, h5, h49, h2, h48, Function.update_apply]; nlinarith)
  set s3 := setSL s2 (Function.update (Function.update s2.sc 53 (s2.sc 50)) 50
    (s2.sc 50 * s2.sc 2 + s2.sc 48)) s2.ls
  have h50 : s3.sc 50 = (c * N + j) * k + i := by
    simp [s3, s2, s1, setSL, h5, h49, h2, h48, Function.update_apply]
  have hs3 : ∀ r : SR, r ≠ 50 → r ≠ 53 → s3.sc r = σ.sc r := fun r a b => by
    simp [s3, s2, s1, setSL, Function.update_of_ne a, Function.update_of_ne b]
  have hl3 : s3.ls = σ.ls := rfl
  obtain ⟨sc4, e4, d4, f4⟩ := exec_fetchC (E := E) 51 23 50 20 s3
  set x := R.getD ((c * N + j) * k + i) 0
  have hx : sc4 51 = x := by rw [d4, hl3, h23, h50]
  set s4 := setSL s3 sc4 (Function.update s3.ls 20 (((s3.ls 23).drop (s3.sc 50)).tail))
  have hs4 : ∀ r : SR, r ≠ 41 → r ≠ 51 → sc4 r = s3.sc r := fun r a b =>
    f4 r (by simp [a, b])
  set s5 := setSL s4 (Function.update sc4 51 (pfix E.n thr N k R c i j)) s4.ls
  have e5 : exec E (.ifLt 51 58 .skip (.mov 51 0)) s4 = s5 := by
    have h58' : sc4 58 = thr := by
      rw [hs4 58 (by decide) (by decide), hs3 58 (by decide) (by decide), h58]
    have h0' : sc4 0 = E.n := by
      rw [hs4 0 (by decide) (by decide), hs3 0 (by decide) (by decide), h0]
    simp only [exec_ifLt, s4, setSL, hx, h58', s5, pfix]
    split_ifs with h
    · simp only [exec]; congr 1; funext r; by_cases hr : r = 51
      · subst hr; simp [hx, x, List.getD_eq_getElem?_getD]
      · simp [Function.update_of_ne hr]
    · simp [exec, h0']
  have hv : pfix E.n thr N k R c i j ≤ E.M := by
    unfold pfix; split_ifs
    · rcases Nat.lt_or_ge ((c * N + j) * k + i) R.length with h | h
      · exact hR _ (by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
      · rw [List.getD_eq_default _ _ h]; omega
    · exact hnM
  have e6 := exec_lpush_lt s5 19 51 (by simp [s5, s4, s3, s2, s1, setSL]; exact hC)
    (by simp [s5, setSL]; exact hv)
  refine ⟨s5.sc, Function.update s5.ls 19 (s5.ls 19 ++ [s5.sc 51]), ?_, ?_, fun r hr => ?_,
    fun l a b => ?_⟩
  · rw [posBody, exec_seq, e1, exec_seq, q2, exec_seq, q3, exec_seq, e4, exec_seq, e5, e6]; rfl
  · simp [s5, s4, s3, s2, s1, setSL]
  · simp only [s5, setSL]
    rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
      hs4 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide),
      hs3 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)]
  · simp [s5, s4, s3, s2, s1, setSL, Function.update_of_ne a, Function.update_of_ne b]

end FhatGen

end SigabaNeo.Lattices
