import PE.Impl.ExpLUT.Prog.KeyTryVM
import PE.Impl.ExpLUT.Prog.KeyEval
import PE.Impl.ExpLUT.Prog.KeyTryMath

/-! Executable automorphic inner products for the real-trapdoor correction. -/
namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- Save the row length, apply the automorphism, then accumulate the inner product. -/
def autDotC : Code := .seq (.cp 56 rQc)
  (.seq autQC (.seq (.cp rQc 56) ipC))

theorem wf_autDotC : autDotC.WFc := by
  simp [autDotC, autQC, autQBody, ipC, ipBody, Code.WFc, Code.writes]

/-- The actual correction kernel consumes both rows and adds their automorphic inner product. -/
theorem exec_autDotC {N K : ℕ} (hN : 0 < N) (hK : 0 < K)
    (w : St) (la lb : List (Rq N K)) (n k : ℕ) (hk : 0 < k) (acc : Rq N K)
    (h1 : la.length = n) (h2 : lb.length = n)
    (hA : w rQa = encL N K la) (hB : w rQb = encL N K lb)
    (hC : w rQc = List.replicate n false) (hQk : w rQk = List.replicate k false)
    (hI : w rIa = encRM N K acc) (hZ : w rZ = encRM N K 0) :
    exec N K autDotC w rIa =
      encRM N K (acc + (List.zipWith (· * ·) (la.map (aut N k)) lb).sum) ∧
    exec N K autDotC w rQa = [] ∧ exec N K autDotC w rQb = [] := by
  let v := exec N K (.cp 56 rQc) w
  have vf : ∀ i : Fin 64, i ≠ 56 → v i = w i :=
    fun i hi ↦ Function.update_of_ne hi _ _
  have va := exec_autQC hN hK v la n k hk h1
    (by rw [vf _ (by decide), hA]) (by rw [vf _ (by decide), hC])
    (by rw [vf _ (by decide), hQk]) (by rw [vf _ (by decide), hZ])
  let u := exec N K (.cp rQc 56) (exec N K autQC v)
  have uf : ∀ i : Fin 64, i ≠ rQc → autQC.writes i = false → i ≠ 56 → u i = w i := by
    intro i hic hi hi56
    change Function.update (exec N K autQC v) rQc (exec N K autQC v 56) i = _
    rw [Function.update_of_ne hic, exec_writes _ _ _ hi, vf i hi56]
  have ua : u rQa = encL N K (la.map (aut N k)) := by
    change Function.update (exec N K autQC v) rQc (exec N K autQC v 56) rQa = _
    rw [Function.update_of_ne (by decide), va]
  have uc : u rQc = List.replicate n false := by
    change exec N K autQC v 56 = _
    rw [exec_writes _ _ _ (by decide)]
    exact hC
  have result := exec_ipC hK u (la.map (aut N k)) lb [] [] n acc
    (by simpa using h1) h2 (by simpa using ua)
    (by simpa using uf rQb (by decide) (by decide) (by decide) |>.trans hB) uc
    (by rw [uf _ (by decide) (by decide) (by decide), hI])
    (by rw [uf _ (by decide) (by decide) (by decide), hZ])
  exact result

/-- The negative real trapdoor becomes an addition in the corrected proposal `p - T z`. -/
theorem corrected_inl (D : Dims)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D) (i : Fin (setting D).E.W) (w : Wb D) :
    (p - realTrap (S := setting D) (J := Jh D) T z) (.inl (i, w)) =
      p (.inl (i, w)) + ∑ c, aut D.N (gD D ^ i.val) (T w c) * z (i, c) := by
  simp only [Pi.sub_apply, realTrap, sub_neg_eq_add]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  change autσ D.N (gD D ^ i.val) (T w c) = _
  exact autσ_of_odd ((odd_gD D).pow) _

/-- All non-trapdoor coordinates of the proposal remain unchanged. -/
theorem corrected_inr (D : Dims)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D)
    (q : (Fin (setting D).E.W × Jh D × Col (setting D).τ) ⊕ Col (setting D).τ) :
    (p - realTrap (S := setting D) (J := Jh D) T z) (.inr q) = p (.inr q) := by
  simp only [Pi.sub_apply, realTrap, sub_zero]

/-- Ordered rows give the finite inner product used in the trapdoor correction. -/
theorem zip_aut_ofFn {N K n : ℕ} (k : ℕ) (a b : Fin n → Rq N K) :
    (List.zipWith (· * ·) ((List.ofFn a).map (aut N k)) (List.ofFn b)).sum =
      ∑ c, aut N k (a c) * b c := by
  have he : List.zipWith (· * ·) ((List.ofFn a).map (aut N k)) (List.ofFn b) =
      List.ofFn (fun c ↦ aut N k (a c) * b c) := by
    apply List.ext_getElem
    · simp
    · intro j hj hj'; simp
  rw [he, List.sum_ofFn]

/-- A corrected trapdoor coordinate is produced by the actual automorphism/inner-product code. -/
theorem exec_autDotC_corrected (D : Dims)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D)
    (i : Fin (setting D).E.W) (row : Wb D) (w : St)
    (hA : w rQa = encL D.N D.K (List.ofFn (T row)))
    (hB : w rQb = encL D.N D.K (List.ofFn (fun c : Fin D.K ↦ z (i, c))))
    (hC : w rQc = List.replicate D.K false)
    (hQk : w rQk = List.replicate (gD D ^ i.val) false)
    (hI : w rIa = encRM D.N D.K (p (.inl (i, row))))
    (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K autDotC w rIa = encRM D.N D.K
      ((p - realTrap (S := setting D) (J := Jh D) T z) (.inl (i, row))) ∧
    exec D.N D.K autDotC w rQa = [] ∧ exec D.N D.K autDotC w rQb = [] := by
  have h := exec_autDotC D.N_pos D.K_pos w (List.ofFn (T row))
    (List.ofFn (fun c : Fin D.K ↦ z (i, c))) D.K (gD D ^ i.val)
    ((odd_gD D).pow).pos (p (.inl (i, row))) (by simp) (by simp) hA hB hC hQk hI hZ
  rw [zip_aut_ofFn, ← corrected_inl D T p z i row] at h
  exact h

end AdvancedEncryption.ExpLUT.Prog
