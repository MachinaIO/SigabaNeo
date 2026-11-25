import PE.Impl.ExpLUT.Prog.RedPubPOutBH
open SigabaNeo.Tape.RingVM.Buf SigabaNeo.Tape.RingVM.Hash
/-!
# `Ā`, `B̄⁽²⁾`, `−v̄_B` and the monomials `X^{w x_t}` (package G2, `pubP`)

* **`exec_prepC`**: the words of `Ā`, `B̄⁽²⁾` (the first `m̄` words of `aB`, `B⁽²⁾`) and of
  `−v̄_B` (`nvW`, decoding to `−v_B`);
* **`exec_monoC`**: from the next 8 attribute bits (symbol `t`, most significant first), the word
  of `X^{w x_t}` in `rU`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-! ### `Ā`, `B̄⁽²⁾`, `−v̄_B` -/

theorem pwordsOf_bcol (v : BCol (Wb D) D.K → Rg D) :
    pwordsOf v = pwordsOf (fun w : Wb D => v (.inl w)) ++ pwordsOf (fun i : Fin D.K => v (.inr i)) := by
  simp only [pwordsOf]
  rw [show (Enum.list (α := BCol (Wb D) D.K)) =
      (Enum.list (α := Wb D)).map Sum.inl ++ (Enum.list (α := Fin D.K)).map Sum.inr from rfl]
  simp [List.map_append, List.map_map, Function.comp_def]

/-- The word of `−v_B` on the column `v`. -/
noncomputable def nvW (σ : RawSec D) (v : Wb D) : List Bool :=
  subRMW D.N D.K (List.replicate (D.N * D.K) false) (encRM D.N D.K (σ.2.1.vB (.inl v)))

theorem length_nvW (σ : RawSec D) (v : Wb D) : (nvW σ v).length = D.N * D.K :=
  length_subRMW _ _ (by simp) _

theorem decRM_nvW (σ : RawSec D) (v : Wb D) : decRM D.N D.K (nvW σ v) = -σ.2.1.vB (.inl v) := by
  rw [nvW, decRM_subRMW (by simp) (length_encRM _ _ _), decRM_replicate, decRM_encRM D.K_pos,
    zero_sub]

/-- **`Ā`, `B̄⁽²⁾`, `−v̄_B`.** -/
theorem exec_prepC (σ : RawSec D) (w : St) (hT : TmplOK D w)
    (hAB : w rAB = pwordsOf σ.2.1.aB) (hB2 : w rB2 = pwordsOf σ.2.2.1)
    (hVB : w rVB = pwordsOf σ.2.1.vB) (hA : (w rAbar).length = pnE (Wb D) * (D.N * D.K))
    (hB : (w rB2bar).length = pnE (Wb D) * (D.N * D.K))
    (hN : w rNV = List.replicate (pnE (Wb D) * (D.N * D.K)) false) (hxv : (w xv).length = D.N * D.K) :
    exec D.N D.K prepC w rAbar = pwordsOf (abarR D σ) ∧
      exec D.N D.K prepC w rB2bar = pwordsOf (b2barR D σ) ∧
      exec D.N D.K prepC w rNV = ((Enum.list (α := Wb D)).map (nvW σ)).flatten ∧
      (exec D.N D.K prepC w xv).length = D.N * D.K ∧
      ∀ j, j ∉ [tmp, rAbar, rB2bar, cnt, xv, xS, rNV] → exec D.N D.K prepC w j = w j := by
  have ex : exec D.N D.K prepC w = exec D.N D.K (.rep cnt nBody)
      (exec D.N D.K (ofList [.cp tmp rAB, .mv rAbar tmp cMb, .cp tmp rB2, .mv rB2bar tmp cMb,
        .cp tmp rVB, .cp cnt xCm]) w) := rfl
  have ex1 : exec D.N D.K (ofList [.cp tmp rAB, .mv rAbar tmp cMb, .cp tmp rB2, .mv rB2bar tmp cMb,
        .cp tmp rVB, .cp cnt xCm]) w =
      Function.update (Function.update (Function.update (Function.update (Function.update
        w rAbar (pwordsOf (abarR D σ))) rB2bar (pwordsOf (b2barR D σ))) tmp (pwordsOf σ.2.1.vB))
        cnt (w xCm)) tmp (pwordsOf σ.2.1.vB) := by
    simp only [exec_ofList_cons, exec_ofList_nil, exec_cp]
    rw [exec_mv_pop (d := rAbar) (s := tmp) (c := cMb) (by decide)
      (v := pwordsOf (abarR D σ)) (L := pwordsOf (fun i : Fin D.K => σ.2.1.aB (.inr i)))
      (by simp [Function.update_apply, hA, hT.len cMb])
      (by simp [Function.update_apply, hT.len cMb, length_pwordsOf])
      (by simp [Function.update_apply, hAB]; exact pwordsOf_bcol _)]
    rw [exec_mv_pop (d := rB2bar) (s := tmp) (c := cMb) (by decide)
      (v := pwordsOf (b2barR D σ)) (L := pwordsOf (fun i : Fin D.K => σ.2.2.1 (.inr i)))
      (by simp [Function.update_apply, hB, hT.len cMb])
      (by simp [Function.update_apply, hT.len cMb, length_pwordsOf])
      (by simp [Function.update_apply, hB2]; exact pwordsOf_bcol _)]
    funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  set w1 := Function.update (Function.update (Function.update (Function.update (Function.update
        w rAbar (pwordsOf (abarR D σ))) rB2bar (pwordsOf (b2barR D σ))) tmp (pwordsOf σ.2.1.vB))
        cnt (w xCm)) tmp (pwordsOf σ.2.1.vB)
  set VW := (Enum.list (α := Wb D)).map fun v => encRM D.N D.K (σ.2.1.vB (.inl v))
  set NW := (Enum.list (α := Wb D)).map (nvW σ)
  have hVW : ∀ x ∈ VW, x.length = D.N * D.K := by
    intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _
  set rest := pwordsOf (fun i : Fin D.K => σ.2.1.vB (.inr i))
  have hstr : pwordsOf σ.2.1.vB = VW.flatten ++ rest := pwordsOf_bcol _
  let P : ℕ → St → Prop := fun i w' =>
    w' tmp = (VW.drop i).flatten ++ rest ∧ w' rNV = pbuf (w rNV) (NW.take i).flatten ∧
      (w' xv).length = D.N * D.K ∧ ∀ j, j ∉ [tmp, xv, xS, rNV] → j ≠ cnt → w' j = w1 j
  have hc : cnt ∉ wr nBody := by decide
  have h0 : P 0 w1 := ⟨by simp [w1]; exact hstr, by simp [w1, pbuf_nil],
    by simp [w1, Function.update_apply, hxv], fun _ _ _ => rfl⟩
  have hlenc : (w1 cnt).length = pnE (Wb D) := by simp [w1, hT.len xCm]
  have key := exec_rep_inv (N := D.N) (K := D.K) cnt nBody hc P w1 h0 (fun i hi w' hP _ => by
    rw [hlenc] at hi
    obtain ⟨p1, p2, p3, p4⟩ := hP
    set u := Function.update w' cnt (w' cnt).tail
    have hu : ∀ j, j ≠ cnt → u j = w' j := fun j hj => Function.update_of_ne hj _ _
    have hiV : i < VW.length := by simpa [VW] using hi
    have hCNK : (u xCNK).length = D.N * D.K := by
      rw [hu _ (by decide), p4 _ (by decide) (by decide)]; simp [w1, Function.update_apply, hT.len xCNK]
    have hZ : u xZero = List.replicate (D.N * D.K) false := by
      rw [hu _ (by decide), p4 _ (by decide) (by decide)]; simp [w1, Function.update_apply, hT.get xZero]
    have e1 := exec_mv_pop (N := D.N) (K := D.K) (d := xv) (s := tmp) (c := xCNK) (by decide) (w := u)
      (v := VW[i]) (L := (VW.drop (i + 1)).flatten ++ rest)
      (by rw [hu _ (by decide), p3, hCNK]) (by rw [hVW _ (List.getElem_mem hiV), hCNK])
      (by rw [hu _ (by decide), p1, flatten_drop_cons hiV, List.append_assoc])
    set u1 := Function.update (Function.update u tmp ((VW.drop (i + 1)).flatten ++ rest)) xv VW[i]
    have hneg : subRMW D.N D.K (opd D.N D.K (u1 xZero)) (opd D.N D.K (u1 xv)) = NW[i]'(by simpa [NW] using hi) := by
      simp only [u1, Function.update_apply]
      simp only [show (xZero = xv) = False by decide, show (xZero = tmp) = False by decide,
        if_false, if_true, hZ]
      rw [opd_eq (by simp), opd_eq (hVW _ (List.getElem_mem hiV))]
      simp [NW, VW, nvW]
    have ex2 : exec D.N D.K nBody u = exec D.N D.K (.mv rNV xS xCNK)
        (Function.update u1 xS (NW[i]'(by simpa [NW] using hi))) := by
      show exec D.N D.K (.mv rNV xS xCNK) (exec D.N D.K (.sub xS xZero xv)
        (exec D.N D.K (.mv xv tmp xCNK) u)) = _
      rw [e1]; simp only [exec]; rw [hneg]
    rw [ex2, exec_mv_blk (d := rNV) (s := xS) (c := xCNK) (by decide) (b₀ := w rNV)
      (acc := (NW.take i).flatten) (v := NW[i]'(by simpa [NW] using hi)) (L := [])
      (by simp [u1, Function.update_apply, hu, p2])
      (by simp [u1, Function.update_apply, hCNK, NW, length_nvW]) (by simp)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [u1, Function.update_apply]
    · rw [Function.update_self, ← List.flatten_concat, ← List.take_succ_eq_append_getElem]
    · simp [u1, Function.update_apply, hVW _ (List.getElem_mem hiV)]
    · intro j hj hjc
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp [u1, Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2, hu j hjc, p4 j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]) hjc])
  rw [hlenc] at key
  obtain ⟨-, k2, k3, k4⟩ := key
  rw [ex, ex1]
  have hNWl : NW.length = pnE (Wb D) := by simp [NW]
  refine ⟨?_, ?_, ?_, k3, ?_⟩
  · rw [k4 _ (by decide) (by decide)]; simp [w1, Function.update_apply]
  · rw [k4 _ (by decide) (by decide)]; simp [w1, Function.update_apply]
  · rw [k2, ← hNWl, List.take_length, pbuf_full]
    rw [hN, List.length_replicate, length_flatten_of (n := D.N * D.K), hNWl]
    intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_nvW _ _
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [k4 j (by simp [hj.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]) hj.2.2.2.1]
    simp [w1, Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1]

end AdvancedEncryption.ExpLUT.Prog.RedPubP
