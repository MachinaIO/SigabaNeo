import PE.Impl.ExpLUT.Prog.RedPubPDig

/-!
# `A^in` (package G2, `pubP`)

* list identities: `dig_map` (the enumeration of `Dig`), **`wAin_eq`** (`wAin` per position, per
  row `r` of `C^in_t`, per entry, per digit), `pzRinW_eq`;
* **`exec_inT`**: one position;
* **`exec_ainC`**: `A^in` (`wAin σ`) into `rOut`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram Matrix
open AdvancedEncryption.ExpLUT.Prog.RedVM

variable {D : Dims}

/-! ### Lists along `Dig` -/

/-- **The enumeration of the digits**: `r` outer, then the entry `c'`, then `i`. -/
theorem dig_map {β : Type} (F : Dig D.K → List β) :
    ((Enum.list (α := Dig D.K)).map F).flatten =
      ((List.finRange 2).map fun r => ((Enum.list (α := Col D.K)).map fun c' =>
        ((List.finRange D.K).map fun i => F (r, c', i)).flatten).flatten).flatten := by
  rw [show (Enum.list (α := Dig D.K)) = (List.finRange 2).product
      ((Enum.list (α := Col D.K)).product (List.finRange D.K)) from rfl,
    map_product, List.flatten_flatten, List.map_map]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply]
  rw [map_product, List.flatten_flatten, List.map_map]
  rfl

/-- The programming bits of `R^in`, per position. -/
def zinL (σ : RawSec D) (t : Pos) : List Bool :=
  ((Enum.list (α := Dig D.K)).map fun d =>
    zBlk fun c => zrR D σ (.inr (.inr (.inl (t, d, c))))).flatten

theorem pzRinW_eq (σ : RawSec D) : pzRinW σ = ((Enum.list (α := Pos)).map (zinL σ)).flatten := by
  rw [pzRinW, pzrBlocks, enum_prod, map_product, List.flatten_flatten, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, zinL, zBlk]
  rw [enum_prod, map_product, List.flatten_flatten, List.map_map]
  rfl

/-- The block of a digit of `A^in` as the output of `entW`. -/
theorem entW_in (σ : RawSec D) (t : Pos) (r : Fin 2) (c' : Col D.K) (i : Fin D.K) :
    entW id σ (fun i c => zrR D σ (.inr (.inr (.inl (t, (r, c', i), c)))))
        (if r = 0 then aR D σ t c' else cbR D σ t c') i =
      wAinRow σ t (r, c', i) 0 ++ wAinRow σ t (r, c', i) 1 := by
  simp only [entW, rowW, wAinRow, pwordsOf, dinR_apply, id]
  rfl

/-- `A^in` at a position, by rows of `C^in_t`. -/
theorem wAin_t (σ : RawSec D) (t : Pos) :
    ((Enum.list (α := Dig D.K)).map fun d => wAinRow σ t d 0 ++ wAinRow σ t d 1).flatten =
      ((Enum.list (α := Col D.K)).map fun c' => ((List.finRange D.K).map
        (entW id σ (fun i c => zrR D σ (.inr (.inr (.inl (t, (0, c', i), c))))) (aR D σ t c'))).flatten).flatten ++
      ((Enum.list (α := Col D.K)).map fun c' => ((List.finRange D.K).map
        (entW id σ (fun i c => zrR D σ (.inr (.inr (.inl (t, (1, c', i), c))))) (cbR D σ t c'))).flatten).flatten := by
  rw [dig_map, finRange_two]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  congr 1

theorem zinL_t (σ : RawSec D) (t : Pos) :
    zinL σ t = ((Enum.list (α := Col D.K)).map fun c' => ((List.finRange D.K).map fun i =>
        zBlk fun c => zrR D σ (.inr (.inr (.inl (t, (0, c', i), c))))).flatten).flatten ++
      ((Enum.list (α := Col D.K)).map fun c' => ((List.finRange D.K).map fun i =>
        zBlk fun c => zrR D σ (.inr (.inr (.inl (t, (1, c', i), c))))).flatten).flatten := by
  rw [zinL]
  refine (dig_map (D := D) _).trans ?_
  rw [finRange_two]
  simp

/-- The registers of a position of `A^in`. -/
def inTW : List (Fin 200) := rCt :: rCt2 :: rSA :: rSC :: digRowW rCt rRin ++ digRowW rCt2 rRin

/-- **One position of `A^in`.** -/
theorem exec_inT (σ : RawSec D) (t : Pos) (w : St) (hT : TmplOK D w)
    (hAbar : w rAbar = pwordsOf (abarR D σ)) (hB2bar : w rB2bar = pwordsOf (b2barR D σ))
    (restA restC rest b₀ acc : List Bool)
    (hSA : w rSA = ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (aR D σ t c)).flatten ++ restA)
    (hSC : w rSC = ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (cbR D σ t c)).flatten ++ restC)
    (hCw : (w rCw).length = D.N * D.K) (hZ : w rRin = zinL σ t ++ rest) (hO : w rOut = pbuf b₀ acc)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    let w' := exec D.N D.K inT w
    w' rOut = pbuf b₀ (acc ++ ((Enum.list (α := Dig D.K)).map fun d =>
        wAinRow σ t d 0 ++ wAinRow σ t d 1).flatten) ∧
      w' rRin = rest ∧ w' rSA = restA ∧ w' rSC = restC ∧ (w' rCw).length = D.N * D.K ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      TmplOK D w' ∧ ∀ j, j ∉ inTW → w' j = w j := by
  intro w'
  set Aw := ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (aR D σ t c)).flatten
  set Cw := ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (cbR D σ t c)).flatten
  have hAwl : Aw.length = pnE (Col D.K) * (D.N * D.K) := length_rowW _
  have hCwl : Cw.length = pnE (Col D.K) * (D.N * D.K) := length_rowW _
  have hzc : (w rZcol).length = pnE (Col D.K) * (D.N * D.K) := by rw [hT.len rZcol, tm_rZcol]
  set w1 := Function.update (Function.update (Function.update (Function.update w rSA restA) rCt Aw)
    rSC restC) rCt2 Cw
  have e1 : exec D.N D.K (ofList [.cp rCt rZcol, .mv rCt rSA cColW, .cp rCt2 rZcol,
      .mv rCt2 rSC cColW]) w = w1 := by
    simp only [exec_ofList_cons, exec_ofList_nil, exec_cp]
    rw [exec_mv_blk (d := rCt) (s := rSA) (c := cColW) (by decide) (b₀ := w rZcol) (acc := [])
      (v := Aw) (L := restA) (by simp [Function.update_apply, pbuf_nil])
      (by simp [Function.update_apply, hAwl, hT.len cColW]) (by simp [Function.update_apply, hSA])]
    rw [exec_mv_blk (d := rCt2) (s := rSC) (c := cColW) (by decide) (b₀ := w rZcol) (acc := [])
      (v := Cw) (L := restC) (by simp [Function.update_apply, pbuf_nil])
      (by simp [Function.update_apply, hCwl, hT.len cColW]) (by simp [Function.update_apply, hSC])]
    rw [List.nil_append, List.nil_append, pbuf_full (by rw [hzc, hAwl]),
      pbuf_full (by rw [hzc, hCwl])]
    funext j
    simp only [w1, Function.update_apply]
    split_ifs <;> simp_all
  have hw1 : ∀ j, j ∉ [rSA, rCt, rSC, rCt2] → w1 j = w j := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [w1, Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]
  have hT1 : TmplOK D w1 := tmplOK_frame [rSA, rCt, rSC, rCt2] (by decide) hT hw1
  have hZ' := hZ
  rw [zinL_t, List.append_assoc] at hZ'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := exec_digRow (D := D) cpPost id postSpec_cp rRin
    (Or.inl rfl) rCt (Or.inl rfl) σ w1 hT1 (by rw [hw1 _ (by decide), hAbar])
    (by rw [hw1 _ (by decide), hB2bar]) (fun c' => aR D σ t c') (by simp [w1, Function.update_apply]; rfl)
    (by rw [hw1 _ (by decide), hCw]) (fun c' i c => zrR D σ (.inr (.inr (.inl (t, (0, c', i), c)))))
    (((Enum.list (α := Col D.K)).map fun c' => ((List.finRange D.K).map fun i =>
        zBlk fun c => zrR D σ (.inr (.inr (.inl (t, (1, c', i), c))))).flatten).flatten ++ rest)
    b₀ acc (by rw [hw1 _ (by decide)]; exact hZ') (by rw [hw1 _ (by decide), hO])
    (by rw [hw1 _ (by decide), hv]) (by rw [hw1 _ (by decide), hb]) (by rw [hw1 _ (by decide), hf])
  set w2 := exec D.N D.K (digRow rCt cpPost rRin) w1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := exec_digRow (D := D) cpPost id postSpec_cp rRin
    (Or.inl rfl) rCt2 (Or.inr rfl) σ w2 a7
    (by rw [a8 _ (by decide), hw1 _ (by decide), hAbar])
    (by rw [a8 _ (by decide), hw1 _ (by decide), hB2bar]) (fun c' => cbR D σ t c')
    (by rw [a8 _ (by decide)]; simp [w1, Function.update_apply]; rfl)
    a3 (fun c' i c => zrR D σ (.inr (.inr (.inl (t, (1, c', i), c))))) rest b₀ _ a2 a1 a4 a5 a6
  have ex : w' = exec D.N D.K (digRow rCt2 cpPost rRin) w2 := by
    show exec D.N D.K (ofList ([.cp rCt rZcol, .mv rCt rSA cColW, .cp rCt2 rZcol,
      .mv rCt2 rSC cColW] ++ [digRow rCt cpPost rRin, digRow rCt2 cpPost rRin])) w = _
    rw [exec_ofList_append, e1]; rfl
  have hfr : ∀ j, j ∉ inTW → w' j = w j := by
    intro j hj
    simp only [inTW, List.mem_cons, List.mem_append, not_or] at hj
    obtain ⟨⟨j1, j2, j3, j4, j5⟩, j6⟩ := hj
    rw [ex, b8 j j6, a8 j j5, hw1 j (by simp [j1, j2, j3, j4])]
  refine ⟨?_, by rw [ex, b2], ?_, ?_, by rw [ex]; exact b3, by rw [ex]; exact b4, by rw [ex]; exact b5,
    by rw [ex]; exact b6, by rw [ex]; exact b7, hfr⟩
  · rw [ex, b1, List.append_assoc]
    exact congrArg (fun x => pbuf b₀ (acc ++ x)) (wAin_t σ t).symm
  · rw [ex, b8 _ (by decide), a8 _ (by decide)]; simp [w1, Function.update_apply]
  · rw [ex, b8 _ (by decide), a8 _ (by decide)]; simp [w1, Function.update_apply]

/-- `A^in`, per position. -/
noncomputable def ainL (σ : RawSec D) : List (List Bool) := (Enum.list (α := Pos)).map fun t =>
  ((Enum.list (α := Dig D.K)).map fun d => wAinRow σ t d 0 ++ wAinRow σ t d 1).flatten

theorem wAin_ainL (σ : RawSec D) : wAin σ = (ainL σ).flatten := by
  rw [wAin, ainL, enum_prod, map_product, List.flatten_flatten, List.map_map]
  rfl

/-- The registers `ainC` writes. -/
def ainW : List (Fin 200) := rSA :: rSC :: cntP :: inTW

/-- **`A^in`.** -/
theorem exec_ainC (σ : RawSec D) (w : St) (hT : TmplOK D w)
    (hAbar : w rAbar = pwordsOf (abarR D σ)) (hB2bar : w rB2bar = pwordsOf (b2barR D σ))
    (hKA : w rKA = wa σ) (hKC : w rKC = (cWL σ).flatten) (hCw : (w rCw).length = D.N * D.K)
    (hZ : w rRin = pzRinW σ) (b₀ acc : List Bool) (hO : w rOut = pbuf b₀ acc)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    let w' := exec D.N D.K ainC w
    w' rOut = pbuf b₀ (acc ++ wAin σ) ∧ (w' rCw).length = D.N * D.K ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      TmplOK D w' ∧ ∀ j, j ∉ ainW → w' j = w j := by
  intro w'
  set w0 := Function.update (Function.update (Function.update w rSA (w rKA)) rSC
    (Function.update w rSA (w rKA) rKC)) cntP (Function.update (Function.update w rSA (w rKA)) rSC
    (Function.update w rSA (w rKA) rKC) cPos)
  have hw0 : ∀ j, j ∉ [rSA, rSC, cntP] → w0 j = w j := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [w0, Function.update_apply, hj.1, hj.2.1, hj.2.2]
  have hT0 : TmplOK D w0 := tmplOK_frame [rSA, rSC, cntP] (by decide) hT hw0
  have ex : w' = exec D.N D.K (.rep cntP inT) w0 := rfl
  have hcw : cntP ∉ wr inT := by decide
  let P : ℕ → St → Prop := fun k w2 =>
    w2 rOut = pbuf b₀ (acc ++ ((ainL σ).take k).flatten) ∧ w2 rSA = ((aWL σ).drop k).flatten ∧
      w2 rSC = ((cWL σ).drop k).flatten ∧
      w2 rRin = (((Enum.list (α := Pos)).map (zinL σ)).drop k).flatten ∧
      (w2 rCw).length = D.N * D.K ∧ (w2 xv).length = D.N * D.K ∧ (w2 xBit).length = 1 ∧
      (w2 xf).length = D.N * D.K ∧ TmplOK D w2 ∧ ∀ j, j ∉ inTW → j ≠ cntP → w2 j = w0 j
  have h0 : P 0 w0 := ⟨by rw [hw0 _ (by decide), hO]; simp,
    by simp [w0, Function.update_apply, hKA, wa_aWL], by simp [w0, Function.update_apply, hKC],
    by rw [hw0 _ (by decide), hZ, pzRinW_eq]; simp, by rw [hw0 _ (by decide), hCw],
    by rw [hw0 _ (by decide), hv], by rw [hw0 _ (by decide), hb], by rw [hw0 _ (by decide), hf],
    hT0, fun _ _ _ => rfl⟩
  have hlen : (w0 cntP).length = pnE Pos := by simp [w0, hT.len cPos]
  have key := exec_rep_inv (N := D.N) (K := D.K) cntP inT hcw P w0 h0 (fun k hk w2 hP _ => by
    rw [hlen] at hk
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := hP
    set u := Function.update w2 cntP (w2 cntP).tail
    have hu : ∀ j, j ≠ cntP → u j = w2 j := fun j hj => Function.update_of_ne hj _ _
    have hTu : TmplOK D u := tmplOK_frame [cntP] (by decide) p9 fun j hj =>
      hu j (fun h => hj (by simp [h]))
    have hk16 : k < 16 := by rw [len_pos16] at hk; exact hk
    have hep := enum_pos_getElem k hk
    have hkA : k < (aWL σ).length := by simpa [aWL] using hk
    have hkC : k < (cWL σ).length := by simpa [cWL] using hk
    have hkZ : k < ((Enum.list (α := Pos)).map (zinL σ)).length := by simpa using hk
    have hkL : k < (ainL σ).length := by simpa [ainL] using hk
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ := exec_inT (D := D) σ ⟨k, hk16⟩ u hTu
      (by rw [hu _ (by decide), p10 _ (by decide) (by decide), hw0 _ (by decide), hAbar])
      (by rw [hu _ (by decide), p10 _ (by decide) (by decide), hw0 _ (by decide), hB2bar])
      ((aWL σ).drop (k + 1)).flatten ((cWL σ).drop (k + 1)).flatten
      ((((Enum.list (α := Pos)).map (zinL σ)).drop (k + 1)).flatten) b₀ _
      (by rw [hu _ (by decide), p2, flatten_drop_cons hkA]; simp [aWL, hep])
      (by rw [hu _ (by decide), p3, flatten_drop_cons hkC]; simp [cWL, hep])
      (by rw [hu _ (by decide), p5])
      (by rw [hu _ (by decide), p4, flatten_drop_cons hkZ]; simp [hep])
      (by rw [hu _ (by decide), p1]) (by rw [hu _ (by decide), p6]) (by rw [hu _ (by decide), p7])
      (by rw [hu _ (by decide), p8])
    refine ⟨?_, q3, q4, q2, q5, q6, q7, q8, q9, fun j h1 h2 => by rw [q10 j h1, hu j h2, p10 j h1 h2]⟩
    rw [q1, List.take_succ_eq_append_getElem hkL, List.flatten_append, List.flatten_singleton,
      List.append_assoc]
    simp [ainL, hep])
  rw [hlen] at key
  obtain ⟨k1, -, -, -, k5, k6, k7, k8, k9, k10⟩ := key
  rw [List.take_of_length_le (by simp [ainL])] at k1
  rw [ex]
  refine ⟨by rw [k1, wAin_ainL], k5, k6, k7, k8, k9, fun j hj => ?_⟩
  simp only [ainW, List.mem_cons, not_or] at hj
  rw [k10 j hj.2.2.2 hj.2.2.1, hw0 j (by simp [hj.1, hj.2.1, hj.2.2.1])]

end AdvancedEncryption.ExpLUT.Prog.RedPubP
