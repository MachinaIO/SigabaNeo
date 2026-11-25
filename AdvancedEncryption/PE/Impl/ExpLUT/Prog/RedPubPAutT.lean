import PE.Impl.ExpLUT.Prog.RedPubPAut

/-!
# `A^aut`: the blocks and the whole (package G2, `pubP`)

* `postSpec_aut`: the post `σ_{g_t}` (template `κ_t`, `t < 32`);
* **`exec_autT`**: the block of `t`;
* **`exec_autC`**: `A^aut` (`wAaut σ`) into `rOut`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram Matrix
open AdvancedEncryption.ExpLUT.Prog.RedVM

variable {D : Dims}

theorem postSpec_aut (t : ℕ) (ht : t < 32) :
    PostSpec (D := D) (autPost t) ((setting D).E.σ ((setting D).kf t)) := by
  refine ⟨fun j hj => by simpa [autPost, wr] using hj, fun w0 hT0 w' hA hfr => ?_⟩
  have hk : (w' (kR t)).length = κD D t := by
    rw [hfr (kR t) (fun h => by
      have := List.all_eq_true.mp (show (xV :: phW).all (fun r => isT r = false) = true by decide)
        _ h
      rw [kR_isT t ht] at this; exact absurd this (by decide)), len_kR hT0 t ht]
  simp only [autPost, exec, Function.update_self, hk, opd_eq hA]
  exact ⟨length_autMW _ _ _ _ D.N_pos, by rw [decRM_autMW (κD_pos D t) hA, σ_kf]⟩

/-- The programming bits of `R^aut`, per block. -/
def zautL (σ : RawSec D) (t : Fin D.b) : List Bool :=
  ((Enum.list (α := Dig D.K)).map fun d =>
    zBlk fun c => zrR D σ (.inr (.inr (.inr (t, d, c))))).flatten

theorem pzAutW_eq (σ : RawSec D) :
    pzAutW σ = ((Enum.list (α := Fin D.b)).map (zautL σ)).flatten := by
  rw [pzAutW, pzrBlocks, enum_prod, map_product, List.flatten_flatten, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, zautL, zBlk]
  rw [enum_prod, map_product, List.flatten_flatten, List.map_map]
  rfl

theorem zautL_t (σ : RawSec D) (t : Fin D.b) :
    zautL σ t = ((Enum.list (α := Col D.K)).map fun c' => ((List.finRange D.K).map fun i =>
        zBlk fun c => zrR D σ (.inr (.inr (.inr (t, (0, c', i), c))))).flatten).flatten ++
      ((Enum.list (α := Col D.K)).map fun c' => ((List.finRange D.K).map fun i =>
        zBlk fun c => zrR D σ (.inr (.inr (.inr (t, (1, c', i), c))))).flatten).flatten := by
  rw [zautL]
  refine (dig_map (D := D) _).trans ?_
  rw [finRange_two]
  simp

theorem entW_aut (σ : RawSec D) (t : Fin D.b) (r : Fin 2) (c' : Col D.K) (i : Fin D.K) (a : Rg D)
    (ha : dautR D σ t (r, c', i) = binaryDigit a i) :
    entW ((setting D).E.σ ((setting D).kf t.val)) σ
        (fun i c => zrR D σ (.inr (.inr (.inr (t, (r, c', i), c))))) a i =
      wAautRow σ t (r, c', i) 0 ++ wAautRow σ t (r, c', i) 1 := by
  simp only [entW, rowW, wAautRow, pwordsOf, ha]
  rfl

/-- `A^aut` at a block, by rows of `C_{g_t}`. -/
theorem wAaut_t (σ : RawSec D) (t : Fin D.b) :
    ((Enum.list (α := Dig D.K)).map fun d => wAautRow σ t d 0 ++ wAautRow σ t d 1).flatten =
      ((Enum.list (α := Col D.K)).map fun c' => ((List.finRange D.K).map
        (entW ((setting D).E.σ ((setting D).kf t.val)) σ
          (fun i c => zrR D σ (.inr (.inr (.inr (t, (0, c', i), c))))) (autC0 σ t c'))).flatten).flatten ++
      ((Enum.list (α := Col D.K)).map fun c' => ((List.finRange D.K).map
        (entW ((setting D).E.σ ((setting D).kf t.val)) σ
          (fun i c => zrR D σ (.inr (.inr (.inr (t, (1, c', i), c))))) (autC1 σ t c'))).flatten).flatten := by
  rw [dig_map, finRange_two]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · exact congrArg List.flatten (List.map_congr_left fun c' _ => congrArg List.flatten
      (List.map_congr_left fun i _ => (entW_aut σ t 0 c' i _ (by rw [dautR_C]; rfl)).symm))
  · exact congrArg List.flatten (List.map_congr_left fun c' _ => congrArg List.flatten
      (List.map_congr_left fun i _ => (entW_aut σ t 1 c' i _ (by rw [dautR_C]; rfl)).symm))

/-- The registers of a block of `A^aut`. -/
def autTW : List (Fin 200) := autPreW ++ digRowW rCt ra ++ digRowW rCt2 ra

/-- **The block of `t` of `A^aut`.** -/
theorem exec_autT (σ : RawSec D) (t : Fin D.b) (ht : t.val < 32) (w : St) (hT : TmplOK D w)
    (hSk : w rSk = ((hk σ.2.1.aH).drop (t.val * 2 + 1)).flatten)
    (hSp : w rSp = ((hp σ.2.1.aH).drop (t.val * 2 + 1)).flatten)
    (hVk : w rVk = ((hk σ.2.1.vH).drop (t.val * 2 + 1)).flatten)
    (hVp : w rVp = ((hp σ.2.1.vH).drop (t.val * 2 + 1)).flatten)
    (hAbar : w rAbar = pwordsOf (abarR D σ)) (hB2bar : w rB2bar = pwordsOf (b2barR D σ))
    (hCw : (w rCw).length = D.N * D.K) (rest b₀ acc : List Bool) (hZ : w ra = zautL σ t ++ rest)
    (hO : w rOut = pbuf b₀ acc)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    let w' := exec D.N D.K (autT t.val) w
    w' rOut = pbuf b₀ (acc ++ ((Enum.list (α := Dig D.K)).map fun d =>
        wAautRow σ t d 0 ++ wAautRow σ t d 1).flatten) ∧ w' ra = rest ∧
      w' rSk = ((hk σ.2.1.aH).drop (t.val * 2 + 3)).flatten ∧
      w' rSp = ((hp σ.2.1.aH).drop (t.val * 2 + 3)).flatten ∧
      w' rVk = ((hk σ.2.1.vH).drop (t.val * 2 + 3)).flatten ∧
      w' rVp = ((hp σ.2.1.vH).drop (t.val * 2 + 3)).flatten ∧ (w' rCw).length = D.N * D.K ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      TmplOK D w' ∧ ∀ j, j ∉ autTW → w' j = w j := by
  intro w'
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := exec_autPre σ t ht w hT hSk hSp hVk hVp hv
  set w1 := exec D.N D.K (ofList (autPre t.val)) w
  have hZ' := hZ
  rw [zautL_t, List.append_assoc] at hZ'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := exec_digRow (D := D) (autPost t.val)
    ((setting D).E.σ ((setting D).kf t.val)) (postSpec_aut t.val ht) ra (Or.inr rfl) rCt
    (Or.inl rfl) σ w1 p8 (by rw [p9 _ (by decide), hAbar]) (by rw [p9 _ (by decide), hB2bar])
    (autC0 σ t) p1 (by rw [p9 _ (by decide), hCw])
    (fun c' i c => zrR D σ (.inr (.inr (.inr (t, (0, c', i), c)))))
    (((Enum.list (α := Col D.K)).map fun c' => ((List.finRange D.K).map fun i =>
        zBlk fun c => zrR D σ (.inr (.inr (.inr (t, (1, c', i), c))))).flatten).flatten ++ rest)
    b₀ acc (by rw [p9 _ (by decide)]; exact hZ') (by rw [p9 _ (by decide), hO])
    p7 (by rw [p9 _ (by decide), hb]) (by rw [p9 _ (by decide), hf])
  set w2 := exec D.N D.K (digRow rCt (autPost t.val) ra) w1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := exec_digRow (D := D) (autPost t.val)
    ((setting D).E.σ ((setting D).kf t.val)) (postSpec_aut t.val ht) ra (Or.inr rfl) rCt2
    (Or.inr rfl) σ w2 a7 (by rw [a8 _ (by decide), p9 _ (by decide), hAbar])
    (by rw [a8 _ (by decide), p9 _ (by decide), hB2bar]) (autC1 σ t)
    (by rw [a8 _ (by decide)]; exact p2) a3
    (fun c' i c => zrR D σ (.inr (.inr (.inr (t, (1, c', i), c))))) rest b₀ _ a2 a1 a4 a5 a6
  have ex : w' = exec D.N D.K (digRow rCt2 (autPost t.val) ra) w2 := by
    show exec D.N D.K (autT t.val) w = _
    rw [autT_eq, exec_ofList_append]; rfl
  have hfr : ∀ j, j ∉ autTW → w' j = w j := by
    intro j hj
    simp only [autTW, List.mem_append, not_or] at hj
    rw [ex, b8 j hj.2, a8 j hj.1.2, p9 j hj.1.1]
  refine ⟨?_, by rw [ex, b2], ?_, ?_, ?_, ?_, by rw [ex]; exact b3, by rw [ex]; exact b4,
    by rw [ex]; exact b5, by rw [ex]; exact b6, by rw [ex]; exact b7, hfr⟩
  · rw [ex, b1, List.append_assoc]
    exact congrArg (fun x => pbuf b₀ (acc ++ x)) (wAaut_t σ t).symm
  · rw [ex, b8 _ (by decide), a8 _ (by decide), p3]
  · rw [ex, b8 _ (by decide), a8 _ (by decide), p4]
  · rw [ex, b8 _ (by decide), a8 _ (by decide), p5]
  · rw [ex, b8 _ (by decide), a8 _ (by decide), p6]

/-- `A^aut`, per block. -/
noncomputable def autL (σ : RawSec D) : List (List Bool) := (Enum.list (α := Fin D.b)).map fun t =>
  ((Enum.list (α := Dig D.K)).map fun d => wAautRow σ t d 0 ++ wAautRow σ t d 1).flatten

theorem wAaut_autL (σ : RawSec D) : wAaut σ = (autL σ).flatten := by
  rw [wAaut, autL, enum_prod, map_product, List.flatten_flatten, List.map_map]
  rfl

/-- The registers `autC` writes. -/
def autCW : List (Fin 200) := [rSk, rSp, rVk, rVp] ++ autTW

/-- **`A^aut`.** -/
theorem exec_autC (hb32 : D.b ≤ 32) (σ : RawSec D) (w : St) (hT : TmplOK D w)
    (hAHk : w rAHk = ringWords (keyHL D σ.2.1.aH)) (hAHp : w rAHp = ringWords (plainHL D σ.2.1.aH))
    (hVHk : w rVHk = ringWords (keyHL D σ.2.1.vH)) (hVHp : w rVHp = ringWords (plainHL D σ.2.1.vH))
    (hAbar : w rAbar = pwordsOf (abarR D σ)) (hB2bar : w rB2bar = pwordsOf (b2barR D σ))
    (hCw : (w rCw).length = D.N * D.K) (hZ : w ra = pzAutW σ) (b₀ acc : List Bool)
    (hO : w rOut = pbuf b₀ acc)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    let w' := exec D.N D.K (autC D) w
    w' rOut = pbuf b₀ (acc ++ wAaut σ) ∧ (w' rCw).length = D.N * D.K ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      TmplOK D w' ∧ ∀ j, j ∉ autCW → w' j = w j := by
  intro w'
  set pre : List Code := [.cp rSk rAHk, .drop rSk xCNK, .cp rSp rAHp, .drop rSp xCNK,
    .cp rVk rVHk, .drop rVk xCNK, .cp rVp rVHp, .drop rVp xCNK]
  set w0 := exec D.N D.K (ofList pre) w
  have hNK : (w xCNK).length = 1 * (D.N * D.K) := by rw [hT.len xCNK, tm_xCNK, one_mul]
  have e0 : ∀ r s, (r = rSk ∧ s = rAHk) ∨ (r = rSp ∧ s = rAHp) ∨ (r = rVk ∧ s = rVHk) ∨
      (r = rVp ∧ s = rVHp) → w0 r = (w s).drop (1 * (D.N * D.K)) := by
    intro r s h
    simp only [w0, pre, exec_ofList_cons, exec_ofList_nil, exec_cp]
    rw [exec_drop_eq (by decide), exec_drop_eq (by decide), exec_drop_eq (by decide),
      exec_drop_eq (by decide)]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;>
      simp [Function.update_apply, hNK]
  have hw0 : ∀ j, j ∉ [rSk, rSp, rVk, rVp] → w0 j = w j := fun j hj =>
    exec_not_mem _ w j fun h => hj (mem_of_all (l := wr (ofList pre)) (by decide) h)
  have hT0 : TmplOK D w0 := tmplOK_frame [rSk, rSp, rVk, rVp] (by decide) hT hw0
  have hst : ∀ (L : List (List Bool)), (∀ x ∈ L, x.length = D.N * D.K) →
      L.flatten.drop (1 * (D.N * D.K)) = (L.drop (0 * 2 + 1)).flatten := fun L hL => by
    rw [flatten_drop_words L hL]
  let P : ℕ → St → Prop := fun n w2 =>
    w2 rOut = pbuf b₀ (acc ++ ((autL σ).take n).flatten) ∧
      w2 ra = (((Enum.list (α := Fin D.b)).map (zautL σ)).drop n).flatten ∧
      w2 rSk = ((hk σ.2.1.aH).drop (n * 2 + 1)).flatten ∧
      w2 rSp = ((hp σ.2.1.aH).drop (n * 2 + 1)).flatten ∧
      w2 rVk = ((hk σ.2.1.vH).drop (n * 2 + 1)).flatten ∧
      w2 rVp = ((hp σ.2.1.vH).drop (n * 2 + 1)).flatten ∧ (w2 rCw).length = D.N * D.K ∧
      (w2 xv).length = D.N * D.K ∧ (w2 xBit).length = 1 ∧ (w2 xf).length = D.N * D.K ∧
      TmplOK D w2 ∧ ∀ j, j ∉ autTW → w2 j = w0 j
  have key : ∀ n ≤ D.b, P n (exec D.N D.K (ofList (((List.finRange D.b).take n).map
      fun t => autT t.val)) w0) := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [List.take_zero, List.map_nil, exec_ofList_nil]
      refine ⟨by rw [hw0 _ (by decide), hO]; simp, by rw [hw0 _ (by decide), hZ, pzAutW_eq]; simp,
        ?_, ?_, ?_, ?_, by rw [hw0 _ (by decide), hCw], by rw [hw0 _ (by decide), hv],
        by rw [hw0 _ (by decide), hb], by rw [hw0 _ (by decide), hf], hT0, fun _ _ => rfl⟩
      · rw [e0 _ _ (Or.inl ⟨rfl, rfl⟩), hAHk, ringWords_hlW]; exact hst _ (length_hlW _)
      · rw [e0 _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩)), hAHp, ringWords_hlW]; exact hst _ (length_hlW _)
      · rw [e0 _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), hVHk, ringWords_hlW]
        exact hst _ (length_hlW _)
      · rw [e0 _ _ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))), hVHp, ringWords_hlW]
        exact hst _ (length_hlW _)
    | succ n ih =>
      intro hn
      obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ := ih (by omega)
      have hnl : n < (List.finRange D.b).length := by simp; omega
      rw [List.take_succ_eq_append_getElem hnl, List.map_append, exec_ofList_append,
        List.map_singleton, exec_ofList_single]
      set w2 := exec D.N D.K (ofList (((List.finRange D.b).take n).map fun t => autT t.val)) w0
      have hfn : (List.finRange D.b)[n] = ⟨n, by omega⟩ := by simp
      rw [hfn]
      have hZl : n < ((Enum.list (α := Fin D.b)).map (zautL σ)).length := by simp [enum_fin]; omega
      have hAl : n < (autL σ).length := by simp [autL, enum_fin]; omega
      have hen : (Enum.list (α := Fin D.b))[n]'(by simp [enum_fin]; omega) = ⟨n, by omega⟩ := by
        simp [enum_fin]
      obtain ⟨r1', r2', r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := exec_autT (D := D) σ ⟨n, by omega⟩
        (by show n < 32; omega) w2 q11 q3 q4 q5 q6
        (by rw [q12 _ (by decide), hw0 _ (by decide), hAbar])
        (by rw [q12 _ (by decide), hw0 _ (by decide), hB2bar]) q7
        ((((Enum.list (α := Fin D.b)).map (zautL σ)).drop (n + 1)).flatten) b₀ _
        (by rw [q2, flatten_drop_cons hZl]; simp [hen]) q1 q8 q9 q10
      refine ⟨?_, r2', ?_, ?_, ?_, ?_, r7, r8, r9, r10, r11, fun j hj => by rw [r12 j hj, q12 j hj]⟩
      · rw [r1', List.take_succ_eq_append_getElem hAl, List.flatten_append, List.flatten_singleton,
          List.append_assoc]
        simp [autL, hen]
      · rw [r3]; exact congrArg (fun m => ((hk σ.2.1.aH).drop m).flatten) (by show n * 2 + 3 = (n + 1) * 2 + 1; ring)
      · rw [r4]; exact congrArg (fun m => ((hp σ.2.1.aH).drop m).flatten) (by show n * 2 + 3 = (n + 1) * 2 + 1; ring)
      · rw [r5]; exact congrArg (fun m => ((hk σ.2.1.vH).drop m).flatten) (by show n * 2 + 3 = (n + 1) * 2 + 1; ring)
      · rw [r6]; exact congrArg (fun m => ((hp σ.2.1.vH).drop m).flatten) (by show n * 2 + 3 = (n + 1) * 2 + 1; ring)
  obtain ⟨k1, -, -, -, -, -, k7, k8, k9, k10, k11, k12⟩ := key D.b le_rfl
  rw [List.take_of_length_le (l := autL σ) (by simp [autL, enum_fin])] at k1
  rw [List.take_of_length_le (l := List.finRange D.b) (by simp)] at k1 k7 k8 k9 k10 k11 k12
  have ex : w' = exec D.N D.K (ofList ((List.finRange D.b).map fun t => autT t.val)) w0 := by
    show exec D.N D.K (ofList (pre ++ (List.finRange D.b).map fun t => autT t.val)) w = _
    rw [exec_ofList_append]
  rw [ex]
  refine ⟨by rw [k1, wAaut_autL], k7, k8, k9, k10, k11, fun j hj => ?_⟩
  simp only [autCW, List.mem_append, not_or] at hj
  rw [k12 j hj.2, hw0 j hj.1]

end AdvancedEncryption.ExpLUT.Prog.RedPubP
