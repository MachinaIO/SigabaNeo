import PE.Impl.ExpLUT.Prog.RedPubPA

/-!
# Rows into the output; `a` and `A₀` (package G2, `pubP`)

* **`exec_rowPush`**: `rowSetC v z p; rowC m ρ; mv rOut xOut cColW` shifts the words
  `ψ(f ⬝ᵥ bv (g c)) + u G_{ρ c}` (`c ∈ Col`, zero addends) into `rOut`;
* **`exec_aPhC`**: `a` (`wa`) into `rOut`, `rKA = wa σ`, `rKC` the words of the `cb_t`;
* **`exec_a0C`**: `A₀` (`wA0row σ 0 ++ wA0row σ 1`) into `rOut`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram Matrix
open AdvancedEncryption.ExpLUT.Prog.RedVM

variable {D : Dims}

/-- A row of hashes pushed into the output. -/
def rowPush (v z p : Fin 200) (m : Code) (ρ : Fin 2) : List Code :=
  [rowSetC v z p, rowC m ρ, .mv rOut xOut cColW]

/-- The registers of a pushed row. -/
def rowPushW : List (Fin 200) := rOut :: xV :: phW

/-- **A row of hashes into the output.** -/
theorem exec_rowPush (v z p : Fin 200) (hz : z ≠ xV) (hp1 : p ≠ xV) (hp2 : p ≠ xZ) (hp3 : p ≠ xF)
    (hp4 : p ≠ xOut) (m : Code) (ρ : Fin 2) (ψ : Rg D → Rg D) (hwm : ∀ j ∈ wr m, j = xH) (w : St)
    (hT : TmplOK D w)
    (hm : ∀ w' : St, (w' xAcc).length = D.N * D.K → (∀ j, j ∉ xV :: phW → w' j = w j) →
      (exec D.N D.K m w' xH).length = D.N * D.K ∧
        decRM D.N D.K (exec D.N D.K m w' xH) = ψ (decRM D.N D.K (w' xAcc)))
    (f : Wb D → Rg D) (vs : Wb D → List Bool) (hvs : ∀ v, (vs v).length = D.N * D.K)
    (hvf : ∀ v, decRM D.N D.K (vs v) = f v) (g : Col D.K → Wb D → Bool) (u : Rg D)
    (rest b₀ acc : List Bool)
    (hV : w v = ((Enum.list (α := Wb D)).map vs).flatten)
    (hZ : w z = ((Enum.list (α := Col D.K)).map fun c => (Enum.list (α := Wb D)).map (g c)).flatten ++
      rest)
    (hPl : (w p).length = D.N * D.K) (hPv : decRM D.N D.K (w p) = u)
    (hO : w rOut = pbuf b₀ acc)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    let w' := exec D.N D.K (ofList (rowPush v z p m ρ)) w
    w' rOut = pbuf b₀ (acc ++ ((Enum.list (α := Col D.K)).map fun c =>
        encRM D.N D.K (ψ (f ⬝ᵥ bv (g c)) + u * (setting D).G ρ c)).flatten) ∧
      w' xZ = rest ∧ (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧
      (w' xf).length = D.N * D.K ∧ TmplOK D w' ∧ ∀ j, j ∉ rowPushW → w' j = w j := by
  intro w'
  have e1 := exec_rowSetC (D := D) v z p hz hp1 hp2 hp3 hp4 w
  set w1 := exec D.N D.K (rowSetC v z p) w
  have hw1 : ∀ j, j ∉ [xV, xZ, xF, xOut, xP] → w1 j = w j := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [e1]; simp [Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2]
  have hT1 : TmplOK D w1 := tmplOK_frame [xV, xZ, xF, xOut, xP] (by decide) hT hw1
  have hzc : w rZcol = ((Enum.list (α := Col D.K)).map fun _ =>
      List.replicate (D.N * D.K) false).flatten := by rw [hT.get rZcol, tm_rZcol, replicate_col]
  have hph1 : ∀ j, j ∉ phW → j ∉ [xV, xZ, xF, xOut, xP] → w1 j = w j := fun j _ h => hw1 j h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := exec_rowC (D := D) ρ m ψ hwm w1
    (fun w' hA hfr => hm w' hA fun j hj => by
      have hj1 : j ∉ phW := fun h => hj (List.mem_cons_of_mem _ h)
      have hj2 : j ≠ xV := fun h => hj (by simp [h])
      rw [hfr j hj1, hw1 j (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hj2, fun h => hj1 (by rw [h]; decide), fun h => hj1 (by rw [h]; decide),
          fun h => hj1 (by rw [h]; decide), fun h => hj1 (by rw [h]; decide)⟩)])
    f vs hvs hvf g (fun _ => 0) (fun _ => List.replicate (D.N * D.K) false) (fun _ => by simp)
    (fun _ => decRM_replicate _ _) u rest []
    (by rw [e1]; simp [Function.update_apply, hz, hV])
    (by rw [e1]; simp [Function.update_apply, hZ])
    (by rw [e1]; simp [Function.update_apply, hzc])
    (by rw [e1]; simp [Function.update_apply, hT.len rZcol, pnE_col])
    (by rw [e1]; simp [Function.update_apply, hp1, hp2, hp3, hp4, hPl])
    (by rw [e1]; simp [Function.update_apply, hp1, hp2, hp3, hp4, hPv])
    (by rw [hT1.len cK, tm_cK]) (by rw [hT1.len xCm]; rfl) (by rw [hT1.len xC1]; rfl)
    (by rw [hT1.len xCNK]; rfl) (by rw [hT1.get xZero]; rfl)
    (by rw [hw1 _ (by decide), hv]) (by rw [hw1 _ (by decide), hb]) (by rw [hw1 _ (by decide), hf])
  set w2 := exec D.N D.K (rowC m ρ) w1
  have hT2 : TmplOK D w2 := tmplOK_frame phW (by decide) hT1 a7
  set R := ((Enum.list (α := Col D.K)).map fun c =>
    encRM D.N D.K (ψ (f ⬝ᵥ bv (g c)) + u * (setting D).G ρ c + 0)).flatten with hR
  have e3 := exec_mv_blk (N := D.N) (K := D.K) (d := rOut) (s := xOut) (c := cColW) (by decide)
    (w := w2) (b₀ := b₀) (acc := acc) (v := R) (L := [])
    (by rw [a7 _ (by decide), hw1 _ (by decide), hO])
    (by rw [hT2.len cColW, tm_cColW]; exact length_rowW _) (by rw [a1, List.append_nil])
  have ex : w' = Function.update (Function.update w2 xOut []) rOut (pbuf b₀ (acc ++ R)) := by
    show exec D.N D.K (.seq (rowC m ρ) (.seq (.mv rOut xOut cColW) .nop)) w1 = _
    show exec D.N D.K (.mv rOut xOut cColW) w2 = _
    exact e3
  have hfr : ∀ j, j ∉ rowPushW → w' j = w j := by
    intro j hj
    have hj1 : j ∉ phW := fun h => hj (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    have hjO : j ≠ rOut := fun h => hj (by simp [rowPushW, h])
    have hjV : j ≠ xV := fun h => hj (by simp [rowPushW, h])
    rw [ex, Function.update_of_ne hjO, Function.update_of_ne (fun h => hj1 (by rw [h]; decide)),
      a7 j hj1, hw1 j (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hjV, fun h => hj1 (by rw [h]; decide), fun h => hj1 (by rw [h]; decide),
          fun h => hj1 (by rw [h]; decide), fun h => hj1 (by rw [h]; decide)⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, tmplOK_frame rowPushW (by decide) hT hfr, hfr⟩
  · rw [ex, Function.update_self, hR]; simp only [add_zero]
  · rw [ex, Function.update_of_ne (by decide), Function.update_of_ne (by decide), a2]
  · rw [ex, Function.update_of_ne (by decide), Function.update_of_ne (by decide), a4]
  · rw [ex, Function.update_of_ne (by decide), Function.update_of_ne (by decide), a5]
  · rw [ex, Function.update_of_ne (by decide), Function.update_of_ne (by decide), a6]

/-! ### `a` and `A₀` -/

/-- The registers `aPhC` writes. -/
def aPhW : List (Fin 200) := tmp :: rOut :: aLoopW

/-- **`a`**, keeping the rows `a_t` and `cb_t`. -/
theorem exec_aPhC (hN : 2 ≤ D.N) (hW : wSt * 2 ^ 7 ≤ 2 * D.N) (σ : RawSec D) (w : St)
    (hT : TmplOK D w) (hA : w rAttr = encAttribute w8 σ.1) (hBit : (w rBit).length = 1)
    (hAbar : w rAbar = pwordsOf (abarR D σ))
    (hNV : w rNV = ((Enum.list (α := Wb D)).map (nvW σ)).flatten)
    (hZ : w rZ = pzZW σ) (hFe : w rFe = pfl2W σ)
    (hKA : (w rKA).length = pnE Pos * (pnE (Col D.K) * (D.N * D.K)))
    (hKC : (w rKC).length = pnE Pos * (pnE (Col D.K) * (D.N * D.K)))
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K)
    (b₀ acc : List Bool) (hO : w rOut = pbuf b₀ acc) :
    let w' := exec D.N D.K aPhC w
    w' rOut = pbuf b₀ (acc ++ wa σ) ∧ w' rKA = wa σ ∧ w' rKC = (cWL σ).flatten ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      TmplOK D w' ∧ ∀ j, j ∉ aPhW → w' j = w j := by
  intro w'
  set w0 := Function.update w cntP (w cPos)
  have hw0 : ∀ j, j ≠ cntP → w0 j = w j := fun j hj => Function.update_of_ne hj _ _
  have hT0 : TmplOK D w0 := tmplOK_frame [cntP] (by decide) hT fun j hj =>
    hw0 j (fun h => hj (by simp [h]))
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := exec_aLoop (D := D) hN hW σ w0 hT0
    (by rw [hw0 _ (by decide), hA]) (by rw [hw0 _ (by decide), hBit])
    (by rw [hw0 _ (by decide), hAbar]) (by rw [hw0 _ (by decide), hNV])
    (by rw [hw0 _ (by decide), hZ]) (by rw [hw0 _ (by decide), hFe])
    (by rw [hw0 _ (by decide), hKA]) (by rw [hw0 _ (by decide), hKC])
    (by rw [hw0 _ (by decide), hv]) (by rw [hw0 _ (by decide), hb]) (by rw [hw0 _ (by decide), hf])
    (by simp [w0, hT.len cPos])
  set w1 := exec D.N D.K (.rep cntP aBody) w0
  have hlwa : (wa σ).length = pnE Pos * (pnE (Col D.K) * (D.N * D.K)) := by
    rw [wa_aWL, length_flatten_of (n := pnE (Col D.K) * (D.N * D.K))]
    · simp [aWL]
    · intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_rowW _
  have e3 := exec_mv_blk (N := D.N) (K := D.K) (d := rOut) (s := tmp) (c := cPC) (by decide)
    (w := Function.update w1 tmp (w1 rKA)) (b₀ := b₀) (acc := acc) (v := wa σ) (L := [])
    (by rw [Function.update_of_ne (by decide), k7 _ (by decide), hw0 _ (by decide), hO])
    (by rw [Function.update_of_ne (by decide), k6.len cPC, tm_cPC, hlwa])
    (by rw [Function.update_self, k1, List.append_nil])
  have ex : w' = Function.update (Function.update (Function.update w1 tmp (w1 rKA)) tmp []) rOut
      (pbuf b₀ (acc ++ wa σ)) := by
    show exec D.N D.K (.mv rOut tmp cPC) (exec D.N D.K (.cp tmp rKA) w1) = _
    rw [exec_cp, e3]
  have hfr : ∀ j, j ∉ aPhW → w' j = w j := by
    intro j hj
    simp only [aPhW, List.mem_cons, not_or] at hj
    rw [ex, Function.update_of_ne hj.2.1, Function.update_of_ne hj.1, Function.update_of_ne hj.1,
      k7 j hj.2.2, hw0 j (fun h => hj.2.2 (by simp [aLoopW, h]))]
  refine ⟨by rw [ex, Function.update_self], ?_, ?_, ?_, ?_, ?_,
    tmplOK_frame aPhW (by decide) hT hfr, hfr⟩
  · rw [ex]; simp [Function.update_apply, k1]
  · rw [ex]; simp [Function.update_apply, k2]
  · rw [ex]; simp [Function.update_apply, k3]
  · rw [ex]; simp [Function.update_apply, k4]
  · rw [ex]; simp [Function.update_apply, k5]

theorem bbR_zero (σ : RawSec D) : bbR D σ 0 = abarR D σ := rfl
theorem bbR_one (σ : RawSec D) : bbR D σ 1 = b2barR D σ := rfl

theorem pzR0W_eq (σ : RawSec D) : pzR0W σ =
    ((Enum.list (α := Col D.K)).map fun c => (Enum.list (α := Wb D)).map
      (zrR D σ (.inr (.inl c)))).flatten := rfl

/-- **`A₀`.** -/
theorem exec_a0C (σ : RawSec D) (w : St) (hT : TmplOK D w)
    (hAbar : w rAbar = pwordsOf (abarR D σ)) (hB2bar : w rB2bar = pwordsOf (b2barR D σ))
    (hR0 : w rR0 = pzR0W σ)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K)
    (b₀ acc : List Bool) (hO : w rOut = pbuf b₀ acc) :
    let w' := exec D.N D.K a0C w
    w' rOut = pbuf b₀ (acc ++ (wA0row σ 0 ++ wA0row σ 1)) ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      TmplOK D w' ∧ ∀ j, j ∉ rowPushW → w' j = w j := by
  intro w'
  have hr1l : (w r1).length = D.N * D.K := by
    rw [hT.2]; simp; have := Nat.mul_pos D.N_pos D.K_pos; omega
  have hr1v : decRM D.N D.K (w r1) = 1 := by rw [hT.2, decRM_r1]
  obtain ⟨a1, -, a3, a4, a5, a6, a7⟩ := exec_rowPush (D := D) rAbar rR0 r1 (by decide) (by decide)
    (by decide) (by decide) (by decide) cpPost 0 id wr_cpPost' w hT
    (fun w' hA _ => hm_cpPost w' w' hA (fun _ _ => rfl))
    (abarR D σ) (fun v => encRM D.N D.K (abarR D σ v)) (fun _ => length_encRM _ _ _)
    (fun _ => decRM_encRM D.K_pos _) (fun c => zrR D σ (.inr (.inl c))) 1 [] b₀ acc
    (by rw [hAbar]; rfl) (by rw [hR0, List.append_nil]; rfl) hr1l hr1v hO hv hb hf
  set w1 := exec D.N D.K (ofList (rowPush rAbar rR0 r1 cpPost 0)) w
  obtain ⟨b1, -, b3, b4, b5, b6, b7⟩ := exec_rowPush (D := D) rB2bar rR0 r1 (by decide) (by decide)
    (by decide) (by decide) (by decide) cpPost 1 id wr_cpPost' w1 a6
    (fun w' hA _ => hm_cpPost w' w' hA (fun _ _ => rfl))
    (b2barR D σ) (fun v => encRM D.N D.K (b2barR D σ v)) (fun _ => length_encRM _ _ _)
    (fun _ => decRM_encRM D.K_pos _) (fun c => zrR D σ (.inr (.inl c))) 1 [] b₀ _
    (by rw [a7 _ (by decide), hB2bar]; rfl) (by rw [a7 _ (by decide), hR0, List.append_nil]; rfl)
    (by rw [a7 _ (by decide), hr1l]) (by rw [a7 _ (by decide), hr1v]) a1 a3 a4 a5
  have ex : w' = exec D.N D.K (ofList (rowPush rB2bar rR0 r1 cpPost 1)) w1 := by
    show exec D.N D.K (ofList (rowPush rAbar rR0 r1 cpPost 0 ++ rowPush rB2bar rR0 r1 cpPost 1)) w = _
    rw [exec_ofList_append]
  rw [ex]
  refine ⟨?_, b3, b4, b5, b6, fun j hj => by rw [b7 j hj, a7 j hj]⟩
  have h0 : ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K
      (id (abarR D σ ⬝ᵥ bv (zrR D σ (.inr (.inl c)))) + 1 * (setting D).G 0 c)).flatten =
      wA0row σ 0 :=
    congrArg List.flatten (List.map_congr_left fun c _ => congrArg (encRM D.N D.K) (by
      rw [one_mul, bbR_zero]; rfl))
  have h1 : ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K
      (id (b2barR D σ ⬝ᵥ bv (zrR D σ (.inr (.inl c)))) + 1 * (setting D).G 1 c)).flatten =
      wA0row σ 1 :=
    congrArg List.flatten (List.map_congr_left fun c _ => congrArg (encRM D.N D.K) (by
      rw [one_mul, bbR_one]; rfl))
  rw [b1, List.append_assoc]
  exact congrArg (fun x => pbuf b₀ (acc ++ x)) (congrArg₂ (· ++ ·) h0 h1)

end AdvancedEncryption.ExpLUT.Prog.RedPubP
