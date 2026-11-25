import PE.Impl.ExpLUT.Prog.RedPubPMono
open SigabaNeo.Tape.RingVM.Buf SigabaNeo.Tape.RingVM.Hash
/-!
# The rows `a_t` and `cb_t` (package G2, `pubP`)

* `exec_rowSetC`: the set-up of a row of hashes;
* **`exec_aBody`**: one position `t`: `u_t = X^{w x_t}`, the row `a_t` (into `rKA`) and the bottom
  row `cb_t` (into `rKC`), both canonical words;
* **`exec_aPhC`**: all positions; `a` (`wa`) is shifted into `rOut`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram Matrix
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-! ### Rows -/

theorem pnE_col : pnE (Col D.K) = 2 * D.K := by
  show (Enum.list (α := Fin 2 × Fin D.K)).length = _
  rw [Enum.length_prod, enum_fin, enum_fin, List.length_finRange, List.length_finRange]

/-- The zero stream of a row. -/
theorem replicate_col :
    List.replicate (pnE (Col D.K) * (D.N * D.K)) false =
      ((Enum.list (α := Col D.K)).map fun _ => List.replicate (D.N * D.K) false).flatten := by
  rw [List.map_const', List.flatten_replicate_replicate]

theorem hm_cpPost (w : St) : ∀ w' : St, (w' xAcc).length = D.N * D.K →
    (∀ j, j ∉ phW → w' j = w j) → (exec D.N D.K cpPost w' xH).length = D.N * D.K ∧
      decRM D.N D.K (exec D.N D.K cpPost w' xH) = id (decRM D.N D.K (w' xAcc)) := by
  intro w' hA _
  simp only [cpPost, exec_cp, Function.update_self]
  exact ⟨hA, rfl⟩

theorem wr_cpPost' : ∀ j ∈ wr cpPost, j = xH := by
  intro j hj; simpa [cpPost, wr] using hj

/-- The set-up of a row. -/
theorem exec_rowSetC (v z p : Fin 200) (hz : z ≠ xV) (hp1 : p ≠ xV) (hp2 : p ≠ xZ) (hp3 : p ≠ xF)
    (hp4 : p ≠ xOut) (w : St) :
    exec D.N D.K (rowSetC v z p) w =
      Function.update (Function.update (Function.update (Function.update (Function.update w
        xV (w v)) xZ (w z)) xF (w rZcol)) xOut (w rZcol)) xP (w p) := by
  simp only [rowSetC, exec_ofList_cons, exec_ofList_nil, exec_cp, Function.update_apply]
  simp [hz, hp1, hp2, hp3, hp4]

/-! ### One position -/

/-- The registers `aBody` writes. -/
def aBodyW : List (Fin 200) := [rU, rAttr, rBit, xV, rKA, rKC, rFe, rZ] ++ phW

theorem cbR_eq (σ : RawSec D) (t : Pos) (c : Col D.K) :
    cbR D σ t c = (fun v => -σ.2.1.vB (.inl v)) ⬝ᵥ bv (zrR D σ (.inl (t, c))) +
      (setting D).E.X ^ (wSt * attrN σ.1 t) * (setting D).G 1 c + (flR D σ).2.1 t c := by
  have hf : (b2barR D σ - bbarP D σ) = fun v => -σ.2.1.vB (.inl v) := by
    funext v; simp only [Pi.sub_apply, b2barR, bbarP]; abel
  rw [cbR, hf, add_right_comm]

theorem aR_eq (σ : RawSec D) (t : Pos) (c : Col D.K) :
    aR D σ t c = id (abarR D σ ⬝ᵥ bv (zrR D σ (.inl (t, c)))) +
      (setting D).E.X ^ (wSt * attrN σ.1 t) * (setting D).G 0 c + 0 := by
  rw [aR, add_zero]; rfl

/-- **One position**: `a_t` into `rKA`, `cb_t` into `rKC`. -/
theorem exec_aBody (hN : 2 ≤ D.N) (hW : wSt * 2 ^ 7 ≤ 2 * D.N) (σ : RawSec D) (t : Pos) (w : St)
    (hT : TmplOK D w) (restA restZ restF bA accA bC accC : List Bool)
    (hA : w rAttr = symbolBits w8 (σ.1 t) ++ restA) (hBit : (w rBit).length = 1)
    (hAbar : w rAbar = pwordsOf (abarR D σ))
    (hNV : w rNV = ((Enum.list (α := Wb D)).map (nvW σ)).flatten)
    (hZ : w rZ = ((Enum.list (α := Col D.K)).map fun c =>
      (Enum.list (α := Wb D)).map (zrR D σ (.inl (t, c)))).flatten ++ restZ)
    (hFe : w rFe = ((Enum.list (α := Col D.K)).map fun c =>
      encRM D.N D.K ((flR D σ).2.1 t c)).flatten ++ restF)
    (hKA : w rKA = pbuf bA accA) (hKC : w rKC = pbuf bC accC)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    let w' := exec D.N D.K aBody w
    w' rAttr = restA ∧ w' rZ = restZ ∧ w' rFe = restF ∧
      w' rKA = pbuf bA (accA ++ ((Enum.list (α := Col D.K)).map fun c =>
        encRM D.N D.K (aR D σ t c)).flatten) ∧
      w' rKC = pbuf bC (accC ++ ((Enum.list (α := Col D.K)).map fun c =>
        encRM D.N D.K (cbR D σ t c)).flatten) ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      (w' rBit).length = 1 ∧ TmplOK D w' ∧ ∀ j, j ∉ aBodyW → w' j = w j := by
  intro w'
  -- the monomial
  obtain ⟨m1, m2, m3, m4, m5⟩ := exec_monoC (D := D) hN hW (σ.1 t) restA w hT hA hBit
  set w1 := exec D.N D.K monoC w
  have hT1 : TmplOK D w1 := tmplOK_frame [rU, rAttr, rBit] (by decide) hT m5
  set u := (setting D).E.X ^ (wSt * attrN σ.1 t) with hu
  have m3' : decRM D.N D.K (w1 rU) = u := m3
  -- the row `a_t`
  have e2 := exec_rowSetC (D := D) rAbar rZ rU (by decide) (by decide) (by decide) (by decide)
    (by decide) w1
  set w2 := exec D.N D.K (rowSetC rAbar rZ rU) w1
  have hw2 : ∀ j, j ∉ [xV, xZ, xF, xOut, xP] → w2 j = w1 j := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [e2]; simp [Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2]
  have hT2 : TmplOK D w2 := tmplOK_frame [xV, xZ, xF, xOut, xP] (by decide) hT1 hw2
  have hzc : w1 rZcol = ((Enum.list (α := Col D.K)).map fun _ =>
      List.replicate (D.N * D.K) false).flatten := by rw [hT1.get rZcol, tm_rZcol, replicate_col]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := exec_rowC (D := D) 0 cpPost id wr_cpPost' w2
    (hm_cpPost w2) (abarR D σ) (fun v => encRM D.N D.K (abarR D σ v)) (fun _ => length_encRM _ _ _)
    (fun _ => decRM_encRM D.K_pos _) (fun c => zrR D σ (.inl (t, c))) (fun _ => 0)
    (fun _ => List.replicate (D.N * D.K) false) (fun _ => by simp) (fun _ => decRM_replicate _ _)
    u restZ []
    (by rw [e2]; simp [Function.update_apply, m5 rAbar (by decide), hAbar]; rfl)
    (by rw [e2]; simp [Function.update_apply, m5 rZ (by decide), hZ])
    (by rw [e2]; simp [Function.update_apply, hzc])
    (by rw [e2]; simp [Function.update_apply, hT1.len rZcol, pnE_col])
    (by rw [e2]; simp [Function.update_apply, m2]) (by rw [e2]; simp [Function.update_apply, m3'])
    (by rw [hw2 _ (by decide), hT1.len cK, tm_cK]) (by rw [hw2 _ (by decide), hT1.len xCm]; rfl)
    (by rw [hw2 _ (by decide), hT1.len xC1]; rfl) (by rw [hw2 _ (by decide), hT1.len xCNK]; rfl)
    (by rw [hw2 _ (by decide), hT1.get xZero]; rfl)
    (by rw [hw2 _ (by decide), m5 _ (by decide), hv]) (by rw [hw2 _ (by decide), m5 _ (by decide), hb])
    (by rw [hw2 _ (by decide), m5 _ (by decide), hf])
  set w3 := exec D.N D.K (rowC cpPost 0) w2
  have hT3 : TmplOK D w3 := tmplOK_frame phW (by decide) hT2 a7
  set At := ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K
    (id (abarR D σ ⬝ᵥ bv (zrR D σ (.inl (t, c)))) + u * (setting D).G 0 c + 0)).flatten with hAt
  have hlenRow : ∀ F : Col D.K → Rg D,
      ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (F c)).flatten.length =
        pnE (Col D.K) * (D.N * D.K) := by
    intro F; rw [length_flatten_of (n := D.N * D.K)]
    · simp
    · intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _
  -- push `a_t`
  have e4 := exec_mv_blk (N := D.N) (K := D.K) (d := rKA) (s := xOut) (c := cColW) (by decide)
    (w := w3) (b₀ := bA) (acc := accA) (v := At) (L := [])
    (by rw [a7 _ (by decide), hw2 _ (by decide), m5 _ (by decide), hKA])
    (by rw [hT3.len cColW, tm_cColW]; exact hlenRow _) (by rw [a1, List.append_nil]; rfl)
  set w4 := Function.update (Function.update w3 xOut []) rKA (pbuf bA (accA ++ At))
  have hw4 : ∀ j, j ≠ xOut → j ≠ rKA → w4 j = w3 j := fun j h1 h2 => by
    simp [w4, Function.update_apply, h1, h2]
  have hT4 : TmplOK D w4 := tmplOK_frame [xOut, rKA] (by decide) hT3 fun j hj => hw4 j
    (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))
  -- the row `cb_t`
  have e5 := exec_rowSetC (D := D) rNV rZ rU (by decide) (by decide) (by decide) (by decide)
    (by decide) w4
  set w5 := exec D.N D.K (rowSetC rNV rZ rU) w4
  have hw5 : ∀ j, j ∉ [xV, xZ, xF, xOut, xP] → w5 j = w4 j := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [e5]; simp [Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2]
  have hT5 : TmplOK D w5 := tmplOK_frame [xV, xZ, xF, xOut, xP] (by decide) hT4 hw5
  set Ft := ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K ((flR D σ).2.1 t c)).flatten
    with hFt
  have hFtl : Ft.length = pnE (Col D.K) * (D.N * D.K) := hlenRow _
  have e6 := exec_mv_blk (N := D.N) (K := D.K) (d := xF) (s := rFe) (c := cColW) (by decide)
    (w := w5) (b₀ := w4 rZcol) (acc := []) (v := Ft) (L := restF)
    (by rw [e5]; simp [Function.update_apply, pbuf_nil])
    (by rw [hT5.len cColW, hFtl]; rfl)
    (by rw [hw5 _ (by decide), hw4 _ (by decide) (by decide), a7 _ (by decide),
      hw2 _ (by decide), m5 _ (by decide), hFe])
  have hpb : pbuf (w4 rZcol) ([] ++ Ft) = Ft := by
    rw [List.nil_append, pbuf_full]; rw [hT4.len rZcol, hFtl]; rfl
  rw [hpb] at e6
  set w6 := Function.update (Function.update w5 rFe restF) xF Ft
  have hw6 : ∀ j, j ≠ xF → j ≠ rFe → w6 j = w5 j := fun j h1 h2 => by
    simp [w6, Function.update_apply, h1, h2]
  have hT6 : TmplOK D w6 := tmplOK_frame [xF, rFe] (by decide) hT5 fun j hj => hw6 j
    (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))
  have hU4 : w4 rU = w1 rU := by rw [hw4 _ (by decide) (by decide), a7 _ (by decide), hw2 _ (by decide)]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := exec_rowC (D := D) 1 cpPost id wr_cpPost' w6
    (hm_cpPost w6) (fun v => -σ.2.1.vB (.inl v)) (nvW σ) (length_nvW σ) (decRM_nvW σ)
    (fun c => zrR D σ (.inl (t, c))) (fun c => (flR D σ).2.1 t c)
    (fun c => encRM D.N D.K ((flR D σ).2.1 t c)) (fun _ => length_encRM _ _ _)
    (fun _ => decRM_encRM D.K_pos _) u restZ []
    (by rw [hw6 _ (by decide) (by decide), e5]
        simp [Function.update_apply, hw4 rNV (by decide) (by decide), a7 rNV (by decide),
          hw2 rNV (by decide), m5 rNV (by decide), hNV])
    (by rw [hw6 _ (by decide) (by decide), e5]
        simp [Function.update_apply, hw4 rZ (by decide) (by decide), a7 rZ (by decide),
          hw2 rZ (by decide), m5 rZ (by decide), hZ])
    (by simp [w6]; rfl)
    (by rw [hw6 _ (by decide) (by decide), e5]; simp [Function.update_apply, hT4.len rZcol, pnE_col])
    (by rw [hw6 _ (by decide) (by decide), e5]; simp [Function.update_apply, hU4, m2])
    (by rw [hw6 _ (by decide) (by decide), e5]; simp [Function.update_apply, hU4, m3'])
    (by rw [hT6.len cK, tm_cK]) (by rw [hT6.len xCm]; rfl) (by rw [hT6.len xC1]; rfl)
    (by rw [hT6.len xCNK]; rfl) (by rw [hT6.get xZero]; rfl)
    (by rw [hw6 _ (by decide) (by decide), hw5 _ (by decide), hw4 _ (by decide) (by decide), a4])
    (by rw [hw6 _ (by decide) (by decide), hw5 _ (by decide), hw4 _ (by decide) (by decide), a5])
    (by rw [hw6 _ (by decide) (by decide), hw5 _ (by decide), hw4 _ (by decide) (by decide), a6])
  set w7 := exec D.N D.K (rowC cpPost 1) w6
  have hT7 : TmplOK D w7 := tmplOK_frame phW (by decide) hT6 b7
  set Ct := ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K
    (id ((fun v => -σ.2.1.vB (.inl v)) ⬝ᵥ bv (zrR D σ (.inl (t, c)))) + u * (setting D).G 1 c +
      (flR D σ).2.1 t c)).flatten with hCt
  have e8 := exec_mv_blk (N := D.N) (K := D.K) (d := rKC) (s := xOut) (c := cColW) (by decide)
    (w := w7) (b₀ := bC) (acc := accC) (v := Ct) (L := [])
    (by rw [b7 _ (by decide), hw6 _ (by decide) (by decide), hw5 _ (by decide),
      hw4 _ (by decide) (by decide), a7 _ (by decide), hw2 _ (by decide), m5 _ (by decide), hKC])
    (by rw [hT7.len cColW, tm_cColW]; exact hlenRow _) (by rw [b1, List.append_nil]; rfl)
  set w8 := Function.update (Function.update w7 xOut []) rKC (pbuf bC (accC ++ Ct))
  have ex : w' = Function.update w8 rZ (w8 xZ) := by
    show exec D.N D.K (.cp rZ xZ) (exec D.N D.K (.mv rKC xOut cColW) (exec D.N D.K (rowC cpPost 1)
      (exec D.N D.K (.mv xF rFe cColW) (exec D.N D.K (rowSetC rNV rZ rU)
        (exec D.N D.K (.mv rKA xOut cColW) w3))))) = _
    rw [e4]
    show exec D.N D.K (.cp rZ xZ) (exec D.N D.K (.mv rKC xOut cColW) (exec D.N D.K (rowC cpPost 1)
      (exec D.N D.K (.mv xF rFe cColW) w5))) = _
    rw [e6]
    show exec D.N D.K (.cp rZ xZ) (exec D.N D.K (.mv rKC xOut cColW) w7) = _
    rw [e8]; rfl
  have hw8 : ∀ j, j ≠ xOut → j ≠ rKC → w8 j = w7 j := fun j h1 h2 => by
    simp [w8, Function.update_apply, h1, h2]
  have hfr : ∀ j, j ∉ aBodyW → w' j = w j := by
    intro j hj
    have hp : j ∉ phW := fun h => hj (List.mem_append_right _ h)
    have hn : ∀ r ∈ [rU, rAttr, rBit, xV, rKA, rKC, rFe, rZ], j ≠ r := fun r hr h =>
      hj (List.mem_append_left _ (h ▸ hr))
    have hph : ∀ r ∈ phW, j ≠ r := fun r hr h => hp (h ▸ hr)
    rw [ex, Function.update_of_ne (hn rZ (by simp)), hw8 j (hph xOut (by decide)) (hn rKC (by simp)),
      b7 j hp, hw6 j (hph xF (by decide)) (hn rFe (by simp)),
      hw5 j (by simp [hn xV (by simp), hph xZ (by decide), hph xF (by decide),
        hph xOut (by decide), hph xP (by decide)]),
      hw4 j (hph xOut (by decide)) (hn rKA (by simp)), a7 j hp,
      hw2 j (by simp [hn xV (by simp), hph xZ (by decide), hph xF (by decide),
        hph xOut (by decide), hph xP (by decide)]),
      m5 j (by simp [hn rU (by simp), hn rAttr (by simp), hn rBit (by simp)])]
  have hA' : At = ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (aR D σ t c)).flatten := by
    rw [hAt]
    exact congrArg List.flatten (List.map_congr_left fun c _ =>
      congrArg (encRM D.N D.K) (aR_eq σ t c).symm)
  have hC' : Ct = ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (cbR D σ t c)).flatten := by
    rw [hCt]
    exact congrArg List.flatten (List.map_congr_left fun c _ =>
      congrArg (encRM D.N D.K) (cbR_eq σ t c).symm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr⟩
  · rw [ex, Function.update_of_ne (by decide), hw8 _ (by decide) (by decide), b7 _ (by decide),
      hw6 _ (by decide) (by decide), hw5 _ (by decide), hw4 _ (by decide) (by decide),
      a7 _ (by decide), hw2 _ (by decide), m1]
  · rw [ex, Function.update_self, hw8 _ (by decide) (by decide), b2]
  · rw [ex, Function.update_of_ne (by decide), hw8 _ (by decide) (by decide), b7 _ (by decide)]
    show Function.update (Function.update w5 rFe restF) xF Ft rFe = restF
    rw [Function.update_of_ne (by decide), Function.update_self]
  · rw [ex, Function.update_of_ne (by decide), hw8 _ (by decide) (by decide), b7 _ (by decide),
      hw6 _ (by decide) (by decide), hw5 _ (by decide), ← hA']
    show Function.update (Function.update w3 xOut []) rKA (pbuf bA (accA ++ At)) rKA = _
    rw [Function.update_self]
  · rw [ex, Function.update_of_ne (by decide), ← hC']
    show Function.update (Function.update w7 xOut []) rKC (pbuf bC (accC ++ Ct)) rKC = _
    rw [Function.update_self]
  · rw [ex, Function.update_of_ne (by decide), hw8 _ (by decide) (by decide), b4]
  · rw [ex, Function.update_of_ne (by decide), hw8 _ (by decide) (by decide), b5]
  · rw [ex, Function.update_of_ne (by decide), hw8 _ (by decide) (by decide), b6]
  · rw [ex, Function.update_of_ne (by decide), hw8 _ (by decide) (by decide), b7 _ (by decide),
      hw6 _ (by decide) (by decide), hw5 _ (by decide), hw4 _ (by decide) (by decide),
      a7 _ (by decide), hw2 _ (by decide), m4]
  · refine tmplOK_frame aBodyW (by decide) hT hfr

/-! ### All positions -/

section Lists

variable (σ : RawSec D)

/-- The attribute bits, per symbol. -/
def aTL : List (List Bool) := (List.ofFn σ.1).map (symbolBits w8)

/-- The bits of the `Z_t`, per position. -/
def zTL : List (List Bool) := (Enum.list (α := Pos)).map fun t =>
  ((Enum.list (α := Col D.K)).map fun c => (Enum.list (α := Wb D)).map (zrR D σ (.inl (t, c)))).flatten

/-- The flooding words `e_t`, per position. -/
noncomputable def fTL : List (List Bool) := (Enum.list (α := Pos)).map fun t =>
  ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K ((flR D σ).2.1 t c)).flatten

/-- The words of `a_t`, per position. -/
noncomputable def aWL : List (List Bool) := (Enum.list (α := Pos)).map fun t =>
  ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (aR D σ t c)).flatten

/-- The words of `cb_t`, per position. -/
noncomputable def cWL : List (List Bool) := (Enum.list (α := Pos)).map fun t =>
  ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (cbR D σ t c)).flatten

end Lists

theorem encAttribute_aTL (σ : RawSec D) : encAttribute w8 σ.1 = (aTL σ).flatten := by
  show (List.ofFn σ.1).flatMap (symbolBits w8) = _
  rw [aTL, List.flatMap_def]

theorem pzZW_zTL (σ : RawSec D) : pzZW σ = (zTL σ).flatten := by
  rw [pzZW, pzrBlocks, zTL, enum_prod, map_product, List.flatten_flatten, List.map_map]
  rfl

theorem pfl2W_fTL (σ : RawSec D) : pfl2W σ = (fTL σ).flatten := by
  rw [pfl2W]
  refine (pfun_enc (α := Pos) (vecE D (Col D.K)) _).trans ?_
  exact congrArg List.flatten (List.map_congr_left fun t _ => vecE_wordsOf _)

theorem wa_aWL (σ : RawSec D) : wa σ = (aWL σ).flatten := by
  rw [wa, aWL, enum_prod, map_product, List.flatten_flatten, List.map_map]
  rfl

theorem len_pos16 : pnE Pos = 16 := by
  show (Enum.list (α := Fin 16)).length = 16; rw [enum_fin, List.length_finRange]

theorem length_rowW (F : Col D.K → Rg D) :
    ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (F c)).flatten.length =
      pnE (Col D.K) * (D.N * D.K) := by
  rw [length_flatten_of (n := D.N * D.K)]
  · simp
  · intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _

theorem enum_pos_getElem (i : ℕ) (hi : i < (Enum.list (α := Pos)).length) :
    (Enum.list (α := Pos))[i] = ⟨i, by simpa [enum_fin] using hi⟩ := by
  simp [enum_fin]

/-- The registers the loop of `a` writes. -/
def aLoopW : List (Fin 200) := cntP :: aBodyW

/-- **The loop of `a` and `cb`.** -/
theorem exec_aLoop (hN : 2 ≤ D.N) (hW : wSt * 2 ^ 7 ≤ 2 * D.N) (σ : RawSec D) (w : St)
    (hT : TmplOK D w) (hA : w rAttr = encAttribute w8 σ.1) (hBit : (w rBit).length = 1)
    (hAbar : w rAbar = pwordsOf (abarR D σ))
    (hNV : w rNV = ((Enum.list (α := Wb D)).map (nvW σ)).flatten)
    (hZ : w rZ = pzZW σ) (hFe : w rFe = pfl2W σ)
    (hKA : (w rKA).length = pnE Pos * (pnE (Col D.K) * (D.N * D.K)))
    (hKC : (w rKC).length = pnE Pos * (pnE (Col D.K) * (D.N * D.K)))
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K)
    (hc : (w cntP).length = pnE Pos) :
    let w' := exec D.N D.K (.rep cntP aBody) w
    w' rKA = wa σ ∧ w' rKC = (cWL σ).flatten ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      TmplOK D w' ∧ ∀ j, j ∉ aLoopW → w' j = w j := by
  intro w'
  let P : ℕ → St → Prop := fun i w' =>
    w' rAttr = ((aTL σ).drop i).flatten ∧ w' rZ = ((zTL σ).drop i).flatten ∧
      w' rFe = ((fTL σ).drop i).flatten ∧ w' rKA = pbuf (w rKA) ((aWL σ).take i).flatten ∧
      w' rKC = pbuf (w rKC) ((cWL σ).take i).flatten ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      (w' rBit).length = 1 ∧ TmplOK D w' ∧ ∀ j, j ∉ aBodyW → j ≠ cntP → w' j = w j
  have hcw : cntP ∉ wr aBody := by decide
  have h0 : P 0 w := ⟨by rw [hA, encAttribute_aTL]; rfl, by rw [hZ, pzZW_zTL]; rfl,
    by rw [hFe, pfl2W_fTL]; rfl, by simp [pbuf_nil], by simp [pbuf_nil], hv, hb, hf, hBit, hT,
    fun _ _ _ => rfl⟩
  have key := exec_rep_inv (N := D.N) (K := D.K) cntP aBody hcw P w h0 (fun i hi w1 hP _ => by
    rw [hc] at hi
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := hP
    set u := Function.update w1 cntP (w1 cntP).tail
    have hu : ∀ j, j ≠ cntP → u j = w1 j := fun j hj => Function.update_of_ne hj _ _
    have hTu : TmplOK D u := tmplOK_frame [cntP] (by decide) p10 fun j hj =>
      hu j (fun h => hj (by simp [h]))
    have hi16 : i < 16 := by rw [len_pos16] at hi; exact hi
    set t : Pos := ⟨i, hi16⟩
    have hiA : i < (aTL σ).length := by simp [aTL]; exact hi16
    have hiZ : i < (zTL σ).length := by simp [zTL]; exact hi
    have hiF : i < (fTL σ).length := by simp [fTL]; exact hi
    have hiAW : i < (aWL σ).length := by simp [aWL]; exact hi
    have hiCW : i < (cWL σ).length := by simp [cWL]; exact hi
    have hep := enum_pos_getElem i hi
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := exec_aBody (D := D) hN hW σ t u hTu
      ((aTL σ).drop (i + 1)).flatten ((zTL σ).drop (i + 1)).flatten ((fTL σ).drop (i + 1)).flatten
      (w rKA) ((aWL σ).take i).flatten (w rKC) ((cWL σ).take i).flatten
      (by rw [hu _ (by decide), p1, flatten_drop_cons hiA]; simp [aTL, t])
      (by rw [hu _ (by decide), p9])
      (by rw [hu _ (by decide), p11 _ (by decide) (by decide), hAbar])
      (by rw [hu _ (by decide), p11 _ (by decide) (by decide), hNV])
      (by rw [hu _ (by decide), p2, flatten_drop_cons hiZ]; simp [zTL, hep, t])
      (by rw [hu _ (by decide), p3, flatten_drop_cons hiF]; simp [fTL, hep, t])
      (by rw [hu _ (by decide), p4]) (by rw [hu _ (by decide), p5])
      (by rw [hu _ (by decide), p6]) (by rw [hu _ (by decide), p7]) (by rw [hu _ (by decide), p8])
    refine ⟨q1, q2, q3, ?_, ?_, q6, q7, q8, q9, q10, ?_⟩
    · rw [q4, List.take_succ_eq_append_getElem hiAW, List.flatten_append, List.flatten_singleton]
      simp [aWL, hep, t]
    · rw [q5, List.take_succ_eq_append_getElem hiCW, List.flatten_append, List.flatten_singleton]
      simp [cWL, hep, t]
    · intro j hj hjc; rw [q11 j hj, hu j hjc, p11 j hj hjc])
  rw [hc] at key
  obtain ⟨-, -, -, k4, k5, k6, k7, k8, -, k10, k11⟩ := key
  have hlA : (aWL σ).length = pnE Pos := by simp [aWL]
  have hlC : (cWL σ).length = pnE Pos := by simp [cWL]
  have hfl : ∀ L : List (List Bool), L.length = pnE Pos → (∀ x ∈ L, x.length = pnE (Col D.K) * (D.N * D.K)) →
      L.flatten.length = pnE Pos * (pnE (Col D.K) * (D.N * D.K)) := fun L hL hx => by
    rw [length_flatten_of hx, hL]
  have hxA : ∀ x ∈ aWL σ, x.length = pnE (Col D.K) * (D.N * D.K) := by
    intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_rowW _
  have hxC : ∀ x ∈ cWL σ, x.length = pnE (Col D.K) * (D.N * D.K) := by
    intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_rowW _
  refine ⟨?_, ?_, k6, k7, k8, k10, fun j hj => ?_⟩
  · show exec D.N D.K (.rep cntP aBody) w rKA = _
    rw [k4, ← hlA, List.take_length, pbuf_full (by rw [hKA, hfl _ hlA hxA]), wa_aWL]
  · show exec D.N D.K (.rep cntP aBody) w rKC = _
    rw [k5, ← hlC, List.take_length, pbuf_full (by rw [hKC, hfl _ hlC hxC])]
  · exact k11 j (fun h => hj (List.mem_cons_of_mem _ h)) (fun h => hj (by simp [aLoopW, h]))

end AdvancedEncryption.ExpLUT.Prog.RedPubP
