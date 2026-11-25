import PE.Impl.ExpLUT.Prog.RedPubPAutK
open SigabaNeo.Tape.RingVM.Buf SigabaNeo.Tape.RingVM.Hash
/-!
# `A^aut` (package G2, `pubP`)

* `autC0`, `autC1`: the rows of `C_{g_t}` (`σ(aH_{(t,1)})`, `σ(G⁽²⁾ − v_{H,(t,1)})`); `dautR_C`:
  the digits of `A^aut` are those of these entries;
* **`exec_strC`**: the strided loops of `autT`;
* **`exec_autT`**, **`exec_autC`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram Matrix
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-! ### The matrix `C_{g_t}` -/

/-- The row `0` of `C_{g_t}`. -/
noncomputable def autC0 (σ : RawSec D) (t : Fin D.b) (c : Col D.K) : Rg D :=
  (setting D).E.σ ((setting D).kf t) (σ.2.1.aH (t, 1) c)

/-- The row `1` of `C_{g_t}`. -/
noncomputable def autC1 (σ : RawSec D) (t : Fin D.b) (c : Col D.K) : Rg D :=
  (setting D).E.σ ((setting D).kf t) ((setting D).G 1 c - σ.2.1.vH (t, 1) c)

theorem σ_sub (t : ℕ) (a b : Rg D) :
    (setting D).E.σ ((setting D).kf t) (a - b) =
      (setting D).E.σ ((setting D).kf t) a - (setting D).E.σ ((setting D).kf t) b := by
  rw [σ_kf, σ_kf, σ_kf, sub_eq_add_neg, aut_add, aut_neg, ← sub_eq_add_neg]

/-- **The digits of `A^aut`** are those of the entries `autC0`, `autC1`. -/
theorem dautR_C (σ : RawSec D) (t : Fin D.b) (r : Fin 2) (c' : Col D.K) (i : Fin D.K) :
    dautR D σ t (r, c', i) = binaryDigit (if r = 0 then autC0 σ t c' else autC1 σ t c') i := by
  rw [dautR_apply]
  congr 1
  by_cases hr : r = 0
  · subst hr; simp [autC0, HR]
  · have hr1 : r = 1 := by revert hr; revert r; decide
    subst hr1
    simp only [if_true, autC1, HR, hR, show ((1 : Fin 2) = 0) = False by decide, if_false]
    rw [← σ_sub]
    congr 1
    simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons]
    exact (fun a b g : Rg D => by abel : ∀ a b g : Rg D, a - (b - g + a) = g - b) _ _ _

/-- `G⁽²⁾` on the columns. -/
theorem G1_apply (c : Col D.K) :
    (setting D).G 1 c = if (1 : Fin 2) = c.1 then (2 : ZMod (2 ^ D.K - 1)) ^ (c.2 : ℕ) • (1 : Rg D)
      else 0 := by
  have := mul_G_apply (D := D) 1 1 c
  rw [one_mul] at this; exact this

/-! ### Strided loops -/

/-- **A strided loop of `autT`.** -/
theorem exec_strC (src : Fin 200) (body : Code) (w : St) :
    exec D.N D.K (strC src body) w =
      exec D.N D.K (.rep cnt body) (Function.update (Function.update w tmp (w src)) cnt
        (Function.update w tmp (w src) cK)) := rfl

theorem pnE_Jh : pnE (Jh D) = D.b * 2 := by
  show (Enum.list (α := Fin D.b × Fin 2)).length = _
  rw [Enum.length_prod, enum_fin, enum_fin, List.length_finRange, List.length_finRange]

/-- The helper `(t, 1)` is at the position `2 t + 1`. -/
theorem enum_jh_odd (t : Fin D.b) (h : t.val * 2 + 1 < pnE (Jh D)) :
    (Enum.list (α := Jh D))[t.val * 2 + 1] = (t, 1) := by
  have e := Enum.getElem_prod (α := Fin D.b) (β := Fin 2) t.val 1 (by simp [enum_fin])
    (by simp [enum_fin]) (by simpa [enum_fin] using h)
  simp only [enum_fin, List.length_finRange, List.getElem_finRange] at e
  exact e

/-- The strided words of the row `i ↦ F i` of a helper block, mapped. -/
theorem strided_words (F : Jh D → Col D.K → Rg D) (ρ' : Fin 2) (t : Fin D.b) (φ : ℕ → Rg D → Rg D)
    (L : List (List Bool))
    (hL : ∀ i : Fin D.K, L.getD ((i : ℕ) * pnE (Jh D) + (t.val * 2 + 1)) [] =
      encRM D.N D.K (F (t, 1) (ρ', i))) :
    ((List.range D.K).map fun i => encRM D.N D.K (φ i (decRM D.N D.K
        (L.getD (i * pnE (Jh D) + (t.val * 2 + 1)) [])))).flatten =
      ((List.finRange D.K).map fun i : Fin D.K => encRM D.N D.K (φ i (F (t, 1) (ρ', i)))).flatten := by
  rw [map_range_finRange]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [hL i, decRM_encRM D.K_pos]

/-! ### The computation of `C_{g_t}` -/

/-- The prefix of `autT`: the rows of `C_{g_t}` into `rCt`, `rCt2`, the streams advanced. -/
def autPre (t : ℕ) : List Code :=
  [.cp rCt rZcol, strC rSk (aBodyK t), strC rSp (aBodyK t),
    .cp rCt2 rZcol, strC rVk (aBodyV0 t), .cp rG r1, strC rVp (aBodyV1 t),
    .drop rSk cNK2, .drop rSp cNK2, .drop rVk cNK2, .drop rVp cNK2]

theorem autT_eq (t : ℕ) :
    autT t = ofList (autPre t ++ [digRow rCt (autPost t) ra, digRow rCt2 (autPost t) ra]) := rfl

/-- The registers of the prefix. -/
def autPreW : List (Fin 200) :=
  [rCt, rCt2, rG, tmp, cnt, xv, xS, xO, rT1, rSk, rSp, rVk, rVp]

/-- One strided map of the prefix, in the form of `exec_strMap`. -/
theorem exec_strC_map (src : Fin 200) (hs1 : src ≠ tmp) (hs2 : src ≠ cnt) (postL : List Code)
    (dst : Fin 200) (postW : List (Fin 200))
    (hpw : xv ∉ postW ∧ tmp ∉ postW ∧ cnt ∉ postW ∧ xCNK ∉ postW ∧ cSkip ∉ postW)
    (hwr : ∀ j ∈ wr (ofList postL), j ∈ postW) (hdst : dst ∈ postW) (hsrc : src ∉ postW)
    (φ : ℕ → Rg D → Rg D) (Q : ℕ → St → Prop)
    (hQ : ∀ i (w1 w2 : St), (∀ j, j ∉ [xv, tmp, cnt] → w2 j = w1 j) → Q i w1 → Q i w2)
    (hpost : ∀ i (w' : St) (b₀ acc : List Bool), (w' xv).length = D.N * D.K →
      w' dst = pbuf b₀ acc → Q i w' →
      exec D.N D.K (ofList postL) w' dst =
          pbuf b₀ (acc ++ encRM D.N D.K (φ i (decRM D.N D.K (w' xv)))) ∧
        Q (i + 1) (exec D.N D.K (ofList postL) w'))
    (w : St) (hT : TmplOK D w) (L : List (List Bool)) (hL : ∀ x ∈ L, x.length = D.N * D.K)
    (kk : ℕ) (hkk : kk < pnE (Jh D)) (hLl : L.length = D.K * pnE (Jh D)) (b₀ acc : List Bool)
    (hs : w src = (L.drop kk).flatten) (hd : w dst = pbuf b₀ acc) (hxv : (w xv).length = D.N * D.K)
    (hQ0 : Q 0 w) :
    let w' := exec D.N D.K (strC src (ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postL))) w
    w' dst = pbuf b₀ (acc ++ ((List.range D.K).map fun i =>
        encRM D.N D.K (φ i (decRM D.N D.K (L.getD (i * pnE (Jh D) + kk) [])))).flatten) ∧
      (w' xv).length = D.N * D.K ∧ Q D.K w' ∧ ∀ j, j ∉ xv :: tmp :: cnt :: postW → w' j = w j := by
  intro w'
  rw [show w' = _ from exec_strC src _ w]
  set w1 := Function.update (Function.update w tmp (w src)) cnt (Function.update w tmp (w src) cK)
  have hw1 : ∀ j, j ≠ tmp → j ≠ cnt → w1 j = w j := fun j h1 h2 => by
    simp [w1, Function.update_apply, h1, h2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpw
  have hdt : dst ≠ tmp := fun h => p2 (h ▸ hdst)
  have hdc : dst ≠ cnt := fun h => p3 (h ▸ hdst)
  obtain ⟨k1, k0, k2, k3⟩ := exec_strMap (D := D) postL dst postW ⟨p1, p2, p3, p4, p5⟩ hwr hdst φ Q hQ
    hpost w1 L hL (pnE (Jh D)) kk (by omega)
    (fun i hi => by rw [hLl]; nlinarith) b₀ acc
    (by simp [w1, Function.update_apply, hs1.symm, hs])
    (by rw [hw1 _ hdt hdc, hd]) (by rw [hw1 _ (by decide) (by decide), hxv])
    (by rw [hw1 _ (by decide) (by decide), hT.len xCNK]; rfl)
    (by rw [hw1 _ (by decide) (by decide), hT.len cSkip, tm_cSkip])
    (by simp [w1, Function.update_apply, hT.len cK])
    (hQ 0 w w1 (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      exact hw1 j hj.2.1 hj.2.2) hQ0)
  refine ⟨k1, k0, k2, fun j hj => ?_⟩
  rw [k3 j hj]
  simp only [List.mem_cons, not_or] at hj
  exact hw1 j hj.2.1 hj.2.2.1

theorem wr_postK (t : ℕ) : ∀ j ∈ wr (ofList (postK t)), j ∈ [xS, xO, rCt] :=
  fun j hj => mem_of_all (l := wr (ofList (postK t))) rfl hj

theorem wr_postV0 (t : ℕ) : ∀ j ∈ wr (ofList (postV0 t)), j ∈ [xS, rT1, xO, rCt2] :=
  fun j hj => mem_of_all (l := wr (ofList (postV0 t))) rfl hj

theorem wr_postV1 (t : ℕ) : ∀ j ∈ wr (ofList (postV1 t)), j ∈ [xS, rT1, xO, rCt2, rG] :=
  fun j hj => mem_of_all (l := wr (ofList (postV1 t))) rfl hj

theorem hQ_tmpl : ∀ (i : ℕ) (w1 w2 : St), (∀ j, j ∉ [xv, tmp, cnt] → w2 j = w1 j) →
    (fun (_ : ℕ) w => TmplOK D w) i w1 → (fun (_ : ℕ) w => TmplOK D w) i w2 :=
  fun _ _ _ hfr hT => tmplOK_frame [xv, tmp, cnt] (by decide) hT hfr

theorem hQ_G : ∀ (i : ℕ) (w1 w2 : St), (∀ j, j ∉ [xv, tmp, cnt] → w2 j = w1 j) →
    QG (D := D) i w1 → QG (D := D) i w2 := fun _ _ _ hfr hQ =>
  ⟨tmplOK_frame [xv, tmp, cnt] (by decide) hQ.1 hfr, by rw [hfr _ (by decide)]; exact hQ.2.1,
    by rw [hfr _ (by decide)]; exact hQ.2.2⟩

/-- The words of the helper blocks. -/
noncomputable def hk (F : Jh D → Col D.K → Rg D) : List (List Bool) := hlW (keyHL D F)
noncomputable def hp (F : Jh D → Col D.K → Rg D) : List (List Bool) := hlW (plainHL D F)

/-- **The computation of `C_{g_t}`.** -/
theorem exec_autPre (σ : RawSec D) (t : Fin D.b) (ht : t.val < 32) (w : St) (hT : TmplOK D w)
    (hSk : w rSk = ((hk σ.2.1.aH).drop (t.val * 2 + 1)).flatten)
    (hSp : w rSp = ((hp σ.2.1.aH).drop (t.val * 2 + 1)).flatten)
    (hVk : w rVk = ((hk σ.2.1.vH).drop (t.val * 2 + 1)).flatten)
    (hVp : w rVp = ((hp σ.2.1.vH).drop (t.val * 2 + 1)).flatten)
    (hxv : (w xv).length = D.N * D.K) :
    let w' := exec D.N D.K (ofList (autPre t.val)) w
    w' rCt = ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (autC0 σ t c)).flatten ∧
      w' rCt2 = ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (autC1 σ t c)).flatten ∧
      w' rSk = ((hk σ.2.1.aH).drop (t.val * 2 + 3)).flatten ∧
      w' rSp = ((hp σ.2.1.aH).drop (t.val * 2 + 3)).flatten ∧
      w' rVk = ((hk σ.2.1.vH).drop (t.val * 2 + 3)).flatten ∧
      w' rVp = ((hp σ.2.1.vH).drop (t.val * 2 + 3)).flatten ∧
      (w' xv).length = D.N * D.K ∧ TmplOK D w' ∧ ∀ j, j ∉ autPreW → w' j = w j := by
  intro w'
  have hkk : t.val * 2 + 1 < pnE (Jh D) := by rw [pnE_Jh]; omega
  have hjh := enum_jh_odd t hkk
  have hz : (w rZcol).length = pnE (Col D.K) * (D.N * D.K) := by rw [hT.len rZcol, tm_rZcol]
  -- the row `0`
  set w1 := Function.update w rCt (w rZcol)
  have hT1 : TmplOK D w1 := tmplOK_frame [rCt] (by decide) hT fun j hj => by
    simp [w1, Function.update_apply, show j ≠ rCt from fun h => hj (by simp [h])]
  have hpK : ∀ (src : Fin 200) (w0 : St) (L : List (List Bool)) (b₀ acc : List Bool),
      (∀ x ∈ L, x.length = D.N * D.K) → L.length = D.K * pnE (Jh D) → src = rSk ∨ src = rSp →
      TmplOK D w0 → w0 src = (L.drop (t.val * 2 + 1)).flatten → w0 rCt = pbuf b₀ acc →
      (w0 xv).length = D.N * D.K → _ := fun src w0 L b₀ acc hL hLl hsrc hT0 hs hd hx =>
    exec_strC_map (D := D) src (by rcases hsrc with h | h <;> subst h <;> decide)
      (by rcases hsrc with h | h <;> subst h <;> decide) (postK t.val) rCt
      [xS, xO, rCt] (by decide) (wr_postK t.val) (by decide)
      (by rcases hsrc with h | h <;> subst h <;> decide)
      (fun _ x => (setting D).E.σ ((setting D).kf t.val) x) (fun _ w => TmplOK D w) hQ_tmpl
      (fun i w' b₀ acc hx hd hQ => exec_postK t.val ht i w' b₀ acc hx hd hQ) w0 hT0 L hL
      (t.val * 2 + 1) hkk hLl b₀ acc hs hd hx hT0
  obtain ⟨a1, a0, a2, a3⟩ := hpK rSk w1 (hk σ.2.1.aH) (w rZcol) [] (length_hlW _)
    (length_hlW_keyHL _) (Or.inl rfl) hT1 (by simp [w1, Function.update_apply, hSk])
    (by simp [w1, pbuf_nil]) (by simp [w1, Function.update_apply, hxv])
  set w2 := exec D.N D.K (strC rSk (ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postK t.val))) w1
  have f2 : ∀ j, j ∉ [xv, tmp, cnt, xS, xO, rCt] → w2 j = w j := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [a3 j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2])]
    simp [w1, Function.update_apply, hj.2.2.2.2.2]
  obtain ⟨b1, b0, b2, b3⟩ := hpK rSp w2 (hp σ.2.1.aH) (w rZcol) _ (length_hlW _)
    (length_hlW_plainHL _) (Or.inr rfl) a2 (by rw [f2 _ (by decide), hSp]) a1 a0
  set w3 := exec D.N D.K (strC rSp (ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postK t.val))) w2
  have f3 : ∀ j, j ∉ [xv, tmp, cnt, xS, xO, rCt] → w3 j = w j := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [b3 j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2]), f2 j (by
      simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2])]
  -- the row `1`
  set w4 := Function.update w3 rCt2 (w3 rZcol)
  have hz4 : w3 rZcol = w rZcol := f3 _ (by decide)
  have hT4 : TmplOK D w4 := tmplOK_frame [rCt2] (by decide) b2 fun j hj => by
    simp [w4, Function.update_apply, show j ≠ rCt2 from fun h => hj (by simp [h])]
  obtain ⟨c1, c0, c2, c3⟩ := exec_strC_map (D := D) rVk (by decide) (by decide) (postV0 t.val) rCt2
    [xS, rT1, xO, rCt2] (by decide) (wr_postV0 t.val) (by decide) (by decide)
    (fun _ x => (setting D).E.σ ((setting D).kf t.val) (0 - x)) (fun _ w => TmplOK D w) hQ_tmpl
    (fun i w' b₀ acc hx hd hQ => exec_postV0 t.val ht i w' b₀ acc hx hd hQ) w4 hT4 (hk σ.2.1.vH)
    (length_hlW _) (t.val * 2 + 1) hkk (length_hlW_keyHL _) (w rZcol) []
    (by simp [w4, Function.update_apply, f3 rVk (by decide), hVk]) (by simp [w4, hz4, pbuf_nil])
    (by simp [w4, Function.update_apply, b0]) hT4
  set w5 := exec D.N D.K (strC rVk (ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postV0 t.val))) w4
  set w6 := Function.update w5 rG (w5 r1)
  have hr1 : w5 r1 = true :: List.replicate (D.N * D.K - 1) false := c2.2
  have hQ6 : QG (D := D) 0 w6 := by
    refine ⟨tmplOK_frame [rG] (by decide) c2 fun j hj => by
      simp [w6, Function.update_apply, show j ≠ rG from fun h => hj (by simp [h])], ?_, ?_⟩
    · simp [w6, hr1]; have := Nat.mul_pos D.N_pos D.K_pos; omega
    · simp [w6, hr1, decRM_r1]
  obtain ⟨d1, d0, d2, d3⟩ := exec_strC_map (D := D) rVp (by decide) (by decide) (postV1 t.val) rCt2
    [xS, rT1, xO, rCt2, rG] (by decide) (wr_postV1 t.val) (by decide) (by decide)
    (fun i x => (setting D).E.σ ((setting D).kf t.val) ((2 : ZMod (2 ^ D.K - 1)) ^ i • (1 : Rg D) - x))
    (QG (D := D)) hQ_G
    (fun i w' b₀ acc hx hd hQ => exec_postV1 t.val ht i w' b₀ acc hx hd hQ) w6 hQ6.1 (hp σ.2.1.vH)
    (length_hlW _) (t.val * 2 + 1) hkk (length_hlW_plainHL _) (w rZcol) _
    (by simp [w6, Function.update_apply]; rw [c3 _ (by decide)]
        simp [w4, Function.update_apply, f3 rVp (by decide), hVp])
    (by simp [w6, Function.update_apply]; exact c1) (by simp [w6, Function.update_apply, c0]) hQ6
  set w7 := exec D.N D.K (strC rVp (ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postV1 t.val))) w6
  have ex : w' = exec D.N D.K (ofList [.drop rSk cNK2, .drop rSp cNK2, .drop rVk cNK2,
      .drop rVp cNK2]) w7 := rfl
  have f7 : ∀ j, j ∉ [rCt, rCt2, rG, tmp, cnt, xv, xS, xO, rT1] → w7 j = w j := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    obtain ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9⟩ := hj
    rw [d3 j (by simp [j1, j2, j3, j4, j5, j6, j7, j8, j9])]
    simp only [w6, Function.update_of_ne j3]
    rw [c3 j (by simp [j2, j4, j5, j6, j7, j8, j9])]
    simp only [w4, Function.update_of_ne j2]
    exact f3 j (by simp [j1, j4, j5, j6, j7, j8])
  have hT7 : TmplOK D w7 := d2.1
  have ex2 : w' = Function.update (Function.update (Function.update (Function.update w7
      rSk ((w7 rSk).drop (2 * (D.N * D.K)))) rSp ((w7 rSp).drop (2 * (D.N * D.K))))
      rVk ((w7 rVk).drop (2 * (D.N * D.K)))) rVp ((w7 rVp).drop (2 * (D.N * D.K))) := by
    rw [ex]
    simp only [exec_ofList_cons, exec_ofList_nil]
    rw [exec_drop_eq (by decide), exec_drop_eq (by decide), exec_drop_eq (by decide),
      exec_drop_eq (by decide)]
    simp only [Function.update_apply]
    simp [hT7.len cNK2]
  have hdrop : ∀ (L : List (List Bool)), (∀ x ∈ L, x.length = D.N * D.K) →
      (L.drop (t.val * 2 + 1)).flatten.drop (2 * (D.N * D.K)) = (L.drop (t.val * 2 + 3)).flatten :=
    fun L hL => by rw [flatten_drop_drop hL]
  -- the words
  have hK0 := strided_words (D := D) σ.2.1.aH 0 t (fun _ x => (setting D).E.σ ((setting D).kf t.val) x)
    (hk σ.2.1.aH) (fun i => (getD_hlW_keyHL _ i _ hkk).trans (by rw [hjh]))
  have hP0 := strided_words (D := D) σ.2.1.aH 1 t (fun _ x => (setting D).E.σ ((setting D).kf t.val) x)
    (hp σ.2.1.aH) (fun i => (getD_hlW_plainHL _ i _ hkk).trans (by rw [hjh]))
  have hK1 := strided_words (D := D) σ.2.1.vH 0 t
    (fun _ x => (setting D).E.σ ((setting D).kf t.val) (0 - x))
    (hk σ.2.1.vH) (fun i => (getD_hlW_keyHL _ i _ hkk).trans (by rw [hjh]))
  have hP1 := strided_words (D := D) σ.2.1.vH 1 t
    (fun i x => (setting D).E.σ ((setting D).kf t.val) ((2 : ZMod (2 ^ D.K - 1)) ^ i • (1 : Rg D) - x))
    (hp σ.2.1.vH) (fun i => (getD_hlW_plainHL _ i _ hkk).trans (by rw [hjh]))
  have hrow : ∀ (F : Col D.K → Rg D) (A B : List Bool),
      A = ((List.finRange D.K).map fun i => encRM D.N D.K (F (0, i))).flatten →
      B = ((List.finRange D.K).map fun i => encRM D.N D.K (F (1, i))).flatten →
      pbuf (w rZcol) (([] ++ A) ++ B) = ((Enum.list (α := Col D.K)).map fun c =>
        encRM D.N D.K (F c)).flatten := by
    intro F A B hA hB
    have hl : (A ++ B).length = pnE (Col D.K) * (D.N * D.K) := by
      have := length_rowW (D := D) F
      simp only [map_col, List.flatten_append] at this
      rw [hA, hB]; exact this
    simp only [map_col, List.flatten_append, List.nil_append]
    rw [← hA, ← hB]
    exact pbuf_full (by rw [hz, hl])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ex2]; simp only [Function.update_apply]; simp only [show (rCt = rVp) = False by decide,
      show (rCt = rVk) = False by decide, show (rCt = rSp) = False by decide,
      show (rCt = rSk) = False by decide, if_false]
    rw [d3 _ (by decide)]; simp only [w6, Function.update_of_ne (show rCt ≠ rG by decide)]
    rw [c3 _ (by decide)]; simp only [w4, Function.update_of_ne (show rCt ≠ rCt2 by decide)]
    rw [b1]
    exact hrow (autC0 σ t) _ _ hK0 hP0
  · rw [ex2]; simp only [Function.update_apply]; simp only [show (rCt2 = rVp) = False by decide,
      show (rCt2 = rVk) = False by decide, show (rCt2 = rSp) = False by decide,
      show (rCt2 = rSk) = False by decide, if_false]
    rw [d1]
    refine (hrow (autC1 σ t) _ _ (hK1.trans ?_) (hP1.trans ?_))
    · congr 1
    · congr 1
  · rw [ex2]; simp [Function.update_apply, f7 rSk (by decide), hSk]; exact hdrop (hk σ.2.1.aH) (length_hlW _)
  · rw [ex2]; simp [Function.update_apply, f7 rSp (by decide), hSp]; exact hdrop (hp σ.2.1.aH) (length_hlW _)
  · rw [ex2]; simp [Function.update_apply, f7 rVk (by decide), hVk]; exact hdrop (hk σ.2.1.vH) (length_hlW _)
  · rw [ex2]; simp [Function.update_apply, f7 rVp (by decide), hVp]; exact hdrop (hp σ.2.1.vH) (length_hlW _)
  · rw [ex2]; simp [Function.update_apply, d0]
  · rw [ex2]; exact tmplOK_frame [rSk, rSp, rVk, rVp] (by decide) hT7 fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp [Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]
  · intro j hj
    simp only [autPreW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [ex2]
    simp only [Function.update_apply, hj.2.2.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.2.2.2.2, if_false]
    exact f7 j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.1])

end AdvancedEncryption.ExpLUT.Prog.RedPubP
