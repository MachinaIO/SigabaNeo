import PE.Impl.ExpLUT.Prog.RedPubPParse
open SigabaNeo.Tape.RingVM.Buf SigabaNeo.Tape.RingVM.Hash
/-!
# The outputs `B` and `H` (package G2, `pubP`)

* **`exec_outBC`**: `B = [aB; B⁽²⁾]` (`wB`) shifted into `rOut`;
* `exec_colC`: a strided column of a helper block;
* `getD_flatten_rows`, `col_keyHL`, `col_plainHL`: the column `k` of the helper blocks is the
  half `(·, i)` of `aH k`;
* **`exec_outHC`**: `H` (`wH`) shifted into `rOut`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-! ### `B` -/

theorem exec_cp (N K : ℕ) (d s : Fin 200) (w : St) :
    exec N K (.cp d s) w = Function.update w d (w s) := rfl

/-- **`B`.** -/
theorem exec_outBC (σ : RawSec D) (w : St) (hT : TmplOK D w) (b₀ acc : List Bool)
    (hO : w rOut = pbuf b₀ acc) (hAB : w rAB = pwordsOf σ.2.1.aB) (hB2 : w rB2 = pwordsOf σ.2.2.1) :
    exec D.N D.K outBC w rOut = pbuf b₀ (acc ++ wB σ) ∧
      ∀ j, j ≠ rOut → j ≠ tmp → exec D.N D.K outBC w j = w j := by
  simp only [outBC, exec_ofList_cons, exec_ofList_nil, exec_cp]
  rw [exec_mv_blk (d := rOut) (s := tmp) (c := cBC) (by decide) (b₀ := b₀) (acc := acc)
    (w := Function.update w tmp (w rAB)) (v := pwordsOf σ.2.1.aB) (L := []) (by simp [Function.update_apply, hO])
    (by simp [Function.update_apply, hT.len cBC]; exact length_pwordsOf _)
    (by simp [Function.update_apply, hAB])]
  rw [exec_mv_blk (d := rOut) (s := tmp) (c := cBC) (by decide) (b₀ := b₀)
    (acc := acc ++ pwordsOf σ.2.1.aB) (v := pwordsOf σ.2.2.1) (L := [])
    (by simp [Function.update_apply])
    (by simp [Function.update_apply, hT.len cBC]; exact length_pwordsOf _)
    (by simp [Function.update_apply, hB2])]
  refine ⟨by simp [wB, List.append_assoc], fun j h1 h2 => by simp [Function.update_apply, h1, h2]⟩

/-! ### Strided columns -/

/-- **A strided column** of a helper block. -/
theorem exec_colC (src : Fin 200) (h1 : src ≠ tmp) (h2 : src ≠ cnt) (h3 : src ≠ rOut)
    (h4 : src ≠ xCNK) (w : St) (hT : TmplOK D w) (L : List (List Bool))
    (hL : ∀ x ∈ L, x.length = D.N * D.K) (kk : ℕ) (hJ : 0 < pnE (Jh D))
    (hlen : ∀ i < D.K, i * pnE (Jh D) + kk < L.length)
    (hsrc : w src = (L.drop kk).flatten) (b₀ acc : List Bool) (hO : w rOut = pbuf b₀ acc) :
    exec D.N D.K (colC src) w rOut =
        pbuf b₀ (acc ++ ((List.range D.K).map fun i => L.getD (i * pnE (Jh D) + kk) []).flatten) ∧
      exec D.N D.K (colC src) w src = (L.drop (kk + 1)).flatten ∧
      ∀ j, j ≠ rOut → j ≠ tmp → j ≠ cnt → j ≠ src → exec D.N D.K (colC src) w j = w j := by
  simp only [colC, exec_ofList_cons, exec_ofList_nil, exec_cp]
  set w1 := Function.update (Function.update w tmp (w src)) cnt (Function.update w tmp (w src) cK)
  obtain ⟨a1, a2, a3⟩ := exec_strided (N := D.N) (K := D.K) (d := rOut) (s := tmp) (c := xCNK)
    (k := cSkip) (cnt := cnt) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) w1 (D.N * D.K) (pnE (Jh D)) D.K kk hJ L hL hlen
    b₀ acc (by simp [w1, Function.update_apply, hO]) (by simp [w1, Function.update_apply, hsrc])
    (by simp [w1, Function.update_apply, hT.len xCNK])
    (by simp [w1, Function.update_apply, hT.len cSkip]) (by simp [w1, Function.update_apply, hT.len cK])
  set w2 := exec D.N D.K (.rep cnt (sBody rOut tmp xCNK cSkip)) w1
  have hs2 : w2 src = (L.drop kk).flatten := by
    rw [a3 src h3 h1 h2]; simp [w1, Function.update_apply, h1, h2, hsrc]
  rw [exec_drop_eq (by intro h; exact h4 h)]
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by intro h; exact h3 h.symm), a1]
  · have hc2 : (w2 xCNK).length = D.N * D.K := by
      rw [a3 xCNK (by decide) (by decide) (by decide)]
      simp [w1, Function.update_apply, hT.len xCNK]
    rw [Function.update_self, hs2, hc2, show D.N * D.K = 1 * (D.N * D.K) by ring,
      flatten_drop_drop hL]
  · intro j j1 j2 j3 j4
    rw [Function.update_of_ne j4, a3 j j1 j2 j3]
    simp [w1, Function.update_apply, j2, j3]

/-! ### The columns of the helper blocks -/

theorem getD_flatten_rows {α : Type} (d : α) (J : ℕ) :
    ∀ (R : List (List α)), (∀ r ∈ R, r.length = J) → ∀ i k, k < J →
      R.flatten.getD (i * J + k) d = (R.getD i []).getD k d
  | [], _, i, k, _ => by simp
  | r :: R, hR, 0, k, hk => by
    rw [List.flatten_cons, zero_mul, zero_add, List.getD_append _ _ _ _ (by rw [hR r (by simp)]; exact hk)]
    simp
  | r :: R, hR, i + 1, k, hk => by
    rw [List.flatten_cons, List.getD_append_right _ _ _ _ (by rw [hR r (by simp)]; nlinarith)]
    rw [hR r (by simp), show (i + 1) * J + k - J = i * J + k by rw [Nat.succ_mul]; omega,
      getD_flatten_rows d J R (fun x hx => hR x (by simp [hx])) i k hk]
    simp

/-- The words of a helper block. -/
noncomputable def hlW (l : List (Rg D)) : List (List Bool) := l.map (encRM D.N D.K)

theorem ringWords_hlW (l : List (Rg D)) : ringWords l = (hlW l).flatten := rfl

theorem length_hlW (l : List (Rg D)) : ∀ x ∈ hlW l, x.length = D.N * D.K := by
  intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _

theorem getD_hlW_keyHL (F : Jh D → Col D.K → Rg D) (i : Fin D.K) (kk : ℕ) (hk : kk < pnE (Jh D)) :
    (hlW (keyHL D F)).getD (i * pnE (Jh D) + kk) [] =
      encRM D.N D.K (F ((Enum.list (α := Jh D))[kk]) (0, i)) := by
  rw [hlW, keyHL, List.map_flatten, getD_flatten_rows [] (pnE (Jh D)) _ (by
    intro r hr; simp only [List.map_map, List.mem_map] at hr
    obtain ⟨_, _, rfl⟩ := hr; simp) i kk hk]
  have hk' : kk < (Enum.list (α := Jh D)).length := hk
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hk']

theorem getD_hlW_plainHL (F : Jh D → Col D.K → Rg D) (i : Fin D.K) (kk : ℕ) (hk : kk < pnE (Jh D)) :
    (hlW (plainHL D F)).getD (i * pnE (Jh D) + kk) [] =
      encRM D.N D.K (F ((Enum.list (α := Jh D))[kk]) (1, i)) := by
  rw [hlW, plainHL, List.map_flatten, getD_flatten_rows [] (pnE (Jh D)) _ (by
    intro r hr; simp only [List.map_map, List.mem_map] at hr
    obtain ⟨_, _, rfl⟩ := hr; simp) i kk hk]
  have hk' : kk < (Enum.list (α := Jh D)).length := hk
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hk']

theorem length_hlW_keyHL (F : Jh D → Col D.K → Rg D) :
    (hlW (keyHL D F)).length = D.K * pnE (Jh D) := by rw [hlW, List.length_map, length_keyHL]

theorem length_hlW_plainHL (F : Jh D → Col D.K → Rg D) :
    (hlW (plainHL D F)).length = D.K * pnE (Jh D) := by rw [hlW, List.length_map, length_plainHL]

/-! ### `H` -/

/-- The words of `H⁽²⁾_k`, along `Enum Jh`. -/
noncomputable def h2L (σ : RawSec D) : List (List Bool) :=
  (Enum.list (α := Jh D)).map fun k => pwordsOf (σ.2.2.2.1 k)

theorem ph2W_eq (σ : RawSec D) : ph2W σ = (h2L σ).flatten := by
  rw [ph2W, pfun_enc]
  exact congrArg List.flatten (List.map_congr_left fun k _ => vecE_wordsOf _)

theorem length_h2L (σ : RawSec D) : ∀ x ∈ h2L σ, x.length = pnE (Col D.K) * (D.N * D.K) := by
  intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_pwordsOf _

/-- The block of `H_k` (`k` the `kk`-th helper). -/
noncomputable def hBlk (σ : RawSec D) (kk : ℕ) : List Bool :=
  ((List.range D.K).map fun i => (hlW (keyHL D σ.2.1.aH)).getD (i * pnE (Jh D) + kk) []).flatten ++
    (((List.range D.K).map fun i => (hlW (plainHL D σ.2.1.aH)).getD (i * pnE (Jh D) + kk) []).flatten ++
      (h2L σ).getD kk [])

theorem hBlk_eq (σ : RawSec D) :
    ((List.range (pnE (Jh D))).map (hBlk σ)).flatten = wH σ := by
  rw [wH]
  congr 1
  refine List.ext_getElem (by simp) fun kk h1 h2 => ?_
  have hk : kk < pnE (Jh D) := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, hBlk]
  rw [map_range_finRange, map_range_finRange, pwordsOf]
  erw [map_col]
  rw [List.flatten_append, List.append_assoc]
  congr 1
  · congr 1
    exact List.map_congr_left fun i _ => getD_hlW_keyHL _ i kk hk
  · congr 1
    · congr 1
      exact List.map_congr_left fun i _ => getD_hlW_plainHL _ i kk hk
    · rw [h2L, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

theorem tmplOK_of_agree {w w' : St} (h : TmplOK D w) (ha : ∀ r, isT r = true → w' r = w r) :
    TmplOK D w' :=
  ⟨fun r hr hr1 => by rw [ha r hr, h.1 r hr hr1], by rw [ha r1 (by decide), h.2]⟩

/-- **The loop of `H`.** -/
theorem exec_hLoop (σ : RawSec D) (w : St) (hT : TmplOK D w) (b₀ acc : List Bool)
    (hO : w rOut = pbuf b₀ acc) (hSk : w rSk = (hlW (keyHL D σ.2.1.aH)).flatten)
    (hSp : w rSp = (hlW (plainHL D σ.2.1.aH)).flatten) (hH2 : w rH2s = (h2L σ).flatten)
    (hc : (w cntJ).length = pnE (Jh D)) :
    exec D.N D.K (.rep cntJ hBody) w rOut = pbuf b₀ (acc ++ wH σ) ∧
      ∀ j, j ∉ [rOut, tmp, cnt, rSk, rSp, rH2s] → j ≠ cntJ → exec D.N D.K (.rep cntJ hBody) w j = w j := by
  set Lk := hlW (keyHL D σ.2.1.aH)
  set Lp := hlW (plainHL D σ.2.1.aH)
  have hLk : ∀ x ∈ Lk, x.length = D.N * D.K := length_hlW _
  have hLp : ∀ x ∈ Lp, x.length = D.N * D.K := length_hlW _
  have hlenk : Lk.length = D.K * pnE (Jh D) := length_hlW_keyHL _
  have hlenp : Lp.length = D.K * pnE (Jh D) := length_hlW_plainHL _
  let P : ℕ → St → Prop := fun kk w' =>
    w' rOut = pbuf b₀ (acc ++ ((List.range kk).map (hBlk σ)).flatten) ∧
      w' rSk = (Lk.drop kk).flatten ∧ w' rSp = (Lp.drop kk).flatten ∧
      w' rH2s = ((h2L σ).drop kk).flatten ∧ TmplOK D w' ∧
      ∀ j, j ∉ [rOut, tmp, cnt, rSk, rSp, rH2s] → j ≠ cntJ → w' j = w j
  have hcw : cntJ ∉ wr hBody := by decide
  have h0 : P 0 w := ⟨by simp [hO], by simp [hSk], by simp [hSp], by simp [hH2], hT,
    fun _ _ _ => rfl⟩
  have key := exec_rep_inv (N := D.N) (K := D.K) cntJ hBody hcw P w h0 (fun kk hkk w' hP _ => by
    have hkk' : kk < pnE (Jh D) := by rw [hc] at hkk; exact hkk
    have hJ : 0 < pnE (Jh D) := by omega
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP
    set u := Function.update w' cntJ (w' cntJ).tail
    have hu : ∀ j, j ≠ cntJ → u j = w' j := fun j hj => Function.update_of_ne hj _ _
    have hTu : TmplOK D u := tmplOK_of_agree p5 fun r hr => hu r (fun h => by subst h; revert hr; decide)
    have hlenI : ∀ (L : List (List Bool)), L.length = D.K * pnE (Jh D) →
        ∀ i < D.K, i * pnE (Jh D) + kk < L.length := by
      intro L hL i hi; rw [hL]; nlinarith
    obtain ⟨a1, a2, a3⟩ := exec_colC (D := D) rSk (by decide) (by decide) (by decide) (by decide)
      u hTu Lk hLk kk hJ (hlenI Lk hlenk) (by rw [hu _ (by decide), p2]) b₀ _
      (by rw [hu _ (by decide), p1])
    set u1 := exec D.N D.K (colC rSk) u
    have hTu1 : TmplOK D u1 := tmplOK_exec (colC rSk) (by decide) hTu
    obtain ⟨b1, b2, b3⟩ := exec_colC (D := D) rSp (by decide) (by decide) (by decide) (by decide)
      u1 hTu1 Lp hLp kk hJ (hlenI Lp hlenp)
      (by rw [a3 _ (by decide) (by decide) (by decide) (by decide), hu _ (by decide), p3]) b₀ _ a1
    set u2 := exec D.N D.K (colC rSp) u1
    have hkH : kk < (h2L σ).length := by simpa [h2L] using hkk'
    have e3 := exec_mv_blk (N := D.N) (K := D.K) (d := rOut) (s := rH2s) (c := cColW) (by decide)
      (w := u2) (b₀ := b₀) (v := (h2L σ)[kk]) (L := ((h2L σ).drop (kk + 1)).flatten) b1
      (by rw [length_h2L σ _ (List.getElem_mem hkH), b3 _ (by decide) (by decide) (by decide)
        (by decide), a3 _ (by decide) (by decide) (by decide) (by decide), hTu.len cColW]; rfl)
      (by rw [b3 _ (by decide) (by decide) (by decide) (by decide), a3 _ (by decide) (by decide)
        (by decide) (by decide), hu _ (by decide), p4, flatten_drop_cons hkH])
    have ex : exec D.N D.K hBody u = exec D.N D.K (.mv rOut rH2s cColW) u2 := rfl
    rw [ex, e3]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_self, List.range_succ, List.map_append, List.flatten_append,
        List.map_singleton, List.flatten_singleton, hBlk, List.getD_eq_getElem _ _ hkH]
      simp only [List.append_assoc]; rfl
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        b3 _ (by decide) (by decide) (by decide) (by decide), a2]
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), b2]
    · rw [Function.update_of_ne (by decide), Function.update_self]
    · rw [← e3]
      exact tmplOK_exec (.mv rOut rH2s cColW) (by decide) (tmplOK_exec (colC rSp) (by decide) hTu1)
    · intro j hj j7
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hj
      rw [Function.update_of_ne j1, Function.update_of_ne j6, b3 j j1 j2 j3 j5,
        a3 j j1 j2 j3 j4, hu j j7]
      exact p6 j (by simp [j1, j2, j3, j4, j5, j6]) j7)
  rw [hc] at key
  obtain ⟨k1, -, -, -, -, k6⟩ := key
  exact ⟨by rw [k1, hBlk_eq], k6⟩

/-- **`H`.** -/
theorem exec_outHC (σ : RawSec D) (w : St) (hT : TmplOK D w) (b₀ acc : List Bool)
    (hO : w rOut = pbuf b₀ acc) (hAHp : w rAHp = ringWords (plainHL D σ.2.1.aH))
    (hAHk : w rAHk = ringWords (keyHL D σ.2.1.aH)) (hH2 : w rH2 = ph2W σ) :
    exec D.N D.K outHC w rOut = pbuf b₀ (acc ++ wH σ) ∧
      ∀ j, j ∉ [rOut, tmp, cnt, rSk, rSp, rH2s, cntJ] → exec D.N D.K outHC w j = w j := by
  have ex : exec D.N D.K outHC w = exec D.N D.K (.rep cntJ hBody)
      (exec D.N D.K (ofList [.cp rSk rAHk, .cp rSp rAHp, .cp rH2s rH2, .cp cntJ cJ]) w) := rfl
  set w1 := exec D.N D.K (ofList [.cp rSk rAHk, .cp rSp rAHp, .cp rH2s rH2, .cp cntJ cJ]) w
  have hw1 : ∀ j, j ∉ [rSk, rSp, rH2s, cntJ] → w1 j = w j := fun j hj =>
    exec_not_mem _ w j (by simpa [wr, ofList] using hj)
  have hT1 : TmplOK D w1 := tmplOK_exec _ (by decide) hT
  obtain ⟨k1, k2⟩ := exec_hLoop σ w1 hT1 b₀ acc
    (by rw [hw1 _ (by decide), hO])
    (by simp [w1, exec_ofList_cons, exec_ofList_nil, exec_cp, Function.update_apply, hAHk, ringWords_hlW])
    (by simp [w1, exec_ofList_cons, exec_ofList_nil, exec_cp, Function.update_apply, hAHp, ringWords_hlW])
    (by simp [w1, exec_ofList_cons, exec_ofList_nil, exec_cp, Function.update_apply, hH2, ph2W_eq])
    (by simp [w1, exec_ofList_cons, exec_ofList_nil, exec_cp, Function.update_apply, hT.len cJ])
  rw [ex]
  refine ⟨k1, fun j hj => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ := hj
  rw [k2 j (by simp [j1, j2, j3, j4, j5, j6]) j7, hw1 j (by simp [j4, j5, j6, j7])]

end AdvancedEncryption.ExpLUT.Prog.RedPubP
