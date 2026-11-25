import PE.Impl.ExpLUT.Prog.RedPubPAin

/-!
# The matrices `C_{g_t}` of `A^aut` (package G2, `pubP`)

* **`exec_strMap`**: a strided loop `rep cnt (mv xv tmp xCNK; drop tmp cSkip; post)` whose post
  pushes the canonical word `φ i (x_i)` of the `i`-th strided word `x_i` into a buffer;
* the posts of `aBodyK`, `aBodyV0`, `aBodyV1`: `σ(x)`, `σ(0 − x)`, `σ(2^i − x)` (`exec_postK`,
  `exec_postV0`, `exec_postV1`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram Matrix
open AdvancedEncryption.ExpLUT.Prog.RedVM

variable {D : Dims}

/-- **A strided map loop.** -/
theorem exec_strMap (postL : List Code) (dst : Fin 200) (postW : List (Fin 200))
    (hpw : xv ∉ postW ∧ tmp ∉ postW ∧ cnt ∉ postW ∧ xCNK ∉ postW ∧ cSkip ∉ postW)
    (hwr : ∀ j ∈ wr (ofList postL), j ∈ postW) (hdst : dst ∈ postW)
    (φ : ℕ → Rg D → Rg D) (Q : ℕ → St → Prop)
    (hQ : ∀ i (w1 w2 : St), (∀ j, j ∉ [xv, tmp, cnt] → w2 j = w1 j) → Q i w1 → Q i w2)
    (hpost : ∀ i (w' : St) (b₀ acc : List Bool), (w' xv).length = D.N * D.K →
      w' dst = pbuf b₀ acc → Q i w' →
      exec D.N D.K (ofList postL) w' dst =
          pbuf b₀ (acc ++ encRM D.N D.K (φ i (decRM D.N D.K (w' xv)))) ∧
        Q (i + 1) (exec D.N D.K (ofList postL) w'))
    (w : St) (L : List (List Bool)) (hL : ∀ x ∈ L, x.length = D.N * D.K) (J kk : ℕ) (hJ : 0 < J)
    (hlen : ∀ i < D.K, i * J + kk < L.length) (b₀ acc : List Bool)
    (hs : w tmp = (L.drop kk).flatten) (hd : w dst = pbuf b₀ acc) (hxv : (w xv).length = D.N * D.K)
    (hc : (w xCNK).length = D.N * D.K) (hk : (w cSkip).length = (J - 1) * (D.N * D.K))
    (hn : (w cnt).length = D.K) (hQ0 : Q 0 w) :
    let w' := exec D.N D.K (.rep cnt (ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postL))) w
    w' dst = pbuf b₀ (acc ++ ((List.range D.K).map fun i =>
        encRM D.N D.K (φ i (decRM D.N D.K (L.getD (i * J + kk) [])))).flatten) ∧
      (w' xv).length = D.N * D.K ∧ Q D.K w' ∧ ∀ j, j ∉ xv :: tmp :: cnt :: postW → w' j = w j := by
  intro w'
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpw
  have hc' : cnt ∉ wr (ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postL)) := by
    rw [wr_ofList, List.flatMap_append]
    simp only [List.mem_append, not_or]
    refine ⟨by decide, fun h => p3 (hwr cnt (by rw [wr_ofList]; exact h))⟩
  let P : ℕ → St → Prop := fun i w2 =>
    w2 dst = pbuf b₀ (acc ++ ((List.range i).map fun i =>
        encRM D.N D.K (φ i (decRM D.N D.K (L.getD (i * J + kk) [])))).flatten) ∧
      w2 tmp = (L.drop (i * J + kk)).flatten ∧ (w2 xv).length = D.N * D.K ∧ Q i w2 ∧
      ∀ j, j ∉ xv :: tmp :: cnt :: postW → w2 j = w j
  have h0 : P 0 w := ⟨by simp [hd], by simp [hs], hxv, hQ0, fun _ _ => rfl⟩
  have key := exec_rep_inv (N := D.N) (K := D.K) cnt _ hc' P w h0 (fun i hi w1 hP _ => by
    rw [hn] at hi
    obtain ⟨q1, q2, q3, q4, q5⟩ := hP
    set u := Function.update w1 cnt (w1 cnt).tail
    have hu : ∀ j, j ≠ cnt → u j = w1 j := fun j hj => Function.update_of_ne hj _ _
    have hm := hlen i hi
    have hx := hL _ (List.getElem_mem hm)
    have hcu : (u xCNK).length = D.N * D.K := by
      rw [hu _ (by decide), q5 _ (by simp [p4]), hc]
    have e1 := exec_mv_pop (N := D.N) (K := D.K) (d := xv) (s := tmp) (c := xCNK) (by decide)
      (w := u) (v := L[i * J + kk]) (L := (L.drop (i * J + kk + 1)).flatten)
      (by rw [hu _ (by decide), q3, hcu]) (by rw [hx, hcu])
      (by rw [hu _ (by decide), q2, flatten_drop_cons hm])
    set u1 := Function.update (Function.update u tmp (L.drop (i * J + kk + 1)).flatten) xv L[i * J + kk]
    have hsk : (u1 cSkip).length = (J - 1) * (D.N * D.K) := by
      simp only [u1, Function.update_apply]
      simp only [show (cSkip = xv) = False by decide, show (cSkip = tmp) = False by decide, if_false]
      rw [hu _ (by decide), q5 _ (by simp [p5]), hk]
    have e2 := exec_drop_eq (N := D.N) (K := D.K) (t := tmp) (c := cSkip) (by decide) u1
    set u2 := Function.update u1 tmp ((u1 tmp).drop (u1 cSkip).length)
    have hu2t : u2 tmp = (L.drop ((i + 1) * J + kk)).flatten := by
      simp only [u2, Function.update_self, hsk]
      simp only [u1, Function.update_apply, show (tmp = xv) = False by decide, if_false, if_true]
      rw [flatten_drop_drop hL]
      congr 2; rw [Nat.succ_mul]; omega
    have hfr2 : ∀ j, j ∉ [xv, tmp, cnt] → u2 j = w1 j := by
      intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp [u2, u1, Function.update_apply, hj.1, hj.2.1, hu j hj.2.2]
    have hQ2 : Q i u2 := hQ i w1 u2 hfr2 q4
    have hd2 : u2 dst = pbuf b₀ (acc ++ ((List.range i).map fun i =>
        encRM D.N D.K (φ i (decRM D.N D.K (L.getD (i * J + kk) [])))).flatten) := by
      rw [hfr2 dst (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => p1 (h ▸ hdst), fun h => p2 (h ▸ hdst), fun h => p3 (h ▸ hdst)⟩), q1]
    have hxv2 : u2 xv = L[i * J + kk] := by simp [u2, u1, Function.update_apply]
    have hxl : (u2 xv).length = D.N * D.K := by rw [hxv2, hx]
    obtain ⟨r1', r2'⟩ := hpost i u2 b₀ _ hxl hd2 hQ2
    have ex : exec D.N D.K (ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postL)) u =
        exec D.N D.K (ofList postL) u2 := by
      rw [exec_ofList_append]
      show exec D.N D.K (ofList postL) (exec D.N D.K (.drop tmp cSkip) (exec D.N D.K (.mv xv tmp xCNK) u)) = _
      rw [e1, e2]
    rw [ex]
    have hnot : ∀ j, j ∉ postW → exec D.N D.K (ofList postL) u2 j = u2 j := fun j hj =>
      exec_not_mem _ u2 j (fun h => hj (hwr j h))
    refine ⟨?_, ?_, ?_, r2', ?_⟩
    · rw [r1', hxv2, List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
        List.flatten_singleton, List.append_assoc, List.getD_eq_getElem _ _ hm]
    · rw [hnot _ p2, hu2t]
    · rw [hnot _ p1, hxl]
    · intro j hj
      have hj' : j ∉ postW := fun h => hj (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ h)))
      simp only [List.mem_cons, not_or] at hj
      rw [hnot j hj', hfr2 j (by simp [hj.1, hj.2.1, hj.2.2.1]),
        q5 j (by simp [hj.1, hj.2.1, hj.2.2.1, hj'])])
  rw [hn] at key
  exact ⟨key.1, key.2.2.1, key.2.2.2.1, key.2.2.2.2⟩

/-! ### The posts -/

theorem kR_isT (t : ℕ) (ht : t < 32) : isT (kR t) = true := by
  simp [isT, kR, Nat.mod_eq_of_lt ht]; omega

theorem kR_ne_r1 (t : ℕ) (ht : t < 32) : kR t ≠ r1 := fun h => by
  have := congrArg Fin.val h; simp [kR, Nat.mod_eq_of_lt ht] at this; omega

theorem len_kR {w : St} (hT : TmplOK D w) (t : ℕ) (ht : t < 32) : (w (kR t)).length = κD D t := by
  rw [hT.len (kR t) (kR_isT t ht) (kR_ne_r1 t ht), tm_kR t ht]

/-- `σ_{g_t}` then the canonical word. -/
theorem canon_aut (t : ℕ) {x : List Bool} (hx : x.length = D.N * D.K) :
    canonW D.N D.K (opd D.N D.K (autMW D.N D.K (κD D t) x)) =
      encRM D.N D.K ((setting D).E.σ ((setting D).kf t) (decRM D.N D.K x)) := by
  have hl := length_autMW D.N D.K (κD D t) x D.N_pos
  rw [opd_eq hl, canonW_eq D.K_pos hl, decRM_autMW (κD_pos D t) hx, σ_kf]

theorem kR_ne (t : ℕ) (ht : t < 32) (r : Fin 200) (hr : isT r = false) : kR t ≠ r := fun h => by
  rw [← h, kR_isT t ht] at hr; exact absurd hr (by decide)

/-- The post of the row `0`: `σ(x)` into `rCt`. -/
def postK (t : ℕ) : List Code := [.aut xS xv (kR t), .canon xO xS, .mv rCt xO xCNK]

theorem aBodyK_eq (t : ℕ) : aBodyK t = ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postK t) := rfl

theorem exec_postK (t : ℕ) (ht : t < 32) (i : ℕ) (w' : St) (b₀ acc : List Bool)
    (hx : (w' xv).length = D.N * D.K) (hd : w' rCt = pbuf b₀ acc) (hT : TmplOK D w') :
    exec D.N D.K (ofList (postK t)) w' rCt =
        pbuf b₀ (acc ++ encRM D.N D.K ((setting D).E.σ ((setting D).kf t) (decRM D.N D.K (w' xv)))) ∧
      TmplOK D (exec D.N D.K (ofList (postK t)) w') := by
  have hk := len_kR hT t ht
  set y := autMW D.N D.K (κD D t) (w' xv)
  set z := encRM D.N D.K ((setting D).E.σ ((setting D).kf t) (decRM D.N D.K (w' xv)))
  have e : exec D.N D.K (ofList (postK t)) w' =
      exec D.N D.K (.mv rCt xO xCNK) (Function.update (Function.update w' xS y) xO z) := by
    simp only [postK, exec_ofList_cons, exec_ofList_nil]
    simp only [exec, Function.update_self, hk, opd_eq hx]
    rw [canon_aut t hx]
  have e2 := exec_mv_blk (N := D.N) (K := D.K) (d := rCt) (s := xO) (c := xCNK) (by decide)
    (w := Function.update (Function.update w' xS y) xO z) (b₀ := b₀) (acc := acc) (v := z) (L := [])
    (by simp [Function.update_apply, hd]) (by simp [Function.update_apply, z, length_encRM, hT.len xCNK])
    (by simp)
  rw [e, e2]
  refine ⟨by simp, tmplOK_frame [xS, xO, rCt] (by decide) hT fun j hj => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp [Function.update_apply, hj.1, hj.2.1, hj.2.2]

/-- The post of the first half of the row `1`: `σ(0 − x)` into `rCt2`. -/
def postV0 (t : ℕ) : List Code :=
  [.sub xS xZero xv, .aut rT1 xS (kR t), .canon xO rT1, .mv rCt2 xO xCNK]

theorem aBodyV0_eq (t : ℕ) : aBodyV0 t = ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postV0 t) :=
  rfl

theorem exec_postV0 (t : ℕ) (ht : t < 32) (i : ℕ) (w' : St) (b₀ acc : List Bool)
    (hx : (w' xv).length = D.N * D.K) (hd : w' rCt2 = pbuf b₀ acc) (hT : TmplOK D w') :
    exec D.N D.K (ofList (postV0 t)) w' rCt2 =
        pbuf b₀ (acc ++ encRM D.N D.K ((setting D).E.σ ((setting D).kf t) (0 - decRM D.N D.K (w' xv)))) ∧
      TmplOK D (exec D.N D.K (ofList (postV0 t)) w') := by
  have hk := len_kR hT t ht
  have hZ : w' xZero = List.replicate (D.N * D.K) false := hT.get xZero
  set s0 := subRMW D.N D.K (w' xZero) (w' xv)
  have hs0 : s0.length = D.N * D.K := length_subRMW _ _ (by rw [hZ]; simp) _
  have hs0v : decRM D.N D.K s0 = 0 - decRM D.N D.K (w' xv) := by
    rw [decRM_subRMW (by rw [hZ]; simp) hx, hZ, decRM_replicate]
  set y := autMW D.N D.K (κD D t) s0
  set z := encRM D.N D.K ((setting D).E.σ ((setting D).kf t) (0 - decRM D.N D.K (w' xv)))
  have hk' : (Function.update w' xS s0 (kR t)).length = κD D t := by
    rw [Function.update_of_ne (kR_ne t ht xS (by decide)), hk]
  have e0 : exec D.N D.K (ofList [.sub xS xZero xv, .aut rT1 xS (kR t), .canon xO rT1]) w' =
      Function.update (Function.update (Function.update w' xS s0) rT1 y) xO z := by
    simp only [exec_ofList_cons, exec_ofList_nil]
    simp only [exec]
    rw [opd_eq (by rw [hZ]; simp), opd_eq hx]
    show Function.update (Function.update (Function.update w' xS s0) rT1
      (autMW D.N D.K (Function.update w' xS s0 (kR t)).length (opd D.N D.K s0))) xO
      (canonW D.N D.K (opd D.N D.K (autMW D.N D.K (Function.update w' xS s0 (kR t)).length
        (opd D.N D.K s0)))) = _
    rw [hk', opd_eq hs0, canon_aut t hs0, hs0v]
  have e : exec D.N D.K (ofList (postV0 t)) w' =
      exec D.N D.K (.mv rCt2 xO xCNK)
        (Function.update (Function.update (Function.update w' xS s0) rT1 y) xO z) := by
    show exec D.N D.K (ofList ([.sub xS xZero xv, .aut rT1 xS (kR t), .canon xO rT1] ++
      [.mv rCt2 xO xCNK])) w' = _
    rw [exec_ofList_append, e0]; rfl
  have e2 := exec_mv_blk (N := D.N) (K := D.K) (d := rCt2) (s := xO) (c := xCNK) (by decide)
    (w := Function.update (Function.update (Function.update w' xS s0) rT1 y) xO z) (b₀ := b₀)
    (acc := acc) (v := z) (L := [])
    (by simp [Function.update_apply, hd]) (by simp [Function.update_apply, z, length_encRM, hT.len xCNK])
    (by simp)
  rw [e, e2]
  refine ⟨by simp, tmplOK_frame [xS, rT1, xO, rCt2] (by decide) hT fun j hj => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp [Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]

/-- The post of the second half of the row `1`: `σ(2^i − x)` into `rCt2`, `rG := 2 rG`. -/
def postV1 (t : ℕ) : List Code :=
  [.sub xS rG xv, .aut rT1 xS (kR t), .canon xO rT1, .mv rCt2 xO xCNK, .add rG rG rG]

theorem aBodyV1_eq (t : ℕ) : aBodyV1 t = ofList ([.mv xv tmp xCNK, .drop tmp cSkip] ++ postV1 t) :=
  rfl

/-- The state of `rG` in round `i`: the word of `2^i`. -/
def QG (i : ℕ) (w : St) : Prop :=
  TmplOK D w ∧ (w rG).length = D.N * D.K ∧
    decRM D.N D.K (w rG) = (2 : ZMod (2 ^ D.K - 1)) ^ i • (1 : Rg D)

theorem exec_postV1 (t : ℕ) (ht : t < 32) (i : ℕ) (w' : St) (b₀ acc : List Bool)
    (hx : (w' xv).length = D.N * D.K) (hd : w' rCt2 = pbuf b₀ acc) (hQ : QG (D := D) i w') :
    exec D.N D.K (ofList (postV1 t)) w' rCt2 =
        pbuf b₀ (acc ++ encRM D.N D.K ((setting D).E.σ ((setting D).kf t)
          ((2 : ZMod (2 ^ D.K - 1)) ^ i • (1 : Rg D) - decRM D.N D.K (w' xv)))) ∧
      QG (D := D) (i + 1) (exec D.N D.K (ofList (postV1 t)) w') := by
  obtain ⟨hT, hGl, hGv⟩ := hQ
  have hk := len_kR hT t ht
  set s0 := subRMW D.N D.K (w' rG) (w' xv)
  have hs0 : s0.length = D.N * D.K := length_subRMW _ _ hGl _
  have hs0v : decRM D.N D.K s0 = (2 : ZMod (2 ^ D.K - 1)) ^ i • (1 : Rg D) - decRM D.N D.K (w' xv) := by
    rw [decRM_subRMW hGl hx, hGv]
  set y := autMW D.N D.K (κD D t) s0
  set z := encRM D.N D.K ((setting D).E.σ ((setting D).kf t)
    ((2 : ZMod (2 ^ D.K - 1)) ^ i • (1 : Rg D) - decRM D.N D.K (w' xv)))
  have hk' : (Function.update w' xS s0 (kR t)).length = κD D t := by
    rw [Function.update_of_ne (kR_ne t ht xS (by decide)), hk]
  set w3 := Function.update (Function.update (Function.update w' xS s0) rT1 y) xO z
  have e : exec D.N D.K (ofList [.sub xS rG xv, .aut rT1 xS (kR t), .canon xO rT1]) w' = w3 := by
    simp only [exec_ofList_cons, exec_ofList_nil]
    simp only [exec]
    rw [opd_eq hGl, opd_eq hx]
    show Function.update (Function.update (Function.update w' xS s0) rT1
      (autMW D.N D.K (Function.update w' xS s0 (kR t)).length (opd D.N D.K s0))) xO
      (canonW D.N D.K (opd D.N D.K (autMW D.N D.K (Function.update w' xS s0 (kR t)).length
        (opd D.N D.K s0)))) = _
    rw [hk', opd_eq hs0, canon_aut t hs0, hs0v]
  have e2 := exec_mv_blk (N := D.N) (K := D.K) (d := rCt2) (s := xO) (c := xCNK) (by decide)
    (w := w3) (b₀ := b₀) (acc := acc) (v := z) (L := [])
    (by simp [w3, Function.update_apply, hd]) (by simp [w3, Function.update_apply, z, length_encRM, hT.len xCNK])
    (by simp [w3])
  set w4 := Function.update (Function.update w3 xO []) rCt2 (pbuf b₀ (acc ++ z))
  have hG4 : w4 rG = w' rG := by simp [w4, w3, Function.update_apply]
  have ex : exec D.N D.K (ofList (postV1 t)) w' =
      Function.update w4 rG (addRMW D.N D.K (w' rG) (w' rG)) := by
    show exec D.N D.K (ofList ([.sub xS rG xv, .aut rT1 xS (kR t), .canon xO rT1] ++
      [.mv rCt2 xO xCNK, .add rG rG rG])) w' = _
    rw [exec_ofList_append, e]
    show exec D.N D.K (.add rG rG rG) (exec D.N D.K (.mv rCt2 xO xCNK) w3) = _
    rw [e2]
    show exec D.N D.K (.add rG rG rG) w4 = _
    rw [show exec D.N D.K (.add rG rG rG) w4 = Function.update w4 rG
      (addRMW D.N D.K (opd D.N D.K (w4 rG)) (opd D.N D.K (w4 rG))) from rfl, hG4, opd_eq hGl]
  rw [ex]
  refine ⟨by simp [w4], tmplOK_frame [xS, rT1, xO, rCt2, rG] (by decide) hT fun j hj => ?_,
    by simp [length_addRMW _ _ hGl], ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [w4, w3, Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2]
  · rw [Function.update_self, decRM_addRMW hGl hGl, hGv, pow_succ, mul_comm, mul_smul, two_smul]

end AdvancedEncryption.ExpLUT.Prog.RedPubP
