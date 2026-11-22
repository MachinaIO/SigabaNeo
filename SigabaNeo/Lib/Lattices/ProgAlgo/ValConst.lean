import SigabaNeo.Lib.Lattices.ProgAlgo.ValFhat

/-!
# The constant bundle on the word machine

`cbC` shifts the word of the constant bundle `constRepVV one zv (gvExp q)` (the bundle of the wire
`1` of `f̂`, `q = 2 ^ K`) into `RES` (`exec_cbC`): for each `(a, col)` and `i`, the value
`constV one zv k (2 ^ col.2 mod q)` at `i` when `a = col.1` (else `zv`) at `t = 0`, and `zv` at the
other `N − 1` coefficients.
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo SigabaNeo.Encode

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

abbrev ES : Fin 120 := 87

/-! ### Pushing copies of a value -/

/-- One copy of the value `src` shifted into `RES`. -/
def pushR (src : Fin 120) : Code := ofList [.cp rY src, .mvV RES rY]

theorem exec_pushRep {src ctr : Fin 120} (hs : src ≠ rY ∧ src ≠ RES ∧ src ≠ ctr)
    (hc : ctr ≠ rY ∧ ctr ≠ RES) (w : St) (hv : (w src).length = V) :
    exec V f (.rep ctr (pushR src)) w RES =
        (w RES ++ (List.replicate (w ctr).length (w src)).flatten).drop ((w ctr).length * V) ∧
      ∀ j, j ≠ rY → j ≠ RES → j ≠ ctr → exec V f (.rep ctr (pushR src)) w j = w j := by
  have I := exec_rep_inv (V := V) (f := f) (c := ctr) (B := pushR src)
    (fun r w' => w' RES = (w RES ++ (List.replicate r (w src)).flatten).drop (r * V) ∧
      ∀ j, j ≠ rY → j ≠ RES → j ≠ ctr → w' j = w j)
    (fun r w' ih => by
      obtain ⟨h1, h2⟩ := ih
      have hsrc : Function.update w' ctr (w' ctr).tail src = w src := by
        rw [Function.update_of_ne hs.2.2, h2 src hs.1 hs.2.1 hs.2.2]
      simp only [pushR, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
      rw [exec_mvV_push (by decide) (by rw [Function.update_self, hsrc, hv])]
      refine ⟨?_, fun j a1 a2 a3 => ?_⟩
      · simp only [Function.update_self, Function.update_of_ne (show RES ≠ rY by decide)]
        rw [Function.update_of_ne hc.2.symm, h1, hsrc, ← hv, drop_append_drop' (by
          simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate]
          simp), List.append_assoc, hv, List.replicate_succ', List.flatten_append,
          List.flatten_singleton, Nat.succ_mul]
      · simp only [Function.update_apply, if_neg a1, if_neg a2, if_neg a3]; exact h2 j a1 a2 a3) w
    ⟨by simp, fun _ _ _ _ => rfl⟩
  exact I

/-! ### The code -/

/-- `ES := EC` when `a = col.1`, else `zv^k`. -/
def esC : Code := .ifb DG (.cp ES EC) (.cp ES ZKV)

/-- One row `i` of the block `(a, col)`: the value `i` of `ES`, then `N − 1` times `zv`. -/
def ciBody : Code := ofList [.cp rY 10, .mvV rY ES, .mvV RES rY, .cp CT TN1, .rep CT (pushR 11)]

/-- One block `(a, col)`. -/
def cc2Body : Code := ofList [ecC, esC, .cp CC2 12, .rep CC2 ciBody]

/-- One row `col.1`. -/
def cc1Body : Code := ofList [dgC, .cp C2 TTk, .rep C2 cc2Body]

/-- One row `a`. -/
def caBody : Code := ofList [.cp C1 TT2, .rep C1 cc1Body]

/-- **The constant bundle**, shifted into `RES`. -/
def cbC : Code := ofList [.cp CA TT2, .rep CA caBody]

/-- The values of the row `t = 0` of the block `(a, col)`. -/
def esVals (one zv : List Bool) (K : ℕ) (a : Fin 2) (col : Fin 2 × Fin (K + 1)) :
    List (List Bool) :=
  if a = col.1 then constV one zv (K + 1) (2 ^ col.2.val % 2 ^ K) else List.replicate (K + 1) zv

theorem esVals_len (one zv : List Bool) (K : ℕ) (a : Fin 2) (col : Fin 2 × Fin (K + 1)) :
    (esVals one zv K a col).length = K + 1 := by
  unfold esVals; split_ifs <;> simp [constV_len]

theorem esVals_uv {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V) (K : ℕ)
    (a : Fin 2) (col : Fin 2 × Fin (K + 1)) : UV V (esVals one zv K a col) := by
  unfold esVals; split_ifs
  · exact constV_vals h1 hz _ _
  · intro x hx; rw [List.eq_of_mem_replicate hx]; exact hz

/-- **The block `(a, col)` of the constant bundle.** -/
theorem blk_constRepVV {N K : ℕ} (hN : 0 < N) (one zv : List Bool) (a : Fin 2)
    (col : Fin 2 × Fin (K + 1)) :
    blk (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a col =
      (esVals one zv K a col).flatMap fun v => v :: List.replicate (N - 1) zv := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [blk, product_def', List.map_flatMap]
  have he : esVals one zv K a col = (List.finRange (K + 1)).map fun i =>
      (esVals one zv K a col).getD i.val one := by
    apply List.ext_getElem (by simp [esVals_len])
    intro n h1 h2
    simp [List.getElem?_eq_getElem h1]
  rw [he, List.flatMap_map]
  congr 1
  funext i
  rw [List.map_map, List.finRange_succ, List.map_cons, List.map_map]
  simp only [Function.comp_def, constRepVV, gvExp, Nat.add_sub_cancel]
  congr 1
  · simp only [Fin.val_zero, true_and, esVals]
    split_ifs <;> simp_all [constV_zero]
  · have : List.replicate N' zv = (List.finRange N').map fun _ => zv := by simp
    rw [this]
    congr 1; funext t
    simp [Fin.succ_ne_zero, constV_zero, List.getElem?_replicate, i.isLt]

/-! ### The rows `i` of a block -/

/-- The words of a row `i`: its value at `t = 0`, then `N − 1` times `zv`. -/
def rowVals (N : ℕ) (zv : List Bool) (v : List Bool) : List (List Bool) :=
  v :: List.replicate (N - 1) zv

theorem exec_ciBody {N K : ℕ} (hN : 0 < N) {one zv : List Bool} (w : St)
    (ctx : NCtx V K N one zv w) {v L : List Bool} (hv : v.length = V) (hES : w ES = v ++ L) :
    exec V f ciBody w RES = (w RES ++ (rowVals N zv v).flatten).drop (N * V) ∧
      exec V f ciBody w ES = L ∧
      ∀ j, j ≠ rY → j ≠ RES → j ≠ CT → j ≠ ES → exec V f ciBody w j = w j := by
  have h1 : (w 10).length = V := ctx.tm.h10
  have hz : (w 11).length = V := ctx.tm.h11
  rw [show ciBody = ofList ([.cp rY 10, .mvV rY ES, .mvV RES rY, .cp CT TN1] ++
    [.rep CT (pushR 11)]) from rfl, exec_ofList_append]
  have hpre : exec V f (ofList [.cp rY 10, .mvV rY ES, .mvV RES rY, .cp CT TN1]) w RES =
        (w RES ++ v).drop V ∧
      exec V f (ofList [.cp rY 10, .mvV rY ES, .mvV RES rY, .cp CT TN1]) w ES = L ∧
      (exec V f (ofList [.cp rY 10, .mvV rY ES, .mvV RES rY, .cp CT TN1]) w CT).length = N - 1 ∧
      ∀ j, j ≠ rY → j ≠ RES → j ≠ CT → j ≠ ES →
        exec V f (ofList [.cp rY 10, .mvV rY ES, .mvV RES rY, .cp CT TN1]) w j = w j := by
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    rw [exec_mvV_pop (d := rY) (s := ES) (L := L) (by decide) (by simp [Function.update_apply, h1]) hv
      (by simp (config := {decide := true}) [Function.update_apply, hES])]
    rw [exec_mvV_push (d := RES) (s := rY) (by decide)
      (by simp (config := {decide := true}) [Function.update_apply, hv])]
    refine ⟨by simp (config := {decide := true}) [Function.update_apply],
      by simp (config := {decide := true}) [Function.update_apply],
      by simp (config := {decide := true}) [Function.update_apply, ctx.tn1],
      fun j a1 a2 a3 a4 => by simp [Function.update_apply, a1, a2, a3, a4]⟩
  obtain ⟨p1, p2, p3, p4⟩ := hpre
  generalize exec V f (ofList [.cp rY 10, .mvV rY ES, .mvV RES rY, .cp CT TN1]) w = u at p1 p2 p3 p4
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
  obtain ⟨P1, P2⟩ := exec_pushRep (V := V) (f := f) (src := 11) (ctr := CT) (by decide)
    (by decide) u (by rw [p4 11 (by decide) (by decide) (by decide) (by decide), hz])
  have u11 : u 11 = zv := by rw [p4 11 (by decide) (by decide) (by decide) (by decide), ctx.vzv]
  rw [p3, u11, p1] at P1
  refine ⟨?_, ?_, fun j a1 a2 a3 a4 => ?_⟩
  · rw [P1, drop_append_drop' (by simp; omega), rowVals, List.flatten_cons, List.append_assoc]
    congr 1
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  · rw [P2 ES (by decide) (by decide) (by decide), p2]
  · rw [P2 j a1 a2 a3, p4 j a1 a2 a3 a4]

theorem exec_esC {K : ℕ} {one zv : List Bool} (a : Fin 2) (col : Fin 2 × Fin (K + 1)) (w : St)
    (hdg : w DG = [decide (a = col.1)]) (hZ : w ZKV = (List.replicate (K + 1) zv).flatten)
    (hE : w EC = (constV one zv (K + 1) (2 ^ col.2.val % 2 ^ K)).flatten) :
    exec V f esC w = Function.update w ES (esVals one zv K a col).flatten := by
  simp only [esC, exec_ifb', hdg, exec_cp', esVals]
  by_cases h : a = col.1 <;> simp [h, hE, hZ]

/-- **One block of the constant bundle.** -/
theorem exec_cc2Body {N K : ℕ} (hN : 0 < N) {one zv : List Bool} (a : Fin 2)
    (col : Fin 2 × Fin (K + 1)) (w : St) (ctx : NCtx V K N one zv w)
    (hdg : w DG = [decide (a = col.1)]) (hc2 : w C2 = List.replicate (K - col.2.val) true) :
    exec V f cc2Body w RES = (w RES ++ (blk (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a
        col).flatten).drop ((K + 1) * N * V) ∧
      NCtx V K N one zv (exec V f cc2Body w) ∧ ∀ j ∉ wr cc2Body, exec V f cc2Body w j = w j := by
  have h1 : one.length = V := by rw [← ctx.vone]; exact ctx.tm.h10
  have hz : zv.length = V := by rw [← ctx.vzv]; exact ctx.tm.h11
  refine ⟨?_, ctx.exec _ (by decide), fun j hj => exec_not_mem _ _ _ hj⟩
  simp only [cc2Body, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  have hE := exec_ecC (V := V) (f := f) (K := K) w (by rw [ctx.vone]; exact h1)
    (by rw [ctx.vzv]; exact hz) (Nat.sub_le K col.2.val) hc2 (by rw [ctx.zkv, ctx.vzv])
  rw [ctx.vone, ctx.vzv, show K - (K - col.2.val) = col.2.val by have := col.2.isLt; omega] at hE
  obtain ⟨hE1, hE2⟩ := hE
  have cu := ctx.of_eq fun j hj => hE2 j (by revert j hj; decide) (by revert j hj; decide)
    (by revert j hj; decide)
  rw [exec_esC a col _ (by rw [hE2 DG (by decide) (by decide) (by decide), hdg])
    (by rw [cu.zkv]) hE1]
  generalize exec V f ecC w = u at hE1 hE2 cu
  set u2 := Function.update (Function.update u ES (esVals one zv K a col).flatten) CC2
    (Function.update u ES (esVals one zv K a col).flatten 12) with hu2
  have cu2 : NCtx V K N one zv u2 := (cu.upd ES (by decide) _).upd CC2 (by decide) _
  have hev := esVals_uv h1 hz K a col
  have I := exec_rep_inv (V := V) (f := f) (c := CC2) (B := ciBody)
    (fun r w' => r ≤ K + 1 → NCtx V K N one zv w' ∧
      w' ES = ((esVals one zv K a col).drop r).flatten ∧
      w' RES = (u2 RES ++ (((esVals one zv K a col).take r).flatMap (rowVals N zv)).flatten).drop
        (r * (N * V)))
    (fun r w' ih hr => by
      obtain ⟨c, he, hres⟩ := ih (by omega)
      have hrl : r < (esVals one zv K a col).length := by rw [esVals_len]; omega
      have cw := c.upd CC2 (by decide) (w' CC2).tail
      obtain ⟨R1, R2, R3⟩ := exec_ciBody (V := V) (f := f) hN _ cw
        (v := (esVals one zv K a col)[r]) (L := ((esVals one zv K a col).drop (r + 1)).flatten)
        (hev _ (List.getElem_mem _))
        (by rw [Function.update_of_ne (by decide), he, flatten_drop_cons hrl])
      refine ⟨cw.of_eq fun j hj => R3 j (by revert j hj; decide) (by revert j hj; decide)
        (by revert j hj; decide) (by revert j hj; decide), R2, ?_⟩
      rw [R1, Function.update_of_ne (by decide), hres,
        show (r + 1) * (N * V) = r * (N * V) + N * V by ring]
      rw [drop_append_drop' (by
        rw [List.length_append, length_flatten_of (fun x hx => by
          simp only [List.mem_flatMap, rowVals, List.mem_cons] at hx
          obtain ⟨y, hy, hx⟩ := hx
          rcases hx with rfl | hx
          · exact hev _ (List.mem_of_mem_take hy)
          · rw [List.eq_of_mem_replicate hx]; exact hz)]
        simp only [List.length_flatMap, rowVals, List.length_cons, List.length_replicate]
        rw [List.map_const', List.sum_replicate, List.length_take, min_eq_left hrl.le]
        simp; obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩; simp; nlinarith),
        List.append_assoc]
      rw [show (esVals one zv K a col).take (r + 1) = (esVals one zv K a col).take r ++
          [(esVals one zv K a col)[r]] by rw [List.take_succ, List.getElem?_eq_getElem hrl]; rfl]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.flatten_append]) u2 (fun _ => ⟨cu2, by simp (config := {decide := true}) [hu2, Function.update_apply],
        by simp⟩)
  have hn : (u2 CC2).length = K + 1 := by
    simp (config := {decide := true}) [hu2, Function.update_apply, cu.tm.h12]
  rw [hn] at I
  obtain ⟨-, -, I3⟩ := I le_rfl
  rw [I3, List.take_of_length_le (by rw [esVals_len]),
    show (rowVals N zv) = fun v => v :: List.replicate (N - 1) zv from rfl, ← blk_constRepVV hN]
  simp (config := {decide := true}) only [hu2, Function.update_apply, if_false]
  rw [hE2 RES (by decide) (by decide) (by decide)]
  congr 1; ring

/-! ### The loops over `col.2`, `col.1`, `a` -/

theorem cb2_step {N K : ℕ} (hN : 0 < N) {one zv : List Bool} (a c1 : Fin 2) {w₀ : St} {r : ℕ}
    (hr : r < K + 1) {w : St}
    (h : NCtx V K N one zv w ∧ w DG = [decide (a = c1)] ∧ w C2 = List.replicate (K + 1 - r) true ∧
      w RES = (w₀ RES ++ (resC2 (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a c1 r).flatten).drop
        (resC2 (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a c1 r).flatten.length) :
    let w' := exec V f cc2Body (Function.update w C2 (w C2).tail)
    NCtx V K N one zv w' ∧ w' DG = [decide (a = c1)] ∧
      w' C2 = List.replicate (K + 1 - (r + 1)) true ∧
      w' RES = (w₀ RES ++ (resC2 (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a c1
        (r + 1)).flatten).drop (resC2 (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a c1
          (r + 1)).flatten.length := by
  obtain ⟨c, hdg, hc2, hres⟩ := h
  set P := constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))
  have hP : ∀ b, (P b).length = V := constRepVV_len one zv
    (by rw [← c.vone]; exact c.tm.h10) (by rw [← c.vzv]; exact c.tm.h11) _
  set c2 : Fin (K + 1) := ⟨r, hr⟩
  obtain ⟨R1, R2, R3⟩ := exec_cc2Body (V := V) (f := f) hN a (c1, c2)
    (Function.update w C2 (w C2).tail) (c.upd C2 (by decide) _)
    (by rw [Function.update_of_ne (by decide), hdg])
    (by rw [Function.update_self, hc2, List.tail_replicate]; congr 1; show K + 1 - r - 1 = K - r
        omega)
  refine ⟨R2, ?_, ?_, ?_⟩
  · rw [R3 DG (by decide), Function.update_of_ne (by decide), hdg]
  · rw [R3 C2 (by decide), Function.update_self, hc2, List.tail_replicate]; congr 1
  · rw [R1, Function.update_of_ne (by decide), hres]
    have hb := blk_shape hP a (c1, c2)
    rw [show (K + 1) * N * V = (blk P a (c1, c2)).flatten.length by
      rw [length_flatten_of hb.1, hb.2], shift_acc]
    have e : resC2 P a c1 (r + 1) = resC2 P a c1 r ++ blk P a (c1, c2) := by
      simp only [resC2]
      rw [List.take_succ, List.flatMap_append, List.getElem?_eq_getElem (by simpa using hr)]
      have : (List.finRange (K + 1))[r]'(by simpa using hr) = c2 := Fin.ext (by simp [c2])
      simp [this]
    rw [e, List.flatten_append]

/-- One row `col.1` of `cbC`. -/
theorem exec_cc1Body {N K : ℕ} (hN : 0 < N) {one zv : List Bool} (a c1 : Fin 2) (w : St)
    (ctx : NCtx V K N one zv w) (hca : w CA = List.replicate (1 - a.val) true)
    (hc1 : w C1 = List.replicate (1 - c1.val) true) :
    exec V f cc1Body w RES = (w RES ++ (resC2 (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a c1
        (K + 1)).flatten).drop (resC2 (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a c1
          (K + 1)).flatten.length ∧
      NCtx V K N one zv (exec V f cc1Body w) ∧ ∀ j ∉ wr cc1Body, exec V f cc1Body w j = w j := by
  refine ⟨?_, ctx.exec _ (by decide), fun j hj => exec_not_mem _ _ _ hj⟩
  simp only [cc1Body, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  rw [exec_dgC a c1 w ctx.ob ctx.zb hca hc1]
  set w1 := Function.update (Function.update w DG [decide (a = c1)]) C2
    (Function.update w DG [decide (a = c1)] TTk) with hw1
  have I := exec_rep_inv (V := V) (f := f) (c := C2) (B := cc2Body)
    (fun r w' => r ≤ K + 1 → NCtx V K N one zv w' ∧ w' DG = [decide (a = c1)] ∧
      w' C2 = List.replicate (K + 1 - r) true ∧
      w' RES = (w1 RES ++ (resC2 (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a c1 r).flatten).drop
        (resC2 (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a c1 r).flatten.length)
    (fun r w' ih hr => cb2_step hN a c1 (by omega) (ih (by omega))) w1
    (fun _ => ⟨(ctx.upd DG (by decide) _).upd C2 (by decide) _,
      by simp (config := {decide := true}) [hw1, Function.update_apply],
      by simp (config := {decide := true}) [hw1, Function.update_apply, ctx.ttk],
      by simp [resC2]⟩)
  have hn : (w1 C2).length = K + 1 := by
    simp (config := {decide := true}) [hw1, Function.update_apply, ctx.ttk]
  rw [hn] at I
  rw [(I le_rfl).2.2.2]
  simp (config := {decide := true}) [hw1, Function.update_apply]

/-- One row `a` of `cbC`. -/
theorem exec_caBody {N K : ℕ} (hN : 0 < N) {one zv : List Bool} (a : Fin 2) (w : St)
    (ctx : NCtx V K N one zv w) (hca : w CA = List.replicate (1 - a.val) true) :
    exec V f caBody w RES = (w RES ++ (resC1 (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a
        2).flatten).drop (resC1 (constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))) a 2).flatten.length ∧
      NCtx V K N one zv (exec V f caBody w) ∧ ∀ j ∉ wr caBody, exec V f caBody w j = w j := by
  refine ⟨?_, ctx.exec _ (by decide), fun j hj => exec_not_mem _ _ _ hj⟩
  simp only [caBody, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set P := constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))
  set w1 := Function.update w C1 (w TT2) with hw1
  have I := exec_rep_inv (V := V) (f := f) (c := C1) (B := cc1Body)
    (fun r w' => r ≤ 2 → NCtx V K N one zv w' ∧ w' CA = List.replicate (1 - a.val) true ∧
      w' C1 = List.replicate (2 - r) true ∧
      w' RES = (w1 RES ++ (resC1 P a r).flatten).drop (resC1 P a r).flatten.length)
    (fun r w' ih hr => by
      obtain ⟨c, hca', hc1, hres⟩ := ih (by omega)
      set c1 : Fin 2 := ⟨r, by omega⟩
      obtain ⟨R1, R2, R3⟩ := exec_cc1Body (V := V) (f := f) hN a c1
        (Function.update w' C1 (w' C1).tail) (c.upd C1 (by decide) _)
        (by rw [Function.update_of_ne (by decide), hca'])
        (by rw [Function.update_self, hc1, List.tail_replicate]; congr 1; show 2 - r - 1 = 1 - r
            omega)
      refine ⟨R2, ?_, ?_, ?_⟩
      · rw [R3 CA (by decide), Function.update_of_ne (by decide), hca']
      · rw [R3 C1 (by decide), Function.update_self, hc1, List.tail_replicate]; congr 1
      · rw [R1, Function.update_of_ne (by decide), hres, shift_acc]
        have e : resC1 P a (r + 1) = resC1 P a r ++ resC2 P a c1 (K + 1) := by
          simp only [resC1]
          rw [List.take_succ, List.flatMap_append, List.getElem?_eq_getElem (by simp; omega)]
          have : (List.finRange 2)[r]'(by simp; omega) = c1 := Fin.ext (by simp [c1])
          simp [this]
        rw [e, List.flatten_append]) w1
    (fun _ => ⟨ctx.upd C1 (by decide) _, by rw [hw1, Function.update_of_ne (by decide), hca],
      by rw [hw1, Function.update_self, ctx.tt2]; rfl, by simp [resC1]⟩)
  have hn : (w1 C1).length = 2 := by rw [hw1, Function.update_self, ctx.tt2]; rfl
  rw [hn] at I
  rw [(I le_rfl).2.2.2, hw1, Function.update_of_ne (by decide)]

/-- **The constant bundle on the machine**: `RES` ends with the word of
`constRepVV one zv (gvExp q)`. -/
theorem exec_cbC {N K : ℕ} (hN : 0 < N) {one zv : List Bool} (w : St)
    (ctx : NCtx V K N one zv w) :
    exec V f cbC w RES = (w RES ++ bw (constRepVV (N := N) (k := K + 1) one zv
        (gvExp (2 ^ K)))).drop (bw (constRepVV (N := N) (k := K + 1) one zv
          (gvExp (2 ^ K)))).length ∧
      NCtx V K N one zv (exec V f cbC w) ∧ ∀ j ∉ wr cbC, exec V f cbC w j = w j := by
  refine ⟨?_, ctx.exec _ (by decide), fun j hj => exec_not_mem _ _ _ hj⟩
  simp only [cbC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set P := constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K))
  set w1 := Function.update w CA (w TT2) with hw1
  have I := exec_rep_inv (V := V) (f := f) (c := CA) (B := caBody)
    (fun r w' => r ≤ 2 → NCtx V K N one zv w' ∧ w' CA = List.replicate (2 - r) true ∧
      w' RES = (w1 RES ++ (resA P r).flatten).drop (resA P r).flatten.length)
    (fun r w' ih hr => by
      obtain ⟨c, hca, hres⟩ := ih (by omega)
      set a : Fin 2 := ⟨r, by omega⟩
      obtain ⟨R1, R2, R3⟩ := exec_caBody (V := V) (f := f) hN a
        (Function.update w' CA (w' CA).tail) (c.upd CA (by decide) _)
        (by rw [Function.update_self, hca, List.tail_replicate]; congr 1; show 2 - r - 1 = 1 - r
            omega)
      refine ⟨R2, ?_, ?_⟩
      · rw [R3 CA (by decide), Function.update_self, hca, List.tail_replicate]; congr 1
      · rw [R1, Function.update_of_ne (by decide), hres, shift_acc]
        have e : resA P (r + 1) = resA P r ++ resC1 P a 2 := by
          simp only [resA]
          rw [List.take_succ, List.flatMap_append, List.getElem?_eq_getElem (by simp; omega)]
          have : (List.finRange 2)[r]'(by simp; omega) = a := Fin.ext (by simp [a])
          simp [this]
        rw [e, List.flatten_append]) w1
    (fun _ => ⟨ctx.upd CA (by decide) _, by rw [hw1, Function.update_self, ctx.tt2]; rfl,
      by simp [resA]⟩)
  have hn : (w1 CA).length = 2 := by rw [hw1, Function.update_self, ctx.tt2]; rfl
  rw [hn] at I
  rw [(I le_rfl).2.2, resA_two, bw_blocks, List.flatten_flatten, hw1, Function.update_of_ne (by decide)]

end ValVM

end SigabaNeo.Tape
