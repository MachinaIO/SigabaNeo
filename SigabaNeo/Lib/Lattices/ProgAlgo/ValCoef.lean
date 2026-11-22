import SigabaNeo.Lib.Lattices.ProgAlgo.ValRounds

/-!
# One block of terms of a coefficient on the word machine

For one column `c'` of the terms of an output coefficient `(a, col, t)`: the digits of the column
(`N` values) and the coefficients `A (a, c', ·, (t − j) mod N)` for `j = 0 … N − 1`. The machine
holds the coefficients of the row `(a, c')` reversed (`ROW = 46`: the coefficient `N − 1` first),
so the coefficients of the subtracted terms (`j ≤ t`) are `ROW` without its first `N − 1 − t`
blocks, and those of the added terms (`j > t`) the first `N − 1 − t` blocks of `ROW`
(`cblockC`, `exec_cblockC`).

Words: `ROW = 46`, `CM = 47` (a counter of `N − 1 − t` bits), `TM0 = 48` (its template),
`TT1 = 49` (a template of `t + 1` bits), `CJ = 50` (the counter of the terms).
-/

set_option maxRecDepth 8192

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

abbrev ROW : Fin 120 := 46
abbrev CM : Fin 120 := 47
abbrev TM0 : Fin 120 := 48
abbrev TT1 : Fin 120 := 49
abbrev CJ : Fin 120 := 50

/-- **A block of terms**: with the digits on `SD` and the reversed row on `ROW`, the `t + 1`
subtracted terms, then the `N − 1 − t` added terms, shifted into `LB`. -/
def cblockC : Code := ofList [.cp SC ROW, .cp CM TM0, .rep CM (.drop SC 14), .cp CJ TT1,
  jloopC termSubC CJ, .cp SC ROW, .cp CJ TM0, jloopC termAddC CJ]

/-- Drop `|CM|` blocks of `|TBk|` bits from `SC`. -/
theorem exec_dropLoop (w : St) :
    exec V f (.rep CM (.drop SC 14)) w =
      Function.update (Function.update w SC ((w SC).drop ((w CM).length * (w 14).length))) CM [] := by
  rw [exec_rep']
  have key : ∀ m : ℕ, (fun w' => exec V f (.drop SC 14) (Function.update w' CM (w' CM).tail))^[m] w =
      Function.update (Function.update w SC ((w SC).drop (m * (w 14).length))) CM
        ((w CM).drop m) := by
    intro m
    induction m with
    | zero =>
      simp only [Function.iterate_zero, id, Nat.zero_mul, List.drop_zero, Function.update_eq_self]
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [exec, show SC ≠ (14 : Fin 120) by decide, if_false]
      funext j
      by_cases hc : j = CM
      · subst hc; simp (config := {decide := true}) [Function.update_apply, List.drop_tail]
      · by_cases hs : j = SC
        · subst hs
          simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
          rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]
        · simp [Function.update_of_ne hc, Function.update_of_ne hs]
  rw [key, List.drop_eq_nil_of_le le_rfl]

theorem fl_append (L M : List (List (List Bool))) : fl (L ++ M) = fl L ++ fl M := by
  simp [fl]

/-- **A block of terms.** -/
theorem exec_cblockC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {K : ℕ}
    (w : St) (ds : List (List Bool)) (rows : List (List (List Bool))) (rd : List Bool) (m0 t1 : ℕ)
    (hdl : ds.length = m0 + t1) (hrl : rows.length = m0 + t1) (hdv : ∀ x ∈ ds, x.length = V)
    (hrv : ∀ cs ∈ rows, cs.length = K + 1 ∧ ∀ x ∈ cs, x.length = V) (htm : Tmpl V K w)
    (h30 : (w 30).length = (K + 1) * V) (h31 : (w 31).length = V)
    (hSD : w SD = ds.flatten ++ rd) (hROW : w ROW = fl rows) (hM0 : (w TM0).length = m0)
    (hT1 : (w TT1).length = t1) :
    exec V f cblockC w LB = (w LB ++
        ((List.zipWith (Fsub V K f (w 10) (w 11)) (ds.take t1) (rows.drop m0)).flatten ++
          (List.zipWith (Fadd V K f (w 10) (w 11)) (ds.drop t1) (rows.take m0)).flatten)).drop
        ((m0 + t1) * ((K + 1) * V)) ∧
      exec V f cblockC w SD = rd ∧ Tmpl V K (exec V f cblockC w) ∧
      (exec V f cblockC w 30).length = (K + 1) * V ∧ (exec V f cblockC w 31).length = V ∧
      exec V f cblockC w 10 = w 10 ∧ exec V f cblockC w 11 = w 11 ∧
      ∀ j : Fin 120, 32 ≤ j.val → j ≠ LB → j ≠ SD → j ≠ SC → j ≠ CM → j ≠ CJ →
        exec V f cblockC w j = w j := by
  have hrows : ∀ cs ∈ rows, cs.flatten.length = (K + 1) * V := fun cs hcs => by
    rw [length_flatten_of (hrv cs hcs).2, (hrv cs hcs).1]
  have hfl : ∀ n, (rows.take n).length = min n rows.length := fun n => List.length_take
  have hROWsplit : fl rows = fl (rows.take m0) ++ fl (rows.drop m0) := by
    rw [← fl_append, List.take_append_drop]
  have hdropSC : (fl rows).drop (m0 * ((K + 1) * V)) = fl (rows.drop m0) := by
    rw [hROWsplit, List.drop_left' (by
      rw [fl_len (fun x hx => hrv x (List.mem_of_mem_take hx)), List.length_take]; simp [hrl])]
  rw [show cblockC = ofList ([.cp SC ROW, .cp CM TM0, .rep CM (.drop SC 14), .cp CJ TT1] ++
    [jloopC termSubC CJ, .cp SC ROW, .cp CJ TM0, jloopC termAddC CJ]) from rfl, exec_ofList_append]
  set w1 := Function.update (Function.update (Function.update (Function.update w SC (w ROW))
    CM (w TM0)) SC ((w ROW).drop (m0 * ((K + 1) * V)))) CM [] with hw1
  have hpre : exec V f (ofList [.cp SC ROW, .cp CM TM0, .rep CM (.drop SC 14), .cp CJ TT1]) w =
      Function.update w1 CJ (w TT1) := by
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    rw [exec_dropLoop]
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false, hM0,
      htm.h14, hw1]
  rw [hpre]
  set w2 := Function.update w1 CJ (w TT1) with hw2
  have w2_ : ∀ j, j ≠ CJ → j ≠ CM → j ≠ SC → w2 j = w j := fun j h1 h2 h3 => by
    simp [w2, w1, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  have hSC2 : w2 SC = fl (rows.drop m0) := by
    simp (config := {decide := true}) only [w2, w1, Function.update_apply, if_true, if_false]
    rw [hROW, hdropSC]
  -- the subtracted terms
  have J1 := exec_jloopC (V := V) (f := f) (termOk_sub hf K (w 10) (w 11) htm.h10 htm.h11)
    (ctr := CJ) (by decide) w2 (w2_ 10 (by decide) (by decide) (by decide))
    (w2_ 11 (by decide) (by decide) (by decide)) (ds.take t1) (rows.drop m0) ((ds.drop t1).flatten ++ rd) []
    (by simp [hdl, hrl]) (fun x hx => hdv x (List.mem_of_mem_take hx))
    (fun x hx => hrv x (List.mem_of_mem_drop hx)) (by simp [w2, hT1, hdl])
    (((((htm.upd SC (by decide) _).upd CM (by decide) _).upd SC (by decide) _).upd CM (by decide)
      _).upd CJ (by decide) _)
    (by rw [w2_ 30 (by decide) (by decide) (by decide)]; exact h30)
    (by rw [w2_ 31 (by decide) (by decide) (by decide)]; exact h31)
    (by rw [w2_ SD (by decide) (by decide) (by decide), hSD, ← List.append_assoc,
      ← List.flatten_append, List.take_append_drop])
    (by rw [hSC2, List.append_nil]; rfl)
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  rw [show (ds.take t1).length = t1 by simp [hdl]] at J1
  generalize exec V f (jloopC termSubC CJ) w2 = u1 at J1
  have u1ROW : u1 ROW = w ROW := by
    rw [J1.hi ROW (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact w2_ ROW (by decide) (by decide) (by decide)
  have u1TM0 : u1 TM0 = w TM0 := by
    rw [J1.hi TM0 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact w2_ TM0 (by decide) (by decide) (by decide)
  set u2 := Function.update (Function.update u1 SC (u1 ROW)) CJ (Function.update u1 SC (u1 ROW) TM0)
    with hu2
  have u2_ : ∀ j, j ≠ CJ → j ≠ SC → u2 j = u1 j := fun j h1 h2 => by
    simp [u2, Function.update_of_ne h1, Function.update_of_ne h2]
  have J2 := exec_jloopC (V := V) (f := f) (termOk_add hf K (w 10) (w 11) htm.h10 htm.h11)
    (ctr := CJ) (by decide) u2 (by rw [u2_ 10 (by decide) (by decide), J1.one]; rfl)
    (by rw [u2_ 11 (by decide) (by decide), J1.zv]; rfl) (ds.drop t1) (rows.take m0) rd
    (fl (rows.drop m0)) (by simp [hdl, hrl]) (fun x hx => hdv x (List.mem_of_mem_drop hx))
    (fun x hx => hrv x (List.mem_of_mem_take hx))
    (by simp (config := {decide := true}) [u2, Function.update_apply, u1TM0, hM0, hdl])
    ((J1.tm.upd SC (by decide) _).upd CJ (by decide) _)
    (by rw [u2_ 30 (by decide) (by decide)]; exact J1.c30)
    (by rw [u2_ 31 (by decide) (by decide)]; exact J1.c31)
    (by rw [u2_ SD (by decide) (by decide), J1.sd, List.drop_eq_nil_of_le (by simp [hdl])]; simp)
    (by simp (config := {decide := true}) only [u2, Function.update_apply, if_true, if_false]
        rw [u1ROW, hROW, hROWsplit]; rfl)
  rw [show (ds.drop t1).length = m0 by simp [hdl]] at J2
  generalize exec V f (jloopC termAddC CJ) u2 = u3 at J2
  have hX1 : ((List.zipWith (Fsub V K f (w 10) (w 11)) (ds.take t1) (rows.drop m0)).flatten).length =
      t1 * ((K + 1) * V) := by
    rw [length_flatten_of (V := (K + 1) * V) (zipWith_len _ _ fun a _ b hb =>
        (termOk_sub hf K (w 10) (w 11) htm.h10 htm.h11).len a b
          (hrv b (List.mem_of_mem_drop hb)).1 (hrv b (List.mem_of_mem_drop hb)).2),
      List.length_zipWith]
    simp [hdl, hrl]
  refine ⟨?_, J2.sd.trans (by rw [List.drop_eq_nil_of_le (by simp [hdl])]; simp), J2.tm, J2.c30,
    J2.c31, ?_, ?_, fun j hj hLB hSD hSC hCM hCJ => ?_⟩
  · have tk1 : (List.zipWith (Fsub V K f (w 10) (w 11)) (ds.take t1) (rows.drop m0)).take t1 =
        List.zipWith (Fsub V K f (w 10) (w 11)) (ds.take t1) (rows.drop m0) :=
      List.take_of_length_le (by simp [hdl, hrl])
    have tk2 : (List.zipWith (Fadd V K f (w 10) (w 11)) (ds.drop t1) (rows.take m0)).take m0 =
        List.zipWith (Fadd V K f (w 10) (w 11)) (ds.drop t1) (rows.take m0) :=
      List.take_of_length_le (by simp [hdl, hrl])
    rw [J2.lb, u2_ LB (by decide) (by decide), J1.lb, w2_ LB (by decide) (by decide) (by decide),
      tk1, tk2, drop_append_drop' (by rw [List.length_append, hX1]; omega), List.append_assoc]
    congr 1; ring
  · rw [J2.one, u2_ 10 (by decide) (by decide), J1.one, w2_ 10 (by decide) (by decide) (by decide)]
  · rw [J2.zv, u2_ 11 (by decide) (by decide), J1.zv, w2_ 11 (by decide) (by decide) (by decide)]
  · rw [J2.hi j hj hLB hSD hSC hCJ, u2_ j hCJ hSC, J1.hi j hj hLB hSD hSC hCJ, w2_ j hCJ hCM hSC]

/-! ### The loop over the columns -/

abbrev DSS : Fin 120 := 51
abbrev RAS : Fin 120 := 52
abbrev TNV : Fin 120 := 53
abbrev TNKV : Fin 120 := 54
abbrev CC : Fin 120 := 55
abbrev T2K : Fin 120 := 56

/-- One column: load its `N` digits into `SD` and its reversed row into `ROW`, then the terms. -/
def colBody : Code := ofList [.cp SD TNV, .mv SD DSS TNV, .cp ROW TNKV, .mv ROW RAS TNKV, cblockC]

/-- **The columns**: `|T2K|` columns. -/
def colC : Code := ofList [.cp CC T2K, .rep CC colBody]

/-- The terms of one column, flattened. -/
def colTerms (V K : ℕ) (f : List Bool → List Bool → List Bool) (one zv : List Bool) (m0 t1 : ℕ)
    (ds : List (List Bool)) (rows : List (List (List Bool))) : List Bool :=
  (List.zipWith (Fsub V K f one zv) (ds.take t1) (rows.drop m0)).flatten ++
    (List.zipWith (Fadd V K f one zv) (ds.drop t1) (rows.take m0)).flatten

/-- The invariant of the columns. -/
structure CInv (V K : ℕ) (f : List Bool → List Bool → List Bool) (w₀ : St) (m0 t1 : ℕ)
    (dss : List (List (List Bool))) (rss : List (List (List (List Bool)))) (c : ℕ) (w : St) :
    Prop where
  hdss : w DSS = ((dss.drop c).map List.flatten).flatten
  hrss : w RAS = ((rss.drop c).map fl).flatten
  lb : w LB = (w₀ LB ++ ((List.zipWith (colTerms V K f (w₀ 10) (w₀ 11) m0 t1) dss rss).take c).flatten).drop
    (c * ((m0 + t1) * ((K + 1) * V)))
  tm : Tmpl V K w
  c30 : (w 30).length = (K + 1) * V
  c31 : (w 31).length = V
  one : w 10 = w₀ 10
  zv : w 11 = w₀ 11
  hi : ∀ j : Fin 120, 35 ≤ j.val → j ≠ ROW → j ≠ CM → j ≠ CJ → j ≠ DSS → j ≠ RAS → j ≠ CC →
    w j = w₀ j

theorem colTerms_len (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {K : ℕ}
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V) {m0 t1 : ℕ}
    {ds : List (List Bool)} {rows : List (List (List Bool))} (hdl : ds.length = m0 + t1)
    (hrl : rows.length = m0 + t1) (hrv : ∀ cs ∈ rows, cs.length = K + 1 ∧ ∀ x ∈ cs, x.length = V) :
    (colTerms V K f one zv m0 t1 ds rows).length = (m0 + t1) * ((K + 1) * V) := by
  unfold colTerms
  rw [List.length_append,
    length_flatten_of (V := (K + 1) * V) (zipWith_len _ _ fun a _ b hb =>
      (termOk_sub hf K one zv h1 hz).len a b (hrv b (List.mem_of_mem_drop hb)).1
        (hrv b (List.mem_of_mem_drop hb)).2),
    length_flatten_of (V := (K + 1) * V) (zipWith_len _ _ fun a _ b hb =>
      (termOk_add hf K one zv h1 hz).len a b (hrv b (List.mem_of_mem_take hb)).1
        (hrv b (List.mem_of_mem_take hb)).2), List.length_zipWith, List.length_zipWith]
  simp [hdl, hrl]
  ring

theorem cinv_step (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {K : ℕ}
    {w₀ : St} {m0 t1 : ℕ} {dss : List (List (List Bool))} {rss : List (List (List (List Bool)))}
    (hl : dss.length = rss.length) (hdl : ∀ ds ∈ dss, ds.length = m0 + t1 ∧ ∀ x ∈ ds, x.length = V)
    (hrl : ∀ rows ∈ rss, rows.length = m0 + t1 ∧
      ∀ cs ∈ rows, cs.length = K + 1 ∧ ∀ x ∈ cs, x.length = V)
    (hNV : (w₀ TNV).length = (m0 + t1) * V) (hNKV : (w₀ TNKV).length = (m0 + t1) * ((K + 1) * V))
    (hM0 : (w₀ TM0).length = m0) (hT1 : (w₀ TT1).length = t1)
    {c : ℕ} (hc : c < dss.length) {w : St} (h : CInv V K f w₀ m0 t1 dss rss c w) :
    CInv V K f w₀ m0 t1 dss rss (c + 1) (exec V f colBody (Function.update w CC (w CC).tail)) := by
  have hc' : c < rss.length := hl ▸ hc
  obtain ⟨hdl1, hdv⟩ := hdl _ (List.getElem_mem hc)
  obtain ⟨hrl1, hrv⟩ := hrl _ (List.getElem_mem hc')
  set u0 := Function.update w CC (w CC).tail with hu0
  have u0_ : ∀ j, j ≠ CC → u0 j = w j := fun j hj => by simp [u0, Function.update_of_ne hj]
  have wTNV : u0 TNV = w₀ TNV := by
    rw [u0_ TNV (by decide), h.hi TNV (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  have wTNKV : u0 TNKV = w₀ TNKV := by
    rw [u0_ TNKV (by decide), h.hi TNKV (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  have hx : (dss[c]).flatten.length = (m0 + t1) * V := by rw [length_flatten_of hdv, hdl1]
  have hyl : (fl rss[c]).length = (m0 + t1) * ((K + 1) * V) := by rw [fl_len hrv, hrl1]
  simp only [colBody, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set s1 := Function.update u0 SD (u0 TNV) with hs1
  have e1 : exec V f (.mv SD DSS TNV) s1 = Function.update (Function.update s1 DSS
      ((dss.drop (c + 1)).map List.flatten).flatten) SD dss[c].flatten := by
    refine exec_mv_pop (by decide) (by simp [s1, Function.update_apply]) ?_ ?_
    · simp (config := {decide := true}) only [s1, Function.update_apply, if_false]
      rw [wTNV, hNV, hx]
    · simp (config := {decide := true}) only [s1, Function.update_apply, if_false]
      rw [u0_ DSS (by decide), h.hdss, List.drop_eq_getElem_cons hc, List.map_cons, List.flatten_cons]
  rw [e1]
  set s2 := Function.update (Function.update s1 DSS ((dss.drop (c + 1)).map List.flatten).flatten)
    SD dss[c].flatten with hs2
  set s3 := Function.update s2 ROW (s2 TNKV) with hs3
  have e2 : exec V f (.mv ROW RAS TNKV) s3 = Function.update (Function.update s3 RAS
      ((rss.drop (c + 1)).map fl).flatten) ROW (fl rss[c]) := by
    refine exec_mv_pop (by decide) (by simp [s3, Function.update_apply]) ?_ ?_
    · simp (config := {decide := true}) only [s3, s2, s1, Function.update_apply, if_false]
      rw [wTNKV, hNKV, hyl]
    · simp (config := {decide := true}) only [s3, s2, s1, Function.update_apply, if_false]
      rw [u0_ RAS (by decide), h.hrss, List.drop_eq_getElem_cons hc', List.map_cons,
        List.flatten_cons]
  rw [e2]
  set s4 := Function.update (Function.update s3 RAS ((rss.drop (c + 1)).map fl).flatten) ROW
    (fl rss[c]) with hs4
  have s4_ : ∀ j : Fin 120, j ≠ ROW → j ≠ RAS → j ≠ SD → j ≠ DSS → j ≠ CC → s4 j = w j :=
    fun j h1 h2 h3 h4 h5 => by
      simp [s4, s3, s2, s1, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3, Function.update_of_ne h4, u0_ j h5]
  have tm4 : Tmpl V K s4 := (((((h.tm.upd CC (by decide) _).upd SD (by decide) _).upd DSS
    (by decide) _).upd SD (by decide) _).upd ROW (by decide) _ |>.upd RAS (by decide) _).upd ROW
    (by decide) _
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := exec_cblockC hf s4 dss[c] rss[c] [] m0 t1 hdl1 hrl1 hdv
    hrv tm4 (by rw [s4_ 30 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.c30)
    (by rw [s4_ 31 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.c31)
    (by simp (config := {decide := true}) [s4, s3, s2, Function.update_apply])
    (by simp [s4]) (by rw [s4_ TM0 (by decide) (by decide) (by decide) (by decide) (by decide),
      h.hi TM0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hM0]) (by rw [s4_ TT1 (by decide) (by decide) (by decide) (by decide) (by decide),
      h.hi TT1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hT1])
  have v10 : s4 10 = w₀ 10 := by
    rw [s4_ 10 (by decide) (by decide) (by decide) (by decide) (by decide), h.one]
  have v11 : s4 11 = w₀ 11 := by
    rw [s4_ 11 (by decide) (by decide) (by decide) (by decide) (by decide), h.zv]
  rw [v10, v11] at b1
  refine ⟨?_, ?_, ?_, b3, b4, b5, by rw [b6, v10], by rw [b7, v11], fun j hj hR hM hJ hD hA hC => ?_⟩
  · rw [b8 DSS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) [s4, s3, s2, Function.update_apply]
  · rw [b8 RAS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) [s4, Function.update_apply]
  · rw [b1, s4_ LB (by decide) (by decide) (by decide) (by decide) (by decide), h.lb]
    have hz : ∀ x ∈ List.zipWith (colTerms V K f (w₀ 10) (w₀ 11) m0 t1) dss rss,
        x.length = (m0 + t1) * ((K + 1) * V) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_zipWith]
      have hi1 : i < dss.length := by simp at hi; omega
      have hi2 : i < rss.length := by simp at hi; omega
      exact colTerms_len hf (by rw [← h.one]; exact h.tm.h10) (by rw [← h.zv]; exact h.tm.h11)
        (hdl _ (List.getElem_mem hi1)).1 (hrl _ (List.getElem_mem hi2)).1
        (hrl _ (List.getElem_mem hi2)).2
    have htk : ((List.zipWith (colTerms V K f (w₀ 10) (w₀ 11) m0 t1) dss rss).take c).flatten.length =
        c * ((m0 + t1) * ((K + 1) * V)) := by
      rw [length_flatten_of (fun x hx => hz x (List.mem_of_mem_take hx)), List.length_take,
        List.length_zipWith, ← hl, min_self, min_eq_left hc.le]
    have htake : (List.zipWith (colTerms V K f (w₀ 10) (w₀ 11) m0 t1) dss rss).take (c + 1) =
        (List.zipWith (colTerms V K f (w₀ 10) (w₀ 11) m0 t1) dss rss).take c ++
          [colTerms V K f (w₀ 10) (w₀ 11) m0 t1 dss[c] rss[c]] := by
      rw [List.take_succ, List.getElem?_zipWith, List.getElem?_eq_getElem hc,
        List.getElem?_eq_getElem hc']
      rfl
    rw [drop_append_drop' (by rw [List.length_append, htk]; omega), List.append_assoc, htake,
      List.flatten_append, List.flatten_singleton]
    unfold colTerms
    congr 1; ring
  · rw [b8 j (by omega) (fun e => by subst e; simp at hj) (fun e => by subst e; simp at hj)
      (fun e => by subst e; simp at hj) hM hJ,
      s4_ j hR hA (fun e => by subst e; simp at hj) hD hC, h.hi j hj hR hM hJ hD hA hC]

/-- **The columns**: after `|T2K| = |dss|` columns, `LB` ends with the terms of all the columns
shifted in. -/
theorem exec_colC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {K : ℕ}
    (w : St) {m0 t1 : ℕ} (dss : List (List (List Bool))) (rss : List (List (List (List Bool))))
    (hl : dss.length = rss.length) (hdl : ∀ ds ∈ dss, ds.length = m0 + t1 ∧ ∀ x ∈ ds, x.length = V)
    (hrl : ∀ rows ∈ rss, rows.length = m0 + t1 ∧
      ∀ cs ∈ rows, cs.length = K + 1 ∧ ∀ x ∈ cs, x.length = V)
    (hNV : (w TNV).length = (m0 + t1) * V) (hNKV : (w TNKV).length = (m0 + t1) * ((K + 1) * V))
    (hM0 : (w TM0).length = m0) (hT1 : (w TT1).length = t1) (h2K : (w T2K).length = dss.length)
    (htm : Tmpl V K w) (h30 : (w 30).length = (K + 1) * V) (h31 : (w 31).length = V)
    (hDSS : w DSS = (dss.map List.flatten).flatten) (hRAS : w RAS = (rss.map fl).flatten) :
    CInv V K f w m0 t1 dss rss dss.length (exec V f colC w) := by
  simp only [colC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  have h0 : CInv V K f w m0 t1 dss rss 0 (Function.update w CC (w T2K)) := by
    refine ⟨?_, ?_, ?_, htm.upd CC (by decide) _, ?_, ?_, ?_, ?_, fun j _ _ _ _ _ _ hC => ?_⟩
    · simp (config := {decide := true}) [Function.update_apply, hDSS]
    · simp (config := {decide := true}) [Function.update_apply, hRAS]
    · simp (config := {decide := true}) [Function.update_apply]
    · simp (config := {decide := true}) [Function.update_apply, h30]
    · simp (config := {decide := true}) [Function.update_apply, h31]
    · simp (config := {decide := true}) [Function.update_apply]
    · simp (config := {decide := true}) [Function.update_apply]
    · simp [Function.update_of_ne hC]
  have := exec_rep_inv (V := V) (f := f) (c := CC) (B := colBody)
    (fun c w' => c ≤ dss.length → CInv V K f w m0 t1 dss rss c w')
    (fun c w' ih hc => cinv_step hf hl hdl hrl hNV hNKV hM0 hT1 (by omega) (ih (by omega)))
    _ (fun _ => h0)
  have hn : (Function.update w CC (w T2K) CC).length = dss.length := by simp [h2K]
  rw [hn] at this
  exact this le_rfl

end ValVM

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-! ### The block of terms of a column as a shadow -/

section Shadow

variable {N : ℕ}

/-- The digits of the column `c'` of the bundle `B` at the output column `col`. -/
def digitsOf (B : BI N k' → List Bool) (col : Fin 2 × Fin k') (c' : Fin 2 × Fin k') :
    List (List Bool) :=
  (List.finRange N).map fun j => B (c'.1, col, c'.2, j)

/-- The coefficients of the row `(a, c')` of the bundle `A`, the last first. -/
def rowRev (A : BI N k' → List Bool) (a : Fin 2) (c' : Fin 2 × Fin k') : List (List (List Bool)) :=
  (List.finRange N).map fun m => coefWV A a c' m.rev

/-- **The terms of a column are the two zips of `cblockC`.** -/
theorem terms_column (K : ℕ) (one zv : List Bool) (A B : BI N (K + 1) → List Bool) (a : Fin 2)
    (col : Fin 2 × Fin (K + 1)) (t : Fin N) (c' : Fin 2 × Fin (K + 1)) :
    ((List.finRange N).map fun j => termV one (fV V f) zv (2 ^ K) (K + 1) A B a col t
        (constV one zv (K + 1) 0) (c', j)) =
      List.zipWith (fun d cs => (modSubV one (fV V f) zv (2 ^ K) (K + 1)
          (List.replicate (K + 1) zv) (andLV one (fV V f) d cs))) ((digitsOf B col c').take (t + 1))
          ((rowRev A a c').drop (N - 1 - t)) ++
        List.zipWith (fun d cs => (modAddV one (fV V f) zv (2 ^ K) (K + 1)
          (List.replicate (K + 1) zv) (andLV one (fV V f) d cs))) ((digitsOf B col c').drop (t + 1))
          ((rowRev A a c').take (N - 1 - t)) := by
  have ht := t.isLt
  apply List.ext_getElem
  · simp [digitsOf, rowRev]; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_finRange] at h1
    simp only [List.getElem_map]
    by_cases hi : i ≤ t.val
    · rw [List.getElem_append_left (by simp [digitsOf, rowRev]; omega), List.getElem_zipWith]
      simp only [termV, List.getElem_finRange, Fin.cast_mk, digitsOf, rowRev, List.getElem_take,
        List.getElem_drop, List.getElem_map]
      rw [dif_pos (by simpa using hi)]
      simp only [constV_zero]
      congr 3
      ext <;> simp [Fin.rev] <;> omega
    · rw [List.getElem_append_right (by simp [digitsOf, rowRev]; omega), List.getElem_zipWith]
      simp only [termV, List.getElem_finRange, Fin.cast_mk, digitsOf, rowRev, List.getElem_take,
        List.getElem_drop, List.getElem_map, List.length_zipWith, List.length_take,
        List.length_drop, List.length_map, List.length_finRange]
      rw [dif_neg (by simpa using hi)]
      simp only [constV_zero]
      congr 3
      · congr 1; ext <;> simp <;> omega
      · ext <;> simp [Fin.rev] <;> omega

theorem leavesV_eq_map {α : Type*} (one : α) (step : α → α → α) (zv : α) (q k' : ℕ)
    (A B : BI N k' → α) (a : Fin 2) (col : Fin 2 × Fin k') (t : Fin N) :
    ∀ es : List ((Fin 2 × Fin k') × Fin N), leavesV one step zv q k' A B a col t es =
      es.map (termV one step zv q k' A B a col t (constV one zv k' 0))
  | [] => rfl
  | e :: es => by rw [leavesV, leavesV_eq_map one step zv q k' A B a col t es, List.map_cons]

/-- The columns `c'` in the order of the terms. -/
def cols (k' : ℕ) : List (Fin 2 × Fin k') := List.finRange 2 ×ˢ List.finRange k'

theorem enumT_eq (k' : ℕ) : enumT N k' = (cols k').flatMap fun c' => (List.finRange N).map (c', ·) := by
  rfl

/-- **The leaves of a coefficient, flattened, are the terms of its columns.** -/
theorem fl_leavesV (K : ℕ) (one zv : List Bool) (A B : BI N (K + 1) → List Bool) (a : Fin 2)
    (col : Fin 2 × Fin (K + 1)) (t : Fin N) :
    fl (leavesV one (fV V f) zv (2 ^ K) (K + 1) A B a col t (enumT N (K + 1))) =
      (List.zipWith (colTerms V K f one zv (N - 1 - t) (t + 1))
        ((cols (K + 1)).map (digitsOf B col)) ((cols (K + 1)).map (rowRev A a))).flatten := by
  rw [leavesV_eq_map, enumT_eq, List.map_flatMap]
  generalize cols (K + 1) = cs
  induction cs with
  | nil => rfl
  | cons c' cs ih =>
    rw [List.flatMap_cons, fl_append, ih, List.map_cons, List.map_cons, List.zipWith_cons_cons,
      List.flatten_cons, List.map_map]
    congr 1
    have := terms_column (V := V) (f := f) K one zv A B a col t c'
    simp only [Function.comp_def] at this ⊢
    rw [this, fl_append]
    simp only [fl, colTerms, List.map_zipWith]
    rfl

/-- The shape of the numbers: `K + 1` values of `V` bits. -/
def NShape (V K : ℕ) (x : List (List Bool)) : Prop := x.length = K + 1 ∧ ∀ y ∈ x, y.length = V

theorem termV_shape (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (K : ℕ)
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V) (A B : BI N (K + 1) → List Bool)
    (a : Fin 2) (col : Fin 2 × Fin (K + 1)) (t : Fin N) (e : (Fin 2 × Fin (K + 1)) × Fin N) :
    NShape V K (termV one (fV V f) zv (2 ^ K) (K + 1) A B a col t (constV one zv (K + 1) 0) e) := by
  unfold termV
  split_ifs
  · exact modSubV_shape hf h1 hz _ _ _ _ (constV_len _ _ _ _) (by rw [length_andLV]; simp [coefWV])
  · exact modAddV_shape hf h1 hz _ _ _ _ (constV_len _ _ _ _) (by rw [length_andLV]; simp [coefWV])

end Shadow

end ValVM

end SigabaNeo.Tape
