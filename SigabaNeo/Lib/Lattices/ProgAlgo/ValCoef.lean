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

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

abbrev ROW : Fin 64 := 46
abbrev CM : Fin 64 := 47
abbrev TM0 : Fin 64 := 48
abbrev TT1 : Fin 64 := 49
abbrev CJ : Fin 64 := 50

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
      simp only [exec, show SC ≠ (14 : Fin 64) by decide, if_false]
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
      ∀ j : Fin 64, 32 ≤ j.val → j ≠ LB → j ≠ SD → j ≠ SC → j ≠ CM → j ≠ CJ →
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

end ValVM

end SigabaNeo.Tape
