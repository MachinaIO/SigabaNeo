import SigabaNeo.Lib.Lattices.ProgAlgo.ValCoef

/-!
# An output coefficient of a NAND block on the word machine

`coefC`: the constant (`CW = 57`) shifted into the leaves buffer (from the template `TLB = 58` of
`(2kN + 1) k V` bits), the terms of the columns (`colC`), then the tree of additions (`roundsC`,
`TH` with `treeHeight N k` bits, the count from `TCNT = 59`), the single number left on `OUT = 60`.
**`exec_coefC`**: `OUT` ends with the flattened `coefV` (the shadow of `coefCircuitL` at the
orders `enumT`), for the bundles `A`, `B` given by their columns' digits and reversed rows.
-/

set_option maxRecDepth 8192

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

abbrev CW : Fin 120 := 57
abbrev TLB : Fin 120 := 58
abbrev TCNT : Fin 120 := 59
abbrev OUT : Fin 120 := 60

/-- **An output coefficient.** -/
def coefC : Code := ofList [.cp LB TLB, .mv LB CW 14, colC, .cp LS LB, .cp CN TCNT, .cp 24 14,
  .cp 25 14, roundsC, .cp OUT LS]

theorem constV_vals {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V) :
    ∀ n m, ∀ x ∈ constV one zv n m, x.length = V
  | 0, _, x, hx => by simp [constV] at hx
  | n + 1, m, x, hx => by
    simp only [constV, List.mem_cons] at hx
    rcases hx with rfl | hx
    · split_ifs <;> assumption
    · exact constV_vals h1 hz n (m / 2) x hx

/-- **An output coefficient on the machine.** -/
theorem exec_coefC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {N K : ℕ}
    (w : St) (A B : BI N (K + 1) → List Bool) (a : Fin 2) (col : Fin 2 × Fin (K + 1)) (t : Fin N)
    (Gv : ℕ) (hA : ∀ b, (A b).length = V) (hB : ∀ b, (B b).length = V) (htm : Tmpl V K w)
    (h30 : (w 30).length = (K + 1) * V) (h31 : (w 31).length = V) (hOB : w OB = [true])
    (hZB : w ZB = [false]) (hCW : w CW = (constV (w 10) (w 11) (K + 1) Gv).flatten)
    (hDSS : w DSS = (((cols (K + 1)).map (digitsOf B col)).map List.flatten).flatten)
    (hRAS : w RAS = (((cols (K + 1)).map (rowRev A a)).map fl).flatten)
    (hNV : (w TNV).length = N * V) (hNKV : (w TNKV).length = N * ((K + 1) * V))
    (hM0 : (w TM0).length = N - 1 - t) (hT1 : (w TT1).length = t + 1)
    (h2K : (w T2K).length = 2 * (K + 1))
    (hTLB : (w TLB).length = (2 * (K + 1) * N + 1) * ((K + 1) * V))
    (hCNT : (w TCNT).length = 2 * (K + 1) * N + 1) (hTH : (w TH).length = treeHeight N (K + 1)) :
    exec V f coefC w OUT = (coefV (w 10) (fV V f) (enumT N (K + 1)) (w 11) (2 ^ K) A B Gv a col
      t).flatten := by
  have ht := t.isLt
  set one := w 10
  set zv := w 11
  have h1 : one.length = V := htm.h10
  have hz : zv.length = V := htm.h11
  set Cl := constV one zv (K + 1) Gv with hCl
  have hCll : Cl.length = K + 1 := constV_len _ _ _ _
  have hClv : ∀ x ∈ Cl, x.length = V := constV_vals h1 hz _ _
  have hClf : Cl.flatten.length = (K + 1) * V := by rw [length_flatten_of hClv, hCll]
  set dss := (cols (K + 1)).map (digitsOf B col) with hdss
  set rss := (cols (K + 1)).map (rowRev A a) with hrss
  have hcols : (cols (K + 1)).length = 2 * (K + 1) := by simp [cols, List.length_product]
  have hdl : ∀ ds ∈ dss, ds.length = (N - 1 - t) + (t + 1) ∧ ∀ x ∈ ds, x.length = V := by
    intro ds hds
    simp only [dss, List.mem_map] at hds
    obtain ⟨c', -, rfl⟩ := hds
    refine ⟨by simp [digitsOf]; omega, fun x hx => ?_⟩
    simp only [digitsOf, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact hB _
  have hrl : ∀ rows ∈ rss, rows.length = (N - 1 - t) + (t + 1) ∧
      ∀ cs ∈ rows, cs.length = K + 1 ∧ ∀ x ∈ cs, x.length = V := by
    intro rows hrows
    simp only [rss, List.mem_map] at hrows
    obtain ⟨c', -, rfl⟩ := hrows
    refine ⟨by simp [rowRev]; omega, fun cs hcs => ?_⟩
    simp only [rowRev, List.mem_map] at hcs
    obtain ⟨m, -, rfl⟩ := hcs
    refine ⟨by simp [coefWV], fun x hx => ?_⟩
    simp only [coefWV, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hA _
  simp only [coefC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  -- the constant
  set s1 := Function.update w LB (w TLB) with hs1
  have e1 : exec V f (.mv LB CW 14) s1 = Function.update (Function.update s1 CW []) LB
      ((s1 LB ++ s1 CW).drop (s1 14).length) :=
    exec_mv_push (by decide) (by
      simp (config := {decide := true}) only [s1, Function.update_apply, if_false]
      rw [hCW, hClf, htm.h14])
  rw [e1]
  set s2 := Function.update (Function.update s1 CW []) LB ((s1 LB ++ s1 CW).drop (s1 14).length)
    with hs2
  have s2_ : ∀ j : Fin 120, j ≠ LB → j ≠ CW → s2 j = w j := fun j h1 h2 => by
    simp [s2, s1, Function.update_of_ne h1, Function.update_of_ne h2]
  have hs2LB : s2 LB = (w TLB ++ Cl.flatten).drop ((K + 1) * V) := by
    simp (config := {decide := true}) [s2, s1, Function.update_apply, hCW, htm.h14]
  -- the columns
  have C := exec_colC (V := V) (f := f) hf s2 dss rss (by simp [dss, rss]) hdl hrl
    (by rw [s2_ TNV (by decide) (by decide), hNV]; congr 1; omega)
    (by rw [s2_ TNKV (by decide) (by decide), hNKV]; congr 1; omega)
    (by rw [s2_ TM0 (by decide) (by decide), hM0]) (by rw [s2_ TT1 (by decide) (by decide), hT1])
    (by rw [s2_ T2K (by decide) (by decide), h2K]; simp [dss, hcols])
    (((htm.upd LB (by decide) _).upd CW (by decide) _).upd LB (by decide) _)
    (by rw [s2_ 30 (by decide) (by decide)]; exact h30) (by rw [s2_ 31 (by decide) (by decide)]; exact h31)
    (by rw [s2_ DSS (by decide) (by decide), hDSS]) (by rw [s2_ RAS (by decide) (by decide), hRAS])
  generalize exec V f colC s2 = u at C
  have v10 : s2 10 = one := s2_ 10 (by decide) (by decide)
  have v11 : s2 11 = zv := s2_ 11 (by decide) (by decide)
  have Clb := C.lb
  rw [v10, v11] at Clb
  set L := Cl :: leavesV one (fV V f) zv (2 ^ K) (K + 1) A B a col t (enumT N (K + 1)) with hL
  have hT := fl_leavesV (V := V) (f := f) K one zv A B a col t
  have hzl : ((List.zipWith (colTerms V K f one zv (N - 1 - t) (t + 1)) dss rss).take
      dss.length) = List.zipWith (colTerms V K f one zv (N - 1 - t) (t + 1)) dss rss :=
    List.take_of_length_le (by simp [dss, rss])
  have hTl : (fl (leavesV one (fV V f) zv (2 ^ K) (K + 1) A B a col t (enumT N (K + 1)))).length =
      2 * (K + 1) * N * ((K + 1) * V) := by
    rw [fl_len (fun x hx => by
      rw [leavesV_eq_map, List.mem_map] at hx
      obtain ⟨e, -, rfl⟩ := hx
      exact termV_shape hf K h1 hz A B a col t e), leavesV_eq_map, List.length_map, enumT,
      List.length_product, List.length_product, List.length_finRange, List.length_finRange,
      List.length_finRange]
  have hLB : u LB = fl L := by
    rw [Clb, hzl, ← hT, hs2LB, drop_append_drop' (by rw [List.length_append, hTLB]; nlinarith),
      List.append_assoc]
    have hNt : N - 1 - t + (t + 1) = N := by omega
    rw [List.drop_left' (by rw [hTLB, show dss.length = 2 * (K + 1) by simp [dss, hcols], hNt]; ring)]
    rw [hL, fl_cons]
  -- the rounds
  have hLshape : ∀ x ∈ L, x.length = K + 1 ∧ ∀ y ∈ x, y.length = V := by
    intro x hx
    rw [hL, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨hCll, hClv⟩
    · rw [leavesV_eq_map, List.mem_map] at hx
      obtain ⟨e, -, rfl⟩ := hx
      exact termV_shape hf K h1 hz A B a col t e
  have hLl : L.length = 2 * (K + 1) * N + 1 := by
    rw [hL, List.length_cons, leavesV_eq_map, List.length_map, enumT, List.length_product,
      List.length_product, List.length_finRange, List.length_finRange, List.length_finRange]
  have hpow : L.length ≤ 2 ^ treeHeight N (K + 1) := by
    rw [treeHeight, hLl]
    have := Nat.le_pow_clog (show 1 < 2 by norm_num) (Fintype.card ((Fin 2 × Fin (K + 1)) × Fin N) + 1)
    simp only [Fintype.card_prod, Fintype.card_fin] at this ⊢
    exact this
  have hsingle := iterate_pairRoundV_single one (fV V f) zv (2 ^ K) (K + 1) (treeHeight N (K + 1)) L
    (by omega) hpow
  have key : ∀ s3 : St, Tmpl V K s3 → s3 OB = [true] → s3 ZB = [false] → s3 LS = fl L →
      (s3 CN).length = L.length → (s3 24).length = (K + 1) * V → (s3 25).length = (K + 1) * V →
      s3 10 = one → s3 11 = zv → (s3 TH).length = treeHeight N (K + 1) →
      exec V f roundsC s3 LS = (coefV one (fV V f) (enumT N (K + 1)) zv (2 ^ K) A B Gv a col
        t).flatten := by
    intro s3 t3 hO hZ hLS hCN h24 h25 h10 h11 hTH3
    have R := exec_roundsC (V := V) (f := f) hf s3 L hLshape t3 hO hZ hLS hCN h24 h25
    rw [R.ls, h10, h11, hTH3]
    obtain ⟨x, hx⟩ : ∃ x, (pairRoundV one (fV V f) zv (2 ^ K) (K + 1))^[treeHeight N (K + 1)] L = [x] :=
      List.length_eq_one_iff.mp hsingle
    simp only [coefV]
    rw [roundsV_eq_iterate, ← hCl, ← hL, hx]
    simp [fl, foldSumV]
  have uhi : ∀ j : Fin 120, 35 ≤ j.val → j ≠ ROW → j ≠ CM → j ≠ CJ → j ≠ DSS → j ≠ RAS → j ≠ CC →
      j ≠ CW → u j = w j := fun j hj h1 h2 h3 h4 h5 h6 h7 => by
    rw [C.hi j hj h1 h2 h3 h4 h5 h6]
    exact s2_ j (fun e => by subst e; simp at hj) h7
  simp only [Function.update_self]
  apply key
  · exact ((((C.tm.upd LS (by decide) _).upd CN (by decide) _).upd 24 (by decide) _).upd 25
      (by decide) _)
  all_goals simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
  · rw [uhi OB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hOB]
  · rw [uhi ZB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hZB]
  · exact hLB
  · rw [uhi TCNT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hCNT, hLl]
  · exact C.tm.h14
  · exact C.tm.h14
  · rw [C.one, v10]
  · rw [C.zv, v11]
  · rw [uhi TH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hTH]

end ValVM

end SigabaNeo.Tape
