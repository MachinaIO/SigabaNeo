import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMGinv

/-!
# Families of vectors on the ring-word machine

Families over the digit positions `Dig = (r, (r₂, i₂), i')` (`2 · 2K · K` members, in this
lexicographic order) of vectors (`2K` words) or matrices (`2 × 2K` words):

* `deintC`: from a family of matrices (register `106`, member `d` = `rows₀[d] ++ rows₁[d]`), the
  families of their rows `0` and `1` (registers `107`, `108`) (**`exec_deintC`**);
* `mulAccC`: for a matrix `A` (register `103`) and a family of vectors `F` (register `104`), the
  vector (register `105`) `o_j = Σ_{r<2} Σ_{i'<K} ddot(F_{(r, j, i')}, A_{0,(r,i')}, A_{1,(r,i')})`
  (**`exec_mulAccC`**), the sum of `Mul` (ePrint 2026/2539 eq. (1)) over the digits.

Scratch: `96 … 99`, `109`, `118`, `119`.
-/

namespace SigabaNeo.Tape

namespace RingVM

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {N K : ℕ} [NeZero (2 ^ K - 1)]

/-! ### Rows of a family of matrices -/

/-- One member: move its row `0`, then its row `1`. -/
def deBody : Code := ofList [.mv 107 96 6, .mv 108 96 6]

/-- **The rows of a family of matrices.** -/
def deintC : Code :=
  ofList [.cp 96 106, .cp 107 10, .cp 108 10, .cp 97 9,
    .rep 97 (ofList [.cp 98 8, .rep 98 (ofList [.cp 99 4, .rep 99 deBody])])]

theorem wr_deintC : wr deintC = [96, 107, 108, 97, 97, 98, 98, 99, 99, 107, 96, 108, 96] := rfl

theorem exec_deintC (w : St) (hc : Consts N K w) (h6 : w 6 = List.replicate (2 * K * (N * K)) false)
    (h8 : w 8 = List.replicate (2 * K) false) (h9 : w 9 = List.replicate 2 false)
    (h10 : w 10 = List.replicate (2 * (2 * K) * K * (2 * K * (N * K))) false)
    {rows₀ rows₁ : List (List Bool)} (hr₀ : ∀ x ∈ rows₀, x.length = 2 * K * (N * K))
    (hr₁ : ∀ x ∈ rows₁, x.length = 2 * K * (N * K)) (hl₀ : rows₀.length = 2 * (2 * K) * K)
    (hl₁ : rows₁.length = 2 * (2 * K) * K)
    (h106 : w 106 = (List.zipWith (· ++ ·) rows₀ rows₁).flatten) :
    (exec N K deintC w) 107 = rows₀.flatten ∧ (exec N K deintC w) 108 = rows₁.flatten ∧
      ∀ j, j ∉ wr deintC → (exec N K deintC w) j = w j := by
  set m := 2 * K * (N * K) with hm
  set T := 2 * (2 * K) * K with hT
  set Z := List.zipWith (· ++ ·) rows₀ rows₁ with hZ
  set B := List.replicate (T * m) false with hB
  have hZl : Z.length = T := by simp [hZ, hl₀, hl₁]
  have hZw : ∀ n, n < T → Z.getD n [] = rows₀.getD n [] ++ rows₁.getD n [] := by
    intro n hn
    simp [hZ, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
      List.getElem?_eq_getElem (show n < rows₀.length by omega),
      List.getElem?_eq_getElem (show n < rows₁.length by omega)]
  have hZm : ∀ y ∈ Z, y.length = 2 * m := by
    intro y hy
    rw [hZ, List.mem_iff_getElem] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [List.getElem_zipWith, List.length_append, hr₀ _ (List.getElem_mem _),
      hr₁ _ (List.getElem_mem _)]
    ring
  let P : ℕ → St → Prop := fun n w' =>
    Consts N K w' ∧ w' 6 = List.replicate m false ∧ w' 96 = (Z.drop n).flatten ∧
      w' 107 = (B ++ (rows₀.take n).flatten).drop (n * m) ∧
      w' 108 = (B ++ (rows₁.take n).flatten).drop (n * m) ∧
      ∀ j, j ∉ wr deintC → w' j = w j
  have hP : ∀ (r : Fin 200), r ∈ ([97, 98, 99] : List (Fin 200)) →
      ∀ n w' v, P n w' → P n (Function.update w' r v) := by
    intro r hr n w' v ⟨q0, q6, q96, q107, q108, qf⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hr4 : 4 < r.val := by rcases hr with rfl | rfl | rfl <;> decide
    have hne : ∀ t : Fin 200, t ∈ ([6, 96, 107, 108] : List (Fin 200)) → t ≠ r := by
      intro t ht h; subst h; rcases hr with rfl | rfl | rfl <;> simp at ht
    refine ⟨consts_update q0 r hr4 v, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
    · rw [Function.update_of_ne (hne 6 (by simp))]; exact q6
    · rw [Function.update_of_ne (hne 96 (by simp))]; exact q96
    · rw [Function.update_of_ne (hne 107 (by simp))]; exact q107
    · rw [Function.update_of_ne (hne 108 (by simp))]; exact q108
    · rw [Function.update_of_ne (fun h => hj (by subst h; rw [wr_deintC]; rcases hr with rfl | rfl | rfl <;> simp))]
      exact qf j hj
  have hbody : ∀ n w', n + 1 ≤ T → P n w' → P (n + 1) (exec N K deBody w') := by
    intro n w' hn ⟨q0, q6, q96, q107, q108, qf⟩
    have hn0 : n < rows₀.length := by omega
    have hn1 : n < rows₁.length := by omega
    have x0 := hr₀ _ (mem_getD hn0)
    have x1 := hr₁ _ (mem_getD hn1)
    have s1 := exec_mv_move (N := N) (K := K) (d := 107) (s := 96) (c := 6) (w := w') (by decide)
      (x := rows₀.getD n []) (L := rows₁.getD n [] ++ (Z.drop (n + 1)).flatten)
      (by rw [q6, List.length_replicate, x0])
      (by rw [q96, flatten_drop_succ (by omega), hZw n (by omega), List.append_assoc])
    set w1 := Function.update (Function.update w' 96 (rows₁.getD n [] ++ (Z.drop (n + 1)).flatten))
      107 ((w' 107 ++ rows₀.getD n []).drop (rows₀.getD n []).length)
    have s2 := exec_mv_move (N := N) (K := K) (d := 108) (s := 96) (c := 6) (w := w1) (by decide)
      (x := rows₁.getD n []) (L := (Z.drop (n + 1)).flatten)
      (by simp only [w1, Function.update_apply, Fin.reduceEq, ↓reduceIte]; rw [q6, List.length_replicate, x1])
      (by simp [w1])
    have e : exec N K deBody w' = Function.update (Function.update w1 96 (Z.drop (n + 1)).flatten) 108
        ((w1 108 ++ rows₁.getD n []).drop (rows₁.getD n []).length) := by
      simp only [deBody, exec_ofList_cons, exec_ofList_nil]
      rw [s1, s2]
    rw [e]
    refine ⟨consts_update (consts_update (consts_update (consts_update q0 96 (by decide) _) 107
      (by decide) _) 96 (by decide) _) 108 (by decide) _, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
    · simp [w1, q6]
    · simp [w1]
    · simp only [w1, Function.update_apply, Fin.reduceEq, ↓reduceIte]
      rw [q107, x0, buf_push hr₀ hn0]
    · simp only [w1, Function.update_apply, Fin.reduceEq, ↓reduceIte]
      rw [q108, x1, buf_push hr₁ hn1]
    · have hne : ∀ t : Fin 200, t ∈ ([96, 107, 108] : List (Fin 200)) → j ≠ t := by
        intro t ht h; subst h; apply hj; rw [wr_deintC]; simp at ht ⊢; rcases ht with h | h | h <;> simp [h]
      simp only [w1, Function.update_apply]
      rw [if_neg (hne 108 (by simp)), if_neg (hne 96 (by simp)), if_neg (hne 107 (by simp)),
        if_neg (hne 96 (by simp))]
      exact qf j hj
  -- the three nested loops
  have inner : ∀ n w', n + K ≤ T → P n w' →
      P (n + K) (exec N K (ofList [.cp 99 4, .rep 99 deBody]) w') := by
    intro n w' hn hw'
    simp only [exec_ofList_cons, exec_ofList_nil]
    have h99 : (exec N K (.cp 99 4) w' 99).length = K := by simp [exec, hw'.1.k]
    have := exec_rep_step (N := N) (K := K) 99 deBody (by decide) P (hP 99 (by simp)) 1 T
      hbody n _ (by rw [h99]; omega) (by
        show P n (Function.update w' 99 (w' 4)); exact hP 99 (by simp) n w' _ hw')
    rwa [h99, mul_one] at this
  have middle : ∀ n w', n + 2 * K * K ≤ T → P n w' →
      P (n + 2 * K * K) (exec N K (ofList [.cp 98 8, .rep 98 (ofList [.cp 99 4, .rep 99 deBody])]) w') := by
    intro n w' hn hw'
    simp only [exec_ofList_cons, exec_ofList_nil]
    have hw8 : w' 8 = w 8 := hw'.2.2.2.2.2 8 (by rw [wr_deintC]; decide)
    have h98 : (exec N K (.cp 98 8) w' 98).length = 2 * K := by simp [exec, hw8, h8]
    have := exec_rep_step (N := N) (K := K) 98 (ofList [.cp 99 4, .rep 99 deBody]) (by decide) P
      (hP 98 (by simp)) K T inner n _ (by rw [h98]; nlinarith) (by
        show P n (Function.update w' 98 (w' 8)); exact hP 98 (by simp) n w' _ hw')
    rwa [h98] at this
  have hw1 : P 0 (Function.update (Function.update (Function.update (Function.update w 96
      (w 106)) 107 (w 10)) 108 (w 10)) 97 (w 9)) := by
    refine ⟨consts_update (consts_update (consts_update (consts_update hc 96 (by decide) _) 107
      (by decide) _) 108 (by decide) _) 97 (by decide) _, by simp [h6, hm], by simp [h106, hZ],
      by simp [h10, hB, hT, hm], by simp [h10, hB, hT, hm], fun j hj => ?_⟩
    have hne : ∀ t : Fin 200, t ∈ ([96, 107, 108, 97] : List (Fin 200)) → j ≠ t := by
      intro t ht h; subst h; apply hj; rw [wr_deintC]; simp at ht ⊢
      rcases ht with h | h | h | h <;> simp [h]
    simp only [Function.update_apply]
    rw [if_neg (hne 97 (by simp)), if_neg (hne 108 (by simp)), if_neg (hne 107 (by simp)),
      if_neg (hne 96 (by simp))]
  have e : exec N K deintC w = exec N K (.rep 97 (ofList [.cp 98 8, .rep 98 (ofList [.cp 99 4,
      .rep 99 deBody])])) (Function.update (Function.update (Function.update (Function.update w 96
      (w 106)) 107 (w 10)) 108 (w 10)) 97 (w 9)) := by
    simp only [deintC, exec_ofList_cons, exec_ofList_nil, exec, Function.update_apply,
      Fin.reduceEq, ↓reduceIte]
  have outer := exec_rep_step (N := N) (K := K) 97 _ (by decide) P (hP 97 (by simp)) (2 * K * K) T
    middle 0 _ (by simp [h9, hT]; ring_nf; omega) hw1
  rw [← e] at outer
  have h97 : ((Function.update (Function.update (Function.update (Function.update w 96 (w 106)) 107
      (w 10)) 108 (w 10)) 97 (w 9)) 97).length = 2 := by simp [h9]
  rw [h97, zero_add, show 2 * (2 * K * K) = T by rw [hT]; ring] at outer
  obtain ⟨_, _, _, p107, p108, pf⟩ := outer
  refine ⟨?_, ?_, pf⟩
  · rw [p107, ← hl₀, buf_final (by rw [hB, hl₀, List.length_replicate])]
  · rw [p108, ← hl₁, buf_final (by rw [hB, List.length_replicate, hl₁])]

/-! ### Sums of digit dot products over a family -/

/-- One digit `i'`: pop `F_d` into `80`, the columns `A_{0,(r,i')}`, `A_{1,(r,i')}` into `81`,
`82`, the dot product, accumulate into `109`. -/
def iBody (Fs : Fin 200) : Code := ofList [.mv 80 Fs 6, .mv 81 98 2, .mv 82 99 2, ddotC, .add 109 109 83]

theorem wr_iBody (Fs : Fin 200) : wr (iBody Fs) = [80, Fs, 81, 98, 82, 99] ++ wr ddotC ++ [109] := by
  simp [iBody, wr, wr_ofList]

/-- The family's members are vectors of `2K` words. -/
def FamOK (N K : ℕ) (fss : List (List (List Bool))) : Prop :=
  ∀ v ∈ fss, v.length = 2 * K ∧ ∀ x ∈ v, x.length = N * K

theorem famOK_getD {fss : List (List (List Bool))} (h : FamOK N K fss) {d : ℕ} (hd : d < fss.length) :
    (fss.getD d []).length = 2 * K ∧ ∀ x ∈ fss.getD d [], x.length = N * K :=
  h _ (by rw [List.getD_eq_getElem _ _ hd]; exact List.getElem_mem hd)

theorem famOK_flatten {fss : List (List (List Bool))} (h : FamOK N K fss) :
    ∀ y ∈ fss.map List.flatten, y.length = 2 * K * (N * K) := by
  intro y hy
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
  rw [length_flatten_of (h v hv).2, (h v hv).1]

theorem map_flatten_drop_succ {fss : List (List (List Bool))} {d : ℕ} (hd : d < fss.length) :
    ((fss.drop d).map List.flatten).flatten =
      (fss.getD d []).flatten ++ ((fss.drop (d + 1)).map List.flatten).flatten := by
  rw [List.drop_eq_getElem_cons hd, List.map_cons, List.flatten_cons, List.getD_eq_getElem _ _ hd]

/-- The value of the inner loop. -/
noncomputable def iSum (fss : List (List (List Bool))) (as : List (List Bool)) (base o₀ o₁ n : ℕ) :
    RM N K :=
  ∑ i ∈ Finset.range n, ddotV (N := N) (fss.getD (base + i) []) (as.getD (o₀ + i) []) (as.getD (o₁ + i) [])

theorem exec_iLoop (hK : 0 < K) (Fs : Fin 200) (hFs : Fs = 96 ∨ Fs = 97) (w : St)
    (hc : Consts N K w) (h6 : w 6 = List.replicate (2 * K * (N * K)) false)
    {fss : List (List (List Bool))} (hf : FamOK N K fss) {as : List (List Bool)}
    (has : ∀ x ∈ as, x.length = N * K) {base o₀ o₁ : ℕ} (hb : base + K ≤ fss.length)
    (ho₀ : o₀ + K ≤ as.length) (ho₁ : o₁ + K ≤ as.length)
    (hFsw : w Fs = ((fss.drop base).map List.flatten).flatten) (h98 : w 98 = (as.drop o₀).flatten)
    (h99 : w 99 = (as.drop o₁).flatten) (h80 : (w 80).length = 2 * K * (N * K))
    (h81 : (w 81).length = N * K) (h82 : (w 82).length = N * K) (h109 : (w 109).length = N * K)
    (h119 : (w 119).length = K) :
    let w' := exec N K (.rep 119 (iBody Fs)) w
    w' Fs = ((fss.drop (base + K)).map List.flatten).flatten ∧ w' 98 = (as.drop (o₀ + K)).flatten ∧
      w' 99 = (as.drop (o₁ + K)).flatten ∧ (w' 80).length = 2 * K * (N * K) ∧
      (w' 81).length = N * K ∧ (w' 82).length = N * K ∧ (w' 109).length = N * K ∧
      decRM N K (w' 109) = decRM N K (w 109) + iSum (N := N) fss as base o₀ o₁ K ∧
      ∀ j, j ∉ wr (.rep 119 (iBody Fs)) → w' j = w j := by
  intro w'
  have n80 : Fs ≠ 80 := by rcases hFs with rfl | rfl <;> decide
  have n81 : Fs ≠ 81 := by rcases hFs with rfl | rfl <;> decide
  have n82 : Fs ≠ 82 := by rcases hFs with rfl | rfl <;> decide
  have n98 : Fs ≠ 98 := by rcases hFs with rfl | rfl <;> decide
  have n99 : Fs ≠ 99 := by rcases hFs with rfl | rfl <;> decide
  have n109 : Fs ≠ 109 := by rcases hFs with rfl | rfl <;> decide
  have n119 : Fs ≠ 119 := by rcases hFs with rfl | rfl <;> decide
  have n6 : Fs ≠ 6 := by rcases hFs with rfl | rfl <;> decide
  have nd : Fs ∉ wr ddotC := by rcases hFs with rfl | rfl <;> (rw [wr_ddotC]; decide)
  have h119n : (119 : Fin 200) ∉ wr (iBody Fs) := by
    rw [wr_iBody]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨⟨by decide, n119.symm, by decide, by decide, by decide, by decide⟩,
      by rw [wr_ddotC]; decide⟩, by decide⟩
  let P : ℕ → St → Prop := fun i v =>
    Consts N K v ∧ v 6 = List.replicate (2 * K * (N * K)) false ∧
      v Fs = ((fss.drop (base + i)).map List.flatten).flatten ∧ v 98 = (as.drop (o₀ + i)).flatten ∧
      v 99 = (as.drop (o₁ + i)).flatten ∧ (v 80).length = 2 * K * (N * K) ∧
      (v 81).length = N * K ∧ (v 82).length = N * K ∧ (v 109).length = N * K ∧
      decRM N K (v 109) = decRM N K (w 109) + iSum (N := N) fss as base o₀ o₁ i ∧
      ∀ j, j ∉ wr (.rep 119 (iBody Fs)) → v j = w j
  have hP := exec_rep_inv (N := N) (K := K) 119 (iBody Fs) h119n P w
    ⟨hc, h6, hFsw, h98, h99, h80, h81, h82, h109, by simp [iSum], fun _ _ => rfl⟩
    (fun i hi v hv _ => by
      obtain ⟨q0, q6, qF, q98, q99, q80, q81, q82, q109, qd, qf⟩ := hv
      rw [h119] at hi
      have hd : base + i < fss.length := by omega
      have hi0 : o₀ + i < as.length := by omega
      have hi1 : o₁ + i < as.length := by omega
      obtain ⟨fl, fw⟩ := famOK_getD hf hd
      set vs := fss.getD (base + i) [] with hvs
      set m0 := as.getD (o₀ + i) [] with hm0
      set m1 := as.getD (o₁ + i) [] with hm1
      have hm0l : m0.length = N * K := has _ (mem_getD hi0)
      have hm1l : m1.length = N * K := has _ (mem_getD hi1)
      have lvs : vs.flatten.length = 2 * K * (N * K) := by rw [length_flatten_of fw, fl]
      set s := Function.update v 119 (v 119).tail with hs
      have sc : Consts N K s := consts_update q0 119 (by decide) _
      have s6 : s 6 = List.replicate (2 * K * (N * K)) false := by
        rw [hs, Function.update_of_ne (by decide)]; exact q6
      have s1 := exec_mv_pop (N := N) (K := K) (d := 80) (s := Fs) (c := 6) (w := s)
        (by simp only [not_or]; exact ⟨n80.symm, by decide, n6⟩)
        (v := vs.flatten) (L := ((fss.drop (base + i + 1)).map List.flatten).flatten)
        (by rw [s6, List.length_replicate, hs, Function.update_of_ne (by decide)]; exact q80)
        (by rw [s6, List.length_replicate, lvs])
        (by rw [hs, Function.update_of_ne n119, qF, map_flatten_drop_succ hd])
      set s1' := Function.update (Function.update s Fs
        ((fss.drop (base + i + 1)).map List.flatten).flatten) 80 vs.flatten with hs1'
      have sc1 : Consts N K s1' := by
        refine consts_update (consts_update sc Fs (by rcases hFs with rfl | rfl <;> decide) _) 80
          (by decide) _
      have s2 := exec_mv_pop (N := N) (K := K) (d := 81) (s := 98) (c := 2) (w := s1') (by decide)
        (v := m0) (L := (as.drop (o₀ + i + 1)).flatten)
        (by rw [sc1.zero, List.length_replicate]
            simp only [hs1', hs, Function.update_apply, Fin.reduceEq, ↓reduceIte, n81.symm]
            exact q81)
        (by rw [sc1.zero, List.length_replicate]; exact hm0l)
        (by simp only [hs1', hs, Function.update_apply, Fin.reduceEq, ↓reduceIte, n98.symm, q98]
            exact flatten_drop_succ hi0)
      set s2' := Function.update (Function.update s1' 98 (as.drop (o₀ + i + 1)).flatten) 81 m0
        with hs2'
      have sc2 : Consts N K s2' := consts_update (consts_update sc1 98 (by decide) _) 81 (by decide) _
      have s3 := exec_mv_pop (N := N) (K := K) (d := 82) (s := 99) (c := 2) (w := s2') (by decide)
        (v := m1) (L := (as.drop (o₁ + i + 1)).flatten)
        (by rw [sc2.zero, List.length_replicate]
            simp only [hs2', hs1', hs, Function.update_apply, Fin.reduceEq, ↓reduceIte, n82.symm]
            exact q82)
        (by rw [sc2.zero, List.length_replicate]; exact hm1l)
        (by simp only [hs2', hs1', hs, Function.update_apply, Fin.reduceEq, ↓reduceIte, n99.symm,
              q99]
            exact flatten_drop_succ hi1)
      set s3' := Function.update (Function.update s2' 99 (as.drop (o₁ + i + 1)).flatten) 82 m1
        with hs3'
      have sc3 : Consts N K s3' := consts_update (consts_update sc2 99 (by decide) _) 82 (by decide) _
      have a80 : s3' 80 = vs.flatten := by
        simp only [hs3', hs2', hs1', Function.update_apply, Fin.reduceEq, ↓reduceIte]
      have a81 : s3' 81 = m0 := by
        simp only [hs3', hs2', Function.update_apply, Fin.reduceEq, ↓reduceIte]
      have a82 : s3' 82 = m1 := by simp only [hs3', Function.update_apply, Fin.reduceEq, ↓reduceIte]
      obtain ⟨d83, dv, df⟩ := exec_ddotC hK s3' sc3 fw fl a80
      set s4 := exec N K ddotC s3' with hs4
      have b109 : s4 109 = v 109 := by
        rw [df 109 (by rw [wr_ddotC]; decide)]
        simp only [hs3', hs2', hs1', hs, Function.update_apply, Fin.reduceEq, ↓reduceIte,
          n109.symm]
      have e : exec N K (iBody Fs) s = Function.update s4 109
          (addRMW N K (opd N K (s4 109)) (opd N K (s4 83))) := by
        simp only [iBody, exec_ofList_cons, exec_ofList_nil]
        rw [s1, s2, s3]
        rfl
      have keep : ∀ r : Fin 200, r ∉ wr ddotC → r ≠ 109 → exec N K (iBody Fs) s r = s3' r := by
        intro r hr h109'
        rw [e, Function.update_of_ne h109', df r hr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
      · rw [e]; exact consts_update (consts_exec sc3 _ rfl) 109 (by decide) _
      · rw [keep 6 (by rw [wr_ddotC]; decide) (by decide)]
        simp only [hs3', hs2', hs1', Function.update_apply, Fin.reduceEq, ↓reduceIte, n6.symm]
        exact s6
      · rw [keep Fs nd n109]
        simp only [hs3', hs2', hs1', Function.update_apply, Fin.reduceEq, ↓reduceIte, n82, n99, n81,
          n98, n80]
        simp [Nat.add_assoc]
      · rw [keep 98 (by rw [wr_ddotC]; decide) (by decide)]
        simp only [hs3', hs2', Function.update_apply, Fin.reduceEq, ↓reduceIte]
        simp [Nat.add_assoc]
      · rw [keep 99 (by rw [wr_ddotC]; decide) (by decide)]
        simp only [hs3', Function.update_apply, Fin.reduceEq, ↓reduceIte]
        simp [Nat.add_assoc]
      · rw [keep 80 (by rw [wr_ddotC]; decide) (by decide), a80, lvs]
      · rw [keep 81 (by rw [wr_ddotC]; decide) (by decide), a81, hm0l]
      · rw [keep 82 (by rw [wr_ddotC]; decide) (by decide), a82, hm1l]
      · rw [e, Function.update_self]
        exact length_addRMW N K (length_takeD _ _) _
      · rw [e, Function.update_self, b109, opd_eq q109, opd_eq d83, decRM_addRMW q109 d83, qd, dv,
          a81, a82]
        simp only [iSum, Finset.sum_range_succ, ddotV, add_assoc]
        rfl
      · have hj' : j ∉ wr (iBody Fs) := fun h => hj (by simp [wr, h])
        rw [wr_iBody] at hj'
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj'
        obtain ⟨⟨⟨j80, jF, j81, j98, j82, j99⟩, jd⟩, j109⟩ := hj'
        have j119 : j ≠ 119 := fun h => hj (by simp [wr, h])
        rw [keep j jd j109]
        simp only [hs3', hs2', hs1', hs, Function.update_apply, j80, jF, j81, j98, j82, j99, j119,
          ↓reduceIte]
        exact qf j hj)
  rw [h119] at hP
  obtain ⟨_, _, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hP
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

/-- One output entry `j`: the digits of row `0` (stream `96`, columns `A_{·,(0,i')}`), then of
row `1` (stream `97`, columns `A_{·,(1,i')}`), pushed into `105`. -/
def jBody : Code :=
  ofList [.cp 109 2, .cp 98 103, .cp 99 103, .drop 99 6, .cp 119 4, .rep 119 (iBody 96),
    .cp 98 103, .drop 98 56, .cp 99 103, .drop 99 6, .drop 99 56, .cp 119 4, .rep 119 (iBody 97),
    .mv 105 109 2]

theorem wr_jBody : wr jBody = [109, 98, 99, 99, 119] ++ wr (.rep 119 (iBody 96)) ++
    [98, 98, 99, 99, 99, 119] ++ wr (.rep 119 (iBody 97)) ++ [105, 109] := by
  simp [jBody, wr, wr_ofList]

/-- The value of an output entry of `mulAccC`. -/
noncomputable def mulAccV (fss : List (List (List Bool))) (as : List (List Bool)) (j : ℕ) : RM N K :=
  iSum (N := N) fss as (j * K) 0 (2 * K) K + iSum (N := N) fss as (2 * K * K + j * K) K (2 * K + K) K

theorem drop_drop_flatten {as : List (List Bool)} (has : ∀ x ∈ as, x.length = N * K) (a b : ℕ) :
    (as.drop a).flatten.drop (b * (N * K)) = (as.drop (a + b)).flatten := by
  rw [flatten_drop_mul (fun y hy => has y (List.mem_of_mem_drop hy)) b, List.drop_drop]

theorem exec_jBody (hK : 0 < K) (v : St) (hc : Consts N K v)
    (h6 : v 6 = List.replicate (2 * K * (N * K)) false) (h56 : v 56 = List.replicate (K * (N * K)) false)
    {fss : List (List (List Bool))} (hf : FamOK N K fss) (hT : fss.length = 2 * (2 * K) * K)
    {as : List (List Bool)} (has : ∀ x ∈ as, x.length = N * K) (hal : as.length = 4 * K)
    {j : ℕ} (hj : j < 2 * K) (q103 : v 103 = as.flatten)
    (q96 : v 96 = ((fss.drop (j * K)).map List.flatten).flatten)
    (q97 : v 97 = ((fss.drop (2 * K * K + j * K)).map List.flatten).flatten)
    (q80 : (v 80).length = 2 * K * (N * K)) (q81 : (v 81).length = N * K)
    (q82 : (v 82).length = N * K) :
    let v' := exec N K jBody v
    v' 96 = ((fss.drop ((j + 1) * K)).map List.flatten).flatten ∧
      v' 97 = ((fss.drop (2 * K * K + (j + 1) * K)).map List.flatten).flatten ∧
      (v' 80).length = 2 * K * (N * K) ∧ (v' 81).length = N * K ∧ (v' 82).length = N * K ∧
      (∃ acc : List Bool, acc.length = N * K ∧ decRM N K acc = mulAccV (N := N) fss as j ∧
        v' 105 = (v 105 ++ acc).drop (N * K)) ∧
      ∀ r, r ∉ wr jBody → v' r = v r := by
  intro v'
  have hjK : (j + 1) * K ≤ 2 * K * K := by nlinarith
  -- before the first row
  set u1 := Function.update (Function.update (Function.update (Function.update v 109
    (List.replicate (N * K) false)) 98 as.flatten) 99 (as.drop (2 * K)).flatten) 119
    (List.replicate K false) with hu1
  have e1 : exec N K (ofList [.cp 109 2, .cp 98 103, .cp 99 103, .drop 99 6, .cp 119 4]) v = u1 := by
    simp only [exec_ofList_cons, exec_ofList_nil, exec, Function.update_apply, Fin.reduceEq,
      ↓reduceIte, hc.zero, q103, h6, List.length_replicate, hc.k, hu1]
    rw [flatten_drop_mul has (2 * K)]
    funext t
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  have uc1 : Consts N K u1 := consts_update (consts_update (consts_update (consts_update hc 109
    (by decide) _) 98 (by decide) _) 99 (by decide) _) 119 (by decide) _
  have uv : ∀ r : Fin 200, r ∉ ([109, 98, 99, 119] : List (Fin 200)) → u1 r = v r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hu1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
      Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
  obtain ⟨a96, a98, a99, a80, a81, a82, a109, ad, af⟩ := exec_iLoop (N := N) hK 96 (Or.inl rfl) u1
    uc1 (by rw [uv 6 (by decide), h6]) hf has (base := j * K) (o₀ := 0) (o₁ := 2 * K)
    (by rw [hT]; nlinarith) (by omega) (by omega) (by rw [uv 96 (by decide), q96])
    (by simp [hu1]) (by simp [hu1]) (by rw [uv 80 (by decide), q80]) (by rw [uv 81 (by decide), q81])
    (by rw [uv 82 (by decide), q82]) (by simp [hu1]) (by simp [hu1])
  set u2 := exec N K (.rep 119 (iBody 96)) u1 with hu2
  have uc2 : Consts N K u2 := consts_exec uc1 _ rfl
  have f2 : ∀ r : Fin 200, r ∈ ([2, 4, 6, 56, 97, 103, 105, 109] : List (Fin 200)) → r ≠ 109 →
      u2 r = u1 r := by
    intro r hr _
    apply af
    simp only [wr, wr_iBody, wr_ddotC]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> first | decide | contradiction
  -- before the second row
  set u3 := Function.update (Function.update (Function.update u2 98 (as.drop K).flatten) 99
    (as.drop (2 * K + K)).flatten) 119 (List.replicate K false) with hu3
  have e3 : exec N K (ofList [.cp 98 103, .drop 98 56, .cp 99 103, .drop 99 6, .drop 99 56,
      .cp 119 4]) u2 = u3 := by
    have g103 : u2 103 = as.flatten := by rw [f2 103 (by simp) (by decide), uv 103 (by decide), q103]
    have g56 : u2 56 = List.replicate (K * (N * K)) false := by
      rw [f2 56 (by simp) (by decide), uv 56 (by decide), h56]
    have g6 : u2 6 = List.replicate (2 * K * (N * K)) false := by
      rw [f2 6 (by simp) (by decide), uv 6 (by decide), h6]
    simp only [exec_ofList_cons, exec_ofList_nil, exec, Function.update_apply, Fin.reduceEq,
      ↓reduceIte, g103, g56, g6, List.length_replicate, uc2.k, hu3]
    rw [flatten_drop_mul has (2 * K), drop_drop_flatten has (2 * K) K, flatten_drop_mul has K]
    funext t
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  have uc3 : Consts N K u3 := consts_update (consts_update (consts_update uc2 98 (by decide) _) 99
    (by decide) _) 119 (by decide) _
  have g3 : ∀ r : Fin 200, r ∉ ([98, 99, 119] : List (Fin 200)) → u3 r = u2 r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hu3, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
      Function.update_of_ne hr.2.2]
  obtain ⟨b97, b98, b99, b80, b81, b82, b109, bd, bf⟩ := exec_iLoop (N := N) hK 97 (Or.inr rfl) u3
    uc3 (by rw [g3 6 (by decide), f2 6 (by simp) (by decide), uv 6 (by decide), h6]) hf has
    (base := 2 * K * K + j * K) (o₀ := K) (o₁ := 2 * K + K)
    (by rw [hT]; nlinarith) (by omega) (by omega)
    (by rw [g3 97 (by decide), f2 97 (by simp) (by decide), uv 97 (by decide), q97])
    (by simp [hu3]) (by simp [hu3]) (by rw [g3 80 (by decide)]; exact a80)
    (by rw [g3 81 (by decide)]; exact a81) (by rw [g3 82 (by decide)]; exact a82)
    (by rw [g3 109 (by decide)]; exact a109) (by simp [hu3])
  set u4 := exec N K (.rep 119 (iBody 97)) u3 with hu4
  have uc4 : Consts N K u4 := consts_exec uc3 _ rfl
  have p := exec_mv_push (N := N) (K := K) (d := 105) (s := 109) (c := 2) (w := u4) (by decide)
    (by rw [uc4.zero, List.length_replicate]; exact b109)
  have e : v' = Function.update (Function.update u4 109 []) 105 ((u4 105 ++ u4 109).drop (u4 2).length)
      := by
    have hj : jBody = ofList ([.cp 109 2, .cp 98 103, .cp 99 103, .drop 99 6, .cp 119 4] ++
        [.rep 119 (iBody 96)] ++ [.cp 98 103, .drop 98 56, .cp 99 103, .drop 99 6, .drop 99 56,
        .cp 119 4] ++ [.rep 119 (iBody 97), .mv 105 109 2]) := rfl
    show exec N K jBody v = _
    rw [hj, exec_ofList_append, exec_ofList_append, exec_ofList_append, e1,
      show exec N K (ofList [Code.rep 119 (iBody 96)]) u1 = u2 from rfl, e3]
    rw [exec_ofList_cons, exec_ofList_cons, exec_ofList_nil, ← hu4, p]
  have n96 : (96 : Fin 200) ∉ wr (.rep 119 (iBody 97)) := by simp only [wr, wr_iBody, wr_ddotC]; decide
  have n105 : (105 : Fin 200) ∉ wr (.rep 119 (iBody 97)) := by simp only [wr, wr_iBody, wr_ddotC]; decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨u4 109, b109, ?_, ?_⟩, fun r hr => ?_⟩
  · rw [e, Function.update_of_ne (by decide), Function.update_of_ne (by decide), bf 96 n96,
      g3 96 (by decide), a96, Nat.add_mul, one_mul]
  · rw [e, Function.update_of_ne (by decide), Function.update_of_ne (by decide), b97]
    congr 3; ring
  · rw [e, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact b80
  · rw [e, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact b81
  · rw [e, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact b82
  · have z109 : u1 109 = List.replicate (N * K) false := by simp [hu1]
    rw [bd, g3 109 (by decide), ad, z109, decRM_replicate, zero_add, mulAccV]
  · rw [e, Function.update_self, uc4.zero, List.length_replicate, bf 105 n105, g3 105 (by decide),
      f2 105 (by simp) (by decide), uv 105 (by decide)]
  · have hm : ∀ t ∈ wr jBody, r ≠ t := fun t ht h => hr (h ▸ ht)
    rw [wr_jBody] at hm
    have hn1 : r ∉ wr (.rep 119 (iBody 96)) := fun h => hm r (by simp [h]) rfl
    have hn2 : r ∉ wr (.rep 119 (iBody 97)) := fun h => hm r (by simp [h]) rfl
    rw [e, Function.update_of_ne (hm 105 (by simp)), Function.update_of_ne (hm 109 (by simp)),
      bf r hn2, g3 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hm 98 (by simp), hm 99 (by simp), hm 119 (by simp)⟩), af r hn1,
      uv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hm 109 (by simp), hm 98 (by simp), hm 99 (by simp), hm 119 (by simp)⟩)]

/-- **`105 := (Σ_{r, i'} ddot(F_{(r, j, i')}, A_{0,(r,i')}, A_{1,(r,i')}))_j`.** The stream of the
row-`1` members starts after `2K · K` members (`97`, positioned by `2K · K` drops). -/
def mulAccC : Code :=
  ofList [.cp 96 104, .cp 97 104, .cp 118 8, .rep 118 (ofList [.cp 119 4, .rep 119 (.drop 97 6)]),
    .cp 105 6, .cp 80 6, .cp 81 2, .cp 82 2, .cp 118 8, .rep 118 jBody]

theorem wr_mulAccC : wr mulAccC = [96, 97, 118, 118, 119, 119, 97, 105, 80, 81, 82, 118, 118] ++
    wr jBody := by
  simp [mulAccC, wr, wr_ofList]

theorem exec_mulAccC (hK : 0 < K) (w : St) (hc : Consts N K w)
    (h6 : w 6 = List.replicate (2 * K * (N * K)) false) (h8 : w 8 = List.replicate (2 * K) false)
    (h56 : w 56 = List.replicate (K * (N * K)) false)
    {fss : List (List (List Bool))} (hf : FamOK N K fss) (hT : fss.length = 2 * (2 * K) * K)
    {as : List (List Bool)} (has : ∀ x ∈ as, x.length = N * K) (hal : as.length = 4 * K)
    (h103 : w 103 = as.flatten) (h104 : w 104 = (fss.map List.flatten).flatten) :
    ∃ os : List (List Bool), (exec N K mulAccC w) 105 = os.flatten ∧ os.length = 2 * K ∧
      (∀ x ∈ os, x.length = N * K) ∧
      (∀ j < 2 * K, decRM N K (os.getD j []) = mulAccV (N := N) fss as j) ∧
      ∀ r, r ∉ wr mulAccC → (exec N K mulAccC w) r = w r := by
  have hfm := famOK_flatten hf
  have hwr : ∀ r : Fin 200, r ∈ ([2, 4, 6, 8, 56, 103, 104] : List (Fin 200)) → r ∉ wr mulAccC := by
    intro r hr
    rw [wr_mulAccC, wr_jBody]
    simp only [wr, wr_iBody, wr_ddotC]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h <;> subst h <;> decide
  -- positioning the stream of row 1
  set v0 := Function.update (Function.update w 96 (fss.map List.flatten).flatten) 97
    (fss.map List.flatten).flatten with hv0
  let P : ℕ → St → Prop := fun n v =>
    Consts N K v ∧ v 97 = ((fss.drop n).map List.flatten).flatten ∧
      ∀ r, r ∉ ([97, 118, 119] : List (Fin 200)) → v r = v0 r
  have hPu : ∀ (c : Fin 200), c ∈ ([118, 119] : List (Fin 200)) → ∀ n v x, P n v →
      P n (Function.update v c x) := by
    intro c hcm n v x ⟨q0, q97, qf⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
    refine ⟨consts_update q0 c (by rcases hcm with rfl | rfl <;> decide) x, ?_, fun r hr => ?_⟩
    · rw [Function.update_of_ne (by rcases hcm with rfl | rfl <;> decide)]; exact q97
    · rw [Function.update_of_ne (fun h => hr (by subst h; rcases hcm with rfl | rfl <;> simp))]
      exact qf r hr
  have v6 : ∀ n v, P n v → v 6 = List.replicate (2 * K * (N * K)) false := fun n v hv => by
    rw [hv.2.2 6 (by decide)]; simp [hv0, h6]
  have dstep : ∀ n v, n + 1 ≤ fss.length → P n v → P (n + 1) (exec N K (.drop 97 6) v) := by
    intro n v hn hv
    rw [exec_drop' (by decide)]
    refine ⟨consts_update hv.1 97 (by decide) _, ?_, fun r hr => ?_⟩
    · rw [Function.update_self, hv.2.1, v6 n v hv, List.length_replicate,
        map_flatten_drop_succ (by omega), List.drop_left' (by
          rw [length_flatten_of (famOK_getD hf (by omega)).2, (famOK_getD hf (by omega)).1])]
    · rw [Function.update_of_ne (fun h => hr (by subst h; simp))]; exact hv.2.2 r hr
  have dinner : ∀ n v, n + K ≤ fss.length → P n v →
      P (n + K) (exec N K (ofList [.cp 119 4, .rep 119 (.drop 97 6)]) v) := by
    intro n v hn hv
    simp only [exec_ofList_cons, exec_ofList_nil]
    have h119 : (exec N K (.cp 119 4) v 119).length = K := by simp [exec, hv.1.k]
    have := exec_rep_step (N := N) (K := K) 119 (.drop 97 6) (by decide) P (hPu 119 (by simp)) 1
      fss.length dstep n (exec N K (.cp 119 4) v) (by rw [h119]; omega)
      (show P n (exec N K (.cp 119 4) v) from hPu 119 (by simp) n v _ hv)
    rwa [h119, mul_one] at this
  have h0 : P 0 (Function.update v0 118 (List.replicate (2 * K) false)) :=
    hPu 118 (by simp) 0 v0 _ ⟨consts_update (consts_update hc 96 (by decide) _) 97 (by decide) _,
      by simp [hv0], fun _ _ => rfl⟩
  have dout := exec_rep_step (N := N) (K := K) 118 _ (by decide) P (hPu 118 (by simp)) K fss.length
    dinner 0 _ (by simp [hT]; nlinarith) h0
  set v1 := exec N K (.rep 118 (ofList [.cp 119 4, .rep 119 (.drop 97 6)]))
    (Function.update v0 118 (List.replicate (2 * K) false)) with hv1
  simp only [Function.update_self, List.length_replicate, zero_add] at dout
  obtain ⟨c1, d97, df⟩ := dout
  have e1 : exec N K (ofList [.cp 96 104, .cp 97 104, .cp 118 8,
      .rep 118 (ofList [.cp 119 4, .rep 119 (.drop 97 6)])]) w = v1 := by
    simp only [exec_ofList_cons, exec_ofList_nil]
    rw [hv1]
    congr 1
    simp [exec, hv0, h104, h8]
  -- the entries
  set v2 := Function.update (Function.update (Function.update (Function.update (Function.update v1
    105 (List.replicate (2 * K * (N * K)) false)) 80 (List.replicate (2 * K * (N * K)) false)) 81
    (List.replicate (N * K) false)) 82 (List.replicate (N * K) false)) 118
    (List.replicate (2 * K) false) with hv2
  have g1 : ∀ r : Fin 200, r ∉ ([97, 118, 119, 96] : List (Fin 200)) → v1 r = w r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [df r (by simp [hr.1, hr.2.1, hr.2.2.1]), hv0, Function.update_of_ne hr.1,
      Function.update_of_ne hr.2.2.2]
  have e2 : exec N K (ofList [.cp 105 6, .cp 80 6, .cp 81 2, .cp 82 2, .cp 118 8]) v1 = v2 := by
    simp only [exec_ofList_cons, exec_ofList_nil, exec, Function.update_apply, Fin.reduceEq,
      ↓reduceIte, g1 6 (by decide), g1 8 (by decide), h6, h8, c1.zero, hv2]
  let Q : ℕ → St → Prop := fun j v =>
    Consts N K v ∧ v 6 = List.replicate (2 * K * (N * K)) false ∧
      v 56 = List.replicate (K * (N * K)) false ∧ v 103 = as.flatten ∧
      v 96 = ((fss.drop (j * K)).map List.flatten).flatten ∧
      v 97 = ((fss.drop (2 * K * K + j * K)).map List.flatten).flatten ∧
      (v 80).length = 2 * K * (N * K) ∧ (v 81).length = N * K ∧ (v 82).length = N * K ∧
      (∃ os : List (List Bool), os.length = j ∧ (∀ x ∈ os, x.length = N * K) ∧
        (∀ c < j, decRM N K (os.getD c []) = mulAccV (N := N) fss as c) ∧
        v 105 = (List.replicate (2 * K * (N * K)) false ++ os.flatten).drop (j * (N * K))) ∧
      ∀ r, r ∉ wr mulAccC → v r = w r
  have hQu : ∀ j v x, Q j v → Q j (Function.update v 118 x) := by
    intro j v x ⟨q0, q6, q56, q103, q96, q97, q80, q81, q82, qo, qf⟩
    obtain ⟨os, a, b, c, d⟩ := qo
    refine ⟨consts_update q0 118 (by decide) x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨os, a, b, c, by rw [Function.update_of_ne (by decide)]; exact d⟩, fun r hr => ?_⟩
    · rw [Function.update_of_ne (by decide)]; exact q6
    · rw [Function.update_of_ne (by decide)]; exact q56
    · rw [Function.update_of_ne (by decide)]; exact q103
    · rw [Function.update_of_ne (by decide)]; exact q96
    · rw [Function.update_of_ne (by decide)]; exact q97
    · rw [Function.update_of_ne (by decide)]; exact q80
    · rw [Function.update_of_ne (by decide)]; exact q81
    · rw [Function.update_of_ne (by decide)]; exact q82
    · rw [Function.update_of_ne (fun h => hr (by rw [h, wr_mulAccC]; simp))]; exact qf r hr
  have jstep : ∀ j v, j + 1 ≤ 2 * K → Q j v → Q (j + 1) (exec N K jBody v) := by
    intro j v hj ⟨q0, q6, q56, q103, q96, q97, q80, q81, q82, ⟨os, ol, ow, ov, o105⟩, qf⟩
    obtain ⟨b96, b97, b80, b81, b82, ⟨acc, al, ad, a105⟩, bf⟩ :=
      exec_jBody (N := N) hK v q0 q6 q56 hf hT has hal (by omega) q103 q96 q97 q80 q81 q82
    have nj : ∀ r : Fin 200, r ∈ ([6, 56, 103] : List (Fin 200)) → r ∉ wr jBody := by
      intro r hr
      rw [wr_jBody]; simp only [wr, wr_iBody, wr_ddotC]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h <;> subst h <;> decide
    refine ⟨consts_exec q0 _ rfl, by rw [bf 6 (nj 6 (by simp)), q6],
      by rw [bf 56 (nj 56 (by simp)), q56], by rw [bf 103 (nj 103 (by simp)), q103], b96, b97, b80,
      b81, b82, ⟨os ++ [acc], by simp [ol], ?_, ?_, ?_⟩, fun r hr => ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ow x hx
      · rw [List.mem_singleton.mp hx]; exact al
    · intro c hc
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | hc
      · rw [List.getD_append _ _ _ _ (by omega)]; exact ov c hc
      · subst hc
        rw [List.getD_append_right _ _ _ _ (by omega), ol, Nat.sub_self]
        exact ad
    · rw [a105, o105]
      have := drop_append_flatten_succ (b := List.replicate (2 * K * (N * K)) false) (vs := os) al ow
      rw [ol] at this
      rw [this, List.length_append, ol, List.length_singleton]
    · rw [bf r (fun h => hr (by rw [wr_mulAccC]; exact List.mem_append_right _ h))]
      exact qf r hr
  have q2 : Q 0 v2 := by
    refine ⟨consts_update (consts_update (consts_update (consts_update (consts_update c1 105
      (by decide) _) 80 (by decide) _) 81 (by decide) _) 82 (by decide) _) 118 (by decide) _,
      ?_, ?_, ?_, ?_, ?_, by simp [hv2], by simp [hv2], by simp [hv2],
      ⟨[], rfl, by simp, fun c hc => absurd hc (Nat.not_lt_zero _), by simp [hv2]⟩, fun r hr => ?_⟩
    · simp only [hv2, Function.update_apply, Fin.reduceEq, ↓reduceIte]; rw [g1 6 (by decide), h6]
    · simp only [hv2, Function.update_apply, Fin.reduceEq, ↓reduceIte]; rw [g1 56 (by decide), h56]
    · simp only [hv2, Function.update_apply, Fin.reduceEq, ↓reduceIte]; rw [g1 103 (by decide), h103]
    · simp only [hv2, Function.update_apply, Fin.reduceEq, ↓reduceIte, zero_mul]
      rw [df 96 (by decide)]; simp [hv0]
    · simp only [hv2, Function.update_apply, Fin.reduceEq, ↓reduceIte, zero_mul, add_zero]
      rw [d97]
    · have hm : ∀ t ∈ wr mulAccC, r ≠ t := fun t ht h => hr (h ▸ ht)
      rw [wr_mulAccC] at hm
      simp only [hv2, Function.update_apply]
      rw [if_neg (hm 118 (by simp)), if_neg (hm 82 (by simp)), if_neg (hm 81 (by simp)),
        if_neg (hm 80 (by simp)), if_neg (hm 105 (by simp)),
        g1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                 exact ⟨hm 97 (by simp), hm 118 (by simp), hm 119 (by simp), hm 96 (by simp)⟩)]
  have jl := exec_rep_step (N := N) (K := K) 118 jBody (by rw [wr_jBody]; simp only [wr, wr_iBody, wr_ddotC]; decide)
    Q hQu 1 (2 * K) jstep 0 v2 (by simp [hv2]) q2
  have h118 : (v2 118).length = 2 * K := by simp [hv2]
  rw [h118, zero_add, mul_one] at jl
  have e : exec N K mulAccC w = exec N K (.rep 118 jBody) v2 := by
    have hm : mulAccC = ofList ([.cp 96 104, .cp 97 104, .cp 118 8,
        .rep 118 (ofList [.cp 119 4, .rep 119 (.drop 97 6)])] ++
        [.cp 105 6, .cp 80 6, .cp 81 2, .cp 82 2, .cp 118 8] ++ [.rep 118 jBody]) := rfl
    rw [hm, exec_ofList_append, exec_ofList_append, e1, e2]
    rfl
  rw [← e] at jl
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨os, ol, ow, ov, o105⟩, qf⟩ := jl
  refine ⟨os, ?_, ol, ow, ov, qf⟩
  rw [o105, ← ol, drop_append_flatten (by rw [ol, List.length_replicate])]

/-! ### The digit dot product as a sum over the gadget columns -/

/-- **`ddot` over `Col = Fin 2 × Fin K`**: `Σ_{(r,i)} v_{rK+i} · d_i(m_r)`. -/
theorem ddotV_eq (vs : List (List Bool)) (m₀ m₁ : List Bool) :
    ddotV (N := N) vs m₀ m₁ = ∑ c : Fin 2 × Fin K,
      decRM N K (vs.getD (c.1.val * K + c.2.val) []) *
        binaryDigit (decRM N K (opd N K (if c.1 = 0 then m₀ else m₁))) c.2.val := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, ddotV, dotRow, dotRow]
  simp only [Fin.val_zero, zero_mul, zero_add, Fin.val_one, one_mul, if_true,
    show ((1 : Fin 2) = 0) = False from by decide, if_false]
  rw [← Fin.sum_univ_eq_sum_range (fun i => decRM N K (vs.getD i []) *
      binaryDigit (decRM N K (opd N K m₀)) i) K,
    ← Fin.sum_univ_eq_sum_range (fun i => decRM N K (vs.getD (K + i) []) *
      binaryDigit (decRM N K (opd N K m₁)) i) K]

end RingVM

end SigabaNeo.Tape
