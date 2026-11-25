import PE.Impl.ExpLUT.Prog.RedChalParse
open SigabaNeo.Tape.RingVM.Hash
/-!
# The vector `b` of the challenge (package G2, `chalP`)

* `exec_add_eq`, `exec_sub_eq`, `exec_canon_eq`: the ring instructions on words of `N K` bits;
* **`exec_bLoop1`**, **`exec_bLoop2`**: the rounds of `b = v_B + B⁽²⁾` along a list of columns
  (the first also pushing `b̄` into `rBbar` and `−v̄_B` into `rNV`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

variable {N K : ℕ}

/-! ### Ring instructions on words -/

theorem exec_add_eq {d a b : Fin 200} {w : St} (ha : (w a).length = N * K)
    (hb : (w b).length = N * K) :
    exec N K (.add d a b) w = Function.update w d (addRMW N K (w a) (w b)) := by
  simp only [exec, opd_eq ha, opd_eq hb]

theorem exec_sub_eq {d a b : Fin 200} {w : St} (ha : (w a).length = N * K)
    (hb : (w b).length = N * K) :
    exec N K (.sub d a b) w = Function.update w d (subRMW N K (w a) (w b)) := by
  simp only [exec, opd_eq ha, opd_eq hb]

theorem exec_canon_eq (hK : 0 < K) {d a : Fin 200} {w : St} (ha : (w a).length = N * K) :
    exec N K (.canon d a) w = Function.update w d (encRM N K (decRM N K (w a))) := by
  simp only [exec, opd_eq ha, canonW_eq hK ha]

theorem exec_cp_eq {d s : Fin 200} {w : St} :
    exec N K (.cp d s) w = Function.update w d (w s) := rfl

theorem mem_words {α : Type} {l : List α} {f : α → RM N K} {y : List Bool}
    (hy : y ∈ l.map fun a => encRM N K (f a)) : y.length = N * K := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy; exact length_encRM _ _ _

theorem words_app {ys : List (List Bool)} (hys : ∀ y ∈ ys, y.length = N * K) {α : Type}
    {l : List α} {f : α → RM N K} : ∀ y ∈ ys ++ l.map fun a => encRM N K (f a),
      y.length = N * K := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact hys y h
  · exact mem_words h

/-! ### The rounds of `b` -/

/-- **A round on a gadget column.** -/
theorem exec_bBody2 (hK : 0 < K) (w : St) {a b LA LB b₀ : List Bool} {ys : List (List Bool)}
    (ha : a.length = N * K) (hb : b.length = N * K) (hys : ∀ y ∈ ys, y.length = N * K)
    (hV : w rV = a ++ LA) (hB : w rB2 = b ++ LB) (hO : w xOut = bufW (N * K) b₀ ys)
    (hNK : (w xCNK).length = N * K) (hv : (w xv).length = N * K) (hf : (w xf).length = N * K) :
    exec N K bBody2 w rV = LA ∧ exec N K bBody2 w rB2 = LB ∧
      exec N K bBody2 w xOut =
        bufW (N * K) b₀ (ys ++ [encRM N K (decRM N K a + decRM N K b)]) ∧
      (exec N K bBody2 w xv).length = N * K ∧ (exec N K bBody2 w xf).length = N * K ∧
      ∀ j, j ∉ [xv, rV, xf, rB2, xS, xO, xOut] → exec N K bBody2 w j = w j := by
  simp only [bBody2, exec_ofList_cons, exec_ofList_nil]
  rw [exec_mv_pop (d := xv) (s := rV) (c := xCNK) (v := a) (L := LA) (by decide)
    (by rw [hv, hNK]) (by rw [ha, hNK]) hV]
  rw [exec_mv_pop (d := xf) (s := rB2) (c := xCNK) (v := b) (L := LB) (by decide)
    (by simp [Function.update_apply, hf, hNK]) (by simp [Function.update_apply, hb, hNK])
    (by simp [Function.update_apply, hB])]
  rw [exec_add_eq (by simp [Function.update_apply, ha]) (by simp [Function.update_apply, hb])]
  rw [exec_canon_eq hK (by simp [Function.update_apply, length_addRMW N K ha])]
  rw [exec_push (by decide) (W := N * K) (b₀ := b₀) (ys := ys) hys
    (by simp [Function.update_apply, hO]) (by simp [Function.update_apply, length_encRM])
    (by simp [Function.update_apply, hNK])]
  refine ⟨by simp [Function.update_apply], by simp [Function.update_apply], ?_,
    by simp [Function.update_apply, ha], by simp [Function.update_apply, hb], ?_⟩
  · simp [Function.update_apply, decRM_addRMW ha hb]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hj
    simp [Function.update_apply, h1, h2, h3, h4, h5, h6, h7]

/-- **A round on a column of `Ā`.** -/
theorem exec_bBody1 (hK : 0 < K) (w : St) {a b LA LB b₀ bb₀ nb₀ : List Bool}
    {ys bys nys : List (List Bool)}
    (ha : a.length = N * K) (hb : b.length = N * K) (hys : ∀ y ∈ ys, y.length = N * K)
    (hbys : ∀ y ∈ bys, y.length = N * K) (hnys : ∀ y ∈ nys, y.length = N * K)
    (hV : w rV = a ++ LA) (hB : w rB2 = b ++ LB) (hO : w xOut = bufW (N * K) b₀ ys)
    (hBb : w rBbar = bufW (N * K) bb₀ bys) (hNV : w rNV = bufW (N * K) nb₀ nys)
    (hZero : w xZero = List.replicate (N * K) false)
    (hNK : (w xCNK).length = N * K) (hv : (w xv).length = N * K) (hf : (w xf).length = N * K) :
    exec N K bBody1 w rV = LA ∧ exec N K bBody1 w rB2 = LB ∧
      exec N K bBody1 w xOut =
        bufW (N * K) b₀ (ys ++ [encRM N K (decRM N K a + decRM N K b)]) ∧
      exec N K bBody1 w rBbar =
        bufW (N * K) bb₀ (bys ++ [encRM N K (decRM N K a + decRM N K b)]) ∧
      exec N K bBody1 w rNV = bufW (N * K) nb₀ (nys ++ [encRM N K (-decRM N K a)]) ∧
      (exec N K bBody1 w xv).length = N * K ∧ (exec N K bBody1 w xf).length = N * K ∧
      ∀ j, j ∉ [xv, rV, xf, rB2, xS, xO, tmpO, rBbar, tmpN, rNV, xOut] →
        exec N K bBody1 w j = w j := by
  simp only [bBody1, exec_ofList_cons, exec_ofList_nil]
  rw [exec_mv_pop (d := xv) (s := rV) (c := xCNK) (v := a) (L := LA) (by decide)
    (by rw [hv, hNK]) (by rw [ha, hNK]) hV]
  rw [exec_mv_pop (d := xf) (s := rB2) (c := xCNK) (v := b) (L := LB) (by decide)
    (by simp [Function.update_apply, hf, hNK]) (by simp [Function.update_apply, hb, hNK])
    (by simp [Function.update_apply, hB])]
  rw [exec_add_eq (d := xS) (by simp [Function.update_apply, ha]) (by simp [Function.update_apply, hb])]
  rw [exec_canon_eq (d := xO) hK (by simp [Function.update_apply, length_addRMW N K ha])]
  rw [exec_cp_eq (d := tmpO)]
  rw [exec_push (d := rBbar) (s := tmpO) (c := xCNK) (by decide) (W := N * K) (b₀ := bb₀) (ys := bys) hbys
    (by simp [Function.update_apply, hBb]) (by simp [Function.update_apply, length_encRM])
    (by simp [Function.update_apply, hNK])]
  rw [exec_sub_eq (d := xS) (by simp [Function.update_apply, hZero]) (by simp [Function.update_apply, ha])]
  rw [exec_canon_eq (d := tmpN) hK (by simp [Function.update_apply, hZero, length_subRMW])]
  rw [exec_push (d := rNV) (s := tmpN) (c := xCNK) (by decide) (W := N * K) (b₀ := nb₀) (ys := nys) hnys
    (by simp [Function.update_apply, hNV]) (by simp [Function.update_apply, length_encRM])
    (by simp [Function.update_apply, hNK])]
  rw [exec_push (d := xOut) (s := xO) (c := xCNK) (by decide) (W := N * K) (b₀ := b₀) (ys := ys) hys
    (by simp [Function.update_apply, hO]) (by simp [Function.update_apply, length_encRM])
    (by simp [Function.update_apply, hNK])]
  have hz : (List.replicate (N * K) false).length = N * K := List.length_replicate
  refine ⟨by simp [Function.update_apply], by simp [Function.update_apply], ?_, ?_, ?_,
    by simp [Function.update_apply, ha], by simp [Function.update_apply, hb], ?_⟩
  · simp [Function.update_apply, decRM_addRMW ha hb]
  · simp [Function.update_apply, decRM_addRMW ha hb]
  · simp [Function.update_apply, hZero, decRM_subRMW hz ha, decRM_replicate]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hj
    simp [Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-! ### The loops of `b` -/

theorem drop_words {α : Type} {l : List α} {i : ℕ} (hi : i < l.length) (f : α → RM N K)
    (L : List Bool) :
    ((l.drop i).map fun a => encRM N K (f a)).flatten ++ L =
      encRM N K (f l[i]) ++ (((l.drop (i + 1)).map fun a => encRM N K (f a)).flatten ++ L) := by
  rw [List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons, List.append_assoc]

theorem take_words {α β : Type} {l : List α} {i : ℕ} (hi : i < l.length) (f : α → β)
    (ys : List β) : ys ++ (l.take (i + 1)).map f = (ys ++ (l.take i).map f) ++ [f l[i]] := by
  rw [take_succ_of_lt hi, List.map_append, List.map_singleton, List.append_assoc]

/-- **The loop of `b` on the gadget columns.** -/
theorem exec_bLoop2 (hK : 0 < K) {α : Type} (l : List α) (x y : α → RM N K) (w : St)
    (LA LB b₀ : List Bool) (ys₀ : List (List Bool)) (hys₀ : ∀ y ∈ ys₀, y.length = N * K)
    (hc : (w cnt).length = l.length)
    (hV : w rV = (l.map fun a => encRM N K (x a)).flatten ++ LA)
    (hB : w rB2 = (l.map fun a => encRM N K (y a)).flatten ++ LB)
    (hO : w xOut = bufW (N * K) b₀ ys₀)
    (hNK : (w xCNK).length = N * K) (hv : (w xv).length = N * K) (hf : (w xf).length = N * K) :
    exec N K (.rep cnt bBody2) w rV = LA ∧ exec N K (.rep cnt bBody2) w rB2 = LB ∧
      exec N K (.rep cnt bBody2) w xOut =
        bufW (N * K) b₀ (ys₀ ++ l.map fun a => encRM N K (x a + y a)) ∧
      (exec N K (.rep cnt bBody2) w xv).length = N * K ∧
      (exec N K (.rep cnt bBody2) w xf).length = N * K ∧
      ∀ j, j ∉ [cnt, xv, rV, xf, rB2, xS, xO, xOut] → exec N K (.rep cnt bBody2) w j = w j := by
  have hcw : cnt ∉ wr bBody2 := by decide
  let P : ℕ → St → Prop := fun i w' =>
    w' rV = ((l.drop i).map fun a => encRM N K (x a)).flatten ++ LA ∧
    w' rB2 = ((l.drop i).map fun a => encRM N K (y a)).flatten ++ LB ∧
    w' xOut = bufW (N * K) b₀ (ys₀ ++ (l.take i).map fun a => encRM N K (x a + y a)) ∧
    (w' xv).length = N * K ∧ (w' xf).length = N * K ∧
    ∀ j, j ∉ [cnt, xv, rV, xf, rB2, xS, xO, xOut] → w' j = w j
  have key := exec_rep_inv (N := N) (K := K) cnt bBody2 hcw P w
    ⟨by simpa using hV, by simpa using hB, by simpa using hO, hv, hf, fun _ _ => rfl⟩
    (fun i hi w' hP _ => by
      rw [hc] at hi
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
      have hu : ∀ j, j ≠ cnt → Function.update w' cnt (w' cnt).tail j = w' j :=
        fun j hj => Function.update_of_ne hj _ _
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := exec_bBody2 hK (Function.update w' cnt (w' cnt).tail)
        (length_encRM _ _ (x l[i])) (length_encRM _ _ (y l[i])) (words_app hys₀)
        (by rw [hu _ (by decide), h1, drop_words hi]) (by rw [hu _ (by decide), h2, drop_words hi])
        (by rw [hu _ (by decide), h3]) (by rw [hu _ (by decide), h6 _ (by decide), hNK])
        (by rw [hu _ (by decide), h4]) (by rw [hu _ (by decide), h5])
      refine ⟨r1, r2, ?_, r4, r5, ?_⟩
      · rw [r3, decRM_encRM hK, decRM_encRM hK, take_words hi]
      · intro j hj
        have hj' : j ∉ [xv, rV, xf, rB2, xS, xO, xOut] := fun h => hj (List.mem_cons_of_mem _ h)
        have hjc : j ≠ cnt := fun h => hj (h ▸ List.mem_cons_self)
        rw [r6 j hj', hu j hjc, h6 j hj])
  rw [hc] at key
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := key
  refine ⟨?_, ?_, ?_, h4, h5, h6⟩
  · rw [h1, List.drop_length]; rfl
  · rw [h2, List.drop_length]; rfl
  · rw [h3, List.take_length]

/-- **The loop of `b` on the columns of `Ā`.** -/
theorem exec_bLoop1 (hK : 0 < K) {α : Type} (l : List α) (x y : α → RM N K) (w : St)
    (LA LB b₀ : List Bool) (ys₀ : List (List Bool)) (hys₀ : ∀ y ∈ ys₀, y.length = N * K)
    (hc : (w cnt).length = l.length)
    (hV : w rV = (l.map fun a => encRM N K (x a)).flatten ++ LA)
    (hB : w rB2 = (l.map fun a => encRM N K (y a)).flatten ++ LB)
    (hO : w xOut = bufW (N * K) b₀ ys₀)
    (hBb : w rBbar = List.replicate (l.length * (N * K)) false)
    (hNV : w rNV = List.replicate (l.length * (N * K)) false)
    (hZero : w xZero = List.replicate (N * K) false)
    (hNK : (w xCNK).length = N * K) (hv : (w xv).length = N * K) (hf : (w xf).length = N * K) :
    exec N K (.rep cnt bBody1) w rV = LA ∧ exec N K (.rep cnt bBody1) w rB2 = LB ∧
      exec N K (.rep cnt bBody1) w xOut =
        bufW (N * K) b₀ (ys₀ ++ l.map fun a => encRM N K (x a + y a)) ∧
      exec N K (.rep cnt bBody1) w rBbar = (l.map fun a => encRM N K (x a + y a)).flatten ∧
      exec N K (.rep cnt bBody1) w rNV = (l.map fun a => encRM N K (-x a)).flatten ∧
      (exec N K (.rep cnt bBody1) w xv).length = N * K ∧
      (exec N K (.rep cnt bBody1) w xf).length = N * K ∧
      ∀ j, j ∉ [cnt, xv, rV, xf, rB2, xS, xO, tmpO, rBbar, tmpN, rNV, xOut] →
        exec N K (.rep cnt bBody1) w j = w j := by
  have hcw : cnt ∉ wr bBody1 := by decide
  set z := List.replicate (l.length * (N * K)) false
  let P : ℕ → St → Prop := fun i w' =>
    w' rV = ((l.drop i).map fun a => encRM N K (x a)).flatten ++ LA ∧
    w' rB2 = ((l.drop i).map fun a => encRM N K (y a)).flatten ++ LB ∧
    w' xOut = bufW (N * K) b₀ (ys₀ ++ (l.take i).map fun a => encRM N K (x a + y a)) ∧
    w' rBbar = bufW (N * K) z ([] ++ (l.take i).map fun a => encRM N K (x a + y a)) ∧
    w' rNV = bufW (N * K) z ([] ++ (l.take i).map fun a => encRM N K (-x a)) ∧
    (w' xv).length = N * K ∧ (w' xf).length = N * K ∧
    ∀ j, j ∉ [cnt, xv, rV, xf, rB2, xS, xO, tmpO, rBbar, tmpN, rNV, xOut] → w' j = w j
  have key := exec_rep_inv (N := N) (K := K) cnt bBody1 hcw P w
    ⟨by simpa using hV, by simpa using hB, by simpa using hO, by simp [hBb, bufW_nil],
      by simp [hNV, bufW_nil], hv, hf, fun _ _ => rfl⟩
    (fun i hi w' hP _ => by
      rw [hc] at hi
      obtain ⟨h1, h2, h3, h3b, h3n, h4, h5, h6⟩ := hP
      have hu : ∀ j, j ≠ cnt → Function.update w' cnt (w' cnt).tail j = w' j :=
        fun j hj => Function.update_of_ne hj _ _
      obtain ⟨r1, r2, r3, r3b, r3n, r4, r5, r6⟩ := exec_bBody1 hK
        (Function.update w' cnt (w' cnt).tail)
        (length_encRM _ _ (x l[i])) (length_encRM _ _ (y l[i])) (words_app hys₀)
        (words_app (fun _ h => absurd h List.not_mem_nil))
        (words_app (fun _ h => absurd h List.not_mem_nil))
        (by rw [hu _ (by decide), h1, drop_words hi]) (by rw [hu _ (by decide), h2, drop_words hi])
        (by rw [hu _ (by decide), h3]) (by rw [hu _ (by decide), h3b])
        (by rw [hu _ (by decide), h3n]) (by rw [hu _ (by decide), h6 _ (by decide), hZero])
        (by rw [hu _ (by decide), h6 _ (by decide), hNK])
        (by rw [hu _ (by decide), h4]) (by rw [hu _ (by decide), h5])
      refine ⟨r1, r2, ?_, ?_, ?_, r4, r5, ?_⟩
      · rw [r3, decRM_encRM hK, decRM_encRM hK, take_words hi]
      · rw [r3b, decRM_encRM hK, decRM_encRM hK, take_words hi]
      · rw [r3n, decRM_encRM hK, take_words hi]
      · intro j hj
        have hj' : j ∉ [xv, rV, xf, rB2, xS, xO, tmpO, rBbar, tmpN, rNV, xOut] :=
          fun h => hj (List.mem_cons_of_mem _ h)
        have hjc : j ≠ cnt := fun h => hj (h ▸ List.mem_cons_self)
        rw [r6 j hj', hu j hjc, h6 j hj])
  rw [hc] at key
  obtain ⟨h1, h2, h3, h3b, h3n, h4, h5, h6⟩ := key
  have hw : ∀ (f : α → RM N K), ∀ y ∈ l.map fun a => encRM N K (f a), y.length = N * K :=
    fun f y hy => mem_words hy
  refine ⟨?_, ?_, ?_, ?_, ?_, h4, h5, h6⟩
  · rw [h1, List.drop_length]; rfl
  · rw [h2, List.drop_length]; rfl
  · rw [h3, List.take_length]
  · rw [h3b, List.take_length, List.nil_append, bufW_full (hw _) (by simp [z])]
  · rw [h3n, List.take_length, List.nil_append, bufW_full (hw _) (by simp [z])]

end AdvancedEncryption.ExpLUT.Prog.RedChal
