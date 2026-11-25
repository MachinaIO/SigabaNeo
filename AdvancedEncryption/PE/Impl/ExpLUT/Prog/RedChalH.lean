import PE.Impl.ExpLUT.Prog.RedChalB

/-!
# The helpers of the challenge (package G2, `chalP`)

The helper samples of the instance are stored in the registry's row order (`i` outer, the helper
`j` inner); the challenge lists them helper by helper. `hC` reads them with a stride:

* **`exec_hIn0Loop`**, **`exec_hIn1Loop`**: `n` rounds reading the words `vs[s + i S]` (`i < n`)
  of a stream, each plus the next word of `H⁽²⁾` (minus `2^i` for the second gadget half);
* **`exec_hOuterLoop`**: the helpers `j < S`, the first gadget half from the key rows (offset
  `s0`), the second from the plain rows (offset `s1`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog.RedVM

variable {N K : ℕ}

theorem exec_drop_eq {t c : Fin 200} (h : t ≠ c) {w : St} :
    exec N K (.drop t c) w = Function.update w t ((w t).drop (w c).length) := by
  simp only [exec, h, ite_false]

/-- Dropping whole words of a stream of words. -/
theorem drop_flatten_words {n : ℕ} : ∀ {vs : List (List Bool)}, (∀ x ∈ vs, x.length = n) →
    ∀ k, vs.flatten.drop (k * n) = (vs.drop k).flatten
  | [], _, k => by simp
  | v :: vs, hv, 0 => by simp
  | v :: vs, hv, k + 1 => by
    rw [List.flatten_cons, Nat.add_mul, one_mul, Nat.add_comm, ← List.drop_drop,
      List.drop_append_of_le_length (by rw [hv v List.mem_cons_self]),
      show n = v.length from (hv v List.mem_cons_self).symm, List.drop_length, List.nil_append,
      ← show n = v.length from (hv v List.mem_cons_self).symm,
      drop_flatten_words (fun x hx => hv x (List.mem_cons_of_mem _ hx)) k]
    rfl

/-! ### Rounds -/

/-- **A round on the first gadget half.** -/
theorem exec_hIn0 (hK : 0 < K) (w : St) {a b LT LB b₀ : List Bool} {ys : List (List Bool)}
    (ha : a.length = N * K) (hb : b.length = N * K) (hys : ∀ y ∈ ys, y.length = N * K)
    (hT : w tmp = a ++ LT) (hH : w rH2 = b ++ LB) (hO : w xOut = bufW (N * K) b₀ ys)
    (hNK : (w xCNK).length = N * K) (hv : (w xv).length = N * K) (hf : (w xf).length = N * K) :
    exec N K hIn0 w tmp = LT.drop (w cSkip).length ∧ exec N K hIn0 w rH2 = LB ∧
      exec N K hIn0 w xOut =
        bufW (N * K) b₀ (ys ++ [encRM N K (decRM N K a + decRM N K b)]) ∧
      (exec N K hIn0 w xv).length = N * K ∧ (exec N K hIn0 w xf).length = N * K ∧
      ∀ j, j ∉ [xv, tmp, xf, rH2, xS, xO, xOut] → exec N K hIn0 w j = w j := by
  simp only [hIn0, exec_ofList_cons, exec_ofList_nil]
  rw [exec_mv_pop (d := xv) (s := tmp) (c := xCNK) (v := a) (L := LT) (by decide)
    (by rw [hv, hNK]) (by rw [ha, hNK]) hT]
  rw [exec_drop_eq (t := tmp) (c := cSkip) (by decide)]
  rw [exec_mv_pop (d := xf) (s := rH2) (c := xCNK) (v := b) (L := LB) (by decide)
    (by simp [Function.update_apply, hf, hNK]) (by simp [Function.update_apply, hb, hNK])
    (by simp [Function.update_apply, hH])]
  rw [exec_add_eq (d := xS) (by simp [Function.update_apply, ha])
    (by simp [Function.update_apply, hb])]
  rw [exec_canon_eq (d := xO) hK (by simp [Function.update_apply, length_addRMW N K ha])]
  rw [exec_push (d := xOut) (s := xO) (c := xCNK) (by decide) (W := N * K) (b₀ := b₀) (ys := ys)
    hys (by simp [Function.update_apply, hO]) (by simp [Function.update_apply, length_encRM])
    (by simp [Function.update_apply, hNK])]
  refine ⟨by simp [Function.update_apply], by simp [Function.update_apply], ?_,
    by simp [Function.update_apply, ha], by simp [Function.update_apply, hb], ?_⟩
  · simp [Function.update_apply, decRM_addRMW ha hb]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hj
    simp [Function.update_apply, h1, h2, h3, h4, h5, h6, h7]

/-- **A round on the second gadget half.** -/
theorem exec_hIn1 (hK : 0 < K) (w : St) {a b LT LB b₀ : List Bool} {ys : List (List Bool)}
    (ha : a.length = N * K) (hb : b.length = N * K) (hys : ∀ y ∈ ys, y.length = N * K)
    (hT : w tmp = a ++ LT) (hH : w rH2 = b ++ LB) (hO : w xOut = bufW (N * K) b₀ ys)
    (hG : (w rG).length = N * K)
    (hNK : (w xCNK).length = N * K) (hv : (w xv).length = N * K) (hf : (w xf).length = N * K) :
    exec N K hIn1 w tmp = LT.drop (w cSkip).length ∧ exec N K hIn1 w rH2 = LB ∧
      exec N K hIn1 w xOut = bufW (N * K) b₀
        (ys ++ [encRM N K (decRM N K a + decRM N K b - decRM N K (w rG))]) ∧
      (exec N K hIn1 w rG).length = N * K ∧
      decRM N K (exec N K hIn1 w rG) = 2 * decRM N K (w rG) ∧
      (exec N K hIn1 w xv).length = N * K ∧ (exec N K hIn1 w xf).length = N * K ∧
      ∀ j, j ∉ [xv, tmp, xf, rH2, xS, xO, xOut, rG] → exec N K hIn1 w j = w j := by
  simp only [hIn1, exec_ofList_cons, exec_ofList_nil]
  rw [exec_mv_pop (d := xv) (s := tmp) (c := xCNK) (v := a) (L := LT) (by decide)
    (by rw [hv, hNK]) (by rw [ha, hNK]) hT]
  rw [exec_drop_eq (t := tmp) (c := cSkip) (by decide)]
  rw [exec_mv_pop (d := xf) (s := rH2) (c := xCNK) (v := b) (L := LB) (by decide)
    (by simp [Function.update_apply, hf, hNK]) (by simp [Function.update_apply, hb, hNK])
    (by simp [Function.update_apply, hH])]
  rw [exec_add_eq (d := xS) (a := xv) (by simp [Function.update_apply, ha])
    (by simp [Function.update_apply, hb])]
  rw [exec_sub_eq (d := xS) (by simp [Function.update_apply, length_addRMW N K ha])
    (by simp [Function.update_apply, hG])]
  rw [exec_canon_eq (d := xO) hK (by simp [Function.update_apply, length_subRMW N K
    (length_addRMW N K ha _)])]
  rw [exec_push (d := xOut) (s := xO) (c := xCNK) (by decide) (W := N * K) (b₀ := b₀) (ys := ys)
    hys (by simp [Function.update_apply, hO]) (by simp [Function.update_apply, length_encRM])
    (by simp [Function.update_apply, hNK])]
  rw [exec_add_eq (d := rG) (by simp [Function.update_apply, hG])
    (by simp [Function.update_apply, hG])]
  refine ⟨by simp [Function.update_apply], by simp [Function.update_apply], ?_,
    by simp [Function.update_apply, length_addRMW N K hG], ?_,
    by simp [Function.update_apply, ha], by simp [Function.update_apply, hb], ?_⟩
  · simp [Function.update_apply, decRM_subRMW (length_addRMW N K ha _) hG, decRM_addRMW ha hb]
  · simp [Function.update_apply, decRM_addRMW hG hG, two_mul]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hj
    simp [Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8]

/-! ### The inner loops -/

theorem tmp_step {vs : List (List Bool)} (hvs : ∀ x ∈ vs, x.length = N * K) {s S i : ℕ}
    (hS : 1 ≤ S) (hi : s + i * S < vs.length) :
    (vs.drop (s + i * S)).flatten = vs[s + i * S] ++ (vs.drop (s + i * S + 1)).flatten ∧
      ((vs.drop (s + i * S + 1)).flatten).drop ((S - 1) * (N * K)) =
        (vs.drop (s + (i + 1) * S)).flatten := by
  refine ⟨by rw [List.drop_eq_getElem_cons hi, List.flatten_cons], ?_⟩
  rw [drop_flatten_words (fun x hx => hvs x (List.mem_of_mem_drop hx)), List.drop_drop]
  congr 2
  rw [Nat.add_mul, one_mul]
  omega

theorem range_drop_words {i n : ℕ} (hi : i < n) (f : ℕ → RM N K) (L : List Bool) :
    (((List.range n).drop i).map fun a => encRM N K (f a)).flatten ++ L =
      encRM N K (f i) ++ ((((List.range n).drop (i + 1)).map fun a => encRM N K (f a)).flatten ++
        L) := by
  rw [drop_words (by simpa using hi), List.getElem_range]

theorem range_take_words {β : Type} {i n : ℕ} (hi : i < n) (f : ℕ → β) (ys : List β) :
    ys ++ ((List.range n).take (i + 1)).map f = (ys ++ ((List.range n).take i).map f) ++ [f i] := by
  rw [take_words (by simpa using hi), List.getElem_range]

/-- **`n` rounds on the first gadget half.** -/
theorem exec_hIn0Loop (hK : 0 < K) (n s S : ℕ) (vs : List (List Bool))
    (hvs : ∀ x ∈ vs, x.length = N * K) (hS : 1 ≤ S) (hlen : ∀ i < n, s + i * S < vs.length)
    (h : ℕ → RM N K) (w : St) (LB b₀ : List Bool) (ys₀ : List (List Bool))
    (hys₀ : ∀ y ∈ ys₀, y.length = N * K) (hc : (w cnt).length = n)
    (hT : w tmp = (vs.drop s).flatten) (hSk : (w cSkip).length = (S - 1) * (N * K))
    (hH : w rH2 = ((List.range n).map fun i => encRM N K (h i)).flatten ++ LB)
    (hO : w xOut = bufW (N * K) b₀ ys₀)
    (hNK : (w xCNK).length = N * K) (hv : (w xv).length = N * K) (hf : (w xf).length = N * K) :
    exec N K (.rep cnt hIn0) w rH2 = LB ∧
      exec N K (.rep cnt hIn0) w xOut = bufW (N * K) b₀ (ys₀ ++ (List.range n).map fun i =>
        encRM N K (decRM N K (vs.getD (s + i * S) []) + h i)) ∧
      (exec N K (.rep cnt hIn0) w xv).length = N * K ∧
      (exec N K (.rep cnt hIn0) w xf).length = N * K ∧
      ∀ j, j ∉ [cnt, xv, tmp, xf, rH2, xS, xO, xOut] → exec N K (.rep cnt hIn0) w j = w j := by
  have hcw : cnt ∉ wr hIn0 := by decide
  let out : ℕ → List Bool := fun i => encRM N K (decRM N K (vs.getD (s + i * S) []) + h i)
  let P : ℕ → St → Prop := fun i w' =>
    w' tmp = (vs.drop (s + i * S)).flatten ∧
    w' rH2 = (((List.range n).drop i).map fun i => encRM N K (h i)).flatten ++ LB ∧
    w' xOut = bufW (N * K) b₀ (ys₀ ++ ((List.range n).take i).map out) ∧
    (w' xv).length = N * K ∧ (w' xf).length = N * K ∧
    ∀ j, j ∉ [cnt, xv, tmp, xf, rH2, xS, xO, xOut] → w' j = w j
  have key := exec_rep_inv (N := N) (K := K) cnt hIn0 hcw P w
    ⟨by simpa using hT, by simpa using hH, by simpa using hO, hv, hf, fun _ _ => rfl⟩
    (fun i hi w' hP _ => by
      rw [hc] at hi
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
      have hu : ∀ j, j ≠ cnt → Function.update w' cnt (w' cnt).tail j = w' j :=
        fun j hj => Function.update_of_ne hj _ _
      obtain ⟨t1, t2⟩ := tmp_step hvs hS (hlen i hi)
      have hw := hvs _ (List.getElem_mem (hlen i hi))
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := exec_hIn0 hK (Function.update w' cnt (w' cnt).tail)
        hw (length_encRM _ _ (h i)) (words_app hys₀)
        (by rw [hu _ (by decide), h1, t1]) (by rw [hu _ (by decide), h2, range_drop_words hi])
        (by rw [hu _ (by decide), h3]) (by rw [hu _ (by decide), h6 _ (by decide), hNK])
        (by rw [hu _ (by decide), h4]) (by rw [hu _ (by decide), h5])
      refine ⟨?_, r2, ?_, r4, r5, ?_⟩
      · rw [r1, hu _ (by decide), h6 _ (by decide), hSk, t2]
      · rw [r3, decRM_encRM hK, range_take_words hi]
        simp only [out, List.getD_eq_getElem _ _ (hlen i hi)]
      · intro j hj
        have hj' : j ∉ [xv, tmp, xf, rH2, xS, xO, xOut] := fun h => hj (List.mem_cons_of_mem _ h)
        have hjc : j ≠ cnt := fun h => hj (h ▸ List.mem_cons_self)
        rw [r6 j hj', hu j hjc, h6 j hj])
  rw [hc] at key
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := key
  refine ⟨?_, ?_, h4, h5, h6⟩
  · rw [h2, show (List.range n).drop n = [] by simp]; rfl
  · rw [h3, show (List.range n).take n = List.range n by simp]

/-- **`n` rounds on the second gadget half**, from `rG = 1`. -/
theorem exec_hIn1Loop (hK : 0 < K) (n s S : ℕ) (vs : List (List Bool))
    (hvs : ∀ x ∈ vs, x.length = N * K) (hS : 1 ≤ S) (hlen : ∀ i < n, s + i * S < vs.length)
    (h : ℕ → RM N K) (w : St) (LB b₀ : List Bool) (ys₀ : List (List Bool))
    (hys₀ : ∀ y ∈ ys₀, y.length = N * K) (hc : (w cnt).length = n)
    (hT : w tmp = (vs.drop s).flatten) (hSk : (w cSkip).length = (S - 1) * (N * K))
    (hH : w rH2 = ((List.range n).map fun i => encRM N K (h i)).flatten ++ LB)
    (hO : w xOut = bufW (N * K) b₀ ys₀)
    (hG : (w rG).length = N * K) (hG1 : decRM N K (w rG) = 1)
    (hNK : (w xCNK).length = N * K) (hv : (w xv).length = N * K) (hf : (w xf).length = N * K) :
    exec N K (.rep cnt hIn1) w rH2 = LB ∧
      exec N K (.rep cnt hIn1) w xOut = bufW (N * K) b₀ (ys₀ ++ (List.range n).map fun i =>
        encRM N K (decRM N K (vs.getD (s + i * S) []) + h i - 2 ^ i)) ∧
      (exec N K (.rep cnt hIn1) w xv).length = N * K ∧
      (exec N K (.rep cnt hIn1) w xf).length = N * K ∧
      ∀ j, j ∉ [cnt, xv, tmp, xf, rH2, xS, xO, xOut, rG] → exec N K (.rep cnt hIn1) w j = w j := by
  have hcw : cnt ∉ wr hIn1 := by decide
  let out : ℕ → List Bool := fun i => encRM N K (decRM N K (vs.getD (s + i * S) []) + h i - 2 ^ i)
  let P : ℕ → St → Prop := fun i w' =>
    w' tmp = (vs.drop (s + i * S)).flatten ∧
    w' rH2 = (((List.range n).drop i).map fun i => encRM N K (h i)).flatten ++ LB ∧
    w' xOut = bufW (N * K) b₀ (ys₀ ++ ((List.range n).take i).map out) ∧
    (w' rG).length = N * K ∧ decRM N K (w' rG) = 2 ^ i ∧
    (w' xv).length = N * K ∧ (w' xf).length = N * K ∧
    ∀ j, j ∉ [cnt, xv, tmp, xf, rH2, xS, xO, xOut, rG] → w' j = w j
  have key := exec_rep_inv (N := N) (K := K) cnt hIn1 hcw P w
    ⟨by simpa using hT, by simpa using hH, by simpa using hO, hG, by rw [hG1, pow_zero], hv, hf,
      fun _ _ => rfl⟩
    (fun i hi w' hP _ => by
      rw [hc] at hi
      obtain ⟨h1, h2, h3, hg, hg1, h4, h5, h6⟩ := hP
      have hu : ∀ j, j ≠ cnt → Function.update w' cnt (w' cnt).tail j = w' j :=
        fun j hj => Function.update_of_ne hj _ _
      obtain ⟨t1, t2⟩ := tmp_step hvs hS (hlen i hi)
      have hw := hvs _ (List.getElem_mem (hlen i hi))
      obtain ⟨r1, r2, r3, rg, rg1, r4, r5, r6⟩ := exec_hIn1 hK (Function.update w' cnt (w' cnt).tail)
        hw (length_encRM _ _ (h i)) (words_app hys₀)
        (by rw [hu _ (by decide), h1, t1]) (by rw [hu _ (by decide), h2, range_drop_words hi])
        (by rw [hu _ (by decide), h3]) (by rw [hu _ (by decide), hg])
        (by rw [hu _ (by decide), h6 _ (by decide), hNK])
        (by rw [hu _ (by decide), h4]) (by rw [hu _ (by decide), h5])
      refine ⟨?_, r2, ?_, rg, ?_, r4, r5, ?_⟩
      · rw [r1, hu _ (by decide), h6 _ (by decide), hSk, t2]
      · rw [r3, decRM_encRM hK, range_take_words hi, hu _ (by decide), hg1]
        simp only [out, List.getD_eq_getElem _ _ (hlen i hi)]
      · rw [rg1, hu _ (by decide), hg1, pow_succ, mul_comm]
      · intro j hj
        have hj' : j ∉ [xv, tmp, xf, rH2, xS, xO, xOut, rG] :=
          fun h => hj (List.mem_cons_of_mem _ h)
        have hjc : j ≠ cnt := fun h => hj (h ▸ List.mem_cons_self)
        rw [r6 j hj', hu j hjc, h6 j hj])
  rw [hc] at key
  obtain ⟨-, h2, h3, -, -, h4, h5, h6⟩ := key
  refine ⟨?_, ?_, h4, h5, h6⟩
  · rw [h2, show (List.range n).drop n = [] by simp]; rfl
  · rw [h3, show (List.range n).take n = List.range n by simp]

/-! ### One helper -/

theorem drop_one_word {vs : List (List Bool)} (hvs : ∀ x ∈ vs, x.length = N * K) (a : ℕ) :
    (vs.drop a).flatten.drop (N * K) = (vs.drop (a + 1)).flatten := by
  have := drop_flatten_words (vs := vs.drop a) (n := N * K)
    (fun x hx => hvs x (List.mem_of_mem_drop hx)) 1
  rw [one_mul, List.drop_drop] at this
  rw [this, Nat.add_comm]

/-- The words of a helper on one gadget half. -/
noncomputable def outs0 (vs : List (List Bool)) (n s S : ℕ) (h : ℕ → RM N K) : List (List Bool) :=
  (List.range n).map fun i => encRM N K (decRM N K (vs.getD (s + i * S) []) + h i)

/-- The words of a helper on the second gadget half. -/
noncomputable def outs1 (vs : List (List Bool)) (n s S : ℕ) (h : ℕ → RM N K) : List (List Bool) :=
  (List.range n).map fun i => encRM N K (decRM N K (vs.getD (s + i * S) []) + h i - 2 ^ i)

theorem mem_outs0 {vs : List (List Bool)} {n s S : ℕ} {h : ℕ → RM N K} :
    ∀ y ∈ outs0 vs n s S h, y.length = N * K := fun _ hy => mem_words hy

theorem mem_outs1 {vs : List (List Bool)} {n s S : ℕ} {h : ℕ → RM N K} :
    ∀ y ∈ outs1 vs n s S h, y.length = N * K := fun _ hy => mem_words hy

/-- The registers `hOuter` writes. -/
def hOW : List (Fin 200) := [tmp, cnt, xv, xf, rH2, xS, xO, xOut, rG, rS0, rS1]

/-- **One helper.** -/
theorem exec_hOuter (hK : 0 < K) (n S a0 a1 : ℕ) (vs : List (List Bool))
    (hvs : ∀ x ∈ vs, x.length = N * K) (hS : 1 ≤ S) (hl0 : ∀ i < n, a0 + i * S < vs.length)
    (hl1 : ∀ i < n, a1 + i * S < vs.length)
    (h0 h1 : ℕ → RM N K) (w : St) (LB b₀ : List Bool) (ys₀ : List (List Bool))
    (hys₀ : ∀ y ∈ ys₀, y.length = N * K) (hc : (w cK).length = n)
    (hT0 : w rS0 = (vs.drop a0).flatten) (hT1 : w rS1 = (vs.drop a1).flatten)
    (hSk : (w cSkip).length = (S - 1) * (N * K))
    (hH : w rH2 = ((List.range n).map fun i => encRM N K (h0 i)).flatten ++
      (((List.range n).map fun i => encRM N K (h1 i)).flatten ++ LB))
    (hO : w xOut = bufW (N * K) b₀ ys₀)
    (hG : (w r1).length = N * K) (hG1 : decRM N K (w r1) = 1)
    (hNK : (w xCNK).length = N * K) (hv : (w xv).length = N * K) (hf : (w xf).length = N * K) :
    exec N K hOuter w rS0 = (vs.drop (a0 + 1)).flatten ∧
      exec N K hOuter w rS1 = (vs.drop (a1 + 1)).flatten ∧
      exec N K hOuter w rH2 = LB ∧
      exec N K hOuter w xOut = bufW (N * K) b₀ (ys₀ ++ (outs0 vs n a0 S h0 ++ outs1 vs n a1 S h1)) ∧
      (exec N K hOuter w xv).length = N * K ∧ (exec N K hOuter w xf).length = N * K ∧
      ∀ j, j ∉ hOW → exec N K hOuter w j = w j := by
  simp only [hOuter, exec_ofList_cons, exec_ofList_nil]
  -- the first half
  set w2 := exec N K (.cp cnt cK) (exec N K (.cp tmp rS0) w) with hw2
  have e2 : ∀ j, j ≠ cnt → j ≠ tmp → w2 j = w j := fun j h1 h2 => by
    simp [hw2, exec_cp_eq, Function.update_apply, h1, h2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := exec_hIn0Loop hK n a0 S vs hvs hS hl0 h0 w2
    (((List.range n).map fun i => encRM N K (h1 i)).flatten ++ LB) b₀ ys₀ hys₀
    (by simp [hw2, exec_cp_eq, hc]) (by simp [hw2, exec_cp_eq, Function.update_apply, hT0])
    (by rw [e2 _ (by decide) (by decide), hSk]) (by rw [e2 _ (by decide) (by decide), hH])
    (by rw [e2 _ (by decide) (by decide), hO]) (by rw [e2 _ (by decide) (by decide), hNK])
    (by rw [e2 _ (by decide) (by decide), hv]) (by rw [e2 _ (by decide) (by decide), hf])
  set w3 := exec N K (.rep cnt hIn0) w2 with hw3
  have e3 : ∀ j, j ∉ [cnt, xv, tmp, xf, rH2, xS, xO, xOut] → w3 j = w j := fun j hj => by
    rw [p5 j hj]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    exact e2 j hj.1 hj.2.2.1
  rw [exec_drop_eq (t := rS0) (c := xCNK) (by decide)]
  set w4 := Function.update w3 rS0 ((w3 rS0).drop (w3 xCNK).length) with hw4
  have h4S0 : w4 rS0 = (vs.drop (a0 + 1)).flatten := by
    rw [hw4, Function.update_self, e3 _ (by decide), e3 _ (by decide), hT0, hNK,
      drop_one_word hvs]
  -- the second half
  set w7 := exec N K (.cp cnt cK) (exec N K (.cp rG r1) (exec N K (.cp tmp rS1) w4)) with hw7
  have e7 : ∀ j, j ≠ cnt → j ≠ tmp → j ≠ rG → w7 j = w4 j := fun j h1 h2 h3 => by
    simp [hw7, exec_cp_eq, Function.update_apply, h1, h2, h3]
  have e74 : ∀ j, j ∉ [cnt, xv, tmp, xf, rH2, xS, xO, xOut, rG, rS0] → w7 j = w j := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [e7 j hj.1 hj.2.2.1 hj.2.2.2.2.2.2.2.2.1, hw4, Function.update_of_ne hj.2.2.2.2.2.2.2.2.2,
      e3 j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1,
        hj.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.1])]
  have e4 : ∀ j, j ≠ rS0 → w4 j = w3 j := fun j hj => Function.update_of_ne hj _ _
  obtain ⟨q1, q2, q3, q4, q5⟩ := exec_hIn1Loop hK n a1 S vs hvs hS hl1 h1 w7 LB b₀
    (ys₀ ++ outs0 vs n a0 S h0) (words_app hys₀)
    (by simp [hw7, exec_cp_eq, Function.update_apply, e4, e3, hc])
    (by simp [hw7, exec_cp_eq, Function.update_apply]
        rw [e4 _ (by decide), e3 _ (by decide), hT1])
    (by rw [e74 _ (by decide), hSk])
    (by rw [e7 _ (by decide) (by decide) (by decide), e4 _ (by decide), p1])
    (by rw [e7 _ (by decide) (by decide) (by decide), e4 _ (by decide), p2]; rfl)
    (by simp [hw7, exec_cp_eq, Function.update_apply]; rw [e4 _ (by decide), e3 _ (by decide), hG])
    (by simp [hw7, exec_cp_eq, Function.update_apply]; rw [e4 _ (by decide), e3 _ (by decide), hG1])
    (by rw [e74 _ (by decide), hNK])
    (by rw [e7 _ (by decide) (by decide) (by decide), e4 _ (by decide), p3])
    (by rw [e7 _ (by decide) (by decide) (by decide), e4 _ (by decide), p4])
  set w8 := exec N K (.rep cnt hIn1) w7 with hw8
  rw [exec_drop_eq (t := rS1) (c := xCNK) (by decide)]
  have e8 : ∀ j, j ∉ [cnt, xv, tmp, xf, rH2, xS, xO, xOut, rG] → w8 j = w7 j := q5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by decide), e8 _ (by decide), e7 _ (by decide) (by decide)
      (by decide), h4S0]
  · rw [Function.update_self, e8 _ (by decide), e8 _ (by decide), e74 _ (by decide),
      e74 _ (by decide), hT1, hNK, drop_one_word hvs]
  · rw [Function.update_of_ne (by decide), q1]
  · rw [Function.update_of_ne (by decide), q2, outs0, outs1, List.append_assoc]
  · rw [Function.update_of_ne (by decide), q3]
  · rw [Function.update_of_ne (by decide), q4]
  · intro j hj
    simp only [hOW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [Function.update_of_ne hj.2.2.2.2.2.2.2.2.2.2, e8 j (by simp [hj.1, hj.2.1, hj.2.2.1,
      hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.2.2.1]), e74 j (by simp [hj.1, hj.2.1, hj.2.2.1,
      hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.2.1])]

/-! ### The helpers -/

/-- The words of `H⁽²⁾` of a helper. -/
noncomputable def hblk (n : ℕ) (F0 F1 : ℕ → ℕ → RM N K) (j : ℕ) : List Bool :=
  ((List.range n).map fun i => encRM N K (F0 j i)).flatten ++
    ((List.range n).map fun i => encRM N K (F1 j i)).flatten

/-- The words of the challenge of a helper. -/
noncomputable def hout (vs : List (List Bool)) (n S s0 s1 : ℕ) (F0 F1 : ℕ → ℕ → RM N K) (j : ℕ) :
    List (List Bool) :=
  outs0 vs n (s0 + j) S (F0 j) ++ outs1 vs n (s1 + j) S (F1 j)

theorem mem_hout {vs : List (List Bool)} {n S s0 s1 : ℕ} {F0 F1 : ℕ → ℕ → RM N K} {j : ℕ} :
    ∀ y ∈ hout vs n S s0 s1 F0 F1 j, y.length = N * K := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact mem_outs0 y h
  · exact mem_outs1 y h

/-- **The helpers `j < S`.** -/
theorem exec_hOuterLoop (hK : 0 < K) (n S s0 s1 : ℕ) (vs : List (List Bool))
    (hvs : ∀ x ∈ vs, x.length = N * K) (hS : 1 ≤ S)
    (hl0 : ∀ j < S, ∀ i < n, s0 + j + i * S < vs.length)
    (hl1 : ∀ j < S, ∀ i < n, s1 + j + i * S < vs.length)
    (F0 F1 : ℕ → ℕ → RM N K) (w : St) (LB b₀ : List Bool) (ys₀ : List (List Bool))
    (hys₀ : ∀ y ∈ ys₀, y.length = N * K) (hJ : (w cntJ).length = S) (hc : (w cK).length = n)
    (hT0 : w rS0 = (vs.drop s0).flatten) (hT1 : w rS1 = (vs.drop s1).flatten)
    (hSk : (w cSkip).length = (S - 1) * (N * K))
    (hH : w rH2 = ((List.range S).map (hblk n F0 F1)).flatten ++ LB)
    (hO : w xOut = bufW (N * K) b₀ ys₀)
    (hG : (w r1).length = N * K) (hG1 : decRM N K (w r1) = 1)
    (hNK : (w xCNK).length = N * K) (hv : (w xv).length = N * K) (hf : (w xf).length = N * K) :
    exec N K (.rep cntJ hOuter) w rH2 = LB ∧
      exec N K (.rep cntJ hOuter) w xOut = bufW (N * K) b₀
        (ys₀ ++ ((List.range S).map (hout vs n S s0 s1 F0 F1)).flatten) ∧
      (exec N K (.rep cntJ hOuter) w xv).length = N * K ∧
      (exec N K (.rep cntJ hOuter) w xf).length = N * K ∧
      ∀ j, j ∉ cntJ :: hOW → exec N K (.rep cntJ hOuter) w j = w j := by
  have hcw : cntJ ∉ wr hOuter := by decide
  let P : ℕ → St → Prop := fun j w' =>
    w' rS0 = (vs.drop (s0 + j)).flatten ∧ w' rS1 = (vs.drop (s1 + j)).flatten ∧
    w' rH2 = (((List.range S).drop j).map (hblk n F0 F1)).flatten ++ LB ∧
    w' xOut = bufW (N * K) b₀ (ys₀ ++ (((List.range S).take j).map
      (hout vs n S s0 s1 F0 F1)).flatten) ∧
    (w' xv).length = N * K ∧ (w' xf).length = N * K ∧
    ∀ j, j ∉ cntJ :: hOW → w' j = w j
  have key := exec_rep_inv (N := N) (K := K) cntJ hOuter hcw P w
    ⟨by simpa using hT0, by simpa using hT1, by simpa using hH, by simpa using hO, hv, hf,
      fun _ _ => rfl⟩
    (fun j hj w' hP _ => by
      rw [hJ] at hj
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
      have hu : ∀ i, i ≠ cntJ → Function.update w' cntJ (w' cntJ).tail i = w' i :=
        fun i hi => Function.update_of_ne hi _ _
      have hd : ((List.range S).drop j).map (hblk n F0 F1) =
          hblk n F0 F1 j :: ((List.range S).drop (j + 1)).map (hblk n F0 F1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hj), List.getElem_range, List.map_cons]
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := exec_hOuter hK n S (s0 + j) (s1 + j) vs hvs hS
        (hl0 j hj) (hl1 j hj) (F0 j) (F1 j) (Function.update w' cntJ (w' cntJ).tail)
        ((((List.range S).drop (j + 1)).map (hblk n F0 F1)).flatten ++ LB) b₀
        (ys₀ ++ (((List.range S).take j).map (hout vs n S s0 s1 F0 F1)).flatten)
        (fun y hy => by
          rcases List.mem_append.mp hy with h | h
          · exact hys₀ y h
          · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp h
            obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
            exact mem_hout (j := a) y hyl)
        (by rw [hu _ (by decide), h7 _ (by decide), hc]) (by rw [hu _ (by decide), h1])
        (by rw [hu _ (by decide), h2]) (by rw [hu _ (by decide), h7 _ (by decide), hSk])
        (by rw [hu _ (by decide), h3, hd, List.flatten_cons, hblk, List.append_assoc,
          List.append_assoc])
        (by rw [hu _ (by decide), h4])
        (by rw [hu _ (by decide), h7 _ (by decide), hG])
        (by rw [hu _ (by decide), h7 _ (by decide), hG1])
        (by rw [hu _ (by decide), h7 _ (by decide), hNK])
        (by rw [hu _ (by decide), h5]) (by rw [hu _ (by decide), h6])
      rw [Nat.add_assoc] at r1 r2
      refine ⟨r1, r2, r3, ?_, r5, r6, ?_⟩
      · rw [r4, take_succ_of_lt (by simpa using hj), List.getElem_range, List.map_append,
          List.flatten_append, List.map_singleton, List.flatten_singleton]
        simp only [hout, List.append_assoc]
      · intro i hi
        have hi' : i ∉ hOW := fun h => hi (List.mem_cons_of_mem _ h)
        have hic : i ≠ cntJ := fun h => hi (h ▸ List.mem_cons_self)
        rw [r7 i hi', hu i hic, h7 i hi])
  rw [hJ] at key
  obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := key
  refine ⟨?_, ?_, h5, h6, h7⟩
  · rw [h3, show (List.range S).drop S = [] by simp]; rfl
  · rw [h4, show (List.range S).take S = List.range S by simp]

end AdvancedEncryption.ExpLUT.Prog.RedChal
