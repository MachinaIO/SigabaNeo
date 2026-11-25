import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMVec

/-!
# Products with `G⁻¹` on the ring-word machine

With the digit dot product `ddot(v, m₀, m₁) = Σ_{i<K} v_i d_i(m₀) + Σ_{i<K} v_{K+i} d_i(m₁)`
(`ddotV`, `exec_ddotC`) and a matrix `M` of `2 × 2K` ring words (row-major, `4K` words):

* `vecGinvC`: `92 := v G⁻¹(M)`, entry `col` is `ddot(v, M_{0,col}, M_{1,col})` for the vector `v`
  (`2K` words, register `90`) and `M` (register `91`) (**`exec_vecGinvC`**); scratch `93 … 95`.
-/

namespace SigabaNeo.Tape

namespace RingVM

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {N K : ℕ} [NeZero (2 ^ K - 1)]

/-- The value of the digit dot product. -/
noncomputable def ddotV (vs : List (List Bool)) (m₀ m₁ : List Bool) : RM N K :=
  dotRow vs 0 (opd N K m₀) K + dotRow vs K (opd N K m₁) K

theorem flatten_drop_mul {L : List (List Bool)} {m : ℕ} (hL : ∀ y ∈ L, y.length = m) :
    ∀ n, L.flatten.drop (n * m) = (L.drop n).flatten := by
  induction L with
  | nil => intro n; simp
  | cons x L ih =>
    intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [List.flatten_cons, Nat.succ_mul, Nat.add_comm, ← List.drop_drop,
        List.drop_left' (hL x (by simp)), ih (fun y hy => hL y (by simp [hy])) n]
      rfl

theorem exec_drop' {t c : Fin 200} (h : t ≠ c) (w : St) :
    exec N K (.drop t c) w = Function.update w t ((w t).drop (w c).length) := by
  simp [exec, h]

/-! ### `v G⁻¹(M)` -/

/-- One column: pop `M_{0,col}`, `M_{1,col}`, the dot product, push. -/
def vgBody : Code := ofList [.mv 81 93 2, .mv 82 94 2, ddotC, .mv 92 83 2]

/-- **`92 := v G⁻¹(M)`.** -/
def vecGinvC : Code :=
  ofList [.cp 93 91, .cp 94 91, .drop 94 6, .cp 92 6, .cp 80 90, .cp 81 2, .cp 82 2, .cp 95 8,
    .rep 95 vgBody]

theorem wr_vgBody : wr vgBody = [81, 93, 82, 94] ++ wr ddotC ++ [92, 83] := by
  simp [vgBody, wr, wr_ofList]

theorem wr_vecGinvC : wr vecGinvC = [93, 94, 94, 92, 80, 81, 82, 95, 95] ++ wr vgBody := by
  simp [vecGinvC, wr, wr_ofList]

/-- **`v G⁻¹(M)`**: the entries of the result are the digit dot products with the columns. -/
theorem exec_vecGinvC (hK : 0 < K) (w : St) (hc : Consts N K w)
    (h6 : w 6 = List.replicate (2 * K * (N * K)) false) (h8 : w 8 = List.replicate (2 * K) false)
    {vs ms : List (List Bool)} (hvs : ∀ x ∈ vs, x.length = N * K) (hvl : vs.length = 2 * K)
    (hms : ∀ x ∈ ms, x.length = N * K) (hml : ms.length = 4 * K)
    (h90 : w 90 = vs.flatten) (h91 : w 91 = ms.flatten) :
    ∃ os : List (List Bool), (exec N K vecGinvC w) 92 = os.flatten ∧ os.length = 2 * K ∧
      (∀ x ∈ os, x.length = N * K) ∧
      (∀ c < 2 * K, decRM N K (os.getD c []) =
        ddotV vs (ms.getD c []) (ms.getD (2 * K + c) [])) ∧
      ∀ j, j ∉ wr vecGinvC → (exec N K vecGinvC w) j = w j := by
  set w1 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update w 93 ms.flatten) 94 (ms.drop (2 * K)).flatten) 92
    (List.replicate (2 * K * (N * K)) false)) 80 vs.flatten) 81 (List.replicate (N * K) false)) 82
    (List.replicate (N * K) false)) 95 (List.replicate (2 * K) false) with hw1
  have e : exec N K vecGinvC w = exec N K (.rep 95 vgBody) w1 := by
    simp only [vecGinvC, exec_ofList_cons, exec_ofList_nil]
    rw [show exec N K (.cp 93 91) w = Function.update w 93 ms.flatten by simp [exec, h91]]
    rw [show exec N K (.cp 94 91) (Function.update w 93 ms.flatten) =
      Function.update (Function.update w 93 ms.flatten) 94 ms.flatten by simp [exec, h91]]
    rw [exec_drop' (by decide)]
    simp only [Function.update_self, Function.update_of_ne (show (6 : Fin 200) ≠ 94 by decide),
      Function.update_of_ne (show (6 : Fin 200) ≠ 93 by decide), h6, List.length_replicate,
      Function.update_idem]
    rw [flatten_drop_mul hms (2 * K)]
    simp only [exec, Function.update_of_ne (show (6 : Fin 200) ≠ 94 by decide),
      Function.update_of_ne (show (6 : Fin 200) ≠ 93 by decide), Function.update_apply,
      Fin.reduceEq, ↓reduceIte, h6, h90, hc.zero, h8, hw1]
  have h95 : (w1 95).length = 2 * K := by simp [hw1]
  let P : ℕ → St → Prop := fun i w' =>
    Consts N K w' ∧ w' 80 = vs.flatten ∧ w' 93 = (ms.drop i).flatten ∧
      w' 94 = (ms.drop (2 * K + i)).flatten ∧ (w' 81).length = N * K ∧ (w' 82).length = N * K ∧
      (∃ os : List (List Bool), os.length = i ∧ (∀ x ∈ os, x.length = N * K) ∧
        (∀ c < i, decRM N K (os.getD c []) = ddotV vs (ms.getD c []) (ms.getD (2 * K + c) [])) ∧
        w' 92 = (List.replicate (2 * K * (N * K)) false ++ os.flatten).drop (i * (N * K))) ∧
      ∀ j, j ∉ wr vecGinvC → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 95 vgBody (by rw [wr_vgBody]; decide) P w1
    ⟨consts_exec hc (ofList [.cp 93 91, .cp 94 91, .drop 94 6, .cp 92 6, .cp 80 90, .cp 81 2,
        .cp 82 2, .cp 95 8]) rfl |> fun h => by
          simpa [hw1] using consts_update (consts_update (consts_update (consts_update
            (consts_update (consts_update (consts_update hc 93 (by decide) _) 94 (by decide) _) 92
            (by decide) _) 80 (by decide) _) 81 (by decide) _) 82 (by decide) _) 95 (by decide) _,
      by simp [hw1], by simp [hw1], by simp [hw1], by simp [hw1], by simp [hw1],
      ⟨[], rfl, by simp, fun c hc => absurd hc (Nat.not_lt_zero _), by simp [hw1]⟩,
      fun j hj => by
        have hm : ∀ r : Fin 200, r ∈ [93, 94, 92, 80, 81, 82, 95] → j ≠ r := fun r hr h =>
          hj (by rw [h, wr_vecGinvC]; simp at hr ⊢; rcases hr with h | h | h | h | h | h | h <;>
            simp [h])
        simp only [hw1, Function.update_apply]
        rw [if_neg (hm 95 (by simp)), if_neg (hm 82 (by simp)), if_neg (hm 81 (by simp)),
          if_neg (hm 80 (by simp)), if_neg (hm 92 (by simp)), if_neg (hm 94 (by simp)),
          if_neg (hm 93 (by simp))]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨hc', p80, p93, p94, p81, p82, ⟨os, hol, how, hov, p92⟩, pf⟩ := hw'
      rw [h95] at hi
      have hi1 : i < ms.length := by omega
      have hi2 : 2 * K + i < ms.length := by omega
      set s := Function.update w' 95 (w' 95).tail with hs
      have hsc : Consts N K s := consts_update hc' 95 (by decide) _
      set m0 := ms.getD i [] with hm0
      set m1 := ms.getD (2 * K + i) [] with hm1
      have hm0l : m0.length = N * K := hms _ (mem_getD hi1)
      have hm1l : m1.length = N * K := hms _ (mem_getD hi2)
      have s1 := exec_mv_pop (N := N) (K := K) (d := 81) (s := 93) (c := 2) (w := s) (by decide)
        (v := m0) (L := (ms.drop (i + 1)).flatten)
        (by rw [hsc.zero]; simp [hs, p81]) (by rw [hsc.zero, List.length_replicate]; exact hm0l)
        (by simp only [hs, Function.update_of_ne (show (93 : Fin 200) ≠ 95 by decide), p93]
            exact flatten_drop_succ hi1)
      set s1' := Function.update (Function.update s 93 (ms.drop (i + 1)).flatten) 81 m0
      have hs1c : Consts N K s1' :=
        consts_update (consts_update hsc 93 (by decide) _) 81 (by decide) _
      have s2 := exec_mv_pop (N := N) (K := K) (d := 82) (s := 94) (c := 2) (w := s1') (by decide)
        (v := m1) (L := (ms.drop (2 * K + i + 1)).flatten)
        (by rw [hs1c.zero]; simp [s1', hs, p82]) (by rw [hs1c.zero, List.length_replicate]; exact hm1l)
        (by simp only [s1', hs, Function.update_of_ne (show (94 : Fin 200) ≠ 95 by decide),
              Function.update_of_ne (show (94 : Fin 200) ≠ 93 by decide),
              Function.update_of_ne (show (94 : Fin 200) ≠ 81 by decide), p94]
            exact flatten_drop_succ hi2)
      set s2' := Function.update (Function.update s1' 94 (ms.drop (2 * K + i + 1)).flatten) 82 m1
      have hs2c : Consts N K s2' :=
        consts_update (consts_update hs1c 94 (by decide) _) 82 (by decide) _
      have a80 : s2' 80 = vs.flatten := by
        simp only [s2', s1', hs, Function.update_apply, Fin.reduceEq, ↓reduceIte]; exact p80
      obtain ⟨d83, dv, df⟩ := exec_ddotC hK s2' hs2c hvs hvl a80
      set s3 := exec N K ddotC s2'
      have a81 : s2' 81 = m0 := by simp only [s2', s1', Function.update_apply, Fin.reduceEq, ↓reduceIte]
      have a82 : s2' 82 = m1 := by simp only [s2', Function.update_apply, Fin.reduceEq, ↓reduceIte]
      have hs3c : Consts N K s3 := consts_exec hs2c _ rfl
      have s4 := exec_mv_push (N := N) (K := K) (d := 92) (s := 83) (c := 2) (w := s3) (by decide)
        (by rw [hs3c.zero, List.length_replicate]; exact d83)
      have ee : exec N K vgBody s = Function.update (Function.update s3 83 []) 92
          ((s3 92 ++ s3 83).drop (s3 2).length) := by
        simp only [vgBody, exec_ofList_cons, exec_ofList_nil]
        rw [s1, s2, s4]
      rw [ee]
      have nd : ∀ r : Fin 200, r ∉ wr ddotC → s3 r = s2' r := fun r hr => df r hr
      have b92 : s3 92 = w' 92 := by
        rw [nd 92 (by rw [wr_ddotC]; decide)]
        simp only [s2', s1', hs, Function.update_apply, Fin.reduceEq, ↓reduceIte]
      refine ⟨consts_update (consts_update hs3c 83 (by decide) _) 92 (by decide) _, ?_, ?_, ?_, ?_,
        ?_, ⟨os ++ [s3 83], by simp [hol], ?_, ?_, ?_⟩, fun j hj => ?_⟩
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [nd 80 (by rw [wr_ddotC]; decide)]; exact a80
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [nd 93 (by rw [wr_ddotC]; decide)]
        simp [s2', s1']
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [nd 94 (by rw [wr_ddotC]; decide)]
        simp [s2', Nat.add_assoc]
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [nd 81 (by rw [wr_ddotC]; decide), a81]; exact hm0l
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [nd 82 (by rw [wr_ddotC]; decide), a82]; exact hm1l
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact how x hx
        · rw [List.mem_singleton.mp hx]; exact d83
      · intro c hc
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | hc
        · rw [List.getD_append _ _ _ _ (by omega)]; exact hov c hc
        · subst hc
          rw [List.getD_append_right _ _ _ _ (by omega), hol, Nat.sub_self]
          simp only [List.getD_cons_zero]
          rw [dv, a81, a82]; rfl
      · rw [Function.update_self, b92, p92, hs3c.zero, List.length_replicate]
        have := drop_append_flatten_succ (b := List.replicate (2 * K * (N * K)) false) (vs := os)
          d83 how
        rw [hol] at this
        rw [this, List.length_append, hol, List.length_singleton]
      · have hjb : j ∉ wr vgBody := fun hm => hj (by rw [wr_vecGinvC]; simp [hm])
        rw [wr_vgBody] at hjb
        simp only [List.mem_append, not_or] at hjb
        have hjd : j ∉ wr ddotC := hjb.1.2
        have hne : ∀ r : Fin 200, r ∈ [81, 93, 82, 94, 92, 83, 95] → j ≠ r := by
          intro r hr h
          subst h
          apply hj
          rw [wr_vecGinvC, wr_vgBody]
          simp at hr ⊢
          rcases hr with h | h | h | h | h | h | h <;> simp [h]
        simp only [Function.update_apply]
        rw [if_neg (hne 92 (by simp)), if_neg (hne 83 (by simp)), nd j hjd]
        simp only [s2', s1', hs, Function.update_apply]
        rw [if_neg (hne 82 (by simp)), if_neg (hne 94 (by simp)), if_neg (hne 81 (by simp)),
          if_neg (hne 93 (by simp)), if_neg (hne 95 (by simp))]
        exact pf j hj)
  rw [h95] at hP
  obtain ⟨_, _, _, _, _, _, ⟨os, hol, how, hov, p92⟩, pf⟩ := hP
  refine ⟨os, ?_, hol, how, hov, fun j hj => by rw [e]; exact pf j hj⟩
  rw [e, p92, ← hol, drop_append_flatten (by rw [hol, List.length_replicate])]

theorem not_mem_wr_vecGinvC {j : Fin 200} (h : j ∈ [2, 4, 6, 7, 8, 9, 10, 56, 90, 91, 96, 97, 98, 99,
    100, 101, 102, 103, 104, 105, 106, 107, 108, 109]) : j ∉ wr vecGinvC := by
  rw [wr_vecGinvC, wr_vgBody, wr_ddotC]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h <;> subst h <;> decide

/-! ### `V G⁻¹(M)` for a matrix `V` -/

/-- **`102 := V G⁻¹(M)`** for the matrix `V` (`2 × 2K`, register `100`): its two rows, each
`vecGinvC`. Scratch `101`. -/
def matGinvC : Code :=
  ofList [.cp 101 100, .cp 102 7, .cp 90 6, .mv 90 101 6, vecGinvC, .mv 102 92 6, .mv 90 101 6,
    vecGinvC, .mv 102 92 6]

theorem wr_matGinvC : wr matGinvC =
    [101, 102, 90, 90, 101] ++ wr vecGinvC ++ [102, 92, 90, 101] ++ wr vecGinvC ++ [102, 92] := by
  simp [matGinvC, wr, wr_ofList]

/-- The rows of `V G⁻¹(M)`. -/
def GinvRow (vs ms os : List (List Bool)) : Prop :=
  os.length = 2 * K ∧ (∀ x ∈ os, x.length = N * K) ∧
    ∀ c < 2 * K, decRM N K (os.getD c []) = ddotV (N := N) vs (ms.getD c []) (ms.getD (2 * K + c) [])

theorem exec_matGinvC (hK : 0 < K) (w : St) (hc : Consts N K w)
    (h6 : w 6 = List.replicate (2 * K * (N * K)) false)
    (h7 : w 7 = List.replicate (4 * K * (N * K)) false) (h8 : w 8 = List.replicate (2 * K) false)
    {vs₀ vs₁ ms : List (List Bool)} (hv₀ : ∀ x ∈ vs₀, x.length = N * K) (hl₀ : vs₀.length = 2 * K)
    (hv₁ : ∀ x ∈ vs₁, x.length = N * K) (hl₁ : vs₁.length = 2 * K)
    (hms : ∀ x ∈ ms, x.length = N * K) (hml : ms.length = 4 * K)
    (h100 : w 100 = vs₀.flatten ++ vs₁.flatten) (h91 : w 91 = ms.flatten) :
    ∃ os₀ os₁ : List (List Bool), (exec N K matGinvC w) 102 = os₀.flatten ++ os₁.flatten ∧
      GinvRow (N := N) (K := K) vs₀ ms os₀ ∧ GinvRow (N := N) (K := K) vs₁ ms os₁ ∧
      ∀ j, j ∉ wr matGinvC → (exec N K matGinvC w) j = w j := by
  have lv₀ : vs₀.flatten.length = 2 * K * (N * K) := by rw [length_flatten_of hv₀, hl₀]
  have lv₁ : vs₁.flatten.length = 2 * K * (N * K) := by rw [length_flatten_of hv₁, hl₁]
  set w1 := Function.update (Function.update (Function.update w 101
    vs₁.flatten) 102 (List.replicate (4 * K * (N * K)) false)) 90 vs₀.flatten with hw1
  have e1 : exec N K (ofList [.cp 101 100, .cp 102 7, .cp 90 6, .mv 90 101 6]) w = w1 := by
    simp only [exec_ofList_cons, exec_ofList_nil]
    set u1 := Function.update w 101 (vs₀.flatten ++ vs₁.flatten) with hu1
    have s1 : exec N K (.cp 101 100) w = u1 := by simp [exec, h100, hu1]
    set u2 := Function.update u1 102 (List.replicate (4 * K * (N * K)) false) with hu2
    have s2 : exec N K (.cp 102 7) u1 = u2 := by simp [exec, hu1, hu2, h7]
    set u3 := Function.update u2 90 (List.replicate (2 * K * (N * K)) false) with hu3
    have s3 : exec N K (.cp 90 6) u2 = u3 := by simp [exec, hu1, hu2, hu3, h6]
    have s4 := exec_mv_pop (N := N) (K := K) (d := 90) (s := 101) (c := 6) (w := u3) (by decide)
      (v := vs₀.flatten) (L := vs₁.flatten) (by simp [hu3, hu2, hu1, h6])
      (by simp [hu3, hu2, hu1, h6, lv₀]) (by simp [hu3, hu2, hu1])
    rw [s1, s2, s3, s4, hw1]
    funext t
    simp only [hu3, hu2, hu1, Function.update_apply]
    split_ifs <;> simp_all
  have hc1 : Consts N K w1 :=
    consts_update (consts_update (consts_update hc 101 (by decide) _) 102 (by decide) _) 90
      (by decide) _
  have f1 : ∀ r : Fin 200, r ∉ ([101, 102, 90] : List (Fin 200)) → w1 r = w r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hw1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2]
  obtain ⟨os₀, a92, al, aw, av, af⟩ := exec_vecGinvC hK w1 hc1 (by rw [f1 6 (by decide), h6])
    (by rw [f1 8 (by decide), h8]) hv₀ hl₀ hms hml (by simp [hw1]) (by rw [f1 91 (by decide), h91])
  set w2 := exec N K vecGinvC w1
  have hc2 : Consts N K w2 := consts_exec hc1 _ rfl
  have f2 : ∀ r : Fin 200, r ∈ [2, 4, 6, 7, 8, 9, 10, 56, 90, 91, 96, 97, 98, 99, 100, 101, 102, 103,
      104, 105, 106, 107, 108, 109] → w2 r = w1 r := fun r hr => af r (not_mem_wr_vecGinvC hr)
  have lo₀ : os₀.flatten.length = 2 * K * (N * K) := by rw [length_flatten_of aw, al]
  have p1 := exec_mv_push (N := N) (K := K) (d := 102) (s := 92) (c := 6) (w := w2) (by decide)
    (by rw [a92, f2 6 (by simp), f1 6 (by decide), h6, lo₀, List.length_replicate])
  set w3 := Function.update (Function.update w2 92 []) 102 ((w2 102 ++ w2 92).drop (w2 6).length)
  have hc3 : Consts N K w3 := consts_update (consts_update hc2 92 (by decide) _) 102 (by decide) _
  have p2 := exec_mv_pop (N := N) (K := K) (d := 90) (s := 101) (c := 6) (w := w3) (by decide)
    (v := vs₁.flatten) (L := [])
    (by simp [w3, f2 90 (by simp), f2 6 (by simp), f1 6 (by decide), h6, hw1, lv₀])
    (by simp [w3, f2 6 (by simp), f1 6 (by decide), h6, lv₁])
    (by simp [w3, f2 101 (by simp), hw1])
  set w4 := Function.update (Function.update w3 101 []) 90 vs₁.flatten
  have hc4 : Consts N K w4 := consts_update (consts_update hc3 101 (by decide) _) 90 (by decide) _
  have g4 : ∀ r : Fin 200, r ∉ ([92, 102, 101, 90] : List (Fin 200)) → w4 r = w2 r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [w4, w3, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
      Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
  obtain ⟨os₁, b92, bl, bw, bv, bf⟩ := exec_vecGinvC hK w4 hc4
    (by rw [g4 6 (by decide), f2 6 (by simp), f1 6 (by decide), h6])
    (by rw [g4 8 (by decide), f2 8 (by simp), f1 8 (by decide), h8]) hv₁ hl₁ hms hml
    (by simp [w4]) (by rw [g4 91 (by decide), f2 91 (by simp), f1 91 (by decide), h91])
  set w5 := exec N K vecGinvC w4
  have hc5 : Consts N K w5 := consts_exec hc4 _ rfl
  have f5 : ∀ r : Fin 200, r ∈ [2, 4, 6, 7, 8, 9, 10, 56, 90, 91, 96, 97, 98, 99, 100, 101, 102, 103,
      104, 105, 106, 107, 108, 109] → w5 r = w4 r := fun r hr => bf r (not_mem_wr_vecGinvC hr)
  have lo₁ : os₁.flatten.length = 2 * K * (N * K) := by rw [length_flatten_of bw, bl]
  have p3 := exec_mv_push (N := N) (K := K) (d := 102) (s := 92) (c := 6) (w := w5) (by decide)
    (by rw [b92, f5 6 (by simp), g4 6 (by decide), f2 6 (by simp), f1 6 (by decide), h6, lo₁,
      List.length_replicate])
  have e : exec N K matGinvC w = Function.update (Function.update w5 92 []) 102
      ((w5 102 ++ w5 92).drop (w5 6).length) := by
    have : matGinvC = ofList ([.cp 101 100, .cp 102 7, .cp 90 6, .mv 90 101 6] ++
        [vecGinvC, .mv 102 92 6, .mv 90 101 6, vecGinvC, .mv 102 92 6]) := rfl
    rw [this, exec_ofList_append, e1]
    simp only [exec_ofList_cons, exec_ofList_nil]
    rw [p1, p2, p3]
  have w6v : w5 6 = List.replicate (2 * K * (N * K)) false := by
    rw [f5 6 (by simp), g4 6 (by decide), f2 6 (by simp), f1 6 (by decide), h6]
  refine ⟨os₀, os₁, ?_, ⟨al, aw, av⟩, ⟨bl, bw, bv⟩, fun j hj => ?_⟩
  · have q102 : w5 102 = (List.replicate (4 * K * (N * K)) false ++ os₀.flatten).drop
        (2 * K * (N * K)) := by
      rw [f5 102 (by simp), show w4 102 = (w2 102 ++ w2 92).drop (w2 6).length by simp [w4, w3],
        f2 102 (by simp), a92, f2 6 (by simp), f1 6 (by decide), h6, List.length_replicate]
      simp [hw1]
    rw [e, Function.update_self, b92, w6v, List.length_replicate, q102,
      show 4 * K * (N * K) = 2 * K * (N * K) + 2 * K * (N * K) by ring,
      ← List.replicate_append_replicate, List.append_assoc,
      List.drop_left' (l₁ := List.replicate (2 * K * (N * K)) false) (by simp),
      List.append_assoc, List.drop_left' (l₁ := List.replicate (2 * K * (N * K)) false) (by simp)]
  · have hm : ∀ r ∈ wr matGinvC, j ≠ r := fun r hr h => hj (h ▸ hr)
    have hv : j ∉ wr vecGinvC := fun h => hj (by rw [wr_matGinvC]; simp [h])
    have h92 : j ≠ 92 := hm 92 (by rw [wr_matGinvC]; simp)
    have h102 : j ≠ 102 := hm 102 (by rw [wr_matGinvC]; simp)
    have h101 : j ≠ 101 := hm 101 (by rw [wr_matGinvC]; simp)
    have h90 : j ≠ 90 := hm 90 (by rw [wr_matGinvC]; simp)
    rw [e, Function.update_of_ne h102, Function.update_of_ne h92, bf j hv]
    simp only [w4, w3, Function.update_of_ne h102, Function.update_of_ne h92,
      Function.update_of_ne h101, Function.update_of_ne h90]
    rw [af j hv]
    simp [hw1, Function.update_of_ne h102, Function.update_of_ne h101, Function.update_of_ne h90]

end RingVM

end SigabaNeo.Tape
