import SigabaNeoStd.Lattices.ProgAlgo.FhatGenCoef

/-!
# Generating gate tapes: a NAND block

`blockC`: one `coefC` per output position `o` of `enumO` (held in the registers `43 … 46`,
advanced by the odometer `odoO`), appending its `k` wires to the list `21`; the list is then the
representation list (`repList`) of the block's output (`exec_blockC`: it is `nandBlockL`).
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-! ### Lengths -/

theorem foldl_modAdd_length {k K : ℕ} : ∀ (L : List (List (Wire ι))) (st : SLP ι × List (Wire ι)),
    st.2.length = k → (∀ a ∈ L, a.length = k) →
    (L.foldl (fun st b => modAdd (.gate 0) (2 ^ K) k st.1 st.2 b) st).2.length = k
  | [], st, h, _ => h
  | b :: L, st, h, hL => foldl_modAdd_length L _ (length_modAdd_eq _ _ _ _ _ _ h (hL b (by simp)))
      (fun x hx => hL x (by simp [hx]))

theorem foldSum_length {k K : ℕ} (P : SLP ι) (L : List (List (Wire ι)))
    (hL : ∀ a ∈ L, a.length = k) : (foldSum (.gate 0) (2 ^ K) k P L).2.length = k := by
  rcases L with _ | ⟨a, L⟩
  · simp [foldSum, constL_length]
  · exact foldl_modAdd_length L (P, a) (hL a (by simp)) (fun x hx => hL x (by simp [hx]))

theorem rounds_lengths {k K : ℕ} : ∀ (h : ℕ) (P : SLP ι) (L : List (List (Wire ι))),
    (∀ a ∈ L, a.length = k) → ∀ x ∈ (rounds (.gate 0) (2 ^ K) k h P L).2, x.length = k
  | 0, P, L, hL => hL
  | h + 1, P, L, hL => rounds_lengths h _ _ (pairRound_lengths P L hL)

theorem coefCircuitL_length {N k K : ℕ} (repA repB : BI N k → Wire ι) (Gv : ℕ) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (P : SLP ι) :
    (coefCircuitL (ordT₀ N k) (.gate 0) (2 ^ K) repA repB Gv a col t P).2.length = k := by
  unfold coefCircuitL
  apply foldSum_length
  apply rounds_lengths
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact constL_length _ _ _
  · exact (leaves_lengths (K := K) repA repB a col t P (ordT₀ N k)).1 x hx

/-! ### The odometer of the output positions -/

/-- The odometer of `(a, (c1, c2), t)` in `43 … 46` (moduli `2 = 6`, `2 = 6`, `k = 2`, `N = 5`). -/
def odoO : Code := .seq (.inc 46) (.ifLt 46 5 .skip (.seq (.zero 46) (.seq (.inc 45)
  (.ifLt 45 2 .skip (.seq (.zero 45) (.seq (.inc 44) (.ifLt 44 6 .skip (.seq (.zero 44)
    (.inc 43)))))))))

theorem exec_odoO {N k : ℕ} (σ : St) (a c1 c2 t : ℕ) (h2 : σ.sc 2 = k) (h5 : σ.sc 5 = N)
    (h6 : σ.sc 6 = 2) (h43 : σ.sc 43 = a) (h44 : σ.sc 44 = c1) (h45 : σ.sc 45 = c2)
    (h46 : σ.sc 46 = t) (hc1 : c1 < 2) (hc2 : c2 < k) (ht : t < N)
    (hM : a + 1 ≤ E.M) (hkM : k ≤ E.M) (hNM : N ≤ E.M) (h2M : 2 ≤ E.M) :
    ∃ a' c1' c2' t', exec E odoO σ = setSL σ (Function.update (Function.update (Function.update
        (Function.update σ.sc 43 a') 44 c1') 45 c2') 46 t') σ.ls ∧
      ((a' * 2 + c1') * k + c2') * N + t' = ((a * 2 + c1) * k + c2) * N + t + 1 ∧
      c1' < 2 ∧ c2' < k ∧ t' < N := by
  have upd : ∀ (f : SR → ℕ) (x y z w : ℕ), Function.update (Function.update (Function.update
      (Function.update f 43 x) 44 y) 45 z) 46 w = fun r => if r = 46 then w else if r = 45 then z
        else if r = 44 then y else if r = 43 then x else f r := by
    intro f x y z w; funext r; simp only [Function.update_apply]
  by_cases ht' : t + 1 < N
  · refine ⟨a, c1, c2, t + 1, ?_, by ring, hc1, hc2, ht'⟩
    simp only [odoC, odoO, exec_seq, exec_ifLt]
    simp [exec, h46, h5, min_eq_left (show t + 1 ≤ E.M by omega), ht', setSL, upd, h43, h44, h45]
    funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
  · have eN : N = t + 1 := by omega
    by_cases hc2' : c2 + 1 < k
    · refine ⟨a, c1, c2 + 1, 0, ?_, by subst eN; ring, hc1, hc2', by omega⟩
      simp only [odoO, exec_seq, exec_ifLt]
      simp [exec, h46, h5, h45, h2, min_eq_left (show t + 1 ≤ E.M by omega),
        min_eq_left (show c2 + 1 ≤ E.M by omega), ht', hc2', setSL, h43, h44]
      funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
    · have ek : k = c2 + 1 := by omega
      by_cases hc1' : c1 + 1 < 2
      · refine ⟨a, c1 + 1, 0, 0, ?_, by subst eN; subst ek; ring, hc1', by omega, by omega⟩
        simp only [odoO, exec_seq, exec_ifLt]
        simp [exec, h46, h5, h45, h2, h44, h6, min_eq_left (show t + 1 ≤ E.M by omega),
          min_eq_left (show c2 + 1 ≤ E.M by omega), min_eq_left (show c1 + 1 ≤ E.M by omega),
          ht', hc2', hc1', setSL, h43]
        funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
      · have e2 : c1 = 1 := by omega
        refine ⟨a + 1, 0, 0, 0, ?_, by subst eN; subst ek; subst e2; ring, by omega, by omega,
          by omega⟩
        subst e2
        simp only [odoO, exec_seq, exec_ifLt]
        simp [exec, h46, h5, h45, h2, h44, h6, h43, min_eq_left (show t + 1 ≤ E.M by omega),
          min_eq_left (show c2 + 1 ≤ E.M by omega), min_eq_left (show 1 + 1 ≤ E.M by omega),
          min_eq_left hM, ht', hc2', setSL]
        funext r; simp only [Function.update_apply]; split_ifs <;> simp_all

/-! ### The loop over the output positions -/

/-- One output position: `coefC`, append the coefficient to `21`, advance the odometer. -/
def blockBody : Code := .seq coefC (.seq (takeC 2 16 21) odoO)

/-- The state of the NAND block after the first `i` output positions. -/
def bst {N k K : ℕ} (repA repB : BI N k → Wire ι) (P : SLP ι) (i : ℕ) :
    SLP ι × (OI N k → List (Wire ι)) :=
  ((enumO N k).take i).foldl (blockStepL (ordT₀ N k) (gvExp (2 ^ K)) (.gate 0) (2 ^ K) repA repB)
    (P, fun _ => [])

/-- The list of the coefficients of the first `i` output positions. -/
def bList {N k K : ℕ} (repA repB : BI N k → Wire ι) (P : SLP ι) (i : ℕ) : List ℕ :=
  (((enumO N k).take i).map fun o => ((bst (K := K) repA repB P i).2 o).map (pos E ix)).flatten

theorem bst_succ {N k K : ℕ} (repA repB : BI N k → Wire ι) (P : SLP ι) (i : ℕ) (o : OI N k)
    (ho : (enumO N k)[i]? = some o) :
    bst (K := K) repA repB P (i + 1) = blockStepL (ordT₀ N k) (gvExp (2 ^ K)) (.gate 0) (2 ^ K)
      repA repB (bst (K := K) repA repB P i) o := by
  simp only [bst, List.take_succ, ho, Option.toList_some, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

theorem bList_succ {N k K : ℕ} (repA repB : BI N k → Wire ι) (P : SLP ι) (i : ℕ) (o : OI N k)
    (ho : (enumO N k)[i]? = some o) :
    bList (E := E) (ix := ix) (K := K) repA repB P (i + 1) =
      bList (E := E) (ix := ix) (K := K) repA repB P i ++
        (coefCircuitL (ordT₀ N k) (.gate 0) (2 ^ K) repA repB (gvExp (2 ^ K) o) o.1 o.2.1 o.2.2
          (bst (K := K) repA repB P i).1).2.map (pos E ix) := by
  have hnd : ((enumO N k).take (i + 1)).Nodup := (nodup_enumO N k).sublist (List.take_sublist _ _)
  rw [List.take_succ, ho, Option.toList_some] at hnd
  have hno : o ∉ (enumO N k).take i := fun h => (List.nodup_append.mp hnd).2.2 o h o (by simp) rfl
  simp only [bList, bst_succ repA repB P i o ho, blockStepL, List.take_succ, ho,
    Option.toList_some, List.map_append, List.map_singleton, List.flatten_append,
    List.flatten_singleton, Function.update_self]
  congr 2
  apply List.map_congr_left; intro x hx
  rw [Function.update_of_ne (fun h => hno (by rw [← h]; exact hx))]

theorem length_bList {N k K : ℕ} (repA repB : BI N k → Wire ι) (P : SLP ι) :
    ∀ i, i ≤ 4 * k * N → (bList (E := E) (ix := ix) (K := K) repA repB P i).length = i * k
  | 0, _ => by simp [bList]
  | i + 1, hi => by
    obtain ⟨o, ho⟩ : ∃ o, (enumO N k)[i]? = some o :=
      ⟨(enumO N k)[i]'(by rw [length_enumO']; omega), List.getElem?_eq_getElem _⟩
    rw [bList_succ repA repB P i o ho, List.length_append, length_bList repA repB P i (by omega),
      List.length_map, coefCircuitL_length]
    ring

theorem le_length_coefCircuitL {N k : ℕ} (ordT : List ((Fin 2 × Fin k) × Fin N)) (z : Wire ι)
    (q : ℕ) (repA repB : BI N k → Wire ι) (Gv : ℕ) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N)
    (p : SLP ι) : p.length ≤ (coefCircuitL ordT z q repA repB Gv a col t p).1.length :=
  (le_length_leaves _ _ _ _ _ _ _ _ _).trans ((le_length_rounds _ _ _ _ _ _).trans
    (le_length_foldSum _ _ _ _ _))

theorem le_length_bst_succ {N k K : ℕ} (repA repB : BI N k → Wire ι) (P : SLP ι) (i : ℕ) :
    (bst (K := K) repA repB P i).1.length ≤ (bst (K := K) repA repB P (i + 1)).1.length := by
  rcases h : (enumO N k)[i]? with _ | o
  · simp only [bst, List.take_succ, h, Option.toList_none, List.append_nil]; exact le_rfl
  · rw [bst_succ repA repB P i o h]
    exact le_length_coefCircuitL _ _ _ _ _ _ _ _ _ _

theorem le_length_bst {N k K : ℕ} (repA repB : BI N k → Wire ι) (P : SLP ι) :
    ∀ i, P.length ≤ (bst (K := K) repA repB P i).1.length
  | 0 => by simp [bst]
  | i + 1 => (le_length_bst repA repB P i).trans (le_length_bst_succ repA repB P i)

set_option maxHeartbeats 4000000 in
theorem iter_blockBody (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n)
    {N k K : ℕ} (hk : 0 < k) (hN : 0 < N) (hK : K ≤ k + 1) (repA repB : BI N k → Wire ι)
    (P : SLP ι) (σ : St) (L0 : List ℕ) (hc : CstC (E := E) N k K σ) (hI : Inv E σ)
    (hS : ScOK E σ) (h43 : σ.sc 43 = 0) (h44 : σ.sc 44 = 0) (h45 : σ.sc 45 = 0)
    (h46 : σ.sc 46 = 0) (h10 : σ.ls 10 = repList E ix repA) (h11 : σ.ls 11 = repList E ix repB)
    (h21 : σ.ls 21 = L0) (hcap : (2 * k * N + 1) * k ≤ E.C) (hcap' : k + 3 ≤ E.C)
    (hcap21 : L0.length + 4 * k * N * k ≤ E.C) (hbig : 4 * k * N * k + 2 * N + k + 2 ≤ E.M) :
    ∀ i, i ≤ 4 * k * N → E.n + (bst (K := K) repA repB P i).1.length ≤ E.M →
      ∃ sc' ls', (exec E blockBody)^[i] (mk E ix P σ) =
          mk E ix (bst (K := K) repA repB P i).1 (setSL σ sc' ls') ∧
        ls' 21 = L0 ++ bList (E := E) (ix := ix) (K := K) repA repB P i ∧
        (∃ a c1 c2 t, sc' 43 = a ∧ sc' 44 = c1 ∧ sc' 45 = c2 ∧ sc' 46 = t ∧
          ((a * 2 + c1) * k + c2) * N + t = i ∧ c1 < 2 ∧ c2 < k ∧ t < N) ∧
        Inv E (setSL σ sc' ls') ∧ ScOK E (setSL σ sc' ls') ∧
        (∀ r : SR, r.val < 16 ∨ 58 < r.val → sc' r = σ.sc r) ∧
        (∀ l : LR, l = 10 ∨ l = 11 ∨ 21 < l.val → ls' l = σ.ls l)
  | 0, _, _ => ⟨σ.sc, σ.ls, by simp [setSL, bst], by simp [bList, h21],
      ⟨0, 0, 0, 0, h43, h44, h45, h46, by ring, by omega, hk, hN⟩, hI, hS, fun _ _ => rfl,
      fun _ _ => rfl⟩
  | i + 1, hi, hM => by
    have hnM' : E.n ≤ E.M := by omega
    rw [Function.iterate_succ_apply']
    obtain ⟨sc1, ls1, h1, d1, ⟨a, c1, c2, t, h43', h44', h45', h46', hidx, hc1, hc2, ht⟩, hI1, hS1,
      f1, g1⟩ := iter_blockBody hnM hWM hix hk hN hK repA repB P σ L0 hc hI hS h43 h44 h45 h46
        h10 h11 h21 hcap hcap' hcap21 hbig i (by omega)
        (le_trans (Nat.add_le_add_left (le_length_bst_succ _ _ _ _) _) hM)
    rw [h1]
    have ha : a < 2 := by
      by_contra h
      have : 4 * k * N ≤ ((a * 2 + c1) * k + c2) * N + t := by nlinarith
      omega
    set o : OI N k := (⟨a, ha⟩, (⟨c1, hc1⟩, ⟨c2, hc2⟩), ⟨t, ht⟩)
    have ho : (enumO N k)[i]? = some o := by rw [← hidx]; exact enumO_getElem? o
    obtain ⟨⟨⟨⟨hc0', hc1'⟩, hc2', hc3', hc4'⟩, hc5', hc6', hc7'⟩, hc8', hc9', hc11'⟩ := hc
    rw [blockBody, exec_seq, exec_seq]
    rw [bst_succ repA repB P i o ho] at hM
    -- the coefficient
    obtain ⟨sc2, ls2, h2, d2, f2, g2⟩ := exec_coefC hnM hWM hix hk hN hK repA repB o
      (bst (K := K) repA repB P i).1 (setSL σ sc1 ls1)
      ⟨⟨⟨⟨by show sc1 0 = _; rw [f1 0 (by decide), hc0'], by show sc1 1 = _; rw [f1 1 (by decide), hc1']⟩,
        by show sc1 2 = _; rw [f1 2 (by decide), hc2'], by show sc1 3 = _; rw [f1 3 (by decide), hc3'],
        by show sc1 4 = _; rw [f1 4 (by decide), hc4']⟩, by show sc1 5 = _; rw [f1 5 (by decide), hc5'],
        by show sc1 6 = _; rw [f1 6 (by decide), hc6'], by show sc1 7 = _; rw [f1 7 (by decide), hc7']⟩,
        by show sc1 8 = _; rw [f1 8 (by decide), hc8'], by show sc1 9 = _; rw [f1 9 (by decide), hc9'],
        by show sc1 11 = _; rw [f1 11 (by decide), hc11']⟩
      hI1 hS1 h43' h44' h45' h46'
      (by show ls1 10 = _; rw [g1 10 (by decide), h10]) (by show ls1 11 = _; rw [g1 11 (by decide), h11])
      hcap hcap' hbig hM
    set c := coefCircuitL (ordT₀ N k) (.gate 0) (2 ^ K) repA repB (gvExp (2 ^ K) o) o.1 o.2.1 o.2.2
      (bst (K := K) repA repB P i).1
    have hcl : c.2.length = k := coefCircuitL_length _ _ _ _ _ _ _
    have hIS2 := is_exec hnM' hWM h2 ⟨hI1, hS1⟩
    rw [h2]
    have hs2 : ∀ x : SR, x.val < 16 ∨ (42 < x.val ∧ x.val < 47) ∨ 58 < x.val →
        sc2 x = sc1 x := fun x hx => f2 x hx
    -- append to `21`
    obtain ⟨sc3, h3, f3⟩ := exec_takeC (E := E) (n := 2) (lA := 16) (lR := 21) (by decide)
      (c.2.map (pos E ix)) [] (L0 ++ bList (E := E) (ix := ix) (K := K) repA repB P i)
      (setSL (setSL σ sc1 ls1) sc2 ls2) hIS2.1 (by simp [setSL, d2])
      (by show ls2 21 = _; rw [g2 21 (by decide)]; exact d1)
      (by show sc2 2 = _; rw [hs2 2 (by decide), f1 2 (by decide), hc2', List.length_map, hcl])
      (by rw [List.length_append, length_bList repA repB P i (by omega), List.length_map, hcl]
          nlinarith)
    set σ3 := setSL σ sc3 (Function.update (Function.update ls2 16 [])
      21 (L0 ++ bList (E := E) (ix := ix) (K := K) repA repB P i ++ c.2.map (pos E ix)))
    have h3' : exec E (takeC 2 16 21) (setSL (setSL σ sc1 ls1) sc2 ls2) = σ3 := by
      rw [h3]; rfl
    rw [exec_mk_noNand (takeC 2 16 21) (by simp [NoNand, takeC]),
      exec_mk_noNand odoO (by simp [NoNand, odoO]), h3']
    have hs3 : ∀ x : SR, x.val < 16 ∨ (42 < x.val ∧ x.val < 47) ∨ 58 < x.val → σ3.sc x = sc1 x :=
      fun x hx => by
        show sc3 x = _
        rw [f3 x (by simp only [List.mem_singleton]; rintro rfl; revert hx; decide)]
        exact hs2 x hx
    -- the odometer
    obtain ⟨a', c1', c2', t', h4, hidx', hc1'', hc2'', ht''⟩ := exec_odoO (E := E) σ3 a c1 c2 t
      (by rw [hs3 2 (by decide), f1 2 (by decide), hc2']) (by rw [hs3 5 (by decide), f1 5 (by decide), hc5'])
      (by rw [hs3 6 (by decide), f1 6 (by decide), hc6']) (by rw [hs3 43 (by decide), h43'])
      (by rw [hs3 44 (by decide), h44']) (by rw [hs3 45 (by decide), h45'])
      (by rw [hs3 46 (by decide), h46']) hc1 hc2 ht (by omega) (by nlinarith) (by nlinarith)
      (by omega)
    rw [h4]
    have hbody : exec E blockBody (mk E ix (bst (K := K) repA repB P i).1 (setSL σ sc1 ls1)) =
        mk E ix c.1 (setSL σ3 (Function.update (Function.update (Function.update (Function.update
          σ3.sc 43 a') 44 c1') 45 c2') 46 t') σ3.ls) := by
      rw [blockBody, exec_seq, exec_seq, h2, exec_mk_noNand (takeC 2 16 21) (by simp [NoNand, takeC]),
        exec_mk_noNand odoO (by simp [NoNand, odoO]), h3', h4]
    have hIS4 := is_exec hnM' hWM hbody ⟨hI1, hS1⟩
    refine ⟨Function.update (Function.update (Function.update (Function.update
      σ3.sc 43 a') 44 c1') 45 c2') 46 t', σ3.ls, ?_, ?_, ⟨a', c1', c2', t',
      by simp [Function.update_apply], by simp [Function.update_apply],
      by simp [Function.update_apply], by simp [Function.update_apply], by omega,
      hc1'', hc2'', ht''⟩, hIS4.1, hIS4.2, fun x hx => ?_, fun l hl => ?_⟩
    · rw [bst_succ repA repB P i o ho]; rfl
    · simp [bList_succ repA repB P i o ho, σ3, setSL, List.append_assoc]; rfl
    · simp only [σ3, setSL]
      rw [Function.update_of_ne (by rintro rfl; revert hx; decide),
        Function.update_of_ne (by rintro rfl; revert hx; decide),
        Function.update_of_ne (by rintro rfl; revert hx; decide),
        Function.update_of_ne (by rintro rfl; revert hx; decide)]
      show sc3 x = _
      rw [f3 x (by simp only [List.mem_singleton]; rintro rfl; revert hx; decide)]
      show sc2 x = _
      rw [hs2 x (by omega), f1 x hx]
    · simp only [σ3, setSL]
      rw [Function.update_of_ne (by rcases hl with rfl | rfl | hl <;> first | decide |
          (rintro rfl; revert hl; decide)),
        Function.update_of_ne (by rcases hl with rfl | rfl | hl <;> first | decide |
          (rintro rfl; revert hl; decide)),
        g2 l (by rcases hl with rfl | rfl | hl <;> first | (left; rfl) | (right; left; rfl) |
          (right; right; omega))]
      show ls1 l = _
      rw [g1 l hl]

theorem bst_length {N k K : ℕ} (repA repB : BI N k → Wire ι) (P : SLP ι) :
    ∀ i, i ≤ 4 * k * N → ∀ o ∈ (enumO N k).take i, ((bst (K := K) repA repB P i).2 o).length = k
  | 0, _, o, ho => by simp at ho
  | i + 1, hi, o, ho => by
    obtain ⟨o', ho'⟩ : ∃ o', (enumO N k)[i]? = some o' :=
      ⟨(enumO N k)[i]'(by rw [length_enumO']; omega), List.getElem?_eq_getElem _⟩
    rw [bst_succ repA repB P i o' ho', blockStepL]
    dsimp only
    rw [List.take_succ, ho', Option.toList_some, List.mem_append, List.mem_singleton] at ho
    by_cases h : o = o'
    · subst h; simp [coefCircuitL_length]
    · rw [Function.update_of_ne h]
      exact bst_length repA repB P i (by omega) o (ho.resolve_right h)

theorem ofFn_getD {α : Type*} {k : ℕ} (l : List α) (d : α) (h : l.length = k) :
    List.ofFn (fun i : Fin k => l.getD i d) = l := by
  subst h; apply List.ext_getElem (by simp)
  intro i h1 h2; simp [List.getD_eq_getElem _ _ h2]

/-- **A NAND block** (`12 = 4kN`): its output representation list into `21`. -/
def blockC : Code :=
  .seq (.seq (.zero 43) (.seq (.zero 44) (.seq (.zero 45) (.seq (.zero 46) (.lnil 21)))))
    (.rep 12 blockBody)

/-- The constants of a block, with `12 = 4kN`. -/
def CstK (N k K : ℕ) (σ : St) : Prop := CstC (E := E) N k K σ ∧ σ.sc 12 = 4 * k * N

theorem exec_blockC (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n)
    {N k K : ℕ} (hk : 0 < k) (hN : 0 < N) (hK : K ≤ k + 1) (repA repB : BI N k → Wire ι)
    (P : SLP ι) (σ : St) (hc : CstK (E := E) N k K σ) (hI : Inv E σ) (hS : ScOK E σ)
    (h10 : σ.ls 10 = repList E ix repA) (h11 : σ.ls 11 = repList E ix repB)
    (hcap : (2 * k * N + 1) * k ≤ E.C) (hcap' : k + 3 ≤ E.C) (hcap21 : 4 * k * N * k ≤ E.C)
    (hbig : 4 * k * N * k + 2 * N + k + 2 ≤ E.M)
    (hM : E.n + (nandBlockL (ordT₀ N k) (ordO₀ N k) (gvExp (2 ^ K)) (.gate 0) (2 ^ K) repA repB
      P).1.length ≤ E.M) :
    ∃ sc' ls', exec E blockC (mk E ix P σ) = mk E ix (nandBlockL (ordT₀ N k) (ordO₀ N k)
        (gvExp (2 ^ K)) (.gate 0) (2 ^ K) repA repB P).1 (setSL σ sc' ls') ∧
      ls' 21 = repList E ix (nandBlockL (ordT₀ N k) (ordO₀ N k) (gvExp (2 ^ K)) (.gate 0) (2 ^ K)
        repA repB P).2 ∧
      (∀ r : SR, r.val < 16 ∨ 58 < r.val → sc' r = σ.sc r) ∧
      (∀ l : LR, l = 10 ∨ l = 11 ∨ 21 < l.val → ls' l = σ.ls l) := by
  obtain ⟨hcc, hc12⟩ := hc
  set σ0 := setSL σ (Function.update (Function.update (Function.update (Function.update σ.sc 43 0)
    44 0) 45 0) 46 0) (Function.update σ.ls 21 [])
  have e0 : exec E (.seq (.zero 43) (.seq (.zero 44) (.seq (.zero 45) (.seq (.zero 46) (.lnil 21)))))
      (mk E ix P σ) = mk E ix P σ0 := rfl
  have hIS0 := is_exec (by omega) hWM e0 ⟨hI, hS⟩
  have hs0 : ∀ x : SR, x.val < 43 ∨ 46 < x.val → σ0.sc x = σ.sc x := fun x hx => by
    simp only [σ0, setSL]
    rw [Function.update_of_ne (by rintro rfl; revert hx; decide),
      Function.update_of_ne (by rintro rfl; revert hx; decide),
      Function.update_of_ne (by rintro rfl; revert hx; decide),
      Function.update_of_ne (by rintro rfl; revert hx; decide)]
  unfold blockC
  rw [exec_seq, e0, exec_rep, show (mk E ix P σ0).sc 12 = 4 * k * N by
    rw [mk_sc, hs0 12 (by decide), hc12]]
  have hall : (enumO N k).take (4 * k * N) = enumO N k := List.take_of_length_le (by
    rw [length_enumO'])
  obtain ⟨⟨⟨⟨h0, h1⟩, h2, h3, h4⟩, h5, h6, h7⟩, h8, h9, h11'⟩ := hcc
  obtain ⟨sc', ls', h, d, _, _, _, f, g⟩ := iter_blockBody hnM hWM hix hk hN hK repA repB P σ0 []
    ⟨⟨⟨⟨by rw [hs0 0 (by decide), h0], by rw [hs0 1 (by decide), h1]⟩, by rw [hs0 2 (by decide), h2],
      by rw [hs0 3 (by decide), h3], by rw [hs0 4 (by decide), h4]⟩, by rw [hs0 5 (by decide), h5],
      by rw [hs0 6 (by decide), h6], by rw [hs0 7 (by decide), h7]⟩,
      by rw [hs0 8 (by decide), h8], by rw [hs0 9 (by decide), h9], by rw [hs0 11 (by decide), h11']⟩
    hIS0.1 hIS0.2 (by simp [σ0, setSL]) (by simp [σ0, setSL]) (by simp [σ0, setSL])
    (by simp [σ0, setSL]) (by simp [σ0, setSL, h10]) (by simp [σ0, setSL, h11])
    (by simp [σ0, setSL]) hcap hcap' (by simpa using hcap21) hbig (4 * k * N) le_rfl
    (by simp only [bst, hall]; exact hM)
  refine ⟨sc', ls', ?_, ?_, fun r hr => ?_, fun l hl => ?_⟩
  · rw [h]; simp only [bst, hall]; rfl
  · rw [d, List.nil_append, bList, repList]
    simp only [hall, nandBlockL]
    congr 1
    apply List.map_congr_left; intro o ho
    have hl := bst_length (K := K) repA repB P (4 * k * N) le_rfl o (by rw [hall]; exact ho)
    simp only [bst, hall] at hl ⊢
    rw [show ((o.1, o.2.1, o.2.2) : OI N k) = o from rfl, show ordO₀ N k = enumO N k from rfl,
      ofFn_getD _ _ hl]
  · rw [f r hr, hs0 r (by omega)]
  · rw [g l hl]
    simp [σ0, setSL, Function.update_of_ne (show l ≠ 21 by
      rcases hl with rfl | rfl | hl <;> first | decide | (rintro rfl; revert hl; decide))]

end FhatGen

end SigabaNeo.Lattices
