import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenRounds

/-!
# Generating gate tapes: one output coefficient of a NAND block

`coefC`: the gadget coefficient `constL z k (gvExp q o)` into the list `12` (`gvBody`), the terms
(`leavesC`), the tree (`roundsC`), the final sum (`foldSumC`) into the list `16`
(`exec_coefC`: it is `coefCircuitL` at the orders of `f̂`).
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-! ### The gadget coefficient -/

/-- Push the bit `42` of `gvExp (2^K) (a, (c1, c2), t)` (registers `43 … 46`, `K` in `4`). -/
def gvBody (l : LR) : Code :=
  .ifLt 7 46 (.lpush l rZ) (.ifLt 43 44 (.lpush l rZ) (.ifLt 44 43 (.lpush l rZ)
    (.ifLt 42 45 (.lpush l rZ) (.ifLt 45 42 (.lpush l rZ) (.ifLt 45 4 (.lpush l rONE)
      (.lpush l rZ))))))

/-- The registers of an output position `(a, (c1, c2), t)`. -/
def OReg (k K : ℕ) (a c1 c2 t : ℕ) (σ : St) : Prop :=
  Cst (E := E) k K σ ∧ σ.sc 7 = 0 ∧ σ.sc 43 = a ∧ σ.sc 44 = c1 ∧ σ.sc 45 = c2 ∧ σ.sc 46 = t

theorem exec_gvBody (hnM : E.n + 1 ≤ E.M) {k K a c1 c2 t : ℕ} (l : LR) (σ : St) (i : ℕ)
    (hc : OReg (E := E) k K a c1 c2 t σ) (hi : σ.sc 42 = i) (hl : (σ.ls l).length < E.C) :
    exec E (gvBody l) σ = { σ with ls := Function.update σ.ls l (σ.ls l ++
      [if t = 0 ∧ a = c1 ∧ i = c2 ∧ c2 < K then E.n else E.n + 1]) } := by
  obtain ⟨⟨⟨h0, h1⟩, _, _, h4⟩, h7, h43, h44, h45, h46⟩ := hc
  simp only [gvBody, exec, hi, h4, h7, h43, h44, h45, h46, hl, ite_true, h0, h1]
  split_ifs <;> simp only [min_eq_left (show E.n + 1 ≤ E.M by omega),
    min_eq_left (show E.n ≤ E.M by omega)] <;> first | rfl | (exfalso; omega)

theorem map_pos_constL_gv {N k K : ℕ} (o : OI N k) :
    (constL (.gate 0 : Wire ι) k (gvExp (2 ^ K) o)).map (pos E ix) =
      (List.range k).map (fun i => if o.2.2.val = 0 ∧ o.1.val = o.2.1.1.val ∧ i = o.2.1.2.val ∧
        o.2.1.2.val < K then E.n else E.n + 1) := by
  rw [constL_eq_map, List.map_map]
  apply List.map_congr_left; intro i _
  simp only [Function.comp, gvExp]
  obtain ⟨a, ⟨c1, c2⟩, t⟩ := o
  simp only
  have hac : (a.val = c1.val) ↔ a = c1 := Fin.val_eq_val _ _
  by_cases hc : t.val = 0 ∧ a = c1
  · rw [if_pos hc, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    by_cases h : i = c2.val ∧ c2.val < K
    · simp [h, hc, pos]
    · have : ¬ (t.val = 0 ∧ a.val = c1.val ∧ i = c2.val ∧ c2.val < K) := fun h' => h ⟨h'.2.2.1, h'.2.2.2⟩
      rw [if_neg this]
      have : ¬ (i < K ∧ c2.val = i) := by omega
      simp [this, pos]
  · rw [if_neg hc]
    have : ¬ (t.val = 0 ∧ a.val = c1.val ∧ i = c2.val ∧ c2.val < K) := fun h' =>
      hc ⟨h'.1, hac.mp h'.2.1⟩
    rw [if_neg this]
    simp [pos]

/-! ### The final sum -/

/-- `foldSum` of the `|54|` numbers of the list `12`, into `16` (`57`, `58` scratch). -/
def foldSumC : Code :=
  .ifLt 7 54 (.seq (.seq (.lnil 16) (.seq (takeC 2 12 16) (.seq (.mov 57 54) (.seq (.zero 58)
    (.seq (.inc 58) (.sub 57 58)))))) (.rep 57 foldBody)) (.seq (.lnil 16) (.rep 2 (.lpush 16 rZ)))

theorem exec_foldSumC (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n)
    {k K : ℕ} (hK : K ≤ k + 1) (hcap' : k + 3 ≤ E.C) (hkM : k + 2 ≤ E.M)
    (L : List (List (Wire ι))) (P : SLP ι) (σ : St) (hL : ∀ a ∈ L, a.length = k)
    (hc : CstR (E := E) k K σ) (hI : Inv E σ) (hS : ScOK E σ)
    (h12 : σ.ls 12 = flatPos (E := E) (ix := ix) L) (h54 : σ.sc 54 = L.length)
    (hM : E.n + (exec E foldSumC (mk E ix P σ)).t ≤ E.M) :
    ∃ sc' ls', exec E foldSumC (mk E ix P σ) =
        mk E ix (foldSum (.gate 0) (2 ^ K) k P L).1 (setSL σ sc' ls') ∧
      ls' 16 = (foldSum (.gate 0) (2 ^ K) k P L).2.map (pos E ix) ∧
      (∀ r : SR, r.val < 16 ∨ (42 < r.val ∧ r.val < 57) ∨ 58 < r.val → sc' r = σ.sc r) ∧
      (∀ l : LR, (8 < l.val ∧ l.val < 12) ∨ (12 < l.val ∧ l.val < 16) ∨ 16 < l.val →
        ls' l = σ.ls l) := by
  have hnM' : E.n ≤ E.M := by omega
  unfold foldSumC at hM ⊢
  rw [exec_ifLt, mk_sc, hc.2.2, h54] at hM ⊢
  rcases L with _ | ⟨a, rest⟩
  · rw [if_neg (by simp)] at hM ⊢
    rw [exec_mk_noNand (.seq (.lnil 16) (.rep 2 (.lpush 16 rZ))) ⟨trivial, trivial⟩]
    refine ⟨σ.sc, Function.update σ.ls 16 (List.replicate k (E.n + 1)), ?_, ?_,
      fun _ _ => rfl, fun l hl => ?_⟩
    · rw [exec_seq, exec_rep, show (exec E (.lnil 16) σ).sc 2 = k from hc.1.2.1,
        iter_push 16 rZ k _ (by simp [exec]; omega) (by simp [exec, rZ, hc.1.1.2]; omega)]
      simp [exec, setSL, foldSum, rZ, hc.1.1.2]
    · simp [foldSum, map_pos_constL_zero]
    · simp [Function.update_of_ne (show l ≠ 16 by rintro rfl; revert hl; decide)]
  · rw [if_pos (by simp)] at hM ⊢
    have ha := hL a (by simp)
    obtain ⟨sc1, h1, f1⟩ := exec_takeC (E := E) (n := 2) (lA := 12) (lR := 16) (by decide)
      (a.map (pos E ix)) (flatPos (E := E) (ix := ix) rest) [] (exec E (.lnil 16) σ)
      (inv_exec E _ σ hI) (by simp [exec, h12, flatPos_cons]) (by simp [exec])
      (by simp [exec, hc.1.2.1, ha]) (by simp [ha]; omega)
    set τ1 : St := { exec E (.lnil 16) σ with sc := sc1, ls := Function.update (Function.update
      (exec E (.lnil 16) σ).ls 12 (flatPos (E := E) (ix := ix) rest)) 16 ([] ++ a.map (pos E ix)) }
    have hs1 : sc1 54 = rest.length + 1 := by rw [f1 54 (by decide)]; simpa [exec] using h54
    set σ1 := setSL τ1 (Function.update (Function.update sc1 58 1) 57 rest.length) τ1.ls
    have e1 : exec E (.seq (.lnil 16) (.seq (takeC 2 12 16) (.seq (.mov 57 54) (.seq (.zero 58)
        (.seq (.inc 58) (.sub 57 58)))))) σ = σ1 := by
      simp only [exec_seq]; rw [h1]
      simp only [exec, σ1, setSL, τ1, hs1, Function.update_self,
        Function.update_of_ne (show (58 : SR) ≠ 57 by decide), Function.update_of_ne
        (show (57 : SR) ≠ 58 by decide), min_eq_left (show 0 + 1 ≤ E.M by omega)]
      simp only [Nat.zero_add, Nat.add_sub_cancel, St.mk.injEq, true_and, and_true]
      funext x; simp only [Function.update_apply]; split_ifs <;> simp_all
    have hIS1 := is_exec hnM' hWM e1 ⟨hI, hS⟩
    rw [exec_seq, exec_mk_noNand _ (by simp [NoNand, takeC]), e1, exec_rep,
      show (mk E ix P σ1).sc 57 = rest.length by simp [σ1, setSL]] at hM ⊢
    have hs1' : ∀ x : SR, x ≠ 41 → x ≠ 57 → x ≠ 58 → σ1.sc x = σ.sc x := fun x h41 h57 h58 => by
      simp only [σ1, setSL]
      rw [Function.update_of_ne h57, Function.update_of_ne h58, f1 x (by simpa using h41)]; rfl
    obtain ⟨sc', ls', h', d', f', g'⟩ := iter_foldBody hnM hWM hix hK hcap' hkM rest P a σ1
      (fun x hx => hL x (by simp [hx])) ha
      (cstR_of hc (fun x hx => hs1' x (by rintro rfl; revert hx; decide)
        (by rintro rfl; revert hx; decide) (by rintro rfl; revert hx; decide)))
      hIS1.1 hIS1.2 (by simp [σ1, τ1, setSL]) (by simp [σ1, τ1, setSL]) hM
    refine ⟨sc', ls', h', d', fun x hx => ?_, fun l hl => ?_⟩
    · rw [f' x (by omega), hs1' x (by rintro rfl; revert hx; decide)
        (by rintro rfl; revert hx; decide) (by rintro rfl; revert hx; decide)]
    · rw [g' l (by omega)]
      simp [σ1, τ1, setSL, exec, Function.update_of_ne (show l ≠ 16 by rintro rfl; revert hl; decide),
        Function.update_of_ne (show l ≠ 12 by rintro rfl; revert hl; decide)]

/-! ### The coefficient -/

theorem leaves_lengths {N k K : ℕ} (repA repB : BI N k → Wire ι) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) : ∀ (P : SLP ι) (es : List ((Fin 2 × Fin k) × Fin N)),
    (∀ x ∈ (leaves (.gate 0) (2 ^ K) k repA repB a col t P es).2, x.length = k) ∧
      (leaves (.gate 0) (2 ^ K) k repA repB a col t P es).2.length = es.length
  | P, [] => by simp [leaves]
  | P, e :: es => by
    have ih := leaves_lengths (K := K) repA repB a col t
      (termStep (.gate 0) (2 ^ K) k repA repB a col t (P, constL (.gate 0) k 0) e).1 es
    refine ⟨fun x hx => ?_, by simp [leaves, ih.2]⟩
    simp only [leaves, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact length_termStep _ _ _ _ _ _ _ (constL_length _ _ _) _
    · exact ih.1 x hx

/-- **One output coefficient** (`9 = 2kN + 1`, `11 = treeHeight`), into the list `16`. -/
def coefC : Code :=
  .seq (constC 2 12 (gvBody 12)) (.seq leavesC (.seq (.mov 54 9) (.seq roundsC foldSumC)))

/-- The constant registers of a block. -/
def CstC (N k K : ℕ) (σ : St) : Prop :=
  CstB (E := E) k K N σ ∧ σ.sc 8 = 2 * k * N ∧ σ.sc 9 = 2 * k * N + 1 ∧ σ.sc 11 = treeHeight N k

set_option maxHeartbeats 4000000 in
theorem exec_coefC (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n)
    {N k K : ℕ} (hk : 0 < k) (hN : 0 < N) (hK : K ≤ k + 1) (repA repB : BI N k → Wire ι)
    (o : OI N k) (P : SLP ι) (σ : St) (hc : CstC (E := E) N k K σ) (hI : Inv E σ) (hS : ScOK E σ)
    (h43 : σ.sc 43 = o.1.val) (h44 : σ.sc 44 = o.2.1.1.val) (h45 : σ.sc 45 = o.2.1.2.val)
    (h46 : σ.sc 46 = o.2.2.val) (h10 : σ.ls 10 = repList E ix repA)
    (h11 : σ.ls 11 = repList E ix repB) (hcap : (2 * k * N + 1) * k ≤ E.C) (hcap' : k + 3 ≤ E.C)
    (hbig : 4 * k * N * k + 2 * N + k + 2 ≤ E.M)
    (hM : E.n + (exec E coefC (mk E ix P σ)).t ≤ E.M) :
    ∃ sc' ls', exec E coefC (mk E ix P σ) = mk E ix (coefCircuitL (ordT₀ N k) (.gate 0) (2 ^ K)
        repA repB (gvExp (2 ^ K) o) o.1 o.2.1 o.2.2 P).1 (setSL σ sc' ls') ∧
      ls' 16 = (coefCircuitL (ordT₀ N k) (.gate 0) (2 ^ K) repA repB (gvExp (2 ^ K) o) o.1 o.2.1
        o.2.2 P).2.map (pos E ix) ∧
      (∀ r : SR, r.val < 16 ∨ (42 < r.val ∧ r.val < 47) ∨ 58 < r.val → sc' r = σ.sc r) ∧
      (∀ l : LR, l = 10 ∨ l = 11 ∨ 20 < l.val → ls' l = σ.ls l) := by
  have hnM' : E.n ≤ E.M := by omega
  obtain ⟨⟨⟨⟨hc0, hc1⟩, hc2, hc3, hc4⟩, hc5, hc6, hc7⟩, hc8, hc9, hc11⟩ := hc
  obtain ⟨a, ⟨c1, c2⟩, t⟩ := o
  simp only at h43 h44 h45 h46 ⊢
  -- 1: the gadget coefficient into `12`
  have hQ : ∀ τ : St, OReg (E := E) k K a.val c1.val c2.val t.val τ → ∀ v ls',
      OReg (E := E) k K a.val c1.val c2.val t.val (setSL τ (Function.update τ.sc 42 v) ls') := by
    intro τ ⟨⟨⟨h0, h1⟩, h2, h3, h4⟩, h7, h43, h44, h45, h46⟩ v ls'
    simp only [setSL]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
      (rw [Function.update_of_ne (by decide)]; assumption)
  have h1 := exec_constC (E := E) (cnt := 2) (l := 12)
    (Q := OReg (E := E) k K a.val c1.val c2.val t.val) (by decide) hQ
    (fun τ i hq hi hl => exec_gvBody hnM 12 τ i hq hi hl) σ
    ⟨⟨⟨hc0, hc1⟩, hc2, hc3, hc4⟩, hc7, h43, h44, h45, h46⟩ (by rw [hc2]; nlinarith)
    (by rw [hc2]; nlinarith)
  rw [hc2, ← map_pos_constL_gv (ix := ix) ((a, (c1, c2), t) : OI N k)] at h1
  set G := constL (.gate 0 : Wire ι) k (gvExp (2 ^ K) ((a, (c1, c2), t) : OI N k))
  set σ1 := setSL σ (Function.update σ.sc 42 k) (Function.update σ.ls 12 (G.map (pos E ix)))
  have hIS1 := is_exec hnM' hWM (τ := σ) h1 ⟨hI, hS⟩
  have hs1 : ∀ x : SR, x ≠ 42 → σ1.sc x = σ.sc x := fun x hx => by
    simp [σ1, setSL, Function.update_of_ne hx]
  unfold coefC at hM ⊢
  simp only [exec_seq] at hM ⊢
  rw [exec_mk_noNand _ (by simp [NoNand, constC, gvBody]), h1] at hM ⊢
  -- 2: the terms
  obtain ⟨sc2, ls2, h2, d2, f2, g2⟩ := exec_leavesC hnM hWM hix hk hN hK repA repB a (c1, c2) t
    P σ1 (G.map (pos E ix))
    ⟨⟨⟨by rw [hs1 0 (by decide), hc0], by rw [hs1 1 (by decide), hc1]⟩, by rw [hs1 2 (by decide), hc2],
      by rw [hs1 3 (by decide), hc3], by rw [hs1 4 (by decide), hc4]⟩, by rw [hs1 5 (by decide), hc5],
      by rw [hs1 6 (by decide), hc6], by rw [hs1 7 (by decide), hc7]⟩
    (by rw [hs1 8 (by decide), hc8]) hIS1.1 hIS1.2 (by rw [hs1 43 (by decide), h43])
    (by rw [hs1 44 (by decide), h44]) (by rw [hs1 45 (by decide), h45])
    (by rw [hs1 46 (by decide), h46]) (by simp [σ1, setSL, h10]) (by simp [σ1, setSL, h11])
    (by simp [σ1, setSL]) (by simp [G, constL_length]; nlinarith) hcap' hbig
    (le_trans (Nat.add_le_add_left (by t_chain) _) hM)
  set R := leaves (.gate 0) (2 ^ K) k repA repB a (c1, c2) t P (enumT N k)
  have hRl := leaves_lengths (K := K) repA repB a (c1, c2) t P (enumT N k)
  have hIS2 := is_exec hnM' hWM h2 hIS1
  rw [h2] at hM ⊢
  have hs2 : ∀ x : SR, x.val < 16 ∨ (42 < x.val ∧ x.val < 47) ∨ 53 < x.val → sc2 x = σ.sc x :=
    fun x hx => by rw [f2 x (by omega), hs1 x (by rintro rfl; revert hx; decide)]
  -- 3: the count `2kN + 1` into `54`
  set σ3 := setSL σ (Function.update sc2 54 (2 * k * N + 1)) ls2
  have e3 : exec E (.mov 54 9) (mk E ix R.1 (setSL σ1 sc2 ls2)) = mk E ix R.1 σ3 := by
    rw [exec_mk_noNand (.mov 54 9) trivial]
    simp only [exec, σ3, setSL, hs2 9 (by decide), hc9]; rfl
  have hIS3 := is_exec hnM' hWM e3 hIS2
  rw [e3] at hM ⊢
  -- 4: the rounds
  set L := G :: R.2
  have hLl : ∀ x ∈ L, x.length = k := fun x hx => by
    simp only [L, List.mem_cons] at hx; rcases hx with rfl | hx
    · exact constL_length _ _ _
    · exact hRl.1 x hx
  have hLn : L.length = 2 * k * N + 1 := by
    rw [show L.length = R.2.length + 1 from rfl, hRl.2, length_enumT]
  have hs3 : ∀ x : SR, x.val < 16 ∨ (42 < x.val ∧ x.val < 47) ∨ 54 < x.val → σ3.sc x = σ.sc x :=
    fun x hx => by
      simp only [σ3, setSL]; rw [Function.update_of_ne (by rintro rfl; revert hx; decide)]
      exact hs2 x (by omega)
  have hc3 : CstR (E := E) k K σ3 := ⟨⟨⟨by rw [hs3 0 (by decide), hc0], by rw [hs3 1 (by decide), hc1]⟩,
    by rw [hs3 2 (by decide), hc2], by rw [hs3 3 (by decide), hc3], by rw [hs3 4 (by decide), hc4]⟩,
    by rw [hs3 6 (by decide), hc6], by rw [hs3 7 (by decide), hc7]⟩
  rw [roundsC, exec_rep, show (mk E ix R.1 σ3).sc 11 = treeHeight N k by
    rw [mk_sc, hs3 11 (by decide), hc11]] at hM ⊢
  obtain ⟨sc4, ls4, h4, d4, c4, l4, f4, g4⟩ := iter_rounds hnM hWM hix hK hcap' (by nlinarith)
    (treeHeight N k) L R.1 σ3 hLl hc3 hIS3.1 hIS3.2
    (by simp only [σ3, setSL, L, flatPos_cons]; rw [d2]; rfl)
    (by simp [σ3, setSL, hLn]) (by rw [hLn]; exact hcap) (by rw [hLn]; nlinarith)
    (le_trans (Nat.add_le_add_left (by t_chain) _) hM)
  have hIS4 := is_exec hnM' hWM (τ := mk E ix R.1 σ3) (c := .rep 11 pairRoundC)
    (τ' := mk E ix (rounds (.gate 0) (2 ^ K) k (treeHeight N k) R.1 L).1 (setSL σ3 sc4 ls4))
    (by rw [exec_rep, show (mk E ix R.1 σ3).sc 11 = treeHeight N k by
      rw [mk_sc, hs3 11 (by decide), hc11]]; exact h4) hIS3
  rw [h4] at hM ⊢
  -- 5: the final sum
  obtain ⟨sc5, ls5, h5, d5, f5, g5⟩ := exec_foldSumC hnM hWM hix hK hcap' (by nlinarith) _ _
    (setSL σ3 sc4 ls4) l4 (cstR_of hc3 (fun x hx => f4 x (by omega))) hIS4.1 hIS4.2 d4 c4 hM
  rw [h5]
  refine ⟨sc5, ls5, rfl, d5, fun x hx => ?_, fun l hl => ?_⟩
  · show sc5 x = _
    rw [f5 x (by omega)]; show sc4 x = _; rw [f4 x (by omega)]; exact hs3 x (by omega)
  · show ls5 l = _
    rw [g5 l (by rcases hl with rfl | rfl | hl <;> first | decide | omega)]
    show ls4 l = _
    rw [g4 l (by rcases hl with rfl | rfl | hl <;> first | decide | omega)]
    show ls2 l = _
    rw [g2 l (by rcases hl with rfl | rfl | hl <;> simp_all)]
    simp [σ1, setSL, Function.update_of_ne (show l ≠ 12 by rcases hl with rfl | rfl | hl <;> first | decide | (rintro rfl; revert hl; decide))]

end FhatGen

end SigabaNeo.Lattices
