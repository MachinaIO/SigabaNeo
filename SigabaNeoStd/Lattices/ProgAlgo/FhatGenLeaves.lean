import SigabaNeoStd.Lattices.ProgAlgo.FhatGenTerm2

/-!
# Generating gate tapes: the terms of an output coefficient

`leavesC`: one round of `termStepC` per term `e` of `enumT` (from the running sum `constL z k 0`),
appending its `k` output wires to the list `12`; the term is held in the registers `47 … 49` and
advanced by an odometer (`odoC`). `exec_leavesC`: it is `leaves`.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-! ### Lengths -/

theorem length_modAdd_eq (z : Wire ι) (q k : ℕ) (p : SLP ι) (as bs : List (Wire ι))
    (ha : as.length = k) (hb : bs.length = k) : (modAdd z q k p as bs).2.length = k := by
  have h1 : (rippleAdd p as bs z).2.length = k + 1 := by
    rw [length_rippleAdd_eq _ _ _ _ (by omega), ha]
  have h2 : (rippleAdd (rippleAdd p as bs z).1 (rippleAdd p as bs z).2
      (constL z (k + 1) (2 ^ (k + 1) - q)) z).2.length = k + 2 := by
    rw [length_rippleAdd_eq _ _ _ _ (by rw [h1, constL_length]), h1]
  show (List.take k (muxL _ _ _ _).2).length = k
  rw [List.length_take, length_muxL_eq _ _ _ _ (by rw [List.length_take, h2, h1]; omega),
    List.length_take, h2]
  omega

theorem length_modSub_eq (z : Wire ι) (q k : ℕ) (p : SLP ι) (as bs : List (Wire ι))
    (ha : as.length = k) (hb : bs.length = k) : (modSub z q k p as bs).2.length = k := by
  have h1 := (length_notL p bs).2
  have h2 : (rippleAdd (notL p bs).1 as (notL p bs).2 .one).2.length = k + 1 := by
    rw [length_rippleAdd_eq _ _ _ _ (by omega), ha]
  have h3 : (rippleAdd (rippleAdd (notL p bs).1 as (notL p bs).2 .one).1
      ((rippleAdd (notL p bs).1 as (notL p bs).2 .one).2.take k) (constL z k q) z).2.length =
      k + 1 := by
    rw [length_rippleAdd_eq _ _ _ _ (by rw [List.length_take, h2, constL_length]; omega),
      List.length_take, h2]; omega
  show (muxL _ _ _ _).2.length = k
  rw [length_muxL_eq _ _ _ _ (by rw [List.length_take, List.length_take, h2, h3]),
    List.length_take, h2]
  omega

theorem length_termStep {N k K : ℕ} (repA repB : BI N k → Wire ι) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (P : SLP ι) (acc : List (Wire ι)) (hacc : acc.length = k)
    (e : (Fin 2 × Fin k) × Fin N) :
    (termStep (.gate 0) (2 ^ K) k repA repB a col t (P, acc) e).2.length = k := by
  unfold termStep
  split_ifs
  · exact length_modSub_eq _ _ _ _ _ _ hacc (by rw [(length_andL _ _ _).2]; simp [coefW, bitsL])
  · exact length_modAdd_eq _ _ _ _ _ _ hacc (by rw [(length_andL _ _ _).2]; simp [coefW, bitsL])

/-! ### The order of the terms -/

theorem enumT_getElem? {N k : ℕ} (x : Fin 2) (y : Fin k) (z : Fin N) :
    (enumT N k)[(x.val * k + y.val) * N + z.val]? = some ((x, y), z) := by
  have e0 := getElem?_product (List.finRange k) (List.finRange 2) x.val y.val
    (by simpa using x.isLt) (by simpa using y.isLt)
  simp only [List.length_finRange] at e0
  have hc : x.val * k + y.val < (List.finRange 2 ×ˢ List.finRange k).length := by
    simp [List.length_product]; nlinarith [x.isLt, y.isLt]
  have e0' : (List.finRange 2 ×ˢ List.finRange k)[x.val * k + y.val] = (x, y) := by
    have := (List.getElem?_eq_some_iff.mp e0).2
    simpa using this
  have e1 := getElem?_product (List.finRange N) (List.finRange 2 ×ˢ List.finRange k)
    (x.val * k + y.val) z.val hc (by simpa using z.isLt)
  simp only [List.length_finRange] at e1
  rw [e0'] at e1
  simp only [enumT]
  rw [e1]; simp

theorem length_enumT {N k : ℕ} : (enumT N k).length = 2 * k * N := by
  simp [enumT, List.length_product]

/-- `t_chain`, also through iterates. -/
macro "t_chain2" : tactic => `(tactic| (repeat (first | (with_reducible exact le_rfl) |
  (with_reducible refine le_trans ?_ (t_le_exec _ _ _)) |
  (with_reducible refine le_trans ?_ (t_le_iter _ _ _ _)))))

/-! ### Repeated pushes and the odometer -/

theorem iter_push (l : LR) (r : SR) : ∀ (m : ℕ) (σ : St), (σ.ls l).length + m ≤ E.C →
    σ.sc r ≤ E.M → (exec E (.lpush l r))^[m] σ =
      { σ with ls := Function.update σ.ls l (σ.ls l ++ List.replicate m (σ.sc r)) }
  | 0, σ, _, _ => by simp
  | m + 1, σ, hC, hr => by
    rw [Function.iterate_succ_apply, exec_lpush_lt σ l r (by omega) hr,
      iter_push l r m { σ with ls := Function.update σ.ls l (σ.ls l ++ [σ.sc r]) }
        (by simp; omega) hr]
    simp [List.replicate_succ, List.append_assoc]

/-- The odometer of the terms `((r, e12), e2)` in the registers `47 48 49` (moduli `k = 2`,
`N = 5`). -/
def odoC : Code := .seq (.inc 49) (.ifLt 49 5 .skip (.seq (.zero 49) (.seq (.inc 48)
  (.ifLt 48 2 .skip (.seq (.zero 48) (.inc 47))))))

theorem exec_odoC {N k : ℕ} (σ : St) (x y z : ℕ) (h2 : σ.sc 2 = k) (h5 : σ.sc 5 = N)
    (h47 : σ.sc 47 = x) (h48 : σ.sc 48 = y) (h49 : σ.sc 49 = z) (hy : y < k) (hz : z < N)
    (hM : x + 1 ≤ E.M) (hkM : k ≤ E.M) (hNM : N ≤ E.M) :
    ∃ x' y' z', exec E odoC σ = setSL σ (Function.update (Function.update (Function.update σ.sc
        47 x') 48 y') 49 z') σ.ls ∧ (x' * k + y') * N + z' = (x * k + y) * N + z + 1 ∧
      y' < k ∧ z' < N := by
  by_cases hz' : z + 1 < N
  · refine ⟨x, y, z + 1, ?_, by ring, hy, hz'⟩
    simp only [odoC, exec_seq, exec_ifLt]
    simp [exec, h49, h5, h47, h48, min_eq_left (show z + 1 ≤ E.M by omega), hz', setSL,
      Function.update_apply]
    funext v; simp only [Function.update_apply]; split_ifs <;> simp_all
  · by_cases hy' : y + 1 < k
    · refine ⟨x, y + 1, 0, ?_, by have : z + 1 = N := by omega
                                  rw [← this]; ring, hy', by omega⟩
      simp only [odoC, exec_seq, exec_ifLt]
      simp [exec, h49, h5, h47, h48, h2, min_eq_left (show z + 1 ≤ E.M by omega),
        min_eq_left (show y + 1 ≤ E.M by omega), hz', hy', setSL, Function.update_apply]
      funext v; simp only [Function.update_apply]; split_ifs <;> simp_all
    · have e1 : N = z + 1 := by omega
      have e2 : k = y + 1 := by omega
      refine ⟨x + 1, 0, 0, ?_, by subst e1; subst e2; ring, by omega, by omega⟩
      simp only [odoC, exec_seq, exec_ifLt]
      simp [exec, h49, h5, h47, h48, h2, min_eq_left (show z + 1 ≤ E.M by omega),
        min_eq_left (show y + 1 ≤ E.M by omega), min_eq_left hM, hz', hy', setSL,
        Function.update_apply]
      funext v; simp only [Function.update_apply]; split_ifs <;> simp_all

/-! ### The loop over the terms -/

/-- One term: the running sum `constL z k 0` into `0`, `termStepC`, append its output to `12`,
advance the odometer. -/
def leafBody : Code :=
  .seq (.seq (.lnil 0) (.rep 2 (.lpush 0 rZ))) (.seq termStepC (.seq (takeC 2 2 12) odoC))

theorem map_pos_constL_zero (k : ℕ) :
    (constL (.gate 0 : Wire ι) k 0).map (pos E ix) = List.replicate k (E.n + 1) := by
  rw [constL_eq_map, List.map_map]
  simp only [Nat.zero_testBit]
  rw [List.eq_replicate_iff]; simp [pos]

theorem noNand_leafPre : NoNand (.seq (.lnil 0) (.rep 2 (.lpush 0 rZ))) := ⟨trivial, trivial⟩
theorem noNand_takeOdo : NoNand (.seq (takeC 2 2 12) odoC) := by
  simp [NoNand, takeC, odoC]

theorem le_length_termStep {N k : ℕ} (z : Wire ι) (q : ℕ) (repA repB : BI N k → Wire ι) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (st : SLP ι × List (Wire ι)) (e : (Fin 2 × Fin k) × Fin N) :
    st.1.length ≤ (termStep z q k repA repB a col t st e).1.length := by
  unfold termStep
  split_ifs
  · exact (le_length_andL _ _ _).trans (le_length_modSub _ _ _ _ _ _)
  · exact (le_length_andL _ _ _).trans (le_length_modAdd _ _ _ _ _ _)

theorem le_length_leaves {N k : ℕ} (z : Wire ι) (q : ℕ) (repA repB : BI N k → Wire ι) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) : ∀ (p : SLP ι) (es : List ((Fin 2 × Fin k) × Fin N)),
    p.length ≤ (leaves z q k repA repB a col t p es).1.length
  | p, [] => le_rfl
  | p, e :: es => (le_length_termStep z q repA repB a col t (p, _) e).trans
      (le_length_leaves z q repA repB a col t _ es)

set_option maxHeartbeats 4000000 in
theorem iter_leafBody (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n)
    {N k K : ℕ} (hK : K ≤ k + 1) (repA repB : BI N k → Wire ι) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) :
    ∀ (j i : ℕ) (P : SLP ι) (σ : St) (x y z : ℕ) (L0 : List ℕ),
      i + j ≤ 2 * k * N → CstB (E := E) k K N σ → Inv E σ → ScOK E σ →
      σ.sc 43 = a.val → σ.sc 44 = col.1.val → σ.sc 45 = col.2.val → σ.sc 46 = t.val →
      σ.sc 47 = x → σ.sc 48 = y → σ.sc 49 = z → (x * k + y) * N + z = i → y < k → z < N →
      σ.ls 10 = repList E ix repA → σ.ls 11 = repList E ix repB → σ.ls 12 = L0 →
      L0.length + j * k ≤ E.C → k + 3 ≤ E.C → 4 * k * N * k + 2 * N + k + 2 ≤ E.M →
      E.n + (leaves (.gate 0) (2 ^ K) k repA repB a col t P
        (((enumT N k).drop i).take j)).1.length ≤ E.M →
      ∃ sc' ls', (exec E leafBody)^[j] (mk E ix P σ) = mk E ix
          (leaves (.gate 0) (2 ^ K) k repA repB a col t P (((enumT N k).drop i).take j)).1
          (setSL σ sc' ls') ∧
        ls' 12 = L0 ++ ((leaves (.gate 0) (2 ^ K) k repA repB a col t P
          (((enumT N k).drop i).take j)).2.map (List.map (pos E ix))).flatten ∧
        (∀ r : SR, r.val < 16 ∨ (43 ≤ r.val ∧ r.val ≤ 46) ∨ 53 < r.val → sc' r = σ.sc r) ∧
        (∀ l : LR, l = 10 ∨ l = 11 ∨ (12 < l.val ∧ l.val ≤ 16) ∨ 20 < l.val → ls' l = σ.ls l)
  | 0, i, P, σ, x, y, z, L0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _, _, _, _ =>
    ⟨σ.sc, σ.ls, by simp [setSL, leaves], by simp [leaves, hL], fun _ _ => rfl, fun _ _ => rfl⟩
  | j + 1, i, P, σ, x, y, z, L0, hij, hc, hI, hS, h43, h44, h45, h46, h47, h48, h49, hi, hy, hz,
      h10, h11, hL, hcap, hcap', hbig, hM => by
    have hnM' : E.n ≤ E.M := by omega
    obtain ⟨⟨⟨hc0, hc1⟩, hc2, hc3, hc4⟩, hc5, hc6, hc7⟩ := hc
    have hk : 0 < k := by omega
    have hN : 0 < N := by omega
    have hx : x < 2 := by
      by_contra h; have : 2 * k * N ≤ (x * k + y) * N := by nlinarith
      omega
    set e : (Fin 2 × Fin k) × Fin N := ((⟨x, hx⟩, ⟨y, hy⟩), ⟨z, hz⟩)
    have hie : (enumT N k)[i]? = some e := by
      rw [← hi]; exact enumT_getElem? (⟨x, hx⟩ : Fin 2) ⟨y, hy⟩ ⟨z, hz⟩
    have hlt : i < (enumT N k).length := (List.getElem?_eq_some_iff.mp hie).1
    have hdrop : ((enumT N k).drop i).take (j + 1) = e :: ((enumT N k).drop (i + 1)).take j := by
      rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons]
      congr 1; exact (List.getElem?_eq_some_iff.mp hie).2
    rw [hdrop] at hM ⊢
    simp only [leaves] at hM
    rw [Function.iterate_succ_apply]
    -- the running sum `constL z k 0` into `0`
    set acc : List (Wire ι) := constL (.gate 0) k 0
    set σ1 : St := { σ with ls := Function.update σ.ls 0 (acc.map (pos E ix)) }
    have e1 : exec E (.seq (.lnil 0) (.rep 2 (.lpush 0 rZ))) (mk E ix P σ) = mk E ix P σ1 := by
      rw [exec_mk_noNand _ noNand_leafPre, exec_seq, exec_rep]
      have : (exec E (.lnil 0) σ).sc 2 = k := hc2
      rw [this, iter_push 0 rZ k _ (by simp [exec]; omega) (by simp [exec, rZ, hc1]; omega)]
      simp [exec, σ1, acc, map_pos_constL_zero, rZ, hc1]
    have hIS1 := is_exec hnM' hWM e1 ⟨hI, hS⟩
    have hb : ∀ τ, exec E leafBody τ = exec E (.seq (takeC 2 2 12) odoC)
        (exec E termStepC (exec E (.seq (.lnil 0) (.rep 2 (.lpush 0 rZ))) τ)) := fun τ => by
      rw [leafBody, exec_seq, exec_seq]
    rw [hb, e1]
    -- the term
    obtain ⟨sc2, ls2, h2, d2, f2, g2⟩ := exec_termStepC hnM hWM hix hK repA repB a col t e P acc σ1
      ⟨⟨⟨hc0, hc1⟩, hc2, hc3, hc4⟩, hc5, hc6, hc7⟩ hIS1.1 hIS1.2 h43 h44 h45 h46 h47 h48 h49
      (by simp [σ1, h10]) (by simp [σ1, h11]) (by simp [σ1]) (constL_length _ _ _) hcap' hbig
      (le_trans (Nat.add_le_add_left (le_length_leaves _ _ _ _ _ _ _ _ _) _) hM)
    set T := termStep (.gate 0) (2 ^ K) k repA repB a col t (P, acc) e
    have hT : T.2.length = k := length_termStep repA repB a col t P acc (constL_length _ _ _) e
    rw [h2]
    set τ2 := setSL σ1 sc2 ls2
    have hIS2 := is_exec hnM' hWM (c := .seq (.seq (.lnil 0) (.rep 2 (.lpush 0 rZ))) termStepC)
      (τ := mk E ix P σ) (by rw [exec_seq, e1, h2]) ⟨hI, hS⟩
    -- append the output to 
    have hf2 : ∀ r : SR, r.val < 16 ∨ (43 ≤ r.val ∧ r.val ≤ 49) ∨ 53 < r.val → τ2.sc r = σ.sc r :=
      fun r hr => f2 r hr
    have hg2 : ∀ l : LR, l = 10 ∨ l = 11 ∨ (12 ≤ l.val ∧ l.val ≤ 16) ∨ 20 < l.val →
        τ2.ls l = σ.ls l := fun l hl => by
      show ls2 l = _
      have hl' : (10 ≤ l.val ∧ l.val ≤ 16) ∨ 20 < l.val := by
        rcases hl with h | h | h | h
        · subst h; decide
        · subst h; decide
        · omega
        · omega
      rw [g2 l hl']
      simp only [σ1]; rw [Function.update_of_ne (by rintro rfl; revert hl'; decide)]
    obtain ⟨sc3, h3, f3⟩ := exec_takeC (E := E) (n := 2) (lA := 2) (lR := 12) (by decide)
      (T.2.map (pos E ix)) [] L0 τ2 hIS2.1 (by simp [τ2, setSL, d2])
      (by rw [hg2 12 (by decide), hL]) (by rw [hf2 2 (by decide), hc2, List.length_map, hT])
      (by simp [hT]; nlinarith)
    set τ3 : St := setSL τ2 sc3 (Function.update (Function.update τ2.ls 2 []) 12
      (L0 ++ T.2.map (pos E ix)))
    have hf3 : ∀ r : SR, r.val < 16 ∨ (43 ≤ r.val ∧ r.val ≤ 49) ∨ 53 < r.val → sc3 r = σ.sc r :=
      fun r hr => by rw [f3 r (by simp; intro h; subst h; revert hr; decide)]; exact hf2 r hr
    obtain ⟨x', y', z', h4, hi4, hy4, hz4⟩ := exec_odoC (E := E) τ3 x y z
      (by rw [show τ3.sc 2 = sc3 2 from rfl, hf3 2 (by decide), hc2])
      (by rw [show τ3.sc 5 = sc3 5 from rfl, hf3 5 (by decide), hc5])
      (by rw [show τ3.sc 47 = sc3 47 from rfl, hf3 47 (by decide), h47])
      (by rw [show τ3.sc 48 = sc3 48 from rfl, hf3 48 (by decide), h48])
      (by rw [show τ3.sc 49 = sc3 49 from rfl, hf3 49 (by decide), h49]) hy hz
      (by omega) (by nlinarith) (by nlinarith)
    set σ4 := setSL τ3 (Function.update (Function.update (Function.update τ3.sc 47 x') 48 y') 49 z')
      τ3.ls
    have h3' : exec E (takeC 2 2 12) τ2 = τ3 := by rw [h3]; rfl
    have hbody : exec E leafBody (mk E ix P σ) = mk E ix T.1 σ4 := by
      rw [hb, e1, h2, exec_mk_noNand _ noNand_takeOdo, exec_seq, h3', h4]
    have hIS4 := is_exec hnM' hWM hbody ⟨hI, hS⟩
    rw [exec_mk_noNand _ noNand_takeOdo, exec_seq, h3', h4]
    have hs4 : ∀ r : SR, r.val < 16 ∨ (43 ≤ r.val ∧ r.val ≤ 46) ∨ 53 < r.val → σ4.sc r = σ.sc r :=
      fun r hr => by
        simp only [σ4, setSL]
        rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide)]
        exact hf3 r (by omega)
    have hl4 : ∀ l : LR, l = 10 ∨ l = 11 ∨ (12 < l.val ∧ l.val ≤ 16) ∨ 20 < l.val →
        σ4.ls l = σ.ls l := fun l hl => by
      simp only [σ4, τ3, setSL]
      rw [Function.update_of_ne (by rintro rfl; revert hl; decide),
        Function.update_of_ne (by rintro rfl; revert hl; decide)]
      refine hg2 l ?_
      rcases hl with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · right; right; left; omega
      · right; right; right; exact h
    obtain ⟨sc', ls', h', d', f', g'⟩ := iter_leafBody hnM hWM hix hK repA repB a col t j (i + 1)
      T.1 σ4 x' y' z' (L0 ++ T.2.map (pos E ix)) (by omega)
      ⟨⟨⟨by rw [← hc0]; exact hs4 0 (by decide), by rw [← hc1]; exact hs4 1 (by decide)⟩,
        by rw [← hc2]; exact hs4 2 (by decide), by rw [← hc3]; exact hs4 3 (by decide),
        by rw [← hc4]; exact hs4 4 (by decide)⟩, by rw [← hc5]; exact hs4 5 (by decide),
        by rw [← hc6]; exact hs4 6 (by decide), by rw [← hc7]; exact hs4 7 (by decide)⟩
      hIS4.1 hIS4.2 (by rw [hs4 43 (by decide), h43]) (by rw [hs4 44 (by decide), h44])
      (by rw [hs4 45 (by decide), h45]) (by rw [hs4 46 (by decide), h46])
      (by simp [σ4, setSL]) (by simp [σ4, setSL]) (by simp [σ4, setSL]) (by omega) hy4 hz4
      (by rw [hl4 10 (by decide), h10]) (by rw [hl4 11 (by decide), h11])
      (by simp [σ4, τ3, setSL]) (by simp [hT]; nlinarith) hcap' hbig hM
    refine ⟨sc', ls', ?_, ?_, fun r hr => (f' r hr).trans (hs4 r hr),
      fun l hl => (g' l hl).trans (hl4 l hl)⟩
    · rw [h']; rfl
    · rw [d']; simp [leaves, T, acc, List.append_assoc]

end FhatGen

end SigabaNeo.Lattices

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-- **`leaves` over all the terms** (`8` holds `2kN`): the outputs appended to the list `12`. -/
def leavesC : Code := .seq (.zero 47) (.seq (.zero 48) (.seq (.zero 49) (.rep 8 leafBody)))

theorem exec_leavesC (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n)
    {N k K : ℕ} (hk : 0 < k) (hN : 0 < N) (hK : K ≤ k + 1) (repA repB : BI N k → Wire ι)
    (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N) (P : SLP ι) (σ : St) (L0 : List ℕ)
    (hc : CstB (E := E) k K N σ) (h8 : σ.sc 8 = 2 * k * N) (hI : Inv E σ) (hS : ScOK E σ)
    (h43 : σ.sc 43 = a.val) (h44 : σ.sc 44 = col.1.val) (h45 : σ.sc 45 = col.2.val)
    (h46 : σ.sc 46 = t.val) (h10 : σ.ls 10 = repList E ix repA)
    (h11 : σ.ls 11 = repList E ix repB) (hL : σ.ls 12 = L0)
    (hcap : L0.length + 2 * k * N * k ≤ E.C) (hcap' : k + 3 ≤ E.C)
    (hbig : 4 * k * N * k + 2 * N + k + 2 ≤ E.M)
    (hM : E.n + (leaves (.gate 0) (2 ^ K) k repA repB a col t P (enumT N k)).1.length ≤ E.M) :
    ∃ sc' ls', exec E leavesC (mk E ix P σ) =
        mk E ix (leaves (.gate 0) (2 ^ K) k repA repB a col t P (enumT N k)).1 (setSL σ sc' ls') ∧
      ls' 12 = L0 ++ ((leaves (.gate 0) (2 ^ K) k repA repB a col t P (enumT N k)).2.map
        (List.map (pos E ix))).flatten ∧
      (∀ r : SR, r.val < 16 ∨ (43 ≤ r.val ∧ r.val ≤ 46) ∨ 53 < r.val → sc' r = σ.sc r) ∧
      (∀ l : LR, l = 10 ∨ l = 11 ∨ (12 < l.val ∧ l.val ≤ 16) ∨ 20 < l.val → ls' l = σ.ls l) := by
  set σ0 := setSL σ (Function.update (Function.update (Function.update σ.sc 47 0) 48 0) 49 0) σ.ls
  have e0 : exec E (.zero 49) (exec E (.zero 48) (exec E (.zero 47) (mk E ix P σ))) =
      mk E ix P σ0 := rfl
  have hIS0 := is_exec (by omega) hWM (c := .seq (.zero 47) (.seq (.zero 48) (.zero 49))) e0 ⟨hI, hS⟩
  have hs0 : ∀ r : SR, r.val < 47 ∨ 49 < r.val → σ0.sc r = σ.sc r := fun r hr => by
    simp only [σ0, setSL]
    rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide)]
  obtain ⟨⟨⟨hc0, hc1⟩, hc2, hc3, hc4⟩, hc5, hc6, hc7⟩ := hc
  unfold leavesC
  simp only [exec_seq]
  rw [e0, exec_rep, show (mk E ix P σ0).sc 8 = 2 * k * N by
    rw [mk_sc, hs0 8 (by decide), h8]]
  have hall : ((enumT N k).drop 0).take (2 * k * N) = enumT N k := by
    rw [List.drop_zero, List.take_of_length_le (by rw [length_enumT])]
  obtain ⟨sc', ls', h, d, f, g⟩ := iter_leafBody hnM hWM hix hK repA repB a col t (2 * k * N) 0 P
    σ0 0 0 0 L0 (by omega)
    ⟨⟨⟨by rw [← hc0]; exact hs0 0 (by decide), by rw [← hc1]; exact hs0 1 (by decide)⟩,
      by rw [← hc2]; exact hs0 2 (by decide), by rw [← hc3]; exact hs0 3 (by decide),
      by rw [← hc4]; exact hs0 4 (by decide)⟩, by rw [← hc5]; exact hs0 5 (by decide),
      by rw [← hc6]; exact hs0 6 (by decide), by rw [← hc7]; exact hs0 7 (by decide)⟩
    hIS0.1 hIS0.2 (by rw [hs0 43 (by decide), h43]) (by rw [hs0 44 (by decide), h44])
    (by rw [hs0 45 (by decide), h45]) (by rw [hs0 46 (by decide), h46])
    (by simp [σ0, setSL]) (by simp [σ0, setSL]) (by simp [σ0, setSL]) (by ring)
    hk hN
    h10 h11 hL (by nlinarith) hcap' hbig (by rw [hall]; exact hM)
  rw [hall] at h d
  refine ⟨sc', ls', h, d, fun r hr => ?_, g⟩
  rw [f r hr, hs0 r (by omega)]

end FhatGen

end SigabaNeo.Lattices
