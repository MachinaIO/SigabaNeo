import SigabaNeo.Lib.Lattices.ProgAlgo.RingProgs

/-!
# Binary digits, monomials and constants of ring words as tape programs

* `digitRWP : Prog 31` (`0` output, `1` a ring word `w`, `2` a word of length `i` (the digit),
  `3` `4` templates of lengths `K`, `N`; scratch `5 … 30`): **`digitRW N K i w`** (`run_digitRWP`):
  `i` block-wise shifts towards the least significant bit (`shrB`), then the block-wise word of the
  first bit (`dig0B`).
* `monoWP : Prog 12` (`0` output, `1` a word `v` of length `K`, `2` a word of length `j`, `3` `4`
  `5` templates of lengths `K`, `N`, `N · K`; scratch `6 … 11`): **`monoW N K j v`**
  (`run_monoWP`); with a blank tape `2` it is **`constW N K v`** (`run_monoWP_const`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Encode

variable {k : ℕ}

/-- `m` shifts of a word towards its first bit, filling with `false`. -/
def shrN (m : ℕ) (u : List Bool) : List Bool := (u ++ List.replicate m false).drop m

@[simp] theorem length_shrN (m : ℕ) (u : List Bool) : (shrN m u).length = u.length := by
  simp [shrN]

theorem shrN_succ (m : ℕ) (u : List Bool) : (shrN m u ++ [false]).tail = shrN (m + 1) u := by
  have hle : m ≤ (u ++ List.replicate m false).length := by simp
  rw [shrN, shrN, List.replicate_succ', ← List.append_assoc, ← List.drop_append_of_le_length hle,
    List.tail_drop]

theorem hd_shrN (m : ℕ) (u : List Bool) : hd (shrN m u) = u.getD m false := by
  rw [shrN]
  rcases lt_or_ge m u.length with h | h
  · rw [List.drop_append_of_le_length h.le]
    obtain ⟨x, l, hl⟩ : ∃ x l, u.drop m = x :: l := by
      cases hd : u.drop m with
      | nil => simp at hd; omega
      | cons x l => exact ⟨x, l, rfl⟩
    rw [hl, List.cons_append, hd_cons, List.getD_eq_getElem _ _ h]
    have := congrArg List.head? hl
    rw [List.head?_drop] at this
    simp only [List.head?_cons] at this
    rw [List.getElem?_eq_getElem h] at this
    exact (Option.some.inj this).symm
  · rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append, List.getD_eq_default _ _ h,
      List.drop_replicate]
    cases m - (m - u.length) <;> rfl

theorem serF_dig0 (c : Bool) (x y : List Bool) :
    serF (fun x _ c => (x && c, false)) c x y =
      match x with
      | [] => []
      | b :: xs => (b && c) :: List.replicate xs.length false := by
  induction x generalizing c y with
  | nil => rfl
  | cons b xs ih =>
    simp only [serF, ih]
    cases xs <;> simp [List.replicate_succ]

namespace Prog

open scoped Prog

/-! ### Block programs -/

/-- One shift towards the first bit. -/
def shrB : Prog 18 := cp 0 1 ⨾ sin false 0

theorem blockSpec_shr (K : ℕ) : BlockSpec K shrB (fun x _ => (x ++ [false]).tail) := by
  intro t _ _ _
  simp only [shrB, run_seq, run_copy, run_sin, Function.update_self, Function.update_idem]

/-- The first bit, then zeros. -/
def dig0B : Prog 18 := zipB (fun x _ c => (x && c, false)) true

theorem blockSpec_dig0 (K : ℕ) : BlockSpec K dig0B (fun x _ => bitW K (hd x)) := by
  intro t ht h1 _
  rw [dig0B, run_zipB _ _ t ht, serF_dig0, ← h1]
  cases t 1 with
  | nil => rfl
  | cons b xs => simp [bitW, zeroW]

/-! ### Digits -/

def vShr : Fin 28 → Fin 31 := ![7, 5, 1, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
  21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
def vDig : Fin 28 → Fin 31 := ![0, 5, 1, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
  21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
theorem vShr_inj : Function.Injective vShr := by decide
theorem vDig_inj : Function.Injective vDig := by decide

/-- Tapes `5` the shifted word, `6` the counter, `7` a result; `8 … 30` scratch. -/
def digitRWP : Prog 31 :=
  cp 5 1 ⨾ forN 6 2 (map vShr (bzip shrB) ⨾ cp 5 7 ⨾ clr 7) ⨾ map vDig (bzip dig0B) ⨾ clr 5

theorem shr_pass {N K : ℕ} {w : List Bool} (hw : w.length = N * K) (m : ℕ) :
    concatN N (fun t => (block K t (concatN N (fun t => shrN m (block K t w))) ++ [false]).tail) =
      concatN N (fun t => shrN (m + 1) (block K t w)) := by
  apply concatN_congr
  intro t ht
  rw [block_concatN (fun i hi => by rw [length_shrN, length_block hw hi])]
  simp only [ht, ↓reduceIte, shrN_succ]

set_option linter.unusedSimpArgs false in
theorem run_digitRWP {K N i : ℕ} (s : Store 31) (hs : ∀ j : Fin 31, 5 ≤ j.val → s j = [])
    (hi : (s 2).length = i) (hK : (s 3).length = K) (hN : (s 4).length = N)
    (hw : (s 1).length = N * K) :
    run digitRWP s = Function.update s 0 (digitRW N K i (s 1)) := by
  have hc : ∀ j : Fin 31, 5 ≤ j.val → j ≠ 6 → s j = [] := fun j hj _ => hs j hj
  have hlenW : ∀ m, (concatN N (fun t => shrN m (block K t (s 1)))).length = N * K := fun m =>
    length_concatN fun t ht => by rw [length_shrN, length_block hw ht]
  have hloop := run_forN 6 2 (map vShr (bzip shrB) ⨾ cp 5 7 ⨾ clr 7)
    (fun m => Function.update s 5 (concatN N (fun t => shrN m (block K t (s 1))))) (· + 1)
    (fun m w => by
      simp only [run_seq, run_copy, run_clear]
      rw [run_bzip_map vShr_inj (N := N) (blockSpec_shr K) (fun x _ hx _ => by simp [hx]) _ ?_ ?_
        ?_ ?_ ?_]
      · funext t; fin_cases t <;> simp [vShr, hc, shr_pass hw]
      all_goals first
        | (intro i hi; fin_cases i <;> simp [vShr, hc] at hi ⊢)
        | simp [vShr, hc, hK, hN, hw, hlenW]) 0 (Function.update s 5 (s 1)) (by
      have h0 : concatN N (fun t => shrN 0 (block K t (s 1))) = s 1 := by
        rw [← concatN_block hw]; apply concatN_congr; intro t _; simp [shrN, concatN_block hw]
      rw [h0])
  simp only [digitRWP, run_seq, run_copy, run_clear]
  rw [hloop]
  have h2 : Function.update s 5 (s 1) 2 = s 2 := by simp
  simp only [h2, hi, Function.iterate_add_apply, Function.iterate_fixed, zero_add]
  have hit : ∀ n, (fun m : ℕ => m + 1)^[n] 0 = n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]
  rw [hit]
  rw [run_bzip_map vDig_inj (N := N) (blockSpec_dig0 K) (fun x _ _ _ => length_bitW K _) _ ?_ ?_
    ?_ ?_ ?_]
  · funext t
    fin_cases t <;> simp [vDig, hc, hs 6 (by decide), digitRW]
    apply concatN_congr
    intro t ht
    rw [block_concatN (fun j hj => by rw [length_shrN, length_block hw hj])]
    simp only [ht, ↓reduceIte, hd_shrN, List.getD_eq_getElem?_getD]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [vDig, hc] at hi ⊢)
    | simp [vDig, hc, hK, hN, hw, hlenW]

/-! ### Monomials and constants -/

def mvS : Fin 5 → Fin 12 := ![7, 0, 8, 9, 3]
theorem mvS_inj : Function.Injective mvS := by decide

/-- One block: the word `v` if the countdown `6` is blank (then the countdown restarts from `N`,
never to reach blank again), zeros otherwise. -/
def monoBody : Prog 12 :=
  ifBlank 6 (cp 7 1 ⨾ map mvS mvP ⨾ cp 6 4) (cp 7 11 ⨾ map mvS mvP) ⨾ tl 6 ⨾ clr 7

/-- Tapes `6` the countdown, `7` a stream, `8` a bit, `9` `10` counters, `11` zero. -/
def monoWP : Prog 12 := cp 0 5 ⨾ cp 6 2 ⨾ cp 11 3 ⨾ setZero 11 ⨾ forN 10 4 monoBody ⨾ clr 6 ⨾ clr 11

def monoStep (K : ℕ) (v tN : List Bool) : List Bool × List Bool → List Bool × List Bool
  | (J, out) => (if J = [] then tN.tail else J.tail,
      (out ++ (if J = [] then takeD K v else List.replicate K false)).drop K)

theorem monoStep_iter {K N : ℕ} (v tN : List Bool) (hN : tN.length = N) :
    ∀ m, m ≤ N → ∀ J out, ((monoStep K v tN)^[m] (J, out)).2 =
      (out ++ concatN m (fun t => if t = J.length then takeD K v else List.replicate K false)).drop
        (m * K)
  | 0, _, J, out => by simp [concatN]
  | m + 1, hm, J, out => by
    rw [Function.iterate_succ_apply, concatN_succ']
    have hu : (if J = [] then takeD K v else List.replicate K false).length = K := by
      split_ifs <;> simp
    rw [monoStep, monoStep_iter v tN hN m (by omega)]
    have := drop_append_drop out (if J = [] then takeD K v else List.replicate K false)
      (concatN m (fun t => if t = (if J = [] then tN.tail else J.tail).length then takeD K v
        else List.replicate K false))
    rw [hu, length_concatN (K := K) (fun t _ => by split_ifs <;> simp)] at this
    rw [this, Nat.succ_mul, Nat.add_comm (m * K)]
    congr 3
    · rcases J with _ | ⟨x, J⟩ <;> simp
    · apply concatN_congr
      intro t ht
      rcases J with _ | ⟨x, J⟩
      · simp only [↓reduceIte, List.length_tail, hN, List.length_nil]
        simp only [show ¬t = N - 1 by omega, show ¬t + 1 = 0 by omega, ↓reduceIte]
      · simp

set_option linter.unusedSimpArgs false in
theorem run_monoWP {K N j : ℕ} (s : Store 12) (hs : ∀ i : Fin 12, 6 ≤ i.val → s i = [])
    (hv : (s 1).length = K) (hj : (s 2).length = j) (hK : (s 3).length = K) (hN : (s 4).length = N)
    (hNK : (s 5).length = N * K) :
    run monoWP s = Function.update s 0 (monoW N K j (s 1)) := by
  have hc : ∀ i : Fin 12, 6 ≤ i.val → i ≠ 10 → s i = [] := fun i hi _ => hs i hi
  let G : List Bool × List Bool → Store 12 := fun a =>
    Function.update (Function.update (Function.update s 11 (List.replicate K false)) 6 a.1) 0 a.2
  have hloop := run_forN 10 4 monoBody G (monoStep K (s 1) (s 4)) (fun a w => by
      obtain ⟨J, out⟩ := a
      simp only [monoBody, run_seq, run_ifBlank, run_copy, run_tail, run_clear]
      by_cases hJ : J = []
      · have : (Function.update (G (J, out)) 10 w) 6 = [] := by simp [G, hJ]
        simp only [this, ↓reduceIte]
        rw [run_mvP_map mvS_inj _ ?_ ?_]
        · funext t; fin_cases t <;> simp [G, mvS, monoStep, hJ, hK, hc]
        all_goals simp [G, mvS, hc]
      · have : (Function.update (G (J, out)) 10 w) 6 ≠ [] := by simp [G, hJ]
        simp only [this, ↓reduceIte]
        rw [run_mvP_map mvS_inj _ ?_ ?_]
        · funext t; fin_cases t <;> simp [G, mvS, monoStep, hJ, hK, hc, takeD_of_length']
        all_goals simp [G, mvS, hc]) (s 2, s 5) (Function.update (G (s 2, s 5)) 10 (s 10))
      (by simp [G])
  have e0 : run (cp 0 5 ⨾ cp 6 2 ⨾ cp 11 3 ⨾ setZero 11) s =
      Function.update (G (s 2, s 5)) 10 (s 10) := by
    funext t; simp only [run_seq, run_copy, run_setZero]; fin_cases t <;> simp [G, hK]
  have hsplit : run monoWP s = run (clr 6 ⨾ clr 11)
      (run (forN 10 4 monoBody) (run (cp 0 5 ⨾ cp 6 2 ⨾ cp 11 3 ⨾ setZero 11) s)) := rfl
  rw [hsplit, e0, hloop]
  have h4 : Function.update (G (s 2, s 5)) 10 (s 10) 4 = s 4 := by simp [G]
  rw [h4, hN]
  have hres := monoStep_iter (K := K) (s 1) (s 4) hN N le_rfl (s 2) (s 5)
  rw [hj, drop_append_of_length hNK] at hres
  generalize hF : (monoStep K (s 1) (s 4))^[N] (s 2, s 5) = F at hres
  obtain ⟨J, out⟩ := F
  simp only at hres
  funext t
  fin_cases t <;> simp [G, hc, hs 10 (by decide), hres, monoW, takeD_of_length' hv, zeroW]

/-- With a blank tape `2`, `monoWP` writes `constW N K v`. -/
theorem run_monoWP_const {K N : ℕ} (s : Store 12) (hs : ∀ i : Fin 12, 6 ≤ i.val → s i = [])
    (hv : (s 1).length = K) (h2 : s 2 = []) (hK : (s 3).length = K) (hN : (s 4).length = N)
    (hNK : (s 5).length = N * K) :
    run monoWP s = Function.update s 0 (constW N K (s 1)) :=
  run_monoWP s hs hv (by rw [h2]; rfl) hK hN hNK

theorem noGrow_digitRWP : digitRWP.NoGrow := rfl
theorem noGrow_monoWP : monoWP.NoGrow := rfl
theorem wf_digitRWP : digitRWP.WF := wf_of_wfB (by decide)
theorem wf_monoWP : monoWP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
