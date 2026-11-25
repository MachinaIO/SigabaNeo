import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.Mul

/-!
# The automorphism `σ_k` of `ℤ_{2^K − 1}[X]/(X^N + 1)` on ring words

`autMP : Prog 25` (`0` output, `1` a ring word `a`, `2` a word of length `k ≥ 1` (the index, in
unary), `3` `4` templates of lengths `K`, `N`; scratch `5 … 24`) writes **`autMW N K k a`**
(`run_autMP`), whose ring element is `σ_k(a) = aut N k a` (`decRM_autMW`; `aut` and `autCoeffs`
of `SigabaNeoStd.Lattices.Automorphism.Coeffs`, for every `k ≥ 1`).

The algorithm needs no index arithmetic (`SigabaNeo.Lattices.Algo.NegaG.rhoG_iter_eA`): with
`e₀ = 0` and `e_{j+1} = X^{−k} (e_j + a_j)`, `σ_k(a) = X^{−kN} e_N`. Each round reads the next
coefficient `a_j`, adds it to the first block of `e` while rotating that block out to the top
negated (one `X⁻¹`, `K` shifts of the register), then applies `X⁻¹` `k − 1` more times
(`rhoIP`); finally `X⁻¹` `kN` times. Every `X⁻¹` is `K` register shifts (`rnbK`), so the program
executes `O(N k K)` primitives.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-- Shift the negation of the first bit of `v` into the register `e`. -/
def pnStep : List Bool × List Bool → List Bool × List Bool
  | (e, v) => ((e ++ [!hd v]).tail, v.tail)

theorem pnStep_iter : ∀ (m : ℕ) (e v : List Bool),
    pnStep^[m] (e, v) = ((e ++ notW (takeD m v)).drop m, v.drop m)
  | 0, e, v => by simp [takeD, notW]
  | m + 1, e, v => by
    rw [Function.iterate_succ_apply, pnStep, pnStep_iter m, takeD]
    simp only [notW, List.map_cons, List.drop_tail]
    rw [tail_append_drop]

/-- The abstract round of `σ_k`: (accumulator, stream of `a`). -/
def autStep (K km : ℕ) : List Bool × List Bool → List Bool × List Bool
  | (ev, sa) =>
    ((rhoMW K)^[km] ((ev ++ notW (addMW (takeD K ev) (takeD K sa))).drop K), sa.drop K)

/-- **`σ_k` on ring words modulo `2^K − 1`.** -/
def autMW (N K k : ℕ) (a : List Bool) : List Bool :=
  (rhoMW K)^[k * N] ((autStep K (k - 1))^[N] (zeroW (N * K), a)).1

theorem autStep_iter {N K k : ℕ} (hN : 0 < N) (hk : 0 < k) {a : List Bool}
    (ha : a.length = N * K) : ∀ j, j ≤ N →
    ((autStep K (k - 1))^[j] (zeroW (N * K), a)).1.length = N * K ∧
      ((autStep K (k - 1))^[j] (zeroW (N * K), a)).2 = a.drop (j * K) ∧
      decRM N K ((autStep K (k - 1))^[j] (zeroW (N * K), a)).1 = eA (decRM N K a) k j
  | 0, _ => by
    refine ⟨by simp, by simp, ?_⟩
    apply ext_coefG
    intro i hi
    rw [coefG_decRM _ hi, eA, coefG_zero, Function.iterate_zero_apply]
    simp only [block, zeroW, decM, List.drop_replicate, List.take_replicate]
    rw [show List.replicate (min K (N * K - i * K)) false = zeroW _ from rfl, val_zeroW]; simp
  | j + 1, hj => by
    obtain ⟨h1, h2, h3⟩ := autStep_iter hN hk ha j (by omega)
    rw [Function.iterate_succ_apply']
    generalize (autStep K (k - 1))^[j] (zeroW (N * K), a) = F at h1 h2 h3
    obtain ⟨ev, sa⟩ := F
    simp only at h1 h2 h3
    subst h2
    have hKe : K ≤ ev.length := by rw [h1]; exact Nat.le_mul_of_pos_left K hN
    have hr : takeD K (a.drop (j * K)) = block K j a := takeD_drop_eq_block ha (by omega)
    have hb : (block K j a).length = K := length_block ha (by omega)
    have hX : (ev ++ notW (addMW (takeD K ev) (takeD K (a.drop (j * K))))).drop K =
        ev.drop K ++ notW (addMW (ev.take K) (block K j a)) := by
      rw [List.drop_append_of_le_length hKe, takeD_eq_take hKe, hr]
    have hXl : (ev.drop K ++ notW (addMW (ev.take K) (block K j a))).length = N * K := by
      simp only [List.length_append, List.length_drop, length_notW, length_addMW,
        List.length_take, h1]
      have : K ≤ N * K := Nat.le_mul_of_pos_left K hN
      omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [autStep, length_rhoMW_iter, hX, hXl]
    · simp only [autStep, List.drop_drop]; congr 1; ring
    · simp only [autStep]
      rw [hX, decRM_rhoMW_iter hN hXl, decRM_rhoAdd hN h1 hb, h3, eA,
        ← coefG_decRM (N := N) a (show j < N by omega),
        ← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hk]

/-- **`autMW` computes `σ_k`.** -/
theorem decRM_autMW {N K k : ℕ} (hk : 0 < k) {a : List Bool} (ha : a.length = N * K) :
    decRM N K (autMW N K k a) = SigabaNeo.Lattices.aut N k (decRM N K a) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ext_coefG fun i hi => absurd hi (Nat.not_lt_zero _)
  obtain ⟨h1, -, h3⟩ := autStep_iter hN hk ha N le_rfl
  rw [autMW, decRM_rhoMW_iter hN h1, h3, rhoG_iter_eA hN]

theorem length_autMW (N K k : ℕ) (a : List Bool) (hN : 0 < N) :
    (autMW N K k a).length = N * K := by
  have : ∀ j, ((autStep K (k - 1))^[j] (zeroW (N * K), a)).1.length = N * K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      generalize (autStep K (k - 1))^[j] (zeroW (N * K), a) = F at ih
      obtain ⟨ev, sa⟩ := F
      simp only at ih
      have hKe : K ≤ ev.length := by rw [ih]; exact Nat.le_mul_of_pos_left K hN
      simp only [autStep, length_rhoMW_iter, List.length_drop, List.length_append, length_notW,
        length_addMW, length_takeD]
      omega
  simp [autMW, this]

namespace Prog

open scoped Prog

/-! ### Subprograms -/

/-- `0 := (s 0 ++ ¬(takeD |s 2| (s 1))).drop |s 2|`, `1 := (s 1).drop |s 2|` (scratch `3` `4`). -/
def pushNP : Prog 5 := forN 3 2 (pp 1 4 ⨾ ifBit 4 (sin false 0) (sin true 0) ⨾ clr 4)

theorem run_pushNP (s : Store 5) (h3 : s 3 = []) (h4 : s 4 = []) :
    run pushNP s = Function.update (Function.update s 0
      ((s 0 ++ notW (takeD (s 2).length (s 1))).drop (s 2).length)) 1 ((s 1).drop (s 2).length) := by
  have h := run_forN 3 2 (pp 1 4 ⨾ ifBit 4 (sin false 0) (sin true 0) ⨾ clr 4)
    (fun a => Function.update (Function.update s 0 a.1) 1 a.2) pnStep (fun a w => by
      obtain ⟨e, v⟩ := a
      funext t
      cases hh : hd v <;> fin_cases t <;> simp [pnStep, hh, h4, run_ifBit]) (s 0, s 1) s
    (by funext t; fin_cases t <;> simp)
  rw [pushNP, h, pnStep_iter]
  funext t; fin_cases t <;> simp [h3]

theorem run_pushNP_map {u : Fin 5 → Fin k} (hu : Function.Injective u) (s : Store k)
    (h3 : s (u 3) = []) (h4 : s (u 4) = []) :
    run (map u pushNP) s = Function.update (Function.update s (u 0)
      ((s (u 0) ++ notW (takeD (s (u 2)).length (s (u 1)))).drop (s (u 2)).length)) (u 1)
      ((s (u 1)).drop (s (u 2)).length) := by
  rw [run_map hu, run_pushNP _ h3 h4, extend_update hu, extend_update hu, extend_comp_self]; rfl

def vRI : Fin 4 → Fin 6 := ![0, 2, 4, 5]
theorem vRI_inj : Function.Injective vRI := by decide

/-- In place: `0 := (rhoMW |s 2|)^[|s 1|] (s 0)` (scratch `3 … 5`). -/
def rhoIP : Prog 6 := forN 3 1 (map vRI rnbK)

theorem run_rhoIP (s : Store 6) (h3 : s 3 = []) (h4 : s 4 = []) (h5 : s 5 = []) :
    run rhoIP s = Function.update s 0 ((rhoMW (s 2).length)^[(s 1).length] (s 0)) := by
  have h := run_forN 3 1 (map vRI rnbK) (fun e => Function.update s 0 e) (rhoMW (s 2).length)
    (fun e w => by
      rw [run_rnbK_map vRI_inj _ (by simp [vRI, h4]) (by simp [vRI, h5])]
      funext t; fin_cases t <;> simp [vRI]) (s 0) s (by funext t; fin_cases t <;> simp)
  rw [rhoIP, h]
  funext t; fin_cases t <;> simp [h3]

theorem run_rhoIP_map {u : Fin 6 → Fin k} (hu : Function.Injective u) (s : Store k)
    (h3 : s (u 3) = []) (h4 : s (u 4) = []) (h5 : s (u 5) = []) :
    run (map u rhoIP) s =
      Function.update s (u 0) ((rhoMW (s (u 2)).length)^[(s (u 1)).length] (s (u 0))) :=
  run_map_eq_update hu _ s 0 _ (run_rhoIP _ h3 h4 h5)

/-! ### The program -/

def vMa : Fin 5 → Fin 25 := ![6, 7, 14, 15, 3]
def vMe : Fin 5 → Fin 25 := ![10, 8, 14, 15, 3]
def vAdA : Fin 12 → Fin 25 := ![9, 8, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24]
def vPn : Fin 5 → Fin 25 := ![5, 9, 3, 13, 14]
def vRk : Fin 6 → Fin 25 := ![5, 11, 3, 13, 15, 14]
def vRf : Fin 6 → Fin 25 := ![5, 2, 3, 13, 15, 14]
theorem vMa_inj : Function.Injective vMa := by decide
theorem vMe_inj : Function.Injective vMe := by decide
theorem vAdA_inj : Function.Injective vAdA := by decide
theorem vPn_inj : Function.Injective vPn := by decide
theorem vRk_inj : Function.Injective vRk := by decide
theorem vRf_inj : Function.Injective vRf := by decide

/-- One round. Tapes: `5` the accumulator `e`, `6` the stream of `a`, `7` the block `a_j`, `8` the
first block of `e`, `9` their sum, `10` a copy of `e`, `11` a word of length `k − 1`, `12` the
counter, `13 … 15` counters and bits, `16 … 24` the adder's scratch. -/
def autBody : Prog 25 :=
  cp 7 3 ⨾ map vMa mvP ⨾ cp 8 3 ⨾ cp 10 5 ⨾ map vMe mvP ⨾ clr 10 ⨾ map vAdA addMP ⨾
    map vPn pushNP ⨾ cp 11 2 ⨾ tl 11 ⨾ map vRk rhoIP ⨾ clr 7 ⨾ clr 8 ⨾ clr 9 ⨾ clr 11

/-- **`σ_k`** (`k ≥ 1` the length of tape `2`). -/
def autMP : Prog 25 :=
  cp 5 1 ⨾ setZero 5 ⨾ cp 6 1 ⨾ forN 12 4 autBody ⨾ forN 12 4 (map vRf rhoIP) ⨾ cp 0 5 ⨾ clr 5 ⨾
    clr 6

def autG (s : Store 25) : List Bool × List Bool → Store 25
  | (ev, sa) => Function.update (Function.update s 5 ev) 6 sa

set_option linter.unusedSimpArgs false in
theorem run_autBody {K : ℕ} (s : Store 25) (hs : ∀ i : Fin 25, 5 ≤ i.val → i ≠ 12 → s i = [])
    (hK : (s 3).length = K) (a) (ha : K ≤ a.1.length) (w : List Bool) :
    run autBody (Function.update (autG s a) 12 w) =
      Function.update (autG s (autStep K ((s 2).length - 1) a)) 12 w := by
  obtain ⟨ev, sa⟩ := a
  simp only at ha
  have hA : (addMW (takeD K ev) (takeD K sa)).length = K := by simp
  simp only [autBody, run_seq, run_copy, run_clear, run_tail]
  rw [run_mvP_map vMa_inj _ ?_ ?_, run_mvP_map vMe_inj _ ?_ ?_, run_addMP_map vAdA_inj _ ?_ ?_,
    run_pushNP_map vPn_inj _ ?_ ?_, run_rhoIP_map vRk_inj _ ?_ ?_ ?_]
  · funext t
    simp only [autG, autStep]
    fin_cases t <;> simp [vMa, vMe, vAdA, vPn, vRk, hK, hs, drop_append_of_length, takeD_of_length' hA]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [vMa, vMe, vAdA, vPn, vRk, autG, hs] at hi ⊢)
    | simp [vMa, vMe, vAdA, vPn, vRk, autG, hs, hK, drop_append_of_length]

set_option linter.unusedSimpArgs false in
theorem run_autMP {K N : ℕ} (s : Store 25) (hs : ∀ i : Fin 25, 5 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hx : (s 1).length = N * K) (hN0 : 0 < N) :
    run autMP s = Function.update s 0 (autMW N K (s 2).length (s 1)) := by
  have hs' : ∀ i : Fin 25, 5 ≤ i.val → i ≠ 12 → s i = [] := fun i hi _ => hs i hi
  have hKN : K ≤ N * K := Nat.le_mul_of_pos_left K hN0
  have hloop := run_loop_iter 12 autBody (autG s) (autStep K ((s 2).length - 1))
    (fun a => a.1.length = N * K) (fun a w ha => run_autBody s hs' hK a (by rw [ha]; exact hKN) w)
    (fun a ha => by
      obtain ⟨ev, sa⟩ := a
      simp only at ha
      simp only [autStep, length_rhoMW_iter, List.length_drop, List.length_append, length_notW,
        length_addMW, length_takeD, ha]
      omega)
    (s 4) (zeroW (N * K), s 1) (by simp [zeroW])
  have e0 : run (cp 12 4) (run (cp 6 1) (run (setZero 5) (run (cp 5 1) s))) =
      Function.update (autG s (zeroW (N * K), s 1)) 12 (s 4) := by
    funext t; simp only [run_copy, run_setZero, autG]; fin_cases t <;> simp [hx, zeroW]
  simp only [autMP, forN, run_seq]
  rw [e0, hloop, hN]
  generalize hF : (autStep K ((s 2).length - 1))^[N] (zeroW (N * K), s 1) = F
  obtain ⟨ev, sa⟩ := F
  have hres : autMW N K (s 2).length (s 1) = ((rhoMW K)^[(s 2).length])^[N] ev := by
    rw [autMW, Function.iterate_mul, hF]
  have e1 : run (cp 12 4) (Function.update (autG s (ev, sa)) 12 []) =
      Function.update (autG s (ev, sa)) 12 (s 4) := by
    funext t; simp only [run_copy, autG]; fin_cases t <;> simp
  rw [e1, run_loop_iter 12 (map vRf rhoIP) (fun e => autG s (e, sa)) (rhoMW K)^[(s 2).length]
    (fun _ => True) (fun e w _ => by
      rw [run_rhoIP_map vRf_inj _ (by simp [vRf, autG, hs]) (by simp [vRf, autG, hs])
        (by simp [vRf, autG, hs])]
      funext t; fin_cases t <;> simp [vRf, autG, hK]) (fun _ _ => trivial) (s 4) ev trivial, hN,
    hres]
  funext t; simp only [run_copy, run_clear, autG]; fin_cases t <;> simp [hs]

theorem run_autMP_map {u : Fin 25 → Fin k} (hu : Function.Injective u) {K N : ℕ} (s : Store k)
    (hs : ∀ i : Fin 25, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) (hN0 : 0 < N) :
    run (map u autMP) s = Function.update s (u 0) (autMW N K (s (u 2)).length (s (u 1))) :=
  run_map_eq_update hu _ s 0 _ (run_autMP (s ∘ u) hs hK hN hx hN0)

theorem noGrow_autMP : autMP.NoGrow := rfl
theorem wf_autMP : autMP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
