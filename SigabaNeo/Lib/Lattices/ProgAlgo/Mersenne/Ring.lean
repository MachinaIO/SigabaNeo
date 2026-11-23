import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.Residue
import SigabaNeo.Lib.Lattices.ProgAlgo.RingProgs

/-!
# Ring words modulo `2^K − 1` as tape programs: additive operations, `X⁻ʲ`, scalars, `2^{−j}`

A ring word has `N` blocks of `K` bits, read by `SigabaNeo.Lattices.Algo.decRM` in
`ℤ_{2^K − 1}[X]/(X^N + 1)`. Templates (tapes holding words of lengths `K`, `N`, …) give the sizes.

* `addRMP`, `subRMP : Prog 28` (layout of `bzip`: `0` output, `1` `2` operands, `3` `4` templates
  `K`, `N`; scratch `5 … 27`): **`addRMW N K`**, **`subRMW N K`** (`run_addRMP`, `run_subRMP`).
* `notP : Prog 11` (`SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.Residue`) negates a whole ring word
  (`decRM_notW`).
* `rnbK : Prog 4` (`0` a register, `1` a template of length `K`; scratch `2` `3`): in place,
  **`rhoMW K`**, i.e. `X⁻¹` (`run_rnbK`, `decRM_rhoMW`): `K` rotations by one bit, each negating the
  bit moved to the top, so `O(K)` primitives.
* `rhoJP : Prog 7` (`0` output, `1` the word, `2` a template of length `j`, `3` of length `K`;
  scratch `4 … 6`): **`(rhoMW K)^[j]`**, the multiplication by the monomial `X^{−j}`
  (`run_rhoJP`, `decRM_rhoMW_iter`: `rhoG^[j]`, `= xInvG^j * ·`; `X^j = X^{−(2N − j)}`, and
  `−X^j` with `notP`).
* `scRMP : Prog 29` (`0` output, `1` a ring word `x`, `2` a residue word `r`, `3` `4` templates
  `K`, `N`; scratch `5 … 28`): **`scRMW N K (takeD K r) x`**, `r · x` (`run_scRMP`,
  `decRM_scRMW`).
* `rotBP : Prog 30` (`0` output, `1` a ring word, `2` a template of length `j`, `3` `4` templates
  `K`, `N`; scratch `5 … 29`): **`rotBW N K j x`**, every coefficient times `2^{−j}`
  (`run_rotBP`, `decRM_rotBW`: `W⁻¹ = 2^{−b}` with `j = b`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-! ### `X⁻¹` on words -/

/-- Rotate a register by one bit, negating the bit moved to the top. -/
def rnb (e : List Bool) : List Bool := (e ++ [!hd e]).tail

/-- `X⁻¹` on a ring word: `K` steps of `rnb`. -/
def rhoMW (K : ℕ) (e : List Bool) : List Bool := rnb^[K] e

@[simp] theorem length_rnb (e : List Bool) : (rnb e).length = e.length := by simp [rnb]

@[simp] theorem length_rhoMW (K : ℕ) (e : List Bool) : (rhoMW K e).length = e.length := by
  unfold rhoMW
  induction K generalizing e with
  | zero => rfl
  | succ K ih => rw [Function.iterate_succ_apply, ih, length_rnb]

@[simp] theorem length_rhoMW_iter (K j : ℕ) (e : List Bool) : ((rhoMW K)^[j] e).length = e.length := by
  induction j generalizing e with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, length_rhoMW]

theorem rnb_iter : ∀ (m : ℕ) (e : List Bool), m ≤ e.length →
    rnb^[m] e = e.drop m ++ notW (e.take m)
  | 0, e, _ => by simp [notW]
  | m + 1, e, h => by
    rw [Function.iterate_succ_apply', rnb_iter m e (by omega)]
    obtain ⟨b, l, hl⟩ : ∃ b l, e.drop m = b :: l := by
      cases hd : e.drop m with
      | nil => simp at hd; omega
      | cons b l => exact ⟨b, l, rfl⟩
    have hb : e.take (m + 1) = e.take m ++ [b] := by
      rw [List.take_add_one]
      have : e[m]? = some b := by rw [show e[m]? = (e.drop m).head? by simp, hl]; rfl
      rw [this]; rfl
    have hd' : e.drop (m + 1) = l := by rw [← List.drop_drop, hl]; rfl
    rw [hl, hd', hb, rnb]
    simp [notW]

theorem rhoMW_eq {K : ℕ} {e : List Bool} (h : K ≤ e.length) :
    rhoMW K e = e.drop K ++ notW (e.take K) := rnb_iter K e h

/-- **`rhoMW` is `X⁻¹`.** -/
theorem decRM_rhoMW {N K : ℕ} (hN : 0 < N) {e : List Bool} (he : e.length = N * K) :
    decRM N K (rhoMW K e) = rhoG (decRM N K e) := by
  rw [rhoMW_eq (by rw [he]; exact Nat.le_mul_of_pos_left K hN), decRM_rho hN he]

theorem decRM_rhoMW_iter {N K : ℕ} (hN : 0 < N) {e : List Bool} (he : e.length = N * K) :
    ∀ j, decRM N K ((rhoMW K)^[j] e) = rhoG^[j] (decRM N K e)
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', decRM_rhoMW hN (by simp [he]),
      decRM_rhoMW_iter hN he j]

/-- **The monomial `X^{−j}`**: `(rhoMW K)^[j]` multiplies by `xInvG^j` (`xInvG ^ (2N) = 1`). -/
theorem decRM_rhoMW_iter_mul {N K : ℕ} (hN : 0 < N) {e : List Bool} (he : e.length = N * K)
    (j : ℕ) : decRM N K ((rhoMW K)^[j] e) = xInvG _ N ^ j * decRM N K e := by
  rw [decRM_rhoMW_iter hN he, rhoG_iter_eq_mul]

/-- `2^{−j}` on every coefficient, iterated. -/
theorem rotBW_succ {N K : ℕ} {x : List Bool} (hx : x.length = N * K) (j : ℕ) :
    concatN N (fun i => rot1 (block K i (rotBW N K j x))) = rotBW N K (j + 1) x := by
  apply concatN_congr
  intro i hi
  rw [rotBW, block_concatN (fun t ht => by rw [length_rot1_iter, length_block hx ht]),
    mIfT hi, ← Function.iterate_succ_apply' rot1]

namespace Prog

open scoped Prog

/-! ### Addition, subtraction -/

/-- `0 := addRMW N K (s 1) (s 2)`. -/
def addRMP : Prog 28 := bzip addMB
/-- `0 := subRMW N K (s 1) (s 2)`. -/
def subRMP : Prog 28 := bzip subMB

theorem run_addRMP {K N : ℕ} (s : Store 28) (hs : BzClean s) (hK : (s 3).length = K)
    (hN : (s 4).length = N) (hx : (s 1).length = N * K) (hy : (s 2).length = N * K) :
    run addRMP s = Function.update s 0 (addRMW N K (s 1) (s 2)) :=
  run_bzip (blockSpec_addMB K) (fun x y hx _ => by simp [hx]) s hs hK hN hx hy

theorem run_subRMP {K N : ℕ} (s : Store 28) (hs : BzClean s) (hK : (s 3).length = K)
    (hN : (s 4).length = N) (hx : (s 1).length = N * K) (hy : (s 2).length = N * K) :
    run subRMP s = Function.update s 0 (subRMW N K (s 1) (s 2)) :=
  run_bzip (blockSpec_subMB K) (fun x y hx _ => by simp [hx]) s hs hK hN hx hy

theorem run_addRMP_map {u : Fin 28 → Fin k} (hu : Function.Injective u) {K N : ℕ} (s : Store k)
    (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) (hy : (s (u 2)).length = N * K) :
    run (map u addRMP) s = Function.update s (u 0) (addRMW N K (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_addRMP (s ∘ u) hs hK hN hx hy)

theorem run_subRMP_map {u : Fin 28 → Fin k} (hu : Function.Injective u) {K N : ℕ} (s : Store k)
    (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) (hy : (s (u 2)).length = N * K) :
    run (map u subRMP) s = Function.update s (u 0) (subRMW N K (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_subRMP (s ∘ u) hs hK hN hx hy)

/-! ### `X⁻¹` in place -/

/-- `K` times: copy the first bit of the register `0` to `3`, shift its negation in at the end. -/
def rnbK : Prog 4 := forN 2 1 (takeHead 3 0 ⨾ ifBit 3 (sin false 0) (sin true 0) ⨾ clr 3)

theorem run_rnbK (s : Store 4) (h2 : s 2 = []) (h3 : s 3 = []) :
    run rnbK s = Function.update s 0 (rhoMW (s 1).length (s 0)) := by
  have h := run_forN 2 1 (takeHead 3 0 ⨾ ifBit 3 (sin false 0) (sin true 0) ⨾ clr 3)
    (fun e => Function.update s 0 e) rnb (fun e w => by
      funext t
      cases hh : hd e <;> fin_cases t <;> simp [rnb, hh, h3, run_ifBit]) (s 0) s (by funext t; fin_cases t <;> simp)
  rw [rnbK, h]
  funext t; fin_cases t <;> simp [h2, rhoMW]

theorem run_rnbK_map {u : Fin 4 → Fin k} (hu : Function.Injective u) (s : Store k)
    (h2 : s (u 2) = []) (h3 : s (u 3) = []) :
    run (map u rnbK) s = Function.update s (u 0) (rhoMW (s (u 1)).length (s (u 0))) :=
  run_map_eq_update hu _ s 0 _ (run_rnbK _ h2 h3)

def vRj : Fin 4 → Fin 7 := ![0, 3, 5, 6]
theorem vRj_inj : Function.Injective vRj := by decide

/-- **The monomial `X^{−j}`**: `0 := (rhoMW K)^[|s 2|] (s 1)` with `K = |s 3|`. -/
def rhoJP : Prog 7 := cp 0 1 ⨾ forN 4 2 (map vRj rnbK)

theorem run_rhoJP (s : Store 7) (hs : ∀ i : Fin 7, 4 ≤ i.val → s i = []) :
    run rhoJP s = Function.update s 0 ((rhoMW (s 3).length)^[(s 2).length] (s 1)) := by
  have h := run_forN 4 2 (map vRj rnbK) (fun e => Function.update s 0 e) (rhoMW (s 3).length)
    (fun e w => by
      rw [run_rnbK_map vRj_inj _ (by simp [vRj, hs 5 (by decide)]) (by simp [vRj, hs 6 (by decide)])]
      funext t; fin_cases t <;> simp [vRj]) (s 1) (Function.update s 0 (s 1))
    (by funext t; fin_cases t <;> simp)
  rw [rhoJP, run_seq, run_copy, h]
  funext t; fin_cases t <;> simp [hs 4 (by decide)]

theorem run_rhoJP_map {u : Fin 7 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 7, 4 ≤ i.val → s (u i) = []) :
    run (map u rhoJP) s =
      Function.update s (u 0) ((rhoMW (s (u 3)).length)^[(s (u 2)).length] (s (u 1))) :=
  run_map_eq_update hu _ s 0 _ (run_rhoJP _ hs)

/-! ### Residue times ring word -/

def vScR : Fin 9 → Fin 29 := ![5, 2, 1, 3, 4, 6, 7, 8, 9]
def vScM : Fin 28 → Fin 29 := ![0, 1, 5, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
  20, 21, 22, 23, 24, 25, 26, 27, 28]
theorem vScR_inj : Function.Injective vScR := by decide
theorem vScM_inj : Function.Injective vScM := by decide

/-- **Residue times ring word**: `N` copies of the residue (`repP`), then the block-wise products
(`bzip mulMB`). -/
def scRMP : Prog 29 := map vScR repP ⨾ map vScM (bzip mulMB) ⨾ clr 5

set_option linter.unusedSimpArgs false in
theorem run_scRMP {K N : ℕ} (s : Store 29) (hs : ∀ i : Fin 29, 5 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hx : (s 1).length = N * K) :
    run scRMP s = Function.update s 0 (scRMW N K (takeD K (s 2)) (s 1)) := by
  have hu : (takeD K (s 2)).length = K := length_takeD _ _
  simp only [scRMP, run_seq, run_clear]
  rw [run_repP_map vScR_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_,
    run_bzip_map vScM_inj (N := N) (blockSpec_mulMB K) (fun x y hx _ => by simp [hx]) _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    have hc : concatN N (fun i => mulMW (block K i (s 1))
        (block K i (concatN N (fun _ => takeD K (s 2))))) = scRMW N K (takeD K (s 2)) (s 1) := by
      apply concatN_congr
      intro i hi
      rw [block_concatN (fun _ _ => hu), mIfT hi]
    fin_cases t <;> simp [vScR, vScM, hc, hs]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [vScR, vScM, hs] at hi ⊢)
    | simp [vScR, vScM, hs, hK, hN, hx, length_concatN_const, hu]

theorem run_scRMP_map {u : Fin 29 → Fin k} (hu : Function.Injective u) {K N : ℕ} (s : Store k)
    (hs : ∀ i : Fin 29, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) :
    run (map u scRMP) s = Function.update s (u 0) (scRMW N K (takeD K (s (u 2))) (s (u 1))) :=
  run_map_eq_update hu _ s 0 _ (run_scRMP (s ∘ u) hs hK hN hx)

/-! ### `2^{−j}` on every coefficient -/

def vRB : Fin 28 → Fin 30 := ![6, 0, 1, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
  20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
theorem vRB_inj : Function.Injective vRB := by decide

/-- **Every coefficient times `2^{−j}`**: `j` block-wise rotations by one bit. -/
def rotBP : Prog 30 := cp 0 1 ⨾ forN 5 2 (map vRB (bzip rot1B) ⨾ cp 0 6 ⨾ clr 6)

set_option linter.unusedSimpArgs false in
theorem run_rotBP {K N : ℕ} (s : Store 30) (hs : ∀ i : Fin 30, 5 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hx : (s 1).length = N * K) :
    run rotBP s = Function.update s 0 (rotBW N K (s 2).length (s 1)) := by
  have h0 : rotBW N K 0 (s 1) = s 1 := by simp [rotBW, concatN_block hx]
  have hit : ∀ n, (· + 1)^[n] 0 = n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]
  rw [rotBP, run_seq, run_copy, run_forN_inv 5 2 (map vRB (bzip rot1B) ⨾ cp 0 6 ⨾ clr 6)
    (fun j => Function.update s 0 (rotBW N K j (s 1))) (· + 1) (fun _ => True)
    (fun j w _ => by
      simp only [run_seq, run_copy, run_clear]
      rw [run_bzip_map vRB_inj (N := N) (blockSpec_rot1B K) (fun x y hx _ => by simp [hx]) _ ?_ ?_
        ?_ ?_ ?_]
      · funext t
        have hst := rotBW_succ hx j
        fin_cases t <;> simp [vRB, hs, hst]
      all_goals first
        | (intro i hi; fin_cases i <;> simp [vRB, hs] at hi ⊢)
        | simp [vRB, hs, hK, hN, hx, length_rotBW N K _ hx])
    (fun _ _ => trivial) 0 trivial _ (by funext t; fin_cases t <;> simp [h0])]
  funext t; fin_cases t <;> simp [hit, hs]

end Prog

end SigabaNeo.Tape
