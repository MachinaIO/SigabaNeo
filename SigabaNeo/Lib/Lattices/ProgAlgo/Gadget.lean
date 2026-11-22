import SigabaNeo.Lib.Lattices.ProgAlgo.Digits
import SigabaNeo.Lib.Lattices.ProgAlgo.MatAdd

/-!
# The binary gadget on words as tape programs

* `ginvP : Prog 35` (`0` output, `1` a row `b` of `2k` ring entries, templates `2` `3` `4` `5` of
  lengths `K`, `2k · N`, `k`, `2k · 2k · N · K`; scratch `6 … 34`): **`ginvW N K k b`**
  (`run_ginvP`). The rows `r < k` of `G̲⁻¹(b)` are `digitRW (2k · N) K r b` (`ginvW_eq`); they are
  produced in order by alternating a block-wise digit pass and a block-wise shift, then `k · 2k`
  zero entries.
* `gadP : Prog 21` (`0` output, templates `1` … `5` of lengths `K`, `N`, `N · K`, `k`,
  `2k · N · K`; scratch `6 … 20`): **`gadW N K k`** (`run_gadP`): the constants `2^p` for `p < k`,
  the word of `2^p` doubled each round, then `k` zero entries.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k : ℕ}

theorem concatN_two_mul (k : ℕ) (R : ℕ → List Bool) :
    concatN (2 * k) R = concatN k R ++ concatN k (fun r => R (k + r)) := by
  rw [two_mul, concatN_add]

theorem concatN_replicate (n c : ℕ) :
    concatN n (fun _ => List.replicate c false) = List.replicate (n * c) false := by
  induction n with
  | zero => simp [concatN]
  | succ n ih => rw [concatN, ih, Nat.succ_mul, List.replicate_add]

/-- Shifting the words `g m, g (m + 1), …` of length `c` into a register. -/
theorem pushIdx_iter (c : ℕ) (g : ℕ → List Bool) (hg : ∀ m, (g m).length = c) :
    ∀ (j m : ℕ) (out : List Bool),
      (fun a : ℕ × List Bool => (a.1 + 1, (a.2 ++ g a.1).drop c))^[j] (m, out) =
        (m + j, (out ++ concatN j (fun i => g (m + i))).drop (j * c))
  | 0, m, out => by simp [concatN]
  | j + 1, m, out => by
    rw [Function.iterate_succ_apply', pushIdx_iter c g hg j m out]
    have hl : (concatN j (fun i => g (m + i))).length = j * c := length_concatN fun _ _ => hg _
    have := drop_append_drop out (concatN j (fun i => g (m + i))) (g (m + j))
    rw [hl, hg] at this
    simp only [this, concatN, Nat.succ_mul, Nat.add_assoc]

theorem length_concatN_bitW (B K : ℕ) (g : ℕ → Bool) :
    (concatN B (fun i => bitW K (g i))).length = B * K :=
  length_concatN fun _ _ => length_bitW K _

theorem takeD_concatN_bitW (B K : ℕ) (g : ℕ → Bool) :
    takeD (B * K) (concatN B (fun i => bitW K (g i))) = concatN B (fun i => bitW K (g i)) :=
  takeD_of_length' (length_concatN_bitW B K g)

theorem digitRW_entries (N K L r : ℕ) (b : List Bool) :
    concatN L (fun c => digitRW N K r (block (N * K) c b)) = digitRW (L * N) K r b := by
  rw [digitRW, concatN_mul]
  apply concatN_congr
  intro c _
  apply concatN_congr
  intro t ht
  rw [block_block b ht]

/-- **The rows of `G̲⁻¹(b)`**: the digit rows, then zero rows. -/
theorem ginvW_eq (N K k : ℕ) (b : List Bool) :
    ginvW N K k b = concatN k (fun r => digitRW (2 * k * N) K r b) ++
      List.replicate (k * (2 * k * (N * K))) false := by
  rw [ginvW, concatN_mul, concatN_two_mul]
  congr 1
  · apply concatN_congr
    intro r hr
    rw [← digitRW_entries]
    apply concatN_congr
    intro c hc
    have hdiv : (r * (2 * k) + c) / (2 * k) = r := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]
    have hmod : (r * (2 * k) + c) % (2 * k) = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
    rw [hdiv, hmod, Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]
    rfl
  · rw [← concatN_replicate, ← concatN_replicate]
    apply concatN_congr
    intro r hr
    apply concatN_congr
    intro c hc
    have hdiv : ((k + r) * (2 * k) + c) / (2 * k) = k + r := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]
    have hk : (k + r) / k = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ (by omega), Nat.div_eq_of_lt hr]
    rw [hdiv, hk]
    rfl

theorem toBits_zero (K : ℕ) : toBits K 0 = List.replicate K false := by
  induction K with
  | zero => rfl
  | succ K ih => simp [toBits, ih, List.replicate_succ]

theorem powW_zero (K : ℕ) : powW K 0 = bitW K true := by
  cases K with
  | zero => rfl
  | succ K => simp [powW, toBits, toBits_zero, bitW, zeroW]

theorem shl_powW (K p : ℕ) : shl (powW K p) = powW K (p + 1) := by
  apply eq_of_dec_eq (K := K) (by simp [powW]) (by simp [powW])
  rw [dec_shl K (by simp [powW]), powW, powW, dec_toBits, dec_toBits]
  push_cast; ring

theorem gadW_eq (N K k : ℕ) :
    gadW N K k = concatN k (fun p => constW N K (powW K p)) ++
      List.replicate (k * (N * K)) false := by
  rw [gadW, Nat.one_mul, concatN_two_mul, ← concatN_replicate]
  congr 1
  · apply concatN_congr
    intro p hp
    rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
    rfl
  · apply concatN_congr
    intro r hr
    have hk : (k + r) / k = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ (by omega), Nat.div_eq_of_lt hr]
    rw [hk]
    rfl

namespace Prog

open scoped Prog

/-! ### `G̲⁻¹` -/

def vDg : Fin 28 → Fin 35 := ![7, 6, 1, 2, 3, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
def mvR : Fin 5 → Fin 35 := ![7, 0, 9, 10, 1]
def vSh : Fin 28 → Fin 35 := ![11, 6, 1, 2, 3, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
def gfl : Fin 3 → Fin 35 := ![0, 10, 1]
theorem vDg_inj : Function.Injective vDg := by decide
theorem mvR_inj : Function.Injective mvR := by decide
theorem vSh_inj : Function.Injective vSh := by decide
theorem gfl_inj : Function.Injective gfl := by decide

/-- A digit row. Tapes `6` the shifted row, `7` its digit row, `8` the counter, `9` a bit, `10` a
counter, `11` the next shift; `12 … 34` scratch. -/
def gRow : Prog 35 :=
  map vDg (bzip dig0B) ⨾ map mvR mvP ⨾ map vSh (bzip shrB) ⨾ cp 6 11 ⨾ clr 7 ⨾ clr 11

/-- **`G̲⁻¹` of a row.** -/
def ginvP : Prog 35 := cp 0 5 ⨾ cp 6 1 ⨾ forN 8 4 gRow ⨾ forN 8 4 (map gfl (fillP false)) ⨾ clr 6

/-- The row `b` shifted `m` times, block by block. -/
def shW (B K m : ℕ) (b : List Bool) : List Bool := concatN B (fun t => shrN m (block K t b))

/-- The digit pass of a shifted row. -/
def dgW (B K m : ℕ) (b : List Bool) : List Bool :=
  concatN B (fun t => bitW K (hd (block K t (shW B K m b))))

theorem length_shW {B K : ℕ} {b : List Bool} (hb : b.length = B * K) (m : ℕ) :
    (shW B K m b).length = B * K :=
  length_concatN fun t ht => by rw [length_shrN, length_block hb ht]

theorem length_dgW (B K m : ℕ) (b : List Bool) : (dgW B K m b).length = B * K :=
  length_concatN fun _ _ => length_bitW K _

theorem dgW_eq {B K : ℕ} {b : List Bool} (hb : b.length = B * K) (m : ℕ) :
    dgW B K m b = digitRW B K m b := by
  apply concatN_congr
  intro t ht
  rw [shW, block_concatN (fun j hj => by rw [length_shrN, length_block hb hj])]
  simp only [ht, ↓reduceIte, hd_shrN, List.getD_eq_getElem?_getD]

theorem shW_zero {B K : ℕ} {b : List Bool} (hb : b.length = B * K) : shW B K 0 b = b := by
  rw [shW, ← concatN_block hb]; apply concatN_congr; intro t _; simp [shrN, concatN_block hb]

def gG (s : Store 35) (B K : ℕ) : ℕ × List Bool → Store 35
  | (m, out) => Function.update (Function.update s 6 (shW B K m (s 1))) 0 out

set_option linter.unusedSimpArgs false in
theorem run_gRow {K B : ℕ} (s : Store 35) (hs : ∀ i : Fin 35, 6 ≤ i.val → i ≠ 8 → s i = [])
    (hK : (s 2).length = K) (hB : (s 3).length = B) (hb : (s 1).length = B * K) (a)
    (w : List Bool) :
    run gRow (Function.update (gG s B K a) 8 w) =
      Function.update (gG s B K ((fun a : ℕ × List Bool =>
        (a.1 + 1, (a.2 ++ dgW B K a.1 (s 1)).drop (B * K))) a)) 8 w := by
  obtain ⟨m, out⟩ := a
  simp only [gRow, run_seq, run_copy, run_clear]
  rw [run_bzip_map vDg_inj (N := B) (blockSpec_dig0 K) (fun x _ _ _ => length_bitW K _) _ ?_ ?_
    ?_ ?_ ?_, run_mvP_map mvR_inj _ ?_ ?_,
    run_bzip_map vSh_inj (N := B) (blockSpec_shr K) (fun x _ hx _ => by simp [hx]) _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    simp only [gG]
    fin_cases t <;> simp [vDg, mvR, vSh, hs, hb, takeD_of_length', length_dgW, shW,
      shr_pass hb, dgW, drop_append_of_length, takeD_concatN_bitW]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [vDg, mvR, vSh, gG, hs] at hi ⊢)
    | simp [vDg, mvR, vSh, gG, hs, hK, hB, hb, length_shW hb,
        length_concatN (K := K) fun _ _ => length_bitW K _]

set_option linter.unusedSimpArgs false in
/-- **`G̲⁻¹` of a row** on words. -/
theorem run_ginvP {K N k : ℕ} (s : Store 35) (hs : ∀ i : Fin 35, 6 ≤ i.val → s i = [])
    (hK : (s 2).length = K) (hB : (s 3).length = 2 * k * N) (hk : (s 4).length = k)
    (hO : (s 5).length = 2 * k * (2 * k * (N * K))) (hb : (s 1).length = 2 * k * (N * K)) :
    run ginvP s = Function.update s 0 (ginvW N K k (s 1)) := by
  set B := 2 * k * N
  have hb' : (s 1).length = B * K := by rw [hb]; ring
  have hc : ∀ i : Fin 35, 6 ≤ i.val → i ≠ 8 → s i = [] := fun i hi _ => hs i hi
  have hloop := run_forN 8 4 gRow (gG s B K) _ (run_gRow s hc hK hB hb') (0, s 5)
    (Function.update (Function.update s 0 (s 5)) 6 (s 1))
    (by funext t; fin_cases t <;> simp [gG, shW_zero hb'])
  have hp := pushIdx_iter (B * K) (fun m => dgW B K m (s 1)) (fun m => length_dgW B K m (s 1)) k 0
    (s 5)
  simp only [zero_add] at hp
  set out1 := (s 5 ++ concatN k (fun i => dgW B K i (s 1))).drop (k * (B * K))
  let G2 : List Bool → Store 35 := fun out => gG s B K (k, out)
  have hloop2 := run_forN 8 4 (map gfl (fillP false)) G2
    (fun o => (o ++ List.replicate (s 1).length false).drop
      (List.replicate (s 1).length false).length) (fun out w => by
      rw [run_fillP_map gfl_inj _ _ (by simp [gfl, G2, gG, hc])]
      funext t; fin_cases t <;> simp [gfl, G2, gG]) out1 (Function.update (G2 out1) 8 [])
    (by simp)
  have hsplit : run ginvP s = run (clr 6) (run (forN 8 4 (map gfl (fillP false)))
      (run (forN 8 4 gRow) (Function.update (Function.update s 0 (s 5)) 6 (s 1)))) := by
    simp only [ginvP, run_seq, run_copy]
    rw [show Function.update s 0 (s 5) 1 = s 1 by simp]
  have h4 : Function.update (Function.update s 0 (s 5)) 6 (s 1) 4 = s 4 := by simp
  rw [hsplit, hloop, h4, hk, hp, hloop2]
  have h4' : Function.update (G2 out1) 8 [] 4 = s 4 := by simp [G2, gG]
  rw [h4', hk, pushConst_iter, List.length_replicate]
  have := drop_append_drop (s 5) (concatN k (fun i => dgW B K i (s 1)))
    (concatN k (fun _ => List.replicate (s 1).length false))
  rw [length_concatN (K := B * K) (fun i _ => length_dgW B K i (s 1)), length_concatN_const,
    List.length_replicate] at this
  rw [show k * (s 1).length = k * (s 1).length from rfl, this, drop_append_of_length (by
    rw [hO, hb]; ring), concatN_replicate, ginvW_eq]
  funext t
  fin_cases t <;> simp [G2, gG, hs]
  rw [hb]
  congr 1
  apply concatN_congr
  intro r _
  exact dgW_eq hb' r

/-! ### The gadget row -/

/-- The first bit set, the others clear (from a word of zeros). -/
def oneOp : SerOp := fun _ _ c => (c, false)

theorem serF_oneOp (c : Bool) (x y : List Bool) :
    serF oneOp c x y = match x with
      | [] => []
      | _ :: xs => c :: List.replicate xs.length false := by
  induction x generalizing c y with
  | nil => rfl
  | cons b xs ih =>
    simp only [serF, oneOp, ih]
    cases xs <;> simp [List.replicate_succ]

theorem run_monoWP_map {u : Fin 12 → Fin k} (hu : Function.Injective u) {K N j : ℕ} (s : Store k)
    (hs : ∀ i : Fin 12, 6 ≤ i.val → s (u i) = []) (hv : (s (u 1)).length = K)
    (hj : (s (u 2)).length = j) (hK : (s (u 3)).length = K) (hN : (s (u 4)).length = N)
    (hNK : (s (u 5)).length = N * K) :
    run (map u monoWP) s = Function.update s (u 0) (monoW N K j (s (u 1))) :=
  run_map_eq_update hu _ s 0 _ (run_monoWP (s ∘ u) hs hv hj hK hN hNK)

def vOne : Fin 11 → Fin 21 := ![6, 13, 11, 12, 14, 15, 16, 17, 18, 19, 20]
def vMono : Fin 12 → Fin 21 := ![7, 6, 12, 1, 2, 3, 13, 14, 15, 16, 17, 18]
def mvG : Fin 5 → Fin 21 := ![7, 0, 9, 10, 3]
def vShlG : Fin 11 → Fin 21 := ![11, 13, 6, 12, 14, 15, 16, 17, 18, 19, 20]
def gfl2 : Fin 3 → Fin 21 := ![0, 10, 3]
theorem vOne_inj : Function.Injective vOne := by decide
theorem vMono_inj : Function.Injective vMono := by decide
theorem mvG_inj : Function.Injective mvG := by decide
theorem vShlG_inj : Function.Injective vShlG := by decide
theorem gfl2_inj : Function.Injective gfl2 := by decide

/-- A gadget column. Tapes `6` the word of `2^p`, `7` its constant, `8` the counter, `9` a bit,
`10` a counter, `11` the next word, `12` blank; `13 … 20` scratch. -/
def gadCol : Prog 21 :=
  map vMono monoWP ⨾ map mvG mvP ⨾ map vShlG shlP ⨾ cp 6 11 ⨾ clr 7 ⨾ clr 11

/-- **The gadget row `G̲`.** -/
def gadP : Prog 21 :=
  cp 0 5 ⨾ cp 11 1 ⨾ setZero 11 ⨾ map vOne (zipW oneOp true) ⨾ clr 11 ⨾ forN 8 4 gadCol ⨾
    forN 8 4 (map gfl2 (fillP false)) ⨾ clr 6

def gaG (s : Store 21) (K : ℕ) : ℕ × List Bool → Store 21
  | (p, out) => Function.update (Function.update s 6 (powW K p)) 0 out

theorem length_powW (K p : ℕ) : (powW K p).length = K := by simp [powW]

theorem length_constW {N K : ℕ} {v : List Bool} (hv : v.length = K) : (constW N K v).length = N * K :=
  length_concatN fun t _ => by split_ifs <;> simp [hv, zeroW]

set_option linter.unusedSimpArgs false in
theorem run_gadCol {K N : ℕ} (s : Store 21) (hs : ∀ i : Fin 21, 6 ≤ i.val → i ≠ 8 → s i = [])
    (hK : (s 1).length = K) (hN : (s 2).length = N) (hNK : (s 3).length = N * K) (a)
    (w : List Bool) :
    run gadCol (Function.update (gaG s K a) 8 w) =
      Function.update (gaG s K ((fun a : ℕ × List Bool =>
        (a.1 + 1, (a.2 ++ constW N K (powW K a.1)).drop (N * K))) a)) 8 w := by
  obtain ⟨p, out⟩ := a
  have hshl : ∀ t : Store 21, (∀ i : Fin 11, 4 ≤ i.val → t (vShlG i) = []) → t (vShlG 1) = [] →
      run (map vShlG shlP) t = Function.update t 11 (shl (t 6)) := fun t h h1 =>
    (run_zipW_map vShlG_inj _ _ t h h1).trans (by rw [serF_shlOp_false]; rfl)
  simp only [gadCol, run_seq, run_copy, run_clear]
  rw [run_monoWP_map vMono_inj (K := K) (N := N) (j := 0) _ ?_ ?_ ?_ ?_ ?_ ?_,
    run_mvP_map mvG_inj _ ?_ ?_, hshl _ ?_ ?_]
  · funext t
    simp only [gaG]
    have hmono : monoW N K 0 (powW K p) = constW N K (powW K p) := rfl
    fin_cases t <;> simp [vMono, mvG, vShlG, hs, hNK, shl_powW, hmono,
      takeD_of_length' (length_constW (N := N) (length_powW K p)), drop_append_of_length]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [vMono, mvG, vShlG, gaG, hs] at hi ⊢)
    | simp [vMono, mvG, vShlG, gaG, hs, hK, hN, hNK, length_powW]

set_option linter.unusedSimpArgs false in
/-- **The gadget row** on words. -/
theorem run_gadP {K N k : ℕ} (s : Store 21) (hs : ∀ i : Fin 21, 6 ≤ i.val → s i = [])
    (hK : (s 1).length = K) (hN : (s 2).length = N) (hNK : (s 3).length = N * K)
    (hk : (s 4).length = k) (hO : (s 5).length = 2 * k * (N * K)) :
    run gadP s = Function.update s 0 (gadW N K k) := by
  have hc : ∀ i : Fin 21, 6 ≤ i.val → i ≠ 8 → s i = [] := fun i hi _ => hs i hi
  have hone : ∀ t : Store 21, (∀ i : Fin 11, 4 ≤ i.val → t (vOne i) = []) → t (vOne 1) = [] →
      run (map vOne (zipW oneOp true)) t =
        Function.update t 6 (serF oneOp true (t 11) (t 12)) := fun t h h1 =>
    run_zipW_map vOne_inj _ _ t h h1
  have e0 : run (cp 0 5 ⨾ cp 11 1 ⨾ setZero 11 ⨾ map vOne (zipW oneOp true) ⨾ clr 11) s =
      Function.update (gaG s K (0, s 5)) 8 [] := by
    simp only [run_seq, run_copy, run_setZero, run_clear]
    rw [hone _ ?_ ?_]
    · funext t
      fin_cases t <;> simp [gaG, hs, hK, powW_zero, serF_oneOp]
      cases K <;> simp [bitW, zeroW, List.replicate_succ]
    all_goals first
      | (intro i hi; fin_cases i <;> simp [vOne, hs] at hi ⊢)
      | simp [vOne, hs]
  have hloop := run_forN 8 4 gadCol (gaG s K) _ (run_gadCol s hc hK hN hNK) (0, s 5)
    (Function.update (gaG s K (0, s 5)) 8 []) (by simp [gaG])
  have hp := pushIdx_iter (N * K) (fun p => constW N K (powW K p))
    (fun p => length_constW (length_powW K p)) k 0 (s 5)
  simp only [zero_add] at hp
  set out1 := (s 5 ++ concatN k (fun i => constW N K (powW K i))).drop (k * (N * K))
  let G2 : List Bool → Store 21 := fun out => gaG s K (k, out)
  have hloop2 := run_forN 8 4 (map gfl2 (fillP false)) G2
    (fun o => (o ++ List.replicate (s 3).length false).drop
      (List.replicate (s 3).length false).length) (fun out w => by
      rw [run_fillP_map gfl2_inj _ _ (by simp [gfl2, G2, gaG, hc])]
      funext t; fin_cases t <;> simp [gfl2, G2, gaG]) out1 (Function.update (G2 out1) 8 [])
    (by simp)
  have hsplit : run gadP s = run (clr 6) (run (forN 8 4 (map gfl2 (fillP false)))
      (run (forN 8 4 gadCol)
        (run (cp 0 5 ⨾ cp 11 1 ⨾ setZero 11 ⨾ map vOne (zipW oneOp true) ⨾ clr 11) s))) := rfl
  have h4 : Function.update (gaG s K (0, s 5)) 8 [] 4 = s 4 := by simp [gaG]
  rw [hsplit, e0, hloop, h4, hk, hp, hloop2]
  have h4' : Function.update (G2 out1) 8 [] 4 = s 4 := by simp [G2, gaG]
  rw [h4', hk, pushConst_iter, List.length_replicate, hNK]
  have := drop_append_drop (s 5) (concatN k (fun i => constW N K (powW K i)))
    (concatN k (fun _ => List.replicate (N * K) false))
  rw [length_concatN (K := N * K) (fun i _ => length_constW (length_powW K i)),
    length_concatN_const, List.length_replicate] at this
  rw [this, drop_append_of_length (by rw [hO]; ring), concatN_replicate, gadW_eq]
  funext t
  fin_cases t <;> simp [G2, gaG, hs]

theorem noGrow_ginvP : ginvP.NoGrow := rfl
theorem noGrow_gadP : gadP.NoGrow := rfl
theorem wf_ginvP : ginvP.WF := wf_of_wfB (by decide)
theorem wf_gadP : gadP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
