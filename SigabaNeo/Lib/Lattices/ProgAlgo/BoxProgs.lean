import SigabaNeo.Lib.Lattices.ProgAlgo.Spec
import SigabaNeo.Lib.Lattices.Algo.BoxWords
import SigabaNeo.Lib.Machines.Prog.CoinLoop

/-!
# The box words as tape programs

The word algorithms of box rejection (`SigabaNeo.Lattices.Algo.BoxWords`) as programs of the
fragment `NoGrow`:

* `embP : Prog 22`: **`embW n B K l`** (`run_embP`), the big-box element from the coins `l`: for
  each of the `n` coefficients, `B` coins from the stream, padded to `K` bits, minus `2^(B−1)`.
  Tapes: `0` output, `1` `l`, templates `2` `3` `4` of lengths `B`, `K`, `n`, `5` the word
  `powW K (B − 1)`, `6` a template of length `n · K`; scratch `7 … 21`.
* `ballP : Prog 23`: **`[ballW n K sW w]`** (`run_ballP`), the ball test, for `0 < K`. Tapes: `0`
  output, `1` `w` (`n · K` bits), `2` `sW` (`K` bits), templates `3` `4` `5` of lengths `K`, `n`,
  `1`; scratch `6 … 22`.
* `decP : Prog 37`: **`decW N K k u`** (`run_decP`), the binary decomposition of a ring word.
  Tapes: `0` output, `1` `u` (`N · K` bits), templates `2` … `6` of lengths `K`, `N`, `k`, `N · K`,
  `2k · N · K`; scratch `7 … 36`.

Every program is placed on any distinct tapes by `Prog.map` (`run_*_map`, `law_*_map`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k : ℕ}

/-! ### Word lemmas -/

theorem hd_drop (l : List Bool) (s : ℕ) : hd (l.drop s) = l.getD s false := by
  rw [hd, List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

theorem getW_eq_takeD : ∀ (B s : ℕ) (l : List Bool), getW B s l = takeD B (l.drop s)
  | 0, _, _ => rfl
  | B + 1, s, l => by
    rw [getW, List.ofFn_succ, takeD, List.tail_drop, ← getW_eq_takeD B (s + 1) l, getW, hd_drop]
    congr 1
    congr 1
    funext t
    show l.getD _ false = l.getD _ false
    congr 1
    simp only [Fin.val_succ]
    omega

theorem takeD_eq_take_append : ∀ (n m : ℕ) (w : List Bool), n ≤ m →
    takeD n w = (w ++ List.replicate m false).take n
  | 0, _, _, _ => rfl
  | n + 1, m, [], h => by
    rw [takeD_nil]; simp only [List.nil_append, List.take_replicate]; congr; omega
  | n + 1, m, b :: w, h => by
    simp only [takeD, hd_cons, List.tail_cons, List.cons_append, List.take_succ_cons]
    rw [takeD_eq_take_append n m w (by omega)]

theorem padW_eq_takeD (K : ℕ) (w : List Bool) : padW K w = takeD K w := by
  rw [padW, takeD_eq_take_append K K w le_rfl, zeroW]

/-- The big-box element from a stream of coins. -/
theorem embW_eq_concatN (n B K : ℕ) (l : List Bool) :
    embW n B K l = concatN n (fun q => subW (takeD K (takeD B (l.drop (q * B)))) (powW K (B - 1))) := by
  apply concatN_congr
  intro q _
  rw [cenW, getW_eq_takeD, padW_eq_takeD, Nat.mul_comm]

/-- Shifting the words `f 0, f 1, …` (each of length `c`) into a register. -/
theorem pushNat_iter (c : ℕ) (f : ℕ → List Bool) (hf : ∀ j, (f j).length = c) :
    ∀ (m : ℕ) (j : ℕ) (out : List Bool),
      (fun a : ℕ × List Bool => (a.1 + 1, (a.2 ++ f a.1).drop c))^[m] (j, out) =
        (j + m, (out ++ concatN m (fun i => f (j + i))).drop (m * c))
  | 0, j, out => by simp [concatN]
  | m + 1, j, out => by
    rw [Function.iterate_succ_apply', pushNat_iter c f hf m j out]
    have hl : (concatN m (fun i => f (j + i))).length = m * c := length_concatN fun i _ => hf _
    have := drop_append_drop out (concatN m (fun i => f (j + i))) (f (j + m))
    rw [hl, hf] at this
    simp only [this, concatN, Nat.succ_mul, Nat.add_assoc]

theorem ball_iter (K : ℕ) (sW : List Bool) : ∀ (m : ℕ) (l : List Bool) (b : Bool),
    (fun a : List Bool × Bool => (a.1.drop K, a.2 && absLeW (takeD K a.1) sW))^[m] (l, b) =
      (l.drop (m * K), b && allN m (fun q => absLeW (takeD K (l.drop (q * K))) sW))
  | 0, l, b => by simp [allN]
  | m + 1, l, b => by
    rw [Function.iterate_succ_apply', ball_iter K sW m l b]
    simp only [List.drop_drop, allN, Bool.and_assoc, Nat.succ_mul, Nat.add_comm K]

theorem allN_congr {n : ℕ} {f g : ℕ → Bool} (h : ∀ q < n, f q = g q) : allN n f = allN n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [allN, allN, ih (fun q hq => h q (by omega)), h n (by omega)]

/-- The ball test of one residue through two comparisons. -/
theorem absLeW_eq_lt {w sW : List Bool} (h : w.length = sW.length) :
    absLeW w sW = !(decide (val sW < val w) && decide (val sW < val (negW w))) := by
  rw [absLeW, leW_eq h, leW_eq (by rw [length_negW, h])]
  cases h1 : decide (val sW < val w) <;> cases h2 : decide (val sW < val (negW w)) <;>
    simp_all [decide_eq_false_iff_not]

namespace Prog

open scoped Prog

/-! ### Placed arithmetic -/

theorem run_subP_map {u : Fin 11 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 11, (i = 1 ∨ 4 ≤ i.val) → s (u i) = []) (h : (s (u 2)).length = (s (u 3)).length) :
    run (map u subP) s = Function.update s (u 0) (subW (s (u 2)) (s (u 3))) :=
  run_map_eq_update hu _ s 0 _ (run_subP _ (clean11_comp s hs) h)

theorem run_ltP_map {u : Fin 11 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 11, (i = 1 ∨ 4 ≤ i.val) → s (u i) = []) (h : (s (u 2)).length = (s (u 3)).length)
    (h0 : s (u 2) ≠ []) :
    run (map u ltP) s = Function.update s (u 0) [decide (val (s (u 2)) < val (s (u 3)))] :=
  run_map_eq_update hu _ s 0 _ (run_ltP _ (clean11_comp s hs) h h0)

/-! ### The big-box element -/

def emA : Fin 5 → Fin 22 := ![7, 8, 12, 13, 2]
def emB : Fin 5 → Fin 22 := ![8, 9, 12, 13, 3]
def emC : Fin 5 → Fin 22 := ![10, 0, 12, 13, 3]
def emS : Fin 11 → Fin 22 := ![10, 14, 9, 5, 15, 16, 17, 18, 19, 20, 21]
theorem emA_inj : Function.Injective emA := by decide
theorem emB_inj : Function.Injective emB := by decide
theorem emC_inj : Function.Injective emC := by decide
theorem emS_inj : Function.Injective emS := by decide

/-- One coefficient. Tapes `7` the coin stream, `8` `9` registers of widths `B`, `K`, `10` the
coefficient, `11` the counter, `12` `13` `14 … 21` scratch. -/
def embBody : Prog 22 :=
  cp 8 2 ⨾ map emA mvP ⨾ cp 9 3 ⨾ map emB mvP ⨾ map emS subP ⨾ map emC mvP ⨾ clr 8 ⨾ clr 9 ⨾
    clr 10

/-- **The big-box element from the coins.** -/
def embP : Prog 22 := cp 0 6 ⨾ cp 7 1 ⨾ forN 11 4 embBody ⨾ clr 7

theorem run_emA (t : Store 22) (h12 : t 12 = []) (h13 : t 13 = []) :
    run (map emA mvP) t = Function.update (Function.update t 7 ((t 7).drop (t 2).length)) 8
      ((t 8 ++ takeD (t 2).length (t 7)).drop (t 2).length) := run_mvP_map emA_inj t h12 h13
theorem run_emB (t : Store 22) (h12 : t 12 = []) (h13 : t 13 = []) :
    run (map emB mvP) t = Function.update (Function.update t 8 ((t 8).drop (t 3).length)) 9
      ((t 9 ++ takeD (t 3).length (t 8)).drop (t 3).length) := run_mvP_map emB_inj t h12 h13
theorem run_emC (t : Store 22) (h12 : t 12 = []) (h13 : t 13 = []) :
    run (map emC mvP) t = Function.update (Function.update t 10 ((t 10).drop (t 3).length)) 0
      ((t 0 ++ takeD (t 3).length (t 10)).drop (t 3).length) := run_mvP_map emC_inj t h12 h13
theorem run_emS (t : Store 22) (h : ∀ j : Fin 22, 14 ≤ j.val → t j = [])
    (hl : (t 9).length = (t 5).length) :
    run (map emS subP) t = Function.update t 10 (subW (t 9) (t 5)) :=
  run_subP_map emS_inj t (by
    intro i hi
    fin_cases i <;> simp at hi <;> exact h _ (by decide)) hl

theorem run_embBody {B K : ℕ} (s : Store 22) (hs : ∀ i : Fin 22, 7 ≤ i.val → s i = [])
    (hB : (s 2).length = B) (hK : (s 3).length = K) (hc : (s 5).length = K)
    (a : List Bool × List Bool) (w : List Bool) :
    run embBody (Function.update (Function.update (Function.update s 7 a.1) 0 a.2) 11 w) =
      Function.update (Function.update (Function.update s 7 (a.1.drop B)) 0
        ((a.2 ++ subW (takeD K (takeD B a.1)) (s 5)).drop K)) 11 w := by
  obtain ⟨sv, ov⟩ := a
  have hc' : ∀ i : Fin 22, 7 ≤ i.val → i ≠ 7 → i ≠ 11 → s i = [] := fun i hi _ _ => hs i hi
  simp only [embBody, run_seq, run_copy, run_clear]
  rw [run_emA _ (by simp [hs]) (by simp [hs])]
  rw [run_emB _ (by simp [hs]) (by simp [hs])]
  rw [run_emS _ (by intro j hj; fin_cases j <;> simp at hj ⊢ <;> exact hs _ (by decide))
    (by simp [hB, hK, hc])]
  rw [run_emC _ (by simp [hs]) (by simp [hs])]
  have hsub : takeD K (subW (takeD K (takeD B sv)) (s 5)) = subW (takeD K (takeD B sv)) (s 5) :=
    takeD_of_length' (by simp)
  funext t
  fin_cases t <;> simp [hs, hB, hK, hsub]

theorem run_embP {n B K : ℕ} (s : Store 22) (hs : ∀ i : Fin 22, 7 ≤ i.val → s i = [])
    (hB : (s 2).length = B) (hK : (s 3).length = K) (hn : (s 4).length = n)
    (hc : s 5 = powW K (B - 1)) (hO : (s 6).length = n * K) :
    run embP s = Function.update s 0 (embW n B K (s 1)) := by
  have hcl : (s 5).length = K := by rw [hc, powW, length_toBits]
  let G : List Bool × List Bool → Store 22 := fun a =>
    Function.update (Function.update s 7 a.1) 0 a.2
  have hloop := run_forN 11 4 embBody G
    (fun a => (a.1.drop B, (a.2 ++ subW (takeD K (takeD B a.1)) (s 5)).drop K))
    (fun a w => run_embBody s hs hB hK hcl a w) (s 1, s 6)
    (Function.update (Function.update s 0 (s 6)) 7 (s 1)) (by
      funext t; simp only [G]; fin_cases t <;> simp)
  have h1 : Function.update s 0 (s 6) 1 = s 1 := by simp
  simp only [embP, run_seq, run_copy, run_clear]
  rw [h1, hloop]
  have h4 : Function.update (Function.update s 0 (s 6)) 7 (s 1) 4 = s 4 := by simp
  rw [h4, hn, pushSeq_iter B K (fun sv => subW (takeD K (takeD B sv)) (s 5)) (fun _ => by simp [hcl])]
  rw [drop_append_of_length hO, embW_eq_concatN, ← hc]
  funext t
  simp only [G]
  fin_cases t <;> simp [hs]

theorem run_embP_map {u : Fin 22 → Fin k} (hu : Function.Injective u) {n B K : ℕ} (s : Store k)
    (hs : ∀ i : Fin 22, 7 ≤ i.val → s (u i) = []) (hB : (s (u 2)).length = B)
    (hK : (s (u 3)).length = K) (hn : (s (u 4)).length = n) (hc : s (u 5) = powW K (B - 1))
    (hO : (s (u 6)).length = n * K) :
    run (map u embP) s = Function.update s (u 0) (embW n B K (s (u 1))) :=
  run_map_eq_update hu _ s 0 _ (run_embP _ hs hB hK hn hc hO)

theorem noGrow_embP : embP.NoGrow := rfl
theorem wf_embP : embP.WF := wf_of_wfB (by decide)

/-! ### The ball test -/

def blA : Fin 5 → Fin 23 := ![6, 7, 13, 14, 3]
def blN : Fin 11 → Fin 23 := ![9, 15, 8, 7, 16, 17, 18, 19, 20, 21, 22]
def blL1 : Fin 11 → Fin 23 := ![10, 15, 2, 7, 16, 17, 18, 19, 20, 21, 22]
def blL2 : Fin 11 → Fin 23 := ![11, 15, 2, 9, 16, 17, 18, 19, 20, 21, 22]
theorem blA_inj : Function.Injective blA := by decide
theorem blN_inj : Function.Injective blN := by decide
theorem blL1_inj : Function.Injective blL1 := by decide
theorem blL2_inj : Function.Injective blL2 := by decide

theorem run_blA (t : Store 23) (h13 : t 13 = []) (h14 : t 14 = []) :
    run (map blA mvP) t = Function.update (Function.update t 6 ((t 6).drop (t 3).length)) 7
      ((t 7 ++ takeD (t 3).length (t 6)).drop (t 3).length) := run_mvP_map blA_inj t h13 h14

theorem clean_bl {u : Fin 11 → Fin 23} (hu1 : u 1 = 15)
    (hu : ∀ i : Fin 11, 4 ≤ i.val → 16 ≤ (u i).val) (t : Store 23)
    (h : ∀ j : Fin 23, 15 ≤ j.val → t j = []) :
    ∀ i : Fin 11, (i = 1 ∨ 4 ≤ i.val) → t (u i) = [] := by
  rintro i (rfl | hi)
  · rw [hu1]; exact h _ (by decide)
  · exact h _ (by have := hu i hi; omega)

theorem run_blN (t : Store 23) (h : ∀ j : Fin 23, 15 ≤ j.val → t j = [])
    (hl : (t 8).length = (t 7).length) :
    run (map blN subP) t = Function.update t 9 (subW (t 8) (t 7)) :=
  run_subP_map blN_inj t (clean_bl rfl (by decide) t h) hl

theorem run_blL1 (t : Store 23) (h : ∀ j : Fin 23, 15 ≤ j.val → t j = [])
    (hl : (t 2).length = (t 7).length) (h0 : t 2 ≠ []) :
    run (map blL1 ltP) t = Function.update t 10 [decide (val (t 2) < val (t 7))] :=
  run_ltP_map blL1_inj t (clean_bl rfl (by decide) t h) hl h0

theorem run_blL2 (t : Store 23) (h : ∀ j : Fin 23, 15 ≤ j.val → t j = [])
    (hl : (t 2).length = (t 9).length) (h0 : t 2 ≠ []) :
    run (map blL2 ltP) t = Function.update t 11 [decide (val (t 2) < val (t 9))] :=
  run_ltP_map blL2_inj t (clean_bl rfl (by decide) t h) hl h0

/-- Clear the flag `0` if both comparisons `10`, `11` hold. -/
def flagP : Prog 23 := ifBit 10 (ifBit 11 (setZero 0) (nop 0)) (nop 0)

theorem run_flagP (t : Store 23) :
    run flagP t = Function.update t 0
      (if (hd (t 10) && hd (t 11)) = true then List.replicate (t 0).length false else t 0) := by
  simp only [flagP, run_ifBit]
  cases h10 : hd (t 10) <;> cases h11 : hd (t 11) <;> simp

/-- One residue. Tapes `6` the stream, `7` the residue, `8` zero, `9` its negation, `10` `11` the
comparisons, `12` the counter, `13 … 22` scratch. -/
def ballBody : Prog 23 :=
  cp 7 3 ⨾ map blA mvP ⨾ cp 8 3 ⨾ setZero 8 ⨾ map blN subP ⨾ map blL1 ltP ⨾ map blL2 ltP ⨾ flagP ⨾
    clr 7 ⨾ clr 8 ⨾ clr 9 ⨾ clr 10 ⨾ clr 11

/-- **The ball test** `[ballW n K sW w]`. -/
def ballP : Prog 23 := cp 0 5 ⨾ sin true 0 ⨾ cp 6 1 ⨾ forN 12 4 ballBody ⨾ clr 6

theorem flag_eq (fl a b : Bool) :
    (if (a && b) = true then List.replicate [fl].length false else [fl]) = [fl && !(a && b)] := by
  cases a <;> cases b <;> cases fl <;> rfl

theorem run_ballBody {K : ℕ} (hK0 : 0 < K) (s : Store 23) (hs : ∀ i : Fin 23, 6 ≤ i.val → s i = [])
    (hS : (s 2).length = K) (hK : (s 3).length = K) (a : List Bool × Bool) (w : List Bool) :
    run ballBody (Function.update (Function.update (Function.update s 6 a.1) 0 [a.2]) 12 w) =
      Function.update (Function.update (Function.update s 6 (a.1.drop K)) 0
        [a.2 && absLeW (takeD K a.1) (s 2)]) 12 w := by
  obtain ⟨sv, fl⟩ := a
  have h0 : s 2 ≠ [] := by intro h; rw [h] at hS; simp at hS; omega
  simp only [ballBody, run_seq, run_copy, run_clear, run_setZero]
  rw [run_blA _ (by simp [hs]) (by simp [hs])]
  rw [run_blN _ (by intro j hj; fin_cases j <;> simp at hj ⊢ <;> exact hs _ (by decide))
    (by simp [hK])]
  rw [run_blL1 _ (by intro j hj; fin_cases j <;> simp at hj ⊢ <;> exact hs _ (by decide))
    (by simp [hK, hS]) (by simp [h0])]
  rw [run_blL2 _ (by intro j hj; fin_cases j <;> simp at hj ⊢ <;> exact hs _ (by decide))
    (by simp [hK, hS]) (by simp [h0])]
  rw [run_flagP]
  have hneg : subW (List.replicate K false) (takeD K sv) = negW (takeD K sv) := by
    rw [negW, length_takeD, zeroW]
  have hab := absLeW_eq_lt (w := takeD K sv) (sW := s 2) (by simp [hS])
  funext t
  fin_cases t <;> simp [hs, hK]
  rw [hneg, hab]
  by_cases h1 : val (s 2) < val (takeD K sv) <;> by_cases h2 : val (s 2) < val (negW (takeD K sv)) <;>
    simp [h1, h2]

theorem run_ballP {n K : ℕ} (hK0 : 0 < K) (s : Store 23)
    (hs : ∀ i : Fin 23, 6 ≤ i.val → s i = []) (hw : (s 1).length = n * K) (hS : (s 2).length = K)
    (hK : (s 3).length = K) (hn : (s 4).length = n) (h1 : (s 5).length = 1) :
    run ballP s = Function.update s 0 [ballW n K (s 2) (s 1)] := by
  let G : List Bool × Bool → Store 23 := fun a =>
    Function.update (Function.update s 6 a.1) 0 [a.2]
  have hloop := run_forN 12 4 ballBody G
    (fun a => (a.1.drop K, a.2 && absLeW (takeD K a.1) (s 2)))
    (fun a w => run_ballBody hK0 s hs hS hK a w) (s 1, true)
    (Function.update (Function.update s 0 [true]) 6 (s 1)) (by
      funext t; simp only [G]; fin_cases t <;> simp)
  have e0 : run (cp 6 1) (run (sin true 0) (run (cp 0 5) s)) =
      Function.update (Function.update s 0 [true]) 6 (s 1) := by
    obtain ⟨x, hx⟩ : ∃ x, s 5 = [x] := by
      match h : s 5, h1 with
      | [x], _ => exact ⟨x, rfl⟩
    funext t; fin_cases t <;> simp [hx]
  simp only [ballP, run_seq] at e0 ⊢
  rw [e0, hloop]
  have h4 : Function.update (Function.update s 0 [true]) 6 (s 1) 4 = s 4 := by simp
  rw [h4, hn, ball_iter]
  have hb : allN n (fun q => absLeW (takeD K ((s 1).drop (q * K))) (s 2)) = ballW n K (s 2) (s 1) := by
    rw [ballW]
    exact allN_congr fun q hq => by rw [takeD_drop_eq_block hw hq]
  funext t
  simp only [G, run_clear, Bool.true_and, hb]
  fin_cases t <;> simp [hs]

theorem run_ballP_map {u : Fin 23 → Fin k} (hu : Function.Injective u) {n K : ℕ} (hK0 : 0 < K)
    (s : Store k) (hs : ∀ i : Fin 23, 6 ≤ i.val → s (u i) = []) (hw : (s (u 1)).length = n * K)
    (hS : (s (u 2)).length = K) (hK : (s (u 3)).length = K) (hn : (s (u 4)).length = n)
    (h1 : (s (u 5)).length = 1) :
    run (map u ballP) s = Function.update s (u 0) [ballW n K (s (u 2)) (s (u 1))] :=
  run_map_eq_update hu _ s 0 _ (run_ballP hK0 _ hs hw hS hK hn h1)

theorem noGrow_ballP : ballP.NoGrow := rfl
theorem wf_ballP : ballP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
