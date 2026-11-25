import SigabaNeoStd.Lattices.ProgAlgo.Spec

/-!
# Products with binary matrices as a tape program

`binMulP : Prog 53` computes, for a `2 × d` matrix `A = [B; C]` of ring words and `I` binary
matrices `Rᵢ` (`d × L`, given **column by column**: for each column the `d` entries, each the word
of a `0/1` ring element, whose first bit is the bit), the words of `A · Rᵢ + xᵢ G` (`G` a fixed
`2 × L` word, `xᵢ` a bit), one after the other. A binary product is a sum of subsets: the entry
`(r, c)` of `A · Rᵢ` is the sum of the entries `A r a` over the rows `a` with a bit `1` in the
column `c`. So the program only adds ring words (`addRWP`): for each `i`, for each column, two
accumulators run over the `d` entries; the column sums are shifted into two row registers, the
rows into a register `Q`, `G` is added when `xᵢ = 1`, and `Q` is shifted into the output.

Tapes: `0` the output register; `1` `B`, `2` `C` (rows of `d` entries); `3` the stream of the
`Rᵢ`; `4` the stream of the bits `xᵢ`; `5` `G`; templates `6` (`K`), `7` (`N`), `8` (`N K`
zeros), `9` (`d`), `10` (`L`), `11` (`I`), `12` (`L · N K` zeros), `13` (`2 L · N K` zeros),
`14` (`2 L · N`); scratch `15 … 52`, blank before and after.

**`run_binMulP`**: the output register receives `binMulW` (`iStepB` iterated `I` times).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k : ℕ}

namespace Prog

/-! ### The abstract steps -/

/-- One entry `a` of a column: add the entries of `B`, `C` when the bit is `1`. -/
def aStepB (N K : ℕ) :
    List Bool × List Bool × List Bool × List Bool × List Bool →
      List Bool × List Bool × List Bool × List Bool × List Bool
  | (x0, x1, rs, bs, cs) =>
    (if hd rs = true then addRW N K x0 (takeD (N * K) bs) else x0,
      if hd rs = true then addRW N K x1 (takeD (N * K) cs) else x1,
      rs.drop (N * K), bs.drop (N * K), cs.drop (N * K))

/-- The two sums of a column (and the rest of the stream). -/
def colB (N K d : ℕ) (b c rs : List Bool) : List Bool × List Bool × List Bool × List Bool × List Bool :=
  (aStepB N K)^[d] (List.replicate (N * K) false, List.replicate (N * K) false, rs, b, c)

/-- One column: shift the two sums into the row registers. -/
def cStepB (N K d : ℕ) (b c : List Bool) :
    List Bool × List Bool × List Bool → List Bool × List Bool × List Bool
  | (r0, r1, rs) =>
    ((r0 ++ takeD (N * K) (colB N K d b c rs).1).drop (N * K),
      (r1 ++ takeD (N * K) (colB N K d b c rs).2.1).drop (N * K),
      (colB N K d b c rs).2.2.1)

/-- The rows of `A · Rᵢ` (and the rest of the stream). -/
def rowsB (N K d L : ℕ) (b c rs : List Bool) : List Bool × List Bool × List Bool :=
  (cStepB N K d b c)^[L]
    (List.replicate (L * (N * K)) false, List.replicate (L * (N * K)) false, rs)

/-- The word of `A · Rᵢ + xᵢ G` from the rows. -/
def qB (N K L : ℕ) (g : List Bool) (x : Bool) (r0 r1 : List Bool) : List Bool :=
  let q := ((List.replicate (2 * L * (N * K)) false ++ takeD (L * (N * K)) r0).drop (L * (N * K)) ++
    takeD (L * (N * K)) r1).drop (L * (N * K))
  if x then addRW (2 * L * N) K q g else q

/-- One matrix `i`: shift `A · Rᵢ + xᵢ G` into the output. -/
def iStepB (N K d L : ℕ) (b c g : List Bool) :
    List Bool × List Bool × List Bool → List Bool × List Bool × List Bool
  | (out, rs, xs) =>
    ((out ++ takeD (2 * L * (N * K)) (qB N K L g (hd xs) (rowsB N K d L b c rs).1
        (rowsB N K d L b c rs).2.1)).drop (2 * L * (N * K)),
      (rowsB N K d L b c rs).2.2, xs.tail)

/-! ### The program -/

/-- Move `N K` bits of the stream `s` into the register `24`. -/
def mvYB (s : Fin 53) : Fin 5 → Fin 53 := ![s, 24, 27, 28, 8]
/-- The sum into `25`. -/
def addXB (x : Fin 53) : Fin 28 → Fin 53 := ![25, x, 24, 6, 7, 30, 31, 32, 33, 34, 35, 36, 37, 38,
  39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
/-- Drop `N K` bits of the stream `s`. -/
def dpBB (s : Fin 53) : Fin 3 → Fin 53 := ![s, 29, 8]
/-- Shift `N K` bits of `x` into the row register `r`. -/
def mvRB (x r : Fin 53) : Fin 5 → Fin 53 := ![x, r, 27, 28, 8]
/-- Shift a row into `Q`. -/
def mvQB (r : Fin 53) : Fin 5 → Fin 53 := ![r, 26, 27, 28, 12]
/-- Add `G` to `Q`. -/
def addGB : Fin 28 → Fin 53 := ![25, 26, 5, 6, 14, 30, 31, 32, 33, 34, 35, 36, 37, 38,
  39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
/-- Shift `Q` into the output. -/
def mvOB : Fin 5 → Fin 53 := ![26, 0, 27, 28, 13]

theorem mvYB_inj (s : Fin 53) (hs : s = 22 ∨ s = 23) : Function.Injective (mvYB s) := by
  rcases hs with rfl | rfl <;> decide
theorem addXB_inj (x : Fin 53) (hx : x = 20 ∨ x = 21) : Function.Injective (addXB x) := by
  rcases hx with rfl | rfl <;> decide
theorem dpBB_inj (s : Fin 53) (hs : s = 22 ∨ s = 23 ∨ s = 3) : Function.Injective (dpBB s) := by
  rcases hs with rfl | rfl | rfl <;> decide
theorem mvRB_inj (x r : Fin 53) (h : (x = 20 ∧ r = 18) ∨ (x = 21 ∧ r = 19)) :
    Function.Injective (mvRB x r) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
theorem mvQB_inj (r : Fin 53) (h : r = 18 ∨ r = 19) : Function.Injective (mvQB r) := by
  rcases h with rfl | rfl <;> decide
theorem addGB_inj : Function.Injective addGB := by decide
theorem mvOB_inj : Function.Injective mvOB := by decide

open scoped Prog

/-- Add the next entry of the stream `s` to the accumulator `x`. -/
def addEntry (x s : Fin 53) : Prog 53 :=
  cp 24 8 ⨾ map (mvYB s) mvP ⨾ map (addXB x) addRWP ⨾ cp x 25 ⨾ clr 25 ⨾ clr 24

/-- One entry of a column. -/
def aBodyB : Prog 53 :=
  ifBit 3 (addEntry 20 22 ⨾ addEntry 21 23) (map (dpBB 22) dropP ⨾ map (dpBB 23) dropP) ⨾
    map (dpBB 3) dropP

/-- One column. -/
def cBodyB : Prog 53 :=
  cp 20 8 ⨾ cp 21 8 ⨾ cp 22 1 ⨾ cp 23 2 ⨾ forN 17 9 aBodyB ⨾ map (mvRB 20 18) mvP ⨾
    map (mvRB 21 19) mvP ⨾ clr 20 ⨾ clr 21 ⨾ clr 22 ⨾ clr 23

/-- One matrix. -/
def iBodyB : Prog 53 :=
  cp 18 12 ⨾ cp 19 12 ⨾ forN 16 10 cBodyB ⨾ cp 26 13 ⨾ map (mvQB 18) mvP ⨾ map (mvQB 19) mvP ⨾
    ifBit 4 (map addGB addRWP ⨾ cp 26 25 ⨾ clr 25) (nop 25) ⨾ tl 4 ⨾ map mvOB mvP ⨾ clr 18 ⨾
    clr 19 ⨾ clr 26

/-- **The products with the binary matrices.** -/
def binMulP : Prog 53 := forN 15 11 iBodyB


/-! ### An entry -/

/-- The scratch of an entry is blank. -/
def EClean (S : Store 53) : Prop :=
  S 24 = [] ∧ S 25 = [] ∧ S 27 = [] ∧ S 28 = [] ∧ S 29 = [] ∧ ∀ i : Fin 53, 30 ≤ i.val → S i = []

set_option maxHeartbeats 4000000 in
theorem run_addEntry {N K : ℕ} (x s : Fin 53) (hx : x = 20 ∨ x = 21) (hs : s = 22 ∨ s = 23)
    (S : Store 53) (hS : EClean S) (hK : (S 6).length = K) (hN : (S 7).length = N)
    (hNK : (S 8).length = N * K) (hxl : (S x).length = N * K) :
    run (addEntry x s) S =
      Function.update (Function.update S x (addRW N K (S x) (takeD (N * K) (S s)))) s
        ((S s).drop (N * K)) := by
  obtain ⟨h24, h25, h27, h28, h29, hsc⟩ := hS
  have hxs : x ≠ s := by rcases hx with rfl | rfl <;> rcases hs with rfl | rfl <;> decide
  simp only [addEntry, run_seq, run_copy, run_clear]
  rw [run_mvP_map (mvYB_inj s hs) _ ?_ ?_, run_addRWP_map (addXB_inj x hx) (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    rcases hx with rfl | rfl <;> rcases hs with rfl | rfl <;>
      fin_cases t <;> simp [mvYB, addXB, h24, h25, hNK, List.drop_left' hNK, hsc]
  all_goals first
    | (intro i hi; rcases hx with rfl | rfl <;> rcases hs with rfl | rfl <;>
        fin_cases i <;> simp [mvYB, addXB, hsc] at hi ⊢)
    | (rcases hx with rfl | rfl <;> rcases hs with rfl | rfl <;>
        simp [mvYB, addXB, h24, h25, h27, h28, hK, hN, hNK, hxl, List.drop_left' hNK])


/-! ### A column -/

/-- The store of an entry round. -/
def aGB (S : Store 53) : List Bool × List Bool × List Bool × List Bool × List Bool → Store 53
  | (x0, x1, rs, bs, cs) => Function.update (Function.update (Function.update (Function.update
      (Function.update S 20 x0) 21 x1) 3 rs) 22 bs) 23 cs

set_option maxHeartbeats 4000000 in
theorem run_aBodyB {N K : ℕ} (S : Store 53) (hS : EClean S) (hK : (S 6).length = K)
    (hN : (S 7).length = N) (hNK : (S 8).length = N * K) (a)
    (ha : a.1.length = N * K ∧ a.2.1.length = N * K) (w : List Bool) :
    run aBodyB (Function.update (aGB S a) 17 w) = Function.update (aGB S (aStepB N K a)) 17 w := by
  obtain ⟨x0, x1, rs, bs, cs⟩ := a
  obtain ⟨h0, h1⟩ := ha
  simp only at h0 h1
  have hE : EClean (Function.update (aGB S (x0, x1, rs, bs, cs)) 17 w) := by
    obtain ⟨h24, h25, h27, h28, h29, hsc⟩ := hS
    refine ⟨by simp [aGB, h24], by simp [aGB, h25], by simp [aGB, h27], by simp [aGB, h28],
      by simp [aGB, h29], fun i hi => ?_⟩
    fin_cases i <;> simp at hi <;> simp [aGB, hsc]
  have hdp : ∀ (t : Fin 53) (ht : t = 22 ∨ t = 23 ∨ t = 3) (T : Store 53), T 29 = [] →
      T 8 = S 8 → run (map (dpBB t) dropP) T = Function.update T t ((T t).drop (N * K)) := by
    intro t ht T h29 h8
    rw [run_dropP_map (dpBB_inj t ht) _ (by rcases ht with rfl | rfl | rfl <;> simpa [dpBB])]
    rcases ht with rfl | rfl | rfl <;> simp [dpBB, h8, hNK]
  simp only [aBodyB, run_seq, run_ifBit]
  have h3 : Function.update (aGB S (x0, x1, rs, bs, cs)) 17 w 3 = rs := by simp [aGB]
  rw [h3]
  by_cases hb : hd rs = true
  · rw [if_pos hb, run_addEntry (N := N) (K := K) 20 22 (Or.inl rfl) (Or.inl rfl) _ hE (by simp [aGB, hK])
      (by simp [aGB, hN]) (by simp [aGB, hNK]) (by simp [aGB, h0])]
    rw [run_addEntry (N := N) (K := K) 21 23 (Or.inr rfl) (Or.inr rfl) _ ?_ (by simp [aGB, hK])
      (by simp [aGB, hN]) (by simp [aGB, hNK]) (by simp [aGB, h1])]
    · rw [hdp 3 (Or.inr (Or.inr rfl)) _ (by obtain ⟨-, -, -, -, h29, -⟩ := hS; simp [aGB, h29])
        (by simp [aGB])]
      funext t
      fin_cases t <;> simp [aGB, aStepB, hb]
    · obtain ⟨h24, h25, h27, h28, h29, hsc⟩ := hS
      refine ⟨by simp [aGB, h24], by simp [aGB, h25], by simp [aGB, h27], by simp [aGB, h28],
        by simp [aGB, h29], fun i hi => ?_⟩
      fin_cases i <;> simp at hi <;> simp [aGB, hsc]
  · rw [if_neg hb]
    obtain ⟨h24, h25, h27, h28, h29, hsc⟩ := hS
    rw [hdp 22 (Or.inl rfl) _ (by simp [aGB, h29]) (by simp [aGB]),
      hdp 23 (Or.inr (Or.inl rfl)) _ (by simp [aGB, h29]) (by simp [aGB]),
      hdp 3 (Or.inr (Or.inr rfl)) _ (by simp [aGB, h29]) (by simp [aGB])]
    funext t
    fin_cases t <;> simp [aGB, aStepB, hb]


theorem aStepB_len {N K : ℕ} (a : List Bool × List Bool × List Bool × List Bool × List Bool)
    (ha : a.1.length = N * K ∧ a.2.1.length = N * K) :
    (aStepB N K a).1.length = N * K ∧ (aStepB N K a).2.1.length = N * K := by
  obtain ⟨x0, x1, rs, bs, cs⟩ := a
  obtain ⟨h0, h1⟩ := ha
  simp only [aStepB]
  split_ifs <;> exact ⟨by first | exact length_addRW N K h0 _ | exact h0,
    by first | exact length_addRW N K h1 _ | exact h1⟩

theorem colB_len {N K d : ℕ} (b c rs : List Bool) :
    (colB N K d b c rs).1.length = N * K ∧ (colB N K d b c rs).2.1.length = N * K := by
  unfold colB
  generalize d = m
  induction m with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply']; exact aStepB_len _ ih

/-- The store of a column round. -/
def cGB (S : Store 53) : List Bool × List Bool × List Bool → Store 53
  | (r0, r1, rs) => Function.update (Function.update (Function.update S 18 r0) 19 r1) 3 rs

/-- The scratch of a column is blank. -/
def CClean (S : Store 53) : Prop := S 17 = [] ∧ ∀ i : Fin 53, 20 ≤ i.val → S i = []

set_option maxHeartbeats 8000000 in
theorem run_cBodyB {N K d : ℕ} (S : Store 53) (hS : CClean S) (hK : (S 6).length = K)
    (hN : (S 7).length = N) (hNK : S 8 = List.replicate (N * K) false) (hd : (S 9).length = d)
    (a) (w : List Bool) :
    run cBodyB (Function.update (cGB S a) 16 w) =
      Function.update (cGB S (cStepB N K d (S 1) (S 2) a)) 16 w := by
  obtain ⟨r0, r1, rs⟩ := a
  obtain ⟨h17, hsc⟩ := hS
  have hNKl : (S 8).length = N * K := by rw [hNK, List.length_replicate]
  set T := Function.update (cGB S (r0, r1, rs)) 16 w with hT
  have e0 : run (cp 23 2) (run (cp 22 1) (run (cp 21 8) (run (cp 20 8) T))) =
      aGB T (S 8, S 8, rs, S 1, S 2) := by
    funext t; simp only [run_copy, aGB, hT, cGB]
    fin_cases t <;> simp [hsc]
  have hloop := run_forN_inv 17 9 aBodyB (aGB T) (aStepB N K)
    (fun a => a.1.length = N * K ∧ a.2.1.length = N * K)
    (fun a w' ha => run_aBodyB T ⟨by simp [hT, cGB, hsc], by simp [hT, cGB, hsc],
      by simp [hT, cGB, hsc], by simp [hT, cGB, hsc], by simp [hT, cGB, hsc],
      fun i hi => by simp only [hT, cGB]; fin_cases i <;> simp at hi <;> simp [hsc]⟩
      (by simp [hT, cGB, hK]) (by simp [hT, cGB, hN]) (by simp [hT, cGB, hNKl]) a ha w')
    (fun a ha => aStepB_len a ha) (S 8, S 8, rs, S 1, S 2) ⟨hNKl, hNKl⟩ _ rfl
  have hsplit : run cBodyB T = run (map (mvRB 20 18) mvP ⨾ map (mvRB 21 19) mvP ⨾ clr 20 ⨾ clr 21 ⨾
      clr 22 ⨾ clr 23) (run (forN 17 9 aBodyB)
        (run (cp 23 2) (run (cp 22 1) (run (cp 21 8) (run (cp 20 8) T))))) := rfl
  rw [hsplit, e0, hloop]
  have hc := colB_len (N := N) (K := K) (d := d) (S 1) (S 2) rs
  simp only [run_seq, run_clear]
  rw [run_mvP_map (mvRB_inj 20 18 (Or.inl ⟨rfl, rfl⟩)) _ ?_ ?_,
    run_mvP_map (mvRB_inj 21 19 (Or.inr ⟨rfl, rfl⟩)) _ ?_ ?_]
  · have e9 : aGB T (S 8, S 8, rs, S 1, S 2) 9 = S 9 := by simp [aGB, hT, cGB]
    rw [e9, hd]
    simp only [colB, hNK] at hc
    funext t
    fin_cases t <;> simp [aGB, hT, cGB, mvRB, cStepB, colB, hsc, h17, hNKl, hNK]
  all_goals simp [aGB, hT, cGB, mvRB, hsc]

/-! ### A matrix -/

theorem cStepB_len {N K d : ℕ} (b c : List Bool) (L : ℕ) (a : List Bool × List Bool × List Bool)
    (ha : a.1.length = L ∧ a.2.1.length = L) :
    (cStepB N K d b c a).1.length = L ∧ (cStepB N K d b c a).2.1.length = L := by
  obtain ⟨r0, r1, rs⟩ := a
  obtain ⟨h0, h1⟩ := ha
  simp [cStepB, h0, h1]

theorem rowsB_len {N K d L : ℕ} (b c rs : List Bool) :
    (rowsB N K d L b c rs).1.length = L * (N * K) ∧
      (rowsB N K d L b c rs).2.1.length = L * (N * K) := by
  have : ∀ m (a : List Bool × List Bool × List Bool), a.1.length = L * (N * K) →
      a.2.1.length = L * (N * K) →
      ((cStepB N K d b c)^[m] a).1.length = L * (N * K) ∧
        ((cStepB N K d b c)^[m] a).2.1.length = L * (N * K) := by
    intro m
    induction m with
    | zero => intro a h0 h1; exact ⟨h0, h1⟩
    | succ m ih =>
      intro a h0 h1
      rw [Function.iterate_succ_apply']
      exact cStepB_len b c _ _ (ih a h0 h1)
  exact this L _ (by simp) (by simp)


/-- The store of a matrix round. -/
def iGB (S : Store 53) : List Bool × List Bool × List Bool → Store 53
  | (out, rs, xs) => Function.update (Function.update (Function.update S 0 out) 3 rs) 4 xs

/-- The scratch of the program is blank. -/
def IClean (S : Store 53) : Prop := ∀ i : Fin 53, 15 ≤ i.val → S i = []

set_option maxHeartbeats 8000000 in
theorem run_iBodyB {N K d L : ℕ} (S : Store 53) (hS : IClean S) (hK : (S 6).length = K)
    (hN : (S 7).length = N) (hNK : S 8 = List.replicate (N * K) false) (hd : (S 9).length = d)
    (hL : (S 10).length = L) (h12 : S 12 = List.replicate (L * (N * K)) false)
    (h13 : S 13 = List.replicate (2 * L * (N * K)) false) (h14 : (S 14).length = 2 * L * N)
    (hG : (S 5).length = 2 * L * (N * K)) (a) (w : List Bool) :
    run iBodyB (Function.update (iGB S a) 15 w) =
      Function.update (iGB S (iStepB N K d L (S 1) (S 2) (S 5) a)) 15 w := by
  obtain ⟨out, rs, xs⟩ := a
  have hS : ∀ i : Fin 53, 15 ≤ i.val → S i = [] := hS
  have hNKl : (S 8).length = N * K := by rw [hNK, List.length_replicate]
  set T := Function.update (iGB S (out, rs, xs)) 15 w with hT
  have e0 : run (cp 19 12) (run (cp 18 12) T) = cGB T (S 12, S 12, rs) := by
    funext t; simp only [run_copy, cGB, hT, iGB]
    fin_cases t <;> simp [hS]
  have hloop := run_forN 16 10 cBodyB (cGB T) (cStepB N K d (S 1) (S 2))
    (fun a w' => by
      have := run_cBodyB (N := N) (K := K) (d := d) T
        ⟨by simp [hT, iGB, hS], fun i hi => by simp only [hT, iGB]; fin_cases i <;> simp at hi <;> simp [hS]⟩
        (by simp [hT, iGB, hK]) (by simp [hT, iGB, hN]) (by simp [hT, iGB, hNK])
        (by simp [hT, iGB, hd]) a w'
      simpa [hT, iGB] using this)
    (S 12, S 12, rs) _ rfl
  have hsplit : run iBodyB T = run (cp 26 13 ⨾ map (mvQB 18) mvP ⨾ map (mvQB 19) mvP ⨾
      ifBit 4 (map addGB addRWP ⨾ cp 26 25 ⨾ clr 25) (nop 25) ⨾ tl 4 ⨾ map mvOB mvP ⨾ clr 18 ⨾
      clr 19 ⨾ clr 26) (run (forN 16 10 cBodyB) (run (cp 19 12) (run (cp 18 12) T))) := rfl
  rw [hsplit, e0, hloop]
  have e10 : cGB T (S 12, S 12, rs) 10 = S 10 := by simp [cGB, hT, iGB]
  rw [e10, hL]
  have hr := rowsB_len (N := N) (K := K) (d := d) (L := L) (S 1) (S 2) rs
  simp only [rowsB, h12] at hr
  set R := (cStepB N K d (S 1) (S 2))^[L] (List.replicate (L * (N * K)) false,
    List.replicate (L * (N * K)) false, rs) with hR
  rw [h12]
  simp only [run_seq, run_copy, run_clear, run_tail, run_ifBit]
  rw [run_mvP_map (mvQB_inj 18 (Or.inl rfl)) _ ?_ ?_, run_mvP_map (mvQB_inj 19 (Or.inr rfl)) _ ?_ ?_]
  rotate_left
  · simp [cGB, hT, iGB, mvQB, hS]
  · simp [cGB, hT, iGB, mvQB, hS]
  · simp [cGB, hT, iGB, mvQB, hS]
  · simp [cGB, hT, iGB, mvQB, hS]
  have hRl : R.1.length = L * (N * K) ∧ R.2.1.length = L * (N * K) := hr
  by_cases hx : Tape.hd xs = true
  · simp only [mvQB, cGB, hT, iGB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Function.update_apply, show (4 : Fin 53) ≠ 26 by decide, show (4 : Fin 53) ≠ 18 by decide,
      show (4 : Fin 53) ≠ 19 by decide, show (4 : Fin 53) ≠ 15 by decide,
      show (4 : Fin 53) ≠ 3 by decide, show (4 : Fin 53) ≠ 0 by decide, if_true, if_false, hx,
      ↓reduceIte]
    rw [run_addRWP_map addGB_inj (K := K) (N := 2 * L * N) _ ?_ ?_ ?_ ?_ ?_]
    · rw [run_mvP_map mvOB_inj _ ?_ ?_]
      · funext t
        fin_cases t <;> simp [mvOB, addGB, iStepB, qB, rowsB, hx, hS, h12, h13, ← hR]
      all_goals simp [mvOB, addGB, hS, hx]
    all_goals first
      | (intro i hi; fin_cases i <;> simp [addGB, hS] at hi ⊢)
      | (simp [addGB, hS, hK, h14, hG, h12, h13, hRl, hx]; try ring)
  · simp only [mvQB, cGB, hT, iGB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Function.update_apply, show (4 : Fin 53) ≠ 26 by decide, show (4 : Fin 53) ≠ 18 by decide,
      show (4 : Fin 53) ≠ 19 by decide, show (4 : Fin 53) ≠ 15 by decide,
      show (4 : Fin 53) ≠ 3 by decide, show (4 : Fin 53) ≠ 0 by decide, if_true, if_false, hx,
      ↓reduceIte, run_nop]
    rw [run_mvP_map mvOB_inj _ ?_ ?_]
    · funext t
      fin_cases t <;> simp [mvOB, iStepB, qB, rowsB, hx, hS, h12, h13, ← hR]
    all_goals simp [mvOB, hS, hx]


/-- **The products with the binary matrices**: the output register receives, for each of the
`|s 11|` matrices, the word `qB` of `A · Rᵢ + xᵢ G`; the streams `3`, `4` are consumed. -/
theorem run_binMulP {N K d L : ℕ} (S : Store 53) (hS : IClean S) (hK : (S 6).length = K)
    (hN : (S 7).length = N) (hNK : S 8 = List.replicate (N * K) false) (hd : (S 9).length = d)
    (hL : (S 10).length = L) (h12 : S 12 = List.replicate (L * (N * K)) false)
    (h13 : S 13 = List.replicate (2 * L * (N * K)) false) (h14 : (S 14).length = 2 * L * N)
    (hG : (S 5).length = 2 * L * (N * K)) :
    run binMulP S = iGB S ((iStepB N K d L (S 1) (S 2) (S 5))^[(S 11).length] (S 0, S 3, S 4)) := by
  have h := run_forN 15 11 iBodyB (iGB S) (iStepB N K d L (S 1) (S 2) (S 5))
    (fun a w => run_iBodyB S hS hK hN hNK hd hL h12 h13 h14 hG a w) (S 0, S 3, S 4) S
    (by funext t; simp only [iGB]; fin_cases t <;> simp)
  rw [binMulP, h]
  funext t
  have hS : ∀ i : Fin 53, 15 ≤ i.val → S i = [] := hS
  simp only [iGB]
  fin_cases t <;> simp [hS]

theorem noGrow_binMulP : binMulP.NoGrow := rfl
theorem wf_binMulP : binMulP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
