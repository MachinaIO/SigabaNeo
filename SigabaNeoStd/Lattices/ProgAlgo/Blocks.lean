import SigabaNeoStd.Machines.Prog.Words
import SigabaNeoStd.Machines.Prog.Stream
import SigabaNeoStd.Lattices.Algo.RingWords

/-!
# Block-wise programs on ring words

A ring word (`SigabaNeo.Encode.ringEnc N K`) is `N` blocks of `K` bits. The programs here stream
over the blocks of their inputs; the sizes `N`, `K` are not in the programs but in *templates*:
tapes holding words of length `K` and `N` (any content), copied to counters and registers.

* `BlockSpec K P f`: the program `P : Prog 18` writes `f (s 1) (s 2)` on tape `0` from inputs of
  length `K`, with scratch tapes `3 … 17` blank before and after.
* `bzip P : Prog 28` (tapes `0` output, `1` `x`, `2` `y`, `3` a word of length `K`, `4` a word of
  length `N`; scratch `5 … 27`): `run_bzip`: on words of `N · K` bits it writes
  `concatN N (fun i => f (block K i x) (block K i y))`. Each round moves the next block of each
  input into a register, runs `P`, and shifts the result into the output register.
* `addRWP`, `subRWP`: `addRW N K`, `subRW N K` (`run_addRWP`, `run_subRWP`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k : ℕ}

theorem concatN_succ' (n : ℕ) (h : ℕ → List Bool) :
    concatN (n + 1) h = h 0 ++ concatN n (fun i => h (i + 1)) := by
  induction n with
  | zero => simp [concatN]
  | succ n ih => rw [concatN, ih, concatN, List.append_assoc]

theorem drop_append_of_length {r : List Bool} {n : ℕ} (h : r.length = n) (l : List Bool) :
    (r ++ l).drop n = l := by
  subst h; simp

theorem takeD_drop_eq_block {N K i : ℕ} {x : List Bool} (hx : x.length = N * K) (hi : i < N) :
    takeD K (x.drop (i * K)) = block K i x := by
  rw [takeD_eq_take, block]
  have : i * K + K ≤ N * K := by
    have := Nat.mul_le_mul_right K (show i + 1 ≤ N by omega); rw [Nat.add_mul] at this; simpa
  simp only [List.length_drop, hx]; omega

namespace Prog

open scoped Prog

/-! ### Block programs -/

/-- `P` writes `f (s 1) (s 2)` on tape `0` from inputs of length `K`; its scratch `3 … 17` is
blank before and after. -/
def BlockSpec (K : ℕ) (P : Prog 18) (f : List Bool → List Bool → List Bool) : Prop :=
  ∀ t : Store 18, (∀ i : Fin 18, 3 ≤ i.val → t i = []) → (t 1).length = K → (t 2).length = K →
    run P t = Function.update t 0 (f (t 1) (t 2))

/-- The tapes of a transducer as a block program. -/
def zl : Fin 11 → Fin 18 := ![0, 3, 1, 2, 4, 5, 6, 7, 8, 9, 10]

theorem zl_inj : Function.Injective zl := by decide

/-- A transducer as a block program. -/
def zipB (g : SerOp) (c₀ : Bool) : Prog 18 := map zl (zipW g c₀)

theorem run_zipB (g : SerOp) (c₀ : Bool) (t : Store 18) (ht : ∀ i : Fin 18, 3 ≤ i.val → t i = []) :
    run (zipB g c₀) t = Function.update t 0 (serF g c₀ (t 1) (t 2)) :=
  run_zipW_map zl_inj g c₀ t (fun i hi => by fin_cases i <;> simp_all [zl])
    (by simp [zl, ht 3 (by decide)])

theorem blockSpec_zipB (K : ℕ) (g : SerOp) (c₀ : Bool) :
    BlockSpec K (zipB g c₀) (serF g c₀) := fun t ht _ _ => run_zipB g c₀ t ht

theorem blockSpec_add (K : ℕ) : BlockSpec K (zipB faOp false) addW := fun t ht _ _ => by
  rw [run_zipB _ _ t ht, serF_faOp]; rfl

theorem blockSpec_sub (K : ℕ) : BlockSpec K (zipB fsOp false) subW := fun t ht h1 h2 => by
  rw [run_zipB _ _ t ht, serF_fsOp (h1.trans h2.symm)]

theorem blockSpec_mul (K : ℕ) : BlockSpec K mulP mulW := fun t ht _ _ => run_mulP t ht

/-! ### The block-wise zip -/

def bzX : Fin 5 → Fin 28 := ![5, 7, 9, 11, 3]
def bzY : Fin 5 → Fin 28 := ![6, 8, 9, 11, 3]
def bzZ : Fin 5 → Fin 28 := ![12, 0, 9, 11, 3]
def bzP : Fin 18 → Fin 28 := ![12, 7, 8, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem bzX_inj : Function.Injective bzX := by decide
theorem bzY_inj : Function.Injective bzY := by decide
theorem bzZ_inj : Function.Injective bzZ := by decide
theorem bzP_inj : Function.Injective bzP := by decide

/-- One round. Tapes: `5` `6` the streams of `x`, `y`; `7` `8` the blocks; `9` a bit; `10` the
block counter; `11` the bit counter; `12` the result block; `13 … 27` the scratch of `P`. -/
def bzBody (P : Prog 18) : Prog 28 :=
  cp 7 3 ⨾ map bzX mvP ⨾ cp 8 3 ⨾ map bzY mvP ⨾ map bzP P ⨾ map bzZ mvP ⨾ clr 7 ⨾ clr 8 ⨾ clr 12

/-- **The block-wise zip of a block program.** -/
def bzip (P : Prog 18) : Prog 28 := cp 0 1 ⨾ cp 5 1 ⨾ cp 6 2 ⨾ forN 10 4 (bzBody P) ⨾ clr 5 ⨾ clr 6

/-- The scratch tapes `5 … 27` of `bzip` are blank. -/
def BzClean (s : Store 28) : Prop := ∀ i : Fin 28, 5 ≤ i.val → s i = []

/-- The abstract round: (stream of `x`, stream of `y`, output register). -/
def bstep (K : ℕ) (f : List Bool → List Bool → List Bool) :
    List Bool × List Bool × List Bool → List Bool × List Bool × List Bool
  | (sx, sy, out) => (sx.drop K, sy.drop K, (out ++ f (takeD K sx) (takeD K sy)).drop K)

def bzG (s : Store 28) : List Bool × List Bool × List Bool → Store 28
  | (sx, sy, out) => Function.update (Function.update (Function.update s 5 sx) 6 sy) 0 out

theorem bstep_iter {K : ℕ} {f : List Bool → List Bool → List Bool}
    (hf : ∀ x y, x.length = K → y.length = K → (f x y).length = K) :
    ∀ (N : ℕ) (sx sy out : List Bool), (bstep K f)^[N] (sx, sy, out) =
      (sx.drop (N * K), sy.drop (N * K), (out ++ concatN N (fun i =>
        f (takeD K (sx.drop (i * K))) (takeD K (sy.drop (i * K))))).drop (N * K))
  | 0, sx, sy, out => by simp [concatN]
  | N + 1, sx, sy, out => by
    rw [Function.iterate_succ_apply, bstep, bstep_iter hf N, concatN_succ']
    have hlen : K ≤ (out ++ f (takeD K sx) (takeD K sy)).length := by
      rw [List.length_append, hf _ _ (length_takeD _ _) (length_takeD _ _)]; omega
    have e1 : ∀ l : List Bool, (l.drop K).drop (N * K) = l.drop ((N + 1) * K) := fun l => by
      rw [List.drop_drop]; congr 1; ring
    have e2 : ∀ (l : List Bool) (i : ℕ), (l.drop K).drop (i * K) = l.drop ((i + 1) * K) :=
      fun l i => by rw [List.drop_drop]; congr 1; ring
    simp only [e1, e2, Nat.zero_mul, List.drop_zero, Prod.mk.injEq, true_and]
    rw [← List.drop_append_of_le_length hlen, List.drop_drop, List.append_assoc]
    congr 1; ring

theorem bz_clean_aux (t : Store 28) (ht : ∀ i : Fin 28, 13 ≤ i.val → t i = []) :
    ∀ i : Fin 18, 3 ≤ i.val → (t ∘ bzP) i = [] := by
  intro i hi; fin_cases i <;> simp_all [bzP]

set_option linter.unusedSimpArgs false in
theorem run_bzBody {K : ℕ} {P : Prog 18} {f : List Bool → List Bool → List Bool}
    (hP : BlockSpec K P f) (hf : ∀ x y, x.length = K → y.length = K → (f x y).length = K)
    (s : Store 28) (hs : BzClean s) (hK : (s 3).length = K) (a) (w : List Bool) :
    run (bzBody P) (Function.update (bzG s a) 10 w) = Function.update (bzG s (bstep K f a)) 10 w := by
  obtain ⟨sx, sy, out⟩ := a
  have hc : ∀ i : Fin 28, 7 ≤ i.val → i ≠ 10 → s i = [] := fun i hi _ => hs i (by omega)
  have hPrun : ∀ t : Store 28, (∀ i : Fin 28, 13 ≤ i.val → t i = []) → (t 7).length = K →
      (t 8).length = K → run (map bzP P) t = Function.update t 12 (f (t 7) (t 8)) := by
    intro t ht h7 h8
    exact run_map_eq_update bzP_inj P t 0 _ (hP (t ∘ bzP) (bz_clean_aux t ht) h7 h8)
  have hfK := takeD_of_length' (hf (takeD K sx) (takeD K sy) (length_takeD _ _) (length_takeD _ _))
  simp only [bzBody, run_seq, run_copy, run_clear]
  rw [run_mvP_map bzX_inj _ ?_ ?_, run_mvP_map bzY_inj _ ?_ ?_, hPrun _ ?_ ?_ ?_,
    run_mvP_map bzZ_inj _ ?_ ?_]
  · funext t
    simp only [bzG, bstep]
    fin_cases t <;> simp [bzX, bzY, bzZ, hK, hc, hfK]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [bzG, bzX, bzY, bzZ, hc] at hi ⊢)
    | simp [bzX, bzY, bzZ, bzG, hc, hK]

/-- **The block-wise zip**: on words of `N` blocks of `K` bits, tape `0` receives the word of the
blocks `f xᵢ yᵢ`. -/
theorem run_bzip {K N : ℕ} {P : Prog 18} {f : List Bool → List Bool → List Bool}
    (hP : BlockSpec K P f) (hf : ∀ x y, x.length = K → y.length = K → (f x y).length = K)
    (s : Store 28) (hs : BzClean s) (hK : (s 3).length = K) (hN : (s 4).length = N)
    (hx : (s 1).length = N * K) (hy : (s 2).length = N * K) :
    run (bzip P) s =
      Function.update s 0 (concatN N (fun i => f (block K i (s 1)) (block K i (s 2)))) := by
  have hc : ∀ i : Fin 28, 5 ≤ i.val → s i = [] := hs
  have hloop := run_forN 10 4 (bzBody P) (bzG s) (bstep K f) (run_bzBody hP hf s hs hK)
    (s 1, s 2, s 1) (Function.update (Function.update (Function.update s 0 (s 1)) 5 (s 1)) 6 (s 2))
    (by funext t; simp only [bzG]; fin_cases t <;> simp)
  have e0 : run (cp 6 2) (run (cp 5 1) (run (cp 0 1) s)) =
      Function.update (Function.update (Function.update s 0 (s 1)) 5 (s 1)) 6 (s 2) := by
    funext t; simp only [run_copy]; fin_cases t <;> simp
  simp only [bzip, run_seq]
  rw [e0, hloop, bstep_iter hf]
  simp only [run_clear]
  have hres : (s 1 ++ concatN N (fun i => f (takeD K ((s 1).drop (i * K)))
      (takeD K ((s 2).drop (i * K))))).drop (N * K) =
      concatN N (fun i => f (block K i (s 1)) (block K i (s 2))) := by
    rw [drop_append_of_length hx]
    apply concatN_congr
    intro i hi
    rw [takeD_drop_eq_block hx hi, takeD_drop_eq_block hy hi]
  have h4 : Function.update (Function.update (Function.update s 0 (s 1)) 5 (s 1)) 6 (s 2) 4 = s 4 := by
    simp
  simp only [h4, hN]
  rw [hres]
  funext t
  simp only [bzG]
  fin_cases t <;> simp [hc]

/-! ### Addition and subtraction of ring words -/

/-- `0 := addRW N K (s 1) (s 2)`. -/
def addRWP : Prog 28 := bzip (zipB faOp false)
/-- `0 := subRW N K (s 1) (s 2)`. -/
def subRWP : Prog 28 := bzip (zipB fsOp false)

theorem run_addRWP {K N : ℕ} (s : Store 28) (hs : BzClean s) (hK : (s 3).length = K)
    (hN : (s 4).length = N) (hx : (s 1).length = N * K) (hy : (s 2).length = N * K) :
    run addRWP s = Function.update s 0 (addRW N K (s 1) (s 2)) :=
  run_bzip (blockSpec_add K) (fun x y hx _ => by simp [hx]) s hs hK hN hx hy

theorem run_subRWP {K N : ℕ} (s : Store 28) (hs : BzClean s) (hK : (s 3).length = K)
    (hN : (s 4).length = N) (hx : (s 1).length = N * K) (hy : (s 2).length = N * K) :
    run subRWP s = Function.update s 0 (subRW N K (s 1) (s 2)) :=
  run_bzip (blockSpec_sub K) (fun x y hx _ => by simp [hx]) s hs hK hN hx hy

theorem noGrow_addRWP : addRWP.NoGrow := rfl
theorem noGrow_subRWP : subRWP.NoGrow := rfl
theorem wf_addRWP : addRWP.WF := wf_of_wfB (by decide)
theorem wf_subRWP : subRWP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
