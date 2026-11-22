import SigabaNeo.Lib.Lattices.ProgAlgo.Blocks
import SigabaNeo.Lib.Lattices.Algo.MatWords

/-!
# Entrywise sums of matrix words as tape programs

A word of `L` ring entries is a word of `L · N` blocks of `K` bits, and the entrywise operations
are the block-wise ones: `matAddW N K L = addRW (L * N) K` (`matAddW_eq_addRW`). So the programs
`addRWP`, `subRWP` with a template of length `L · N` on tape `4` compute `matAddW`, `matSubW`
(`run_addRWP_mat`, `run_subRWP_mat`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

theorem concatN_add (m n : ℕ) (g : ℕ → List Bool) :
    concatN (m + n) g = concatN m g ++ concatN n (fun i => g (m + i)) := by
  induction n with
  | zero => simp [concatN]
  | succ n ih => rw [← Nat.add_assoc, concatN, ih, concatN, List.append_assoc]

theorem concatN_mul (a b : ℕ) (g : ℕ → List Bool) :
    concatN (a * b) g = concatN a (fun p => concatN b (fun i => g (p * b + i))) := by
  induction a with
  | zero => simp [concatN]
  | succ a ih => rw [Nat.succ_mul, concatN_add, ih, concatN]

theorem block_block {N K p i : ℕ} (x : List Bool) (hi : i < N) :
    block K i (block (N * K) p x) = block K (p * N + i) x := by
  have hle : i * K + K ≤ N * K := by
    have := Nat.mul_le_mul_right K (show i + 1 ≤ N by omega); rw [Nat.add_mul] at this; simpa
  simp only [block, List.drop_take, List.take_take, List.drop_drop]
  have hc := Nat.mul_comm K i
  congr 1
  all_goals first | (apply Nat.min_eq_left; omega) | (congr 1; ring)

/-- Entrywise operations on `L` ring entries are block-wise operations on `L · N` blocks. -/
theorem concatN_entries (N K L : ℕ) (f : List Bool → List Bool → List Bool) (x y : List Bool) :
    concatN L (fun p => concatN N (fun i => f (block K i (block (N * K) p x))
      (block K i (block (N * K) p y)))) =
      concatN (L * N) (fun q => f (block K q x) (block K q y)) := by
  rw [concatN_mul]
  apply concatN_congr
  intro p _
  apply concatN_congr
  intro i hi
  rw [block_block x hi, block_block y hi]

theorem matAddW_eq_addRW (N K L : ℕ) (x y : List Bool) : matAddW N K L x y = addRW (L * N) K x y :=
  concatN_entries N K L addW x y

theorem matSubW_eq_subRW (N K L : ℕ) (x y : List Bool) : matSubW N K L x y = subRW (L * N) K x y :=
  concatN_entries N K L subW x y

namespace Prog

theorem run_addRWP_mat {K N L : ℕ} (s : Store 28) (hs : BzClean s) (hK : (s 3).length = K)
    (hLN : (s 4).length = L * N) (hx : (s 1).length = L * N * K) (hy : (s 2).length = L * N * K) :
    run addRWP s = Function.update s 0 (matAddW N K L (s 1) (s 2)) := by
  rw [matAddW_eq_addRW]; exact run_addRWP s hs hK hLN hx hy

theorem run_subRWP_mat {K N L : ℕ} (s : Store 28) (hs : BzClean s) (hK : (s 3).length = K)
    (hLN : (s 4).length = L * N) (hx : (s 1).length = L * N * K) (hy : (s 2).length = L * N * K) :
    run subRWP s = Function.update s 0 (matSubW N K L (s 1) (s 2)) := by
  rw [matSubW_eq_subRW]; exact run_subRWP s hs hK hLN hx hy

end Prog

end SigabaNeo.Tape
