import Definitions.Def_EvLWE
import CslibFrontier.Tactic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# The Post attack of [DJMMV25] (Lemma 5.1), as a typed program

On a sample `(q, C, K, aux)` with `ℓ = 1` (`C` and `aux` are rows):

1. `kBit r j`: the parity of the integer `K[r][j]`, read from its representative `x ∈ [0, q)` as
   `x` if `2x < q` and `x − q` otherwise (`q` odd).
2. `depMask`: a nonempty set `u` of columns among `0, …, m` with `Σ_{j ∈ u} K_j ≡ 0 (mod 2)`, found by
   Gaussian elimination over GF(2) (columns as `m`-bit numbers, a basis of
   `(pivot, vector, mask)` triples, each mask recording which columns a vector combines).
3. Output `true` iff `Σ_{j ∈ u} ((c·K_j − aux_j) mod q)` is even.

On the real side `c·K_j − aux_j = e·K_j + 2·t_j (mod q)`, which does not wrap around for short `e`,
`K` and `t_j` away from the ends of its range, so the sum is `e·Σ_{j∈u} K_j + 2·Σ t_j`: even.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM TestCase

/-! ### Reading the sample -/

/-- The `idx`-th `W`-bit number of the sample. -/
def entryAt (κ : ℕ) (word : List Bool) (idx : ℕ) : ℕ :=
  Cslib.Matrix.binaryEntry 1 (EvLWE.W κ) word idx 0

def qOf (κ : ℕ) (word : List Bool) : ℕ := entryAt κ word 0
def cAt (κ : ℕ) (word : List Bool) (r : ℕ) : ℕ := entryAt κ word (1 + r)
def kAt (κ : ℕ) (word : List Bool) (r j : ℕ) : ℕ :=
  entryAt κ word (1 + EvLWE.m κ + r * EvLWE.k κ + j)
def auxAt (κ : ℕ) (word : List Bool) (j : ℕ) : ℕ :=
  entryAt κ word (1 + EvLWE.m κ + EvLWE.m κ * EvLWE.k κ + j)

/-- The parity of the integer that the representative `K[r][j]` stands for. -/
def kBit (κ : ℕ) (word : List Bool) (r j : ℕ) : ℕ :=
  if 2 * kAt κ word r j < qOf κ word then kAt κ word r j % 2 else (kAt κ word r j + 1) % 2

/-- Column `j` of `K mod 2`, as an `m`-bit number. -/
def colVec (κ : ℕ) (word : List Bool) (j : ℕ) : ℕ :=
  ((List.range (EvLWE.m κ)).map fun r => kBit κ word r j * 2 ^ r).sum

/-! ### Elimination over GF(2) -/

/-- Reduce `(v, mask)` by one basis triple `(pivot, vector, mask)`. Results are kept below `2^M`
(a no-op on the attack's data, where every number has at most `M = m + 1` bits); this bounds the
size of every intermediate state. -/
def reduceStep (M : ℕ) (acc : ℕ × ℕ) (b : ℕ × ℕ × ℕ) : ℕ × ℕ :=
  if acc.1.testBit b.1 then ((acc.1 ^^^ b.2.1) % 2 ^ M, (acc.2 ^^^ b.2.2) % 2 ^ M) else acc

def reduce (M : ℕ) (basis : List (ℕ × ℕ × ℕ)) (v mk : ℕ) : ℕ × ℕ :=
  basis.foldl (reduceStep M) (v % 2 ^ M, mk % 2 ^ M)

/-- Process column `j`: stop once a dependency is found; otherwise reduce the column and either
record the dependency or add it to the basis. -/
def elimStep (κ : ℕ) (word : List Bool) (st : List (ℕ × ℕ × ℕ) × ℕ) (j : ℕ) :
    List (ℕ × ℕ × ℕ) × ℕ :=
  if st.2 == 0 then
    if (reduce (EvLWE.m κ + 1) st.1 (colVec κ word j) (2 ^ j)).1 == 0 then
      (st.1, (reduce (EvLWE.m κ + 1) st.1 (colVec κ word j) (2 ^ j)).2)
    else (st.1 ++ [(Nat.log 2 (reduce (EvLWE.m κ + 1) st.1 (colVec κ word j) (2 ^ j)).1,
      reduce (EvLWE.m κ + 1) st.1 (colVec κ word j) (2 ^ j))], 0)
  else st

/-- The dependency among columns `0, …, m`, as a bit mask (`0` if none was found). -/
def depMask (κ : ℕ) (word : List Bool) : ℕ :=
  ((List.range (EvLWE.m κ + 1)).foldl (elimStep κ word) ([], 0)).2

/-! ### The test -/

/-- `(c·K_j − aux_j) mod q`, from representatives. -/
def wAt (κ : ℕ) (word : List Bool) (j : ℕ) : ℕ :=
  (((List.range (EvLWE.m κ)).map fun r => cAt κ word r * kAt κ word r j).sum +
    (qOf κ word - auxAt κ word j)) % qOf κ word

def parityOut (κ : ℕ) (word : List Bool) : Bool :=
  decide (((List.range (EvLWE.m κ + 1)).map fun j =>
    if (depMask κ word).testBit j then wAt κ word j else 0).sum % 2 = 0)

/-- The distinguisher. -/
noncomputable def attack : Distinguisher := fun κ word => pure (parityOut κ word)

end TestCase.EvLWE
