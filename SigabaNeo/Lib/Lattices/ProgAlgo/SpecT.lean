import SigabaNeo.Lib.Machines.Prog.AbsBound
import SigabaNeo.Lib.Lattices.ProgAlgo.Spec

/-!
# The word algorithms as tape programs: per-tape bounds

`SigabaNeo.Lib.Lattices.ProgAlgo.Spec` bounds the time of each word program by `C · (L + 1) ^ d`
for one global bound `L` on every word, so every loop is charged `L` rounds. Here the bounds are
**per tape** (`lenBoundT`, `timeBoundT` of `SigabaNeo.Lib.Machines.Prog.BoundsT`): the tapes hold
words of their actual lengths (operands of `N · K` bits, templates of lengths `N`, `K`, `m`, …;
scratch blank), and each loop is charged the length of its own counter. The bounds are certified by
the abstract interpreter of `SigabaNeo.Lib.Machines.Prog.AbsBound` (`check … = true` by
`decide +kernel`).

## Shape of the results

For a program `p` with per-tape input bounds `ℓin` (`ℓRing`, `ℓDigit`, …, the actual lengths; the
output tape `0` may hold anything of length at most `M`) and output bounds `ℓout`:

  if `ℓ ≤ ℓin` and every `ℓ t ≤ M` (`M`: the longest word, e.g. `M = N · K` for a ring
  program), then
  * `lenBoundT p ℓ t ≤ ℓout t` on the listed tapes (the output tape `0` gets the length of the
    value, the inputs and templates keep theirs), `lenBoundT p ℓ t ≤ M` on every tape;
  * `timeBoundT p ℓ ≤ (2 M + 3) · W`, where `W` counts the primitives executed (*sweeps*).

`2 M + 3` is the cost of one primitive: its column machine sweeps every tape of the program, so it
is charged the longest word. Framed inside a larger store (`XProg.frame`), only the program's own
tapes count (`frameT_*`): the other tapes may be arbitrarily long.

| program | `W` (sweeps) |
|---|---|
| `addRWP`, `subRWP` | `29 N K + 28 N + 7` |
| `mulRWP` | `22 N² K² + 97 N² K + 61 N² + 64 N K + 89 N + 23 K + 49` |
| `digitRWP` | `18 N K² + 44 N K + 28 N + 11 K + 11` |
| `monoWP` | `6 N K + 9 N + 8` |
| `matMulP` | `m n l (22 N² K² + 97 N² K + 61 N² + 105 N K + 117 N + 23 K + 73) + …` |
| `ginvP` | `112 N K k'² + 86 N k'² + 25 k' + 7` |
| `gadP` | `15 N K k' + 9 N k' + 11 K k' + 34 k' + 11 K + 24` |
| `nandP` | `k'² (88 N² K² + 388 N² K + …) + k'³ (24 N K + 32) + …` |

The leading terms are the algorithms' true costs: `mulRWP` is Horner's rule over the `N` blocks of
`y`, each round a block-wise product of `N` shift-and-add multiplications of `K`-bit words (`K`
conditional additions of `K` sweeps each), so `N · N · K · K` sweeps; `matMulP` performs `m n l`
ring products (and as many ring additions and block moves); `nandP` multiplies a `1 × 2k'` by a
`2k' × 2k'` matrix of ring elements. With `N = 2^33`, `K = 2^25`, a ring product costs at most
`(2 · 2^58 + 3) · 2^121` steps, about `2^180`.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Tape.Sym

namespace Prog

namespace SpecT

/-! ### Symbolic sizes -/

/-- The values of the variables: `0` the top size `M`, then `N`, `K`, `m`, `n`, `l`, `k'`. -/
def vars (M N K m n l k' : ℕ) : List ℕ := [M, N, K, m, n, l, k']

/-- The monomial `c · N^a · K^b · m^c · …` with exponents `e`. -/
def mo (c : ℕ) (e : List ℕ) : Poly := [(0 :: e, c)]

def pN : Poly := mo 1 [1]
def pK : Poly := mo 1 [0, 1]
def pNK : Poly := mo 1 [1, 1]
def pm : Poly := mo 1 [0, 0, 1]
def pn : Poly := mo 1 [0, 0, 0, 1]
def pl : Poly := mo 1 [0, 0, 0, 0, 1]
def pk : Poly := mo 1 [0, 0, 0, 0, 0, 1]
def pmnNK : Poly := mo 1 [1, 1, 1, 1]
def pnlNK : Poly := mo 1 [1, 1, 0, 1, 1]
def pmlNK : Poly := mo 1 [1, 1, 1, 0, 1]
def p2k : Poly := mo 2 [0, 0, 0, 0, 0, 1]
def p2kN : Poly := mo 2 [1, 0, 0, 0, 0, 1]
def p2kNK : Poly := mo 2 [1, 1, 0, 0, 0, 1]
def p4kkNK : Poly := mo 4 [1, 1, 0, 0, 0, 2]

/-! ### The per-tape bounds of the inputs and outputs

Each `ℓ…` lists the bounds of the first tapes of a program (tape `0` the output); every later tape
(scratch) is `0`, i.e. blank. -/

/-- `0` output, `1` `2` operands of `N · K` bits, `3` `4` templates of lengths `K`, `N`. -/
def ℓRing (o N K : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => N * K | 2 => N * K | 3 => K | 4 => N | _ => 0

/-- `0` output, `1` the operand, `2` the digit index `i ≤ K`, `3` `4` templates `K`, `N`. -/
def ℓDigit (o N K : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => N * K | 2 => K | 3 => K | 4 => N | _ => 0

/-- `0` output, `1` the coefficient (`K` bits), `2` the index `j ≤ N`, templates `K`, `N`,
`N · K`. -/
def ℓMono (o N K : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => K | 2 => N | 3 => K | 4 => N | 5 => N * K | _ => 0

/-- `0` output, `1` an `m × n`, `2` an `n × l` matrix word, templates `K`, `N`, `N · K`, `m`, `n`,
`l`, `m · l · N · K`. -/
def ℓMat (o N K m n l : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => m * n * (N * K) | 2 => n * l * (N * K) | 3 => K | 4 => N | 5 => N * K
  | 6 => m | 7 => n | 8 => l | 9 => m * l * (N * K) | _ => 0

/-- `0` output, `1` a row of `2k'` ring words, templates `K`, `2k' · N`, `k'`,
`2k' · 2k' · N · K`. -/
def ℓGinv (o N K k' : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => 2 * k' * (N * K) | 2 => K | 3 => 2 * k' * N | 4 => k'
  | 5 => 2 * k' * (2 * k' * (N * K)) | _ => 0

/-- `0` output, templates `K`, `N`, `N · K`, `k'`, `2k' · N · K`. -/
def ℓGad (o N K k' : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => K | 2 => N | 3 => N * K | 4 => k' | 5 => 2 * k' * (N * K) | _ => 0

/-- `0` output, `1` `2` rows of `2k'` ring words, templates `K`, `N`, `N · K`, `k'`, `2k'`, `1`,
`2k' · N`, `2k' · N · K`, `2k' · 2k' · N · K`. -/
def ℓNand (o N K k' : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => 2 * k' * (N * K) | 2 => 2 * k' * (N * K) | 3 => K | 4 => N | 5 => N * K
  | 6 => k' | 7 => 2 * k' | 8 => 1 | 9 => 2 * k' * N | 10 => 2 * k' * (N * K)
  | 11 => 2 * k' * (2 * k' * (N * K)) | _ => 0

/-- The abstract inputs (`pTop` on the output tape: any word of length at most `M`) and outputs. -/
def σRing : Asg := [pTop, pNK, pNK, pK, pN]
def σRing' : Asg := [pNK, pNK, pNK, pK, pN]
def σDigit : Asg := [pTop, pNK, pK, pK, pN]
def σDigit' : Asg := [pNK, pNK, pK, pK, pN]
def σMono : Asg := [pTop, pK, pN, pK, pN, pNK]
def σMono' : Asg := [pNK, pK, pN, pK, pN, pNK]
def σMat : Asg := [pTop, pmnNK, pnlNK, pK, pN, pNK, pm, pn, pl, pmlNK]
def σMat' : Asg := [pmlNK, pmnNK, pnlNK, pK, pN, pNK, pm, pn, pl, pmlNK]
def σGinv : Asg := [pTop, p2kNK, pK, p2kN, pk, p4kkNK]
def σGinv' : Asg := [p4kkNK, p2kNK, pK, p2kN, pk, p4kkNK]
def σGad : Asg := [pTop, pK, pN, pNK, pk, p2kNK]
def σGad' : Asg := [p2kNK, pK, pN, pNK, pk, p2kNK]
def σNand : Asg := [pTop, p2kNK, p2kNK, pK, pN, pNK, pk, p2k, pC 1, p2kN, p2kNK, p4kkNK]
def σNand' : Asg := [p2kNK, p2kNK, p2kNK, pK, pN, pNK, pk, p2k, pC 1, p2kN, p2kNK, p4kkNK]

/-- Case analysis on the first twelve tapes, then evaluation. -/
macro "size_tac" : tactic => `(tactic| (
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | v, hv⟩ <;>
    simp_all [ℓRing, ℓDigit, ℓMono, ℓMat, ℓGinv, ℓGad, ℓNand, bnd, aGet, σRing, σRing', σDigit,
      σDigit', σMono, σMono', σMat, σMat', σGinv, σGinv', σGad, σGad', σNand, σNand', pN, pK, pNK,
      pm, pn, pl, pk, pmnNK, pnlNK, pmlNK, p2k, p2kN, p2kNK, p4kkNK, pTop, pC, mo, pEval, mEval,
      vars] <;>
    first | omega | exact le_of_eq (by ring) | ring))

section Sizes

variable {k : ℕ} (M N K m n l k' : ℕ)

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

theorem ℓRing_le : (ℓRing M N K : Fin k → ℕ) ≤ bnd (vars M N K m n l k') σRing := by size_tac
theorem ℓRing_out : ∀ t : Fin k, t.val < σRing'.length →
    pEval (vars M N K m n l k') (aGet σRing' t.val) = ℓRing (N * K) N K t := by size_tac
theorem ℓDigit_le : (ℓDigit M N K : Fin k → ℕ) ≤ bnd (vars M N K m n l k') σDigit := by size_tac
theorem ℓDigit_out : ∀ t : Fin k, t.val < σDigit'.length →
    pEval (vars M N K m n l k') (aGet σDigit' t.val) = ℓDigit (N * K) N K t := by size_tac
theorem ℓMono_le : (ℓMono M N K : Fin k → ℕ) ≤ bnd (vars M N K m n l k') σMono := by size_tac
theorem ℓMono_out : ∀ t : Fin k, t.val < σMono'.length →
    pEval (vars M N K m n l k') (aGet σMono' t.val) = ℓMono (N * K) N K t := by size_tac
theorem ℓMat_le : (ℓMat M N K m n l : Fin k → ℕ) ≤ bnd (vars M N K m n l k') σMat := by size_tac
theorem ℓMat_out : ∀ t : Fin k, t.val < σMat'.length →
    pEval (vars M N K m n l k') (aGet σMat' t.val) = ℓMat (m * l * (N * K)) N K m n l t := by
  size_tac
theorem ℓGinv_le : (ℓGinv M N K k' : Fin k → ℕ) ≤ bnd (vars M N K m n l k') σGinv := by size_tac
theorem ℓGinv_out : ∀ t : Fin k, t.val < σGinv'.length →
    pEval (vars M N K m n l k') (aGet σGinv' t.val) =
      ℓGinv (2 * k' * (2 * k' * (N * K))) N K k' t := by size_tac
theorem ℓGad_le : (ℓGad M N K k' : Fin k → ℕ) ≤ bnd (vars M N K m n l k') σGad := by size_tac
theorem ℓGad_out : ∀ t : Fin k, t.val < σGad'.length →
    pEval (vars M N K m n l k') (aGet σGad' t.val) = ℓGad (2 * k' * (N * K)) N K k' t := by
  size_tac
theorem ℓNand_le : (ℓNand M N K k' : Fin k → ℕ) ≤ bnd (vars M N K m n l k') σNand := by size_tac
theorem ℓNand_out : ∀ t : Fin k, t.val < σNand'.length →
    pEval (vars M N K m n l k') (aGet σNand' t.val) = ℓNand (2 * k' * (N * K)) N K k' t := by
  size_tac

end Sizes

/-! ### The certificates -/

/-- The sweeps of `addRWP`, `subRWP`: `29 N K + 28 N + 7`. -/
def wAdd : Poly := [([], 7), ([0, 1], 28), ([0, 1, 1], 29)]
/-- The sweeps of `mulRWP`. -/
def wMul : Poly :=
  [([], 49), ([0, 1], 89), ([0, 1, 1], 64), ([0, 2], 61), ([0, 2, 1], 97), ([0, 2, 2], 22),
    ([0, 0, 1], 23)]
/-- The sweeps of `digitRWP`. -/
def wDigit : Poly := [([], 11), ([0, 0, 1], 11), ([0, 1, 1], 44), ([0, 1, 2], 18), ([0, 1], 28)]
/-- The sweeps of `monoWP`. -/
def wMono : Poly := [([], 8), ([0, 1], 9), ([0, 1, 1], 6)]
/-- The sweeps of `matMulP`. -/
def wMat : Poly :=
  [([], 5), ([0, 0, 0, 1], 8), ([0, 0, 0, 1, 0, 1], 15), ([0, 0, 0, 1, 1, 1], 73),
    ([0, 1, 1, 1, 1, 1], 105), ([0, 0, 0, 1, 1, 2], 4), ([0, 1, 1, 1, 1, 2], 3),
    ([0, 1, 0, 1, 1, 1], 117), ([0, 2, 0, 1, 1, 1], 61), ([0, 2, 1, 1, 1, 1], 97),
    ([0, 2, 2, 1, 1, 1], 22), ([0, 0, 1, 1, 1, 1], 23), ([0, 1, 1, 1, 0, 1], 9),
    ([0, 0, 0, 1, 1], 4),     ([0, 1, 1, 1, 1], 3)]
/-- The sweeps of `ginvP`. -/
def wGinv : Poly :=
  [([], 7), ([0, 0, 0, 0, 0, 0, 1], 25), ([0, 1, 0, 0, 0, 0, 2], 86), ([0, 1, 1, 0, 0, 0, 2], 112)]
/-- The sweeps of `gadP`. -/
def wGad : Poly :=
  [([], 24), ([0, 0, 1], 11), ([0, 0, 0, 0, 0, 0, 1], 34), ([0, 1, 0, 0, 0, 0, 1], 9),
    ([0, 1, 1, 0, 0, 0, 1], 15), ([0, 0, 1, 0, 0, 0, 1], 11)]
/-- The sweeps of `nandP`. -/
def wNand : Poly :=
  [([], 56), ([0, 0, 1], 11), ([0, 0, 0, 0, 0, 0, 1], 97), ([0, 1, 0, 0, 0, 0, 1], 65),
    ([0, 1, 1, 0, 0, 0, 1], 97), ([0, 0, 1, 0, 0, 0, 1], 11), ([0, 1, 0, 0, 0, 0, 2], 554),
    ([0, 1, 1, 0, 0, 0, 2], 532), ([0, 0, 0, 0, 0, 0, 2], 292), ([0, 0, 0, 0, 0, 0, 3], 32),
    ([0, 1, 1, 0, 0, 0, 3], 24), ([0, 2, 0, 0, 0, 0, 2], 244), ([0, 2, 1, 0, 0, 0, 2], 388),
    ([0, 2, 2, 0, 0, 0, 2], 88), ([0, 0, 1, 0, 0, 0, 2], 92)]

theorem check_addRWP : check 8 addRWP σRing σRing' wAdd = true := by decide +kernel
theorem check_subRWP : check 8 subRWP σRing σRing' wAdd = true := by decide +kernel
theorem check_mulRWP : check 8 mulRWP σRing σRing' wMul = true := by decide +kernel
theorem check_digitRWP : check 8 digitRWP σDigit σDigit' wDigit = true := by decide +kernel
theorem check_monoWP : check 8 monoWP σMono σMono' wMono = true := by decide +kernel
theorem check_matMulP : check 8 matMulP σMat σMat' wMat = true := by decide +kernel
theorem check_ginvP : check 8 ginvP σGinv σGinv' wGinv = true := by decide +kernel
theorem check_gadP : check 8 gadP σGad σGad' wGad = true := by decide +kernel
theorem check_nandP : check 8 nandP σNand σNand' wNand = true := by decide +kernel

/-! ### From a certificate to the stated bounds -/

variable {n : ℕ}

theorem boundsT_of {p : Prog n} {σ claim : Asg} {w : Poly} (h : check 8 p σ claim w = true)
    (ρ : List ℕ) {ℓin ℓout : Fin n → ℕ} {W : ℕ} (hin : ℓin ≤ bnd ρ σ)
    (hout : ∀ t : Fin n, t.val < claim.length → pEval ρ (aGet claim t.val) = ℓout t)
    (hW : pEval ρ w = W) {ℓ : Fin n → ℕ} (hℓ : ℓ ≤ ℓin) (hM : ∀ t, ℓ t ≤ top ρ) :
    (∀ t : Fin n, t.val < claim.length → lenBoundT p ℓ t ≤ ℓout t) ∧
      (∀ t, lenBoundT p ℓ t ≤ top ρ) ∧ timeBoundT p ℓ ≤ (2 * top ρ + 3) * W := by
  obtain ⟨h1, h2, h3⟩ := bounds_of_check h ρ (hℓ.trans hin) hM
  exact ⟨fun t ht => (h1 t ht).trans (hout t ht).le, h2, hW ▸ h3⟩

theorem frameT_of {p : Prog n} {σ claim : Asg} {w : Poly} (h : check 8 p σ claim w = true)
    (ρ : List ℕ) {ℓin ℓout : Fin n → ℕ} {W : ℕ} (hin : ℓin ≤ bnd ρ σ)
    (hout : ∀ t : Fin n, t.val < claim.length → pEval ρ (aGet claim t.val) = ℓout t)
    (hW : pEval ρ w = W) {k : ℕ} (e : Fin n ↪ Fin k) {ℓ : Fin k → ℕ}
    (hℓ : ∀ j, ℓ (e j) ≤ ℓin j) (hM : ∀ j, ℓ (e j) ≤ top ρ) :
    XProg.timeBoundT (.frame e (.prog p)) ℓ ≤ (2 * top ρ + 3) * W ∧
      (∀ j : Fin n, j.val < claim.length → XProg.lenBoundT (.frame e (.prog p)) ℓ (e j) ≤ ℓout j) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog p)) ℓ t = ℓ t := by
  obtain ⟨h1, h2, h3⟩ := frame_of_check h ρ e (fun j => (hℓ j).trans (hin j)) hM
  exact ⟨hW ▸ h1, fun j hj => (h2 j hj).trans (hout j hj).le, h3⟩

/-! ### The per-tape bounds of the word programs

Hypotheses: `ℓ ≤ ℓ… M …` (tape `0` at most `M`, inputs and templates of their lengths, scratch
blank) and `∀ t, ℓ t ≤ M`. Conclusions: the bounds of the first tapes afterwards (the output gets
the length of its value), every tape at most `M`, and the time. -/

section Bounds

variable {M N K m n l k' : ℕ}

theorem boundsT_addRWP {ℓ : Fin 28 → ℕ} (hℓ : ℓ ≤ ℓRing M N K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 28, t.val < 5 → lenBoundT addRWP ℓ t ≤ ℓRing (N * K) N K t) ∧
      (∀ t, lenBoundT addRWP ℓ t ≤ M) ∧
      timeBoundT addRWP ℓ ≤ (2 * M + 3) * (29 * (N * K) + 28 * N + 7) :=
  boundsT_of check_addRWP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wAdd, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_subRWP {ℓ : Fin 28 → ℕ} (hℓ : ℓ ≤ ℓRing M N K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 28, t.val < 5 → lenBoundT subRWP ℓ t ≤ ℓRing (N * K) N K t) ∧
      (∀ t, lenBoundT subRWP ℓ t ≤ M) ∧
      timeBoundT subRWP ℓ ≤ (2 * M + 3) * (29 * (N * K) + 28 * N + 7) :=
  boundsT_of check_subRWP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wAdd, pEval, mEval, vars]; ring) hℓ hM

/-- **Ring multiplication**: `N² K²` sweeps (Horner over the `N` blocks, each a block-wise product
of `N` schoolbook products of `K`-bit words), each at most `2 M + 3` steps. -/
theorem boundsT_mulRWP {ℓ : Fin 38 → ℕ} (hℓ : ℓ ≤ ℓRing M N K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 38, t.val < 5 → lenBoundT mulRWP ℓ t ≤ ℓRing (N * K) N K t) ∧
      (∀ t, lenBoundT mulRWP ℓ t ≤ M) ∧
      timeBoundT mulRWP ℓ ≤ (2 * M + 3) * (22 * N ^ 2 * K ^ 2 + 97 * N ^ 2 * K + 61 * N ^ 2 +
        64 * (N * K) + 89 * N + 23 * K + 49) :=
  boundsT_of check_mulRWP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wMul, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_digitRWP {ℓ : Fin 31 → ℕ} (hℓ : ℓ ≤ ℓDigit M N K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 31, t.val < 5 → lenBoundT digitRWP ℓ t ≤ ℓDigit (N * K) N K t) ∧
      (∀ t, lenBoundT digitRWP ℓ t ≤ M) ∧
      timeBoundT digitRWP ℓ ≤
        (2 * M + 3) * (18 * N * K ^ 2 + 44 * (N * K) + 28 * N + 11 * K + 11) :=
  boundsT_of check_digitRWP (vars M N K 0 0 0 0) (ℓDigit_le M N K 0 0 0 0)
    (ℓDigit_out M N K 0 0 0 0)
    (by simp [wDigit, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_monoWP {ℓ : Fin 12 → ℕ} (hℓ : ℓ ≤ ℓMono M N K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 12, t.val < 6 → lenBoundT monoWP ℓ t ≤ ℓMono (N * K) N K t) ∧
      (∀ t, lenBoundT monoWP ℓ t ≤ M) ∧
      timeBoundT monoWP ℓ ≤ (2 * M + 3) * (6 * (N * K) + 9 * N + 8) :=
  boundsT_of check_monoWP (vars M N K 0 0 0 0) (ℓMono_le M N K 0 0 0 0) (ℓMono_out M N K 0 0 0 0)
    (by simp [wMono, pEval, mEval, vars]; ring) hℓ hM

/-- **Matrix products**: `m n l` ring products. -/
theorem boundsT_matMulP {ℓ : Fin 59 → ℕ} (hℓ : ℓ ≤ ℓMat M N K m n l) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 59, t.val < 10 → lenBoundT matMulP ℓ t ≤ ℓMat (m * l * (N * K)) N K m n l t) ∧
      (∀ t, lenBoundT matMulP ℓ t ≤ M) ∧
      timeBoundT matMulP ℓ ≤ (2 * M + 3) *
        (m * n * l * (22 * N ^ 2 * K ^ 2 + 97 * N ^ 2 * K + 61 * N ^ 2 + 105 * (N * K) + 117 * N +
            23 * K + 73) + m * n * l ^ 2 * (3 * (N * K) + 4) + m * n * (3 * (N * K) + 4) +
          m * l * (9 * (N * K) + 15) + 8 * m + 5) :=
  boundsT_of check_matMulP (vars M N K m n l 0) (ℓMat_le M N K m n l 0) (ℓMat_out M N K m n l 0)
    (by simp [wMat, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_ginvP {ℓ : Fin 35 → ℕ} (hℓ : ℓ ≤ ℓGinv M N K k') (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 35, t.val < 6 →
        lenBoundT ginvP ℓ t ≤ ℓGinv (2 * k' * (2 * k' * (N * K))) N K k' t) ∧
      (∀ t, lenBoundT ginvP ℓ t ≤ M) ∧
      timeBoundT ginvP ℓ ≤ (2 * M + 3) * (112 * (N * K) * k' ^ 2 + 86 * N * k' ^ 2 + 25 * k' + 7) :=
  boundsT_of check_ginvP (vars M N K 0 0 0 k') (ℓGinv_le M N K 0 0 0 k') (ℓGinv_out M N K 0 0 0 k')
    (by simp [wGinv, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_gadP {ℓ : Fin 21 → ℕ} (hℓ : ℓ ≤ ℓGad M N K k') (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 21, t.val < 6 → lenBoundT gadP ℓ t ≤ ℓGad (2 * k' * (N * K)) N K k' t) ∧
      (∀ t, lenBoundT gadP ℓ t ≤ M) ∧
      timeBoundT gadP ℓ ≤ (2 * M + 3) *
        (15 * (N * K) * k' + 9 * N * k' + 11 * K * k' + 34 * k' + 11 * K + 24) :=
  boundsT_of check_gadP (vars M N K 0 0 0 k') (ℓGad_le M N K 0 0 0 k') (ℓGad_out M N K 0 0 0 k')
    (by simp [wGad, pEval, mEval, vars]; ring) hℓ hM

/-- **The BGG+ NAND of public keys**: a `1 × 2k'` by `2k' × 2k'` product of ring matrices
(`4 k'²` ring products), the gadget inverse and the gadget row. -/
theorem boundsT_nandP {ℓ : Fin 65 → ℕ} (hℓ : ℓ ≤ ℓNand M N K k') (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 65, t.val < 12 → lenBoundT nandP ℓ t ≤ ℓNand (2 * k' * (N * K)) N K k' t) ∧
      (∀ t, lenBoundT nandP ℓ t ≤ M) ∧
      timeBoundT nandP ℓ ≤ (2 * M + 3) *
        (k' ^ 2 * (88 * N ^ 2 * K ^ 2 + 388 * N ^ 2 * K + 244 * N ^ 2 + 532 * (N * K) + 554 * N +
            92 * K + 292) + k' ^ 3 * (24 * (N * K) + 32) +
          k' * (97 * (N * K) + 65 * N + 11 * K + 97) + 11 * K + 56) :=
  boundsT_of check_nandP (vars M N K 0 0 0 k') (ℓNand_le M N K 0 0 0 k') (ℓNand_out M N K 0 0 0 k')
    (by simp [wNand, pEval, mEval, vars]; ring) hℓ hM

end Bounds

/-! ### Framed inside a larger store

`XProg.frame e (.prog p)` runs `p` on the tapes `e 0, e 1, …` of a larger machine only: its cost
sees only those tapes (bounded by `M`), whatever the lengths of the others, which it leaves alone.
Its law is the update of the output tape (`law_frame_eq_update`, with the laws of `Spec`). -/

section Frame

variable {k : ℕ}

theorem law_frame (e : Fin n ↪ Fin k) (p : Prog n) (s : Store k) :
    XProg.law (.frame e (.prog p)) s = (p.law fun j => s (e j)).map (embedF e s) := by
  simp only [XProg.law, XProg.denote, Cslib.ProbComp.eval_map]
  rfl

theorem embedF_update (e : Fin n ↪ Fin k) (s : Store k) (o : Fin n) (v : List Bool) :
    embedF e s (Function.update (fun j => s (e j)) o v) = Function.update s (e o) v := by
  funext t
  rcases embedF_cases e s (Function.update (fun j => s (e j)) o v) t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h, Function.update_of_ne]
    rintro rfl
    rw [partialInv_self] at hn
    exact Option.some_ne_none _ hn
  · rw [h]
    by_cases hj : j = o
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne (e.injective.ne hj)]

/-- **The law of a framed program** whose law is an update of its output tape. -/
theorem law_frame_eq_update (e : Fin n ↪ Fin k) (p : Prog n) (s : Store k) (o : Fin n)
    (v : List Bool)
    (h : p.law (fun j => s (e j)) = PMF.pure (Function.update (fun j => s (e j)) o v)) :
    XProg.law (.frame e (.prog p)) s = PMF.pure (Function.update s (e o) v) := by
  rw [law_frame, h, PMF.pure_map, embedF_update]

/-- `law_*_map` of `Spec` on the program's own tapes. -/
theorem law_eq_of_map_id {p : Prog n} {s : Store n} {μ : PMF (Store n)}
    (h : law (map id p) s = μ) : law p s = μ := by rwa [Prog.map_id] at h

variable {M N K m n' l k' : ℕ} {ℓ : Fin k → ℕ}

theorem frameT_addRWP (e : Fin 28 ↪ Fin k) (hℓ : ∀ j, ℓ (e j) ≤ ℓRing M N K j)
    (hM : ∀ j, ℓ (e j) ≤ M) :
    XProg.timeBoundT (.frame e (.prog addRWP)) ℓ ≤ (2 * M + 3) * (29 * (N * K) + 28 * N + 7) ∧
      (∀ j : Fin 28, j.val < 5 →
        XProg.lenBoundT (.frame e (.prog addRWP)) ℓ (e j) ≤ ℓRing (N * K) N K j) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog addRWP)) ℓ t = ℓ t :=
  frameT_of check_addRWP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wAdd, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_subRWP (e : Fin 28 ↪ Fin k) (hℓ : ∀ j, ℓ (e j) ≤ ℓRing M N K j)
    (hM : ∀ j, ℓ (e j) ≤ M) :
    XProg.timeBoundT (.frame e (.prog subRWP)) ℓ ≤ (2 * M + 3) * (29 * (N * K) + 28 * N + 7) ∧
      (∀ j : Fin 28, j.val < 5 →
        XProg.lenBoundT (.frame e (.prog subRWP)) ℓ (e j) ≤ ℓRing (N * K) N K j) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog subRWP)) ℓ t = ℓ t :=
  frameT_of check_subRWP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wAdd, pEval, mEval, vars]; ring) e hℓ hM

/-- **Ring multiplication framed in a larger store**: `M` bounds only its own tapes (e.g.
`M = N · K`), however long the other tapes are. -/
theorem frameT_mulRWP (e : Fin 38 ↪ Fin k) (hℓ : ∀ j, ℓ (e j) ≤ ℓRing M N K j)
    (hM : ∀ j, ℓ (e j) ≤ M) :
    XProg.timeBoundT (.frame e (.prog mulRWP)) ℓ ≤ (2 * M + 3) * (22 * N ^ 2 * K ^ 2 +
        97 * N ^ 2 * K + 61 * N ^ 2 + 64 * (N * K) + 89 * N + 23 * K + 49) ∧
      (∀ j : Fin 38, j.val < 5 →
        XProg.lenBoundT (.frame e (.prog mulRWP)) ℓ (e j) ≤ ℓRing (N * K) N K j) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog mulRWP)) ℓ t = ℓ t :=
  frameT_of check_mulRWP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wMul, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_digitRWP (e : Fin 31 ↪ Fin k) (hℓ : ∀ j, ℓ (e j) ≤ ℓDigit M N K j)
    (hM : ∀ j, ℓ (e j) ≤ M) :
    XProg.timeBoundT (.frame e (.prog digitRWP)) ℓ ≤
        (2 * M + 3) * (18 * N * K ^ 2 + 44 * (N * K) + 28 * N + 11 * K + 11) ∧
      (∀ j : Fin 31, j.val < 5 →
        XProg.lenBoundT (.frame e (.prog digitRWP)) ℓ (e j) ≤ ℓDigit (N * K) N K j) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog digitRWP)) ℓ t = ℓ t :=
  frameT_of check_digitRWP (vars M N K 0 0 0 0) (ℓDigit_le M N K 0 0 0 0)
    (ℓDigit_out M N K 0 0 0 0) (by simp [wDigit, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_monoWP (e : Fin 12 ↪ Fin k) (hℓ : ∀ j, ℓ (e j) ≤ ℓMono M N K j)
    (hM : ∀ j, ℓ (e j) ≤ M) :
    XProg.timeBoundT (.frame e (.prog monoWP)) ℓ ≤ (2 * M + 3) * (6 * (N * K) + 9 * N + 8) ∧
      (∀ j : Fin 12, j.val < 6 →
        XProg.lenBoundT (.frame e (.prog monoWP)) ℓ (e j) ≤ ℓMono (N * K) N K j) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog monoWP)) ℓ t = ℓ t :=
  frameT_of check_monoWP (vars M N K 0 0 0 0) (ℓMono_le M N K 0 0 0 0) (ℓMono_out M N K 0 0 0 0)
    (by simp [wMono, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_matMulP (e : Fin 59 ↪ Fin k) (hℓ : ∀ j, ℓ (e j) ≤ ℓMat M N K m n' l j)
    (hM : ∀ j, ℓ (e j) ≤ M) :
    XProg.timeBoundT (.frame e (.prog matMulP)) ℓ ≤ (2 * M + 3) *
        (m * n' * l * (22 * N ^ 2 * K ^ 2 + 97 * N ^ 2 * K + 61 * N ^ 2 + 105 * (N * K) +
            117 * N + 23 * K + 73) + m * n' * l ^ 2 * (3 * (N * K) + 4) +
          m * n' * (3 * (N * K) + 4) + m * l * (9 * (N * K) + 15) + 8 * m + 5) ∧
      (∀ j : Fin 59, j.val < 10 → XProg.lenBoundT (.frame e (.prog matMulP)) ℓ (e j) ≤
        ℓMat (m * l * (N * K)) N K m n' l j) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog matMulP)) ℓ t = ℓ t :=
  frameT_of check_matMulP (vars M N K m n' l 0) (ℓMat_le M N K m n' l 0)
    (ℓMat_out M N K m n' l 0) (by simp [wMat, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_ginvP (e : Fin 35 ↪ Fin k) (hℓ : ∀ j, ℓ (e j) ≤ ℓGinv M N K k' j)
    (hM : ∀ j, ℓ (e j) ≤ M) :
    XProg.timeBoundT (.frame e (.prog ginvP)) ℓ ≤
        (2 * M + 3) * (112 * (N * K) * k' ^ 2 + 86 * N * k' ^ 2 + 25 * k' + 7) ∧
      (∀ j : Fin 35, j.val < 6 → XProg.lenBoundT (.frame e (.prog ginvP)) ℓ (e j) ≤
        ℓGinv (2 * k' * (2 * k' * (N * K))) N K k' j) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog ginvP)) ℓ t = ℓ t :=
  frameT_of check_ginvP (vars M N K 0 0 0 k') (ℓGinv_le M N K 0 0 0 k')
    (ℓGinv_out M N K 0 0 0 k') (by simp [wGinv, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_gadP (e : Fin 21 ↪ Fin k) (hℓ : ∀ j, ℓ (e j) ≤ ℓGad M N K k' j)
    (hM : ∀ j, ℓ (e j) ≤ M) :
    XProg.timeBoundT (.frame e (.prog gadP)) ℓ ≤ (2 * M + 3) *
        (15 * (N * K) * k' + 9 * N * k' + 11 * K * k' + 34 * k' + 11 * K + 24) ∧
      (∀ j : Fin 21, j.val < 6 → XProg.lenBoundT (.frame e (.prog gadP)) ℓ (e j) ≤
        ℓGad (2 * k' * (N * K)) N K k' j) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog gadP)) ℓ t = ℓ t :=
  frameT_of check_gadP (vars M N K 0 0 0 k') (ℓGad_le M N K 0 0 0 k')
    (ℓGad_out M N K 0 0 0 k') (by simp [wGad, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_nandP (e : Fin 65 ↪ Fin k) (hℓ : ∀ j, ℓ (e j) ≤ ℓNand M N K k' j)
    (hM : ∀ j, ℓ (e j) ≤ M) :
    XProg.timeBoundT (.frame e (.prog nandP)) ℓ ≤ (2 * M + 3) *
        (k' ^ 2 * (88 * N ^ 2 * K ^ 2 + 388 * N ^ 2 * K + 244 * N ^ 2 + 532 * (N * K) +
            554 * N + 92 * K + 292) + k' ^ 3 * (24 * (N * K) + 32) +
          k' * (97 * (N * K) + 65 * N + 11 * K + 97) + 11 * K + 56) ∧
      (∀ j : Fin 65, j.val < 12 → XProg.lenBoundT (.frame e (.prog nandP)) ℓ (e j) ≤
        ℓNand (2 * k' * (N * K)) N K k' j) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog nandP)) ℓ t = ℓ t :=
  frameT_of check_nandP (vars M N K 0 0 0 k') (ℓNand_le M N K 0 0 0 k')
    (ℓNand_out M N K 0 0 0 k') (by simp [wNand, pEval, mEval, vars]; ring) e hℓ hM

end Frame

/-! ### The concrete instance

`N = 2^33`, `K = 2^25`: a ring word has `2^58` bits, and a ring product, alone or framed, costs
fewer than `2^180` steps. -/

theorem timeBoundT_mulRWP_concrete {ℓ : Fin 38 → ℕ} (hℓ : ℓ ≤ ℓRing (2 ^ 58) (2 ^ 33) (2 ^ 25))
    (hM : ∀ t, ℓ t ≤ 2 ^ 58) : timeBoundT mulRWP ℓ < 2 ^ 180 := by
  have h := (boundsT_mulRWP hℓ hM).2.2
  refine lt_of_le_of_lt h ?_
  norm_num

end SpecT

end Prog

end SigabaNeo.Tape
