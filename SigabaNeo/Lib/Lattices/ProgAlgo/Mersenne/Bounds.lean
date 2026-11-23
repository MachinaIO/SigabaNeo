import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.Aut
import SigabaNeo.Lib.Lattices.ProgAlgo.SpecT

/-!
# Per-tape bounds of the programs modulo `2^K − 1`

As in `SigabaNeo.Lib.Lattices.ProgAlgo.SpecT`: each program is certified by the abstract
interpreter of `SigabaNeo.Lib.Machines.Prog.AbsBound` (`check … = true` by `decide +kernel`), with
the variables `M` (the top size: a bound on every tape), `N`, `K`, and `j` (the length of an index
template: the exponent of `X^{−j}`, the rotation count of `2^{−j}`, the index `k` of `σ_k`).

## Shape of the results

If the tapes are at most their listed lengths (`ℓ ≤ ℓ… M …`: output tape at most `M`, inputs and
templates of their lengths, scratch blank) and at most `M`, then the listed tapes end at most
their listed lengths (the output gets the length of its value), every tape stays at most `M`, and

  `timeBoundT p ℓ ≤ (2 M + 3) · W`,

`W` the number of primitives executed (sweeps). Framed in a larger store (`frameT_*`), `M` bounds
only the program's own tapes.

| program | layout | `W` (sweeps) |
|---|---|---|
| `addMP`, `subMP` | `ℓRes` (`K`, `K`) | `22 K + 31` |
| `mulMB` | `ℓRes` | `22 K² + 43 K + 8` |
| `rotJP` | `ℓRotJ` (`K`, `j`) | `7 j + 3` |
| `notP` | `ℓNot` (`N K`) | `11 N K + 15` |
| `addRMP`, `subRMP` | `ℓRing` | `40 N K + 44 N + 7` |
| `rhoJP` (`X^{−j}`) | `ℓRho` (`N K`, `j`, `K`) | `7 j K + 4 j + 3` |
| `scRMP` | `ℓSc` (`N K`, `K`, `K`, `N`) | `22 N K² + 67 N K + 27 N + 11` |
| `rotBP` (`2^{−j}`) | `ℓJ` (`N K`, `j`, `K`, `N`) | `18 N K j + 19 N j + 11 j + 3` |
| `mulRMP` | `ℓRing` | `22 N² K² + 107 N² K + 71 N² + 24 N K + 29 N + 7 K + 24` |
| `autMP` (`σ_j`) | `ℓJ` | `14 N K j + 8 N j + 40 N K + 55 N + 10` |

The ring product has the cost of `mulRWP` modulo `2^K` (`22 N² K²` sweeps); `σ_k` costs
`O(N K k)` sweeps (`2 N k` multiplications by `X⁻¹`, `K` register shifts each).
-/

set_option Elab.async false

namespace SigabaNeo.Tape

open SigabaNeo.Tape.Sym

namespace Prog

namespace MersenneT

open SigabaNeo.Tape.Prog.SpecT

/-! ### Layouts -/

/-- `0` output, `1` `2` residues of `K` bits. -/
def ℓRes (o K : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => K | 2 => K | _ => 0

/-- `0` output, `1` a ring word. -/
def ℓNot (o N K : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => N * K | _ => 0

/-- `0` output, `1` a residue, `2` a template of length `j`. -/
def ℓRotJ (o K j : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => K | 2 => j | _ => 0

/-- `0` output, `1` a ring word, `2` `3` templates of lengths `j`, `K`. -/
def ℓRho (o N K j : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => N * K | 2 => j | 3 => K | _ => 0

/-- `0` output, `1` a ring word, `2` a residue, `3` `4` templates of lengths `K`, `N`. -/
def ℓSc (o N K : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => N * K | 2 => K | 3 => K | 4 => N | _ => 0

/-- `0` output, `1` a ring word, `2` `3` `4` templates of lengths `j`, `K`, `N`. -/
def ℓJ (o N K j : ℕ) {k : ℕ} (t : Fin k) : ℕ :=
  match t.val with
  | 0 => o | 1 => N * K | 2 => j | 3 => K | 4 => N | _ => 0

def σRes : Asg := [pTop, pK, pK]
def σRes' : Asg := [pK, pK, pK]
def σNot : Asg := [pTop, pNK]
def σNot' : Asg := [pNK, pNK]
def σRotJ : Asg := [pTop, pK, pm]
def σRotJ' : Asg := [pK, pK, pm]
def σRho : Asg := [pTop, pNK, pm, pK]
def σRho' : Asg := [pNK, pNK, pm, pK]
def σSc : Asg := [pTop, pNK, pK, pK, pN]
def σSc' : Asg := [pNK, pNK, pK, pK, pN]
def σJ : Asg := [pTop, pNK, pm, pK, pN]
def σJ' : Asg := [pNK, pNK, pm, pK, pN]

/-- Case analysis on the first tapes, then evaluation. -/
macro "msize_tac" : tactic => `(tactic| (
  rintro ⟨_ | _ | _ | _ | _ | _ | v, hv⟩ <;>
    simp_all [ℓRes, ℓNot, ℓRotJ, ℓRho, ℓSc, ℓJ, bnd, aGet, σRes, σRes', σNot, σNot', σRotJ,
      σRotJ', σRho, σRho', σSc, σSc', σJ, σJ', pN, pK, pNK, pm, pTop, mo, pEval, mEval, vars] <;>
    first | omega | exact le_of_eq (by ring) | ring))

section Sizes

variable {k : ℕ} (M N K j : ℕ)

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

theorem ℓRes_le : (ℓRes M K : Fin k → ℕ) ≤ bnd (vars M N K j 0 0 0) σRes := by msize_tac
theorem ℓRes_out : ∀ t : Fin k, t.val < σRes'.length →
    pEval (vars M N K j 0 0 0) (aGet σRes' t.val) = ℓRes K K t := by msize_tac
theorem ℓNot_le : (ℓNot M N K : Fin k → ℕ) ≤ bnd (vars M N K j 0 0 0) σNot := by msize_tac
theorem ℓNot_out : ∀ t : Fin k, t.val < σNot'.length →
    pEval (vars M N K j 0 0 0) (aGet σNot' t.val) = ℓNot (N * K) N K t := by msize_tac
theorem ℓRotJ_le : (ℓRotJ M K j : Fin k → ℕ) ≤ bnd (vars M N K j 0 0 0) σRotJ := by msize_tac
theorem ℓRotJ_out : ∀ t : Fin k, t.val < σRotJ'.length →
    pEval (vars M N K j 0 0 0) (aGet σRotJ' t.val) = ℓRotJ K K j t := by msize_tac
theorem ℓRho_le : (ℓRho M N K j : Fin k → ℕ) ≤ bnd (vars M N K j 0 0 0) σRho := by msize_tac
theorem ℓRho_out : ∀ t : Fin k, t.val < σRho'.length →
    pEval (vars M N K j 0 0 0) (aGet σRho' t.val) = ℓRho (N * K) N K j t := by msize_tac
theorem ℓSc_le : (ℓSc M N K : Fin k → ℕ) ≤ bnd (vars M N K j 0 0 0) σSc := by msize_tac
theorem ℓSc_out : ∀ t : Fin k, t.val < σSc'.length →
    pEval (vars M N K j 0 0 0) (aGet σSc' t.val) = ℓSc (N * K) N K t := by msize_tac
theorem ℓJ_le : (ℓJ M N K j : Fin k → ℕ) ≤ bnd (vars M N K j 0 0 0) σJ := by msize_tac
theorem ℓJ_out : ∀ t : Fin k, t.val < σJ'.length →
    pEval (vars M N K j 0 0 0) (aGet σJ' t.val) = ℓJ (N * K) N K j t := by msize_tac

end Sizes

/-! ### The certificates -/

def wAddM : Poly := [([], 31), ([0, 0, 1], 22)]
def wNotM : Poly := [([], 15), ([0, 1, 1], 11)]
def wRotJ : Poly := [([], 3), ([0, 0, 0, 1], 7)]
def wMulM : Poly := [([], 8), ([0, 0, 1], 43), ([0, 0, 2], 22)]
def wAddRM : Poly := [([], 7), ([0, 1], 44), ([0, 1, 1], 40)]
def wRhoJ : Poly := [([], 3), ([0, 0, 0, 1], 4), ([0, 0, 1, 1], 7)]
def wScRM : Poly := [([], 11), ([0, 1], 27), ([0, 1, 1], 67), ([0, 1, 2], 22)]
def wRotB : Poly := [([], 3), ([0, 0, 0, 1], 11), ([0, 1, 0, 1], 19), ([0, 1, 1, 1], 18)]
def wMulRM : Poly :=
  [([], 24), ([0, 1], 29), ([0, 1, 1], 24), ([0, 2], 71), ([0, 2, 1], 107), ([0, 2, 2], 22),
    ([0, 0, 1], 7)]
def wAut : Poly := [([], 10), ([0, 1], 55), ([0, 1, 1], 40), ([0, 1, 0, 1], 8), ([0, 1, 1, 1], 14)]

theorem check_addMP : check 8 addMP σRes σRes' wAddM = true := by decide +kernel
theorem check_subMP : check 8 subMP σRes σRes' wAddM = true := by decide +kernel
theorem check_notP : check 8 notP σNot σNot' wNotM = true := by decide +kernel
theorem check_rotJP : check 8 rotJP σRotJ σRotJ' wRotJ = true := by decide +kernel
theorem check_mulMB : check 8 mulMB σRes σRes' wMulM = true := by decide +kernel
theorem check_addRMP : check 8 addRMP σRing σRing' wAddRM = true := by decide +kernel
theorem check_subRMP : check 8 subRMP σRing σRing' wAddRM = true := by decide +kernel
theorem check_rhoJP : check 8 rhoJP σRho σRho' wRhoJ = true := by decide +kernel
theorem check_scRMP : check 8 scRMP σSc σSc' wScRM = true := by decide +kernel
theorem check_rotBP : check 8 rotBP σJ σJ' wRotB = true := by decide +kernel
theorem check_mulRMP : check 8 mulRMP σRing σRing' wMulRM = true := by decide +kernel
theorem check_autMP : check 8 autMP σJ σJ' wAut = true := by decide +kernel

/-! ### The per-tape bounds

Hypotheses: `ℓ ≤ ℓ… M …` and `∀ t, ℓ t ≤ M`. Conclusions: the bounds of the listed tapes
afterwards, every tape at most `M`, the time. -/

section Bounds

variable {M N K j : ℕ}

theorem boundsT_addMP {ℓ : Fin 12 → ℕ} (hℓ : ℓ ≤ ℓRes M K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 12, t.val < 3 → lenBoundT addMP ℓ t ≤ ℓRes K K t) ∧
      (∀ t, lenBoundT addMP ℓ t ≤ M) ∧ timeBoundT addMP ℓ ≤ (2 * M + 3) * (22 * K + 31) :=
  boundsT_of check_addMP (vars M 0 K 0 0 0 0) (ℓRes_le M 0 K 0) (ℓRes_out M 0 K 0)
    (by simp [wAddM, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_subMP {ℓ : Fin 12 → ℕ} (hℓ : ℓ ≤ ℓRes M K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 12, t.val < 3 → lenBoundT subMP ℓ t ≤ ℓRes K K t) ∧
      (∀ t, lenBoundT subMP ℓ t ≤ M) ∧ timeBoundT subMP ℓ ≤ (2 * M + 3) * (22 * K + 31) :=
  boundsT_of check_subMP (vars M 0 K 0 0 0 0) (ℓRes_le M 0 K 0) (ℓRes_out M 0 K 0)
    (by simp [wAddM, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_mulMB {ℓ : Fin 18 → ℕ} (hℓ : ℓ ≤ ℓRes M K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 18, t.val < 3 → lenBoundT mulMB ℓ t ≤ ℓRes K K t) ∧
      (∀ t, lenBoundT mulMB ℓ t ≤ M) ∧
      timeBoundT mulMB ℓ ≤ (2 * M + 3) * (22 * K ^ 2 + 43 * K + 8) :=
  boundsT_of check_mulMB (vars M 0 K 0 0 0 0) (ℓRes_le M 0 K 0) (ℓRes_out M 0 K 0)
    (by simp [wMulM, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_rotJP {ℓ : Fin 5 → ℕ} (hℓ : ℓ ≤ ℓRotJ M K j) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 5, t.val < 3 → lenBoundT rotJP ℓ t ≤ ℓRotJ K K j t) ∧
      (∀ t, lenBoundT rotJP ℓ t ≤ M) ∧ timeBoundT rotJP ℓ ≤ (2 * M + 3) * (7 * j + 3) :=
  boundsT_of check_rotJP (vars M 0 K j 0 0 0) (ℓRotJ_le M 0 K j) (ℓRotJ_out M 0 K j)
    (by simp [wRotJ, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_notP {ℓ : Fin 11 → ℕ} (hℓ : ℓ ≤ ℓNot M N K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 11, t.val < 2 → lenBoundT notP ℓ t ≤ ℓNot (N * K) N K t) ∧
      (∀ t, lenBoundT notP ℓ t ≤ M) ∧ timeBoundT notP ℓ ≤ (2 * M + 3) * (11 * (N * K) + 15) :=
  boundsT_of check_notP (vars M N K 0 0 0 0) (ℓNot_le M N K 0) (ℓNot_out M N K 0)
    (by simp [wNotM, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_addRMP {ℓ : Fin 28 → ℕ} (hℓ : ℓ ≤ ℓRing M N K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 28, t.val < 5 → lenBoundT addRMP ℓ t ≤ ℓRing (N * K) N K t) ∧
      (∀ t, lenBoundT addRMP ℓ t ≤ M) ∧
      timeBoundT addRMP ℓ ≤ (2 * M + 3) * (40 * (N * K) + 44 * N + 7) :=
  boundsT_of check_addRMP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wAddRM, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_subRMP {ℓ : Fin 28 → ℕ} (hℓ : ℓ ≤ ℓRing M N K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 28, t.val < 5 → lenBoundT subRMP ℓ t ≤ ℓRing (N * K) N K t) ∧
      (∀ t, lenBoundT subRMP ℓ t ≤ M) ∧
      timeBoundT subRMP ℓ ≤ (2 * M + 3) * (40 * (N * K) + 44 * N + 7) :=
  boundsT_of check_subRMP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wAddRM, pEval, mEval, vars]; ring) hℓ hM

/-- **The monomial `X^{−j}`**: `O(j K)` sweeps. -/
theorem boundsT_rhoJP {ℓ : Fin 7 → ℕ} (hℓ : ℓ ≤ ℓRho M N K j) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 7, t.val < 4 → lenBoundT rhoJP ℓ t ≤ ℓRho (N * K) N K j t) ∧
      (∀ t, lenBoundT rhoJP ℓ t ≤ M) ∧
      timeBoundT rhoJP ℓ ≤ (2 * M + 3) * (7 * j * K + 4 * j + 3) :=
  boundsT_of check_rhoJP (vars M N K j 0 0 0) (ℓRho_le M N K j) (ℓRho_out M N K j)
    (by simp [wRhoJ, pEval, mEval, vars]; ring) hℓ hM

theorem boundsT_scRMP {ℓ : Fin 29 → ℕ} (hℓ : ℓ ≤ ℓSc M N K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 29, t.val < 5 → lenBoundT scRMP ℓ t ≤ ℓSc (N * K) N K t) ∧
      (∀ t, lenBoundT scRMP ℓ t ≤ M) ∧
      timeBoundT scRMP ℓ ≤ (2 * M + 3) * (22 * N * K ^ 2 + 67 * (N * K) + 27 * N + 11) :=
  boundsT_of check_scRMP (vars M N K 0 0 0 0) (ℓSc_le M N K 0) (ℓSc_out M N K 0)
    (by simp [wScRM, pEval, mEval, vars]; ring) hℓ hM

/-- **`2^{−j}` on every coefficient** (`W⁻¹` with `j = b`). -/
theorem boundsT_rotBP {ℓ : Fin 30 → ℕ} (hℓ : ℓ ≤ ℓJ M N K j) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 30, t.val < 5 → lenBoundT rotBP ℓ t ≤ ℓJ (N * K) N K j t) ∧
      (∀ t, lenBoundT rotBP ℓ t ≤ M) ∧
      timeBoundT rotBP ℓ ≤ (2 * M + 3) * (18 * (N * K) * j + 19 * N * j + 11 * j + 3) :=
  boundsT_of check_rotBP (vars M N K j 0 0 0) (ℓJ_le M N K j) (ℓJ_out M N K j)
    (by simp [wRotB, pEval, mEval, vars]; ring) hℓ hM

/-- **Ring multiplication modulo `2^K − 1`**: `22 N² K²` sweeps, as modulo `2^K`. -/
theorem boundsT_mulRMP {ℓ : Fin 37 → ℕ} (hℓ : ℓ ≤ ℓRing M N K) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 37, t.val < 5 → lenBoundT mulRMP ℓ t ≤ ℓRing (N * K) N K t) ∧
      (∀ t, lenBoundT mulRMP ℓ t ≤ M) ∧
      timeBoundT mulRMP ℓ ≤ (2 * M + 3) * (22 * N ^ 2 * K ^ 2 + 107 * N ^ 2 * K + 71 * N ^ 2 +
        24 * (N * K) + 29 * N + 7 * K + 24) :=
  boundsT_of check_mulRMP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wMulRM, pEval, mEval, vars]; ring) hℓ hM

/-- **`σ_j`**: `O(N K j)` sweeps. -/
theorem boundsT_autMP {ℓ : Fin 25 → ℕ} (hℓ : ℓ ≤ ℓJ M N K j) (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 25, t.val < 5 → lenBoundT autMP ℓ t ≤ ℓJ (N * K) N K j t) ∧
      (∀ t, lenBoundT autMP ℓ t ≤ M) ∧
      timeBoundT autMP ℓ ≤ (2 * M + 3) * (14 * (N * K) * j + 8 * N * j + 40 * (N * K) + 55 * N + 10) :=
  boundsT_of check_autMP (vars M N K j 0 0 0) (ℓJ_le M N K j) (ℓJ_out M N K j)
    (by simp [wAut, pEval, mEval, vars]; ring) hℓ hM

end Bounds

/-! ### Framed inside a larger store -/

section Frame

variable {k : ℕ} {M N K j : ℕ} {ℓ : Fin k → ℕ}

theorem frameT_addRMP (e : Fin 28 ↪ Fin k) (hℓ : ∀ i, ℓ (e i) ≤ ℓRing M N K i)
    (hM : ∀ i, ℓ (e i) ≤ M) :
    XProg.timeBoundT (.frame e (.prog addRMP)) ℓ ≤ (2 * M + 3) * (40 * (N * K) + 44 * N + 7) ∧
      (∀ i : Fin 28, i.val < 5 →
        XProg.lenBoundT (.frame e (.prog addRMP)) ℓ (e i) ≤ ℓRing (N * K) N K i) ∧
      ∀ t, (∀ i, e i ≠ t) → XProg.lenBoundT (.frame e (.prog addRMP)) ℓ t = ℓ t :=
  frameT_of check_addRMP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wAddRM, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_subRMP (e : Fin 28 ↪ Fin k) (hℓ : ∀ i, ℓ (e i) ≤ ℓRing M N K i)
    (hM : ∀ i, ℓ (e i) ≤ M) :
    XProg.timeBoundT (.frame e (.prog subRMP)) ℓ ≤ (2 * M + 3) * (40 * (N * K) + 44 * N + 7) ∧
      (∀ i : Fin 28, i.val < 5 →
        XProg.lenBoundT (.frame e (.prog subRMP)) ℓ (e i) ≤ ℓRing (N * K) N K i) ∧
      ∀ t, (∀ i, e i ≠ t) → XProg.lenBoundT (.frame e (.prog subRMP)) ℓ t = ℓ t :=
  frameT_of check_subRMP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wAddRM, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_notP (e : Fin 11 ↪ Fin k) (hℓ : ∀ i, ℓ (e i) ≤ ℓNot M N K i)
    (hM : ∀ i, ℓ (e i) ≤ M) :
    XProg.timeBoundT (.frame e (.prog notP)) ℓ ≤ (2 * M + 3) * (11 * (N * K) + 15) ∧
      (∀ i : Fin 11, i.val < 2 →
        XProg.lenBoundT (.frame e (.prog notP)) ℓ (e i) ≤ ℓNot (N * K) N K i) ∧
      ∀ t, (∀ i, e i ≠ t) → XProg.lenBoundT (.frame e (.prog notP)) ℓ t = ℓ t :=
  frameT_of check_notP (vars M N K 0 0 0 0) (ℓNot_le M N K 0) (ℓNot_out M N K 0)
    (by simp [wNotM, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_rhoJP (e : Fin 7 ↪ Fin k) (hℓ : ∀ i, ℓ (e i) ≤ ℓRho M N K j i)
    (hM : ∀ i, ℓ (e i) ≤ M) :
    XProg.timeBoundT (.frame e (.prog rhoJP)) ℓ ≤ (2 * M + 3) * (7 * j * K + 4 * j + 3) ∧
      (∀ i : Fin 7, i.val < 4 →
        XProg.lenBoundT (.frame e (.prog rhoJP)) ℓ (e i) ≤ ℓRho (N * K) N K j i) ∧
      ∀ t, (∀ i, e i ≠ t) → XProg.lenBoundT (.frame e (.prog rhoJP)) ℓ t = ℓ t :=
  frameT_of check_rhoJP (vars M N K j 0 0 0) (ℓRho_le M N K j) (ℓRho_out M N K j)
    (by simp [wRhoJ, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_scRMP (e : Fin 29 ↪ Fin k) (hℓ : ∀ i, ℓ (e i) ≤ ℓSc M N K i)
    (hM : ∀ i, ℓ (e i) ≤ M) :
    XProg.timeBoundT (.frame e (.prog scRMP)) ℓ ≤
        (2 * M + 3) * (22 * N * K ^ 2 + 67 * (N * K) + 27 * N + 11) ∧
      (∀ i : Fin 29, i.val < 5 →
        XProg.lenBoundT (.frame e (.prog scRMP)) ℓ (e i) ≤ ℓSc (N * K) N K i) ∧
      ∀ t, (∀ i, e i ≠ t) → XProg.lenBoundT (.frame e (.prog scRMP)) ℓ t = ℓ t :=
  frameT_of check_scRMP (vars M N K 0 0 0 0) (ℓSc_le M N K 0) (ℓSc_out M N K 0)
    (by simp [wScRM, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_rotBP (e : Fin 30 ↪ Fin k) (hℓ : ∀ i, ℓ (e i) ≤ ℓJ M N K j i)
    (hM : ∀ i, ℓ (e i) ≤ M) :
    XProg.timeBoundT (.frame e (.prog rotBP)) ℓ ≤
        (2 * M + 3) * (18 * (N * K) * j + 19 * N * j + 11 * j + 3) ∧
      (∀ i : Fin 30, i.val < 5 →
        XProg.lenBoundT (.frame e (.prog rotBP)) ℓ (e i) ≤ ℓJ (N * K) N K j i) ∧
      ∀ t, (∀ i, e i ≠ t) → XProg.lenBoundT (.frame e (.prog rotBP)) ℓ t = ℓ t :=
  frameT_of check_rotBP (vars M N K j 0 0 0) (ℓJ_le M N K j) (ℓJ_out M N K j)
    (by simp [wRotB, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_mulRMP (e : Fin 37 ↪ Fin k) (hℓ : ∀ i, ℓ (e i) ≤ ℓRing M N K i)
    (hM : ∀ i, ℓ (e i) ≤ M) :
    XProg.timeBoundT (.frame e (.prog mulRMP)) ℓ ≤ (2 * M + 3) * (22 * N ^ 2 * K ^ 2 +
        107 * N ^ 2 * K + 71 * N ^ 2 + 24 * (N * K) + 29 * N + 7 * K + 24) ∧
      (∀ i : Fin 37, i.val < 5 →
        XProg.lenBoundT (.frame e (.prog mulRMP)) ℓ (e i) ≤ ℓRing (N * K) N K i) ∧
      ∀ t, (∀ i, e i ≠ t) → XProg.lenBoundT (.frame e (.prog mulRMP)) ℓ t = ℓ t :=
  frameT_of check_mulRMP (vars M N K 0 0 0 0) (ℓRing_le M N K 0 0 0 0) (ℓRing_out M N K 0 0 0 0)
    (by simp [wMulRM, pEval, mEval, vars]; ring) e hℓ hM

theorem frameT_autMP (e : Fin 25 ↪ Fin k) (hℓ : ∀ i, ℓ (e i) ≤ ℓJ M N K j i)
    (hM : ∀ i, ℓ (e i) ≤ M) :
    XProg.timeBoundT (.frame e (.prog autMP)) ℓ ≤
        (2 * M + 3) * (14 * (N * K) * j + 8 * N * j + 40 * (N * K) + 55 * N + 10) ∧
      (∀ i : Fin 25, i.val < 5 →
        XProg.lenBoundT (.frame e (.prog autMP)) ℓ (e i) ≤ ℓJ (N * K) N K j i) ∧
      ∀ t, (∀ i, e i ≠ t) → XProg.lenBoundT (.frame e (.prog autMP)) ℓ t = ℓ t :=
  frameT_of check_autMP (vars M N K j 0 0 0) (ℓJ_le M N K j) (ℓJ_out M N K j)
    (by simp [wAut, pEval, mEval, vars]; ring) e hℓ hM

end Frame

end MersenneT

end Prog

end SigabaNeo.Tape
