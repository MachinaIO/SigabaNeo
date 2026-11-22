import SigabaNeo.Lib.Lattices.ProgAlgo.KeySum
import SigabaNeo.Lib.Lattices.ProgAlgo.SpecT

/-!
# Bounds of the key-matrix sum on tapes

* `bounds_keySumP`, `bounds_simKeyP`, `bounds_simTmplP`: the global bounds (`C · (L + 1) ^ d` on
  words at most `L` long, from the syntactic constants), and membership in the fragment `NoGrow`,
  well-formedness;
* `boundsT_keySumP`: **per-tape bounds**, certified by the abstract interpreter
  (`check … = true` by `decide +kernel`): with the store of `Lst` bits, the positions of `Lpos` bits
  and the templates of their lengths (`ℓKS`), every tape stays at most `M` and the time is at most
  `(2 M + 3) · keySumSweeps N K m k W V off` — leading term `176 N³ K² m k⁴`: the `2k · k · N`
  rounds each multiply an `m × 2k` by a `2k × 2k` matrix of ring elements (`m · 2k · 2k` products of
  `22 N² K²` sweeps); the reads cost `6 N k² (W V + W + off)`.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Tape.Sym

namespace Prog

/-! ### Global bounds -/

theorem noGrow_readP : readP.NoGrow := rfl
theorem noGrow_vtermP : vtermP.NoGrow := rfl
theorem noGrow_keySumP : keySumP.NoGrow := rfl
theorem noGrow_simKeyP : simKeyP.NoGrow := rfl
theorem noGrow_simTmplP : simTmplP.NoGrow := rfl
theorem wf_readP : readP.WF := wf_of_wfB (by decide +kernel)
theorem wf_vtermP : vtermP.WF := wf_of_wfB (by decide +kernel)
theorem wf_keySumP : keySumP.WF := wf_of_wfB (by decide +kernel)
theorem wf_simKeyP : simKeyP.WF := wf_of_wfB (by decide +kernel)
theorem wf_simTmplP : simTmplP.WF := wf_of_wfB (by decide +kernel)

theorem tbC_keySumP : tbC keySumP = 3409 := by decide +kernel
theorem tbD_keySumP : tbD keySumP = 11 := by decide +kernel
theorem tbC_simKeyP : tbC simKeyP = 3723 := by decide +kernel
theorem tbD_simKeyP : tbD simKeyP = 11 := by decide +kernel
theorem tbC_simTmplP : tbC simTmplP = 649 := by decide +kernel
theorem tbD_simTmplP : tbD simTmplP = 4 := by decide +kernel

/-- **Global bounds of `keySumP`**: lengths unchanged, time at most `3409 (L + 1) ^ 11`. -/
theorem bounds_keySumP (L : ℕ) :
    lenBound keySumP L = L ∧ timeBound keySumP L ≤ 3409 * (L + 1) ^ 11 ∧
      timeBoundT keySumP (fun _ => L) ≤ 3409 * (L + 1) ^ 11 := by
  have h := timeBound_le keySumP noGrow_keySumP L
  rw [tbC_keySumP, tbD_keySumP] at h
  exact ⟨lenBound_eq _ noGrow_keySumP L, h, (timeBoundT_const_le _ L).trans h⟩

/-- **Global bounds of `simKeyP`**: time at most `3723 (L + 1) ^ 11`. -/
theorem bounds_simKeyP (L : ℕ) :
    lenBound simKeyP L = L ∧ timeBound simKeyP L ≤ 3723 * (L + 1) ^ 11 ∧
      timeBoundT simKeyP (fun _ => L) ≤ 3723 * (L + 1) ^ 11 := by
  have h := timeBound_le simKeyP noGrow_simKeyP L
  rw [tbC_simKeyP, tbD_simKeyP] at h
  exact ⟨lenBound_eq _ noGrow_simKeyP L, h, (timeBoundT_const_le _ L).trans h⟩

/-- **Global bounds of `simTmplP`**: time at most `649 (L + 1) ^ 4`. -/
theorem bounds_simTmplP (L : ℕ) :
    lenBound simTmplP L = L ∧ timeBound simTmplP L ≤ 649 * (L + 1) ^ 4 ∧
      timeBoundT simTmplP (fun _ => L) ≤ 649 * (L + 1) ^ 4 := by
  have h := timeBound_le simTmplP noGrow_simTmplP L
  rw [tbC_simTmplP, tbD_simTmplP] at h
  exact ⟨lenBound_eq _ noGrow_simTmplP L, h, (timeBoundT_const_le _ L).trans h⟩

/-! ### Per-tape bounds of `keySumP`

The variables: `0` the top size `M`, then `N`, `K`, `m`, `k`, `W`, `V`, `off`, and the lengths
`Lst`, `Lpos` of the store and of the positions. -/

namespace KST

/-- The values of the variables. -/
def ksVars (M N K m k W V off Lst Lpos : ℕ) : List ℕ := [M, N, K, m, k, W, V, off, Lst, Lpos]

/-- The monomial `c · N^a · K^b · …` with exponents `e`. -/
def q (c : ℕ) (e : List ℕ) : Poly := [(0 :: e, c)]

/-- The abstract inputs: the output any word of length at most `M`, the store, the positions, the
templates. -/
def σKS : Asg :=
  [pTop, q 1 [0, 0, 0, 0, 0, 0, 0, 1], q 1 [0, 0, 0, 0, 0, 0, 0, 0, 1], q 1 [0, 1], q 1 [1],
    q 1 [1, 1], q 1 [0, 0, 0, 1], q 2 [0, 0, 0, 1], q 2 [0, 0, 0, 1], q 2 [1, 0, 0, 1],
    q 2 [1, 1, 0, 1], q 4 [1, 1, 0, 2], q 1 [0, 0, 1], q 2 [1, 1, 1, 1], q 2 [1, 0, 1, 1],
    q 1 [0, 0, 0, 0, 1], q 1 [0, 0, 0, 0, 0, 1], q 1 [0, 0, 0, 0, 0, 0, 1]]

/-- The abstract outputs: the output of `m · 2k · N K` bits, the rest unchanged. -/
def σKS' : Asg := q 2 [1, 1, 1, 1] :: σKS.tail

/-- The sweeps of `keySumP`. -/
def wKS : Poly :=
  [([], 11), ([0, 0, 0, 0, 1], 78), ([0, 0, 1, 0, 1], 22), ([0, 0, 0, 0, 2], 84), ([0, 1, 0, 0, 2], 148), ([0, 1, 0, 0, 2, 1], 26), ([0, 1, 0, 0, 2, 1, 1], 6), ([0, 1, 0, 0, 2, 0, 0, 1], 6), ([0, 2, 1, 1, 3], 188), ([0, 2, 0, 0, 2], 24), ([0, 2, 1, 0, 2], 36), ([0, 1, 0, 0, 3], 82), ([0, 2, 1, 0, 3], 60), ([0, 2, 0, 0, 4], 172), ([0, 2, 1, 0, 4], 224), ([0, 1, 0, 1, 2], 128), ([0, 1, 0, 1, 3], 188), ([0, 1, 0, 1, 4], 584), ([0, 2, 1, 1, 4], 840), ([0, 1, 0, 1, 5], 64), ([0, 2, 1, 1, 5], 48), ([0, 2, 0, 1, 4], 936), ([0, 3, 0, 1, 4], 488), ([0, 3, 1, 1, 4], 776), ([0, 3, 2, 1, 4], 176), ([0, 1, 1, 1, 4], 184), ([0, 2, 0, 1, 3], 112), ([0, 1, 1, 1, 3], 116), ([0, 0, 1, 0, 2], 22), ([0, 1, 1, 1, 2], 116)]

set_option maxRecDepth 100000 in
theorem check_keySumP : check 8 keySumP σKS σKS' wKS = true := by decide +kernel

end KST

/-- The sweeps of `keySumP`. -/
def keySumSweeps (N K m k W V off : ℕ) : ℕ :=
  176 * N ^ 3 * K ^ 2 * m * k ^ 4 +
    48 * N ^ 2 * K * m * k ^ 5 +
    776 * N ^ 3 * K * m * k ^ 4 +
    840 * N ^ 2 * K * m * k ^ 4 +
    488 * N ^ 3 * m * k ^ 4 +
    188 * N ^ 2 * K * m * k ^ 3 +
    224 * N ^ 2 * K * k ^ 4 +
    64 * N * m * k ^ 5 +
    936 * N ^ 2 * m * k ^ 4 +
    184 * N * K * m * k ^ 4 +
    60 * N ^ 2 * K * k ^ 3 +
    172 * N ^ 2 * k ^ 4 +
    584 * N * m * k ^ 4 +
    112 * N ^ 2 * m * k ^ 3 +
    116 * N * K * m * k ^ 3 +
    6 * N * k ^ 2 * W * V +
    36 * N ^ 2 * K * k ^ 2 +
    188 * N * m * k ^ 3 +
    116 * N * K * m * k ^ 2 +
    26 * N * k ^ 2 * W +
    6 * N * k ^ 2 * off +
    24 * N ^ 2 * k ^ 2 +
    82 * N * k ^ 3 +
    128 * N * m * k ^ 2 +
    148 * N * k ^ 2 +
    22 * K * k ^ 2 +
    22 * K * k +
    84 * k ^ 2 +
    78 * k +
    11

/-- The per-tape input bounds of `keySumP`: `0` the output (at most `o`), `1` the store, `2` the
positions, the templates of `KTmpl`; scratch blank. -/
def ℓKS (o N K m k W V off Lst Lpos : ℕ) (t : Fin 86) : ℕ :=
  match t.val with
  | 0 => o | 1 => Lst | 2 => Lpos | 3 => K | 4 => N | 5 => N * K | 6 => k | 7 => 2 * k
  | 8 => 2 * k | 9 => 2 * k * N | 10 => 2 * k * (N * K) | 11 => 2 * k * (2 * k * (N * K))
  | 12 => m | 13 => m * (2 * k) * (N * K) | 14 => m * (2 * k) * N | 15 => W | 16 => V
  | 17 => off | _ => 0

section

open KST

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable (M N K m k W V off Lst Lpos : ℕ)

theorem ℓKS_le : ℓKS M N K m k W V off Lst Lpos ≤ bnd (ksVars M N K m k W V off Lst Lpos) σKS := by
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | v, hv⟩ <;>
    simp_all [ℓKS, bnd, aGet, σKS, q, pTop, pEval, mEval, ksVars] <;>
    first | omega | exact le_of_eq (by ring) | ring

theorem ℓKS_out : ∀ t : Fin 86, t.val < σKS'.length →
    pEval (ksVars M N K m k W V off Lst Lpos) (aGet σKS' t.val) =
      ℓKS (m * (2 * k) * (N * K)) N K m k W V off Lst Lpos t := by
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | v, hv⟩ <;>
    simp_all [ℓKS, bnd, aGet, σKS, σKS', q, pTop, pEval, mEval, ksVars] <;>
    first | omega | ring

set_option maxHeartbeats 4000000 in
/-- **Per-tape bounds of `keySumP`**: on the store of `Lst` bits, the positions of `Lpos` bits and
the templates (`ℓKS`), every tape at most `M`: the output gets `m · 2k · N K` bits, the other first
tapes keep their lengths, and the time is at most `(2 M + 3) · keySumSweeps …`. -/
theorem boundsT_keySumP {ℓ : Fin 86 → ℕ} (hℓ : ℓ ≤ ℓKS M N K m k W V off Lst Lpos)
    (hM : ∀ t, ℓ t ≤ M) :
    (∀ t : Fin 86, t.val < 18 →
        lenBoundT keySumP ℓ t ≤ ℓKS (m * (2 * k) * (N * K)) N K m k W V off Lst Lpos t) ∧
      (∀ t, lenBoundT keySumP ℓ t ≤ M) ∧
      timeBoundT keySumP ℓ ≤ (2 * M + 3) * keySumSweeps N K m k W V off :=
  SpecT.boundsT_of check_keySumP (ksVars M N K m k W V off Lst Lpos) (ℓKS_le M N K m k W V off Lst Lpos)
    (ℓKS_out M N K m k W V off Lst Lpos)
    (by simp only [wKS, keySumSweeps, pEval, mEval, ksVars, List.headD, List.tail]; ring) hℓ hM

end

/-! ### Per-tape bounds of `simKeyP` and `simTmplP` -/

namespace KST

/-- The values of the variables of `simKeyP`: those of `keySumP`, then the length `Lst₂` of the
second store and `W'`, `V'`, `off'`. -/
def skVars (M N K m k W V off Lst Lpos Lst₂ W' V' off' : ℕ) : List ℕ :=
  [M, N, K, m, k, W, V, off, Lst, Lpos, Lst₂, W', V', off']

def σSK : Asg := σKS ++ List.replicate 68 [] ++
  [q 1 [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], q 1 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    q 1 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], q 1 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    q 1 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- The claim: the output of `m · 2k · N K` bits. -/
def σSK' : Asg := [q 2 [1, 1, 1, 1]]

/-- The sweeps of `simKeyP`. -/
def wSK : Poly := (([], 35) :: wKS.tail) ++
  [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 13), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], 3),
    ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 3), ([0, 1, 1, 1, 1], 70), ([0, 1, 0, 1, 1], 56)]

set_option maxRecDepth 100000 in
theorem check_simKeyP : check 8 simKeyP σSK σSK' wSK = true := by decide +kernel

/-- The values of the variables of `simTmplP`. -/
def tmVars (M N K k Lw : ℕ) : List ℕ := [M, N, K, k, Lw]

def σTm : Asg :=
  [pTop, pTop, pTop, pTop, q 1 [0, 1], q 1 [1], q 1 [1, 1], q 1 [0, 0, 1], q 2 [1, 1, 1],
    q 4 [1, 1, 1], q 1 [1, 1, 1], q 1 [0, 0, 0, 1]]

def σTm' : Asg :=
  [q 2 [1, 1, 1], q 4 [1, 1, 1], q 1 [0, 0, 0, 1], q 1 [1, 1], q 1 [0, 1], q 1 [1], q 1 [1, 1],
    q 1 [0, 0, 1], q 2 [1, 1, 1], q 4 [1, 1, 1], q 1 [1, 1, 1], q 1 [0, 0, 0, 1]]

/-- The sweeps of `simTmplP`. -/
def wTm : Poly :=
  [([], 63), ([0, 0, 1], 22), ([0, 0, 0, 1], 34), ([0, 1, 0, 1], 9), ([0, 1, 1, 1], 36),
    ([0, 0, 1, 1], 11), ([0, 1], 9), ([0, 1, 1], 6)]

set_option maxRecDepth 100000 in
theorem check_simTmplP : check 8 simTmplP σTm σTm' wTm = true := by decide +kernel

end KST

/-- The per-tape input bounds of `simKeyP`: those of `keySumP` on `0 … 85`, then the second store
(`Lst₂` bits), its position (`W'` bits) and the templates `W'`, `V'`, `off'`; `91 … 93` blank. -/
def ℓSK (o N K m k W V off Lst Lpos Lst₂ W' V' off' : ℕ) (t : Fin 94) : ℕ :=
  if h : t.val < 86 then ℓKS o N K m k W V off Lst Lpos ⟨t.val, h⟩ else
  match t.val with
  | 86 => Lst₂ | 87 => W' | 88 => W' | 89 => V' | 90 => off' | _ => 0

/-- The per-tape input bounds of `simTmplP`: the outputs at most `o`, the templates. -/
def ℓTm (o N K k Lw : ℕ) (t : Fin 31) : ℕ :=
  match t.val with
  | 0 => o | 1 => o | 2 => o | 3 => o | 4 => K | 5 => N | 6 => N * K | 7 => k
  | 8 => 2 * k * (N * K) | 9 => 2 * (2 * k) * (N * K) | 10 => k * (N * K) | 11 => Lw | _ => 0

/-- The sweeps of `simKeyP`. -/
def simKeySweeps (N K m k W V off W' V' off' : ℕ) : ℕ :=
  keySumSweeps N K m k W V off + 24 + 13 * W' + 3 * W' * V' + 3 * off' + 70 * N * K * m * k +
    56 * N * m * k

/-- The sweeps of `simTmplP`. -/
def simTmplSweeps (N K k : ℕ) : ℕ :=
  63 + 22 * K + 34 * k + 9 * N * k + 36 * N * K * k + 11 * K * k + 9 * N + 6 * N * K

section

open KST

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

theorem ℓSK_le (M N K m k W V off Lst Lpos Lst₂ W' V' off' : ℕ) :
    ℓSK M N K m k W V off Lst Lpos Lst₂ W' V' off' ≤
      bnd (skVars M N K m k W V off Lst Lpos Lst₂ W' V' off') σSK := by
  rintro ⟨v, hv⟩
  interval_cases v <;>
    simp [ℓSK, ℓKS, bnd, aGet, σSK, σKS, q, pTop, pEval, mEval, skVars] <;>
    first | omega | exact le_of_eq (by ring) | ring

theorem ℓTm_le (M N K k Lw : ℕ) : ℓTm M N K k Lw ≤ bnd (tmVars M N K k Lw) σTm := by
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | v, hv⟩ <;>
    simp_all [ℓTm, bnd, aGet, σTm, q, pTop, pEval, mEval, tmVars] <;>
    first | omega | exact le_of_eq (by ring) | ring

set_option maxHeartbeats 4000000 in
/-- **Per-tape bounds of `simKeyP`**: every tape at most `M`, the output `m · 2k · N K` bits, and
the time at most `(2 M + 3) · simKeySweeps …`. -/
theorem boundsT_simKeyP (M N K m k W V off Lst Lpos Lst₂ W' V' off' : ℕ) {ℓ : Fin 94 → ℕ}
    (hℓ : ℓ ≤ ℓSK M N K m k W V off Lst Lpos Lst₂ W' V' off') (hM : ∀ t, ℓ t ≤ M) :
    lenBoundT simKeyP ℓ 0 ≤ m * (2 * k) * (N * K) ∧ (∀ t, lenBoundT simKeyP ℓ t ≤ M) ∧
      timeBoundT simKeyP ℓ ≤ (2 * M + 3) * simKeySweeps N K m k W V off W' V' off' := by
  obtain ⟨h1, h2, h3⟩ := bounds_of_check check_simKeyP
    (skVars M N K m k W V off Lst Lpos Lst₂ W' V' off')
    (hℓ.trans (ℓSK_le M N K m k W V off Lst Lpos Lst₂ W' V' off')) hM
  have ht : top (skVars M N K m k W V off Lst Lpos Lst₂ W' V' off') = M := rfl
  have hw : pEval (skVars M N K m k W V off Lst Lpos Lst₂ W' V' off') wSK =
      simKeySweeps N K m k W V off W' V' off' := by
    simp only [wSK, wKS, simKeySweeps, keySumSweeps, pEval, mEval, skVars, List.headD, List.tail,
      List.cons_append, List.nil_append]
    ring
  have ho : pEval (skVars M N K m k W V off Lst Lpos Lst₂ W' V' off') (aGet σSK' 0) =
      m * (2 * k) * (N * K) := by
    simp [σSK', aGet, q, pEval, mEval, skVars]; ring
  rw [ht] at h2 h3
  rw [hw] at h3
  exact ⟨(h1 0 (by decide)).trans ho.le, h2, h3⟩

set_option maxHeartbeats 4000000 in
/-- **Per-tape bounds of `simTmplP`**: the outputs get `2k N K`, `2 · 2k N K`, `Lw`, `N K` bits,
every tape at most `M`, and the time is at most `(2 M + 3) · simTmplSweeps N K k`. -/
theorem boundsT_simTmplP (M N K k Lw : ℕ) {ℓ : Fin 31 → ℕ} (hℓ : ℓ ≤ ℓTm M N K k Lw)
    (hM : ∀ t, ℓ t ≤ M) :
    lenBoundT simTmplP ℓ 0 ≤ 2 * k * (N * K) ∧ lenBoundT simTmplP ℓ 1 ≤ 2 * (2 * k) * (N * K) ∧
      lenBoundT simTmplP ℓ 2 ≤ Lw ∧ lenBoundT simTmplP ℓ 3 ≤ N * K ∧
      (∀ t, lenBoundT simTmplP ℓ t ≤ M) ∧
      timeBoundT simTmplP ℓ ≤ (2 * M + 3) * simTmplSweeps N K k := by
  obtain ⟨h1, h2, h3⟩ := bounds_of_check check_simTmplP (tmVars M N K k Lw)
    (hℓ.trans (ℓTm_le M N K k Lw)) hM
  have ht : top (tmVars M N K k Lw) = M := rfl
  have hw : pEval (tmVars M N K k Lw) wTm = simTmplSweeps N K k := by
    simp only [wTm, simTmplSweeps, pEval, mEval, tmVars, List.headD, List.tail]; ring
  rw [ht] at h2 h3
  rw [hw] at h3
  refine ⟨(h1 0 (by decide)).trans (le_of_eq ?_), (h1 1 (by decide)).trans (le_of_eq ?_),
    (h1 2 (by decide)).trans (le_of_eq ?_), (h1 3 (by decide)).trans (le_of_eq ?_), h2, h3⟩
  all_goals (simp [σTm', aGet, q, pEval, mEval, tmVars]; try ring)

end

end Prog

end SigabaNeo.Tape
