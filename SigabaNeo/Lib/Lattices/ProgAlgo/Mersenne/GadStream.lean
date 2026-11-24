import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.EncRow
import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.Bounds

/-!
# The gadget stream `z G` modulo `2^K − 1`

The term `z G` of an encoding (`z ∈ R²`, `G = I₂ ⊗ (1, 2, …, 2^{K−1})`) is the family
`(r, i) ↦ 2^i z_r` over `Fin 2 × Fin K`. `gzP : Prog 36` writes its stream
**`gzW N K z₀ ++ gzW N K z₁`** (`run_gzP`), `gzW N K z = z, 2z, …, 2^{K−1} z` by doublings
(`rotBW` by `K − 1`, i.e. `2^{1 − K} = 2`; `gIt`), with `decRM (gIt N K z i) = 2^i • decRM z`
(`decRM_gIt`):

* tapes: `0` the output register (any word of `2 K · N K` bits before), `1` `z₀`, `2` `z₁`,
  templates `3` (`K`), `4` (`N`), `5` (`N K`), `6` (`K − 1`); scratch `7 … 35`, blank before and
  after.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

/-- The stream `z, 2z, …, 2^{K−1} z`. -/
def gzW (N K : ℕ) (z : List Bool) : List Bool := concatN K (gIt N K z)

theorem length_gzW {N K : ℕ} {z : List Bool} (hz : z.length = N * K) :
    (gzW N K z).length = K * (N * K) := length_concatN fun i _ => length_gIt hz i

/-- The abstract round: the current multiple, the output register. -/
def gzStep (N K : ℕ) : List Bool × List Bool → List Bool × List Bool
  | (cur, out) => (rotBW N K (K - 1) cur, (out ++ cur).drop (N * K))

theorem gzStep_iter {N K : ℕ} {z : List Bool} (hz : z.length = N * K) : ∀ (c : ℕ) (out : List Bool),
    (gzStep N K)^[c] (z, out) = (gIt N K z c, (out ++ concatN c (gIt N K z)).drop (c * (N * K)))
  | 0, out => by simp [concatN, gIt]
  | c + 1, out => by
    rw [Function.iterate_succ_apply', gzStep_iter hz c out]
    have hl : (concatN c (gIt N K z)).length = c * (N * K) := length_concatN fun j _ => length_gIt hz j
    have hd := drop_append_drop out (concatN c (gIt N K z)) (gIt N K z c)
    rw [hl, length_gIt hz c] at hd
    simp only [gzStep, Prod.mk.injEq]
    refine ⟨by rw [gIt, gIt, Function.iterate_succ_apply'], ?_⟩
    rw [hd, show (c + 1) * (N * K) = c * (N * K) + N * K by ring]
    rfl

/-- **The multiples**: `gIt N K z i` reads as `2^i z`. -/
theorem decRM_gIt {N K : ℕ} (hK : 1 ≤ K) {z : List Bool} (hz : z.length = N * K) :
    ∀ i : ℕ, decRM N K (gIt N K z i) = (2 : ZMod (2 ^ K - 1)) ^ i • decRM N K z
  | 0 => by simp [gIt]
  | i + 1 => by
    rw [gIt, Function.iterate_succ_apply', ← gIt]
    have h := decRM_rotBW (i := 1) (length_gIt hz i) hK
    rw [h, decRM_gIt hK hz i, smul_smul, pow_one, pow_succ, mul_comm]

namespace Prog

open scoped Prog

/-- `mvP` from `8` into the output `0`. -/
def zMv : Fin 5 → Fin 36 := ![8, 0, 11, 12, 5]
/-- `rotBP`: `9 := rotBW (K − 1) 7`. -/
def zRot : Fin 30 → Fin 36 := ![9, 7, 6, 3, 4, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
  24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]

set_option maxRecDepth 10000 in
theorem zMv_inj : Function.Injective zMv := by decide
set_option maxRecDepth 10000 in
theorem zRot_inj : Function.Injective zRot := by decide

/-- One multiple: shifted into the output, then doubled. -/
def gzBody : Prog 36 := cp 8 7 ⨾ map zMv mvP ⨾ map zRot rotBP ⨾ cp 7 9 ⨾ clr 9

/-- **The gadget stream of `(z₀, z₁)`.** -/
def gzP : Prog 36 := cp 7 1 ⨾ forN 10 3 gzBody ⨾ cp 7 2 ⨾ forN 10 3 gzBody ⨾ clr 7

def zG (S : Store 36) : List Bool × List Bool → Store 36
  | (cur, out) => Function.update (Function.update S 7 cur) 0 out

set_option maxHeartbeats 4000000 in
theorem run_gzBody {K N : ℕ} (S : Store 36) (hS : ∀ i : Fin 36, 8 ≤ i.val → i.val ≠ 10 → S i = [])
    (hK : (S 3).length = K) (hN : (S 4).length = N) (hNK : (S 5).length = N * K)
    (hj : (S 6).length = K - 1) (a : List Bool × List Bool) (hc : a.1.length = N * K)
    (w : List Bool) :
    run gzBody (Function.update (zG S a) 10 w) = Function.update (zG S (gzStep N K a)) 10 w := by
  obtain ⟨cur, out⟩ := a
  simp only at hc
  simp only [gzBody, run_seq, run_copy, run_clear]
  rw [run_mvP_map zMv_inj _ (by simp [zMv, zG, hS]) (by simp [zMv, zG, hS])]
  rw [run_rotBP_map zRot_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [zRot, zMv, zG, hS] at hi ⊢
  · simp [zRot, zMv, zG, hK]
  · simp [zRot, zMv, zG, hN]
  · simp [zRot, zMv, zG, hc]
  funext t
  simp only [zG, gzStep]
  fin_cases t <;> simp [zRot, zMv, hS, hNK, hj, hc, takeD_of_length' hc]

/-- **The gadget stream**: `0 := gzW z₀ ++ gzW z₁`. -/
theorem run_gzP {K N : ℕ} (s : Store 36) (hs : ∀ i : Fin 36, 7 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hNK : (s 5).length = N * K)
    (hj : (s 6).length = K - 1) (h1 : (s 1).length = N * K) (h2 : (s 2).length = N * K)
    (hO : (s 0).length = (K + K) * (N * K)) :
    run gzP s = Function.update s 0 (gzW N K (s 1) ++ gzW N K (s 2)) := by
  have hclean : ∀ (S : Store 36), (∀ i : Fin 36, 7 ≤ i.val → S i = [] ∨ i.val = 7) →
      ∀ i : Fin 36, 8 ≤ i.val → i.val ≠ 10 → S i = [] := fun S h i hi _ => by
    rcases h i (by omega) with h' | h'
    · exact h'
    · omega
  set s1 := Function.update s 7 (s 1)
  have hl1 := run_forN_inv 10 3 gzBody (zG s1) (gzStep N K) (fun a => a.1.length = N * K)
    (fun a w ha => run_gzBody s1 (fun i hi h10 => by
        have := hs i (by omega)
        simp [s1, Function.update_apply]
        split_ifs with h <;> [(subst h; simp at hi); exact this]) (by simp [s1, hK])
        (by simp [s1, hN]) (by simp [s1, hNK]) (by simp [s1, hj]) a ha w)
    (fun a ha => by obtain ⟨cur, out⟩ := a; exact length_rotBW N K _ ha)
    (s 1, s 0) h1 s1 (by funext t; fin_cases t <;> simp [s1, zG, hs])
  rw [show s1 3 = s 3 by simp [s1], hK, gzStep_iter h1] at hl1
  set s2 := Function.update (Function.update (zG s1 (gIt N K (s 1) K,
    (s 0 ++ concatN K (gIt N K (s 1))).drop (K * (N * K)))) 10 []) 7 (s 2)
  have hl2 := run_forN_inv 10 3 gzBody (zG s2) (gzStep N K) (fun a => a.1.length = N * K)
    (fun a w ha => run_gzBody s2 (fun i hi h10 => by
        have := hs i (by omega)
        simp [s2, s1, zG, Function.update_apply]
        split_ifs with h h' h'' <;> first | rfl | (subst_vars; simp at hi) | omega | exact this)
        (by simp [s2, s1, zG, hK]) (by simp [s2, s1, zG, hN]) (by simp [s2, s1, zG, hNK])
        (by simp [s2, s1, zG, hj]) a ha w)
    (fun a ha => by obtain ⟨cur, out⟩ := a; exact length_rotBW N K _ ha)
    (s 2, (s 0 ++ concatN K (gIt N K (s 1))).drop (K * (N * K))) h2 s2
    (by funext t; fin_cases t <;> simp [s2, s1, zG, hs])
  rw [show s2 3 = s 3 by simp [s2, s1, zG], hK, gzStep_iter h2] at hl2
  have hsplit : run gzP s = run (clr 7) (run (forN 10 3 gzBody) (run (cp 7 2)
      (run (forN 10 3 gzBody) s1))) := by
    simp only [gzP, run_seq, run_copy, s1]
  have e2 : run (cp 7 2) (Function.update (zG s1 (gIt N K (s 1) K,
      (s 0 ++ concatN K (gIt N K (s 1))).drop (K * (N * K)))) 10 []) = s2 := by
    simp only [run_copy, s2]
    congr 1
  rw [hsplit, hl1, e2, hl2]
  have hd := drop_append_drop (s 0) (concatN K (gIt N K (s 1))) (concatN K (gIt N K (s 2)))
  have l1 : (concatN K (gIt N K (s 1))).length = K * (N * K) :=
    length_concatN fun j _ => length_gIt h1 j
  have l2 : (concatN K (gIt N K (s 2))).length = K * (N * K) :=
    length_concatN fun j _ => length_gIt h2 j
  rw [l1, l2] at hd
  rw [hd, show K * (N * K) + K * (N * K) = (s 0).length by rw [hO]; ring,
    drop_append_of_length rfl]
  funext t
  fin_cases t <;> simp [zG, s2, s1, hs, gzW]

section Cert

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT

/-- The inputs of `gzP` (variables `top, N, K`; the template `K − 1` at most `K`). -/
def σGz' : Asg := [pTop, pNK, pNK, pK, pN, pNK, pK]
def σGz : Asg := σGz' ++ List.replicate 29 pTop

/-- A bound of the sweeps of `gzP`. -/
def wGz : Poly := [([], 100), ([0, 0, 1], 400), ([0, 1, 1], 400), ([0, 1, 2], 400), ([0, 1, 3], 100),
  ([0, 0, 2], 100), ([0, 1], 100)]

set_option maxRecDepth 100000 in
/-- **The certificate of `gzP`.** -/
theorem check_gzP : check 8 gzP σGz σGz' wGz = true := by decide +kernel

/-- **The time of the gadget stream** from the inputs at their lengths and tapes at most `M`. -/
theorem time_gzP {M N K : ℕ} {ℓ : Fin 36 → ℕ} (hℓ : ℓ ≤ bnd (vars M N K 0 0 0 0) σGz)
    (hM : ∀ t, ℓ t ≤ M) :
    timeBoundT gzP ℓ ≤ (2 * M + 3) * (100 + 400 * K + 400 * (N * K) + 400 * (N * K ^ 2) +
      100 * (N * K ^ 3) + 100 * K ^ 2 + 100 * N) := by
  refine (bounds_of_check check_gzP (vars M N K 0 0 0 0) hℓ hM).2.2.trans (le_of_eq ?_)
  simp [wGz, pEval, mEval, vars, top]
  ring

end Cert

theorem noGrow_gzP : gzP.NoGrow := rfl
theorem wf_gzP : gzP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
