import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncZRow
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.Canon

/-!
# The gadget ciphertext of an automorphism, entrywise

`C = σ(H) − [0; σ(h)]` (eq. (2) of ePrint 2026/2539, `σ = (σ_g)^{T}`) for a `2 × L` matrix `H` and a
row `h`, as the canonical words of its entries in the order of its word. **`gcAutP : Prog 60`**
(`run_gcAutP`): tapes `0` the output register (shift register), `1` the stream of `H` (consumed,
`2 L` entries), `2` the stream of `h` (consumed, `L` entries), templates `3` (`g`), `4` (`T`), `5`
(`K`), `6` (`N`), `7` (`N K`), `8` (`L`); scratch `9 … 59`.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-- `σ^T` on a word. -/
def autTW (N K g T : ℕ) (x : List Bool) : List Bool := (autMW N K g)^[T] x

/-- One entry of row `0`. -/
def gc0Step (N K g T : ℕ) : List Bool × List Bool → List Bool × List Bool
  | (C, H) => ((C ++ canonW N K (autTW N K g T (takeD (N * K) H))).drop (N * K), H.drop (N * K))

/-- One entry of row `1`. -/
def gc1Step (N K g T : ℕ) :
    List Bool × List Bool × List Bool → List Bool × List Bool × List Bool
  | (C, H, h) => ((C ++ canonW N K (subRMW N K (autTW N K g T (takeD (N * K) H))
      (autTW N K g T (takeD (N * K) h)))).drop (N * K), H.drop (N * K), h.drop (N * K))

namespace Prog

open scoped Prog

def gMvH : Fin 5 → Fin 60 := ![1, 9, 14, 15, 7]
def gMvh : Fin 5 → Fin 60 := ![2, 10, 14, 15, 7]
def gAe : Fin 27 → Fin 60 := ![9, 3, 4, 5, 6, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35]
def gAf : Fin 27 → Fin 60 := ![10, 3, 4, 5, 6, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35]
def gCn0 : Fin 28 → Fin 60 := ![11, 9, 7, 5, 6, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35, 36]
def gSb : Fin 28 → Fin 60 := ![11, 9, 10, 5, 6, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35, 36]
def gCn1 : Fin 28 → Fin 60 := ![12, 11, 7, 5, 6, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35, 36]
def gMvO0 : Fin 5 → Fin 60 := ![11, 0, 14, 15, 7]
def gMvO1 : Fin 5 → Fin 60 := ![12, 0, 14, 15, 7]

set_option maxRecDepth 10000 in
theorem gMvH_inj : Function.Injective gMvH := by decide
set_option maxRecDepth 10000 in
theorem gMvh_inj : Function.Injective gMvh := by decide
set_option maxRecDepth 10000 in
theorem gAe_inj : Function.Injective gAe := by decide
set_option maxRecDepth 10000 in
theorem gAf_inj : Function.Injective gAf := by decide
set_option maxRecDepth 10000 in
theorem gCn0_inj : Function.Injective gCn0 := by decide
set_option maxRecDepth 10000 in
theorem gSb_inj : Function.Injective gSb := by decide
set_option maxRecDepth 10000 in
theorem gCn1_inj : Function.Injective gCn1 := by decide
set_option maxRecDepth 10000 in
theorem gMvO0_inj : Function.Injective gMvO0 := by decide
set_option maxRecDepth 10000 in
theorem gMvO1_inj : Function.Injective gMvO1 := by decide

/-- One entry of row `0`. -/
def gc0Body : Prog 60 :=
  cp 9 7 ⨾ map gMvH mvP ⨾ map gAe autItP ⨾ map gCn0 canonRP ⨾ map gMvO0 mvP ⨾ clr 9 ⨾ clr 11

/-- One entry of row `1`. -/
def gc1Body : Prog 60 :=
  cp 9 7 ⨾ map gMvH mvP ⨾ map gAe autItP ⨾ cp 10 7 ⨾ map gMvh mvP ⨾ map gAf autItP ⨾
    map gSb subRMP ⨾ map gCn1 canonRP ⨾ map gMvO1 mvP ⨾ clr 9 ⨾ clr 10 ⨾ clr 11 ⨾ clr 12

/-- **The gadget ciphertext of an automorphism.** -/
def gcAutP : Prog 60 := forN 13 8 gc0Body ⨾ forN 13 8 gc1Body

theorem run_autItP_map {u : Fin 27 → Fin k} (hu : Function.Injective u) {K N : ℕ} (hN0 : 0 < N)
    (s : Store k) (hs : ∀ i : Fin 27, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 0)).length = N * K) :
    run (map u autItP) s = Function.update s (u 0)
      ((autMW N K (s (u 1)).length)^[(s (u 2)).length] (s (u 0))) :=
  run_map_eq_update hu _ s 0 _ (run_autItP hN0 (s ∘ u) hs hK hN hx)

theorem length_autTW {N K g : ℕ} (hN : 0 < N) {x : List Bool} (hx : x.length = N * K) :
    ∀ T, (autTW N K g T x).length = N * K
  | 0 => hx
  | T + 1 => by
    unfold autTW; rw [Function.iterate_succ_apply']; exact length_autMW _ _ _ _ hN

/-- The store of row `0`. -/
def g0G (S : Store 60) : List Bool × List Bool → Store 60
  | (C, H) => Function.update (Function.update S 0 C) 1 H

/-- The store of row `1`. -/
def g1G (S : Store 60) : List Bool × List Bool × List Bool → Store 60
  | (C, H, h) => Function.update (Function.update (Function.update S 0 C) 1 H) 2 h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_gc0Body {K N : ℕ} (hK : 0 < K) (hN0 : 0 < N) (S : Store 60)
    (hS : ∀ i : Fin 60, 9 ≤ i.val → i.val ≠ 13 → S i = []) (hK' : (S 5).length = K)
    (hN : (S 6).length = N) (hNK : (S 7).length = N * K) (a : List Bool × List Bool)
    (w : List Bool) :
    run gc0Body (Function.update (g0G S a) 13 w) =
      Function.update (g0G S (gc0Step N K (S 3).length (S 4).length a)) 13 w := by
  obtain ⟨C, H⟩ := a
  have hT := length_autTW (g := (S 3).length) hN0 (length_takeD (N * K) H) (S 4).length
  have hc := length_canonW N K hT
  simp only [gc0Body, run_seq, run_copy, run_clear]
  rw [run_mvP_map gMvH_inj _ (by simp [gMvH, g0G, hS]) (by simp [gMvH, g0G, hS])]
  rw [run_autItP_map gAe_inj (K := K) (N := N) hN0 _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [gAe, gMvH, g0G, hS] at hi ⊢
  · simp [gAe, gMvH, g0G, hK']
  · simp [gAe, gMvH, g0G, hN]
  · simp [gAe, gMvH, g0G, hNK, drop_append_of_length]
  rw [run_canonRP_map gCn0_inj (K := K) (N := N) hK _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [gCn0, gAe, gMvH, g0G, hS] at hi ⊢
  · simp [gCn0, gAe, gMvH, g0G, hK']
  · simp [gCn0, gAe, gMvH, g0G, hN]
  · simp [gCn0, gAe, gMvH, g0G, hNK, drop_append_of_length]
    exact hT
  · simp [gCn0, gAe, gMvH, g0G, hNK]
  rw [run_mvP_map gMvO0_inj _ (by simp [gMvO0, gCn0, gAe, gMvH, g0G, hS])
    (by simp [gMvO0, gCn0, gAe, gMvH, g0G, hS])]
  simp only [autTW] at hc
  funext t
  fin_cases t <;> simp [gMvO0, gCn0, gAe, gMvH, g0G, hS, gc0Step, hNK, autTW, hc,
    drop_append_of_length, takeD_of_length' hc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_gc1Body {K N : ℕ} (hK : 0 < K) (hN0 : 0 < N) (S : Store 60)
    (hS : ∀ i : Fin 60, 9 ≤ i.val → i.val ≠ 13 → S i = []) (hK' : (S 5).length = K)
    (hN : (S 6).length = N) (hNK : (S 7).length = N * K)
    (a : List Bool × List Bool × List Bool) (w : List Bool) :
    run gc1Body (Function.update (g1G S a) 13 w) =
      Function.update (g1G S (gc1Step N K (S 3).length (S 4).length a)) 13 w := by
  obtain ⟨C, H, h⟩ := a
  have hT := length_autTW (g := (S 3).length) hN0 (length_takeD (N * K) H) (S 4).length
  have hT' := length_autTW (g := (S 3).length) hN0 (length_takeD (N * K) h) (S 4).length
  have hs := length_subRMW N K hT (autTW N K (S 3).length (S 4).length (takeD (N * K) h))
  have hc := length_canonW N K hs
  simp only [gc1Body, run_seq, run_copy, run_clear]
  rw [run_mvP_map gMvH_inj _ (by simp [gMvH, g1G, hS]) (by simp [gMvH, g1G, hS])]
  rw [run_autItP_map gAe_inj (K := K) (N := N) hN0 _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [gAe, gMvH, g1G, hS] at hi ⊢
  · simp [gAe, gMvH, g1G, hK']
  · simp [gAe, gMvH, g1G, hN]
  · simp [gAe, gMvH, g1G, hNK, drop_append_of_length]
  rw [run_mvP_map gMvh_inj _ (by simp [gMvh, gAe, gMvH, g1G, hS])
    (by simp [gMvh, gAe, gMvH, g1G, hS])]
  rw [run_autItP_map gAf_inj (K := K) (N := N) hN0 _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [gAf, gMvh, gAe, gMvH, g1G, hS] at hi ⊢
  · simp [gAf, gMvh, gAe, gMvH, g1G, hK']
  · simp [gAf, gMvh, gAe, gMvH, g1G, hN]
  · simp [gAf, gMvh, gAe, gMvH, g1G, hNK, drop_append_of_length]
  rw [run_subRMP_map gSb_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [gSb, gAf, gMvh, gAe, gMvH, g1G, hS] at hi ⊢
  · simp [gSb, gAf, gMvh, gAe, gMvH, g1G, hK']
  · simp [gSb, gAf, gMvh, gAe, gMvH, g1G, hN]
  · simp [gSb, gAf, gMvh, gAe, gMvH, g1G, hNK, drop_append_of_length]
    exact hT
  · simp [gSb, gAf, gMvh, gAe, gMvH, g1G, hNK, drop_append_of_length]
    exact hT'
  rw [run_canonRP_map gCn1_inj (K := K) (N := N) hK _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [gCn1, gSb, gAf, gMvh, gAe, gMvH, g1G, hS] at hi ⊢
  · simp [gCn1, gSb, gAf, gMvh, gAe, gMvH, g1G, hK']
  · simp [gCn1, gSb, gAf, gMvh, gAe, gMvH, g1G, hN]
  · simp [gCn1, gSb, gAf, gMvh, gAe, gMvH, g1G, hNK, drop_append_of_length]
    exact hs
  · simp [gCn1, gSb, gAf, gMvh, gAe, gMvH, g1G, hNK]
  rw [run_mvP_map gMvO1_inj _ (by simp [gMvO1, gCn1, gSb, gAf, gMvh, gAe, gMvH, g1G, hS])
    (by simp [gMvO1, gCn1, gSb, gAf, gMvh, gAe, gMvH, g1G, hS])]
  simp only [autTW] at hc
  funext t
  fin_cases t <;> simp [gMvO1, gCn1, gSb, gAf, gMvh, gAe, gMvH, g1G, hS, gc1Step, hNK, autTW, hc,
    drop_append_of_length, takeD_of_length' hc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The gadget ciphertext of an automorphism**: `|8|` entries of row `0` from `1`, then `|8|`
entries of row `1` from `1` and `2`, shifted into `0`. -/
theorem run_gcAutP {K N : ℕ} (hK : 0 < K) (hN0 : 0 < N) (s : Store 60)
    (hs : ∀ i : Fin 60, 9 ≤ i.val → s i = []) (hK' : (s 5).length = K) (hN : (s 6).length = N)
    (hNK : (s 7).length = N * K) :
    run gcAutP s = g1G s ((gc1Step N K (s 3).length (s 4).length)^[(s 8).length]
      (((gc0Step N K (s 3).length (s 4).length)^[(s 8).length] (s 0, s 1)).1,
       ((gc0Step N K (s 3).length (s 4).length)^[(s 8).length] (s 0, s 1)).2, s 2)) := by
  have h1 := run_forN 13 8 gc0Body (g0G s) (gc0Step N K (s 3).length (s 4).length)
    (fun a w => run_gc0Body hK hN0 s (fun i hi _ => hs i hi) hK' hN hNK a w) (s 0, s 1) s
    (by funext t; fin_cases t <;> simp [g0G])
  generalize hr : (gc0Step N K (s 3).length (s 4).length)^[(s 8).length] (s 0, s 1) = r at h1
  obtain ⟨C1, H1⟩ := r
  have h2 := run_forN 13 8 gc1Body (g1G s) (gc1Step N K (s 3).length (s 4).length)
    (fun a w => run_gc1Body hK hN0 s (fun i hi _ => hs i hi) hK' hN hNK a w) (C1, H1, s 2)
    (Function.update (g0G s (C1, H1)) 13 [])
    (by funext t; fin_cases t <;> simp [g0G, g1G, hs])
  rw [gcAutP, run_seq, h1, h2, show Function.update (g0G s (C1, H1)) 13 [] 8 = s 8 by simp [g0G]]
  funext t
  generalize (gc1Step N K (s 3).length (s 4).length)^[(s 8).length] (C1, H1, s 2) = r
  obtain ⟨C, H, h⟩ := r
  fin_cases t <;> simp [g1G, hs]

theorem noGrow_gcAutP : gcAutP.NoGrow := rfl
theorem wf_gcAutP : gcAutP.WF := wf_of_wfB (by decide)

/-! ### Certificate -/

section Cert

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT

/-- The inputs of `gcAutP` (variables `top, N, K, g, T, L`). -/
def σGc' : Asg := [pTop, pTop, pTop, pm, pn, pK, pN, pNK, pl]
def σGc : Asg := σGc' ++ List.replicate 51 pTop

/-- A bound of the sweeps of `gcAutP`: `3 L` iterated automorphisms. -/
def wGc : Poly := [([], 20), ([0, 0, 0, 0, 0, 1], 200), ([0, 1, 0, 0, 0, 1], 400),
  ([0, 1, 1, 0, 0, 1], 400), ([0, 0, 0, 0, 1, 1], 100), ([0, 1, 0, 0, 1, 1], 200),
  ([0, 1, 1, 0, 1, 1], 200), ([0, 1, 0, 1, 1, 1], 50), ([0, 1, 1, 1, 1, 1], 50)]

set_option maxRecDepth 100000 in
/-- **The certificate of `gcAutP`.** -/
theorem check_gcAutP : check 8 gcAutP σGc σGc' wGc = true := by decide +kernel

/-- The sweeps of `gcAutP`. -/
def gcSweeps (N K g T L : ℕ) : ℕ := 20 + L * (200 + 400 * N + 400 * (N * K) + T * (100 + 200 * N +
  200 * (N * K) + 50 * (N * g) + 50 * (N * K * g)))

set_option maxHeartbeats 4000000 in
theorem time_gcAutP {M N K g T L : ℕ} {ℓ : Fin 60 → ℕ} (hℓ : ℓ ≤ bnd (vars M N K g T L 0) σGc)
    (hM : ∀ t, ℓ t ≤ M) : timeBoundT gcAutP ℓ ≤ (2 * M + 3) * gcSweeps N K g T L := by
  refine (bounds_of_check check_gcAutP (vars M N K g T L 0) hℓ hM).2.2.trans
    (Nat.mul_le_mul_left _ (le_of_eq ?_))
  simp [wGc, pEval, mEval, vars, top, gcSweeps]
  ring

end Cert

end Prog

end SigabaNeo.Tape
