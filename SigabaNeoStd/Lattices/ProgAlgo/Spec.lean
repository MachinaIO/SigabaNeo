import SigabaNeoStd.Lattices.ProgAlgo.Nand

/-!
# The word algorithms as tape programs: interface

For each word function of `SigabaNeo.Lattices.Algo` (`RingWords`, `MatWords`), a program `p` of
the tape language over a fixed set of tapes, to be placed on any distinct tapes of a machine with
`k` tapes by an injective `u` (`Prog.map u p`), with

* **its law** (`law_*`): on inputs of the right lengths, with the templates of the sizes on their
  tapes and its scratch tapes blank, `law (map u p) s = PMF.pure (Function.update s (u 0) v)` with
  `v` the word function of the inputs;
* **its frame**: every tape outside the image of `u` is preserved (`preserves_map_of_not_mem`);
  scratch tapes are blank again afterwards, so the store is exactly the update;
* **well-formedness** (`wf_*`, placed by `WF.map`) and membership in the fragment `NoGrow`;
* **its bounds** (`bounds_*`, unchanged by `map`: `lenBound_map`, `timeBound_map`, `size_map`): the
  length bound is the identity (`lenBound p L = L`), the time on words at most `L` long is at most
  `C · (L + 1) ^ d`, and the machine has `S` states.

The sizes `N`, `K`, `k`, `m`, `n`, `l` are not in the programs: they enter through template tapes
holding words of the corresponding lengths (any content), copied to counters and registers. So a
program is the same for all sizes and its state count is a constant.

| program | value on tape `u 0` | `C`, `d` | states |
|---|---|---|---|
| `addRWP`, `subRWP` | `addRW N K`, `subRW N K` (`matAddW`, `matSubW` with `L · N` blocks) | 210, 3 | 2365 |
| `mulRWP` | `mulRW N K` | 1318, 5 | 14877 |
| `digitRWP` | `digitRW N K i` | 332, 4 | 3751 |
| `monoWP` | `monoW N K j`, `constW N K` | 81, 3 | 912 |
| `matMulP` | `matMulW N K m n l` | 1716, 8 | 19366 |
| `ginvP` | `ginvW N K k` | 375, 4 | 4229 |
| `gadP` | `gadW N K k` | 375, 4 | 4221 |
| `nandP` | `nandPKW N K k` | 2691, 8 | 30361 |
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k : ℕ}

namespace Prog

/-! ### Bounds -/


theorem bounds_addRWP (L : ℕ) : lenBound addRWP L = L ∧ timeBound addRWP L ≤ 210 * (L + 1) ^ 3 ∧
    size addRWP = 2365 := bounds_of _ noGrow_addRWP rfl rfl rfl L
theorem bounds_subRWP (L : ℕ) : lenBound subRWP L = L ∧ timeBound subRWP L ≤ 210 * (L + 1) ^ 3 ∧
    size subRWP = 2365 := bounds_of _ noGrow_subRWP rfl rfl rfl L
theorem bounds_mulRWP (L : ℕ) : lenBound mulRWP L = L ∧ timeBound mulRWP L ≤ 1318 * (L + 1) ^ 5 ∧
    size mulRWP = 14877 := bounds_of _ noGrow_mulRWP rfl rfl rfl L
theorem bounds_digitRWP (L : ℕ) : lenBound digitRWP L = L ∧
    timeBound digitRWP L ≤ 332 * (L + 1) ^ 4 ∧ size digitRWP = 3751 :=
  bounds_of _ noGrow_digitRWP rfl rfl rfl L
theorem bounds_monoWP (L : ℕ) : lenBound monoWP L = L ∧ timeBound monoWP L ≤ 81 * (L + 1) ^ 3 ∧
    size monoWP = 912 := bounds_of _ noGrow_monoWP rfl rfl rfl L
theorem bounds_matMulP (L : ℕ) : lenBound matMulP L = L ∧
    timeBound matMulP L ≤ 1716 * (L + 1) ^ 8 ∧ size matMulP = 19366 :=
  bounds_of _ noGrow_matMulP rfl rfl rfl L
theorem bounds_ginvP (L : ℕ) : lenBound ginvP L = L ∧ timeBound ginvP L ≤ 375 * (L + 1) ^ 4 ∧
    size ginvP = 4229 := bounds_of _ noGrow_ginvP rfl rfl rfl L
theorem bounds_gadP (L : ℕ) : lenBound gadP L = L ∧ timeBound gadP L ≤ 375 * (L + 1) ^ 4 ∧
    size gadP = 4221 := bounds_of _ noGrow_gadP rfl rfl rfl L
theorem bounds_nandP (L : ℕ) : lenBound nandP L = L ∧ timeBound nandP L ≤ 2691 * (L + 1) ^ 8 ∧
    size nandP = 30361 := bounds_of _ noGrow_nandP rfl rfl rfl L

/-! ### Laws, placed on any distinct tapes -/

section Placed

variable {K N : ℕ}

/-- `u 0 := addRW N K (s (u 1)) (s (u 2))`; templates `u 3`, `u 4` of lengths `K`, `N`. -/
theorem law_addRWP_map {u : Fin 28 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) (hy : (s (u 2)).length = N * K) :
    law (map u addRWP) s = PMF.pure (Function.update s (u 0) (addRW N K (s (u 1)) (s (u 2)))) :=
  law_map_eq_update hu _ noGrow_addRWP s 0 _ (run_addRWP _ hs hK hN hx hy)

/-- `u 0 := subRW N K (s (u 1)) (s (u 2))`. -/
theorem law_subRWP_map {u : Fin 28 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) (hy : (s (u 2)).length = N * K) :
    law (map u subRWP) s = PMF.pure (Function.update s (u 0) (subRW N K (s (u 1)) (s (u 2)))) :=
  law_map_eq_update hu _ noGrow_subRWP s 0 _ (run_subRWP _ hs hK hN hx hy)

/-- `u 0 := matAddW N K L (s (u 1)) (s (u 2))`; template `u 4` of length `L · N`. -/
theorem law_matAddP_map {L : ℕ} {u : Fin 28 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hLN : (s (u 4)).length = L * N) (hx : (s (u 1)).length = L * N * K)
    (hy : (s (u 2)).length = L * N * K) :
    law (map u addRWP) s =
      PMF.pure (Function.update s (u 0) (matAddW N K L (s (u 1)) (s (u 2)))) :=
  law_map_eq_update hu _ noGrow_addRWP s 0 _ (run_addRWP_mat _ hs hK hLN hx hy)

/-- `u 0 := matSubW N K L (s (u 1)) (s (u 2))`. -/
theorem law_matSubP_map {L : ℕ} {u : Fin 28 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hLN : (s (u 4)).length = L * N) (hx : (s (u 1)).length = L * N * K)
    (hy : (s (u 2)).length = L * N * K) :
    law (map u subRWP) s =
      PMF.pure (Function.update s (u 0) (matSubW N K L (s (u 1)) (s (u 2)))) :=
  law_map_eq_update hu _ noGrow_subRWP s 0 _ (run_subRWP_mat _ hs hK hLN hx hy)

/-- `u 0 := mulRW N K (s (u 1)) (s (u 2))`. -/
theorem law_mulRWP_map {u : Fin 38 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 38, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) (hy : (s (u 2)).length = N * K) :
    law (map u mulRWP) s = PMF.pure (Function.update s (u 0) (mulRW N K (s (u 1)) (s (u 2)))) :=
  law_map_eq_update hu _ noGrow_mulRWP s 0 _ (run_mulRWP _ hs hK hN hx hy)

/-- `u 0 := digitRW N K i (s (u 1))`, the digit `i = |s (u 2)|`. -/
theorem law_digitRWP_map {i : ℕ} {u : Fin 31 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ j : Fin 31, 5 ≤ j.val → s (u j) = []) (hi : (s (u 2)).length = i)
    (hK : (s (u 3)).length = K) (hN : (s (u 4)).length = N) (hw : (s (u 1)).length = N * K) :
    law (map u digitRWP) s = PMF.pure (Function.update s (u 0) (digitRW N K i (s (u 1)))) :=
  law_map_eq_update hu _ noGrow_digitRWP s 0 _ (run_digitRWP _ hs hi hK hN hw)

/-- `u 0 := monoW N K j (s (u 1))`, `j = |s (u 2)|`; template `u 5` of length `N · K`. -/
theorem law_monoWP_map {j : ℕ} {u : Fin 12 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 12, 6 ≤ i.val → s (u i) = []) (hv : (s (u 1)).length = K)
    (hj : (s (u 2)).length = j) (hK : (s (u 3)).length = K) (hN : (s (u 4)).length = N)
    (hNK : (s (u 5)).length = N * K) :
    law (map u monoWP) s = PMF.pure (Function.update s (u 0) (monoW N K j (s (u 1)))) :=
  law_map_eq_update hu _ noGrow_monoWP s 0 _ (run_monoWP _ hs hv hj hK hN hNK)

/-- `u 0 := constW N K (s (u 1))` (tape `u 2` blank). -/
theorem law_constWP_map {u : Fin 12 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 12, 6 ≤ i.val → s (u i) = []) (hv : (s (u 1)).length = K)
    (h2 : s (u 2) = []) (hK : (s (u 3)).length = K) (hN : (s (u 4)).length = N)
    (hNK : (s (u 5)).length = N * K) :
    law (map u monoWP) s = PMF.pure (Function.update s (u 0) (constW N K (s (u 1)))) :=
  law_map_eq_update hu _ noGrow_monoWP s 0 _ (run_monoWP_const _ hs hv h2 hK hN hNK)

/-- `u 0 := matMulW N K m n l (s (u 1)) (s (u 2))`; templates `u 3` … `u 9` of lengths `K`, `N`,
`N · K`, `m`, `n`, `l`, `m · l · N · K`. -/
theorem law_matMulP_map {m n l : ℕ} {u : Fin 59 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 59, 10 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hNK : (s (u 5)).length = N * K) (hm : (s (u 6)).length = m)
    (hn : (s (u 7)).length = n) (hl : (s (u 8)).length = l)
    (hO : (s (u 9)).length = m * l * (N * K)) (hx : (s (u 1)).length = m * n * (N * K))
    (hy : (s (u 2)).length = n * l * (N * K)) :
    law (map u matMulP) s =
      PMF.pure (Function.update s (u 0) (matMulW N K m n l (s (u 1)) (s (u 2)))) :=
  law_map_eq_update hu _ noGrow_matMulP s 0 _ (run_matMulP _ hs hK hN hNK hm hn hl hO hx hy)

/-- `u 0 := ginvW N K k' (s (u 1))`; templates `u 2` … `u 5` of lengths `K`, `2k' · N`, `k'`,
`2k' · 2k' · N · K`. -/
theorem law_ginvP_map {k' : ℕ} {u : Fin 35 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 35, 6 ≤ i.val → s (u i) = []) (hK : (s (u 2)).length = K)
    (hB : (s (u 3)).length = 2 * k' * N) (hk : (s (u 4)).length = k')
    (hO : (s (u 5)).length = 2 * k' * (2 * k' * (N * K)))
    (hb : (s (u 1)).length = 2 * k' * (N * K)) :
    law (map u ginvP) s = PMF.pure (Function.update s (u 0) (ginvW N K k' (s (u 1)))) :=
  law_map_eq_update hu _ noGrow_ginvP s 0 _ (run_ginvP _ hs hK hB hk hO hb)

/-- `u 0 := gadW N K k'`; templates `u 1` … `u 5` of lengths `K`, `N`, `N · K`, `k'`,
`2k' · N · K`. -/
theorem law_gadP_map {k' : ℕ} {u : Fin 21 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 21, 6 ≤ i.val → s (u i) = []) (hK : (s (u 1)).length = K)
    (hN : (s (u 2)).length = N) (hNK : (s (u 3)).length = N * K) (hk : (s (u 4)).length = k')
    (hO : (s (u 5)).length = 2 * k' * (N * K)) :
    law (map u gadP) s = PMF.pure (Function.update s (u 0) (gadW N K k')) :=
  law_map_eq_update hu _ noGrow_gadP s 0 _ (run_gadP _ hs hK hN hNK hk hO)

/-- `u 0 := nandPKW N K k' (s (u 1)) (s (u 2))`; templates `u 3` … `u 11` of lengths `K`, `N`,
`N · K`, `k'`, `2k'`, `1`, `2k' · N`, `2k' · N · K`, `2k' · 2k' · N · K`. -/
theorem law_nandP_map {k' : ℕ} {u : Fin 65 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 65, 12 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hNK : (s (u 5)).length = N * K) (hk : (s (u 6)).length = k')
    (h2k : (s (u 7)).length = 2 * k') (h1 : (s (u 8)).length = 1)
    (hB : (s (u 9)).length = 2 * k' * N) (hRow : (s (u 10)).length = 2 * k' * (N * K))
    (hSq : (s (u 11)).length = 2 * k' * (2 * k' * (N * K)))
    (ha : (s (u 1)).length = 2 * k' * (N * K)) (hb : (s (u 2)).length = 2 * k' * (N * K)) :
    law (map u nandP) s = PMF.pure (Function.update s (u 0) (nandPKW N K k' (s (u 1)) (s (u 2)))) :=
  law_map_eq_update hu _ noGrow_nandP s 0 _
    (run_nandP _ hs hK hN hNK hk h2k h1 hB hRow hSq ha hb)

end Placed

end Prog

end SigabaNeo.Tape
