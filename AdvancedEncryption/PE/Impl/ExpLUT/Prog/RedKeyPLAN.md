# `keyP` of the reduction (`KGsim` on the VM) — design note (package G2, item 5)

Goal: a component `keyP : XProg (R + 2)` of `RawComps Dc kb L impl χfl` with

* `wf_key : keyP.WF`;
* `law_key : ∀ σ C, Ok σ → XProg.law keyP (io2 ((rawEnc D).enc σ) C []) =
     (KGsim D kb L (rawF D σ) C).map fun sk => io2 sk [] []`
  (`spS … .key σ C = KGsim D kb L (rawF D σ) C` by `comap`, `AH/RedChain.lean`);
* `len_key : XProg.lenBoundT keyP (io2 (sigBound cd W) L 0) ≤ io2 Lk 0 0` (`K₀ = L = predLen`);
* an explicit bound on `XProg.timeBoundT keyP (io2 (sigBound cd W) L 0)` at `Dc` (`≤ 2^370`).

## What `KGsim` computes (σ = rawF s, s = (x, i, B2, H2, d2, fl, zr))

1. `|C| > L` → `[]`. `|C| ≤ L`, `¬ ValidC C` → `skEnc (mpk, 0)`.
2. `(mpk, ct) = view2 M wSt (redPub i B2 H2 d2) (attrN x) zr (redCore i B2 H2 d2) fl` (`redView`).
3. `F = bpOf (progOf C)`, `A_F = keyPK M mpk F` (EvalPK — **same as the real KeyGen**).
4. `R̂_F = simKey M mpk F ct (attrN x) (progOf zr)` = `simEval F (evalPub M mpk) (evalData M mpk ct)
   x (simFreshOf M (progOf zr))`: the EvalPK recursion lifted to pairs `(A, R̂)`
   (`simMul`, `simAut`/`simPerm`, `simLut`, `SimEval.lean`).
5. `X = simX M (h1Of mpk) A_F R̂_F` (`vRounds`: `V₁ = (−R̂_F; I)`, `vStep` along the binary basis).
6. one box try (`keyLaw`): `p ← Big`, `y = keyTarget mpk − pubShort p`, `z = gadDec y`,
   `x' = p − T_sim z` with `T_sim z = X *ᵥ gadDec (pubZ z − gadZ z)`, accept iff `x' ∈ Small`;
   output `skEnc (mpk, keyOfOutput …)`.

Steps 1, 3, 6-without-correction and the output are **the real KeyGen** (`Prog/KeyCore.lean`
`program`, `Prog/KeyAccept.lean` `tryKeyC`): only the correction (`Prog/KeyCorrection.lean`
`correctionC`, real trapdoor in register 16) and the inputs (raw secret instead of `msk`) change.

## Sizes at `Dc` (K = 2^16, N = 2^24, b = 22, m̄ ≈ 2^41.6)

* ring word `N K = 2^40` bits; `|Col τ| = 2^17`; `|LCol| = W(m̄ + |J| 2τ) ≈ 2^63.6`;
* a `SimMat` has `≈ 2^80.6` ring entries (`2^120.6` bits); `X` has `|PIdx| · W τ ≈ 2^101.6` entries;
* `simKey`: `16` steps × `W b / 2` `simAut`s (bit chains, as F3's `lutPK`) × one
  `SimMat · G⁻¹(·)` (`2^97.6` ring products) ⇒ `≈ 2^127` ring ops; with MVM per-instruction cost
  linear in the touched registers (`≤ 2^122` bits) the VM time is `≈ 2^250 ≪ 2^370`.
* `X`: `W` `vStep`s via bit chains (`≤ b` each, `2^97.6` ring ops each), `≈ 2^125`; the
  correction `X *ᵥ u`: `2^101.6` products. Everything fits `2^370` with room for tape overheads.

## VM register layout (MVM, 64 registers; routines' scratch `29 … 63` as in F3)

Kept from the real KeyGen try (so `keyDigitsC`, `assembleC`, `acceptC` are reused verbatim):
`8` = `matL A_F`, `9` = candidate `p`, `14` = `mpkEnc mpk`, `17` = `z`, `18` = corrected `x'`,
`19` = key, `rB1`, `rZ` templates. **Register `16`**, the real trapdoor's register (never written
by `keyDigitsC`: `keyDigitsC_frame`), holds the **rows of `X`** (`encL` of the row-major list,
rows in `Enum.list` order of `PIdx`, entries in `Enum.list` order of `ZIdx`).
New: register `20` = `u = gadDec (pubZ z − gadZ z)` (queue), `21`/`22` = unary templates of
`|ZIdx|`/`|PIdx|` (set inside the try); the `u` routine uses `10–13` and F3's scratch (`0–7`,
`23–28` = `rCK rU rZq rY rDqn rDq`, `39`, `49–55`). The simulation phases (modules 5–6) run before
the try, so all registers except `8`, `14`, `16` (and the coins) are free for them.

## Modules (all new, `Prog/RedKey*.lean`)

1. **`RedKeyMath`** (math, generic over `Setting`): streaming forms used by the VM code —
   `simTrap_apply` (`T_sim z q = Σ_ic X q ic · u ic`), `pubZ_sub_gadZ_apply` (row `i`:
   `Σ_c (σ_i(B⁽¹⁾_c) − g_c) z(i,c)`), `vChain`/`vRounds_eq_vChain` (vRounds = index-carrying bit
   chain, as `roundsPK_eq_bitChain`), `simTrap_rows` (`T_sim z = Σ_j Σ_c V_j[·,(0,c)] u(j,c)`).
   **Done.**
2. **`RedKeyMatVec`** (VM, generic over `N K`): `mvSubC` — `18 := [p_q − Σ_c X_{q,c} u_c]_q` from
   `9` (`p`), `16` (rows of `X`), `20` (`u`), counters `21`/`22`; `exec_mvSubC`,
   `exec_mvSubC_enum`. **Done.**
3. `RedKeyURow` (generic `N K`) + `RedKeyU` (`D`): `u` from `z` (reg 17) and `mpk` (reg 14):
   ring one (`ringOneC`, reg 7), the gadget row of `B⁽¹⁾` (reg 10, `bRowC`: public-key prefix +
   `gatherC`), per row `i` `uRowC K (rowExponent D i)` (`gadRecC` → reg 13, `autQC` + `ipC` → reg
   12; z queue in reg 11), then F3's `decRowsC`. Scratch: `0–7, 10–13, 23–28, 39, 49–55`.
   **Done**: `uOk_uC : UOk D (uC D)` (`2 ≤ K`).
4. `RedKeyTry` (VM, `D`): parametrized by the `u` routine (`UOk` contract):
   `simCorrectionC uC = uC ; natC 21 ; natC 22 ; mvSubC`, `simProposalC = keyDigitsC ; cp 17 rDq ;
   simCorrectionC`, `simTryKeyC = simProposalC ; assembleC ; acceptC`; `exec_simTryKeyC`,
   `map_uniform_simAttemptOutput`, `map_coins_exec_simTryKeyC(_Dc)`. **Done**; with module 3:
   `map_coins_exec_simTryKeyC_uC_Dc` (in `RedKeyU`).
5. `RedKeyX` (VM, `D`): `simX` rows into register `16` from `R̂_F` (reg 21) and `A_F` (reg 8):
   index-carrying bit chain of `vStep` (`V ↦ V · G̃⁻¹(σ_j(H_a⁽¹⁾)) − J̃_{η_{j,a}}`, `ginvMulC`-like
   kernel on queues of rows; `J̃` = add `−1` at one known position) and a transposition into row
   order. Spec `exec_simXC : w' 16 = encL (rows (simX M (h1Of mpk) A_F R̂))`.
6. `RedKeySim*` (VM, `D`): `simKey` — the EvalPK loop of F3 (`KeyEval*`, `KeyLut`) with every
   public matrix `A` paired with its `R̂` queue: `simMulC` (Lemma 10.3: `simS + R̂ G⁻¹(C) + μ Ẑ`),
   `simPermC` (row permutation `rotC` + `σ`), `simAutC`, `simSmulC` (`R̂ G⁻¹(αG)`), the `j` loop of
   `simLut` with the same bit counter as `KeyLut`; fresh matrices `jβ`/`jη` from `zr` bits and
   `B̄`. Spec: `w' 21 = encL (rows (simKey M mpk F ct x (progOf zr)))`.
7. `RedKeyView` (VM, `D`): `mpkEnc`/`evalData` of `view2` from `rawEnc s` — **shared with
   `pubP`/`chalP` (item 4 of G2)**; must leave `mpkEnc mpk` in 14 and the ciphertext data needed by
   `evalData` (the digits of `C^in_t`, `C_{g_t}`) in fixed registers.
8. `RedKeyFront`/`RedKeyMachine`: `XProg (R + 2)` front end — input `io2 (rawEnc s) C []`,
   length guard `|C| ≤ L` (else `[]`), `ValidC` (else `skEnc (mpk, 0)`), `KeyEvalPrepare` (F3) on
   register 14, the sampler `sampleP` (F3), `simTryKeyC`, output `skEnc` unframed on tape 0
   (`io2`, not `encodeTuple`), all scratch cleared. `wf_keyP`, `law_keyP`.
9. `RedKeyTime*`: runtime certificates — reuse `KeyTime*` (`Cert`, layout, `RingInputs`) for the
   reused phases; new certificates for 2–7; generic over `D`, specialized at `Dc` last.

## Interface theorems (targets)

* `exec_mvSubC` (module 2), `exec_uC` (3), `exec_simTryKeyC`, `map_coins_exec_simTryKeyC` (4),
  `exec_simXC` (5), `exec_simKeyC` (6), `exec_viewC` (7), then
* `law_keyP (s : RawSec Dc) (C) : XProg.law keyP (io2 ((rawEnc Dc).enc s) C []) =
   (KGsim Dc kbDc L (rawF Dc s) C).map fun sk => io2 sk [] []`,
* `len_keyP`, `time_keyP_Dc : XProg.timeBoundT keyP (io2 (sigBound …) L 0) ≤ 2 ^ 370`.

## Status (2026-11-25, first session)

**Done and building** (`lake build PE.Impl.ExpLUT.Prog.RedKeyU` builds all five; axioms of every
theorem: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`native_decide`):
`RedKeyMath`, `RedKeyMatVec`, `RedKeyURow`, `RedKeyTry`, `RedKeyU` — modules 1–4. Headline:

* `map_coins_exec_simTryKeyC_uC_Dc`: for every `mpk`, `F`, `R̂` and every family of VM states
  `states p` satisfying `SimTryReady mpk F (simX (helperMap Dc) (h1Of mpk) (keyPK … mpk F) R̂) p`
  (registers `14` = `mpkEnc mpk`, `8` = `matL A_F`, `16` = `rowsWord X`, `9` = candidate `p`,
  `rB1`, `rZ`), fair coins + `coinDec` + `simTryKeyC Dc (uC Dc) Bk rSmall` give exactly
  `((keyLaw kbDc.Big kbDc.Small kbDc.hBig gadDec M mpk F (simTrap M mpk F R̂)).map keyOfOutput)
   .map (keyEnc Dc).enc` — i.e. the box try of `redKeyLaw` once `X` is in register `16`.

## Status (2026-11-25, second session): module 5 done, module 6 math (6a) and transposition (6c) done

**Done and building** (`lake build PE.Impl.ExpLUT.Prog.RedKeyX`; axioms `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`/`native_decide`): module 5, four files.

* `RedKeyXRow` (generic `N K`): the **row kernel** `xRowC`. Lemma 11's `V_j` act row by row:
  a row `v` of `V_j` goes to `v · G̃⁻¹(σ_j(H_a⁽¹⁾)) − (J̃_η)_ℓ`, and `(J̃_η)_ℓ` is `0` or a unit
  row. For one start row `v₀` (`rxV0`), tag (`rxTag`) and correction row `e` (`rxE`), `xRowC`
  builds the rows `v_j`, `j < 2^b`, by the doubling recursion of `vRounds` (round `t`: `Y :=
  H_{(t,0)}` popped from the helper queue, then `2^t` steps `v ↦ row 0 of mask(v)·G⁻¹(Y)`
  (`ginvMulC`), minus `e` when `0^t 1 0^j = tag` (`eqb` + `xsubC`), `Y := σ_g(Y)` (`aStep`)),
  and appends the first `K` entries of every `v_j` to register `16` (`exec_xRowC`; output
  `xOut g Hs tag e v₀ b`). No `bitChain`/exponent arithmetic: `σ_{idx j} = σ_g^j` incrementally.
* `RedKeyXDrive` (generic): the drivers over all rows of `X`: part A (`Ā` rows, start `−R̂_ℓ`
  via `xNegC`, tag `11`), part B (`η` rows, nested loops `i`/`s`/`d`/`c'`, tag `0^s 1 0^i` for
  `d = 0`, unit rows `e_{c'}` via `xEInit`/`xENext`), part C (`V.2` rows, start `e_r`);
  `simXC = clr 16; A; B; C`, `exec_simXC_gen`, `wf_simXC`, `simXC_writes` (writes only
  registers `< 57`, never `8`, `14`, the inputs).
* `RedKeyXMath` (at `D`): `vRounds_fst_row`, `vRounds_snd_row` (rows of `V_j` = `xRow`),
  `jη_row`, `mul_ginvTop_row`, **`simX_row`**, **`rowsWord_simX`**.
* `RedKeyX` (at `D`): order bookkeeping (`rowsWord_rh`, `rowsWord_simX_drive`, `enumB_flatMap`),
  **`exec_simXC`**: from `XIn (gD D) D.b (xHs D mpk) (xHi D mpk) w` (helpers `rxH = 15`,
  `rxTb = 17` unary `b`, `rxTru = 19` `[true]`, `rxFal = 20` `[false]`, `rxW = 21` length `2^b`,
  `rKc = 31` length `gD D`, `MulTmpl`), `rxRh = 24` = `encL (rowsWord R̂)` (row-major over
  `LCol × Col`), `rxTs = 27` of length `2^b · m̄`, `rxOne = 25` = `encRM 1`:
  `exec simXC w 16 = encL (rowsWord (simX (helperMap D) (h1Of mpk) A_F R̂))` — exactly
  `SimTryReady.rows`. `xHL_eq`: the helper queue is `(Enum Jh).flatMap (matL ∘ mpk.H)`, i.e. the
  `H` field of `mpkEnc mpk` (module 8 extracts it from register `14`).

**Remaining** (in order):

* **6 `RedKeySim*`**: `R̂_F = simKey …` — **done** (fourth session; see below).
  * **6a `RedKeySimSlab` — done** (builds, standard axioms). Rows of a simulation matrix are
    `lcol i r`, `i < W`, `r ∈ Rest = Wb ⊕ (J × Col τ)`; the **slab** `r` (`slab Rh r : Fin W →
    Col τ → R`) is closed under the whole propagation: `slab_simMul` (row by row, `slabMul`),
    `slab_simPerm` (rows rotated by `g^e` + `σ`, `slabPerm`), `slab_simAut`, `slab_simRounds`,
    `slab_simLut`, `slab_simEvalAt`, **`slab_simKey`**: `slab (simKey M mpk F ct x P) r =
    slabEvalAt F (evalPub M mpk) (evalData M mpk ct) x (slabFreshOf M P r) F.T`, with explicit
    fresh slabs (`slabβ`: one row `i₀` = `Z_w` on `inl w`; `slabη`: one unit row on `inr (k, c')`
    when `k` matches). **`slabChain_eq`**: `slabRounds` (and `roundsPK`) are the index-carrying
    *paired* bit chain `slabChainStep` (state `(k, A, s)`, step at bit `s`: `k += 2^s`,
    `A := autPK (kf s) …`, `s := slabAut (2^s) … A (σ_{idx k} μ) …`), and `slabLut_eq_chain`,
    `lutPK_eq_chain`: the table is `Σ_{j<W}` over the chains — exactly F3's `chainC`/`jLoopK`
    shape (`KeyLut`), so the VM pairs the public chain with the slab chain.
  * **6b (VM, to do)**: an outer loop over the slabs `r ∈ Rest` (`m̄` slabs `inl w`, then
    `2b · 2K` slabs `inr (k, c')`); per slab a copy of F3's `evalC` (`KeyLut.stepK`, `chainC`,
    `jLoopK`) with the slab queue (`W` rows of `2K` words) carried alongside `rA`:
    - before the `j` loop of step `i`: `s := slabMul(A_i, C^in_{read i}, X^{state_i}, s, Zin, Rin)`
      — row by row; the `Rin`/`Zin`/`R0` slabs are `slabβ row0 …` (only row `0` of `inl w` slabs,
      the bits of `zr` at `w`: `progOf`), so the digit term is one `mulPKm`-type row (the row
      `w` of `P.Rin t ·`) and `C^in_t = cinMat (mpk.a t) (ct.cinBot t)` comes from `view2`;
    - in `chainC`'s `autStep` (bit `s` of `j`): `s := slabAut(2^s, …)` = `sh ·ᵥ G⁻¹(A')`
      (`A' = mulPK(σ(A), A^aut_s)`, already in `rMOut` inside `autPKC`; `sh = slabη row0 (fwd s)`,
      nonzero only on the slabs `inr ((s,0), c')`) `+ slabMul(σ(A), gcAut(H_{inv s}, h_{inv s}),
      σ_{idx k} μ, slabPerm (2^s) s, slabη (rowT s) (inv s), slabβ (rowT s) (Raut s ·))`;
      `slabPerm` = rotate the row queue right by `2^s` rows (`mv` of `(W − 2^s)·2K` words) and
      `σ_g^{2^s}` entrywise (as `rP`); the payload `μ_k = σ_{idx k}(μ)` is carried as one ring word
      and stepped by `σ_g^{2^s}` with the chain;
    - the accumulation `rAccL += A_j G⁻¹(α_j G)` gets a slab twin `Σ_j s_j ·ᵥ G⁻¹(α_j G)` (rows
      paired as `2 × 2K` matrices for `ginvMulC` with `gM α_j`, or row-masked as in module 5);
    - after the `16` steps, the slab is appended to an output queue (**slab-major**); a final VM
      transposition turns it into `rowsWord R̂` (row-major over `LCol`: the `inl` part, then the
      `inr` part, each `i`-major) — `W` passes over the queue, `≈ 2^{142}` steps — for module 5's
      `rxRh`.
    **6c done** (`RedKeySimT`, generic; `RedKeySimTD`, at `D`): the transposition `transC`
    (`exec_transC`: `n` slabs of `W` rows, slab-major in `rtQ = 0`, appended row-major to
    `rxRh = 24`; templates `rtR = 1` of `(W − 1)·2K` words, `rtN = 5` unary `n`, `rtW = 6` unary
    `W`) and **`rowsWord_trans`**: `rowsWord R̂ = transOut (rowsInl R̂) W m̄ ++ transOut (rowsInr R̂)
    W |J × Col τ|`, `rowsInl_slab`/`rowsInr_slab`: these rows are the rows of `slab R̂ (inl w)` /
    `slab R̂ (inr ρ)` (`ρ` in `Enum` order). So 6b must leave the `Ā` slabs (in `w` order), run
    `transC` (`n = m̄`), then the `η` slabs, `transC` again (`n = 2b · 2K`), into `rxRh`.
    Generic-first as in modules 4–5 (`N K`, abstract programs), `D` last; math bridges at `D`:
    `mulPK_eq_mulPKm`/`mul_ginv_eq`/`autMat_eq` (`KeyVM`) for the public side, row versions for the
    slab side (as `RedKeyXMath.mul_ginvTop_row`). Estimated size: a paired copy of `KeyLut`
    (`~1200` lines) + slab kernels (`~800`) + bridges (`~500`).
  * **6b in progress (third session)** — generic VM, slabs as *lists of rows* (`seRows L =
    L.flatMap vecL`), the evaluator paired with F3's inside F3's register layout (F3's `rA = 4` is
    the chain's public matrix `seA` during the `j` loop; `seMu = 2`, `seSl = 13`, `seSc = 16` (the
    current slab / the chain start), `seAcc = 17` (the slab accumulator); one per-bit record
    stream `seSW = 1` / working copy `rSs = 12`, record template `seTRec = 26`; kernels use the
    library scratch `29, 41, 42, 45 … 48`).
    - **`RedKeySimEK` — done** (builds, standard axioms): kernels `seAutC` (`σ_g^{|rP|}` on all
      entries), `seRotC` (`List.rotate`), `seMapC` (rows `· G⁻¹(Y)`, `seGRow v Y = ginvMulm
      (fun _ => v) Y 0`), `seAddHC`/`seAdd0C`/`seAddTC` (row `0` / row `|rPw2|` `+= v`,
      `seAddAt = List.modify`), `seScaleC`, `seSumC`, each with `exec_*`.
    - **`RedKeySimEC` — done** (builds): the per-bit data `SeBits` (`gc`, `ad`, `crow`, `Aa`,
      `hrow`, `Hf`), one record per bit (`seRec`: `gc ++ ad ++ crow ++ Aa ++ hrow ++ Hf`), the
      generic step `seStep g D t (A, μ, L)` (= `slabChainStep` up to the bridges: σ + rotate right
      `2^t` + `·G⁻¹(C_t)`, row `2^t += (σA ⋆ ad_t)₀ + σ^{2^t}(μ)·crow_t`, row `0 += hrow_t·G⁻¹(A')`,
      `A ↦ H_{g_t} G⁻¹(A')`), its code `seAutStep` (phases `seSA … seSG`), **`exec_seAutStep`**,
      the chain `seChainC`, **`exec_seChainC`**: `(seA, seMu, seSl) = bitChain (seStep g D) b j
      (A, μ, L)` (reads `SeChainIn`: `seSW`, `rTb`, `rBit1`, `seTRec`, `rTW`, `rKc`, templates).
    - **`RedKeySimEJ` — done** (builds): `bitChain_seStep_fst` (the public part of the paired
      chain is F3's `chainM`), the `j` body `seJBody cf = cf ; seJRest` (chain from `(rB, pu,
      seSc)`, `pu` = head word of `rAinS`, read not consumed; `seAcc += [v·G⁻¹(α_j G) | v ∈
      slab_j]`), **`exec_seJLoop`**: `rAccL = accM …` (F3) and `seAcc = seTab cv g D b B pu μ0 Lc n`.
    - **`RedKeySimES` — done** (builds): the slab pre `seLc A Cin pz z rd L` (= `slabMul` on
      rows: rows `·G⁻¹(C^in)`, row `0 += pz·z + (A ⋆ rd)₀`), the per-step record `seStepRec`
      (`adL A^in_i ++ matL C^in_i ++ [pz_i] ++ vecL z_i ++ adL rd_i ++ [pu_i]` in `rAinS`),
      `seStepK cf`, **`exec_seStepK`**, `seEvalC` (`T = 16`), **`exec_seEvalC`**: `rA =
      evalVM …` (F3's public `EvalPK`, unchanged) and `seSc = seEvalVM cvs g D b μ0 n Ain A0 Cin pz
      pu z rd L0 16` (reads `SeStepIn`: `SeChainIn` + `rOne`, `rMu0`, `rT4K`, `rTtab`; `CoefIn`;
      `rT15`; `rCs` = predicate word). Axioms of all: `propext`, `Classical.choice`, `Quot.sound`.
    - **`RedKeySimEMath` — started** (builds, standard axioms), bridges at `D`: `seSigIdx`
      (`σ_{g^m} = σ_g^[m]`), `seSlabL s = (List.finRange W).map (s ·)`, `seSlabL_ginv`,
      `seSlabL_add`, `seSlabL_addRow` (`seAddAt`), `rotEquiv_symm_val`, **`seSlabL_perm`**
      (`slabPerm (2^t)` = `(map σ^{2^t}).rotate (W − 2^t)`), **`seSlabL_slabMul`** (`slabMul` with
      `Z`, `R^in` on row `0` = `seLc`), **`seSlabL_slabAut`** (`slabAut (2^t)` with `R_H` on row
      `0`, `R_C`, `R^aut` on `rowT t` = the slab part of `seStep`, `gc t = gcAut …`, `ad = fun d _
      => ρ d`, `crow = cr`, `hrow = h`).
    - **6b remaining items — done (fourth session)**, see "Status (fourth session)" below.
* **7 `RedKeyView`**: `mpk`, `ct` of `view2` from `rawEnc s` (shared with `pubP`/`chalP`).
  The parallel package's codes are **`RingVM`** code (200 registers, `ringIO` handlers, 247
  tapes), not MVM: `pubC D` writes `(mpkEnc D).enc (pubK D σ)` (`pubK D σ = (redView D (rawF D
  σ)).1`, `RedPubPMath.pubWord_eq`, field words `wB ++ wH ++ wa ++ wA0 ++ wAin ++ wAaut ++ wd`),
  `chalC D` the words of `chalCT D σ μ` (`RedChalCode`). Reuse at the `XProg` level: run
  `pubC`/`chalC` as their own (framed) phases and hand their output words to the MVM key machine
  (register `14` = `mpkEnc mpk`; the `ct` fields `simKey` needs: `cinBot`, the helpers `h`, for
  `evalData`), rather than porting them to MVM. The helper queue of module 5 (`rxH`) is the `wH`
  field (`RedKeyX.xHL_eq`).
* **8 front/machine**: input `io2 (rawEnc s) C []`, guards (`|C| ≤ L`, `ValidC`), F3's
  `keyPrepareC` part for `A_F` (register `8`), modules 5–7, F3's `sampleP` + candidate decode
  (copy `candidateTryC` with `simTryKeyC`), output `skEnc` unframed, cleanup; `wf_keyP`,
  `law_keyP` against `KGsim` (via `redKeyLaw` = `keyLaw … (simTrap … (simKey …))`).
* **9 time/length**: certificates for the new routines (`mvSubC`, `uC`, 5, 6, 7) in the style of
  `KeyTime*`; reuse F3's for `keyDigitsC`, `assembleC`, `acceptC`, sampler; `≤ 2^370` at `Dc`.
  Target now `≤ 2^450` in total. Costs of the new code (MVM: per instruction linear in the touched
  registers): module 5 runs `|PIdx| ≈ 2^{63.6}` row kernels, each `b` rounds of `≤ 2^{22}` steps
  (`ginvMulC` + `autMatC` on `2 × 2K` matrices, `≈ 2^{40}` ring ops) with registers `≤ 2^{80}` bits
  except `16` (`≤ 2^{141}` bits, only appended): `≲ 2^{130}` instructions, `≲ 2^{275}` steps with
  the crude bound "every register `≤ 2^{142}` bits". The KeyTime framework certifies with bound
  vectors (`Cert`, `rep_family` for growing registers, `layout` envelopes); a crude uniform envelope
  (`layout` with `M = 2^{142}`, `rep_fixed`) fails for `app` on `16`/`rxQ` — use `rep_family`
  with the output register's bound as a function of the round.

## Status (2026-11-25, fourth session): module 6 done

**Done and building** (`lake build PE.Impl.ExpLUT.Prog.RedKeySimE` builds all; axioms of every
theorem: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`native_decide`; the new modules
are **not yet in the aggregator** `ExpLUT.lean`: add `RedKeySimEB`, `RedKeySimEL`, `RedKeySimEP`,
`RedKeySimE`). Four new files:

* **`RedKeySimEB`** (at `D`, bridges on full states): `SeForms Q hr cr ρ` (helper slabs supported
  on the rows `0` / `2^t`), `seBitsOf P h hr cr ρ : SeBits` (`gc t = gcAut (idx 2^t) (P.Hi t)
  (h.hi t)`, `ad t = ρ t`, `crow = cr`, `Aa = P.Aaut`, `hrow = hr`, `Hf = P.Hf`), the state map
  `seStOf μ (k, A, s) = (A, σ_g^k μ, seSlabL s)`; **`seStep_slabChainStep`** (one step),
  **`bitChain_seStep_slab`** (chains, `t ≤ b`), **`seSlabL_slabLut`** (`slabLut = seTab … (2^b)`
  given `coef j = cv (σ_g^j μ₀)`), **`seSlabL_slabEvalAt`** (`F = bpOf (progOf C)`, `b = 22`:
  `slabEvalAt … i = seEvalVM (cvsK C) … i`, `i ≤ 16`; public side via F3's `evalPKAt_eq`), the
  fresh slabs of `slabFreshOf` are of the supported forms (`seForms_slabFreshOf`,
  `seFormsIn_slabFreshOf`; the rows are `seHrOf/seCrOf/seRhoOf/seZvOf/seRvOf P r` — extracted rows
  of `slabFreshOf (helperMap D) P r`), and **`seSlabL_simKey`**: `seSlabL (slab (simKey (helperMap
  D) mpk (bpOf (progOf C)) ct x P) r) = seEvalVM (cvsK D C) (gD D) (seBitsOf …) b X⁻¹ (2^b) (AinK
  mpk) A₀ (C^in_{read i}) (X^{z_i}) (X^{z_i + w x_{read i}}) (z-rows) (R^in-rows) (seSlabL (slabβ
  row0 R₀ r)) 16`.
* **`RedKeySimEL`** (generic VM): the MVM has no free register around `seEvalC` (it writes or reads
  every register except its inputs), so **`seEvalC2`** = `seEvalC` with the 15-step counter built
  from `rTe ++ rBit1` (frees `rT15 = 28`, the slab counter `seLoopC`); **`exec_seEvalC2`** (with a
  trailing `rest` in `rAinS`; final `rAinS = rest`, `rCs = C.drop (16 tl)`); `sePopC`/`sePopsC`
  (pop chunks of a stream through a temporary, `exec_sePopsC`); the packet `sePacket D b L0 A0 Ain
  Cin pz pu z rd = seStream D [0,b) ++ seRows L0 ++ matL A0 ++ seStepsL … [0,16)` and its loader
  `seLoadC` (`exec_seLoadC`); `seSlabC = seLoadC ; seEvalC2 ; app rAinS seSc` and
  **`exec_seLoopKC`**: `rep 28 seSlabC` consumes the packets at the head of `rAinS` and appends the
  output slabs at its tail (slab-major), `rCs` advances by `16 tl` per slab, the constants
  `SeConst` (registers `18 … 27`, `rKc`, `57 … 63`) are kept.
* **`RedKeySimEP`** (generic VM): `sePostC` = split (first `|rCs| · W` rows into `8`, the rest into
  `9`), `transC` with `n = |rCs|` into `rxRh` (`rtR` rebuilt by `seRtC`), then `transC` with
  `n = b · 2 · 2K` (`seNBC`: unary from `rTb`, `rT2K`); **`exec_sePostC`**: `rxRh = encL (transOut A
  W nA ++ transOut B W (b·2·2K))`.
* **`RedKeySimE`** (at `D`): `seRestL` (slabs `inl w`, `w < m̄`, then `inr ρ`, `Enum` order),
  `sePkOf mpk C ct x P r` (the packet of slab `r`), `progOf_append` (`ValidC C →
  progOf (C ++ u) = progOf C`), `simKeyC = seLoopKC ; sePostC`, `wf_simKeyC`, and
  **`exec_simKeyC`** (`D.b = 22`, `D.b < D.K`): `SimKeyIn D mpk C ct x P Cf w →
  exec simKeyC w rxRh = encL (rowsWord (simKey (helperMap D) mpk (bpOf (progOf C)) ct x P))`;
  **`exec_simKeyXC`**: with a set-up code `setX` satisfying `SetXOk setX mpk (exec simKeyC w)`
  (module 5's `XIn`, `rxTs`, `rxOne` established, `rxRh` kept), `simKeyC ; setX ; simXC` leaves
  `encL (rowsWord (simX (helperMap D) (h1Of mpk) A_F (simKey …)))` in register `16`.

**Input contract `SimKeyIn`** (for modules 7/8; see the header of `RedKeySimE.lean`):
`SeConst w (gD D) b (2^b) tlK X⁻¹ (xcK D)` (constants in `18 … 27`, `rKc`, templates `57 … 63`);
`rAinS = encL (seRestL.flatMap (sePkOf mpk C ct x P))` — **the payloads `pz_i = X^{z_i}`,
`pu_i = X^{z_i + w x_{read i}}` (BP states of `F = bpOf (progOf C)` on `x`) are supplied inside the
step records by module 8** (no BP-state routine on the VM); `rCs = Cf` with `Cf.drop (16 tlK k) = C
++ _` for every slab `k < |seRestL|` (`|seRestL|` copies of `C` padded to `16 tlK` bits) and a
final word of length `m̄` (the split counter); `|reg 28| = |seRestL| = m̄ + b·2·2K`; `ValidC C`.
After `simKeyC` only `SeConst`'s registers (except `24 = rxRh`), `rxRh` and the tail of `rCs`
survive — data needed later (helper queue `rxH`, `mpkEnc mpk`, `matL A_F` for register `8`) must be
rebuilt or carried in the tail of `rCs` by module 8 (`SetXOk`).

**Remaining** for module 6: none functionally; module 9 needs time/length certificates for
`simKeyC` (`seEvalC2` ≈ `seEvalC`/F3's `evalC` per slab, `|seRestL| ≈ 2^{41.6}` slabs; packets
`≈ (b · recLen + W·2K + 4K + 16·stepRec)` words each; `rCs` of `|seRestL| · 16 tlK + m̄` bits).

## Status (2026-11-25, fifth session): module 8 top level and back end done; the middle is a contract

**Done and building** (no `sorry`/`native_decide`; axioms `propext`, `Classical.choice`,
`Quot.sound`; **not in the aggregator** — add `RedKeyMTail`, `RedKeyMFront`, `RedKeyMComp`):

* **`RedKeyMTail`** (MVM, `105` tapes): `rkTryC D B r = candidateC ; simTryKeyC (uC)`,
  `rkTailP D B r = sampleP ; compile rkTryC ; compile packKeyC ; post`; `uC_keeps_mpk`,
  `simTryKeyC_keeps_mpk`; the contract **`RkMidReady mpk F R̂ w`** (`14` = `mpkEnc mpk`, `8` =
  `matL A_F`, `16` = `rowsWord (simX M (h1Of mpk) A_F R̂)`); **`law_rkTailP`** /
  **`law_rkTailP_Dc`**: `law (rkTailP Dc Bk rSmall) (enc w) = ((keyLaw … mpk F (simTrap M mpk F
  R̂)).map keyOfOutput).map (inputStore 0 ∘ skEnc (mpk, ·))`; `wf_rkTailP_Dc`.
* **`RedKeyMFront`** (`247` tapes, namespace `…Prog.RedKeyM`):
  - `rkLenLeP n` (`Prog 6`, `|C| ≤ n` flag, copy of `lenEqP`), `rkLeChk`/`rkEqChk` (tests on
    tapes `1 … 6`, flag on tape `2`);
  - `rkLongP` (blank output), `rkInvP = clr ; RedPubP.pubP Dc ; natP 1 2 |keyEnc| ; appT 0 1 2 3`
    (**`law_rkInvP`**: `skEnc (mpk, 0)`);
  - `rkKeyOf vP` (guards + branches), **`law_rkKeyOf`** under `RkValidOk vP` (the valid branch's
    law = `redKeyLaw … .map (io2 (skEnc (mpk, keyOfOutput o)) [] [])`);
  - `rkE : Fin 105 ↪ Fin 247` (tapes `0 … 104`), `rkLift a` (a `105`-store there, rest blank),
    `rkValidP mid = mid ; frame rkE rkTailP`, **`rkValidOk_of_mid`**;
  - **`rkKeyP mid := rkKeyOf (rkValidP mid)`**, **`wf_rkKeyP`** (from `mid.WF`),
    **`law_rkKeyP`** (from `RkMidOk mid`): exactly the `law` field of `Sub.KeyComp`.
* **`RedKeyMComp`** (namespace `AdvancedEncryption.ExpLUT.Sub`): `law_rkKeyP_spR` (the field verbatim, against `spR.key`/`cdR`) and
  **`keyCompOf mid hwf hm Lk hLk hlen htime hsize : Sub.KeyComp`** — then
  `Sub.spec_of_keyComp (keyCompOf …)` is the final statement.

**The one remaining functional obligation — `RkMidOk mid`** (`RedKeyMFront`): a deterministic
`mid : XProg 247` with `mid.WF` such that for every raw secret `σ` and `ValidC C` there is an MVM
state `w` with `mid.law (io2 ((rawEnc Dc).enc σ) C []) = pure (rkLift (enc Dc.N Dc.K w))`
(tapes `105 … 246` blank at the end) and `RkMidReady mpk F R̂ w` for `mpk = (redView Dc (rawF Dc
σ)).1`, `F = bpOf (progOf C)`, `R̂ = simKey (helperMap Dc) mpk F (redView …).2 (rawF Dc σ).1
(ExpLUT.progOf (rawF Dc σ).2.2.1)`.

### Design of `mid` (next sessions)

Tapes: the MVM phases run framed on `0 … 104` (`frame rkE (compile c)`, `law_frame` +
`rkLift_rkE` + `law_compile`); tapes `105 … 246` are free storage for words between phases
(Prog `cp`s; `update (rkLift (enc w)) (rkE (41 + r)) v = rkLift (enc (update w r v))` is the
load/stash lemma to write, cf. `RedIO.enc_update_tWd`).

1. **M1 (RingVM, the `mpk`/`ct` words).** `pubP`/`chalP` (`RedIO.ringIO1`) clear every tape, and
   `preP` overwrites every register tape but `ra`/`rb`, so `C` and the raw secret cannot survive a
   plain call. Plan: a wrapper `ringIOk` = custom `preP` whose template list skips a few *stash*
   registers `rS₁ rS₂ rS₃` (loaded from tapes `2, 3, 4`), `compile c`, custom `postP` copying
   `ro, rS₁, rS₂, rS₃` to tapes `0 … 3`; laws as `law_preP`/`law_ringIO1` (copy). For the codes:
   a generic RingVM lemma **`exec_update_unused`** (`c` never mentions `r` ⇒ `exec c (update w r
   v) = update (exec c w) r v`, by induction on `Code`, ~80 lines; `mentions` decided by `decide`
   on `pubC Dc`/`chalC Dc`, which only use a fraction of the 200 registers). Then
   `exec_pubC`/`chalC`'s spec transfer verbatim. Run `pubC` (word `mpkEnc mpk`) and `chalC` with
   `μ = false` (`chalCT σ false = shiftCT … (redView …).2` differs from `ct` only in `cm`, which
   `evalData` never reads: `evalData M mpk (shiftCT h m ct) = evalData M mpk ct` by `rfl`).
2. **M2 (`A_F`, reuse F3).** `keyPrepareC D` reads the msk word from register `0` and `C` from
   `rCs`: feed it `mskW = mpkEnc mpk ++ 0^{|T part|}` (an msk with a zero trapdoor; its
   `mpk` field is `mpk`) → `14 = mpkEnc mpk`, `8 = matL (keyPK M mpk F)`
   (`exec_keyPrepareC`); stash `8`, `14` to storage tapes (they are destroyed by `simKeyC`).
3. **M3 (packets, the bulk of the remaining work).** Establish `SimKeyIn` (`RedKeySimE`): the
   constants `SeConst`, the slab packets `seRestL.flatMap (sePkOf …)` in `rAinS`, the padded copies
   of `C` in `rCs`, the slab counter. New MVM code: the public parts of a packet (per-bit records
   `gcAut`, `A^aut`, `H_f`, `A₀`, `A^in`, `C^in = cinMat (mpk.a t) (ct.cinBot t)`, payloads
   `X^{z_i}`, `X^{z_i + w x_{read i}}`) once, then per slab `r` the slab rows from `zr`
   (`slabβ row0 R₀ r`, `seHrOf/seCrOf/seRhoOf/seZvOf/seRvOf P r`) — bridges against
   `slabFreshOf`. The BP states `z_i` of `bpOf (progOf C)` on `x = attrN` need a VM routine that
   walks the LUT of `C` (`tabsOf`) — or reuse F3's/Dec's evaluator if one computes states.
4. **M4.** `simKeyC` (`exec_simKeyC`), a `setX` with `SetXOk` (rebuild `xHs`/`xHi` from the
   stashed `mpkEnc mpk`, `RedKeyX.xHL_eq`), `simXC` (`exec_simKeyXC`) → `16`; restore `8`, `14`
   from storage; clear storage tapes → `RkMidReady`.

**Module 9 (certificates)** — what `keyCompOf` needs for `rkKeyP mid`, at input
`io2 (sigBound cdR (WR Dc)) predLen 0`: `lenBoundT ≤ io2 Lk 0 0` with `Lk ≤ 2^125` (the output is
`≤ |skEnc Dc|` bits; all scratch cleared), `timeBoundT ≤ 2^450`, `size ≤ 2^200`. `timeBoundT` of
`rkKeyOf vP` is `time(rkLeChk) + max(time(clr;rkEqChk) + max(time(clr) + time vP, time rkInvP)
+ 1, time rkLongP) + 1`; `rkInvP` reuses `RedPubP.bounds_pubP_Dc`/`size` (input bound `2^101` for
tape 0 — check `sigBound cdR (WR Dc) ≤ 2^101`) plus `natP`/`appT` costs
(`XProg.natP_bounds`); `rkTailP` reuses F3's `KeyTime*` certificates for `sampleP`,
`candidateC`, `keyDigitsC`, `assembleC`, `acceptC`, `packKeyC`, `post`, with new ones for `uC`
and `mvSubC` (module 4); `frame rkE` is free (`timeBoundT_frame`).

## Status (2026-11-25, sixth session): `mid` built; the remaining obligation is the packet stream

**Done and building** (`lake build PE.Impl.ExpLUT.Prog.RedKeyMidPk` builds all five; no
`sorry`/`native_decide`; axioms of every theorem `propext`, `Classical.choice`, `Quot.sound`;
**not in the aggregator** — add `RedKeyMidRing`, `RedKeyMidPub`, `RedKeyMidCode`, `RedKeyMidM`,
`RedKeyMidPk`, all in namespace `AdvancedEncryption.ExpLUT.Prog.RedKeyMid`):

* **`RedKeyMidRing`** (generic `RingVM`): `usesR r c` (the code mentions register `r`),
  **`exec_update_of_usesR`** (`usesR r c = false → exec c (update w r v) = update (exec c w) r v`);
  the stash handler **`ringIOS N K ra rb ro r1 tm c`** = `ringIO1` with three stash register tapes
  `tWd 197/198/199` (= `244/245/246`), parked on the operation-area tapes `10/11/12` while `preP`
  runs (`law_preP_park`, via `law_preP_gen`/`preF_update`); **`law_ringIOS`**:
  `law (ringIOS …) (stash3 (io2 a b []) v₁ v₂ v₃) = pure (stash3 (io2 (exec c (initW1 …) ro) [] [])
  v₁ v₂ v₃)`; `wf_ringIOS`.
* **`RedKeyMidPub`** (M1 at `Dc`): `pub_uses*`/`chal_uses*` (`by decide`: `pubC Dc`, `chalC Dc`
  never mention `197 … 199`), `chalCT_false` (`chalCT σ false = (redView …).2`), **`m1P`**,
  **`law_m1P`**: `law m1P (io2 (rawEnc σ) C []) = pure (m1Store σ C)` — storage tapes
  `tCt = 243` (`ctW σ = ctEnc (redView …).2`), `tMpk = 244` (`mpkW σ`), `tSig = 245`
  (`rawEnc σ`), `tC = 246` (`C`), all else blank; `wf_m1P`.
* **`RedKeyMidCode`** (MVM, register level): **M2** `m2C = natC 6 rB1 |T| ; cp 0 2 ; app 0 6 ;
  keyPrepareC Dc` (msk with the zero trapdoor `mskZ σ`, `matE_enc_zero`), **`exec_m2C`** (from
  `m2Init σ C`: `14` = `mpkW σ`, `8` = `matL A_F`); **M3 contract `PkOk pk`** (from `pkInit σ C`:
  `0` = `rawEnc σ`, `1` = `ctW σ`, `2` = `mpkW σ`, `rCs` = `C`, all else blank, reach `SimKeyIn`);
  **M4** `setXC D` (module 5's inputs from `SeConst`'s surviving `rTW`, `rTb`, `rOne`, `rKc`,
  `MulTmpl` and the `H` field of the public-key word in `14`: `readFieldC 14 rxH |B| |H|`,
  `mpkEnc_H`, `hEnc_flat`), **`setXOk_setXC`**, `simKeyC_keeps` (`decide`); the chain
  **`ready_of_pk`**: `PkOk pk → RkMidReady … (wFin pk σ C (matL A_F))` with
  `w4Of = exec simKeyC (exec pk (pkInit σ C))`, `w6Of = exec simXC (exec setXC (w4Of[14 := mpkW]))`,
  `wFin = w6Of[8 := A][14 := mpkW]`.
* **`RedKeyMidM`** (tape level, `247` tapes): `mS a g` (MVM store `a` on `0 … 104` via
  `RedKeyM.rkE`, storage `g` elsewhere), `law_frame_mS`, `run_ld`/`run_st`/`run_clrS`/`run_consR`
  (load/stash/clear/bit between register tapes `tRg r = rkE (tR r)` and storage tapes `≥ 105`);
  **`mid pk`** (table below), **`wf_mid`** (`pk.WFc → (mid pk).WF`), **`rkMidOk_mid`**
  (`PkOk pk → RkMidOk (mid pk)`).
* **`RedKeyMidPk`** (M3, first part): `pkOf pkt = pkConstC Dc ; pkCfC Dc ; pkt`:
  `pkConstC` = F3's `templateOpsC` with `pkConstOps` (unary templates by doubling, `1`, `X⁻¹`,
  `X^{2^14−1}` literal) → **`seConst_pkConstC`**; `pkCfC` → `4 := C`,
  `rCs := cfOf D C = (C ++ 0^{16 tlK − predLen})^{nSl} ++ 0^{m̄}`, `seLoopC := 0^{nSl}`
  (**`exec_pkCfC`**, `cfOf_blocks`, `cfOf_tail`; `nSl = |seRestL| = m̄ + b·2·2K`);
  **contract `PktOk pkt`**: `pkt` never writes `pktKeepR` (`seConstR`, `rCs`, `seLoopC`) and from
  `0` = `rawEnc σ`, `1` = `ctW σ`, `2` = `mpkW σ`, `4` = `C` (anything else) writes
  `rAinS = encL (seRestL.flatMap (sePkOf Dc mpk C ct (attrN x) (progOf zr)))`;
  **`pkOk_pkOf`**, **`rkMidOk_pkOf : PktOk pkt → RkMidOk (mid (pkOf pkt))`**, `wf_pkOf`.

**So the Submission closes with** `RedKeyMComp.keyCompOf (mid (pkOf pkt)) (wf_mid (wf_pkOf hwf))
(rkMidOk_pkOf hpkt) …` once a packet-stream code `pkt` with `PktOk pkt` (and `pkt.WFc`) exists,
plus the cost certificates.

### The phases of `mid pk` (for the cost certificate)

`mid pk = m1P ; midEnter ; prog midLdM2 ; onM m2C ; prog midStA ; midEnter ; prog midLdPk ;
onM pk ; onM simKeyC ; prog midLd14 ; onM (setXC Dc) ; onM simXC ; prog midFin`
(`onM c = frame rkE (MVM.compile c)`; `timeBoundT_frame` makes the frame free; the storage tapes
`242 … 246` are untouched by every `onM`/`midEnter` and only change in the `prog` steps):

| phase | role | cost source |
|---|---|---|
| `m1P` | `m1InP` (3 prims); `ringIOS … pubC` ; `m1MidP` (3 prims) ; `ringIOS … chalC` ; `m1OutP` (2) | `ringIOS` = `bounds_ringIO1` + `parkP`/`unparkP` (6 prims each) + `postS` (`clrL` over ≤ 247 tapes); the stash registers are never mentioned by the code, so `RingVM.Closed` holds with `B 197/198/199` = the stash lengths (`|rawEnc σ| ≤ sigBound`, `predLen`, `|mpkW|`); `pubC`/`chalC` clocks from `RedPubPTime`/`RedChalTime` |
| `midEnter` (×2) | `frame rkE (prog (MVM.IO.pre Dc.N Dc.K 0))` (fresh MVM state) | `setList` of `105` tapes, templates `≤ N K = 2^40` bits (as F3's `enterP`) |
| `midLdM2`, `midStA`, `midLdPk`, `midLd14`, `midFin` | `cp`/`clr`/`cons` prims between storage tapes and register tapes | `2 (L + pad) + 3` each, `L` = longest word (≤ `|reg 16|`) |
| `onM m2C` | `natC` + F3 `keyPrepareC` | F3 `KeyTimePrepare`/`KeyPrepareSize` |
| `onM (pkOf pkt)` | `pkConstC` (`templateOpsC`, F3 `KeyTimeTemplates`), `pkCfC` (`natC`, `app`, `rep` of `nSl ≈ 2^{41.6}` appends; `|rCs| ≈ nSl · 2^{29.8} + m̄ ≈ 2^{71.4}` bits), `pkt` | |
| `onM simKeyC` | module 6 | module 9 for `simKeyC` |
| `onM (setXC Dc)` | 6 moves + `readFieldC` + `natC rxTs (2^b · m̄)` (`≈ 2^{63.6}` bits) | `natC`/`readFieldC` clocks (F3) |
| `onM simXC` | module 5 | module 9 for `simXC`; register `16` ≈ `2^{143}` bits |

Lengths: internal tapes `≤ 2^150` (register `16`); output after the back end `≤ |skEnc|`.

### The remaining obligation: `PktOk pkt` (the packet stream)

Per slab `r ∈ seRestL` (`inl w`, `w < m̄`, then `inr (k, c')`), `sePkOf … r = sePacket (seBitsOf …
(seHrOf P r) (seCrOf P r) (seRhoOf P r)) b (seSlabL (slabβ row0 R₀ r)) A₀ (AinK mpk)
(Cin ∘ read) pz pu (seZvOf P r ∘ read) (seRvOf P r ∘ read)`, i.e. the concatenation of

1. `b` bit records `seRec t = matL gc_t ++ adL ad_t ++ vecL crow_t ++ adL Aaut_t ++ vecL hrow_t ++
   matL Hf_t` — **public**: `gc_t = gcAut (idx 2^t) (evalPub mpk).aut.Hi_t (evalData mpk ct).aut.hi_t`,
   `Aaut_t = (evalPub mpk).aut.Aaut t`, `Hf_t = (evalPub mpk).aut.Hf t`; **slab rows**: `ad_t =
   seRhoOf P r t` (`inl w`: the bits `zr(Raut t d)` of row `w` at row `2^t`, else `0`),
   `crow_t = seCrOf P r t`, `hrow_t = seHrOf P r t` (`inr (k, c')`: the unit row `e_{c'}` iff
   `k = inv t` resp. `k = fwd t`; `inl`: `0`);
2. the start slab `seRows (seSlabL (slabβ row0 R₀ r))` (`inl w`: row `0` = `R₀[w, ·]` (bits of
   `zr`), other `2^b − 1` rows `0`; `inr`: all `0`);
3. `matL A₀` (public, a field of `mpkW`);
4. `16` step records `seStepRec (AinK mpk i) (Cin (read i)) pz_i (z-row) (rd-rows) pu_i` with
   `Cin t = cinMat (mpk.a t) (ct.cinBot t)` (public), `pz_i = X^{z_i}`,
   `pu_i = X^{z_i + w·x_{read i}}` (**BP states** `z_i = (bpOf (progOf C)).state x i`, `x =
   attrN σ.1`), slab rows `seZvOf P r (read i)`, `seRvOf P r (read i) d` (`inl w`: bits of
   `zr(Z (read i))`, `zr(Rin (read i) d)` of row `w`; `inr`: `0`).

Suggested code structure (`pkt = pubPartsC ; slabLoopC`):
* `pubPartsC` (once): from `mpkW` (`2`) and `ctW` (`1`) the public records — reuse F3's public
  evaluation for `(evalPub mpk).aut` (`KeyEval*`, `KeyRowAut`, `evalPublicC` computes `A_F` via the
  same `aut` data) and Dec's code (`DecMachine*`) for `(evalData mpk ct).aut`/`Cin`; the BP states
  from `C` (`4`) and the attribute (field of `rawEnc σ` in `0`): `16` table look-ups
  `z_{i+1} = tabsOf … i (z_i, x_{read i})` (`readSt` on `C`) — or reuse Dec's state walk if it has
  one; then `pz_i`, `pu_i` by `rho` from `1` (as `rXc`).
* `slabLoopC`: `rep` over the `m̄` `inl` slabs (row `w` of the bit matrices of `zr`, read from the
  `zr` field of `rawEnc σ`) and the `b·2·2K` `inr` slabs (unit rows), appending each packet to
  `rAinS`; the public records are copied into each packet. Bridges against `slabFreshOf` exist
  (`RedKeySimEB`: `seForms_slabFreshOf`, `seFormsIn_slabFreshOf`).

## Status (2026-11-25, seventh session): the packet stream `pkt` — slab half, bridge and BP walk done

New files `RedKeyPkt*.lean` (namespace `AdvancedEncryption.ExpLUT.Prog.RedKeyPkt`, prefix `pt`; all
build, no `sorry`/`native_decide`; **not in the aggregator**). Design (`pkt = setup ; pubPartsC ;
ptInlLoopC ; ptInrLoopC`; `pkt` must be self-contained: `PktOk` gives only registers `0,1,2,4`, so
`pkt` builds its own constants in free registers — it may not write `pktKeepR`):

* **`RedKeyPktSkel`**: `ptPacket` (the packet as public/slab interleaving), `sePacket_eq_ptPacket`,
  `flatMap_ptPacket`; the skeleton `ptSkelC ad cr hr l0 z rd` (public segments popped from copies of
  `ptPB = ∏_t (G_t ++ Aa_t ++ Hf_t)` (reg 10), `ptPS = ∏_i (SP_i ++ PU_i)` (11), `ptA0` (12), widths
  `ptTM/ptTAa/ptTSP/ptTPU` (15/16/17/29), counts `ptTB` (13, unary b), `ptT16` (14)), contract
  `PtSubOk` (five phase invariants), **`exec_ptSkelC`**.
* **`RedKeyPktMath`** (at `D`): **`sePkOf_eq`**: `sePkOf D mpk C ct x (progOf zr) r = ptPacket D.b
  (ptG …) (ptAd zr r) (ptCr r) (ptAa …) (ptHr r) (ptHf …) (ptL0 zr r) (ptA0L …) (ptSP …) (ptZ zr r)
  (ptRd zr r) (ptPU …)`; slab rows of `inl w` are bit rows of `zr` (column `w`), of `inr (k, c')`
  unit rows/zeros.
* **`RedKeyPktRows`** (generic): cursors on row-major bit matrices (`PtCur`, `ptCol`, `ptEmit`),
  `ptBitRowC`, `ptDigRowsC` (+ specs).
* **`RedKeyPktInl`/`RedKeyPktInr`** (generic): the six slab codes of each slab kind,
  `ptSubOk_inl`/`ptSubOk_inr`, `exec_ptSlabInlC`/`exec_ptSlabInrC`.
* **`RedKeyPktLoop`/`RedKeyPktLoopR`** (generic): `ptInlLoopC` (cursors from `ptZR = (rZ ++ rR0 ++
  rRin ++ rA).flatten`, reg 49) **`exec_ptInlLoopC`**; `ptInrLoopC` (selector `ptSelVM`, unit row
  `ptUnitVM`) **`exec_ptInrLoopC`**.

Registers used by the slab half: `0` (out), `5–17`, `29` (skeleton), `32–37`, `39–48` (slab codes;
`38 = rB1` avoided), `49–56` (loops). Free for the public half: `1, 2, 4, 30` and everything above
before the loops start (the loops need their inputs only).

* **`RedKeyPktBridge`** (at `D`, **(A) done**): `ptZRWord_eq` (`(ptRZ ++ ptRR0 ++ ptRRin ++
  ptRA).flatten = zrEnc.enc zr`, rows `ptRowOf zr i = (finRange m̄).map (zr i)`), segment bridges
  `ptAdLW_eq`, `ptL0LW_eq`, `ptZLW_eq`, `ptRdLW_eq`, `ptAdRW_eq`, `ptL0RW_eq`, `ptSelVM_getD`,
  `ptUnitVM_eq`; packets `ptInlPk_eq`, `ptInrPk_eq`, `ptJPk_eq`; **`ptStream_eq`**: (inl-loop word)
  `++` (inr-loop word) `= encL ((seRestL D).flatMap (sePkOf D mpk C ct x (progOf zr)))` with
  `O = encRM 1`, `Z = encRM 0`, `Z2 = ptZ2W D`, `ZL = ptZLW' D`, `nC = ptNC D = 2K`,
  `nD = ptND D = |DigI K|`, public words `ptGW`, `ptAaW`, `ptHfW`, `ptSPW`, `ptPUW`, `ptA0W`.
* **`RedKeyPktState`** (generic, **(C) VM done**): the BP walk `swLoopC` (regs `32–55`, prefix `sw`):
  Horner of the 8 symbol bits (`swSymC`), `u = z + 2^14 x` (`swUC`), `X^{z}`, `X^{u}` by `rho`
  (`swMonoC`, count `2N − e`), the next state = 14 bits at `14u` of the table (`swReadC`, then
  `swUnaryC`), `swCcur` advanced by `tlK`; **`exec_swLoopC`**: `swQZ = ∏_{i<16} swMonoW (swSt i)
  O`, `swQU = ∏_{i<16} swMonoW (swSt i + 2^14 xs i) O`.
* **`RedKeyPktStateD`** (at `D`): **`swSt_eq_state`** (`|C| = predLen`, symbols `< 256`, `i ≤ 15`:
  `swSt C tlK (x ∘ (· % 16)) i = (bpOf (progOf C)).state x i`), **`swMonoW_eq`**
  (`swMonoW N K e (encRM 1) = encRM (X^e)`, `e ≤ 2N`), `hornerB_symbolBits` (`decide`, 256 cases).

**Remaining** — (B) and (D); everything is designed, nothing proven yet:

(B) **public words** (new file `RedKeyPktPub.lean`, generic VM + `D` bridge), into `ptPB` (10),
`ptPS` (11), `ptA0` (12) and the widths `ptTM = 4K·NK`, `ptTAa = 16K^3·NK` (`= |adL|·NK`),
`ptTSP = (16K^3 + 4K + 1)·NK`, `ptTPU = NK`, `ptTB` (unary b), `ptT16`:
  1. field slices (`readFieldC`, needs `rB1 = [false]` and scratch `29`, `30` — run before `ptTPU`
     (29) is set): from `mpkW` (reg 2) the `H` field (`(Enum Jh).flatMap (matE ∘ H)` = for `t`:
     `encL (matL H_{(t,0)}) ++ encL (matL H_{(t,1)})`), `Aaut` (for `t`: `encL (adL Aaut_t)`),
     `a` (for `t`: `encL (vecL a_t)`), `A0` (`= ptA0W` directly), `Ain` (for `t`: `encL (adL
     Ain_t)`); from `ctW` (reg 1) `h` (for `k ∈ Jh`: `encL (vecL h_k)`), `cinBot` (for `t`).
     Offsets: `mpkEnc`/`ctEnc` are `FixedEnc.prod` chains (`prod_take`/`fun_block` lemmas,
     `RedKeyMidCode.mpkEnc_H` does the `H` field already).
  2. bit loop `t < b`: pop `H_{(t,0)}` (→ `Hf_t`), `H_{(t,1)}`, `h_{(t,0)}` (discard), `h_{(t,1)}`,
     `Aaut_t`; `G_t` entrywise: row 0 `σ^{2^t}(H_{(t,1)}[0,c])`, row 1 `σ^{2^t}(H_{(t,1)}[1,c] −
     h_{(t,1)}[c])` (`op sub`, then `rep P (op aut X X Kg)` with `|Kg| = gD D`, `|P| = 2^t` doubled
     per `t`; math: `seSigIdx` (`E.σ (idx m) = (aut N gD)^[m]`), `canonW_aut` (`0 < gD`),
     `map_sub` of `E.σ`); append `G_t ++ Aa_t ++ Hf_t` to `ptPB`. Bridge to `ptGW`/`ptAaW`/`ptHfW`:
     `evalPub.aut.Hi t = H (t,1)`, `Hf t = H (t,0)`, `Aaut t = mpk.Aaut ⟨t⟩`, `evalData.aut.hi t =
     ct.h (t,1)` (`finExt`, `t < b`).
  3. step loop `i < 16`: pop `Ain_i`, `a_i`, `cinBot_i`, pop `pz_i` from `swQZ`, `pu_i` from `swQU`
     (`mvR`); append `Ain_i ++ a_i ++ cinBot_i ++ pz_i` then `pu_i` to `ptPS`. Bridge:
     `matL (cinMat a bot) = vecL a ++ vecL bot` (`matL_eq`/`enum_fin2`), `AinK mpk i = Ain ⟨i%16⟩`,
     `read i = ⟨i % 16⟩`, payloads by `swSt_eq_state` + `swMonoW_eq` (`z_i < 2^14`, `u_i < 2^22 ≤ 2N`).

(D) **assembly** (`RedKeyPkt.lean`): `pkt = ptMoveC ; ptConstC ; swSetupC ; swLoopC ; pubC ;
ptZRC ; ptInlLoopC ; ptInrLoopC ; ptClrC` where `ptMoveC` = `cp 30 0 ; clr 0` (rawEnc out of
`rAinS`), `ptConstC` builds `[false]`/`[true]` (`bitsC` from a cleared register), `encRM 1`
(`[true] ++ 0^{NK−1}`), `encRM 0`, all unary templates by `natC` (`ptTm = m̄`, `ptTC = 2K`, `ptTD =
4K^2`, `ptTB`, `ptT16`, `swT8/14/2N/14b/16`, `swTtab = tlK`, block widths `ptTZb = 32K m̄`,
`ptTR0b = 2K m̄`, `ptTRinb = 16·4K^2·2K m̄`, `Kg = gD`), `ptZ2 = 0^{2K NK}`, `ptZL`, `ptZS = 0^{2b}`;
`swSetupC` = `cp swA 30` (attribute = head of `rawEnc`, `attrEnc.enc = (ofFn x).flatMap symbolBits`),
`cp swCcur 4`; `ptZRC` = the `zr` field of `rawEnc` into `ptZR = 49` (suffix: `readFieldC` with offset
`128 + |inst| + |B2| + |H2| + NK + |fl|`, `ptZRWord_eq`); `ptClrC` clears every scratch register
(for the cost certificate). `PktOk`: (i) `pkt.writes r = false` for `pktKeepR r` — every register
above is outside `pktKeepR` (`3, 18–28, 31, 57–63`) **except** that the slab codes never touch them:
check by `decide` on the whole code; (ii) the stream: `exec_ptInlLoopC`, `exec_ptInrLoopC` (with
`PtSkIn` from (B), `PtRowConst`, `PtInrIn`), then `ptStream_eq`. Note `rAinS` must be `[]` before
the loops (`ptMoveC`).
### Per-phase cost table (`pkt`; `m̄ ≈ 2^{41.6}`, `K = 2^16`, `NK = 2^40`, `b = 22`)

| phase | rounds | per round | total (MVM steps · word bits) |
|---|---|---|---|
| `ptInlLoopC` | `m̄` slabs | cursors: 8 moves of `|ptZR| ≈ |PrI| m̄ ≈ 2^{41.6+38}` bits; packet: `≈ 2^{38}` bit-row rounds (`ifb`, `app`, `drop` of the cursor ≤ `2^{80}` bits) + `3b + 48` pops of `≤ |ptPB| ≈ 2^{22+49+40}` bits | `≲ 2^{41.6} · 2^{38} · 2^{111} ≈ 2^{191}` |
| `ptInrLoopC` | `b · 2 · 2K ≈ 2^{23.5}` slabs | selector/unit set-up `O(2K NK)`; packet as above without cursors | `≲ 2^{23.5} · 2^{8} · 2^{111}` |
| `swLoopC` | 16 steps | Horner (8), `2^{14}` appends of `≤ 2^8` bits, 2 `rho` (count `≤ 2N = 2^{25}`, word `NK`), `14` drops of `C` (`2^{29.7}` bits), 14-bit unary | `≲ 2^{4} · 2^{25} · 2^{40} = 2^{69}` |
| `pubC` (planned) | `b` bits + 16 steps | `G_t`: `4K` entries × `2^t ≤ 2^{21}` `aut`s on `NK` bits; pops of `≤ |mpkW| ≈ 2^{100}` bits | `≲ 2^{18} · 2^{21} · 2^{60} + 2^{110}` |

All registers written by the slab half stay below `|rAinS| ≤ nSl · |packet| ≈ 2^{41.6} · 2^{91} =
2^{132.6}` bits (`≤ 2^{150}`); every scratch register (`ptX`, cursors, counters) is overwritten per
round (not cleared at the end yet — `pkt`'s final phase must `clr` them for the cost certificate).

## Status (2026-11-25, eighth session): `pkt` done — `PktOk pkt`, `rkMidOk_pkt`

New files (namespace `AdvancedEncryption.ExpLUT.Prog.RedKeyPkt`; all build with
`lake build PE.Impl.ExpLUT.Prog.RedKeyPktOk`; no `sorry`/`native_decide`; axioms of `rkMidOk_pkt`,
`pktOk_pkt`, `wf_pkt`, `exec_pktC`, `pktC_keeps`: `propext`, `Classical.choice`, `Quot.sound`;
**not in the aggregator** — add `RedKeyPktSkel … RedKeyPktStateD` (seventh session) and
`RedKeyPktPub`, `RedKeyPktPubLoop`, `RedKeyPktPubD`, `RedKeyPktAsm`, `RedKeyPktExec`,
`RedKeyPktOk`):

* **`RedKeyPktPub`** (generic `N K`, prefix `pb`): `pbPopC d q T` (`d :=` first `|T|` bits of `q`,
  `exec_pbPopC`), `pbAutC e` (`e := σ_g^{|P|}(e)` by `|P|` rounds of `op aut`, `exec_pbAutC`,
  `pbSig g m = (aut N g)^[m]`), the rows of `G` (`pbRow0C`, `pbRow1C`), **`exec_pbGC`**:
  `G = encL (pbGL σ l0 l1 l2)`, `pbGL σ l0 l1 l2 = l0.map σ ++ zipWith (σ a − σ b) l1 l2`.
* **`RedKeyPktPubLoop`** (generic): **`exec_pbBitC`** (`ptPB = ∏_{t<b} encL (pbGL (σ_g^{2^t}) …) ++ Aa_t ++
  Hf_t`, `P` doubled per round from `[false]`), **`exec_pbStepC`** (`ptPS = ∏_{i<16} (Ain_i ++ a_i ++
  cb_i ++ z_i) ++ u_i`), **`exec_pbPubC`** (cursors `cp q src ; drop q offset`, both loops, `A₀` by a pop).
* **`RedKeyPktPubD`** (at `D`): **`pbG_eq`** (`pbGL (σ_g^{2^t})` of the rows of `H_{(t,1)}`, `h_{(t,1)}`
  `= ptG`, via `seSigIdx`), the fields as queues (`pbFH_eq`, `pbFh_eq`, `pbFAa_eq`, `pbFAin_eq`,
  `pbFa_eq`, `pbFcb_eq`; `pbFin_range`, `pbJh_flatMap`), `pbSP_eq` (`SP_i`), `pbPU_eq`, lengths.
* **`RedKeyPktAsm`**: offsets `pbOff*v`, `pbOffzr` and `pkDrop_*` (the fields of `mpkEnc`/`ctEnc`/
  `rawEnc` after the offsets); **the code** `pktC D = pkMoveC ; templateOpsC pkSwOps ; pkWalkC ;
  templateOpsC pkPbOps ; pbPubC ; templateOpsC pkLpOps ; pkFinC` (`pkFinC` ends with
  `pkClrL pkScratch`: every register outside `rAinS` and `pktKeepR` is cleared); **`pktC_keeps`**
  (`natC`-free phases by `decide`, the template phases by `templateOpsC_frame`), **`wf_pktC`**
  (`pkWfB`, a decidable `WFc`).
* **`RedKeyPktExec`** (at `D`): `exec_pkPre` (walk), `exec_pkPub` (public phase), `exec_pkFin`
  (loops, `ptStream_eq`), **`exec_pktC`** (`2^22 ≤ 2N`): `exec (pktC D) w rAinS = encL ((seRestL D).flatMap
  (sePkOf D mpk C ct (attrN σ.1) (progOf σ.2.2.2.2.2.2)))` from `w 0 = rawEnc σ`, `w 1 = ctEnc ct`,
  `w 2 = mpkEnc mpk`, `w 4 = C` (`mpk`, `ct` arbitrary).
* **`RedKeyPktOk`** (at `Dc`): **`pkt := pktC Dc`**, **`wf_pkt`**, **`pktOk_pkt : PktOk pkt`**,
  **`rkMidOk_pkt : RedKeyM.RkMidOk (mid (pkOf pkt))`**, `wf_pkOf_pkt`.

Register map of `pktC` (`pktKeepR = {3, 18–28, 31, 57–63}` never written): `30` raw word; `5`/`38`
`[true]`/`[false]` for `templateOpsC`; walk `32–55` (outputs `swQZ = 42`, `swQU = 43`); public phase
templates `6–8, 13–16, 29, 47–53`, `P = 9`, cursors `32–34`, scratch `17, 35–37, 39–41, 44–46`, outputs
`10–12`; loop constants `17, 37, 39, 40, 42, 44–46, 50–52, 55, 56` (+ `1 := 0^{2b}`, `2 := [true]`,
`4 := 0^{NK−1}` parked for `ptZS`, `ptBT`, `ptOne`).

### Per-phase cost table (`pktC Dc`; `m̄ ≈ 2^{41.6}`, `K = 2^16`, `NK = 2^40`, `b = 22`)

| phase | rounds | per round | total (MVM steps · word bits) |
|---|---|---|---|
| `pkMoveC` | 1 | `cp` of `|rawEnc| ≈ 2^{97}` bits, `bitsC` | `≲ 2^{97}` |
| `templateOpsC pkSwOps` | 9 templates | `natC`: `O(log n)` doublings; largest `tlK ≈ 2^{25.8}`, `NK` | `≲ 2^{46}` |
| `pkWalkC` (`swLoopC`) | 16 steps | as in the seventh-session table | `≲ 2^{69}` |
| `templateOpsC pkPbOps` | 15 templates | offsets `≤ |mpkW| ≈ 2^{97}` bits (`A^in`, `A^aut` fields `≈ 2^{96}`) | `≲ 2^{104}` |
| `pbPubC` cursors | 7 | `cp` + `drop` of `≤ 2^{97}` bits | `≲ 2^{101}` |
| `pbBitC` | `b` | 5 pops (`≤ |TAa| = 16K^3 NK ≈ 2^{92}` bits); `G_t`: `4K = 2^{18}` entries × `≤ 2·2^{21}` `aut`s on `NK` bits; 3 appends to `ptPB` (`≤ b·2^{93}`) | `≲ 2^{4.5}·(2^{18+22+40} + 2^{98}) ≈ 2^{103}` |
| `pbStepC` | 16 | 5 pops `≤ 2^{92}` bits, appends to `ptPS` (`≤ 2^{97}`) | `≲ 2^{102}` |
| `templateOpsC pkLpOps` | 16 templates | largest `ptTRinb = 16 nD 2K m̄ ≈ 2^{96.6}`, `pbOffzr ≈ 2^{97}`, `ptZL ≈ 2^{79}` | `≲ 2^{104}` |
| `pkFinC` loops | `ptInlLoopC`, `ptInrLoopC` | as in the seventh-session table | `≲ 2^{191}` |
| `pkClrL pkScratch` | 43 `clr` | | `43` |

All registers stay `≤ |rAinS| ≈ 2^{132.6}` bits. **Remaining** for the Submission: the aggregator
entries above; the cost certificates of `mid (pkOf pkt)` (the table) — the law side of `keyP` is now
closed by `rkMidOk_pkt` (with `RedKeyMComp.keyCompOf (mid (pkOf pkt)) (wf_mid wf_pkOf_pkt)
rkMidOk_pkt …`).

## Status (2026-11-25, ninth session): cost certificate of `mid (pkOf pkt)` — **blocked by the interface**

Target: `∃ a, RkTailIn a ∧ RkMidBound (mid (pkOf pkt)) a` and `(mid (pkOf pkt)).size ≤ 2^190`
(`RedKeyTSpec.spec_of_mid`). **The length half is false for the current `mid`**, and the time half
cannot reuse F3's KeyGen certificate. Details and the tool built to find this:

### Blocker 1 (length): static bounds of `sePostC` exceed `2^150` on register `24` (`rxRh`)

`XProg.lenBoundT` is data-oblivious: `drop`/`mv` never shrink a static bound (`dropPc`/`mvPc` are
loops whose `iterSupT` includes round `0`), and a loop runs its counter's *static* bound. After
`pkCfC`, `|rCs|` is statically `nSl · 16 tlK + m̄ = (3·2^40 + 408 + 22·2^18) · 14·2^26 + 3·2^40 + 408
≈ 42·2^66 ≈ 2^71.39`; the slab loop of `simKeyC` consumes it (really `0^{m̄}` is left) but the static
bound stays. `sePostC` then uses `rCs` as a count:

* `seSplitC`: `cp sePD rCs ; rep sePD (app sePC rTW)` → `|sePC| ≈ 2^93.39`, `sePopsC` appends a
  `2K·NK = 2^57`-bit row per round → `sePA` (reg `8`) `≈ 42·2^145 ≈ 2^150.39` (harmless: `midFin`
  overwrites `8`), `cp rAinS sePA`;
* `cp rtN rCs ; … ; transC`: `2^22` passes × `|rtN| ≈ 2^71.39` slabs; per slab `app rxRh rtX`
  (`2^57` bits) and `app rtQ rtX` (`|rtR| = (2^22−1)·2^57 ≈ 2^79` bits) →
  **`rxRh` (reg `24`, tape `65`) `≥ 2^22 · 2^71.39 · 2^57 ≈ 2^150.39`**, and `rtQ` (reg `0`)
  `≈ 2^172.4` transiently (reset by the straight-line `cp rtQ sePB`).

`rxRh` is only consumed afterwards (`mvR` in `simXC`), never reset by a straight-line `cp`/`clr`
(`simXC`'s `cp`/`clr` of it, if any, sit inside loops whose `iterSupT` keeps round `0`), and
`midFin` does not clear it. So `lenBoundT (mid (pkOf pkt)) rkIn (rkE (tR 24)) > 2^150 =
rkTailEnv (tR 24)`: no `a` with `RkTailIn a ∧ RkMidBound … a` exists.

**Fix options** (decision for the orchestrator):
* **(A, recommended) code**: in `RedKeySimEP` (`seSplitC`, `sePostC`) count with a fresh unary
  `m̄` (e.g. `natC _ rB1 D.mb` into a spare register, or a copy of `0^{m̄}` saved by `pkCfC`)
  instead of `rCs` (semantically equal: after the slab loop `rCs = 0^{m̄}`, `exec_sePostC` changes
  little). Statically then `sePA`, `rxRh ≈ 2^120.6`, `rtQ ≈ 2^142.6`; it also removes the `2^172`
  transient, which otherwise forces every per-instruction certificate (F3's take `∀ t, a t ≤ M`)
  to run at `M ≥ 2^173` — and F3's `op` certificates leave the scratch tapes `0 … 31` at `M`
  (`ringArea`, `countedArea`), which would then also violate `RkTailIn.top` (any `op` after the
  transient, e.g. in `simXC`).
* (B) interface: raise `rkTailEnv`/`RkTailIn.top` (at least for tape `tR 24`, and the scratch
  tapes unless the `op` certificates are re-framed to a local `M`) to `≥ 2^151`/`2^173`, and
  re-check the tail certificate against it.

### Blocker 2 (time): F3's `compile_keyPrepareC_Dc` is `2^461 > 2^440`

M2 (`m2C = natC ; cp ; app ; keyPrepareC Dc`) cannot reuse F3's certificate (`2^461`; the loss is
`operationBound_concrete … (count := 2^120)` charging every `op` `2^340`). A re-certification with
the actual counters (the analyzer below) gives `≈ 2^333` at `M = 2^120`.

### Tool: a static bound analyzer for MVM codes (`RedKeyCA.lean`, `RedKeyCAX.lean`; build, no proofs)

`RedKeyCA`: `caAn L N K c E` (computable, `Except` with diagnostics) over-approximates
`lenBoundT`/`timeBoundT` of `MVM.compile c` from `KeyTime.layout L N K x`, `x ≤ E`, as a
per-register transformer (`out r ≤ max a (x s + δ)` or `≤ a`); loops by a linear-growth rule
(box `B` found by ≤ 3 tries; iterates `max a (x r) + j δ`) with an unrolling fallback for counts
`≤ 64` (doubling loops); leaves `CaX.n` (`natC`), `CaX.t` (templates). `RedKeyCAX`: mirrors of the
MVM phases with estimated literal sizes (doc of the file lists the `#eval`s). Results:

| phase | `L` | time | notes |
|---|---|---|---|
| M2 `m2C` | `2^120` | `2^333` | `14 ≤ |mpkW|`, `8 ≈ 2^58` |
| M3 `pkOf pkt` | `2^150` | `2^314` | `rAinS ≤ 2^141`; `pkClrL` leaves scratch `0` |
| M4a `simKeyC` | `2^150` | fails | `sePopsC`: `app 8 12` at `2^151` (Blocker 1) |
| M4a `simKeyC` | `2^250` | `2^510` | artificial cap; time inflated by `L` (charged per instruction) |

Every loop rule of `pkt`, `evalC`, `keyPrepareC` succeeds (relational `cp` entries were needed for
`simKeyC`'s round trips `cp X 0 ; … ; cp 0 X`).

**Making it a certificate** (next session, after the fix):
1. Soundness by induction on `Code`: per instruction F3's certificates (`compile_op_scratch_ready`
   + `le_layout`, `compile_cp_any`, `compile_clr_cert`, `compile_tl_cert`,
   `compile_drop_scratch`/`_self`, `compile_mv_scratch`/`_overlap`, `compile_mvR_scratch`/`_self`,
   `compile_append`, `compile_eqb_cert`/`_overlap`, `compile_nop`), `Cert.seq`, `Cert.ifBit` +
   `mono`, `rep_family` with `γ j = layout (G_j x)` (linear rule) and a `loop_family` variant with
   an output bound over all `j ≤ R` (unrolling: `U_j` compositions, prefix joins); leaves
   `compile_natC` (needs `a (tR rB1) = 1`), `compile_templateOps`. Better: make `M` per
   instruction the sup of the current box and track the scratch tapes `0 … 40` separately (the
   `2^172` transient otherwise caps everything), or use the tail's `rktOp`/`rktOpU`.
2. **Kernel cost**: `decide +kernel` on the prefix `pkConstC ; pkCfC ; pkMoveC ; templates ;
   pkWalkC` took **65 s** (compiled: instant); `simKeyC` compiled takes 1.5–3 min (nested loops,
   depth 7, ≤ 3 body analyses per level). Needed: per-loop **hints** (the box `B` found by the
   compiled run, sparse and rounded up to powers of two) so the kernel analyzes each body once,
   kernel-friendly data (a fixed-depth tree instead of `List.getD`/`List.range`), and/or
   compositional leaves (prove a sub-code once at its envelope box, reuse it).
3. Size: `codeWeight` of the mirrors (`size_compile_weight`; `natC` leaves `RedKeyTSize.wtNatC`,
   templates `weight_templateOpsC`).
4. M1 (`m1P`, RingVM: `bounds_ringIO1`, `RedPubPBound`, `RedChalBound`) and the `prog`/`midEnter`
   steps (`cert_vmPre`, `Cert.frame`) are untouched by this session.

## Status (2026-11-25, tenth session): fix (A) done; phase M4 of `mid` certified

### Fix (A) of Blocker 1 (`RedKeySimEP`, `RedKeySimE`, `RedKeyMidCode`, `RedKeyMidM`, `RedKeyCAX`)

`sePostC` counts with a fresh register **`seMb = 13`** instead of `rCs` (`cp sePD seMb`,
`cp rtN seMb`); **`sePostMC mb = natC seMb rBit1 mb ; sePostC`** builds `0^{mb}` from `rBit1`
(a `SeConst` constant), so the static bound of the count is `m̄`, not `|rCs|`.
**`simKeyC D = seLoopKC ; sePostMC D.mb`** now takes `D`. Statement changes (names kept):
`exec_sePostC` assumes `(w seMb).length = nA` (was `rCs`); new `exec_sePostMC` (assumes
`w rBit1 = [false]`), `sePostMC_writes`, `wf_sePostMC`, `wf_sePostC`, `wf_seLoopKC`;
`exec_simKeyC`, `exec_simKeyXC`, `SetXOk`, `wf_simKeyC` are about `simKeyC D`;
`simKeyC_keeps`/`w4Of` about `simKeyC Dc`; `mid` uses `onM (simKeyC Dc)`. `SimKeyIn.tail` is no
longer used by `exec_simKeyC` (kept). `rkMidOk_pkt`, `wf_pkOf_pkt`, `RedKeyTSpec`, the aggregator
build unchanged. Static bounds now: `rxRh (24) ≤ 2^120`, `sePA (8) ≤ 2^120`, no `rtQ` transient.

### Phase M4: `RedKeyC4A` (analyzer), `RedKeyC4X` (search, exploration), `RedKeyC4H` (checks), `RedKeyC4`

* **`RedKeyC4A`** — a verified version of the ninth session's analyzer (namespace
  `RedKeyC4`): entries `max a (m · x s + δ)` (multipliers for doubling loops), sparse
  transformers, loop rules by **hint** (`C4H.box`: linear rule with one body analysis on the
  hinted box; `C4H.unroll`), `natC` leaves through `AC`/`AC.Er`. **`an_sound`**, **`anA_sound`**,
  **`c4Ok_cert`**: `c4Ok M N K ac E hs Eo T = true → AC.Er ac c → (NK, N, K ≤ M, 1 ≤ M) →
  ∀ x ≤ bx E, Cert (compile c) (layout M N K x) (layout M N K (bx Eo)) T`. Also `codeEq`
  (Boolean `Code` equality, `codeEq_eq`).
* **`RedKeyC4X`** — `c4S`/`c4SA`: the analyzer with box search (finds the hints), `c4Report`,
  `c4Hints`. Generator used for `RedKeyC4H` (a scratch file importing `RedKeyC4X`): run `c4SA`
  at `M = 2^150`, `N = 2^24`, `K = 2^16` on `.c seLoopKC` from `c4In`, then on `c4AcP`, set
  register `14 := 2^102`, `c4AcX`, `.c simXC`; print boxes (`toString`) and hints.
* **`RedKeyC4H`** — the literal boxes `c4In`, `c4E1 … c4E5`, hints `c4H1` (245), `c4H2` (9),
  `c4H4` (53), and **`c4_ok1 … c4_ok4`** (`decide +kernel`; `c4_ok1` ≈ 30 s, ≈ 7 GB above the
  import baseline; the module builds in ≈ 75 s, peak RSS ≈ 11.6 GB), `c4_top`, `c4_len`.
* **`RedKeyC4`** — **`m4P`** (`onM (simKeyC Dc) ; midLd14 ; onM (setXC Dc) ; onM simXC ;
  midFin`), **`mid_m4P : mid pk = m1P ; midEnter ; midLdM2 ; onM m2C ; midStA ; midEnter ;
  midLdPk ; onM pk ; m4P`** (`rfl`), and

      theorem c4_cert_m4 (x : Fin 64 → ℕ) (hx : x ≤ bx c4In) (g : Fin 247 → ℕ) (hg : C4Store g) :
          Cert m4P (c4Env x g) (rkLiftB c4Out) (2 ^ 412)
      theorem c4_tailIn : RkTailIn c4Out

  with `c4Env x g = embedF rkE g (layout (2^150) (2^24) (2^16) x)`,
  `c4Out = layout (2^150) (2^24) (2^16) c4OutB` (`c4OutB = c4E5` with `8 := 2^150`,
  `14 := 2^102`). Per phase: `simKeyC` `2^411 + 2^298`, `setXC` `2^256`, `simXC` `2^407`,
  `midLd14`/`midFin` `8 · (2^151 + 5)`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

| phase | time | notable output bounds |
|---|---|---|
| `seLoopKC` | `2^411` | `rAinS (0) ≤ 2^142` (slabs appended), registers `≤ 2^142` |
| `natC seMb ; sePostC` | `2^298` | `rxRh (24) ≤ 2^120`, `8 ≤ 2^120` |
| `midLd14` | `2^152` | `14 := tMpk ≤ 2^102` |
| `setXC Dc` | `2^256` | `rxH (15) ≤ 2^98`, `rxTs (27) ≤ 2^64` |
| `simXC` | `2^407` | `16 (rows of X) ≤ 2^141` |
| `midFin` | `2^154` | `8 := tAF`, `14 := tMpk`, storage `0` |

### The INPUT envelope of M4 (what M1–M3 must deliver after `onM (pkOf pkt)`)

On the `247` tapes: **`≤ c4Env x g`** with

* **registers `x ≤ bx c4In`**: `rAinS (0) ≤ 2^142`, `rCs (3) ≤ 2^73`, `seLoopC (28) ≤ 2^42`,
  `rKc (31) ≤ 16` (`gD Dc = 9`), `rBit1 (21) ≤ 1`, the `SeConst`/`MulTmpl` templates at their exact
  sizes (`18, 19, 20`: `2^40`; `22`: `2^22`; `23`: `22`; `24`: `14`; `25`: `14 · 2^22`; `26`:
  `(32 · 2^48 + 12 · 2^16) · 2^40`; `27`: `2^18`; `57`: `2^17`; `58`: `2^58`; `59`: `2^57`; `60`:
  `2^56`; `61`, `62`: `2^16`; `63`: `2^40`), **every other register `≤ 2^141`**;
* the MVM scratch tapes `0 … 40` `≤ 2^150`, the ring templates `35 … 38` exactly `K, N, NK, NK`
  (the shape of `layout (2^150) (2^24) (2^16)`);
* **storage `C4Store g`**: every tape `≤ 2^150`, `tMpk ≤ 2^102`, every tape `≥ 105` other than
  `tAF tCt tMpk tSig tC` at `0` (M1's `c1Out` and `midStA` give this with `tAF ≤ 2^104`).

The ninth-session estimates of M3's output (`RedKeyCAX`, `rAinS ≈ 2^141.1`, `rCs ≈ 2^72.4`,
`seLoopC = nSl ≈ 2^41.6`, everything else cleared by `pkClrL`) fit with margin.

### Remaining

* M1–M3 certificates ending in the envelope above (other agent, `RedKeyC1*`, `RedKeyC2*`, …;
  `RedKeyC4A` can certify M2/M3 too: `c4Ok_cert` + `AC` for the `natC`/template leaves —
  `templateOpsC` would need an `AC` leaf, not provided yet).
* The assembly `RkMidBound (mid (pkOf pkt)) c4Out` (`mid_m4P`, `Cert.seq`; time
  `2^437 + 2^389 + … + 2^412 ≤ 2^440`) and `(mid (pkOf pkt)).size ≤ 2^190`.
* The new modules (`RedKeyC4A`, `RedKeyC4H`, `RedKeyC4`; `RedKeyC4X` is exploration) are **not in
  the aggregator** (`RedKeyC4H` costs ≈ 75 s / 11.6 GB peak).

## Status (2026-11-25, eleventh session): M1, M2, glue, assembly with M4, size — only M3 remains

New files (namespace `AdvancedEncryption.ExpLUT.Prog.RedKeyC`, prefixes `c1`/`c2`/`c3`/`cs`; all
build with `lake build PE.Impl.ExpLUT.Prog.RedKeyC3Fin`; no `sorry`/`native_decide`; axioms of
every main theorem `propext`, `Classical.choice`, `Quot.sound`; **not in the aggregator**):

* **`RedKeyC1Un`** (generic tape programs): `c1XAv S p` (`p` never mentions a tape of `S`),
  `c1X_len : lenBoundT p (c1Mix S ℓ g) = c1Mix S (lenBoundT p ℓ) g`,
  `c1X_time : (∀ t ∈ S, g t ≤ V) → timeBoundT p (c1Mix S ℓ g) ≤ (V+1) · timeBoundT p ℓ`.
* **`RedKeyC1Ring`**: **`c1_bounds_ringIOS`** — `Cert (ringIOS …) (c1St (io2 La Lb 0) v₁ v₂ v₃)
  (c1St (io2 (B ro) 0 0) v₁ v₂ v₃) ((M+1)·210(2M+1)(4M+12) + vmTime … + 300(2M+3))`: the stash
  keeps its exact bounds (`c1_closed_update`: a code not mentioning `r` is `Closed` for any bound on
  `r`; the parked stash costs a factor `M+1` on `preP` only).
* **`RedKeyC1`**: `c1_cert_pub` (`≤ 2^436`), `c1_cert_chal` (`≤ 2^351`), **`c1_cert_m1P : Cert m1P
  rkIn c1Out (2^437)`**, `c1Out`: `tCt ≤ 2^110`, `tMpk ≤ 2^102`, `tSig ≤ 2^101`, `tC ≤ predLen`,
  all other tapes `0`.
* **`RedKeyC2Eval`/`RedKeyC2`** (M2): F3's evaluator lemmas are generic in the tape cap; they are
  re-instantiated at **`M = 2^104`** (all M2 words `< 2^99`: `c2_codec`); numeric facts by `decide`
  on closed numerals. `c2_evalC_env ≤ 2^388`, `c2_cert_keyPrepareC ≤ 2^390`,
  **`c2_cert_m2C : Cert (compile m2C) c2In c2L (2^391)`** (`c2In = layout 2^104 … c2InB`,
  `c2InB 2 = 2^102`, `rB1 = 1`; `c2L = layout 2^104 … (fun _ => 2^104)`).
  *Kernel lesson*: never let the kernel unfold `compile (seq (natC r u nT) …)` (it evaluates `natC`
  on `nT ≈ 2^97`: deep recursion) — rewrite with a generic `c2_compile_seq`; likewise prove
  `a (e 0) = …` by `rw`, not by defeq, when `a` is a `set` of a `natResult … nT`.
* **`RedKeyC3Glue`**: `c3S a g` (bounds: `a` on the MVM tapes, `g` on storage), `c3_onM`,
  `c3_enter` (`midEnter`, `2^310`), `c3_cert_ldM2`, `c3_cert_stA`, `c3_cert_ldPk`,
  **`c3_cert_head`**: the head `m1P ; midEnter ; midLdM2 ; onM m2C ; midStA ; midEnter ; midLdPk`
  from `rkIn` to **`c3S c3In c3G`** in `≤ 2^438` (then any continuation).
* **`RedKeyCSize`**: `cs_ringIOS_le` (`ringIOS ≤ ringIO1 + 12000` states), `cs_m1P ≤ 2^32`,
  `cs_enter ≤ 2^53`, `cs_m2C : codeWeight m2C ≤ 2^104`, **`cs_mid`**:
  `codeWeight pk ≤ 2^160 → codeWeight (simKeyC Dc) + codeWeight (setXC Dc) + codeWeight simXC ≤
  2^160 → (mid pk).size ≤ 2^190`. *Kernel lesson*: sizes of concrete `Prog 247`s must not be
  compared by defeq (`decide`/`rfl` on `midLd*` evaluates `tRg` → giant `Nat.pow`); use `simp` with
  `Prog.size`, generic equations (`cs_seq13`, `cs_m1_gen`) and pass hypotheses whose atoms match
  syntactically (no `omega` across differently elaborated atoms).
* **`RedKeyC3Fin`**: `c3_store : C4Store c3G`, `c3In_le : c3In ≤ c4L c3InB`,
  **`c3_midBound_of_m3 (pk) (x) (hx : x ≤ bx c4In) (T) (hT : T ≤ 2^438)
  (h3 : Cert (compile pk) c3In (c4L x) T) : RkMidBound (mid pk) c4Out`** (with M4's
  `c4_cert_m4`), and **`c3_spec`**: from `h3` for `pk = pkOf pkt` and the weights of `pkOf pkt`
  and the M4 codes (`≤ 2^160`), the final `Spec` (`RedKeyT.spec_of_mid`).

### Envelopes

* **Input of M3** (MVM tapes, after `midLdPk`): **`c3In`** = `preResult Dc.N Dc.K c2L` (templates
  `35 … 38` exact, registers blank, op-area tapes `≤ 2^104`) updated at `tR 0 := 2^101`,
  `tR 1 := 2^110`, `tR 2 := 2^102`, `tR rCs := predLen`; `c3In ≤ c4L c3InB` (the `2^150`
  layout with these four register caps, others `0`), so `RedKeyC4A.c4Ok_cert` applies from
  `bx [2^101, 2^110, 2^102, predLen, 0, …]`. Storage **`c3G`**: `tAF ≤ 2^104`, `tCt ≤ 2^110`,
  `tMpk ≤ 2^102`, `tSig ≤ 2^101`, `tC ≤ predLen`, others `0` (`C4Store c3G`).
* **Output of M3** required by M4 (tenth session): `c4L x` with `x ≤ bx c4In` (`rAinS ≤ 2^142`,
  `rCs ≤ 2^73`, `seLoopC ≤ 2^42`, `rKc ≤ 16`, `rBit1 ≤ 1`, templates exact, others `≤ 2^141`).
  The ninth-session analyzer run from `c3InB` (`RedKeyCAX`, `M = 2^150`) predicts
  `T ≈ 2^314`, `rAinS ≈ 2^141.2`, `rCs ≈ 2^72.35`, `seLoopC = nSl ≈ 2^41.6`, SeConst templates
  exact, every other register `0` — within `bx c4In`.

### Time budget

`2^437` (M1) `+ 2^310 + 2^391 + 2^310 + …` (glue, M2) `≤ 2^438`; M3 `≤ 2^438` (estimate
`2^314`); M4 `2^412`; total `≤ 2^440`.

### Remaining (only M3, plus two weight bounds)

1. **`h3 : Cert (compile (pkOf pkt)) c3In (c4L x) T`, `x ≤ bx c4In`, `T ≤ 2^438`.** Plan:
   `pkOf pkt = pkConstC Dc ; pkCfC Dc ; pkMoveC ; templateOpsC pkSwOps ; pkWalkC ;
   templateOpsC pkPbOps ; pbPubC ; templateOpsC pkLpOps ; pkFinC`. Certify the template phases by
   F3's generic `compile_templateOps`-style lemmas (or a new `AC` leaf — `RedKeyC4A.AC` has only
   `natC` leaves; `emitBitsC` of `N K`-bit literals cannot be analyzed by the kernel), the others
   by `c4Ok_cert` (`pkCfC` with its `natC` leaves as `AC.nat`), with hints from `RedKeyC4X.c4SA`
   (as for `RedKeyC4H`), composed by `Cert.seq`/`Cert.mono` at the cap `2^150` from `c4L c3InB`.
2. `codeWeight (pkOf pkt) ≤ 2^160` and `codeWeight (simKeyC Dc) + codeWeight (setXC Dc) +
   codeWeight simXC ≤ 2^160` (F3's `weight_templateOpsC`, `weight_natC`; `codeWeight` by
   structural lemmas — never `decide` on codes with `natC` of a large literal).
Then `c3_spec` closes the Submission.

## Status (2026-11-25, twelfth session): M3 certified — `c3_spec_closed`

New files (namespace `AdvancedEncryption.ExpLUT.Prog.RedKeyC3M`, prefix `m3`; all build with
`lake build PE.Impl.ExpLUT.Prog.RedKeyC3M`, each module in ≈ 2–5 s; `RedKeyC3MH`'s nine
`decide +kernel` checks ≈ 4 s, ≈ 5 GB peak; no `sorry`/`native_decide`; axioms of
`c3_spec_closed`, `m3_h3`, `m3Ok_cert`: `propext`, `Classical.choice`, `Quot.sound`; **not in the
aggregator**):

* **`RedKeyC3MA`** — `RedKeyC4A`'s analyzer extended by **template leaves**: `AD` (`a : AC`,
  `tw r v`, `s`), `AD.Er` (`tw r v` describes `TemplateWord.code r w` for `|w.value| ≤ v`,
  certified by F3's `compile_template`; needs registers `5`, `rB1` `≤ 1` on the box, bumps them to
  `1`), `anD`, `anD_sound`, **`m3Ok_cert`** (as `c4Ok_cert`), `twL`/`twL_er` (a `templateOpsC`
  list as a chain of leaves — no literal is ever expanded).
* **`RedKeyC3MT`** — the mirrors: `m3Const` (`pkConstC Dc`), `m3Cf` (`pkCfC Dc`, `AC.nat` leaves
  `13·2^22`, `nSl = m̄ + 22·2^18`, `m̄`), `m3SwL`/`m3PbL`/`m3LpL` (template bounds: exact sizes,
  field offsets `≤ 2^98` (mpk), `≤ 2^110` (ct), `≤ 2^99` (`zr`)), `m3In` (= `c3InB`).
* **`RedKeyC3MB`** — the descriptions `m3_er_const`, `m3_er_cf`, `m3_er_sw`, `m3_er_pb`,
  `m3_er_lp` (symbolic sizes: `m3_gD : gD Dc = 9`, `m3_nSl`, `m3_offH`, `m3_offh`, `m3_offzr`,
  `m3_nZ`, `m3_encRM_le`).
* **`RedKeyC3MX`** — exploration (no proofs): `m3S` (box/hint search through `AD`, via
  `RedKeyC4X.c4SA`), `m3Report`, `m3Hints`, `m3OutL`. `RedKeyC3MH` was generated by running `m3S`
  phase by phase from `m3In` and printing the output boxes and hints.
* **`RedKeyC3MH`** — boxes `m3E1 … m3E9`, hints `m3H0 … m3H8` (33 loop hints), checks
  `m3_ok0 … m3_ok8` (one per phase: const `2^250`, cf `2^225`, move `2^154`, sw `2^197`, walk
  `2^270`, pb `2^268`, pub `2^302`, lp `2^256`, fin `2^296`), **`m3_E9_le : leL m3E9 c4In`**
  (`rAinS ≤ 2^140`, `rCs ≤ 2^72`, `seLoopC ≤ 2^42`, `SeConst` templates exact, all else `0`).
* **`RedKeyC3M`** — `m3_cert` (the chain, `m3_pkOf_eq`/`m3_compile_seq` by `rfl` on generic
  shapes), `m3_in_le : c3InB ≤ bx m3In`, **`m3_h3 : Cert (compile (pkOf pkt)) c3In
  (c4L (bx m3E9)) (2^303)`**, `m3_x_le : bx m3E9 ≤ bx c4In`, and

      theorem RedKeyC.c3_spec_closed
          (hw3 : codeWeight (pkOf RedKeyPkt.pkt) ≤ 2 ^ 160)
          (hw4 : codeWeight (simKeyC Dc) + codeWeight (setXC Dc) + codeWeight simXC ≤ 2 ^ 160) :
          Spec (primitive w8) Sub.registry (Sub.submissionOf DecConf.decMachine …)

### Remaining

Only the two weight bounds `hw3`, `hw4` (other agent, `RedKeyCW*`); then add the `RedKeyC*`
modules (`RedKeyC1* … RedKeyC4*`, `RedKeyC3M*`, `RedKeyCSize`) to the aggregator.

## Weights of the M3/M4 codes (`hw3`, `hw4` of `c3_spec`) — done

* **`RedKeyCWPk`** — `cw_pkOf : codeWeight (pkOf RedKeyPkt.pkt) ≤ 2 ^ 160` (in fact `≤ 2^124`):
  fixed phases by `decide +kernel` one at a time; template lists by `weight_templateOpsC`; codec
  and `Enum` lengths at `Dc` by `omega` after rewriting the dimensions to **numerals**
  (`cw_K : Dc.K = 65536`, `cw_N`, `cw_b`) and generalizing `Dc.mb`, `rows`, `gD`.
* **`RedKeyCW`** — `cw_m4` (`hw4`, `simKeyC Dc ≤ 2^44`, `setXC Dc ≤ 2^123`, `simXC ≤ 1000`) and
  **`c3_spec_w`**: `c3_spec` without `hw3`/`hw4`.
* Kernel lessons: (1) a single `simp only [pkSwOps/pkConstOps, List.map_cons, …, List.sum_cons]`
  makes the kernel recurse too deeply (≈2 min, then fails) when the list holds `tlK`/`2 ^ 14`
  — first prove the `map` as an explicit list for a generic `D` (`cw_swMap`, `cw_constMap`), then
  `rw` and sum; (2) `simp only [pkConstC, codeWeight]` / `rw [pkOf, pkt]; simp only [codeWeight]`
  also blow up — use `rw [show c = .seq … from rfl, cs_cw_seq]`; (3) `rw` with `Dc.N`/`Dc.K`
  fails (motive) when `(setting Dc).τ` hides `Dc.N` in instances — rewrite `Enum` lengths through
  `n`-generic lemmas (`cw_lenNZ`, …) and use `simp only` for the dimensions; (4) `nH`/`nB` clash
  with another namespace's names — write `RedKeyMid.nH`.
