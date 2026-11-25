# Tight clock and description length of the ExpLUT KeyGen machine (`KeyTight*`)

Deliverables (all build; axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorry`,
no `native_decide`):

* **`KeyCore.descLen_keyMachine_tight : keyMachine.descLen ≤ 2^295`** (`KeyTightSize.lean`;
  F3: `2^620`).
* **`KeyCore.time_keyMachine_tight : keyMachine.time ≤ 2^385`** (`KeyTightFront.lean`;
  F3: `2^508`).

Files (module dependency order): `KeyTightSize` (descLen); `KeyTightCorr` (tight real-trapdoor
correction, generic), `KeyTightPubY` (RedKeyT's Dc-level back end ported to the cap `2^121`),
`KeyTightTailY` (the attempt), `KeyTightEval` (F3's evaluator with exact numbers),
`KeyTightChain` (tight evaluator kernels, generic), `KeyTightEval2` (evaluator with the tight
chain), `KeyTightFront` (the machine clock).

Nothing existing was edited. Integration: import `KeyTightFront` and `KeyTightSize` and use the
two theorems in place of `time_keyMachine` / `descLen_keyMachine`
(`EncConf.machine_cost_lt keyMachine time_keyMachine_tight descLen_keyMachine_tight _`).

## 1. Description length (`KeyTightSize`)

Two independent losses in F3:

1. `descLen_arithA` bounds `Nat.size S` by `S`, so `descLen ≈ 6 S² 3^105`. With
   `entryBits 105 S 0 = 424 + Nat.size S` and `S ≤ 2^E ⇒ Nat.size S ≤ E + 1`
   (`KeyTight.descLen_arithLog`), `descLen ≤ 6 · 2^E · 3^105 · (425 + E)`.
2. The state count charges `natC r u n` with `3 n + 1` states (codec sizes `≈ 2^102 … 2^106`)
   and every gather index `j` with `3 j N K`. With RedKeyT's logarithmic `natC` (`wtNatC`,
   `≤ 401` for `n < 2^200`) and `wtGatherC` (`407` per index):
   * prepare `≤ 2^95` (dominated by the evaluator templates, `3 · 16 K³ N K ≈ 2^93.6`),
   * digits `≈ 2^98.35` (`2^22` rows × three gathers of `≤ 2^66` indices — the real floor of
     this program shape), correction `≤ 2^93` (`2^66` coordinates × `3 (K+1) 407`),
     assembly `≤ 2^75`, acceptance `≤ 2^69`, candidate `≤ 2^70`, invalid branch `≤ 2200`;
   * `keyProgram.size ≤ 2^115 + 2^114`, guarded program + loader `≤ 2^116`
     (the length guard `tailsP` is `≈ 60 · 2^103`).

   `6 · 2^116 · 3^105 · 541 ≤ 2^295`.

Further reduction would need a different program shape (the `2^22 · 2^66` unrolled gather
indices of the public rows dominate).

## 2. Clock

`validP = enterP ; keyPrepareC ; sampleP ; candidateTryC ; packKeyC ; post`; the rest of the
machine (parser `2^230`, length check `2^250`, invalid branch `2^254`, frame `2^250`, guard
`≤ 2^300`) is F3's, recomposed in `KeyTightFront` (`+4` bits over the valid branch).

* **Preparation / public evaluator, step 1** (`KeyTightEval`): F3's generic evaluator theorems
  re-instantiated at the cap `2^120` with *exact* numeric bounds (`decide +kernel` on the closed
  time expressions) instead of F3's rounded `norm_num` chains: chain `< 2^391` (F3 `2^422`),
  matrix product `< 2^386` (F3 `2^412`), coefficient routines `< 2^358` (F3 `2^376`),
  `evalC ≤ 2^420`, `keyPrepareC ≤ 2^422` (F3 `2^461`).
* **Preparation, step 2** (`KeyTightChain`, `KeyTightEval2`): the evaluator envelope with the two
  counters tracked (`rKc ↦ gD Dc = 9`, `rTK1 ↦ K - 1`, exact template lengths by
  `EvalLengths.kc/tk1`); tight leaves (binary ring ops at `operationBound M N K 0`, counted ops at
  the counter bound, single-word moves at `(2M+3)(20+10NK)`, drops at `(2M+3)(20+10C)`); the
  digit counter `rUp := rTK1` is certified through `layout_copy_update` so the digit instruction
  sees `≤ K`. Digit body `< 2^226`, matrix product `< 2^280` (F3 `2^412`), inverse product
  `< 2^264`, chain `< 2^335` (now `chPre`'s digit instruction with counter `rS` at the cap),
  `j`-step `≤ 2^358 + 2^350` (the coefficient routine `cfA`, `< 2^358`, dominates),
  `evalC ≤ 2^384 + 2^378`, **`keyPrepareC ≤ 2^384 + 2^381`**.
* **Real-trapdoor correction** (`KeyTightCorr`, generic in `D M I`): per coordinate the queue
  automorphism and the inner product use RedKeyT's tight kernels (`rktAutQC`, `rktIpC`) with the
  actual length `K` (F3 charged `2^66`) and exponent bound `2N`: `≤ 2^269` per coordinate at the
  cap `2^121`, `≤ 2^336` for all `|PIdx| ≤ 2^66` (F3 `2^484`).
* **Attempt** (`KeyTightTail`, cap `2^150`, RedKeyT's Dc-level certificates verbatim):
  candidate `2^397`, digits `2^433`, correction `2^390`, assembly `2^373`, acceptance `2^371`,
  total `2^435` (superseded, file removed). **`KeyTightPubY`/`KeyTightTailY`**: the same at the cap `2^121` (mechanical
  port of RedKeyT's Dc-level files, names suffixed `Y`, exponents re-targeted from `#eval`s):
  public rows `< 2^372`, digits `< 2^373`, candidate `< 2^339`, acceptance `< 2^335`,
  attempt `≤ 2^374` (try) + coins `2^236` + packing `2^249`.
* **Machine**: `validP ≤ 2^384 + 2^382`, both branches `≤ 2^384 + 2^383`, `keyProgram ≤ 2^384 +
  2^383 + 2^252`, guarded `≤ … + 2^253`, total `≤ 2^385` (sums `2^a + 2^b` are carried through
  every composition step; rounding to `2^k` at each step had cost 9 bits).

### Kernel / elaboration lessons (new)

* `rfl`/`rw` equations between a concrete-`Dc` time term and its numeral form blow the
  elaborator's recursion limit; state the equation generically (`tStepT_eq (D) (M I) : tStepT D M
  I = tStepNK D.N D.K M I := rfl`), then `rw [tStepT_eq, rkN, rkK]` and close the closed numeral
  goal with `decide +kernel`.
* `decide +kernel` evaluates the closed time expressions in seconds (GMP); it replaces long
  `calc`/`gcongr`/`norm_num` chains and gives exact bounds.
* `omega` treats `S * (expr with variables)` as an atom: keep per-item weights opaque
  (`corrCoordW`).
* Instances: indices of `PIdx` in F3's definitions use `Classical.propDecidable`; supply the
  instance explicitly (`@Enum.index_lt _ _ (fun a b => Classical.propDecidable (a = b)) _`) or
  let unification fill it (`refine le_trans (Nat.add_le_add (wtLoadFamilyC _ …) …) ?_`).

## 3. Where the remaining time goes, and the next steps

Now (`T1 = 385`): the preparation (`2^384`) dominates; inside it the `16 · 2^22` `j`-steps are
dominated by F3's coefficient routine `cfA` (`< 2^358`, about `2^28` ring instructions charged
at the counter cap `2^329` each); next come `matAddC` (`< 2^348`), `agC` (`< 2^346`), the chain's
`chPre` digit instruction (`22 × 2^329`) and the two single instructions of a `j`-step
(`2 × 2^329`). The attempt (`2^374`) is next: `negativeReadyC` (`< 2^348` per row × `2^22`
rows) and `decomposeRows` (`< 2^370`), again instructions charged at the cap.

Next steps, same technique as `KeyTightChain` (tight leaves + counter tracking):

1. `cfA`/`cfV` (`KeyTimeCoefFlexible`, `KeyTimeCoefA/V`, `KeyTimeBitLoop`): binary ops at
   count `0`; the `rot` counter is `rTb` (`= 22`, already in the envelope), the `rho` counter
   `rCnt` (`≤ 2^14`). Expected `j`-step `≈ 2^348` (then `matAddC`), evaluator `≈ 2^374`.
2. `matAddC` (binary add, moves) and `agC`: expected `≲ 2^270`; with `chPre` (copy-update trick
   for `rS := rTb`, counter `≤ 22`) and the two `j`-step instructions tight, the evaluator would
   drop to `≈ 2^330`, and the attempt (`2^374`) would dominate.
3. Attempt: `negativeReadyC` (`powersBody`'s binary add charged at the cap) and
   `digitQueueBody` (`dig` with counter `rU`, binary `sub`) → expected `≈ 2^330`; then the
   public-row gathers (`2^22 · 3 · 2^313`) and the correction (`2^336`) dominate, `T1 ≈ 2^340`.
