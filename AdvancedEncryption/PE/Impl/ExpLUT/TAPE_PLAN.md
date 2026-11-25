# Fewer physical tapes: packing the logical tapes of an `XProg` onto a few machine tapes

Status file of the tape-reduction work (see the bottom for what is done).

## Problem

`descLen = 6 · S · 3^k · (4 + 4k + size S)` charges the full transition table. The ExpLUT machines
are compiled from `XProg k` with one physical tape per logical tape, so `k = 326` (Enc), `256`
(Dec), `105` (KeyGen), `128` (Setup): `3^326 ≈ 2^516.7` alone. With `S ≈ 2^105` states, Enc's
`descLen ≈ 2^635` is the dominant term of `Ncost = 2^636`.

## Alternatives considered

(a) **TM-level simulation of an arbitrary `k`-tape `MultiTapePTM`** (tracks / blocks on few tapes).
Rejected: a generic simulator must gather the `k` head symbols before it can look up the
transition, so its finite control needs `≈ 3^k` states (the table has to live somewhere). The
`3^k` factor moves from the tape count into the state count; `descLen` does not drop. Only
*structure* of the transition function (each primitive reads ≤ 3 tapes) can be exploited, and that
structure is visible in the program, not in the machine.

(b) **Re-compile the program** so that logical tapes are delimited segments of one physical "store"
tape, and every primitive (or every *narrow* sub-program) runs on a few unpacked "workspace" tapes.
Chosen. The existing compiler and its correctness proofs are reused unchanged for the narrow
parts (frames of width `≤ w` and narrow `Prog` leaves); only the glue is new.

## Design

### Store layout (generic, `SigabaNeo/Lib/Machines/Pack/…`)

A logical store `S : Fin K → List Bool` is kept on physical tape `0` as

  `pkW S = encodeTuple (List.ofFn S) = frame (S 0) ++ … ++ frame (S (K-1))`

(`frame u` = every bit `b` as `[true, b]`, then `[false]`; a plain Bool word, so physical stores are
ordinary `RunsWords` stores and all cslib/Prog combinators apply). `|pkW S| = Σ (2|S i| + 1)`.

Physical tapes (`c = base + w + D`): `0` the store, a few scratch/flag tapes for the segment phases,
a test tape `T`, the workspace `W 0 … W (w-1)`, and one loop-counter tape per nesting depth
`F 0 … F (D-1)` of the *wide* loops.

### Target language `ZProg c` (generic)

`XProg c` plus **certified native phases** (`Phase c`: a machine, a store function `f`, a
precondition, a per-store time, and a `RunsWords` proof). Constructors: `xp (p : XProg c)`,
`ph (P : Phase c)`, `seq`, `ifBlank`, `ifBit`, `loop`. Compiled exactly like `XProg`
(`seq`, `branch`, `branchBit`, `repeatUntilBlank`), with:

* `ZProg.law` – denotation (phases are point masses `pure (f s)`);
* `ZProg.HT p Pre t` – a **Hoare-style time judgment**: from every store satisfying `Pre` the
  compiled machine halts within `t` steps (leaves: `timeBoundT` from a `Fits` bound / the phase
  time; `seq` through an intermediate predicate; loops through an invariant). This replaces the
  static per-tape bound propagation of `XProg.timeBoundT`, which would be far too weak on the store
  tape (a `put` changes `|pkW S|` in a way only the logical semantics knows).
* `compile_runsWords : HT p Pre t → Pre s → (compile p).RunsWords x s out₀ t (sample (denote p s)) …`
  and the explicit machine `toMachineZ` with `run_toMachineZ` (same statement shape as
  `XProg.run_toMachineT`).

Segment phases (native, linear time `O(|pkW S|)`):

* `get j t`: `W t := S j` — the existing `trPhase` with a finite transducer `τ_get j`
  (states `O(j)`), `6 |pkW S| + 16` steps.
* `put j t`: `pkW S := pkW (update S j (W t))`, `W t := []` — three transducer passes
  (`τ_pre j`, `frame`, `τ_suf j`) whose *outputs* are concatenated by running them in sequence
  under `outputToWord` (needs a non-tidy `RunsWords.outputToWord` generalisation of
  cslib-frontier's `ComputesTidily.outputToWord_of_le`, re-proved in a new file), then
  clear-and-copy back to tape `0`. `O(|pkW S| + |W t|)` steps.

(A slower fallback needs no new machine at all: `get`/`put` as `XProg c` programs built from the
verified `unfrP`, `frameApP`, `appT`; `O(|pkW S|²)` per call.)

### Translation `pack : XProg K → ZProg c` (generic)

`tr σ d p` for `p : XProg k`, an embedding `σ : Fin k ↪ Fin K` (composed frames) and loop depth
`d`:

* `k ≤ w` (narrow) → **leaf group**: `get (σ j) (W j)` for all `j`, then `xp (frame W p)` (the
  old compiled machine, unchanged), then `put (σ j) (W j)` back.
* `frame e q` (wide) → `tr (e.trans σ) d q`.
* `prog q` (wide `Prog k`) → narrowed by the set of tapes it mentions (`Prog.map` + restriction)
  if `≤ w`, otherwise exploded structurally (`Prog` control = `XProg` control; primitives and coins
  are narrow leaf groups of width `≤ 3`).
* `seq` → `seq`; `ifBlank i` → `get (σ i) T ; ifBlank T (clear T ; ·) (clear T ; ·)`; `ifBit`
  likewise; `loop i body` → `get (σ i) (F d) ; loop (F d) (tailSeg (σ i) ; tr σ (d+1) body)`.

**Law theorem** (`Sim`): for every physical store `P` with `P 0 = pkW S` and the other tapes
blank (except the counters of enclosing loops, which are preserved),
`(tr σ d p).law P = (p.law (S ∘ σ)).map (fun a => update P 0 (pkW (embedF σ S a)))`.
Proved by induction on `p` from the laws of the phases and of `XProg.frame`; no correctness proof
of the ExpLUT algorithms is touched.

### Top-level machine

`packMachine p i₀ o n` = load `x` on a scratch tape, build `pkW (inputStore i₀ x)`
(`K-1` empty frames around `frame x`), run `tr id 0 p`, `get o` onto a scratch tape, emit it.
**`run_packMachine`**: `(packMachine p i₀ o n).run x = (p.law (inputStore i₀ x)).map (· o)` for
`|x| ≤ n` — the right-hand side of `XProg.run_toMachineT`, so every ExpLUT `…Spec` proof transfers
by rewriting with it instead.

### Bounds

* **States**: `card ≤ card p.State + (#leaf groups) · O(w · K)` (each `get`/`put` transducer has
  `O(K)` states); since every leaf group already has `≥ 1` state, `S' ≤ O(w·K) · S`.
* **Time**: per executed leaf group an overhead of `O(w · (|pkW S| + 1))`, i.e.
  `O(w · (2 Σ_t ℓ_t + K))` for the current logical bounds `ℓ`. For a wide `Prog` leaf whose
  primitives sweep all `K` tapes (cost `≥ 2 maxLen + 3 ≥ (|pkW S| - K)/K`), the slowdown is
  `O(K)` — the classical `O(T·k)` simulation. For narrow frames executed inside wide loops the
  overhead is relative to the store size, so `w` should be chosen so that hot inner loops are
  narrow (the descLen allows `w` up to ≈ 100 before it matters).

## Expected new costs (estimates, to be confirmed by the ExpLUT bound proofs)

`c = 5 + w + D`. With `w = 32`, `D ≤ 8` (`c ≤ 45`): `3^45 ≈ 2^71.3`, entry width `≈ 4 + 180 + 110`.

| machine | old time / descLen | new descLen (est.) | new time (est.) |
|---|---|---|---|
| Enc (326) | 2^253 / 2^635 | `6 · 2^~110 · 3^45 · 2^8.2 ≈ 2^192` | `≤ 2^253 · O(K) ≈ 2^266` (core is a wide `Prog 326`) |
| Dec (256) | 2^225 / 2^447 | `≈ 2^(2.6+~38+71.3+8) ≈ 2^120` | `≈ 2^225 · O(K) ≈ 2^238` |
| KeyGen (105) | 2^385 / 2^295 | unchanged (time-dominated; packing optional) | unchanged |
| Setup (128) | 2^241 / 2^233 | unchanged (time-dominated) | unchanged |

So `Ncost` would drop from `2^636` to the KeyGen clock `≈ 2^385` (next bottleneck).
(The `O(K)` time factor is the worst case of the core's full-width sweeps; the `S'` estimate
assumes the large literal readers are narrow `Prog` leaves after restriction, otherwise
`S' ≤ 2^105 · O(wK) ≈ 2^120` and descLen `≈ 2^202`, still negligible.)

## Implementation status (end of session 1)

**The generic transformation is complete**: correctness, clock and state count, with no extra
hypotheses beyond well-formedness and a loop-depth bound. Not yet applied to the ExpLUT machines.

All new files are under `SigabaNeo/Lib/Machines/Pack/` (3.4k lines). No existing file was edited;
nothing imports them yet. Build from the repository root, e.g.
`lake build SigabaNeo.Lib.Machines.Pack.States SigabaNeo.Lib.Machines.Pack.MachineT`.
No `sorry` and no `native_decide`. Every headline theorem uses only the axioms
`propext, Classical.choice, Quot.sound` (checked with `#print axioms`).

| file | content |
|---|---|
| `ZProg.lean` | `Phase k` (a certified native phase), `ZProg k` (XProg leaves, phases, control), `law`, the Hoare-style time judgment `HT`, `compile`, **`compile_runsWords`**, `toMachineZ`, **`run_toMachineZ`** |
| `Seg.lean` | `pkW` (the packed store), the segment transducers `getT`/`preT`/`sufT`/`frT`, **`run_getT_pkW`**, `putW`, **`putW_pkW`**, `length_pkW` |
| `Restrict.lean` | `Prog.law_map` (the law of a relabelled program, coins included), `Prog.tapes`, `Prog.localize`, **`Prog.law_localize`**, `kIter_map_embed` |
| `OutWord.lean` | **`RunsWords.outputToWord_of_le`**: cslib-frontier's tidy `outputToWord` lemma, generalised to any `RunsWords` phase |
| `SegPhases.lean` | native phases **`getPh`** (the `trPhase` of `getT`, `6·|E| + 16` steps) and **`putPh`** (three transducer emissions → `outputToWord` → copy back, `putTime E U ≤ 30(E+U)+60`), with their `RunsWords` proofs |
| `Translate.lean` | `Layout`, `Kit`, `Clean`, `Sim`, `lift`; leaf groups (**`sim_leaf`**), `sim_seq`, `sim_ifBlank`/`sim_ifBit`, `tailZ`, **`sim_loopZ`** |
| `Tr.lean` | the translation `tr`/`trP`, depth conditions `OkX`/`OkP` (implied by `loopDepth`: `okX_of_loopDepth`), **`sim_tr`**, **`law_tr`** |
| `Machine.lean` | the concrete `packLayout w D` (`5 + w + D` tapes) and `packKit`, `topZ`, **`law_topZ`**, `packMachine`, `run_packMachine` (takes `HT` as a hypothesis) |
| `TimeLeaf.lean`, `TimeTr.lean`, `TimeMain.lean` | `Phys` (physical stores), `leafT`/**`ht_leaf`**, `testT`/`ht_testZ`, `tailZT`/`ht_tailZ`, `loopT`/**`ht_loopZ`**, `ptime`/`ptimeP` and **`ht_tr`** |
| `MachineT.lean` | `topTime`, **`ht_topZ`**, `packMachineT`, **`run_packMachineT`**, `time_packMachineT` |
| `States.lean` | the cards of the phases, **`card_tr_le`**, **`states_packMachineT_le`** |

### Headline statements

```lean
-- MachineT.lean: the drop-in replacement for XProg.run_toMachineT
theorem run_packMachineT (hw : 3 ≤ w) (p : XProg K) (hp : OkX w D 0 p) (hwf : p.WF)
    (i₀ o : Fin K) (n : ℕ) (x : List Bool) (hx : x.length ≤ n) :
    (packMachineT w D p i₀ o n).run x = (p.law (inputStore i₀ x)).map (fun s => s o)

theorem tapes_packMachineT : (packMachineT w D p i₀ o n).tapes = 5 + w + D
theorem time_packMachineT : (packMachineT w D p i₀ o n).time =
    (2 * n + 2) + topTime w D p i₀ o n + (2 * XProg.lenBoundT p (Prog.inputBound i₀ n) o + 2)

-- States.lean
theorem states_packMachineT_le : (packMachineT w D p i₀ o n).states ≤
    stA w K * p.size + 96 * K + 254     -- stA w K = w * (36 K + 214) + 12 K + 143
-- (XProg.size p = card of the old states, XProg.card_state; old machine: size + 4 states)

-- Tr.lean: the depth condition, from the loop nesting depth
theorem okX_of_loopDepth (d : ℕ) (p : XProg k) : d + XProg.loopDepth p ≤ D → OkX w D d p
```

`topTime w D p i₀ o n = timeBoundT (snocN st false K) (…) + putTime K n +
ptime w refl 0 p (inputBound i₀ n) 0 + (6 · Lam (Lafter refl p (inputBound i₀ n)) + 16)`.
`ptime` follows the translation node by node (`TimeMain.lean`):

* a narrow frame/program `q` (`k ≤ w`, or a `Prog` leaf mentioning `≤ w` tapes) costs
  `leafT σ q L M = m(6 Λ + 16) + timeBoundT q (L ∘ σ) + m · putTime (Λ(L ⊔ L')) (supB ℓ') + 2 max(Λ L', M) + 3`
  with `Λ = Lam L = Σ_i (2 L i + 1)` (a bound on the packed store), `m ≤ w`;
* `seq` adds, propagating the logical bound by `Lafter σ p L = embedF σ L (lenBoundT p (L ∘ σ))`;
* a wide `ifBlank`/`ifBit` costs `6 Λ + 16 + 2 max(Λ, M, L j) + 4` plus the larger branch;
* a wide `loop i b` costs `6 Λ + 16 + L(σ i) · (2 max(Λ*, M') + 3 + tailZT + ptime b Λ* + 1) + 2`,
  `Λ*` the invariant bound `iterSupT` (as `XProg.timeBoundT` does).

So the overhead is linear in the packed store size per leaf execution; no quadratic step.

## Expected new costs (estimates, not yet proved for ExpLUT)

descLen with `S' ≤ stA w K · S_old` states and `c = 5 + w + D` tapes:
`descLen ≈ 6 · stA · S_old · 3^c · (4 + 4c + log S')`.

| machine | old time / descLen | new descLen, `w = 16`, `D ≤ 8` (`c ≤ 29`, `stA ≈ 2^17.6`) | new time (estimate) |
|---|---|---|---|
| Enc (`K = 326`, `S ≈ 2^105`) | 2^253 / 2^635 | ≈ 2^(2.6 + 105 + 17.6 + 46 + 8) ≈ **2^180** | ≈ 2^253 · 108K ≈ **2^268** if the time is dominated by the wide `Prog 326` core (each primitive: old `2 maxLen + 3`, packed `≈ 36·3·Λ ≤ 108 K (2 maxLen + 1)`); narrow frames executed inside wide loops pay `O(w Λ)` per execution instead |
| Dec (`K = 256`, `S ≈ 2^28`) | 2^225 / 2^447 | ≈ 2^(2.6 + 28 + 17.3 + 46 + 7) ≈ **2^101** | ≈ 2^225 · 2^15 ≈ **2^240** |
| KeyGen (105) | 2^385 / 2^295 | not needed (time-dominated) | unchanged |
| Setup (128) | 2^241 / 2^233 | not needed | unchanged |

`Ncost` would then be dominated by the KeyGen clock (`2^385`) instead of `2^636`.
A larger `w` (up to ≈ 100 before `3^c` matters) keeps more frames native and lowers the time.

## Remaining work

1. **ExpLUT side (new `Prog/Tape*.lean` files)**: define `encMP' := packMachineT w D (encProgram …) 0 0
   (encInputLength D)` (likewise Dec), get `EncSpec` from `run_packMachineT` exactly as
   `encSpec_encMP` does from `XProg.run_toMachineT`, and prove:
   * `OkX w D 0 (encProgram …)`, via `okX_of_loopDepth` and a bound on `XProg.loopDepth` (a
     syntactic recursion; for `NoGrow` word algorithms `Prog.loopDepth p + 1 ≤ Prog.tbD p`, not yet
     stated);
   * `XProg.size (encProgram …) ≤ 2^105 + 2^101` is already proved (`size_encProgram_tight`), so
     `states_packMachineT_le` gives the descLen bound immediately (arithmetic only);
   * the clock: a numeric bound on `ptime`. Suggested generic lemma (not yet proved):
     *if every bound reached along `p` (the `L`s of `ptime`'s recursion) is `≤ Lmax` pointwise
     and `M ≤ Lmax`, then `ptime w σ d p L M ≤ (1 + c₀ · w · (Lam Lmax + 1)) · (timeBoundT p (L ∘ σ) + 1)`*,
     using that every node of `XProg.timeBoundT` costs `≥ 1` and every overhead is
     `O(w · Lam Lmax)`. Alternatively mirror the existing tight `timeBoundT` proofs (`EncTight…`)
     for `ptime`.
2. Optional optimisations: share one `get`/`put` sweep for all `m` segments of a leaf group (one
   pass instead of `m`); keep the segments of consecutive leaf groups unpacked when their tape
   sets coincide; a smaller constant in `putTime` (the final copy-back via `putTail` sweeps 3×).
3. Optional: apply to KeyGen/Setup if their descLen ever dominates.

## Implementation status (end of session 2): Enc and Dec packed, all bounds proved

No `sorry`, no `native_decide`; every headline theorem uses only `propext, Classical.choice,
Quot.sound`. Nothing existing imports the new files (the aggregator / `Submission*` are untouched).

**Generic (`SigabaNeo/Lib/Machines/Pack/`)**
* `Restrict.lean` (edited): now imports `Prog/AbsBound` and drops its duplicate `Prim.map_map` /
  `Prog.map_map` (they clashed with `AbsBound`, so no file could import both before).
* `Det.lean`: `CoinIndep` through the plumbing; **`deterministic_packMachineT`** (coin-free ⇒
  `Machine.Deterministic`).
* `MapBound.lean`: `Prog.lenBoundT_map`, `Prog.timeBoundT_le_map`, `embedF_trans'`.
* `Flat.lean`: `ovT w K T` (one leaf overhead), judgments `FX`/`FP` ("packed clock ≤ old
  `timeBoundT` + n·ovT", rules `leaf`, `narrow`, `seq`, `frame`, `prog`, `mono`),
  `time_packMachineT_le`, **`descLen_packMachineT_le`**.
* `FlatLoop.lean`: absolute judgment `FXa` with `of_FX`, `seq`, `prog`, **`loop`** (wide loops,
  invariant = bound after the loop, `iterSupT_gX`), `ifBlank`, `ifBit`; **`time_packMachineT_le'`**.
* `Leaves.lean`: narrowness from tape lists (`narrowP_of_subT`, `narrowP_map`), `loopDepth_map`,
  `loopDepth_putW`, length closure `BndP`, `FP.leafB`, `FXa.prim`, `FXa.narrowProg`, `FXa.frame`,
  `Lafter_ifBit`, `iterSupT_le_add`.

**ExpLUT (`Prog/Tape*.lean`)**

| machine | w, D, tapes | spec | clock | descLen |
|---|---|---|---|---|
| `TapeEnc.encMachineP` | 105, 8, 118 | `encSpec_encMachineP` | `time_encMachineP : ≤ 2^253` | `descLen_encMachineP : ≤ 2^325` |
| `TapeDec.decMachineP` | 37, 8, 50 | `decSpec_decMachineP` (incl. determinism) | `time_decMachineP : ≤ 2^356` | `descLen_decMachineP : ≤ 2^137` |

* Enc (`TapeEnc`, `TapeEncTime`): with `w = 105` the parser/sampler and the four core phases are
  single native leaves charged their old clocks; the suffix is flat (`fp_suffix`, ≤ 1000 leaves);
  the ciphertext framing's wide loop by `FXa.loop`. Same clock as before (2^253).
* Dec (`TapeDec`, `TapeDecVM`, `TapeDecTime`): VM instructions are flat (≤ 4 frames, all
  non-lengthening, `fx_instr`); `absRun_soundP` mirrors `DecT.absRun_sound` with the packed clock
  `fD · T`, `fD = 1 + 4·ovT 37 256 2^110 ≈ 2^131`, and `dtP_decCode` mirrors the block glue. The
  clock is therefore crude: `2^131 · dtTvm ≈ 2^355`.
* Resulting costs: Enc `2^325`, Dec `2^356`; `Ncost` would become the KeyGen clock `2^385`.

**Remaining / possible improvements**
1. Integration (parent): switch `Submission*` to `encMachineP`/`decMachineP`.
2. Dec clock: replace the multiplicative factor by an additive count (packed ≤ old + ovT·#leaf
   executions) — needs an instruction-counting abstract run (a variant of `DecT.absRun` returning
   the number of executed instructions, re-checked block by block); expected ≈ 2^240.
3. Enc descLen: `D = 8` only because `OkP` counts loops inside narrow `Prog` subtrees; refining
   `OkP` to stop at narrow subtrees would allow `D = 1` (−11 bits). A smaller `w` needs a
   packed analysis of the core phases (the old tight proofs are via `TB`/`Sound`).
