# Predicate encryption for branching programs: executable plan

> **Status: complete.** `PE/Impl/RingBTVW/Submission.lean` proves `spec_submission` and
> `valid_submission` for `BranchingProgram.primitive` with no hypotheses (axioms `propext`,
> `Classical.choice`, `Quot.sound`): attribute hiding from decision Ring-LWE at 965 bits
> (`attributeHiding_conf_rlwe`, `keyRConfA`; certified strength 2650 at `N = 2^36`,
> `q = 2^(2^27)`), cost `N = 2^818` (`cost_implC`). The sections below are the plan as executed;
> §12 records the switch.

Status: plan (2026-11-23), branch `t3/bp-design`, base `c47c58f4`. Nothing below is implemented
and nothing was built for this plan. Numbers marked "est." are hand or floating-point estimates;
numbers with a declaration name are from the code at `c47c58f4`.

Decisions of the owner that this plan implements:

1. **Strategy A′**: the scheme stays BTVW17 §4.2 literally. `f̂` is the Boolean program of the
   Ring-GSW evaluation of a NAND circuit of the predicate; the predicate circuit is a mux tree; the
   noise bound becomes depth-based. (The linear evaluation of the earlier draft is dropped.)
2. A key is **authorized iff the output bit is `0`**.
3. The date-window primitive **is deleted and overwritten**: its trusted file, its front end and
   its numbers are replaced in place.

## 0. Summary

| | Date windows (proved, `c47c58f4`) | Branching programs (this plan) |
| --- | --- | --- |
| attribute | 10 bits | 128 bits (16 symbols of 8 bits) |
| predicate circuit | ≤ 375 NAND gates | `1443 · 2^39 − 770 ≈ 2^49.49` NAND gates, depth `1054` |
| noise exponent | `375 · log₂ G` (gates) | `1054 · log₂ G` (depth), `G = gswFactor ≤ 2^48440` |
| ring degree `N` | `2^34` | `2^36` |
| `K = log₂ q`, `k` | `2^25`, `K + 1` | `2^27`, `K + 1` |
| `d = \|Wd\|` | `2^61` | `2^65` |
| flooding width `w` | 512 | 768 |
| Ring-LWE strength used / certified | 2645 / 2650 | 2645 / 2650 (same ratio `N / K = 2^9`) |
| clocks (Setup, KeyGen, Enc, Dec) | `2^355, 2^557, 2^416, 2^556` | est. `2^387, 2^629, 2^452, 2^629` |
| description lengths | `2^300` (Setup, Enc), `2^1000` (KeyGen, Dec) | `2^300`, est. `2^946`–`2^951` |
| cost `N` | `2^1002` | est. `2^952`; `2^1002` holds with today's rounding |

What makes it work:

* **Depth instead of size** in three lemmas (`nb_fhatSLP`, `noiseBound_le`,
  `rnorm_rowOf_simKeyMat_le_closed`); the definitions `noiseBound`, `simKeyMat`, the scheme and
  the security proof do not change (§3).
* **The circuit is a register program**: NAND instructions on 183 registers, emitted in post-order
  of the mux trees. Its unfolding is the SLP of the math layer; the machines run it with a store of
  312 bundles, fewer than the 513 they hold today. No machine and no proof ever holds or
  enumerates the `2^49.5` gates (§2, §5).
* **The cost of the `W_f` block is a certificate in two numbers of the circuit family**: the
  instruction count bound `2^50` and the store width 512. It is computed as today (`absC` on the
  code of the word machine, checked by `decide +kernel` on numerals) and holds for every
  instruction stream within those bounds (§5.3).
* **The estimator needs no restructuring**: it never materialises `q` (§4.3).

## 1. The trusted problem file

`PE/BranchingProgram.lean` replaces `PE/DateWindow.lean` (deleted at the switch, §7). It imports
`PE` only.

```lean
namespace AdvancedEncryption.PE.BranchingProgram

/-- An 8-bit symbol. -/
abbrev Sym := Fin 256
/-- A 32-bit state. -/
abbrev State := Fin (2 ^ 32)
/-- An attribute: 16 symbols. -/
abbrev Attr := Fin 16 → Sym

/-- The 8 bits of a symbol, most significant first. -/
def symBits (s : Sym) : List Bool := List.ofFn fun i : Fin 8 => s.val.testBit (7 - i.val)

/-- The 128 bits of an attribute: symbol 0 first. -/
def encAttr : Attr ↪ List Bool := ⟨fun x => (List.ofFn x).flatMap symBits, _⟩

/-- A branching program: 15 transition tables and an output table. -/
structure BP where
  step : Fin 15 → State → Sym → State
  out : State → Sym → Bool

/-- The state before the last step: `z₀ = 0`, `z_{i+1} = step i z_i x_i`. -/
def run (F : BP) (x : Attr) : State :=
  Fin.foldl 15 (fun z i => F.step i z (x i.castSucc)) 0

/-- The output bit `F(x)`: the last table at `(z₁₅, x₁₅)`. -/
def output (F : BP) (x : Attr) : Bool := F.out (run F x) (x (Fin.last 15))

def bpUniverse : Universe where
  Attr := Attr
  Msg := Bool
  encAttr := encAttr
  encMsg := encMsg                    -- one bit, encoded as itself
  Req := BP
  req F x := output F x = false       -- authorized iff the bit is 0
  desc := []

/-- `λ = 128`, `κ = 128`, one run of each algorithm. -/
def params : Params := ⟨128, 128, 1, 1⟩

def primitive : Primitive := AdvancedEncryption.PE bpUniverse params
```

* The class is Definition 2 of the manuscript (`predicate-encryption-paper-2026`,
  `sections/preliminaries.tex`, `def:bp`) at `T = 16`, `w = 2^32`, `|Σ| = 256`, `ℓ = 16`,
  `ι(i) = i`, i.e. mxx's `PeClass::new(16, 256, 2^32, 16)`. `State → Sym → State` is exactly the
  set of tables of `2^40` entries of 32 bits.
* Bit `0` authorizes, as in BTVW17 (`C(x) = 0`), the manuscript and mxx; the class is closed under
  complementing `out`, so nothing is lost.
* The representation of predicates stays the implementation's, as `PE.lean` prescribes (§2.4).
* Checks of the definition: `(encAttr x).length = 128`; a small program (equality with a fixed
  string, as a DFA with a dead state) with one accepted and one rejected attribute; the all-reject
  program. Statements over `Sym` may use `decide` (256 cases); nothing may enumerate `State`.

## 2. The predicate circuit

### 2.1 Register programs

New, generic (`SigabaNeo/Lib/Lattices/Homomorphic/RegProg.lean`):

```lean
/-- A source: an input, the constant `1`, or a register. -/
inductive Src (ι : Type*) (W : ℕ) | input (i : ι) | one | reg (r : Fin W)
/-- `dst := NAND(a, b)`. -/
structure Instr (ι W) where (dst : Fin W) (a b : Src ι W)
abbrev RP (ι W) := List (Instr ι W)

/-- Run on any type of values: registers start at the value of `1`. -/
def RP.run (inp : ι → α) (one : α) (step : α → α → α) : RP ι W → (Fin W → α) → (Fin W → α)
/-- The unfolding: instruction `t` is gate `t`; a register is the wire of the last gate written
to it (`Wire.one` if none). -/
def RP.toSLP : RP ι W → SLP ι × (Fin W → Wire ι)

theorem RP.run_eq_valueOf (rp : RP ι W) (r : Fin W) :
    RP.run inp one step rp (fun _ => one) r =
      SLP.valueOf inp one step (RP.toSLP rp).1 ((RP.toSLP rp).2 r)
```

`run_eq_valueOf` holds for every value type, so one lemma gives the Boolean value
(`step = nand`), the depth (`ℕ`, `max a b + 1`, which is `SLP.depth`), the homomorphic values on
bundles (`fhatV`, the shadows of `Lib/Lattices/Algo/FhatShadow.lean`) and the noise bound. The
predicate of the math layer is `(RP.toSLP rp).1` with the wire of the output register, of type
`SLP (Fin 128) × Wire (Fin 128)`: `Setting.Pred`, `fhatSLP`, `keyMatrix`, `simKeyMat` are used
unchanged.

### 2.2 The mux-tree layout

Inputs: the 128 attribute bits, `x_{i,m}` = bit `m` (most significant first) of symbol `i`, input
index `8 i + m`. One step is a function of 40 bits: leaf index `u = 256 z + a` (state-major), so
the leaves of the tree for output bit `j` are bit `j` of the table entries in the order of the
predicate word.

**Selectors by level** (level 1 at the leaves): levels `1 … 8` select by the bits of the symbol,
least significant first (level `ℓ` uses input `8 i + (8 − ℓ)`); levels `9 … 40` by the bits of
the state, least significant first (level `9 + m` uses state bit `m`). Attribute bits are at the
bottom because they have depth 0; this order gives the least depth (65 per step; the reverse
order gives 79).

**Nodes.**

* Level 1 is not a gate: for the two leaf bits `(c₀, c₁)` of a pair, the value is the source
  `ZERO` if `(0,0)`, `one` if `(1,1)`, the selector `s₁` if `(0,1)`, its negation `¬s₁` if `(1,0)`.
* A node of level `ℓ ≥ 2` with children `lo` (selector 0), `hi` (selector 1) is three gates:
  `X1 := NAND(s_ℓ, hi)`, `X2 := NAND(¬s_ℓ, lo)`, `dst := NAND(X1, X2)`.

**Registers** (183): `ZERO`; state banks `Z₀[0..31]`, `Z₁[0..31]` (step `i` reads bank `i mod 2`
and writes bank `(i+1) mod 2`, so no copy is needed); negated state `NZ[0..31]`; negated symbol
bits `NA[0..7]`; `L_ℓ`, `H_ℓ` for `ℓ = 2 … 39` (the result of a level-`ℓ` node goes to `L_ℓ` if it
is a `lo` child and to `H_ℓ` if it is a `hi` child; the root of a tree goes to the output bank);
temporaries `X1`, `X2`. With the constant and the 128 inputs the store has `1 + 128 + 183 = 312`
slots; the store width is **`W = 512`** as today.

**Program** (`bpRP`):

```
ZERO := NAND(1, 1);  Z₀[j] := NAND(1, 1)  (j < 32)                       -- 33 gates, z₀ = 0
for i = 0 … 15:
  NA[m] := NAND(x_{i,m}, x_{i,m})  (m < 8);  NZ[j] := NAND(Z[j], Z[j])  (j < 32)    -- 40 gates
  for each output bit j (32 of them for i < 15; one for i = 15):
    tree(40) on the bits j of table i, root into the next bank (or OUT)   -- 3 (2^39 − 1) gates
```

where `tree(ℓ + 1) = tree(ℓ) into L_ℓ ; tree(ℓ) into H_ℓ ; node(ℓ + 1)` and `tree(2)` is one node
on four leaf bits. This is the post-order of the tree: an instruction reads only registers
written earlier, and at most one live value per level and side exists.

**Size**, exactly: a tree has `2^38` nodes of level 2 and `2^38 − 1` above, so
`3 (2^39 − 1)` gates;

```
|bpRP| = 33 + 15 · (96 (2^39 − 1) + 40) + (3 (2^39 − 1) + 40) = 1443 · 2^39 − 770
       = 793 297 639 439 614 ≈ 2^49.49
```

It does not depend on the program: every `F` gives the same shape; only the sources of the
level-2 nodes depend on the table bits.

**Depth**, exactly. Symbol bits have depth 0, `NA`, `ZERO` depth 1. A level-2 node has depth
at most 3; levels `3 … 8` add 2 each: 15. With the state at depth `δ` (`NZ` at `δ + 1`), the
level-9 node has depth `max(δ + 3, 17)` and levels `10 … 40` add 2 each: a step maps
`δ ↦ max(δ + 65, 79)`. From `δ₀ = 1`: `δ₁ = 79`, `δ_{i+1} = δ_i + 65`, `δ₁₅ = 989`, and the output
has depth **`D = 1054`**.

Rejected variants: Lupanov's construction (size `≈ 2^44`, same depth, a much longer proof; the
size does not enter the noise any more and the gate count is not what bounds `N`, §6); a special
first step using `z₀ = 0` (depth 990, 6 % less, but a second code path).

### 2.3 What is proved about the circuit (generic in the program, no enumeration)

With `bpPred F : SLP (Fin 128) × Wire (Fin 128)` the unfolding of `bpRP` at the output register:

```lean
theorem evalBool_bpPred (F : BP) (x : Attr) :
    SLP.evalBool (bitsOf x) (bpPred F).1 (bpPred F).2 = output F x
theorem depth_bpPred (F : BP) : SLP.depth (bpPred F).1 (bpPred F).2 ≤ 1054
theorem length_bpRP (F : BP) : (bpRP F).length = 1443 * 2 ^ 39 - 770
theorem bnd_bpRP (F : BP) : ∀ ins ∈ bpRP F, slots of ins < 312
```

All four are inductions over the levels of a tree and the 16 steps on `RP.run` (Boolean values,
depths, lengths), through `RP.run_eq_valueOf`. The tree lemma is stated for a leaf function
`(Fin ℓ → Bool) → Bool`, never for a table.

### 2.4 The predicate word and `Eval`

* `bpWord F`: the 15 tables, then the output table; entry `(z, a)` at index `256 z + a`; 32 bits
  per entry, most significant first; `bpLen = 15 · 2^40 · 32 + 2^40 = 481 · 2^40` bits
  (`≈ 2^48.9`). `tablesOf C` reads a word of `bpLen` bits back; every such word is a program.
* The class test of `KeyGen`, `Dec`, `Eval` and the game is `C.length = bpLen` (today
  `∃ w : Window, winWord w = C`); outside the class `KeyGen` gives the dummy key and `Dec`
  `[false]`, as today.
* `predC C := bpPred (tablesOf C)`.
* `Eval`: `bpEvalFun C x = [decide (C.length = bpLen) && !output (tablesOf C) x]`, a machine by
  `Machine.exists_of_almostConst` as `winEvalMachine` today (finitely many inputs). `Eval` is not
  counted in the cost.
* `Expressive`: `C := bpWord F`, by `evalBool_bpPred`.

### 2.5 How KeyGen and Dec obtain the circuit

They do not receive a gate list and no table of predicates exists (today `frontP` looks the word
up in a hard-wired table of all windows, `≤ 2^238` states). After the length test, a **compiler
program** writes the instruction stream

```
rpW W rp = rp.flatMap fun ins => unaryW W (slot ins.dst) ++ unaryW W (slot ins.a) ++ unaryW W (slot ins.b)
```

(slot 0 the constant, `1 … 128` the inputs, then the registers; the unary operand words of
`GateListLayout.gsW`, with a destination added) of `rpW 512 (bpRP (tablesOf C))` on the tape the
block reads: `3 · 512 · |bpRP| ≈ 2^60.1` bits, below the bound `2^64` the block's certificate
already assumes for its gate list. The compiler is code of the word machine without `gate`
instructions (§5.2), so its law and its time come from `law_compileA` and `costC`; est. `2^121`
steps, negligible.

## 3. The depth-based noise theorem

### 3.1 What exists

* `nb_nandBlock` (`Lib/Lattices/Homomorphic/GSWNoise.lean`): a NAND block maps bundles whose
  wires are within `A` to a bundle within `gswFactor WN N k · A`
  (`gswFactor = modFactor^(treeHeight + 1) · (WN + 1)`, `modFactor = (4k + 14)² (WN + 1)^10`).
* `nb_foldl_compileStep` keeps one bound `B` for all bundles, so `nb_fhatSLP` gives
  `gswFactor^(p.length) · E`.
* `noiseBound` (`RingBTVW/Noise.lean`) is defined from `slpBound` on `f̂` and `errBound` on the
  circuit of `f`; only its closed form `noiseBound_le` (`RingBTVW/NoiseClosed.lean`) and
  `rnorm_rowOf_simKeyMat_le_closed`, `simTrapBound`, `cnorm_simTrap_le`
  (`RingBTVW/Params/SimTrapNorm.lean`) mention `f.1.length`.
* `slpBound_le_depth` (`Lib/Lattices/Homomorphic/Depth.lean`): `slpBound WN E p w ≤
  (WN + 1)^(SLP.depth p w) · E` for a plain program; `SLP.depth` reads a missing gate as depth 0,
  as `repOf` reads it as the constant.

### 3.2 Statements

```lean
-- Lib/Lattices/Homomorphic/GSWNoise.lean
theorem nb_fhatSLP_depth {A : Type*} (hk : q < 2 ^ k) (p : SLP A) (w : Wire A) (b : BI N k) :
    nb WN E (fhatSLP (N := N) hk p w).1 ((fhatSLP (N := N) hk p w).2 b) ≤
      gswFactor WN N k ^ SLP.depth p w * E

-- PE/Impl/RingBTVW/Fresh/NoiseClosed.lean
theorem noiseBound_le_depth (Bχ K : ℕ) (f : SLP Attr × Wire Attr) :
    noiseBound (N := N) hk Bχ K f ≤
      Bχ + |Col k| * N * Bχ * K +
        |Col k| * N * ((|Fin 1 × Col k × Fin k × Fin N| * (|Col k| * N) + 1) *
          (gswFactor (|Col k| * N) N k ^ SLP.depth f.1 f.2 * Bχ)) * K

-- PE/Impl/RingBTVW/Params/SimTrapNorm.lean: `simTrapBound N k D` with `D` a depth
theorem cnorm_simTrap_le … : … ≤ simTrapBound N k (SLP.depth f.1 f.2)
```

**Proof of `nb_fhatSLP_depth`.** Generalise the invariant of `nb_foldl_compileStep` from
`∀ r ∈ reps, RepNB … r B` to `∀ m < reps.length, RepNB … reps[m] (G^(ds[m]) · E)`, with `ds` the
depths of the gates compiled so far (`SLP.run (fun _ => 0) 0 (fun a b => max a b + 1)`). For a
gate `g`, `repOf … g.a` and `repOf … g.b` are within `G^(d_a) E` and `G^(d_b) E` (an input: `E`;
the constant or a missing gate: `nb z ≤ E`); `RepNB.mono` to `A := G^(max d_a d_b) E` and
`nb_nandBlock` give `G^(max d_a d_b + 1) E`, the depth of the new gate. `nb_compileSLP` and
`nb_fhatSLP` follow as today. `noiseBound_le_depth` and the trapdoor bound replace `nb_fhatSLP`
by it and `slpBound_le_length` by `slpBound_le_depth` (with `le_gswFactor`). The old size-based
lemmas may stay or go.

### 3.3 Where it plugs in

* `Params/Sizes.lean`: `gswPow_le {n} (hn : n ≤ 1054) : gswFactor … ^ n ≤ 2 ^ 51055760`;
  `simTrapBound_le`, `realShift_le` with `Eτ`.
* `noise_ok (f) (hf : SLP.depth f.1 f.2 ≤ 1054) (S) (hS : S ≤ 2 ^ (Bp − 1)) :
  4 * noiseBound … (2 ^ w) S f + 2 < 2 ^ Kp`, through `noiseBound_le_depth`.
* `Params/Conf.lean`: `correct_conf` calls `noise_ok _ (depth_bpPred _) Sp Sp_le`;
  `goodTrap_sim` uses `simTrapBound_le (depth_bpPred _)`. `length_predC` (≤ 375) disappears.
* `decrypt_correct_of_bounds`, `cnorm_noise_le`, the hybrids and `Security.lean` are untouched.

## 4. Parameters `confA`

They overwrite the present values **under the present names** (`confP`, `Np`, `Kp`, `kp`, `dp`,
`Eτ`, `Bp`, `hkp`, …), to keep the diff of the 100-odd files that mention them small. A cosmetic
rename is the lead's choice at the end.

### 4.1 Values

| Name | Value | Why |
| --- | --- | --- |
| `Np` | `2^36` | `N / K = 2^9` (strength, §4.3) |
| `Kp`, `kp` | `2^27`, `2^27 + 1` | noise (§4.2) |
| `dp` | `2^65` | `2 K N + 1000 ≤ d` (`2 K N = 2^64`) |
| `nA` | 128 | attribute bits |
| `confP.w` | 768 | flooding (§4.4) |
| `Eτ` | 51055984 | `65 + 159 + 1054 · 48440` |
| `Bp` | 51056224 | `Eτ + 240` (abort) |
| `confP.L` | `481 · 2^40` | `bpLen` |
| `W` (store) | 512 | 312 slots used |
| instruction bound | `2^50` | `|bpRP| = 1443 · 2^39 − 770` |

Derived sizes (est. to `2^0.1`): wires `nJ = nA · 4k²N = 2^99`; row `2kNK = 2^91`;
`|mpk| ≈ 8 nA k³N²K = 2^190`; SimData `nJ · d · 2kNK = 2^255` (bound `Lb = 2^260`); joint value
`V = (1 + d) · 2kNK + NK = 2^156`; bundle `4k²N · V = 2^248`; store `513` bundles `= 2^257`; tape
bound `Mall = 2^262`.

### 4.2 Noise

In the style of `Params/Sizes.lean` (`k ≤ 2^28`): `WN ≤ 2^65`, `WN + 1 ≤ 2^66`,
`modFactor ≤ 2^62 · 2^660 = 2^722`, `treeHeight ≤ 66`, `gswFactor ≤ 2^(722 · 67 + 66) = 2^48440`,
`G^1054 ≤ 2^51055760`, `|rowBits| · WN + 1 ≤ 2^159`, `E = d · N · 2^w ≤ 2^869`. Then

```
noise ≤ 2^(65 + 159 + 51055760 + 869 + (Bp − 1) + 6) = 2^102113082 < 2^134217728 = 2^K
```

Margin 24 % of `K`: the depth could be up to 1385 at these `N`, `K`. Without the rounding,
`log₂ G ≈ 46132` and `K ≥ 9.73 · 10^7` would do (est.). `K` need not be a power of two, but a
power of two keeps `N / K = 2^9` exactly and the estimator scans as they are today.

### 4.3 Ring-LWE strength

Facts (`SigabaNeo/Lib/Lattices/Estimator/*`, `Params/Strength*.lean`):

* `q` is never materialised: `cbdP n e M` keeps `2^e` unevaluated and the scans receive
  `lq = e · ONE` (`Usvp.cost_eq_of_q`, `Dual.cost_eq_of_q`, `log2_ofInt_two_pow`,
  `Guess.mitmCost_eq`, `Bkw.cost_eq_none`, `Guess.exhaustiveCost_eq_none`). A larger `e` adds
  `log₂ e` bits to the integers of a scan. **No log-domain restructuring is needed.**
* The per-β checks depend on `log₂ δ(β*) ≈ K / (4N)` up to a term `O(70 / K)`: at `N / K = 2^9`,
  `β* ≈ 9312` and about 2656 bits are certifiable for `K ≥ 2^20` (est.), for any such `N`.
* Side conditions of the present instance: Arora–GB (`K₀ = 50`, `R = 2^20`) needs `n ≥ 2^27` and
  `kb ≤ 2 log₂ C(n − 549, 51)` (`≈ 3232` at `n = 2^36`); `56 · M ≤ (n − 600) · 2^120`
  (`M5 ≈ 2^101`); `e ≥ 1024`; `n ≥ 10050`; the constant `W = 90` caps `kb` at 2669. All hold.
* Hard-coded: `ringParams3`, `ringParams5`, `inDomain_of`, `H_ge_of_bits`, `two_le_q`,
  `params3_eq`, `params5_eq` (`Params/Strength.lean`) and `chk3`, `chk5`
  (`Params/Strength/Check.lean`) fix `N = 2^34`, `2^(2^25)`, 2650.

**Strength needed.** `attributeHiding_of_comps_rlwe` needs `64 · (2^128)² · C ≤ 2^kb`.
`AHConcrete.const_le` proves `C ≤ 2^2383` from an envelope `t = 2376` on the per-query time,
whose real content is the uniform key-try bound `20000 (2M + 1)^8` (`2^2045` at `M ≈ 2^251`) and
the block time `T ≤ 2370`. At `confA`: `T ≈ 629` and the key try gives `2^(8 · 263 + 15) = 2^2119`
at `Mall = 2^262` (est.). Both fit the same envelope (it tolerates `Mall ≤ 2^293`), so
**`kb = 2645 ≤ 2650` stays as it is** (`prem3`, `prem5`, `valid_submission` keep their numbers).
Fallback if a bound grows: the per-tape key-try bound of `KeyTightTry` in the reduction's key
component (`kb ≈ 1100`).

**Plan.** `chk3 = cbdCheck (2^36) (2^27) M3 2650` with `M3 = 2^36 · (2^28 + 2)` and
`chk5` with `M5 = 2^36 · (2^65 + 2^29 + 5)`; the 16 scan files regenerated on the same β ranges
(132 `decide +kernel` evaluations; ≈ 11 min of kernel time per `docs/LWE_ESTIMATOR.md`); the
lemmas of `Strength.lean` for the new numbers. The scans are the first thing to run: they are
independent of everything else and confirm §4.1.

### 4.4 Statistical terms

`GameChain.lean` sums over the attribute: `statTerm = |Attr| · (3 δ₁ + ε + δ₆)` with
`|Attr| = 2^128` (today `2^10`), and `hstat` needs `4 · 2^128 · statTerm² ≤ 1`, i.e.
`statTerm ≤ 2^-65`.

* Leftover hash lemma (`Params/Stat.lean`, `lhl_le`): today `|JC|, |HC| ≤ 2^120` and a slack of
  600 bits give `2^-180`. Now `|JC| = nJ · 2k = 2^127`: restate with `|JC|, |HC| ≤ 2^130` and
  `2 K N + 1000 ≤ d`: `δ₁, δ₆ ≤ 2^(130 − 500) = 2^-370`.
* Flooding (`flood_conf`): `ε ≤ |JC| · N · (d · N · 16) / 2^w = 2^(127 + 36 + 65 + 36 + 4 − 768)
  = 2^-500`. (`w = 512` would give `2^-244`, enough but thin; the width costs nothing.)
* `statTerm ≤ 2^128 · 2^-368 = 2^-240`.
* Abort (`abortP`): `|Coef| · (4τ + 1) · 2^128 ≤ 2^Bp` with `|Coef| ≤ 2^102`: `Bp = Eτ + 240`.
* `Fintype.card Attr = 2^128` is proved by `Fintype.card_fun`, never by evaluation.

## 5. Machines

### 5.1 KeyGen and Dec shells

`keyGenP`, `decGenP` keep their structure (`Prog/KeyGenP.lean`, `Prog/DecGenP.lean`): load and
parse, class test, the block through `bfX` / `cfX` on crafted simulation data, key try or
decoding. Changes:

* class test: compare the length of the predicate word with a template of `bpLen` bits made by
  `natP` (`O(log)` states); the table lookup `frontP` and its `2^238` states disappear;
* the compiler (§5.2), framed on its own tapes, writes the instruction stream on the block's
  input tape;
* `BfSpec`, `CfSpec`, `WfSpec`: the hypotheses `C.length ≤ c.L`, `∃ w, winWord w = C` become
  `C.length = bpLen`, and the block's input `gsW W (parse C)` becomes
  `rpW W (bpRP (tablesOf C))`.

### 5.2 The compiler and the authorization program

Both are `Code` of the word machine (`Lib/Machines/Prog/ValVM.lean`) with `cp`, `mv`, `drop`,
`tl`, `rep`, `ifb` only, so `law_compileA`, `wf_compileA` and `costC` apply.

* **Compiler** `bpCompC`: for each step and output bit, one pass over the table extracts the leaf
  bits (drop `j` bits, take one, drop `31 − j`) into a word of `2^40` bits; `treeC ℓ` is defined
  by recursion on `ℓ` in Lean as `rep TWO_ℓ (treeC (ℓ − 1))` followed by the emission of the three
  instructions of the node, the destination `L_ℓ` or `H_ℓ` chosen by the iteration (a flag word
  per level); `treeC 2` reads four leaf bits and emits one node with sources chosen by them. The
  code has 38 nested loops and linear size; its law is proved by induction on `ℓ` against the
  recursive definition of §2.2, so no equivalence between a recursive and an iterative traversal
  is needed. Register indices are built from a level word, not from one template per register
  (the machine has 120 words; about 80 are loop counters and flags).
  Law: the output word is `rpW 512 (bpRP (tablesOf C))`. Est. time `2^121`, every word below
  `2^61` bits.
* **Authorization** `authBPC` (for the reductions and the handlers, replacing `authL`): 16 table
  lookups; the state is expanded to unary by doubling and the table is advanced by
  `256 z + a` entries. Output `[decide (C.length = bpLen) && !output (tablesOf C) x]`. Est. time
  `2^99`.

### 5.3 The `W_f` block for a parametric circuit family

Today (`Prog/WfB2*.lean`, `Lib/Lattices/ProgAlgo/Val*.lean`): `gloopC blk` runs the gates of a
list on a store that holds **every** gate's result (`W + 1` slots, `|gs| + 10 ≤ W`); `nandC` is
the NAND block on bundles; `absC` computes the word bounds and the step count of the code from
the input bounds; `chk_r1`, `chk_r2`, … check them at numerals by `decide +kernel`; the gate
rounds charged are `3W − 1 = 1535`.

Changes:

1. **Register loop** `rloopC blk` (new `Lib/Lattices/ProgAlgo/ValReg.lean`): per instruction, read
   the operands `a`, `b` from the store by their unary slot words (`rdC`), run `blk`, write the
   result back to slot `dst` (split the store at `dst`, replace one slot). Store:
   `C :: ins ++ regs`, 312 slots padded to `W + 1`.
   ```lean
   theorem exec_rloopC (hB : BlockSpec V f blk S F Ctx) (rp : RP …) (hbnd : slots of rp ≤ W) … :
       exec V f (rloopC blk) w GST = (C :: ins ++ regs (RP.run … F rp)).flatten ++ padding ∧ …
   ```
   and, by `RP.run_eq_valueOf`, slot `OUT` holds `SLP.valueOf` of the unfolded program: with
   `blockSpec_nandC` this is `bw (fhatV …)` (the present `getLast_gl_nandW`), with
   `blockSpec_gate` the predicate's Ring-GSW simulation (`gl_values`).
2. **Inputs** (`ValIns.insC`, `ValGsw.insGC`, `ValMain`): the template `T10` and the literals
   `10` become a template of `nA` bits.
3. **`wfB2`** (`Prog/WfB2.lean`): `countP`/`capP` count instructions (`3W` bits each) and cap the
   count at a template of `2^50`; `runT`, `runG` use `rloopC`; the output is the slot `OUT`
   instead of the last gate; `simKeyP` and the rest are unchanged. `wfSpec_wfB2` for every
   instruction stream with slots `≤ W` (so for every program, by `bnd_bpRP`).
4. **Cost.** The write-back is a sequence of existing instructions, so `absC` and
   `inv_compileA` apply without new certified primitives. The certificate is the present one at
   new numerals: `Nc = 2^36`, `Kc = 2^27`, `dc = 2^65`, `Wc = 512`, `nA = 128`, `Lb = 2^260`,
   stream `≤ 2^64` bits, gate rounds `≤ 2^50`, `Mall = 2^262`. `time_wfB2_conf` then holds **for
   every instruction stream within these bounds**; the circuit family enters through the two
   lemmas `length_bpRP` and `bnd_bpRP` only. The lists `L1c`, `L1Gc` are recomputed by kernel
   reduction as today (minutes; the integers are a few hundred digits).

Est. numbers: one gate round `≈ 2^575.4` (today `2^539.4`; it scales as
`treeHeight · N^5 K^4 k^5 d²`), of which the store accesses are `≈ 2^514`; run of `f̂`
`≤ 2^50 · 2^575.4 = 2^625.4`; `simKeyP` `≈ 2^592.5`; the predicate's Ring-GSW run far below.
**Block `≤ 2^628`.**

### 5.4 Setup and Enc

No loop is unrolled over the attribute today: `Setup` draws the `B_j` as one run of coins and
`encCoreP` runs counted loops with templates `(22, 10)`, `(27, 10 · 4k)`, … and reads the
attribute by `ufChunk 5 10`. The literal `10` becomes `nA` in the programs, the layouts
(`FixedEnc.fun (α := Fin 10)`), the closed forms (`nBj = 8 nA k³N²K`) and the certificates
(`check_encCoreP`, `wE_num`, `TightChain.chk_*`); the attribute word is 16 chunks of 8 bits.

## 6. Cost estimate

`descLen A = 6 · states · 3^tapes · 3^ops · entryBits` (`Trusted/Machine.lean`); the proofs use
`descLen ≤ 6 B · 3^tapes · (4 + 4 tapes + B)` for a state bound `B` (`descLen_arith`).

| | Today (proved) | `confA` (est.) | Driver |
| --- | --- | --- | --- |
| Setup clock | `≤ 2^355` | `2^386.3` | `78 n²`, `n = 8 nA k³N²K = 2^190` |
| Enc clock | `≤ 2^416` | `2^450.5` | `(2G + 3) · 44 N²K²k · 4 nA k²N` |
| KeyGen clock | `≤ 2^557` | `≤ 2^629` | the block `2^628`; key try `(2T + 3) · wKR` below |
| Dec clock | `≤ 2^556` | `≤ 2^629` | the block; `ballP` `419 (M + 1)³ ≈ 2^595` |
| Setup, Enc descLen | `≤ 2^300` (96, 124 tapes) | `≤ 2^300` | `natP` templates, constants below `2^240` |
| KeyGen descLen | `≤ 2^1000` (formula `2^908`) | `2^943.5`–`2^948.5` | `B ≈ 1600 X`, `X ≈ 2^257`: `6 B · 3^256 · (1028 + B)` |
| Dec descLen | `≤ 2^1000` | `2^945.5`–`2^950.5` | `B ≈ 3200 X` |
| **`N`** | **`2^1002`** | **`≈ 2^952`** | the two description lengths |

* The state counts of KeyGen and Dec are linear in the SimData length `X` (offsets hard-wired bit
  by bit by `getAt`, `prefP`, `putW`), and the bound is quadratic in them; the gate count
  (`2^49.5`) and the clocks do not matter. The lower figures use the formula directly, the upper
  ones today's margins (`2^13`, `2^14` above `X`).
* `cost_arith` with the new clock exponents and the same `2^300`, `2^1000` gives **`2^1002`
  again**; with the exponents the formulas give, `≈ 2^952`. The plan proves the second and falls
  back to the first.
* Not in the plan: `Nat.size S ≤ log₂ S + 1` in `descLen_arith` would give `≈ 2^690`.

## 7. Layout and rules

**Overwrite in place.** One implementation in the tree. Deleted at the switch: `PE/DateWindow.lean`,
`PE/Impl/Gates/{DateWindow, ProgWindow, WindowBound, WindowTest, AuthGen, AuthProg}.lean`,
`Prog/{Auth, AuthL, KeyFront, WfPred}.lean`, and whatever of `Prog/{WfB, WfIns, FhatGen}.lean`,
`Lib/Machines/Prog/GateGen.lean`, `Lib/Lattices/ProgAlgo/FhatGen*.lean` is no longer imported.
Existing names are kept where the role is kept (`confP`, `Sdw`, `predC`, `wfB2`, `implC`,
`submission`, …).

**Two stages**, so that implementers work in a green tree as long as possible:

* **Stage I (green, still date windows).** Day 1, WS1 adds neutral names in `ImplBase.lean`:
  `abbrev nA : ℕ := 10`, `ValidC C := ∃ w : Window, winWord w = C`, `blockWord W C :=
  gsW W (parse C)`, `PUniv := dateUniverse`, with `Sdw` over `Fin nA`. Every workstream then
  replaces `Fin 10`, the literal `10`, `∃ w : Window, …`, `gsW W (parse C)`, `dateUniverse` by
  these names **in its own files**, turns its statements into closed forms in `N, K, k, d, nA`
  and the instruction bound, and adds its new files. Everything still builds, so each merge is
  checked by a full build.
* **The switch (lead, one commit).** `nA := 128`; `ValidC C := C.length = bpLen`;
  `predC := bpPred ∘ tablesOf`; `blockWord W C := rpW W (bpRP (tablesOf C))`;
  `PUniv := bpUniverse`; the values of §4.1 in `Params/Sizes.lean`; the deletions above.
* **Stage II (repair, bottom-up).** Each workstream re-establishes its instance lemmas and
  numerical certificates at `confA` in its own files; merges in the order of §8.

**Rules for every workstream.**

1. Generic first: a statement is proved for variable `N, K, k, d, nA` (and the instruction bound)
   with hypotheses, then instantiated. No tactic runs on a `confP` constant; `Kp`, `Np`, `dp`,
   `Eτ`, `Bp` stay `irreducible_def`.
2. Nothing enumerates `State`, `Attr`, a table, the circuit, or `Fin nA × …`; `decide +kernel`
   is for numerals and for fixed program shapes only.
3. A file has one owner (§9). A change needed in another owner's file is requested from the
   lead.
4. Commits end with the repository's trailer; never push; never bare `git stash`.
5. Builds: a worktree with `.lake/packages` symlinked to a shared copy takes ≈ 2.4 GB built; one
   with its own packages ≈ 16 GB. With 28 GB free every worktree symlinks packages, and finished
   worktrees are removed. A cold build of `AdvancedEncryption` is ≈ 1 h: build your own modules
   (`lake build PE.Impl.…`); the lead runs full builds at merges.

## 8. Milestones

| | Content | Who | Needs |
| --- | --- | --- | --- |
| M0 | `PE/BranchingProgram.lean`; `RegProg.lean` definitions and `run_eq_valueOf`; neutral names in `ImplBase.lean`; tree green | WS1 | — |
| M1 | `nb_fhatSLP_depth`, `noiseBound_le_depth`, trapdoor bound by depth | WS2 | — |
| M2 | `ringLWE_H` ≥ 2650 at `(2^36, 2^27)` by the scans | WS3 | — |
| M3 | circuit: `evalBool_bpPred`, `depth_bpPred`, `length_bpRP`, `bnd_bpRP`; word, `Eval`, expressiveness lemma | WS1 | M0 |
| M4 | `exec_rloopC` and its link to `SLP.valueOf`; compiler law; authorization law | WS6, WS7 | M0 |
| M5 | Stage I complete: every file on neutral names and closed forms; full build green | all | M0 |
| M6 | switch; math layer green; **`correct_conf`, `expressive_conf` for branching programs** (abstract machines) | lead, WS1, WS2 | M1, M3, M5 |
| M7 | compiled machines: `run_setupMP`, `run_encMP`, `wfSpec_wfB2`, KeyGen/Dec laws; `implC`; `Correct`, `Expressive` for `implC` | WS4–WS7 | M4, M6 |
| M8 | clocks, sizes, description lengths at `confA`; `cost_implC` | WS4–WS6 | M7 |
| M9 | `attributeHiding_conf_rlwe`; `spec_submission`, `valid_submission` | WS8, lead | M2, M8 |

M0–M4 touch new files or add lemmas, so they are green within days and independent of each other.

## 9. Workstreams

Common to all: read §2 (circuit), §4.1 (numbers), §7 (stages, rules). "Stage I" and "Stage II"
are those of §7. Sizes are rough.

### WS1 — Problem, circuit, class (math)

* **Goal.** The trusted file, the circuit with its four theorems, the predicate word, `Eval`, and
  the switch of the math layer from date windows to branching programs.
* **Owns.** New: `PE/BranchingProgram.lean`,
  `SigabaNeo/Lib/Lattices/Homomorphic/{RegProg, MuxTree}.lean`,
  `PE/Impl/Gates/{BPCircuit, BPWord}.lean`. Existing: `PE/Impl/RingBTVW/{ImplBase, Impl,
  ImplCorrect, Codec, GameChain, SimKeyGame, SimGame, SimGame3, SimGame5}.lean`,
  `PE/Impl/RingBTVW/Algo/*`, `PE/Impl/Gates/*` (the window files until they are deleted),
  `PE/DateWindow.lean` until it is deleted, `AdvancedEncryption.lean`, the READMEs.
* **Does.**
  1. Day 1: §1 as written; `RegProg.lean` (`Src`, `Instr`, `RP`, `run`, `toSLP`,
     `run_eq_valueOf`, `rpW`); the neutral names of §7 in `ImplBase.lean`. This fixes the
     interfaces of WS5–WS8.
  2. `MuxTree.lean`: the tree of §2.2 for any number of levels over an abstract leaf function and
     abstract selector sources; its Boolean value (the leaf at the index given by the selectors),
     depth (`max(δ_sel + 3, δ_leafside + 2)` per level, as in §2.2), length `3 (2^(ℓ−1) − 1)`,
     slot bound.
  3. `BPCircuit.lean`: `bpRP`, `bpPred` and the four theorems of §2.3. `BPWord.lean`: `bpWord`,
     `tablesOf`, `bpLen`, `bpEvalFun`, `bpEvalMachine`, `bp_authorized_iff`, `expressive_bp`,
     `encAttr_onto` (every word of 128 bits is an attribute), `card_attr`.
  4. Stage I in its files. At the switch (with the lead): `keyTry`, `decM`, `correct`,
     `expressive`, `Impl.lean`, the game chain for `bpUniverse`; `bitsOf x` is the 128 bits of
     `encAttr x`.
* **Acceptance.** M0, M3; after the switch `RingBTVW.correct` and `RingBTVW.expressive` for
  `bpUniverse` under the parameter hypotheses they have today, with `Machines` abstract. Axioms
  `propext`, `Classical.choice`, `Quot.sound`.
* **Needs.** Nothing. **Size.** ≈ 2.5k new lines, ≈ 15 files edited.

### WS2 — Depth-based noise and parameters

* **Goal.** §3 and the configuration at the numbers of §4.
* **Owns.** `SigabaNeo/Lib/Lattices/Homomorphic/{GSWNoise, Depth}.lean`,
  `PE/Impl/RingBTVW/{Noise, NoiseClosed}.lean`, `PE/Impl/RingBTVW/{Noise, ConcreteNoise, Concrete,
  ParamSupport}.lean`, `PE/Impl/RingBTVW/Params/{SimTrapNorm, Sizes, Conf, Stat, Advantage}.lean`.
* **Does.**
  1. M1: the three statements of §3.2 by the proof of §3.2 (additive; the tree stays green).
  2. Stage I: `noise_ok`, `gswPow_le`, `simTrapBound_le`, `goodTrap_*`, `abortP`, `correct_conf`
     stated through named bounds (`Dmax`, the exponents) so that only numerals change later;
     `lhl_le` with the bounds `2^130` and a slack parameter; `flood_conf` in `c.w`.
  3. Stage II: the values of §4.1; the chain of §4.2 (`WN_le`, `modFactor_le`, `treeHeight_le`,
     `gswFactor_le ≤ 2^48440`, `gswPow_le`, `R_le`, `RW_le`, `E_le`, `noise_ok`); `Eτ`, `Bp`,
     `hτM`, `hBp`, `abortP`; `KN2_le : 2 K N + 1000 ≤ d`, `delta1_le`, `delta6_le ≤ 2^-370`,
     `flood_conf ≤ 2^-500`, `statTerm` inputs; `correct_conf`, `expressive_conf`, `goodTrap_real`,
     `goodTrap_sim` for programs with `depth_bpPred`.
* **Acceptance.** M1; then M6: `correct_conf : Correct bpUniverse params (impl hkp confP ms)` and
  `expressive_conf`, no hypothesis.
* **Needs.** `depth_bpPred` (WS1) for the last step only; the number 1054 is fixed now.
  **Size.** ≈ 400 new lines for M1, ≈ 10 files edited.

### WS3 — Ring-LWE strength

* **Goal.** `2650 ≤ RingLWE.H` for the two instances at `N = 2^36`, `q = 2^(2^27)`.
* **Owns.** `SigabaNeo/Lib/Lattices/Estimator/**`, `PE/Impl/RingBTVW/Params/Strength.lean`,
  `PE/Impl/RingBTVW/Params/Strength/*`.
* **Does.** First, as an experiment in new files: `cbdCheck (2^36) (2^27) M 2650` on a few
  ranges of β around `β* ≈ 9312` and at both ends, for `M3 = 2^36 · (2^28 + 2)` and
  `M5 = 2^36 · (2^65 + 2^29 + 5)`; report the margin. Then `Check.lean`, the 16 scan files,
  `cbdFacts`, `ringParams3/5`, `inDomain_of`, `two_le_q`, `H_ge_of_bits`, `params3_eq`,
  `params5_eq`, `ringLWE_H_registry3/5` at the new numbers, with `N`, `e`, `M`, `kb` as arguments
  of the generic lemmas. Keep the old files until the switch (new names or a branch merged at
  the switch).
* **Acceptance.** M2: `ringLWE_H_registry3`, `ringLWE_H_registry5` at the parameters of `confA`.
  If 2650 fails, report the largest certified value; the strength needed is ≈ 2400 (est., §4.3).
* **Needs.** Nothing. **Size.** ≈ 20 files regenerated, ≈ 200 lines of lemmas.

### WS4 — Setup, Enc and the block library

* **Goal.** `Setup` and `Enc` for `nA` attribute bits with their laws, sizes and clocks.
* **Owns.** `Prog/{SetupP, SetupCost, SetupCostP, SetupEncCost, SetupTime, SetupTime3, TightSetup,
  TightChain, TightConf, TightApp, TightB1, TightC0, B1, C0, Chi, Core, Fields, Finish, Lift,
  Place, Layout, Blocks, WordLemmas, UBound, UBLoop, CostTools, Flip, EncBits, EncCore,
  EncCoreCert, EncCostConfT, EncCostP, EncCostT, EncP, EncPsi, EncSem, PsiBits, SchemeWords,
  SchemeWords2, CostConf, SizeConf}.lean`.
* **Does.** Stage I: `10 → nA` in the templates of `EncP.tmplList`, `ufChunk`, the layouts
  `FixedEnc.fun (α := Fin 10)`, the closed forms (`nW_eq`, `nR_eq`, `nPsi_eq`, `nCj_eq`,
  `nBj_eq`); the certificates `check_encCoreP`, `wE_num`, `TightChain.chk_*`, `setupF_conf`
  restated with the template lengths as variables. The attribute is read as `nA` bits whatever
  its symbol structure. Stage II: the numerals of `confA`; flooding width 768.
* **Acceptance.** `run_setupMP`, `run_encMP` for `nA = 128`; `time_setupMP_conf'`,
  `time_encMP_confT`, `descLen_setupMP_conf`, `descLen_encMP_conf` at `confA` (expected
  `2^387`, `2^452`, `2^300`, `2^300`).
* **Needs.** The neutral names (day 1). **Size.** ≈ 40 files edited.

### WS5 — KeyGen and Dec shells, sizes, description lengths

* **Goal.** The compiled `KeyGen` and `Dec` around a block given by its spec, with clocks and
  description lengths.
* **Owns.** `Prog/KeyFront.lean` until it is deleted; `Prog/{KeyP, KeyGenP, KeyGenCost, KeyCfgP, KeyCostC, KeyCostConf, KeyCostP, KeyPTime,
  KeyPTime2, KeyPTimeT, KeyTightBfX, KeyTightConf, KeyTightGen, KeyTightLib, KeyTightPost,
  KeyTightPre, KeyTightTry, KeyTightWin, KeyTryReal, KeyTryRealLaw, Post, PostCost, PostSize, BfX,
  BfXCost, BlockCost, SizeCost, CfX, Decode, DecodeCost, DecodeLaw, DecodeWord, DecFin,
  DecGenCost, DecGenP, DecP, DecCostConf, DecTightCf, DecTightConf, DecTightFin, DecTightGen,
  DecTightLib, DecTightPost, DecTightPre, DescConf}.lean`, `PE/Impl/RingBTVW/ImplP.lean`.
* **Does.** Stage I: `BfSpec`, `CfSpec`, `WfSpec` on `ValidC` and `blockWord`; the front end
  behind an interface `FrontSpec` (a program with law "`[]` if too long, `[false]` if not
  `ValidC`, `true :: blockWord W C` otherwise" and its time, tape and size bounds), instantiated
  by `frontP`; all clocks and sizes as closed forms in the bounds of the front end and of the
  block. Stage II: the front end is the length test followed by the compiler of WS7
  (`law_frontBP` from `law_bpCompC`); `KeyTightWin`, `frontL` go; numerals of `confA`;
  `DescConf` (`ksz_arith`, `dsz_arith` at `X = 2^257`).
* **Acceptance.** `keyMachineP`, `decMachineP` laws (`key_short`, `key_long`, `dec_law`) from
  `WfSpec` for programs; `time_keyMachineP_conf'`, `time_decMachineP_conf'` (expected `≤ 2^629`),
  `descLen_keyMachineP_conf`, `descLen_decMachineP_conf` (expected `≤ 2^951`, at worst `2^1000`).
* **Needs.** WS1 (names), WS6 (`WfSpec` statement, block bounds), WS7 (compiler law and bounds).
  **Size.** ≈ 45 files edited.

### WS6 — Register evaluator and the `W_f` block

* **Goal.** §5.3: `wfB2` on instruction streams, with law, size and the time certificate.
* **Owns.** `SigabaNeo/Lib/Lattices/ProgAlgo/Val*.lean` and new `ValReg.lean`,
  `SigabaNeo/Lib/Machines/Prog/{ValVM, CountP}.lean`, `Prog/{WfB2, WfB2CoinFree, WfB2Conf,
  WfB2Inst, WfB2Size, WfB2Time, WfLib, WfTime, KeyWfWords, KeySumStore, SimKeyStore}.lean`
  (`WfB`, `WfIns`, `WfPred`, `FhatGen` are deleted when nothing imports them).
* **Does.**
  1. `ValReg.lean`: `rloopC`, the register semantics `rl`, `exec_rloopC`, and `rl` as
     `SLP.valueOf` of `RP.toSLP` (through `RP.run_eq_valueOf`); the instances with
     `blockSpec_nandC` and `blockSpec_gate` replacing `getLast_gl_nandW` and `gl_values`.
     Independent of the rest; this is M4.
  2. Stage I: `nA` in `ValIns`, `ValGsw`, `ValMain`, `ValFhat` (template of `nA` bits instead of
     `T10`); `wfB2` on `rloopC` with the instruction count capped at a template; the output slot;
     `wfSpec_wfB2` for any stream with slots `≤ W`; `coinFree_wfB2`; `size_wfB2`. During Stage I
     `blockWord` is still the gate list: provide `gsW`-to-stream as the trivial register program
     (gate `t` writes register `t`) so the tree stays green.
  3. Stage II: the certificate at the numerals of §5.3 (`L0c`, `L1c`, `L1Gc`, `chk_*`),
     `time_wfB2_conf`, `size_wfB2_conf`, `wfB2_confP`, `wfCost_wfB2`, with `length_bpRP`,
     `bnd_bpRP`, `treeHeight ≤ 66`, the offsets (`offs_conf`).
* **Acceptance.** M4; `wfSpec_wfB2_confP` for programs; `timeBoundT (wfB2 hkp confP 512) ≤
  2^628` (expected), every tape `≤ 2^262`, size `≤ 2^25`, for SimData `≤ 2^260` and streams
  `≤ 2^64` bits of at most `2^50` instructions.
* **Needs.** `RegProg.lean` (day 1). **Size.** ≈ 1.5k new lines, ≈ 15 files edited; the largest
  workstream.

### WS7 — Compiler and authorization programs

* **Goal.** §5.2: the two programs with laws and bounds.
* **Owns.** New `PE/Impl/RingBTVW/Prog/{BpComp, BpCompLaw, BpCompCost, AuthBP}.lean` (and
  `SigabaNeo/Lib/Machines/Prog/` helpers it adds, in new files).
* **Does.** `bpCompC` as in §5.2 with `law_bpCompC : exec … = rpW 512 (bpRP (tablesOf C))` for
  `C.length = bpLen`, well-formedness, coin-freeness, and `costC` bounds for a predicate word of
  `bpLen` bits; `authBPC` with its law and bounds; the length test `lenEqP`. The pure functions
  it must match are WS1's (`bpRP`, `tablesOf`, `output`).
* **Acceptance.** M4 (laws); bounds: time `≤ 2^130`, tapes `≤ 2^64`, size `≤ 2^20` (expected) for
  the compiler; time `≤ 2^110` for the authorization.
* **Needs.** WS1's definitions (day 1 for `RP`, `rpW`; `bpRP` within the first days).
  **Size.** ≈ 2.5k new lines.

### WS8 — Reductions and attribute hiding

* **Goal.** The reductions' components for `nA` bits and programs, and attribute hiding at
  `confA` from Ring-LWE.
* **Owns.** `PE/Impl/RingBTVW/{Reduction*, AH*, Registry, Security, Hybrid*, SimKeys, IdealBridge,
  RealBridge, IdealViews, FinalView}.lean`, `PE/Impl/Game/*`, `Prog/{Setup3, Setup5, SetupI,
  SetupL, SetupLaws, Pub3, Pub5, Chal3, Chal5, ChalI, ChalITime, Sd3, RowSimP, KeyTrySim,
  KeyTrySimLaw, Comps, CompCost}.lean`; `Prog/{Auth, AuthL}.lean` until they are deleted.
* **Does.** Stage I: `10 → nA` in the components and their closed forms; `Game/HandlersDate`
  generalised to the universe behind `PUniv` (codes with `nA` bits, `encAttr_onto`); the
  authorization component behind an interface (law, time, size), instantiated by `authL`;
  `statTerm` with `Fintype.card PUniv.Attr`. Stage II: `HandlersBP`; authorization by `authBPC`
  (WS7); the constants of `AHConcrete` (`compConst_le_two_pow` with the program sizes and tape
  bounds of `confA`; the envelope `t = 2376` is expected to hold, §4.3); `statTerm_conf` with
  `2^128` (§4.4); `attributeHiding_conf_rlwe`.
* **Acceptance.** M9: `attributeHiding_conf_rlwe 2645` for `bpUniverse` from the two `HardAt`
  hypotheses; if the envelope fails, the smallest `kb` that the bounds give and whether WS3
  certifies it.
* **Needs.** WS1 (universe), WS4 (blocks), WS5 and WS6 (key component bounds, `WfCost`), WS7
  (authorization), WS2 (`Stat`), WS3 (numbers). **Size.** ≈ 35 files edited.

### Lead

Owns the files no workstream lists (the generic scheme: `PE.lean`, `PE/Impl/Bridge.lean`,
`PE/Impl/RingBTVW/{Scheme, Laws, Security, Simulation}.lean`, `PE/Impl/RingBTVW/{Scheme,
Correctness, KeyGen, KeyBoxes, Flooding, Trapdoor, SetupLaw, BitLaws, Encodings}.lean`); no change
is expected there. Reviews the day-1 interfaces; merges Stage I branches after a full build; makes the switch
commit; merges Stage II in the order WS2 → WS1 → WS4 → WS6, WS7 → WS5 → WS8; owns
`PE/Impl/RingBTVW/Submission.lean` (`implC`, `cost_arith` with the new exponents, `cost_implC`,
`spec_submission`, `valid_submission` for `BranchingProgram.primitive`).

### Dependencies

```
WS3 ───────────────────────────────────────────────┐
WS2 (M1) ──────────────┐                           │
WS1 (M0) ─┬─ WS1 (M3) ─┼─ switch ─ M6 ─┬─ WS4 ─┐   │
          ├─ WS6 (M4) ─┤               ├─ WS6 ─┼─ WS5 ─ M8 ─ WS8 ─ M9
          └─ WS7 (M4) ─┘               └─ WS7 ─┘
```

## 10. Risks

1. **Noise margin** (24 % of `K` with rounded bounds). If a constant is lost: the special first
   step (`D = 990`), or a larger `K` at the price of the ratio `N / K` (then the strength).
2. **Strength margin**: ≈ 2656 certifiable against 2650 claimed, as today; the bits actually
   needed are ≈ 2400 (est.), and ≈ 1100 with the per-tape key-try bound.
3. **Description lengths** est. `2^946`–`2^951` against the rounding `2^1000`: every doubling of
   the SimData length costs 2 bits; `d = 2^65` (rather than `2^64 + 1000`) costs 2 of them.
4. **Certificates of the block**: the nesting of the code does not change and the rounds are a
   numeral, so the kernel work should be as today; to be confirmed early in WS6 Stage II by
   evaluating `absC` at the new numerals before proving anything about them.
5. **Word budget of the compiler** (120 words of the word machine against ≈ 80 loop words): if
   short, the compiler becomes a plain `Prog` with its own tapes and a hand-proved law.
6. **Hidden dependence on the value 10** in kernel-checked certificates (`check_encCoreP`,
   `TightChain`, `KeyTightConf.pEval_*`): found at Stage I, where the tree is still green.
7. **`statTerm` with `2^128`**: the constants of `Params/Stat` change (§4.4); the lemmas do not.

## 11. Open point for the owner

* **The cost claim**: prove `≈ 2^952` (the formulas' exponents) or keep the statement `2^1002`
  with today's rounding. The plan aims at the first and accepts the second.

## 12. Switch and Stage II status (lead, branch `t3/bp-switch`)

### Done (commits `b1940271`, `aed92e0a`, tree not green yet)

* `ImplBase`: `PUniv := bpUniverse`, `nA := 128`, `ValidC C := C.length = bpLen`,
  `predC C := bpPred (tablesOf C)`, `attrBits x := bitsOfBP x` (the old `bitsOf` of dates; the name
  `bitsOf` stays `RingBTVW.bitsOf`), `attr0`, `bit0 C := output (tablesOf C) attr0`,
  **`blockWord W C := bit0 C :: RP.rpW W (bpRP (tablesOf C))`** (see below), `evalBool_predC`,
  `export BPWord (bpLen tablesOf)`, `export BranchingProgram (output)` (beware: the project has
  `autoImplicit` on — an unknown name such as `bpLen` silently becomes a variable).
* Deleted: `PE/DateWindow`, `Gates/{DateWindow, ProgWindow, WindowBound, WindowTest, AuthGen,
  AuthProg}`, `Prog/{Auth, AuthL, WfPred}`, `Concrete`, `Game/HandlersDate` (`head_paramsWord`
  moved to `HandlersBP`). `Prog/KeyFront` rewritten (generic `KGsim_eq_front`, `authI_eq` for
  programs). The date-front instances `keyGenP`, `keyMachineP`, `decGenP`, `decMachineP` (and their
  laws) are removed from `KeyGenP`/`DecGenP`; `keyP` removed from `KeyP` (`law_keyPF`,
  `law_keyP_spPack` take any front end with `FrontSpec`).
* Math layer: `Impl` (`bpEvalMachine`, `correct_of_scheme (hL : bpLen ≤ c.L)`, `expressive`),
  `ImplCorrect`, `GameChain`, `RealBridge`, `SimKeyGame`, `SimGame*`, `AHAssembly`, `IdealBridge`,
  `AHMath`, `Algo/*`. `Params/Sizes` at confA values (WS2 table), `Params/Conf`
  (**`correct_conf`, `expressive_conf` for `bpUniverse`**, `confP.L = bpLen`, `eCoef = 102`),
  `Params/Stat` (`flood_conf ≤ 2^-499`, `delta1_le`, `delta6_le ≤ 2^-370`), `Params/Advantage`
  (`≤ δ₃ + δ₅ + δ_I + 2^-239`).
* Hidden literal `10`s (= `nA`) fixed in `SetupLaws`, `ChalI`, `C0`, `Sd3`, `Chal3`, `BfX`, `CfX`,
  `BlockCost`, and `Fin 10 →` everywhere.

### The `f(0)` term (found at the switch, not in §5)

Real `KeyGen`/`Dec` compute `B_f̂` and `c_f̂` from crafted simulation data at the attribute `0`
(`Algo/RowSim`): `B_f̂ = row(W_f) + f(0) G̲`, `c_f̂ = row(W_f) + f(0) · (row 1 of G)`. The date
windows all reject `(0,0)`, so `f(0) = 1` was hard-wired (the post blocks add `G̲`). A branching
program may output `0` on `attr0`. Now `keyMatrix_sdB`, `evalCiphertext_sdC` (`Algo/RowSimData`)
state `… + bitR (bit0 C) • …`. Machines:

* the front end emits `true :: bit0 C :: stream` (that is `blockWord`); `frontBP` must compute
  `bit0 C` = `!authA C 0^128` with `authBPC` (WS7) on a copy of `C` and `128` zeros;
* `bfX`/`cfX`: first move the head bit of tape `1` to the end of tape `0`
  (`snocHead 0 1 ⨾ tail 1`); the pre block stashes it with the trapdoor (`LT := lenT + 1`), the
  `W_f` block sees the stream only (spec `WfSpecS`: law on `(blockWord W C).tail`), the post block
  reads the bit back and adds the gadget only if it is set (`ifBit`);
* the reductions' key component (`keyPF`, simulated keys, `f(x*) = 1`) does not need the bit: its
  block is `tail 1` then the stream block (`WfSpec` on `blockWord`, from `WfSpecR`).

### Progress after the switch (lead, `t3/bp-switch`)

| Milestone | State | Where |
| --- | --- | --- |
| M6 `correct_conf`, `expressive_conf` (`bpUniverse`) | **done** | `Params/Conf.lean` |
| statistics at confA (`flood_conf` 2^-499, `delta1/6_le` 2^-370, advantage + 2^-239) | **done** | `Params/Stat.lean`, `Params/Advantage.lean` |
| f(0) machine fix: `frontBP` emits `bit0 C` (authBPC at `attr0`), `bfX`/`cfX` carry it, `postCoreB`/`postCoreC` add the gadget under `ifBit` | **done** (laws) | `Prog/FrontBP.lean`, `Prog/BfX.lean`, `Prog/CfX.lean` |
| front-end cost with the bit: `frontBTn ≤ 2^8 X²`, `frontBA m = m + allG + S0 + 3` | **done** | `Prog/FrontBPCost.lean` |
| `WfSpecS` (block on the stream), `wfSpecS_of_wfSpecR`, `wfSpec_tailB` (key component), `bpRP_getLast` | **done** | `Prog/KeyP.lean`, `Prog/WfSpecBridge.lean` |
| M7 shells with `frontBP` (`keyMachineP hk c bfX cf`, `decMachineP hk c cfX`), `machinesP`, **`implC`, `correct_implC`, `expressive_implC`** | **done** | `Prog/ShellsBP.lean`, `ImplP.lean`, `ImplBP.lean` |
| Setup/Enc at confA: `time_setupMP_conf' ≤ 2^387`, `time_encMP_confT ≤ 2^452`, `descLen_setupMP_conf`, `descLen_encMP_conf ≤ 2^300` | **done** | `Prog/SetupConfA.lean`, `Prog/EncConfA.lean` |
| W_f stream block at confA (`time_wfB2S_conf ≤ 2^628`, `size_wfB2S_conf ≤ 2^25`, `wfSpecR_wfB2S`) | builds (WS6, hypotheses `nA = nAn` etc. now true by `rfl`) | `Prog/WfB2S*.lean`, `Prog/WfRCert.lean` |
| KeyGen/Dec clocks and descLen at confA (KeyTight*, DecTight*, KeyCost*, DecCostConf, DescConf, BlockCost, PostCost, BfXCost, SizeCost, KeyGenCost, DecGenCost) | **open** (helpers `t3/bp-r-key`, `t3/bp-r-dec`) | `Attic/` |
| authorization component: `AuthSpec`, **`authSpec_authBPX : AuthSpec hk c authBPX (2^49) 109 18`** (WS7's `authBPC` + output normalization, lifted to 256 tapes) | **done** | `Prog/AuthBPX.lean` |
| reductions' components and kb at confA | **done** (key component's cost a hypothesis, `KeyRConfA`) | `ReductionCompsBound`, `Prog/{SetupLA, CompCost, SzWide, RedDecodeA}`, `AHConcrete` |
| `Submission` for `BranchingProgram.primitive` | **done** (hypotheses `KeyRConfA`, `KeyDecCost`) | `Submission.lean` |

Facts kept from the workstream status files (removed):

* WS1: never `unfold bpPred`/`bpRP`/`RP.toSLP` of a concrete program (go through `RP.pred`,
  `RP.valueOf_pred`, `RP.run_eq_valueOf` with a variable program); a kernel-cheap route for the
  predicate of the stream block is `predC_eq_pred`, `predR_eq_pred` (both `rfl` on variables).
* WS2: `Params/SizesA.lean` (generic confA chain) is now redundant with `Params/Sizes.lean`;
  flooding is `2^-499` (`|JC| = 2^127 (1 + 2^-27)^3`).
* WS5: KeyGen, Dec and the key component keep `256` tapes (`3^256` in `descLen`); the front end
  costs `≤ 2^8 X²` (`frontBTn_le`), its output `≤ frontBA bpLen ≤ 2^63`, its states
  `≤ 36 n + 2^56`; WS9's per-tape key clock for any front end is `KeyPTimeV.time_keyPFV`.
* WS6: `time_wfB2S_conf ≤ 2^628` (every tape `≤ 2^262`), `size_wfB2S_conf ≤ 2^25`, for SimData
  `≤ 2^260` and streams `≤ 2^64` bits of `≤ 2^50` instructions (`WfRCert`: f̂ run `≤ 2^627`).
* WS7: compiler `≤ 2^126` steps, tapes `≤ 2^62`, `≤ 2^27` states; `authBPC` `≤ 2^108` steps,
  `≤ 2^17` states.
* WS8: the generic `kb` formula (`ReductionCompsBoundG`, now in `Attic/`) gives
  `kb = 495 + ⌈1.585 (298 + tc)⌉` (`tc` = tapes the compiler adds to the key component; with the
  front end framed inside the `256` tapes `tc = 0`, `kb ≈ 968`); `AHConcreteBP.statTerm_bp`
  (`statTerm ≤ 2^-239`), `compBoundBP_le`, `attributeHiding_of_constBound`.

`AdvancedEncryption/Attic/` holds the files not yet repaired (not built). A file is restored by
`git mv` back under `PE/`, its import added to `AdvancedEncryption.lean`, then fixed or pruned of
its date-window numerals (the pruning helper used: delete the declarations whose build fails and
re-prove them at confA).

### M9: reductions, attribute hiding, submission (branch `t3/bp-r-ah`)

* **`kb = 965`**: `AHConcrete.attributeHiding_conf_rlwe (hkey : KeyRConfA) (kb) (hkb : 965 ≤ kb)
  hard3 hard5 : AttributeHiding PUniv params (impl hkp confP ms)`; `registry_covers_kb : 965 ≤
  RingLWE.H` at both instances (`Params/Strength.lean`, now the confA scans under the unprimed
  names `ringLWE_H_registry3/5`; the `N = 2^34` scans are removed). The premises of the submission
  ask `965` bits (`Sub.kbA`).
* The constant: `compConst_le_bp` (`ReductionCompsBound`, generic in the codes, BP slope
  `postPc nA 1 = 802`, `chainSlope ≤ 11 Tc + 2^26 X²`) and `compBound_confA`, `kb_confA`
  (`64 · (2^128)² · Cst ≤ 2^965`, `Cst ≈ 2^702.8`): states of the chain `≈ 55944 · Sz2` with
  `Sz2 ≤ 2^198 + 2^196 + 2^28`, `3^298` for `14 + 254 + 30` tapes.
* Components at confA (proved): setups `≤ 2^394` steps, `≤ 2^195` bits (`Prog/SetupLA`, generic
  closed forms `…_numA` then instantiated; packed secrets `+ 132 ≤ 2^193`); public keys and
  challenges `≤ 2^458` steps, `≤ 2^196`/`2^197` bits; SimData programs `≤ 2^520` steps
  (`≈ 2^519.85`), `≤ 2^259` bits; states `≤ 2^25` (`Prog/CompCost`; the SimData templates reach
  `2^257`, so their state counts use `Prog/SzWide`, the block counts for templates below `2^260`);
  the reductions' decoders `≤ 2^380` steps, `≤ 2^16` states (`Prog/RedDecodeA`, new file, does not
  touch BP-R-Dec's `DecodeCost`); authorization `authSpec_authBPX`.
* The reductions' key component is `keyR sdP = keyPF hkp confP sdP eF (frontBP confP.L)
  (tailB Sub.wfC) cfP` (law proved). **Its cost is the hypothesis** `KeyRConfA := ∃ Tk Lk Sk,
  KeyRCost 520 259 Tk Lk Sk ∧ Tk ≤ 650 ∧ Lk ≤ 270 ∧ Sk ≤ 2^198 + 2^196`, where `KeyRCost Ts Ls Tk Lk
  Sk`: for any `sdP : XProg 82` and `a ≤ 2^193` with `timeBoundT sdP (io2 a 0 0) ≤ 2^Ts` and
  `lenBoundT sdP (io2 a 0 0) ≤ io2 (2^Ls) 0 0`, `timeBoundT (keyR sdP) (io2 a confP.L 0) ≤ 2^Tk` and
  `lenBoundT … ≤ io2 (2^Lk) 0 0`; and `sdP.size ≤ 2^25 → (keyR sdP).size ≤ Sk` (expected
  `≈ 264 · lenPK = 2^198.05`, `lenPK ≤ 2^191`). To be discharged from BP-R-Key's
  `time_keyP_confV`/`size_keyP_confV`-style lemmas for `keyPF … frontBP …`.
* `Submission.lean` (`Sub` namespace): registry over decision Ring-LWE, `deps .attributeHiding =
  [prem3, prem5]` at `965` bits, `[]` otherwise, `N = 2^1002`; `cost_implC (hKD : KeyDecCost)`,
  `spec_submission (hkey : KeyRConfA) (hKD : KeyDecCost)`, `valid_submission` (no hypothesis).
  `KeyDecCost`: `(keyMachineP hkp confP bfC cfP).time ≤ 2^700`, `(decMachineP hkp confP cfC).time
  ≤ 2^700`, both `descLen ≤ 2^1000` (Setup/Enc are proved: `2^387`, `2^452`, `2^300`).


## 13. 14-bit states (relaxed problem, branch `t3/dualuse-14`)

The problem now asks for 14-bit states with a width chosen by the submission. RingBTVW takes `w8`.

* **Circuit** (`Gates/BP14`, `BPCircuit`, `BPWord`): the programs on 14-bit states natively (the
  `univ w8` tables; `Relaxed.ofProgram` is the identity on tables). Trees of 22 levels, 93 registers
  (`< 222` slots), `633 · 2^21 − 266` instructions, **depth `≤ 478`** (`max (δ + 29) 43` per step),
  predicate words of `211 · 2^22` bits. Compiler (`BpComp*`) and authorization (`AuthBP`) re-derived
  (14-bit entries, 20 tree counters); their envelopes (`2^126`, `2^108` steps) unchanged.
* **Parameters** (`Params/Sizes`): `K = 2^26`, `N = 2^34`, `d = 2^62`, `Dmax = 478`,
  `Eτ = 21138808`, `B = 21139048`; noise `< 2^42278725 ≤ q/4` (margin 37 % of `K`). Ring-LWE at
  `N/K = 2^8`: **certified 1158 bits** (`Params/Strength`, both instances; fails at 1159), against
  `965` asked (`kb_confA`, the earlier envelope).
* **Cost**: `N = 2^677` (Setup `2^371`, KeyGen `2^629`, Enc `2^452`, Dec `2^629` — the KeyGen, Enc,
  Dec clocks are the earlier envelopes, still valid; description lengths `2^300`, `2^615`,
  `2^300`, `2^676`). Also: the description length of KeyGen now uses `Nat.size` of the state count
  (it used the state count itself: `2^817` at the old parameters).
* What dominates: Dec's description length, `≈ 6 · S · 3^256 · 1286` with `S ≈ 2^257` states,
  linear in the largest SimData offset read (`≈ 2^245`, `getAt`/`prefP` unrolled per bit). Loops
  over `natP` counters there would bring `S` down to the loader (`≈ 2^186`), i.e. `≈ 2^605`, and
  then the clocks (to be re-certified at the tight `Lb`, `Mall`, `Ic = 2^31`) dominate.
* Other widths (estimates): `w16` (depth 262) allows `K = 2^25`, `N = 2^33` (`≈ 2^668`); `w32`
  (depth 178, `≈ 2^52` instructions, 44 tree counters: more tapes) `K = 2^24`, `N = 2^32` (`≈ 2^660`).
