# WS8 status (reductions and attribute hiding)

Branch `t3/bp-ws8`, base `e5632ceb` (WS9 merged: `C ≤ 2^687`, `kb ≥ 949` at `confP`).

## Stage I (tree still date windows)

* **Codes behind `PUniv`.** `PE/Impl/DualUse/PUCodes.lean` (new): `puCodes sig : Codes PUniv Sig`
  (Stage I `= dateCodes sig`), `nA_puCodes : (puCodes sig).nA = nA`, `nM_puCodes`, `nS_puCodes`,
  `length_paramsWord_pu : (paramsWord PUniv params).length = 515`.
  `PE/Impl/Game/HandlersBP.lean` (new): `bpCodes` (`nA = 128`, `nM = 1`, `full_attr` from
  `encAttr_onto`), `nA_bpCodes`, `nM_bpCodes`, `length_paramsWord_bp = 515` (same `λ`, `κ`, empty
  description as the date-window universe). At the switch: `puCodes := bpCodes`.
* **Reductions on the neutral names**: `ReductionComps`, `ReductionCompsBound`,
  `ReductionCompsBoundV`, `ReductionMachine`, `ReductionOracle`, `ReductionPerQuery`,
  `ReductionSteps`, `AHComps`, `AHConcrete`, `AHConcreteV`, `AHFinal`: `dateUniverse → PUniv`,
  `Date → PUniv.Attr`, `dateCodes → puCodes`, `Post _ _ 10 1 → Post _ _ nA 1`. `AHMath`,
  `RealBridge`, `IdealBridge`, `AHAssembly`: only `dateUniverse → PUniv` — they must match
  `GameChain` (WS1), which still states `Date`; `accOn` keeps `F : Date → …`. Date-specific lemmas
  kept under their names (`nA_dateCodes`, `postPc_date`, `postSlope_date`, `stateBound_date_le`,
  `length_paramsWord_date` — the last still about `dateUniverse`, as WS4/WS5 files use it).
* **Closed forms in `nA`**: `SetupL.nW_eq`, `nR_eq`, `nE_eq`, `nPsi_eq`, `nCj_eq`,
  `CompCost.len_Attr`.
* **`statTerm`** (`AHAssembly`) sums `Fintype.card PUniv.Attr`; `statTerm_eq_date` rewrites it to
  the `Date` form of the game chain.
* **Authorization behind an interface** (`Prog/AuthL.lean`): `AuthSpec hk c authP Lq Ta Sa` (WF, the
  law of `Comps.law_auth` with `authI hk c`, time `≤ 2^Ta` and one output bit from a query `≤ Lq`
  and an attribute `≤ nA` bits, `≤ 2^Sa` states); `authSpec_authL : AuthSpec hk c authL (2^240)
  275 19`. `AHConcrete` uses `authC := authL` only through `authC_spec`.
* **The generic `kb` formula** (`ReductionCompsBoundG.lean`, new): `postStatesG nA nM =
  1546 + 288 (nA + nM)`, `glue3 nA nM Lc = 4479 + 1656 nA + 984 nM + 264 Lc`,
  `compStatesG nA nM pw sP Sz2 Lc t`, `compBoundG nA nM pw sP tP p R Sz2 Lc Sl t`
  (`Sl`: any bound on the chain's slope); `compStatesG_date`, `compBoundG_date` (= `compBound2` at
  `10, 1, 515`); `sum_states_compHandlersG`; **`compConst_le_explicitG`** (the bound for the codes
  `puCodes`, with `(puCodes sig).nA`, `.nM` and `pw` symbolic). `kb ≥ 6 + 2 λ + log₂ C`.

## Stage II preparation (`PE/Impl/DualUse/AHConcreteBP.lean`, new)

* `statTerm_le_gen` (attributes `≤ 2^a`, terms `≤ 2^-(a+s+3)` ⇒ `statTerm ≤ 2^-s`), `stat_of_le`
  (`λ + 2 ≤ 2 s` ⇒ `4 · 2^λ · statTerm² ≤ 1`), `statTerm_ne_top_of_le`, **`statTerm_bp`**: `2^128`
  attributes, `δ₁, δ₆ ≤ 2^-370`, `ε ≤ 2^-499` ⇒ `statTerm ≤ 2^-239` and the condition (§4.4).
* **`compBoundBP_le`**: at `nA = 128`, `nM = 1`, `pw = 515`, decoder `≤ 2^16` states, `≤ 2^350`
  steps, `14` tapes, `254 ≤ R ≤ 370` component tapes, `Sz2 ≤ 2^199`, cut `≤ 2^49`, slope `≤ 2^660`:
  `compBoundG … ≤ 2^233 · 3^(44 + R)`.
* `kb_bp tc : 64 · (2^128)² · 2^233 · 3^(298 + tc) ≤ 2^(495 + clog₂ 3^(298+tc))`; `kb_bp_64`
  (`≤ 2^1069`), `kb_bp_120` (`≤ 2^1158`).
* **`attributeHiding_of_constBound`**: `attributeHiding_of_comps_rlwe` with the statistical part
  given by an exponent `s`; the switch instantiates it with the bundles at `confA`.

### Inputs assumed for the BP numbers (to be supplied at Stage II)

| Input | Value used | Source |
| --- | --- | --- |
| `Sz2 = 2(|setup|+|pub|) + |key| + |auth| + |chal|` | `≤ 2^199` | key: `264 · lenPK + 2^140` (`size_keyP_confV` form), `lenPK = 8 nA k³N²K = 2^190.0` at `confA`; compiler `≤ 2^27`, `authBPC ≤ 2^17` (WS7); `frontP` (`2^60`) gone |
| component tapes `R` | `254 + tc` | `tc` = tapes the compiler adds to the key component (WS5) |
| decoder | `2^16` states, `2^350` steps, 14 tapes | as at `confP` (to re-check at `N = 2^36`) |
| cut `c.L` | `bpLen = 481 · 2^40 ≤ 2^49` | WS1 |
| slope | `≤ 2^660` | components' time `≤ 2^651` est. (block `2^628`, key try, compiler `2^126`), lengths `≤ 2^262` |

### Estimate of `kb` for branching programs

`kb = 495 + ⌈1.585 (298 + tc)⌉`: **`tc = 64` ⇒ `kb = 1069`** (float estimate `≈ 1067`);
`tc = 0` ⇒ 968; `kb ≤ 1158` iff `tc ≤ 120`. So with the compiler's 64 tapes (or anything up to
120 extra tapes), **ring degree `2^35` would suffice** (WS3: ≈ 1158 bits certifiable there), as
long as the inputs above hold; otherwise stay at `2^36` with 2650. The dominating factor is
`3^(tapes)` (`≈ 2^574` at 362 tapes); the states (`≈ 2^214.8`) add ≈ 215 bits, `secBits` 262.

## What the switch / Stage II still needs

* `GameChain` (WS1) on `PUniv.Attr` (then `statTerm_eq_date`, `accOn`'s `Date` go).
* `attributeHiding_of_comps_rlwe` and `law_authL` carry `hL : dateBound ≤ c.L` (via
  `compReduction`/`realCovered`): becomes the BP class bound.
* `AuthSpec` for `authBPC`: frame WS7's `authBPC : Prog 16` to `XProg 256` (`liftP`, `Prog.toX`),
  law from `law_authBPC`, time `2^108` for queries `≤ 2^49` bits, size `2^17`.
* `StepComps` fields `b ≤ 10` (attribute length) → `nA`, with the setup certificates (`SetupL`
  `time_setup*D_conf` still at `10`), and the step components at `confA`.
* `AdvancedEncryption.lean` (WS1) should import `PE.Impl.DualUse.AHConcreteBP` (built by the
  `PE.*` glob already).
