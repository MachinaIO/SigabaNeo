# Module 9 of `keyP`: time/length/size certificates (`RedKeyT*`)

## 1. Blocker in `RedKeyMFront` (proved): the `len` field is false for `rkKeyP`

`XProg.lenBoundT` is static. A loop's bound is the sup over all rounds, *including round 0*, so
the counter tape of `forN c t body` keeps the bound `ℓ t` after the loop, even though it is blank
at run time.

* `rkInvP` ends with `appT 0 1 2 3 ⨾ clr 1`: tape `2` (the counter of `appT`/`natP`) keeps the
  bound `|keyEnc|`. **`RedKeyTNeg.not_len_rkKeyP`**: `0 < codecSize (keyEnc Dc) →
  ¬ lenBoundT (rkKeyP mid) ℓ ≤ io2 Lk 0 0`, for every `mid`, `ℓ` and `Lk`.
* The same holds, informally, for the global scratch tapes `5`, `6` of `rkLeChk`/`rkEqChk`
  (counters of `natU`/`dropT`), which `rkLongP` does not clear.

**Fix (done in `RedKeyTFront`, law unchanged):** `rkLeChkT = rkLeChk ⨾ clr 5 ⨾ clr 6`,
`rkEqChkT = rkEqChk ⨾ clr 5 ⨾ clr 6`, `rkInvPT = rkInvP ; clr 2`, `rkKeyOfT`,
**`rkKeyPT mid := rkKeyOfT (rkValidP mid)`**, `wf_rkKeyPT`, **`law_rkKeyPT`** (same `RkMidOk`).
`RedKeyTTop.keyCompOfT` is the `Sub.KeyComp` built from `rkKeyPT`, so `RedKeyMComp.keyCompOf`
(built from `rkKeyP`) cannot be completed. Either switch the assembly to `keyCompOfT`, or
patch `RedKeyMFront` the same way (then `RedKeyTFront` becomes redundant).

**The same pitfall applies to `mid`:** every scratch tape must end with a `clr` (or a
`setList`). A tape that is blank only at run time is not enough.

## 2. What is proved (all build; axioms `propext`, `Classical.choice`, `Quot.sound`)

Files: `RedKeyTNeg`, `RedKeyTFront`, `RedKeyTGuard`, `RedKeyTInv`, `RedKeyTTop`.

* `sigBound_cdR_le : sigBound cdR (WR Dc) ≤ 2^100` (`(rawEnc Dc).len ≤ 2^99`, `WR Dc ≤ 2^93`).
* `time_pubP_Dc_T : timeBoundT (pubP Dc) (io2 (2^101) 0 0) ≤ 2^436` (the evaluated
  `bounds_pubP`; `≈ 2^435.4`). `size_pubP_Dc_T : ≤ 2^30`.
* Guards (`gF 2^101 predLen` envelope → itself, `≤ 2^140` steps), invalid branch
  (`→ io2 2^107 0 0`, `≤ 2^437`), long branch (`→ io2 0 0 0`, `≤ 2^105`).
* **`bounds_rkKeyPT`** (`RkMidBound mid a`, `RkTailCert a Lt Tt`, `Tt ≤ 2^449`):
  `lenBoundT (rkKeyPT mid) (io2 (sigBound cdR (WR Dc)) predLen 0) ≤ io2 (max Lt 2^107) 0 0` and
  `timeBoundT … ≤ 2^450`.
* **`size_rkKeyPT`**: `mid.size ≤ 2^190`, `(rkTailP Dc Bk rSmall).size ≤ 2^195` ⇒ `≤ 2^200`.
* **`keyCompOfT mid hwf hm a hb Lt Tt ht hLt hTt hsm hst : Sub.KeyComp`** (`Lk = max Lt 2^107`).

### The hypothesis on `mid` (`RedKeyTTop.RkMidBound mid a`)

With `rkIn := io2 (2^101) predLen 0` and `rkLiftB a := embedF rkE (fun _ => 0) a`:

* `time : XProg.timeBoundT mid rkIn ≤ 2^440`;
* `len : XProg.lenBoundT mid rkIn ≤ rkLiftB a`, i.e. the MVM tapes `0 … 104` are within `a`, and
  **tapes `105 … 246` have static bound `0`**.

`a` should be the input envelope of the back-end certificate: a uniform `2^150` cap is fine for
time, but `a (tR 14) ≤ 2^102` (the `mpk` word) and the template tapes `35 … 38`
(`K`, `N`, `N K`, `N K`) must be tracked exactly. The output bound is `Lt ≥ a(tR 14) +
a(tR 19)`, and `Lk = max Lt 2^107 ≤ 2^125` needs this. With a uniform cap on register `14`,
`Lk` would be `2^151`.

## 3. Remaining: `RkTailCert a Lt Tt` for `rkTailP Dc Bk rSmall`, `Tt ≤ 2^449`, plus `size ≤ 2^195`

`RkTailCert a Lt Tt := KeyTime.Cert (rkTailP Dc Bk rSmall) a (outputBounds Lt) Tt`.

**Sizes:** register `16` holds `rowsWord X` with `|PIdx| · |ZIdx|` ring words:
`|PIdx| ≤ 2^65` (`card_PIdx_Dc : |PIdx|·2^24 ≤ 2^89`; ≈ `2^63.6`), `|ZIdx| = W τ = 2^38`, and a
word is `N K = 2^40` bits. That gives **≈ `2^141.6` bits, at most `2^143`**. This is above
`2^125`, but it is internal only: `post` clears it, and the output is `|mpkEnc| + |keyEnc|
≤ 2^102 + 2^106`. A `2^150` cap is enough.

**F3's certificates cannot be reused as they are.** All the `*_Dc` certificates in `KeyTime*`
assume `RingInputs (2^120) …`, i.e. every tape `≤ 2^120`, and register `16` breaks this. They are
also too loose: `compile_keyDigitsC_Dc ≤ 2^497` (`publicStepTime = 2^472` per row × `2^22` rows,
because `signedProductTime` is instantiated with count cap `2^120`), `compile_correctionC_Dc ≤
2^484`, `compile_tryKeyC_Dc ≤ 2^500`, `compile_candidateC_precise ≤ 2^414`,
`compile_acceptC_Dc ≤ 2^434`. `keyDigitsC` alone already exceeds `2^450`.

**The real cost fits easily.** `operationBound M N K _ = 1000 (M+1)(N+1)²(K+1)²` is `≈ 2^240` at
`M = 2^150`. The try does about `2^64` ring products in `A·p` (`2^22` rows × `≈2^42`) and about
`2^102` in `X ·ᵥ u` (`mvSubC`). That is `≈ 2^342`. Each loop round also costs `2·supB ≈ 2^151`.

**Plan:** re-instantiate the generic kernels (`compile_signedDotC M N K L`, `compile_gatherC`,
`compile_decQC…`, `layout_*`, `rep_family`) at `M = 2^150` with count caps `L = 2^66` (not
`2^120`). Then re-compose `keyDigitsC`, `candidateC`, `assembleC`, `acceptC` and `sampleP` at the
`layout (2^150) … b` envelope. `b 14`, `b 19` and `b 16` (`≤ 2^143`) must stay register-specific,
as F3 does with `layout`. New certificates are needed for `uC` (`RedKeyU`), `natC 21/22` and
`mvSubC` (`RedKeyMatVec`: nested `rep` over `|PIdx|` rows × `|ZIdx|` columns, register `18`
growing; use `rep_family`). Then `packKeyC ; post` (`cert_packPost_Dc` re-done at `2^150`, or
`cert_vmPost` with `M = 2^150`). A crude uniform `M^depth` bound in the style of `DecTimeUni`
does not work here: depth `≥ 2` at `M = 2^150` gives `≥ 2^300 · 2^240`.

Size of the tail: `size_compile_weight` (`≤ 100000 · codeWeight`) with `weight_tryKeyC`-style
bounds for `simTryKeyC`, plus `weight_natC` (`≤ 3n+1`) for `natC 21 |ZIdx|` and
`natC 22 |PIdx|` (`≈ 2^66`). This should come out far below `2^195`.

### Budget check

`2^140` (guards) + `2^104` + `2^440` (`mid`) + `Tt` (`≤ 2^449`) ≤ `2^450` (proved). The invalid
branch needs `2^437`, which is below that.

## 4. Done: the back end (`RkTailCert`, size) and the final assembly

Files (all build; axioms `propext`, `Classical.choice`, `Quot.sound`): `RedKeyTIn` (interface),
`RedKeyTSize`, `RedKeyTK`, `RedKeyTAcc`, `RedKeyTCand`, `RedKeyTMv`, `RedKeyTPub`, `RedKeyTDig`,
`RedKeyTUc`, `RedKeyTUD`, `RedKeyTNum`, `RedKeyTTail`, `RedKeyTMain`, `RedKeyTSpecG`, `RedKeyTSpec`.

* **Interface `RkTailIn a`** (`RedKeyTIn`): every MVM tape `≤ 2^150`, templates
  `a 35 ≤ K`, `a 36 ≤ N`, `a 37 ≤ N K`, `a 38 ≤ N K`, register `14` (tape `55`) `≤ 2^102`.
  Downward closed; `rkTailIn_iff : RkTailIn a ↔ a ≤ rkTailEnv`.
* `rkTailCert_of : RkTailIn a → RkTailCert a rkLt rkTt`, `rkLt = 2^102 + 2^120`, `rkTt = 2^436`.
* `size_rkTailP_Dc : (rkTailP Dc Bk rSmall).size ≤ 2^195` (log-weight `natC`).
* `keyCompOfMid mid hwf hm hsm (hb : ∃ a, RkTailIn a ∧ RkMidBound mid a) : Sub.KeyComp` and
  `spec_of_mid … : Spec …` (`RedKeyTSpec`).

Method: cap `Mx = 2^150` on all tapes; tight per-instruction costs (`rktOp`: the counter register
is charged with its layout bound, not the cap) on the hot paths (inner products, queue
automorphisms, candidate decoder, box test, `mvSubC`); F3's generic kernels at `M = 2^150`
elsewhere (`≈ 2^430` each for the `2^22`-row loops of `keyDigitsC`/`uC`). Kernel lesson: numeric
bounds must be stated for variables / generic `D` and only instantiated at `Dc`; `gcongr`,
`norm_num` or `omega` near concrete `Dc` terms stall the elaborator or kernel.

Remaining: only `mid` (with `RkMidOk`, `WF`, `size ≤ 2^190`, and a witness `a` with
`RkTailIn a ∧ RkMidBound mid a`).
