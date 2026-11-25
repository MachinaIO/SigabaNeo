# `pubP`: the reduction's public-key component — status and plan

Target (`Generic.Comps`, `AH/RedCompsR.RawComps` at `Dc`, `Ok := fun _ => True`):

* `law_pub : ∀ σ, XProg.law pubP (io2 ((rawEnc D).enc σ) [] []) = PMF.pure (io2 ((mpkEnc D).enc (pubK D σ)) [] [])`
  (`sp.pub σ = (mpkEnc D).enc (redView D (rawF D σ)).1 = (mpkEnc D).enc (pubK D σ)`, definitional);
* `wf_pub : pubP.WF`;
* `len_pub : XProg.lenBoundT pubP (io2 (2^101) 0 0) ≤ io2 Lp 0 0` with `Lp ≤ 2^125`;
* `XProg.timeBoundT pubP (io2 (2^101) 0 0) ≤ 2^450` at `Dc`; `pubP.size ≤ 2^200`.

## Done (building, no sorry/native_decide, axioms: propext, Classical.choice, Quot.sound)

### `Prog/RedPubPMath.lean` — the output word, field by field
Imports `AH/RedSecret`, `AH/RedGame`, `Prog/DecCoefMath`, `Prog/DecFinalD` (no `DecMachineCode`,
no `RedChalMath`, no `SetupConf`).

* `pvecE_enc`, `pfun_enc`, `pmatE2_enc` (copies of the `DecMachineCode` lemmas), `pwordsOf v`
  (`encRM` words along `Enum`), `vecE_wordsOf`, `matE2_wordsOf`, `funMat_enc`, `funMat2_enc`.
* `pubK D σ := (redView D (rawF D σ)).1`; the parts of the raw secret: `abarR` (`Ā`), `b2barR`
  (`B̄⁽²⁾`), `bbR σ = ![Ā, B̄⁽²⁾]`, `zrR`, `flR`, `bbarP` (`b̄ = v_B + B⁽²⁾` on `Wb`), `hR`
  (`h_k = v_H k − G⁽²⁾ + H⁽²⁾ k`), `HR` (`H_k = [aH k; H⁽²⁾ k]`), `aR` (`a_t`), `cbR` (`cb_t`),
  `dinR`, `dautR` (the digits).
* Field lemmas: `pubK_B` (`B = of ![aB, B⁽²⁾]`), `pubK_H`, `pubK_d`, `pubK_a`, `pubK_A0`,
  `pubK_Ain`, `pubK_Aaut`, `cb2_eq`, `progA_eq`.
* **`pubWord_eq`**: `(mpkEnc D).enc (pubK D σ) = wB σ ++ (wH σ ++ (wa σ ++ ((wA0row σ 0 ++ wA0row σ 1) ++ (wAin σ ++ (wAaut σ ++ wd σ)))))` with
  - `wB σ = pwordsOf aB ++ pwordsOf B⁽²⁾` (BCol order);
  - `wH σ = flatten_{k ∈ Enum Jh} (pwordsOf (aH k) ++ pwordsOf (H⁽²⁾ k))` (Col order inside);
  - `wa σ = flatten_{(t,c) ∈ Enum (Pos × Col)} encRM (aR σ t c)`;
  - `wA0row σ ρ = pwordsOf (c ↦ bbR σ ρ ⬝ᵥ bv (zr (R₀ c)) + G ρ c)`;
  - `wAin σ = flatten_{(t,d)} (wAinRow σ t d 0 ++ wAinRow σ t d 1)`,
    `wAinRow σ t d ρ = pwordsOf (c ↦ bbR σ ρ ⬝ᵥ bv (zr (R^in (t,d,c))) + dinR σ t d * G ρ c)`;
  - `wAaut σ` likewise with `σ_{kf t}(…)` and `dautR`;
  - `wd σ = encRM ad ++ encRM d₂`.
* Addends: `mul_G_apply` (`δ G ρ c = if ρ = c.1 then 2^{c.2} • δ else 0`), `setting_d`
  (digits = `binaryDigit`), **`dinR_apply`** (`dinR σ t (r,c',i) = binaryDigit (if r = 0 then aR t c' else cbR t c') i`),
  **`dautR_apply`** (`binaryDigit (σ_{kf t}(HR (t,1) r c') − [r = 1] σ_{kf t}(hR (t,1) c')) i`).

### `Prog/RedPubPInst.lean` — the instance inside the raw secret
* `map_finRange_sum`, `map_finRange_prod`, `map_finRange_congr`, `map_jh`, `map_bcol`
  (lists over `Fin` along `finSumFinEquiv`, `finProdFinEquiv`, `finCongr`, `jhE`, `bcolE`).
* `plainHL D F` / `keyHL D F`: `flatten_{i ∈ finRange K} [F k (1,i) | k ∈ Enum Jh]` / same with `(0,i)`.
* **`rows_map`**: for any `F : Coord D → β`, `(finRange rows).map (F ∘ ρ D) = [F (inl b) | b ∈ Enum BCol] ++ ([F d] ++ (plainHL (F helpers) ++ keyHL (F helpers)))`.
* `ringWords`, `vecE_rows`, **`instA_words`**, **`instV_words`**:
  `(vecE D (Fin rows)).enc (toPair D i).1 = pwordsOf i.aB ++ (encRM i.ad ++ (ringWords (plainHL D i.aH) ++ ringWords (keyHL D i.aH)))`
  (and `.2` with `vB`, `vd`, `vH`). With `RedChalMath.rawEnc_split`/`instEnc_enc` (both `rfl`; restate
  locally to avoid importing `RedChalMath`) this gives the whole input word:
  `attr(128 bits) ++ [aB | ad | aH plain (i,k) | aH key (i,k)] ++ [vB | vd | vH plain | vH key] ++ B⁽²⁾(BCol) ++ H⁽²⁾(k outer, Col) ++ d₂ ++ flood ++ zr`.

## Status: P1–P7 DONE (all building; no sorry / native_decide; axioms propext, Classical.choice, Quot.sound)

Entry points (namespace `AdvancedEncryption.ExpLUT.Prog.RedPubP`):

* `pubP D := RedIO.ringIO1 D.N D.K ra rb rOut r1 (tm D) (pubC D)` (`RedPubPCode`).
* **`law_pubP`** (`RedPubP`): for `2 ≤ D.N`, `wSt·2^7 ≤ 2·D.N`, `D.b ≤ 32`,
  `law (pubP D) (io2 ((rawEnc D).enc σ) [] []) = pure (io2 ((mpkEnc D).enc (redView D (rawF D σ)).1) [] [])`;
  **`wf_pubP`**; **`exec_pubC`** (the code leaves `(mpkEnc D).enc (pubK D σ)` in `rOut`).
* **`bounds_pubP`** (`RedPubPBound`): generic length/clock bound from register classes
  (`prk`/`pBf`: operation templates `Mo`, loop counters `Bc`, rest `Mb`), clock
  `210((2Mb+1)(4Mb+12)) + (478 + 241 b)(Bc^5 (2Mb+4+pIB Mb Mo) 6) + 300(2Mb+3)`.
* At `Dc` (`RedPubPDc`): **`law_pubP_Dc`**, **`wf_pubP_Dc`**, **`len_pubP_Dc`**
  (`io2 (2^101) 0 0 ↦ io2 (2^102) 0 0`), **`time_pubP_Dc`** (`≤ 2^450`), **`size_pubP_Dc`**
  (`≤ 2^200`), bundled as **`pubP_Dc_spec`**.
* P7 (`RedPubPComps`): **`law_pub_spS`** — the `law_pub` field for
  `spS Dc kb L (rawF Dc) setupS impl χfl i₀` with `cd = w8Codes (rawEnc Dc)` (any `Ok`, any
  `setupS`); use `wf_pubP_Dc` for `wf_pub`, `len_pubP_Dc` for `len_pub`.

Files (in import order): `RedPubPKit` (shift registers `pbuf`, `exec_mv_blk`, `exec_strided`),
`RedPubPRow` (`exec_rowC`: gadget row of two `hashPhase`s), `RedPubPCode` (registers, `tm`,
`pubC`, `loopOkB_pubC`), `RedPubPWords` (`prawEnc_fields`), `RedPubPParse` (`TmplOK`,
`exec_parseC`), `RedPubPOutBH` (`B`, `H`), `RedPubPPrep` (`Ā`, `B̄⁽²⁾`, `−v̄_B`), `RedPubPMono`
(`X^{w x_t}`), `RedPubPA` (`a_t`, `cb_t` loop), `RedPubPA0` (`exec_rowPush`, `a`, `A₀`),
`RedPubPDig` (digit rows), `RedPubPAin` (`A^in`), `RedPubPAutK` (`exec_strMap`, posts),
`RedPubPAut` (`C_{g_t}`, `exec_autPre`), `RedPubPAutT` (`A^aut`), `RedPubP` (law, wf),
`RedPubPTime` / `RedPubPBound` (clock; adapted copies of `RedChalTime`/`RedChalBound` with
`digit`), `RedPubPDc`, `RedPubPComps`.

Not done here: adding the files to the aggregator `ExpLUT.lean` (not allowed for this agent) and
assembling the full `Generic.Comps` record (needs the other components).

The original plan below is kept for reference; the implementation deviates in that all output is
shifted into one register `rOut` by block `mv`s, and `A^in`/`A^aut` use the template-length digit
index (`cp rI cK; drop rI rRem`).

## Remaining work (in order)

All on `RedIO.ringIO1 N K ra rb ro r1 tm c` (`Prog/RedPubFront.lean`: `law_ringIO1`,
`wf_ringIO1`, `bounds_ringIO1`), input on `ra`, output from `ro`; templates `tm r` (any length,
built at run time in `O(log)` states) give every stream template, zero word and the
pre-sized output shift register. Hash kernels from `Prog/RedChalVM.lean` (`RedVM.hashC`,
`exec_hashC`, `hashPhase`, `exec_hashPhase` with post-maps; registers 150–168 reserved there).
Prove everything over abstract `D` (`Dims`), specialize to `Dc` only in the final bounds file.

### P1 `Prog/RedPubPSplit.lean` — split the input (≈300 lines)
`mv d s c` pops `|c|` bits of stream `s` into the shift register `d` (pre-sized by a template of
the same length, so `d` becomes exactly the field). Sequence of pops with templates of lengths
`128`, `|BCol|·NK`, `NK`, `K·|J|·NK` (×2), the same for the `v` half, `|BCol|·NK`, `|J|·|Col|·NK`,
`NK`, `|flood|`, `|zr|`, into registers `rAttr, rAB, rAd, rAHp, rAHk, rVB, rVd, rVHp, rVHk, rB2,
rH2, rD2, rFl, rZr` (the `v` half and the flood are only used for `b̄`, `h`, `cb`). Lemma:
`exec (splitC) (initW1 …) r = field r` from `rawEnc_split`, `instA_words`, `instV_words` and
`RedVM.exec_mv_pop`-style lemmas (`exec_mv_pop` in `VMLib`).

### P2 `Prog/RedPubPCopy.lean` — `B`, `H`, `d` (≈400 lines)
* `B`: push `rAB` then `rB2` into the output buffer (`mv out tmp cBCol` with `tmp := cp`).
* `H`: needs the transpose of the key/plain helper blocks (`i` outer → `k` outer). Kernel
  `transC src out`: for `k` in `|J|` rounds (counter template `|J|`): `cp tmp src`, `drop tmp skip`
  (`skip` = `k·NK` zeros, grown by one word per round with `mv skip zeroStream cNK`), then `K`
  rounds of `mv out tmp cNK; drop tmp cJ1` (`cJ1` = `(|J|−1)·NK` zeros). Spec:
  `bufW` appends `[keyHL… column k]`. Per `k` the output is
  `col_k(keyHL aH) ++ col_k(plainHL aH) ++ (first Col-half of H⁽²⁾ k) ++ (second half)` — i.e.
  `pwordsOf (aH k)` = `[aH k (0,i)]_i ++ [aH k (1,i)]_i` since `Enum Col = (0,·) then (1,·)`.
  Simplest: first materialize `transpose(keyHL)` and `transpose(plainHL)` into two registers, then
  one loop over `k` popping `K` words from each of the four streams (`rAHk^T`, `rAHp^T`, `rH2`
  twice `K` words).
* `d`: push `rAd`, `rD2`.
Spec lemmas against `wB`, `wH`, `wd` of `RedPubPMath`.

### P3 `Prog/RedPubPHash.lean` — `a`, `cb`, `A₀` (≈700 lines)
* Registers: `Ā` (cp of the first `mb` words of `rAB`: pop with template `mb·NK`), `B̄⁽²⁾`
  likewise from `rB2`, `b̄ = v̄_B + B̄⁽²⁾` (a loop of `add` over `mb` words) and
  `B̄⁽²⁾ − b̄` (a loop of `sub`). Use `pwordsOf` + `RedChalMath.hashV_enum` (copy as
  `phashV_enum`): hash of enumerated words = `f ⬝ᵥ bv z`.
* The monomial `X^{w x_t}` per `t`: from the 8 bits of symbol `t` (`rAttr`, most significant first,
  `symOf_encAttribute`), `u := Π_{bit j set} X^{w 2^j}` with `rhoJ` (`X^{−|tmpl|}`, template of length
  `2N − (w 2^j mod 2N)`; cf. `EncCb.rbitP`). Gadget column words `u·G⁽ʳ⁾_c = 2^i u` by doubling
  (`rotB` by `K − 1`, cf. `GadStream.gzW`, `decRM_gIt`).
* `a`/`cb` phase over `Pos × Col`: per `t`, pop the `|Col|·mb` bits of `Z_t` (`zr` part 1,
  `RedChalMath.zrEnc_split` order) into `Zt`; run `hashPhase cpPost` with `xV := Ā`, `xZ := Zt`,
  `xF := [u·G⁰_c]_c` → appends `encRM (aR σ t c)` to the `a` buffer **and** to a kept register
  `rA_t`; again with `xV := B̄⁽²⁾ − b̄`, `xZ := Zt`, `xF := [e_t c + u G¹_c]_c` (flood part 2 plus
  gadget, one `add` per word) → `encRM (cbR σ t c)` into `rCb_t`.
  `exec_hashPhase` needs `encRM`-canonical addend words only through `decRM`, so addends may be
  non-canonical sums.
* `A₀`: two single-row phases over `Col` with `zr` part 2 (copy the block first: `cp`), addends
  `G ρ c` (= `2^i` on the diagonal block: word of `1` in `r1` doubled).

### P4 `Prog/RedPubPDig.lean` — `A^in`, `A^aut` (≈900 lines)
For each `(t, d = (r, c', i))` in `Enum (Pos × Dig)` (resp. `Fin b × Dig`):
* `δ := digitRW (|i|) (canon C_{r,c'})` with `C = cinMat(a_t, cb_t)` (words kept in P3:
  `rA_t`, `rCb_t`, pick word `c'` by `drop`) resp. `C = σ_{κ_t}(H_{(t,1)}) − [0; σ_{κ_t}(h_{(t,1)})]`
  (`aut` with the template `κD D t`, `σ_kf`; `h` from `vH`, `H⁽²⁾`, `G¹`). Lemmas:
  `decRM_digitRW_canon` / `EncWordMath` line 280 (`decRM (digitRW N K i (encRM a)) = binaryDigit a i`;
  copy, `EncWordMath` is uncommitted), `dinR_apply`, `dautR_apply`.
  Digit index `i` by a template growing one bit per round, or by rotating (`VMDot.dBody`:
  `digit 0` of the word rotated `i` times, `digitRW_zero_rotBW`).
* the addend streams `[δ G⁰_c]_c`, `[δ G¹_c]_c` (`mul_G_apply`: `2^i δ` on the diagonal block,
  zero word elsewhere) by doubling;
* two single-row hash phases (`cpPost` / `RedChalPhases.autPost` with `κD D t`) with the block of
  `R^in_{t,d}` (resp. `R^aut_{t,d}`) copied twice — matches `wAinRow σ t d 0 ++ wAinRow σ t d 1`.
  A generic "two-row" lemma: `exec_hashPhase` twice with `xZ := blk` restored by `cp`.

### P5 `Prog/RedPubP.lean` — assembly and law (≈400 lines)
`pubCode := splitC ⨾ outB ⨾ outH ⨾ phaseA ⨾ phaseA0 ⨾ phaseAin ⨾ phaseAaut ⨾ outD`,
`pubP := RedIO.ringIO1 D.N D.K ra rb ro r1 tmP pubCode`; `law_pubP` from `law_ringIO1`,
the phase lemmas, `bufW_full` (output register pre-sized to `(mpkEnc D).len`) and
`pubWord_eq`. `wf_pubP` from `wf_ringIO1` + `loopOkB pubCode = true` (by `decide` on the
**abstract-register** code only; never on templates).

### P6 `Prog/RedPubPCost.lean`, `Prog/RedPubPDc.lean` — bounds (≈600 lines)
* `Closed Mo N K B pubCode` for register bounds `B` (inputs ≤ `2^101`, words `NK`, buffers their
  lengths); `bounds_ringIO1` gives length and time
  `210 ((2M+1)(4M+12)) + vmTime Mo N K B (instrTime …) pubCode + 300 (2M+3)`.
* `vmTime` of `rep` is `B t · (2 supB + 3 + body + 1) + 2`: generic bound
  `vmTime ≤ (#rounds) · poly(M)` per phase; at `Dc`: `M ≤ 2^102`, the largest loop is
  `|Pos × Dig| · |Col| · mb ≤ 2^4 · 2^34 · 2^17 · 2^42 = 2^97` rounds of `≤ 2^{2·102+30}` steps,
  so `≤ 2^{340}` ≪ `2^450`. Prove generically in `M`, then `norm_num` on symbolic powers
  (never unfold `Dc` terms; generalize atoms if `omega` recurses).
* `Lp = (mpkEnc Dc).len` (`≤ 2^125`: `|Pos×Dig×Fin 2×Col|·NK ≈ 2^4·2^34·2·2^17·2^40 = 2^96`).
* States: `pubP.size ≤ 2^200` from the `RingVM.compile` size lemmas (`VMSize`) and the
  `O(log)` template builders (`natP`).

### P7 `Comps` field
With `setupP` (`Prog/RedSetupP*.lean`), `keyP`, `authP`, `chalP` from the other agents:
`law_pub σ _ := law_pubP σ` (`spS` unfolds to `(mpkEnc D).enc (redView D (rawF D σ)).1`, which is
`pubK D σ` by `rfl`), `wf_pub := wf_pubP`, `len_pub` from P6.

## Notes / hazards
* `Prog/DecMachineCode.lean` (uncommitted, `len_col` clash with `SetupConf`) — the RedPubP files
  do **not** import it; `RedChalMath`/`RedChalPhases` do (import them only without `SetupConf`).
* `Col (setting D).τ` vs `Col D.K`: defeq but blocks `rw` (motive / instance mismatch). Use
  `refine (lemma …).trans ?_`, `show`, or state helper lemmas with `D.K`.
* Matrices vs functions: `matE` lemmas take `Fin 2 → α → Rg D`; apply them with `exact`/`refine`,
  not `rw`, on `Matrix` arguments.
