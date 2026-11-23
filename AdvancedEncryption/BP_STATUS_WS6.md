# WS6 status (register evaluator and the `W_f` block)

Branch `t3/bp-ws6` (base `db15ea12`, `t3/bp-ws1` merged at M0/M3 `e58a15c7`).

## Commits

| What | Commit |
| --- | --- |
| `ValReg.lean`: register loop on slot programs, `exec_rloopC` | `57f429ca` |
| `ValReg.lean`: generic loop `rloopX` (destination code + `DstOk`), stream instance `rloopC` | `ff5be93d` |
| `ValReg.lean`: stage-I counter loop `rloopG`, `exec_rloopG` (results `gl` of the gate loop) | `436cd4b5` |
| Stage I: `fhatC`, `gswC` on `rloopG`, store `C :: ins ++ C^(W−10)`; `L1c`, `L1Gc` recomputed | `37030f8a` |
| `WfRCert.lean`: stage-II runs at the numbers of `confA` (kernel-checked) | `e7147f6d` |
| M4: `ValRegRP.lean` (`RP` link), merge of `t3/bp-ws1` | `efe42733` |

## M4 (done)

* `SigabaNeo/Lib/Lattices/ProgAlgo/ValReg.lean`: `rl` (slot semantics, `List.set`), `wrC` (write a
  slot: two shift loops over the destination word), `rloopX iC dC blk`, `exec_rloopX`,
  `rloopC blk` (destination popped from the stream `spW W sp`), `exec_rloopC`, and the stage-I
  `rloopG T blk` (gate `t` writes slot `|T| + 1 + t`), `exec_rloopG`, `rl_gsSP`.
* `SigabaNeo/Lib/Lattices/ProgAlgo/ValRegRP.lean`: `rpSP rp` (slot program of `rp : RP (Fin n) W'`),
  `spW_rpSP : spW S (rpSP rp) = RP.rpW S rp`, `rl_rpSP` (slots = `RP.run` on the registers),
  `outw_rloopC` (`OUTW` = `SLP.valueOf` of `RP.toSLP rp` at the wire of the register written last,
  via `RP.run_eq_valueOf`), instances `outw_rloopC_gate` (value of the predicate, step `f`) and
  `outw_rloopC_nand` (`bw (fhatV …)`), `fhatV_eq_valueOf`.

## Stage I (done)

`10 → nA` in the proofs: `ValIns`, `ValGsw`, `ValFhat`, `ValMain` are generic in the number `n` of
inputs (the length of the template `T10`); `WfB2`, `WfB2Time`, `SimKeyStore`, `KeyWfWords` use
`nA` (templates `T10 ↦ nA`, `INSW`/`TINS ↦ nA · S`, `TW9 ↦ W − nA + 1`, `oXG = offPsi + nA · lenPsi`).
`WfB2` is now generic in the stream word `G`, the count `m`, the run codes and the predicate
program `P` (`S1 … a G m`, `S3 … T m`, `law_prepTRest`, `law_prepGRest`, `law_runX`, `law_runGX`,
`w6_pos`, `key_run P …`, `final_eq`); the date-window instance `wfSpec_wfB2` is unchanged in
meaning. `ValMain`: `exec_fhatPre`/`exec_gswPre` (the preambles) shared with the stream codes.

## Stage II block on register streams (done)

New files (the stage-I `wfB2` keeps building; swap at the switch):

* `SigabaNeo/Lib/Machines/Prog/CapN.lean`: `capN w` (template `false^w` by `natP`, ≈ `195 log₂ w`
  states), `law_capN`, `ph_capN`, `size_capN`.
* `SigabaNeo/Lib/Lattices/ProgAlgo/ValMainR.lean`: `fhatCR`, `gswCR` (register loop `rloopC`),
  `exec_fhatCR` (`OUTW = bw (fhatV … (RP.toSLP rp).1 ((RP.toSLP rp).2 ins'.dst))`), `exec_gswCR`
  (`OUTW = SLP.valueOf … f (RP.toSLP rp).1 ((RP.toSLP rp).2 ins'.dst)`).
* `Prog/WfB2S.lean`: `wfB2S hk c Ic W` (count of `3 W`-bit blocks, clear of the phase word,
  cap `capN Ic`, runs `runTR`/`runGR`), `w3_FOUT_R`, `w6_OUTW_R`, `predR rp ins' :=
  ((RP.toSLP rp).1, (RP.toSLP rp).2 ins'.dst)`, **`law_wfB2S`**, the structure **`WfSpecR`** and
  **`wfSpecR_wfB2S hk c Ic W hN hK : WfSpecR hk c (wfB2S hk c Ic W) W Ic`**.
* `Prog/WfB2SCoinFree.lean`: `coinFree_wfB2S`.
* `Prog/WfB2STime.lean`: phases (`ph_prepTS`, `ph_prepGS`, `ph_wfBodyS`, `ph_wfB2S`, `tTS_le`, …).
* `Prog/WfB2SConf.lean`: **`time_wfB2S_conf`** and `Prog/WfB2SSize.lean`: **`size_wfB2S_conf`**.
* `WfRCert.lean` now imports `WfB2S` (the stream codes are defined there only).

### Interface for WS5

```lean
structure WfSpecR (wfB : XProg 256) (W Ic : ℕ) : Prop where
  wf : wfB.WF
  law : ∀ (sd : SimData hk c) {W'} (rp : RP (Fin nA) W') (ins' : Instr (Fin nA) W'),
    nA + W' ≤ W → rp.length ≤ Ic → rp.getLast? = some ins' →
    wfB.law (io2 (R := 254) ((sdEnc hk c).enc sd) (RP.rpW W rp) []) =
      PMF.pure (Function.update (io2 (R := 254) ((sdEnc hk c).enc sd) [] []) 2
        (colsW N K k c.d (simWP sd (WB2.predR rp ins'))))
```

`simWP sd P` (`KeyWfWords`) is `simKeyMat … P`; `simW sd C = simWP sd (predC C)` (rfl). At the
switch WS5 needs `predC C = predR (bpRP (tablesOf C)) ins'` with `ins'` the last instruction
(WS1), `length_bpRP < 2^50 = Icn`, and `nA + W' ≤ 512` from `bnd_bpRP`.

Bounds, at `N = Nn = 2^36`, `K = Kn = 2^27`, `c.d = dn = 2^65`, `nA = nAn = 128`, `W = Wn = 512`,
`Ic = Icn = 2^50`, `treeHeight ≤ 66`, the offsets (`offB`, `offW`, `offPsi`, `offR`,
`offPsi + nA·lenPsi`) and `|sdEnc| ≤ Lbn = 2^260`, stream `≤ Lgn = 2^64` bits:

* `time_wfB2S_conf`: `timeBoundT (wfB2S hk c Icn Wn) (io2 Lsd Lg 0) ≤ 2^628` and every tape
  `≤ Malln = 2^262`; 256 tapes (`XProg 256`).
* `size_wfB2S_conf`: `(wfB2S hk c Icn Wn).size ≤ 2^25`.
* `coinFree_wfB2S`. Hypothesis `hnA : nA = nAn` (vacuous until the switch).

## Stage II certificate of the runs

`WfRCert.lean` at the numbers above: f̂ run `≤ 2^627`, predicate run `≤ 2^525`, every word
`≤ 2^261` bits, key sum (`Mskn = 2^262`) `≤ 2^607`.
