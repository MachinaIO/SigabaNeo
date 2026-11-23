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

## Stage I (partly done)

Done: the block runs the gate list `gsW W (parse C)` (still its input) as the trivial register
program (`rloopG`), the whole tree green, `time_wfB2_conf` unchanged (`≤ 2^556`).

Open: `10 → nA` in `ValIns`, `ValGsw`, `ValMain`, `ValFhat`, `WfB2*` (the codes already take the
input count from the template `T10`; only the proofs fix `10`); the stage-II `wfB2` (stream input,
`countP (3 W)`, the count capped by a `natP` template of `2^50`) and `wfSpec` for streams.

## Stage II certificate (done for the runs)

`WfRCert.lean` at `N = 2^36`, `K = 2^27`, `d = 2^65`, `W = 512`, `nA = 128`, SimData `≤ 2^260`,
stream `≤ 2^64` bits, `≤ 2^50` instructions: f̂ run `≤ 2^627` (≈ 2^626), predicate run `≤ 2^525`,
every word `≤ 2^261` bits, key sum `≤ 2^608`. Block expected `≤ 2^628`.
