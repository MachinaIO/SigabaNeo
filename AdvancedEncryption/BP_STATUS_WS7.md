# WS7 status

- M4 (laws) committed 30932975: `law_bpCompC` (compiler, `PE/Impl/DualUse/Prog/BpCompLaw.lean`),
  `law_authBPC` (authorization, `Prog/AuthBP.lean`), `law_lenEqP` (length test,
  `SigabaNeo/Lib/Machines/Prog/LenEq.lean`). Built on WS1's M3 (merged `t3/bp-ws1` at e58a15c7).
- Bounds (`Prog/BpCompCost.lean`, `SigabaNeo/Lib/Machines/Prog/AppendWCost.lean`):
  `bounds_bpCompC` (≤ 2^126 steps, tapes ≤ 2^62, inputs ≤ 481·2^40 bits), `size_bpCompC` (≤ 2^27),
  `bounds_authBPC` (≤ 2^108 steps, tapes ≤ 2^49, words ≤ 2^49 bits), `size_authBPC` (≤ 2^17),
  `lenEqP_bounds`, `size_lenEqP`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
