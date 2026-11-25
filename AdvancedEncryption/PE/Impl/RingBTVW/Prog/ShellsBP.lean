import PE.Impl.RingBTVW.Prog.FrontBPCost
import PE.Impl.RingBTVW.Prog.WfSpecBridge
import PE.Impl.RingBTVW.Prog.DecGenP

/-!
# `KeyGen` and `Dec` with the front end for branching programs

The shells `keyGenF`, `decGenF` (and the key component `keyPF` of the reductions) take a front end
meeting `FrontSpec`. Here the front end is `frontBP c.L` (the length tests, the bit `f(0)` by the
authorization program at `attr0`, the compiler; `R = 70`, framed on the tapes `1, 83, …, 153` by
`eF`), at the store width `512`:

* **`frontSpec_frontBP`**: `FrontSpec (frontBP n) n 512 (frontBTn n bpLen) (fun _ => frontBA bpLen)
  (36 n + 2^56)`: its block word is `bit0 C :: rpW 512 (bpRP (tablesOf C))` (`bwBP0_eq`);
* `keyGenP`, `keyMachineP`, `run_keyMachineP`, `keyMachineP_short`, `keyMachineP_long`;
* `decGenP`, `decMachineP`, `deterministic_decMachineP`, `decMachineP_law`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

theorem frontG_congr {n : ℕ} {V : List Bool → Prop} {bw bw' : List Bool → List Bool}
    (h : ∀ C, V C → bw C = bw' C) (C : List Bool) : frontG n V bw C = frontG n V bw' C := by
  unfold frontG
  by_cases h1 : C.length ≤ n
  · by_cases h2 : V C
    · simp [h1, h2, h C h2]
    · simp [h1, h2]
  · simp [h1]

/-- **The front end for branching programs at the neutral names.** -/
theorem frontSpec_frontBP (n : ℕ) :
    FrontSpec (frontBP n) n 512 (frontBTn n bpLen) (fun _ => frontBA bpLen) (36 * n + 2 ^ 56) where
  wf := (frontSpecG_frontBP n).wf
  coinFree := (frontSpecG_frontBP n).coinFree
  law C := by
    rw [(frontSpecG_frontBP n).law C, frontG_congr (fun C h => bwBP0_eq h) C]
  ph := (frontSpecG_frontBP n).ph
  size := (frontSpecG_frontBP n).size

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-! ### `KeyGen` -/

variable (hk c) in
/-- **The program of `KeyGen`** with the front end `frontBP c.L`. -/
noncomputable def keyGenP (bfX : XProg 256) (cf : KeyCfg) : XProg 256 :=
  keyGenF hk c eF (frontBP c.L) bfX 512 cf

variable (hk c) in
/-- **The machine of `KeyGen`**: input on tape `255` (at most `nKG + 1` bits loaded), output on
tape `0`. -/
noncomputable def keyMachineP (bfX : XProg 256) (cf : KeyCfg) : Machine :=
  keyMachineF hk c eF (frontBP c.L) bfX 512 cf

theorem wf_keyGenP {bfX : XProg 256} (hbf : BfSpec hk c bfX 512) (cf : KeyCfg) :
    (keyGenP hk c bfX cf).WF :=
  wf_keyGenF eF (frontSpec_frontBP c.L).wf hbf cf

theorem run_keyMachineP {bfX : XProg 256} (hbf : BfSpec hk c bfX 512) (cf : KeyCfg)
    (hcf : cf.Valid hk c) (msk : SKey hk c) (C : List Bool) :
    (keyMachineP hk c bfX cf).run (SigabaNeo.encodeTuple [pw, (mskEnc hk c).enc msk, C]) =
      if C.length ≤ c.L then (RingBTVW.keyM hk c msk C).map fun sk =>
        SigabaNeo.encodeTuple [(skEnc hk c).enc sk]
      else PMF.pure (SigabaNeo.encodeTuple []) :=
  run_keyMachineF frEmb_eF (frontSpec_frontBP c.L) hbf cf hcf msk C

theorem keyMachineP_short {bfX : XProg 256} (hbf : BfSpec hk c bfX 512) (cf : KeyCfg)
    (hcf : cf.Valid hk c) (msk : SKey hk c) (C : List Bool) (hC : C.length ≤ c.L) :
    (keyMachineP hk c bfX cf).run (SigabaNeo.encodeTuple [pw, (mskEnc hk c).enc msk, C]) =
      (RingBTVW.keyM hk c msk C).map fun sk => SigabaNeo.encodeTuple [(skEnc hk c).enc sk] := by
  rw [run_keyMachineP hbf cf hcf, if_pos hC]

theorem keyMachineP_long {bfX : XProg 256} (hbf : BfSpec hk c bfX 512) (cf : KeyCfg)
    (hcf : cf.Valid hk c) (msk : SKey hk c) (C : List Bool) (hC : ¬ C.length ≤ c.L) :
    (keyMachineP hk c bfX cf).run (SigabaNeo.encodeTuple [pw, (mskEnc hk c).enc msk, C]) =
      PMF.pure (SigabaNeo.encodeTuple []) := by
  rw [run_keyMachineP hbf cf hcf, if_neg hC]

/-! ### `Dec` -/

variable (hk c) in
/-- **The program of `Dec`** with the front end `frontBP c.L`. -/
noncomputable def decGenP (cfX : XProg 256) : XProg 256 :=
  decGenF hk c eF (frontBP c.L) cfX

variable (hk c) in
/-- **The machine of `Dec`**: input on tape `255` (at most `nDec + 1` bits loaded), output on
tape `0`. -/
noncomputable def decMachineP (cfX : XProg 256) : Machine :=
  decMachineF hk c eF (frontBP c.L) cfX

theorem wf_decGenP {cfX : XProg 256} (hcf : CfSpec hk c cfX 512) : (decGenP hk c cfX).WF :=
  wf_decGenF eF (frontSpec_frontBP c.L).wf hcf

theorem deterministic_decMachineP {cfX : XProg 256} (hcf : CfSpec hk c cfX 512) :
    (decMachineP hk c cfX).Deterministic :=
  deterministic_decMachineF eF (frontSpec_frontBP c.L).coinFree hcf

theorem decMachineP_law {cfX : XProg 256} (hcf : CfSpec hk c cfX 512) (hK2 : 2 ≤ K)
    (sk : SK hk c) (C : List Bool) (ct : CT hk c) (hL : C.length ≤ c.L) :
    (decMachineP hk c cfX).run
        (SigabaNeo.encodeTuple [pw, (skEnc hk c).enc sk, C, (ctEnc hk c).enc ct]) =
      PMF.pure (SigabaNeo.encodeTuple [decM hk c sk C ct]) :=
  decMachineF_law frEmb_eF (frontSpec_frontBP c.L) hcf hK2 sk C ct hL

end AdvancedEncryption.RingBTVW.Prog
