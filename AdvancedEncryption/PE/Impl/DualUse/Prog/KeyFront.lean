import PE.Impl.DualUse.SimKeyGame
import PE.Impl.DualUse.Prog.FrontSpec

/-!
# The front end of the simulated key query and the authorization flag

* **`authI_eq`**: the authorization flag of the experiment, classically `decide (Authorized …)`,
  is the explicit test `decide (|C| = bpLen) && !output (tablesOf C) x` (`bp_authorized_iff`),
  the bit the authorization program `authBPC` computes (`Prog/AuthBPX.lean`).
* **`KGsim_eq_front`**: the simulated key oracle depends on the query only through the output
  `frontW c.L W C` of a front end (`frontG c.L ValidC (blockWord W)`, `Prog/FrontSpec.lean`) and,
  for a program word, through the predicate `predC C` the `W_f` block reads from the stream of
  `blockWord W C`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}
variable {ms : Machines hk c}

variable (hk c) in
/-- **The authorization flag is the explicit test.** -/
theorem authI_eq (C : List Bool) (x : PUniv.Attr) :
    authI hk c C x = (decide (C.length = bpLen) && !output (tablesOf C) x) := by
  classical
  unfold authI
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact (bp_authorized_iff (impl hk c) rfl C x).trans (by simp)

open Classical in
/-- The simulated key oracle from the output of the front end. -/
noncomputable def kgOfFront (d : SimData hk c) (C : List Bool) : List Bool → PMF (List Bool)
  | [] => PMF.pure []
  | false :: _ => PMF.pure ((skEnc hk c).enc (d.mpk, dummyKey c))
  | true :: _ => (keyLaw c.Big c.Small c.hBig c.dec d.mpk (simTrap (Wt := TrapCol k) (simW d C))).map
      fun o => (skEnc hk c).enc (d.mpk, keyOfOutput o)

/-- **`KGsim` through the front end.** -/
theorem KGsim_eq_front (W : ℕ) (d : SimData hk c) (C : List Bool) :
    KGsim d C = kgOfFront d C (Prog.frontW c.L W C) := by
  unfold KGsim
  by_cases hl : C.length ≤ c.L
  · by_cases hw : ValidC C
    · rw [Prog.frontW, Prog.frontG_valid hl hw, if_pos hl, if_pos hw]; rfl
    · rw [Prog.frontW, Prog.frontG_short_not hl hw, if_pos hl, if_neg hw]; rfl
  · rw [Prog.frontW, Prog.frontG_long hl, if_neg hl]; rfl

end AdvancedEncryption.DualUse
