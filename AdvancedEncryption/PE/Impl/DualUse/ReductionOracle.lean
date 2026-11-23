import PE.Impl.DualUse.ReductionMachine
import PE.Impl.Game.HandlersMain
import PE.Impl.Game.HandlersP

/-!
# The reduction's oracle with the instance in the state

The handlers of `PE.Generic` serve `oracleW sp setupW` on states `(w, s)`: the instance word `w`
stays, and the selection draws the secret from `setupW w x`. For the challenger `specSim` of a
reduction, whose public key, keys and challenge depend on the instance, the secret is packed with
the instance (`spPack`, `setupPack`). Started from `(w, {})`, this oracle has the observations of
`specSim` for the instance `inst w` (`hgame_oracleW`): the `hgame` hypothesis of
`acceptProb_reduction`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d]
variable {Sec Inst : Type}

/-- The challenger reading the instance from the packed secret (the setup `st` is replaced by
the setup of the instance word in `oracleW`). -/
noncomputable def spPack (st : PUniv.Attr → PMF (Inst × Sec))
    (viewI : Inst → Sec → PK hk c × CT hk c) (sdI : Inst → Sec → SimData hk c) :
    Generic.Spec PUniv (Inst × Sec) where
  setup := st
  pub p := (pkEnc hk c).enc (viewI p.1 p.2).1
  key p := KGsim (sdI p.1 p.2)
  chal p μ := PMF.pure ((ctEnc hk c).enc (shiftCT hk c μ (viewI p.1 p.2).2))
  auth := authI hk c

/-- The setup of an instance word: the secret of its instance, packed with the instance. -/
noncomputable def setupPack (inst : List Bool → Inst) (setupI : Inst → PUniv.Attr → PMF Sec)
    (w : List Bool) (x : PUniv.Attr) : PMF (Inst × Sec) :=
  (setupI (inst w) x).map fun σ => (inst w, σ)

/-- **The oracle with the instance in the state has the observations of `specSim`.** -/
theorem hgame_oracleW (st : PUniv.Attr → PMF (Inst × Sec)) (inst : List Bool → Inst)
    (setupI : Inst → PUniv.Attr → PMF Sec) (viewI : Inst → Sec → PK hk c × CT hk c)
    (sdI : Inst → Sec → SimData hk c) {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) (w : List Bool) :
    (ProbOracleComp.runWith (Generic.oracleW (spPack st viewI sdI) (setupPack inst setupI))
        program (w, {})).map (fun r => Generic.obs (r.1, r.2.2)) =
      (ProbOracleComp.runWith (Generic.oracle (specSim (setupI (inst w)) (viewI (inst w))
        (sdI (inst w)))) program {}).map Generic.obs := by
  -- the instance word stays in the state
  have h1 : (ProbOracleComp.runWith
        (Generic.oracle { spPack st viewI sdI with setup := setupPack inst setupI w }) program
        ({} : Generic.GState PUniv (Inst × Sec))).map (fun r => (r.1, (w, r.2))) =
      ProbOracleComp.runWith (Generic.oracleW (spPack st viewI sdI) (setupPack inst setupI))
        program (w, {}) :=
    ProbOracleComp.runWith_map_state
      (Generic.oracle { spPack st viewI sdI with setup := setupPack inst setupI w })
      (Generic.oracleW (spPack st viewI sdI) (setupPack inst setupI)) (fun s => (w, s))
      (fun q s => rfl) program ({} : Generic.GState PUniv (Inst × Sec))
  -- `specSim` for `inst w`, with the secret packed with `inst w`, is the packed challenger
  have h2 : (ProbOracleComp.runWith (Generic.oracle (specSim (hk := hk) (c := c) (setupI (inst w))
        (viewI (inst w)) (sdI (inst w)))) program ({} : Generic.GState PUniv Sec)).map
        (fun r => (r.1, Generic.mapSec (fun σ => (inst w, σ)) r.2)) =
      ProbOracleComp.runWith
        (Generic.oracle { spPack st viewI sdI with setup := setupPack inst setupI w }) program
        ({} : Generic.GState PUniv (Inst × Sec)) := by
    refine ProbOracleComp.runWith_map_state _ _ (Generic.mapSec (fun σ => (inst w, σ))) ?_ program {}
    intro q s
    rcases s with ⟨attr, sec, msg, bad⟩
    by_cases hq : q.1 = selectOp
    · rcases attr with _ | x
      · rcases hd : decode PUniv.encAttr q.2 with _ | x
        · simp [Generic.oracle, Generic.oracleWith, hq, hd, Generic.mapSec]
        · simp only [Generic.oracle, Generic.oracleWith, hq, hd, if_true, PMF.map_comp,
            Generic.mapSec, setupPack]
          rfl
      · simp [Generic.oracle, Generic.oracleWith, hq, Generic.mapSec]
    · by_cases hk' : q.1 = keyGenOp
      · rcases attr with _ | x <;> rcases sec with _ | σ <;>
          simp [Generic.oracle, Generic.oracleWith, hq, hk', Generic.mapSec, PMF.map_comp,
            Function.comp_def, specSim, spPack, selectOp, keyGenOp]
      · rcases attr with _ | x <;> rcases sec with _ | σ <;> rcases msg with _ | μ <;>
          rcases hd : decode PUniv.encMsg q.2 with _ | μ' <;>
          simp [Generic.oracle, Generic.oracleWith, hq, hk', hd, Generic.mapSec, PMF.map_comp,
            Function.comp_def, specSim, spPack]
  rw [← h1, PMF.map_comp, ← h2, PMF.map_comp]
  rfl

/-- **The packed challenger answers long predicates with a fixed word and never authorizes
them**: the hypothesis of the per-query handlers, with `K₀ = L` and the empty answer. -/
theorem longKeys_spPack (st : PUniv.Attr → PMF (Inst × Sec))
    (viewI : Inst → Sec → PK hk c × CT hk c) (sdI : Inst → Sec → SimData hk c)
    (Ok : Inst × Sec → Prop) : Generic.LongKeys (spPack st viewI sdI) Ok c.L [] where
  key p C _ hC := by
    show KGsim (sdI p.1 p.2) C = PMF.pure []
    unfold KGsim
    rw [if_neg (by omega)]
  auth C x hC := authI_long hk c C x hC

end AdvancedEncryption.DualUse
