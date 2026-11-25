import SigabaNeoStd.Machines.Prog.CoinFreeX
import SigabaNeoStd.Machines.Prog.Machine

/-!
# Coin-free programs compile to deterministic machines

`CoinIndep m`: the transitions of a fair-coin machine ignore the coin. It holds for deterministic
machines and is preserved by the combinators of the compiler (`seq`, `extendTapes`, `branch`,
`branchBit`, `repeatUntilBlank`), so the compiled machine of a coin-free program ignores the coin
(`coinIndep_compile`, `XProg.coinIndep_compile`), and so do the explicit machines
(`XProg.deterministic_toMachineT`).
-/

namespace SigabaNeo.Tape

open Cslib Turing MultiTapeMachine MultiTapePTM

variable {k : ℕ}

/-- The transitions ignore the coin. -/
def CoinIndep {S : Type} (m : MultiTapePTM k Bool S Empty) : Prop :=
  ∀ q a w o, m.tr q a w o true = m.tr q a w o false

theorem coinIndep_ofDeterministic {S : Type} (tm : MultiTapeTM k Bool S) :
    CoinIndep (ofDeterministic tm : MultiTapePTM k Bool S Empty) := fun _ _ _ _ => rfl

theorem CoinIndep.seq {S₁ S₂ : Type} {m₁ : MultiTapePTM k Bool S₁ Empty}
    {m₂ : MultiTapePTM k Bool S₂ Empty} (h₁ : CoinIndep m₁) (h₂ : CoinIndep m₂) :
    CoinIndep (m₁.seq m₂) := by
  intro q a w o
  rcases q with q | q
  · show Sequential.leftAction _ (m₁.tr q a w o true) = Sequential.leftAction _ (m₁.tr q a w o false)
    rw [h₁]
  · show Sequential.rightAction (m₂.tr q a w o true) = Sequential.rightAction (m₂.tr q a w o false)
    rw [h₂]

theorem CoinIndep.extendTapes {k' : ℕ} {S : Type} {m : MultiTapePTM k Bool S Empty}
    (h : CoinIndep m) (e : Fin k ↪ Fin k') : CoinIndep (m.extendTapes e) := by
  intro q a w o
  show Action.extendTapes e (m.tr q a _ o true) = Action.extendTapes e (m.tr q a _ o false)
  rw [h]

theorem CoinIndep.branch {S₁ S₂ : Type} (i : Fin k) {m₁ : MultiTapePTM k Bool S₁ Empty}
    {m₂ : MultiTapePTM k Bool S₂ Empty} (h₁ : CoinIndep m₁) (h₂ : CoinIndep m₂) :
    CoinIndep (MultiTapePTM.branch i m₁ m₂) := by
  intro q a w o
  rcases q with _ | q | q
  · rfl
  · show Action.mapState _ (m₁.tr q a w o true) = Action.mapState _ (m₁.tr q a w o false)
    rw [h₁]
  · show Action.mapState _ (m₂.tr q a w o true) = Action.mapState _ (m₂.tr q a w o false)
    rw [h₂]

theorem CoinIndep.branchBit {S₁ S₂ : Type} (i : Fin k) {m₁ : MultiTapePTM k Bool S₁ Empty}
    {m₂ : MultiTapePTM k Bool S₂ Empty} (h₁ : CoinIndep m₁) (h₂ : CoinIndep m₂) :
    CoinIndep (Tape.branchBit i m₁ m₂) := by
  intro q a w o
  rcases q with _ | q | q
  · rfl
  · show Action.mapState _ (m₁.tr q a w o true) = Action.mapState _ (m₁.tr q a w o false)
    rw [h₁]
  · show Action.mapState _ (m₂.tr q a w o true) = Action.mapState _ (m₂.tr q a w o false)
    rw [h₂]

theorem CoinIndep.repeatUntilBlank {S : Type} (i : Fin k) {m : MultiTapePTM k Bool S Empty}
    (h : CoinIndep m) : CoinIndep (MultiTapePTM.repeatUntilBlank i m) := by
  intro q a w o
  rcases q with q | _
  · show RepeatUntilBlank.runAction (m.tr q a w o true) =
      RepeatUntilBlank.runAction (m.tr q a w o false)
    rw [h]
  · rfl

namespace Prog

theorem coinIndep_compile : ∀ (p : Prog k), p.CoinFree → CoinIndep (compile p)
  | prim _, _ => coinIndep_ofDeterministic _
  | coin _, h => absurd h (by simp [CoinFree, coinFreeB])
  | seq p q, h => by
    simp only [CoinFree, coinFreeB, Bool.and_eq_true] at h
    exact (coinIndep_compile p h.1).seq (coinIndep_compile q h.2)
  | ifBlank i p q, h => by
    simp only [CoinFree, coinFreeB, Bool.and_eq_true] at h
    exact CoinIndep.branch i (coinIndep_compile q h.2) (coinIndep_compile p h.1)
  | ifBit i p q, h => by
    simp only [CoinFree, coinFreeB, Bool.and_eq_true] at h
    exact CoinIndep.branchBit i (coinIndep_compile p h.1) (coinIndep_compile q h.2)
  | loop i body, h =>
    CoinIndep.branch i (CoinIndep.repeatUntilBlank i
      ((coinIndep_ofDeterministic _).seq (coinIndep_compile body h))) (coinIndep_ofDeterministic _)

end Prog

namespace XProg

theorem coinIndep_compile : ∀ {k : ℕ} (p : XProg k), p.CoinFree → CoinIndep (compile p)
  | _, prog p, h => Prog.coinIndep_compile p h
  | _, frame e p, h => (coinIndep_compile p h).extendTapes e
  | _, seq p q, h => by
    simp only [CoinFree, coinFreeB, Bool.and_eq_true] at h
    exact (coinIndep_compile p h.1).seq (coinIndep_compile q h.2)
  | _, ifBlank i p q, h => by
    simp only [CoinFree, coinFreeB, Bool.and_eq_true] at h
    exact CoinIndep.branch i (coinIndep_compile q h.2) (coinIndep_compile p h.1)
  | _, ifBit i p q, h => by
    simp only [CoinFree, coinFreeB, Bool.and_eq_true] at h
    exact CoinIndep.branchBit i (coinIndep_compile p h.1) (coinIndep_compile q h.2)
  | _, loop i body, h =>
    CoinIndep.branch i (CoinIndep.repeatUntilBlank i
      ((coinIndep_ofDeterministic _).seq (coinIndep_compile body h))) (coinIndep_ofDeterministic _)

end XProg

/-- A machine built by `Machine.ofPTM` from a machine ignoring the coin is deterministic. -/
theorem deterministic_ofPTM {S : Type} [Finite S] {m : MultiTapePTM k Bool S Empty}
    (h : CoinIndep m) (time : ℕ) : (Machine.ofPTM m time).Deterministic := by
  intro q a w o
  exact congrArg (ptmAction (Finite.equivFin S)) (h ((Finite.equivFin S).symm q) a w _)

theorem XProg.deterministic_toMachineT (p : XProg k) (hc : p.CoinFree) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachineT i₀ o n).Deterministic :=
  deterministic_ofPTM (((coinIndep_ofDeterministic _).seq (XProg.coinIndep_compile p hc)).seq
    (coinIndep_ofDeterministic _)) _

end SigabaNeo.Tape
