/-
UNTRUSTED. A helper for assembling downloaded proofs (`python/sigaba_neo.py`).

`p2m_apply% f` is `f` applied to every binder of the declaration being elaborated, in order. The
assembler closes a Prove2Me statement `theorem x (a : A) … : P := by sorry` with
`:= p2m_apply% Ns.solution`, where `Ns.solution : ∀ (a : A) …, P` is its downloaded proof. The
kernel checks the result; a wrong term only fails to build.
-/
import Lean

open Lean Elab Term Meta

namespace SigabaNeo.Assemble

elab "p2m_apply% " f:ident : term <= expected => do
  let n ← realizeGlobalConstNoOverloadWithInfo f
  let fn ← mkConstWithFreshMVarLevels n
  let xs := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.toExpr
  let e := mkAppN fn xs
  unless ← isDefEq (← inferType e) expected do
    throwError "p2m_apply%: {f} applied to the binders has type{indentExpr (← inferType e)}\n\
      but the statement is{indentExpr expected}"
  instantiateMVars e

end SigabaNeo.Assemble
