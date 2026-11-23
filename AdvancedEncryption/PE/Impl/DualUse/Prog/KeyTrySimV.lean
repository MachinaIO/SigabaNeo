import PE.Impl.DualUse.Prog.KeyTightTry
import PE.Impl.DualUse.Prog.KeyTrySimLaw

/-!
# The simulated key try, per tape

`ub_keyTry` (`PE.Impl.DualUse.Prog.KeyPTime`) bounds the simulated key try `keyTrySimCoinsP` of the
reductions' key component uniformly by `23 (M + 1)² + tbC · (2M + 1)^tbD` (`tbD = 8`,
`tbC ≤ 20000`): `2^2039` at `M ≈ 2^251`. As for the real key try (`KeyTightTry`):

* `absRun_keyTrySim`: the abstract interpreter on `keyTrySimP ⨾ clr 3` from the store `σKS` (the
  first `90` tapes of `σKR`: the templates of `keyTmpl` at their lengths, the data words — output,
  public key, the word of `W_f` — at the top, the norm word and `powW` at `K` bits, the coins and
  their counter at `m`, scratch blank) yields the sweeps `wKS`, a polynomial in the top and
  `N, K, k, d, nT, P, B, m`, each loop charged its own counter (checked by `decide +kernel`);
* **`ph_keyTrySim_v`**: the simulated key try from per-tape bounds below `σKS` takes at most
  `coinT S m + (2 top + 3) · wKS` steps.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open scoped SigabaNeo.Tape.Prog

namespace KeySV

open Sym

/-- **The abstract store at the simulated key try**: the first `90` tapes of `σKR`. -/
def σKS : Asg := KeyV.σKR.take 90

/-- The store after the simulated key try. -/
def oKS : Asg := ((absRun 8 (ProgKey.keyTrySimP ⨾ Prog.clr 3) σKS).map (·.1)).getD []
/-- **The sweeps of the simulated key try.** -/
def wKS : Poly := ((absRun 8 (ProgKey.keyTrySimP ⨾ Prog.clr 3) σKS).map (·.2)).getD []

set_option maxRecDepth 100000 in
theorem absRun_keyTrySim : absRun 8 (ProgKey.keyTrySimP ⨾ Prog.clr 3) σKS = some (oKS, wKS) := by
  decide +kernel

theorem aGet_σKS {j : ℕ} (hj : j < 90) : aGet σKS j = aGet KeyV.σKR j := by
  simp only [σKS, aGet, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]

end KeySV

set_option maxRecDepth 100000 in
open KeySV in
/-- **The simulated key try, per tape**: from bounds `γ` below the top whose coins and counter, set
to the template `γ 25`, fit `σKS`. -/
theorem ph_keyTrySim_v (ρ : List ℕ) (γ : Fin 90 → ℕ)
    (hin : Function.update (Function.update γ 3 (γ 25)) 41 (γ 25) ≤ Sym.bnd ρ σKS)
    (htop : ∀ j, γ j ≤ Sym.top ρ) :
    Ph (.prog ProgKey.keyTrySimCoinsP) γ
      (coinT (Sym.top ρ) (γ 25) + (2 * Sym.top ρ + 3) * Sym.pEval ρ wKS) (capB ρ oKS) := by
  have h1 := ph_coinsAt (r := (3 : Fin 90)) (t := 25) (c := 41) (b := 42) (by decide) γ htop
  have htop' : ∀ j, Function.update (Function.update γ 3 (γ 25)) 41 (γ 25) j ≤ Sym.top ρ := by
    intro j; simp only [Function.update_apply]; split_ifs <;> exact htop _
  have h2 := ph_absRun absRun_keyTrySim ρ hin htop'
  exact fun ℓ hℓ => (h1.seq h2) ℓ hℓ

end AdvancedEncryption.DualUse.Prog
