import SigabaNeoStd.Lattices.ProgAlgo.SimStep
import SigabaNeoStd.Lattices.ProgAlgo.SpecT
import SigabaNeoStd.Machines.Prog.XAbs

/-!
# Per-tape bounds of the step of the simulation

`simStepP ginvTopP : Prog 132` (the step of the simulation on joint words with the top-row gadget,
`run_simStepP`) is certified by the framed abstract interpreter (`SigabaNeoStd.Machines.Prog.XAbs`):
its splits and its join are analysed directly, its `G̲⁻¹`, matrix products and ring operations are
calls of the certified summaries of `SpecT` (`matMulP`, `ginvP`, `subRWP`, `addRWP`, `mulRWP`) at
the shapes of the step (`pSubst`).

The variables: `0` unused (the top of each level is a polynomial), `1` `N`, `2` `K`, `3` `k`,
`4` `d`. The inputs (`σSt`): the operands `V = 2k NK + 2dk NK + NK` on `1`, `2` (and `0`), the
templates of `SimPre` with `r = 1`, those of `GPreTop`, scratch blank. **`boundsT_simStepP`**: on
those per-tape bounds, the step keeps its templates and inputs, and takes at most
`pEval ρ cStep` steps, every primitive charged the longest of its own tapes (`qT`, about `V`).
-/

namespace SigabaNeo.Tape

namespace Prog

namespace StepT

open _root_.SigabaNeo.Tape.Sym SpecT

set_option maxRecDepth 100000

/-! ### The summaries, with scratch below the top -/

theorem check_matMulP_top : check 8 matMulP (σMat ++ List.replicate 49 pTop) σMat' wMat = true := by
  decide +kernel
theorem check_ginvP_top : check 8 ginvP (σGinv ++ List.replicate 29 pTop) σGinv' wGinv = true := by
  decide +kernel
theorem check_subRWP_top : check 8 subRWP (σRing ++ List.replicate 23 pTop) σRing' wAdd = true := by
  decide +kernel
theorem check_addRWP_top : check 8 addRWP (σRing ++ List.replicate 23 pTop) σRing' wAdd = true := by
  decide +kernel
theorem check_mulRWP_top : check 8 mulRWP (σRing ++ List.replicate 33 pTop) σRing' wMul = true := by
  decide +kernel

theorem sMat : Sound matMulP (σMat ++ List.replicate 49 pTop) (σMat' ++ List.replicate 59 pTop) wMat :=
  sound_of_check check_matMulP_top
theorem sGinv : Sound ginvP (σGinv ++ List.replicate 29 pTop) (σGinv' ++ List.replicate 35 pTop)
    wGinv := sound_of_check check_ginvP_top
theorem sSub : Sound subRWP (σRing ++ List.replicate 23 pTop) (σRing' ++ List.replicate 28 pTop)
    wAdd := sound_of_check check_subRWP_top
theorem sAdd : Sound addRWP (σRing ++ List.replicate 23 pTop) (σRing' ++ List.replicate 28 pTop)
    wAdd := sound_of_check check_addRWP_top
theorem sMul : Sound mulRWP (σRing ++ List.replicate 33 pTop) (σRing' ++ List.replicate 38 pTop)
    wMul := sound_of_check check_mulRWP_top

/-! ### The variables and the inputs -/

/-- The monomial `c · N^a K^b k^c d^e` (exponents `e`). -/
def mo' (c : ℕ) (e : List ℕ) : Poly := [(0 :: e, c)]

def qN : Poly := mo' 1 [1]
def qK : Poly := mo' 1 [0, 1]
def qk : Poly := mo' 1 [0, 0, 1]
def qd : Poly := mo' 1 [0, 0, 0, 1]
/-- `V = 2k NK + 2dk NK + NK`, the length of a joint word. -/
def pV : Poly := [([0, 1, 1, 1], 2), ([0, 1, 1, 1, 1], 2), ([0, 1, 1], 1)]

/-- The per-tape bounds of the step's tapes: operands, templates (`SimPre` with `r = 1`,
`GPreTop`), scratch blank. -/
def σSt : Asg := [pV, pV, pV, qK, qN, mo' 1 [1, 1], pC 1, mo' 2 [0, 0, 1], mo' 2 [0, 0, 1],
  mo' 2 [0, 0, 1, 1], pC 1, pC 1, qd, mo' 2 [1, 1, 1], mo' 2 [1, 1, 1, 1], pV, mo' 2 [1, 0, 1],
  mo' 2 [1, 0, 1, 1], [], mo' 2 [1, 1, 1], mo' 2 [1, 1, 1, 1], mo' 1 [1, 1]] ++
  List.replicate 64 [] ++ [qK, mo' 2 [1, 0, 1], qk, mo' 4 [1, 1, 2]]

/-- The bound of every tape of the step (the longest word, `V` plus lower terms). -/
def qT : Poly := (σSt ++ [mo' 4 [1, 1, 2]]).foldl pJoin []

def θMat (m n l : Poly) : List Poly := [qT, qN, qK, m, n, l, []]
def θRing (N' : Poly) : List Poly := [qT, N', qK]

/-! ### The certificate -/

open XAst

/-- `simStepP ginvTopP`, with its subprograms summarised. -/
def aStep : XAst (fun _ => True) 132 :=
  .seq (.seq (.leaf (map sU splitP) qT) (.leaf (map sV splitP) qT)) <|
  .seq (.call (vG ∘ gT) ginvP (σGinv ++ List.replicate 29 pTop) (σGinv' ++ List.replicate 35 pTop)
    wGinv [qT, qN, qK, [], [], [], qk] qT (vG_inj.comp gT_inj) sGinv) <|
  .seq (.call mP1 matMulP _ _ wMat (θMat (pC 1) (mo' 2 [0, 0, 1]) (mo' 2 [0, 0, 1])) qT mP1_inj sMat) <|
  .seq (.call sO1 subRWP _ _ wAdd (θRing (mo' 2 [1, 0, 1])) qT sO1_inj sSub) <|
  .seq (.call mP2 matMulP _ _ wMat (θMat qd (mo' 2 [0, 0, 1]) (mo' 2 [0, 0, 1])) qT mP2_inj sMat) <|
  .seq (.call mS matMulP _ _ wMat (θMat (pC 1) (pC 1) (mo' 2 [0, 0, 1, 1])) qT mS_inj sMat) <|
  .seq (.call aSum addRWP _ _ wAdd (θRing (mo' 2 [1, 0, 1, 1])) qT aSum_inj sAdd) <|
  .seq (.call sO2 subRWP _ _ wAdd (θRing (mo' 2 [1, 0, 1, 1])) qT sO2_inj sSub) <|
  .seq (.call mM3 mulRWP _ _ wMul (θRing qN) qT mM3_inj sMul) <|
  .seq (.call sO3 subRWP _ _ wAdd (θRing qN) qT sO3_inj sSub) <|
  .seq (.leaf (map jO joinP) qT) <|
  .leaf (clr 22 ⨾ clr 23 ⨾ clr 24 ⨾ clr 25 ⨾ clr 26 ⨾ clr 27 ⨾ clr 28 ⨾ clr 29 ⨾ clr 30 ⨾ clr 31 ⨾
    clr 32 ⨾ clr 33 ⨾ clr 34 ⨾ clr 35 ⨾ clr 36) qT

/-- **The steps of the step**: the cost found by the interpreter. -/
def cStep : Poly := ((xabs 8 aStep σSt).map Prod.snd).getD []

/-- The claimed bounds afterwards: the operands, templates and gadget words kept (tapes `0 … 21`). -/
def σSt' : Asg := σSt.take 22

theorem xcheck_aStep : xcheck 8 aStep σSt σSt' cStep = true := by decide +kernel

theorem map_vG_ginvTopP : map vG ginvTopP = map (vG ∘ gT) ginvP := Prog.map_map gT vG ginvP

theorem timeBoundT_toX_aStep (ℓ : Fin 132 → ℕ) :
    XProg.timeBoundT aStep.toX ℓ = Prog.timeBoundT (simStepP ginvTopP) ℓ := by
  rw [simStepP, map_vG_ginvTopP]; rfl

theorem lenBoundT_toX_aStep (ℓ : Fin 132 → ℕ) :
    XProg.lenBoundT aStep.toX ℓ = Prog.lenBoundT (simStepP ginvTopP) ℓ := by
  rw [simStepP, map_vG_ginvTopP]; rfl

/-- **Per-tape bounds of the step**: from bounds below `σSt` (at the values `ρ` of `N, K, k, d`),
the tapes `0 … 21` end below `σSt'` and the step takes at most `pEval ρ cStep` steps. -/
theorem boundsT_simStepP (ρ : List ℕ) {ℓ : Fin 132 → ℕ} (hℓ : ℓ ≤ bnd ρ σSt) :
    (∀ t : Fin 132, t.val < 22 → Prog.lenBoundT (simStepP ginvTopP) ℓ t ≤ pEval ρ (aGet σSt' t.val)) ∧
      Prog.timeBoundT (simStepP ginvTopP) ℓ ≤ pEval ρ cStep := by
  have h := bounds_of_xcheck xcheck_aStep ρ trivial hℓ
  rw [timeBoundT_toX_aStep, lenBoundT_toX_aStep] at h
  exact ⟨fun t ht => h.1 t (by simp [σSt', σSt]; omega), h.2⟩

/-! ### The summary of the step in a machine

In a machine (`SigabaNeoStd.Machines.Prog.ValVM`) the step is called repeatedly; its scratch tapes,
blank in fact, are bounded abstractly by the top `qT` after a call. The summary is taken from
inputs with scratch below `qT` (`σSt2`), so that calls compose. -/

/-- The inputs of the step with its scratch below the top. -/
def σSt2 : Asg := (List.range 132).map fun j =>
  if j < 22 ∨ (86 ≤ j ∧ j < 90) then aGet σSt j else qT

/-- The store after the step (all its tapes). -/
def σStOut : Asg := ((xabs 8 aStep σSt2).map Prod.fst).getD []

/-- The steps of the step, from `σSt2`. -/
def cStep2 : Poly := ((xabs 8 aStep σSt2).map Prod.snd).getD []

theorem xabs_aStep2 : xabs 8 aStep σSt2 = some (σStOut, cStep2) := by decide +kernel

/-- **The summary of the step at every value of `N, K, k, d`**: inputs below `σSt2`, outputs
below `σStOut`, at most `pEval ρ cStep2` steps. -/
theorem xsound_simStepP : XSound (fun _ => True) (.prog (simStepP ginvTopP)) σSt2 σStOut cStep2 := by
  intro ρ _ ℓ hℓ
  have h := xabs_sound 8 aStep xabs_aStep2 ρ trivial ℓ hℓ
  rw [timeBoundT_toX_aStep, lenBoundT_toX_aStep] at h
  exact h

end StepT

end Prog

end SigabaNeo.Tape
