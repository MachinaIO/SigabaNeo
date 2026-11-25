import SigabaNeoStd.Lattices.ProgAlgo.SimStepT

/-!
# Per-tape bounds of the Ring-GSW step of the simulation

`simStepP ginvGswP : Prog 132` (the step of the simulation on joint words with the Ring-GSW gadget,
`r = 2`), certified like the top-row step (`SimStepT.lean`): its `G̲⁻¹` is a split, two calls of
`ginvP` on the halves, a join; the matrix products and ring operations are the summaries of
`SpecT`. **`xsound_simStepG`**: from inputs below `σStG2` (operands `V = 4k NK + 2dk NK + NK`,
templates of `SimPre` with `r = 2` and of `GPreGsw`, scratch below the top), the tapes end below
`σStGOut` and the step takes at most `pEval ρ cStepG2` steps.
-/

namespace SigabaNeo.Tape

namespace Prog

namespace StepT

open _root_.SigabaNeo.Tape.Sym SpecT

set_option maxRecDepth 100000

/-- `V = 4k NK + 2dk NK + NK`, the length of a joint word of the predicate's simulation. -/
def pVG : Poly := [([0, 1, 1, 1], 4), ([0, 1, 1, 1, 1], 2), ([0, 1, 1], 1)]

/-- The per-tape bounds of the step's tapes (`SimPre` with `r = 2`, `GPreGsw`). -/
def σStG : Asg := [pVG, pVG, pVG, qK, qN, mo' 1 [1, 1], pC 2, mo' 2 [0, 0, 1], mo' 2 [0, 0, 1],
  mo' 2 [0, 0, 1, 1], pC 1, pC 1, qd, mo' 4 [1, 1, 1], mo' 2 [1, 1, 1, 1], pVG, mo' 4 [1, 0, 1],
  mo' 2 [1, 0, 1, 1], [], mo' 4 [1, 1, 1], mo' 2 [1, 1, 1, 1], mo' 1 [1, 1]] ++
  List.replicate 64 [] ++ [qK, mo' 2 [1, 0, 1], qk, mo' 4 [1, 1, 2], mo' 2 [1, 1, 1],
    mo' 2 [1, 1, 1], [], mo' 2 [1, 1, 2], mo' 2 [1, 1, 2]]

/-- The bound of every tape of the step. -/
def qTG : Poly := (σStG ++ [mo' 4 [1, 1, 2]]).foldl pJoin []

def θMatG (m n l : Poly) : List Poly := [qTG, qN, qK, m, n, l, []]
def θRingG (N' : Poly) : List Poly := [qTG, N', qK]

open XAst

/-- `simStepP ginvGswP`, with its subprograms summarised. -/
def aStepG : XAst (fun _ => True) 132 :=
  .seq (.seq (.leaf (map sU splitP) qTG) (.leaf (map sV splitP) qTG)) <|
  .seq (.seq (.leaf (map (vG ∘ gsS) splitP) qTG) <|
    .seq (.call (vG ∘ gi0) ginvP (σGinv ++ List.replicate 29 pTop)
      (σGinv' ++ List.replicate 35 pTop) wGinv [qTG, qN, qK, [], [], [], qk] qTG
      (vG_inj.comp gi0_inj) sGinv) <|
    .seq (.call (vG ∘ gi1) ginvP (σGinv ++ List.replicate 29 pTop)
      (σGinv' ++ List.replicate 35 pTop) wGinv [qTG, qN, qK, [], [], [], qk] qTG
      (vG_inj.comp gi1_inj) sGinv) <|
    .seq (.leaf (map (vG ∘ gjJ) joinP) qTG) <|
    .leaf (map vG (clr 12 ⨾ clr 13 ⨾ clr 14 ⨾ clr 15 ⨾ clr 16)) qTG) <|
  .seq (.call mP1 matMulP _ _ wMat (θMatG (pC 2) (mo' 2 [0, 0, 1]) (mo' 2 [0, 0, 1])) qTG mP1_inj
    sMat) <|
  .seq (.call sO1 subRWP _ _ wAdd (θRingG (mo' 4 [1, 0, 1])) qTG sO1_inj sSub) <|
  .seq (.call mP2 matMulP _ _ wMat (θMatG qd (mo' 2 [0, 0, 1]) (mo' 2 [0, 0, 1])) qTG mP2_inj sMat) <|
  .seq (.call mS matMulP _ _ wMat (θMatG (pC 1) (pC 1) (mo' 2 [0, 0, 1, 1])) qTG mS_inj sMat) <|
  .seq (.call aSum addRWP _ _ wAdd (θRingG (mo' 2 [1, 0, 1, 1])) qTG aSum_inj sAdd) <|
  .seq (.call sO2 subRWP _ _ wAdd (θRingG (mo' 2 [1, 0, 1, 1])) qTG sO2_inj sSub) <|
  .seq (.call mM3 mulRWP _ _ wMul (θRingG qN) qTG mM3_inj sMul) <|
  .seq (.call sO3 subRWP _ _ wAdd (θRingG qN) qTG sO3_inj sSub) <|
  .seq (.leaf (map jO joinP) qTG) <|
  .leaf (clr 22 ⨾ clr 23 ⨾ clr 24 ⨾ clr 25 ⨾ clr 26 ⨾ clr 27 ⨾ clr 28 ⨾ clr 29 ⨾ clr 30 ⨾ clr 31 ⨾
    clr 32 ⨾ clr 33 ⨾ clr 34 ⨾ clr 35 ⨾ clr 36) qTG

/-- The inputs of the step with its scratch below the top. -/
def σStG2 : Asg := (List.range 132).map fun j =>
  if j < 22 ∨ (86 ≤ j ∧ j < 95) then aGet σStG j else qTG

/-- The store after the step (all its tapes). -/
def σStGOut : Asg := ((xabs 8 aStepG σStG2).map Prod.fst).getD []

/-- The steps of the step, from `σStG2`. -/
def cStepG2 : Poly := ((xabs 8 aStepG σStG2).map Prod.snd).getD []

theorem xabs_aStepG2 : xabs 8 aStepG σStG2 = some (σStGOut, cStepG2) := by decide +kernel

theorem map_vG_ginvGswP : map vG ginvGswP =
    map (vG ∘ gsS) splitP ⨾ (map (vG ∘ gi0) ginvP ⨾ (map (vG ∘ gi1) ginvP ⨾
      (map (vG ∘ gjJ) joinP ⨾ map vG (clr 12 ⨾ clr 13 ⨾ clr 14 ⨾ clr 15 ⨾ clr 16)))) := by
  simp only [ginvGswP, Prog.map, Prog.map_map]

theorem timeBoundT_toX_aStepG (ℓ : Fin 132 → ℕ) :
    XProg.timeBoundT aStepG.toX ℓ = Prog.timeBoundT (simStepP ginvGswP) ℓ := by
  rw [simStepP, map_vG_ginvGswP]; rfl

theorem lenBoundT_toX_aStepG (ℓ : Fin 132 → ℕ) :
    XProg.lenBoundT aStepG.toX ℓ = Prog.lenBoundT (simStepP ginvGswP) ℓ := by
  rw [simStepP, map_vG_ginvGswP]; rfl

/-- **The summary of the Ring-GSW step at every value of `N, K, k, d`.** -/
theorem xsound_simStepG :
    XSound (fun _ => True) (.prog (simStepP ginvGswP)) σStG2 σStGOut cStepG2 := by
  intro ρ _ ℓ hℓ
  have h := xabs_sound 8 aStepG xabs_aStepG2 ρ trivial ℓ hℓ
  rw [timeBoundT_toX_aStepG, lenBoundT_toX_aStepG] at h
  exact h

/-- The outputs of the steps stay below their inputs. -/
theorem aLe_out_top : aLe σStOut σSt2 = true := by decide +kernel
theorem aLe_out_gsw : aLe σStGOut σStG2 = true := by decide +kernel

end StepT

end Prog

end SigabaNeo.Tape
