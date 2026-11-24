import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.Bounds
import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VM

/-!
# Cost certificates of the programs of the ring-word machine

The instructions of `RingVM` (`SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VM`) run the Mersenne
programs on the **operation area**, whose scratch tapes are not blank between instructions as far
as the per-tape length bounds know (the abstract interpreter bounds them by the top size only). So
the certificates here take every scratch tape at the top size `pTop` (and give the same sweep
polynomials as `Mersenne/Bounds.lean`), and the move programs of the instructions (`ValVM.inP`,
`outP`, `mvPc`, `dropPc`, `cp`) get certificates with exact claims on all their tapes.

`frame_of_check'`: a checked program framed in a larger store: its time, the claimed bounds of its
first tapes, the top bound on all its tapes, and the other tapes unchanged.
-/

set_option Elab.async false

namespace SigabaNeo.Tape

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.SpecT SigabaNeo.Tape.Prog.MersenneT

namespace RingVM

/-! ### The operations, with the scratch at the top size -/

/-- The sweeps of `canonRP`: `40 N K + 44 N + 7`. -/
def wCanon : Poly := [([], 7), ([0, 1], 44), ([0, 1, 1], 40)]

theorem checkT_addRMP : check 8 addRMP (σRing ++ List.replicate 23 pTop) σRing' wAddRM = true := by
  decide +kernel
theorem checkT_subRMP : check 8 subRMP (σRing ++ List.replicate 23 pTop) σRing' wAddRM = true := by
  decide +kernel
theorem checkT_mulRMP : check 8 mulRMP (σRing ++ List.replicate 32 pTop) σRing' wMulRM = true := by
  decide +kernel
theorem checkT_canonRP : check 8 canonRP (σRing ++ List.replicate 23 pTop) σRing' wCanon = true := by
  decide +kernel
theorem checkT_notP : check 8 notP (σNot ++ List.replicate 9 pTop) σNot' wNotM = true := by
  decide +kernel
theorem checkT_digitRWP : check 8 digitRWP (σDigit ++ List.replicate 26 pTop) σDigit' wDigit = true := by
  decide +kernel
/-- `digitRWP` with a template of any length `m` (the digit index). -/
def wDigitM : Poly :=
  wDigit ++ [([0, 1, 1, 1], 18), ([0, 1, 0, 1], 44), ([0, 0, 0, 1], 11), ([0, 1, 2, 0], 18)]
theorem checkT_digitRWPm : check 8 digitRWP ([pTop, pNK, pm, pK, pN] ++ List.replicate 26 pTop)
    [pNK, pNK, pm, pK, pN] wDigitM = true := by decide +kernel
theorem checkT_rotBP : check 8 rotBP (σJ ++ List.replicate 25 pTop) σJ' wRotB = true := by
  decide +kernel
theorem checkT_autMP : check 8 autMP (σJ ++ List.replicate 20 pTop) σJ' wAut = true := by
  decide +kernel
theorem checkT_rhoJP : check 8 rhoJP (σRho ++ List.replicate 3 pTop) σRho' wRhoJ = true := by
  decide +kernel

/-! ### The moves (variables `M N K m n l`: `m`, `n`, `l` are register lengths) -/

/-- The polynomials `n`, `l`. -/
def pn' : Poly := mo 1 [0, 0, 0, 1]
def pl' : Poly := mo 1 [0, 0, 0, 0, 1]

/-- `inP` on `[area i, NK, word a (m), X0, X1, X2]`: the area gets `N K` bits. -/
def wIn : Poly := [([], 30), ([0, 1, 1], 10)]
theorem check_inP : check 8 ValVM.inP [pTop, pNK, pm, [], [], []] [pNK, pNK, pm, [], [], []] wIn =
    true := by decide +kernel

/-- `outP` on `[area 0 (NK), area 1, area 2, word d (m)]`. -/
def wOut : Poly := [([], 10)]
theorem check_outP : check 8 ValVM.outP [pNK, pTop, pTop, pm] [[], [], [], pNK] wOut = true := by
  decide +kernel

/-- `mvPc` on `[stream s (m), register d (n), X1, X2, template c (l)]`. -/
def wMv : Poly := [([], 20), ([0, 0, 0, 0, 0, 1], 10)]
theorem check_mvPc : check 8 ValVM.mvPc [pm, pn', [], [], pl'] [pm, pn', [], [], pl'] wMv = true := by
  decide +kernel

/-- `dropPc` on `[word t (m), X1, word c (n)]`. -/
def wDr : Poly := [([], 20), ([0, 0, 0, 0, 1], 10)]
theorem check_dropPc : check 8 ValVM.dropPc [pm, [], pn'] [pm, [], pn'] wDr = true := by
  decide +kernel

/-- `cp 0 1` on `[word d (m), word s (n)]`. -/
def wCp : Poly := [([], 5)]
theorem check_cp : check 8 (Prog.cp 0 1 : Prog 2) [pm, pn'] [pn', pn'] wCp = true := by
  decide +kernel

/-! ### Framed -/

theorem frame_of_check' {fuel n k : ℕ} {p : Prog n} {σ claim : Asg} {w : Poly}
    (h : check fuel p σ claim w = true) (ρ : List ℕ) (e : Fin n ↪ Fin k) {ℓ : Fin k → ℕ}
    (hℓ : (fun j => ℓ (e j)) ≤ bnd ρ σ) (hM : ∀ j, ℓ (e j) ≤ top ρ) :
    XProg.timeBoundT (.frame e (.prog p)) ℓ ≤ (2 * top ρ + 3) * pEval ρ w ∧
      (∀ j : Fin n, j.val < claim.length →
        XProg.lenBoundT (.frame e (.prog p)) ℓ (e j) ≤ pEval ρ (aGet claim j.val)) ∧
      (∀ j : Fin n, XProg.lenBoundT (.frame e (.prog p)) ℓ (e j) ≤ top ρ) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog p)) ℓ t = ℓ t := by
  obtain ⟨h1, h2, h3⟩ := frame_of_check h ρ e hℓ hM
  obtain ⟨-, h4, -⟩ := bounds_of_check h ρ hℓ hM
  refine ⟨h1, h2, fun j => ?_, h3⟩
  show embedF e ℓ _ (e j) ≤ _
  rw [embedF_apply_self]; exact h4 j

end RingVM

end SigabaNeo.Tape
