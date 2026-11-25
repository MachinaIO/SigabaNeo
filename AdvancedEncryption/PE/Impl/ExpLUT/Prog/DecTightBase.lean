import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMFlowClock
import PE.Impl.ExpLUT.Prog.DecMachineCode
open SigabaNeo.Tape.RingVM.Flow
/-!
# Tight clock of the `Dec` code: certificates of blocks (part 1)

The flow-sensitive abstract run `SigabaNeo.Tape.RingVM.Flow.absRun` (`DecTimeVM`) is sound but too slow to run on the
whole compiled `Dec` code at once in the kernel. Here it is run **block by block**, with the bound
vectors at the block boundaries given as literals, and the blocks are glued with generic lemmas on
`SigabaNeo.Tape.RingVM.Flow.CodeOK` (no concrete code is unfolded by the glue):

* `dtChk P c Bin Bout T`: the abstract run of `c` from `Bin` succeeds, ends below `Bout`
  (pointwise) and takes at most `T` steps; **`dtChk_sound`** gives `CodeOK`;
* `codeOK_seqT`, `codeOK_monoT`, `codeOK_nopT`: sequencing, weakening, the empty code;
* `dtP`: the parameters at the concrete dimensions (`N = 2^24`, `K = 2^16`), with the operation
  area `Mo = 2^40 = N K` and the templates of the template operations `Mt = 2^25 = 2 N`
  (**`dtP_valid`**);
* `pkL`: a packed bound vector from its nonzero entries.
-/

namespace AdvancedEncryption.ExpLUT.Prog.DecTight

set_option autoImplicit false

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.MersenneT
  SigabaNeo.Tape.Prog.SpecT
open SigabaNeo.Tape.RingVM.Flow

/-! ### Packed literals -/

/-- A packed bound vector from its nonzero entries `(register, bound)`. -/
def pkL (l : List (ℕ × ℕ)) : ℕ := l.foldl (fun B p => ps B p.1 p.2) 0

/-! ### Gluing `CodeOK` -/

theorem codeOK_seqT {Mo N K : ℕ} {p q : Code} {B B1 B2 : Fin 200 → ℕ} {T1 T2 : ℕ}
    (h1 : CodeOK Mo N K p B B1 T1) (h2 : CodeOK Mo N K q B1 B2 T2) :
    CodeOK Mo N K (.seq p q) B B2 (T1 + T2) := by
  intro ℓ hℓ
  obtain ⟨t1, n1⟩ := h1 ℓ hℓ
  obtain ⟨t2, n2⟩ := h2 _ n1
  exact ⟨by
    show XProg.timeBoundT (compile p) ℓ +
      XProg.timeBoundT (compile q) (XProg.lenBoundT (compile p) ℓ) ≤ T1 + T2
    omega, n2⟩

theorem codeOK_monoT {Mo N K : ℕ} {c : Code} {A B B' A' : Fin 200 → ℕ} {T T' : ℕ}
    (h : CodeOK Mo N K c B B' T) (h0 : A ≤ B) (h1 : B' ≤ A') (hT : T ≤ T') :
    CodeOK Mo N K c A A' T' := fun ℓ hℓ =>
  have h' := h ℓ (hℓ.trans (encB_mono Mo N K h0))
  ⟨h'.1.trans hT, h'.2.trans (encB_mono Mo N K h1)⟩

theorem codeOK_nopT (Mo N K : ℕ) (B : Fin 200 → ℕ) : CodeOK Mo N K .nop B B 3 :=
  codeOK_of_instr le_rfl (instrOK_nop Mo N K B) le_rfl

/-! ### Checked blocks -/

/-- **A checked block**: the abstract run from `Bin` ends below `Bout` within `T` steps. -/
def dtChk (P : VCP) (c : Code) (Bin Bout T : ℕ) : Bool :=
  match absRun P 8 c Bin with
  | some (B', T') => ble B' Bout && Nat.ble T' T
  | none => false

theorem dtChk_sound {P : VCP} (hP : P.Valid) {c : Code} {Bin Bout T : ℕ}
    (h : dtChk P c Bin Bout T = true) : CodeOK P.Mo P.N P.K c (toB Bin) (toB Bout) T := by
  unfold dtChk at h
  rcases hr : absRun P 8 c Bin with _ | ⟨B', T'⟩
  · rw [hr] at h; simp at h
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  exact codeOK_monoT (absRun_sound hP 8 c Bin B' T' hr) le_rfl (toB_le_of_ble h.1)
    (Nat.le_of_ble_eq_true h.2)

/-! ### The parameters -/

/-- The parameters of the clock at the concrete dimensions. -/
def dtP : VCP where
  Mo := 2 ^ 40
  N := 2 ^ 24
  K := 2 ^ 16
  Mt := 2 ^ 25
  cAdd := 43981203308551
  cMul := 26598341853148840878080024
  cCanon := 43981203308551
  cNeg := 12094627905551
  cDig := 666701678216211005451
  cRot := 664093482703027961859
  cAut := 516513381644882673674
  cRho := 15393297006595

theorem dtP_mono (p : Poly) (v : ℕ) (h : pEval (ρLd (2 ^ 40) (2 ^ 24) (2 ^ 16) (2 ^ 25)) p ≤ v) :
    ∀ m ≤ dtP.Mt, pEval (ρLd dtP.Mo dtP.N dtP.K m) p ≤ v := fun _ hm =>
  (pEval_ρLd_mono _ _ _ hm p).trans h

/-- **The parameters are valid.** -/
theorem dtP_valid : dtP.Valid where
  hNK := by decide
  hK := by decide
  hN := by decide
  hMt := by decide
  hW := by decide
  add := by decide
  mul := by decide +kernel
  canon := by decide +kernel
  neg := by decide +kernel
  dig := dtP_mono _ _ (by decide +kernel)
  rot := dtP_mono _ _ (by decide +kernel)
  aut := dtP_mono _ _ (by decide +kernel)
  rho := dtP_mono _ _ (by decide +kernel)

/-- The checked blocks at the concrete parameters. -/
theorem dtChk_ok {c : Code} {Bin Bout T : ℕ} (h : dtChk dtP c Bin Bout T = true) :
    CodeOK (2 ^ 40) (2 ^ 24) (2 ^ 16) c (toB Bin) (toB Bout) T :=
  dtChk_sound dtP_valid h

end AdvancedEncryption.ExpLUT.Prog.DecTight
