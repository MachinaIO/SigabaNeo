import PE.Impl.DualUse.Security
import PE.Impl.DualUse.IdealViews
import PE.Impl.DualUse.Impl
import PE.Impl.Game.Generic

/-!
# The hybrids of attribute hiding as experiments with oracles

The adversary of `PE.AttributeHiding` interacts with the challenger through oracles. With the
challenger's secret the pair `(mpk, ct₀)` of the public key and the challenge for the message `0`
(`specV`), the key oracle answering from `mpk` only (any `KGi`, the ideal key law in the end) and
the challenge for `μ` the shift of `ct₀` by `μ · ⌊q/2⌋` (`shiftCT`), the hybrids of
`DualUse.game_close` become changes of the law `V x` of the secret for the selected attribute `x`:

* statistical steps (hybrids 1, 4, 6) move the experiment by at most `|Date| = 1024` times the
  step's distance (`Generic.closeTo_runWith_setup`);
* the Ring-LWE steps (hybrids 3, 5) are averages over one instance (`Generic.runWith_bind_setup`):
  the whole experiment, as a function of the instance, is the distinguisher.

`chain_real`: the real experiment is close to the final one.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped ENNReal

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The challenge for the message `μ` from the challenge for `0`. -/
noncomputable def shiftCT (μ : Bool) (ct : CT hk c) : CT hk c :=
  { ct with κ := ct.κ + if μ then (Sdw (N := N) hk).half else 0 }

theorem encrypt_shift (mpk : PK hk c) (x : Fin 10 → Bool) (μ : Bool)
    (r : EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k)) :
    encrypt mpk x μ r = shiftCT hk c μ (encrypt mpk x false r) := by
  cases μ <;> simp [encrypt, shiftCT]

instance : Fintype dateUniverse.Attr := inferInstanceAs (Fintype Date)
instance : DecidableEq dateUniverse.Attr := inferInstanceAs (DecidableEq Date)

variable (encMPK : PK hk c → List Bool) (encCT : CT hk c → List Bool)
  (KGi : PK hk c → List Bool → PMF (List Bool)) (authB : List Bool → Date → Bool)

/-- The challenger with the secret `(mpk, ct₀)` drawn from `V x`. -/
noncomputable def specV (V : Date → PMF (PK hk c × CT hk c)) :
    Generic.Spec dateUniverse (PK hk c × CT hk c) where
  setup := V
  pub σ := encMPK σ.1
  key σ := KGi σ.1
  chal σ μ := PMF.pure (encCT (shiftCT hk c μ σ.2))
  auth := authB

/-- The observable law of the experiment of the adversary `A` against `specV V`. -/
noncomputable def gameV (A : Machine 3) (V : Date → PMF (PK hk c × CT hk c)) :=
  (A.runWith (Generic.oracle (specV hk c encMPK encCT KGi authB V)) (paramsWord dateUniverse params)
    {}).map Generic.obs

/-! ### The laws of the hybrids -/

section Views

variable [NeZero c.d]

/-- The flooding errors. -/
noncomputable def lawEc : PMF ((Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index →
    Matrix (Fin 1) (Col k) (Rg N K)) :=
  haveI : NeZero (2 ^ c.w) := ⟨by positivity⟩
  floodRows (S := Sdw (N := N) hk) (2 ^ c.w)

/-- The error law of the ring. -/
noncomputable def χR : PMF (Rg N K) := polyOf c.χc

/-- The coins other than the encodings' errors. -/
noncomputable def lawRestC : PMF (Rest (Sdw (N := N) hk) (Fin c.d) (TrapCol k)) :=
  lawRestNF lawRmBin (χR c)

/-- The trapdoor part of the real setup. -/
noncomputable def lawB₁r : PMF (Matrix (Fin 1) (TrapCol k) (Rg N K)) :=
  (inst3Real (k := k) (χR c)).map (toB₁ (Sdw (N := N) hk))

/-- `H0`: the real `(mpk, ct₀)`. -/
noncomputable def V0 (x : Date) : PMF (PK hk c × CT hk c) :=
  realGame (Wd := Fin c.d) (lawEc hk c) (χR c) (bitsOf x) false

/-- `H1`: `B_j = B₀ W_j + ψ_j G̲`. -/
noncomputable def V1 (x : Date) : PMF (PK hk c × CT hk c) :=
  viewW (lawB₁r hk c) (PMF.uniformOfFintype _) (lawRestC hk c) (lawEc hk c) (bitsOf x) false
    (realCj (bitsOf x))

/-- `H2`: flooded encodings. -/
noncomputable def V2 (x : Date) : PMF (PK hk c × CT hk c) :=
  viewW (lawB₁r hk c) (PMF.uniformOfFintype _) (lawRestC hk c) (lawEc hk c) (bitsOf x) false
    floodCj

/-- The view of hybrid 3 for the Ring-LWE pair `(a, b)`. -/
noncomputable def F3 (x : Date)
    (ab : Matrix (Fin 1) (Col k) (Rg N K) × Matrix (Fin 1) (Col k) (Rg N K)) :
    PMF (PK hk c × CT hk c) :=
  viewW (PMF.pure (toB₁ (Sdw (N := N) hk) ab)) (PMF.uniformOfFintype _) (lawRestC hk c)
    (lawEc hk c) (bitsOf x) false floodCj

/-- `H3`: `B₁` uniform. -/
noncomputable def V3 (x : Date) : PMF (PK hk c × CT hk c) :=
  viewW lawB₁u (PMF.uniformOfFintype _) (lawRestC hk c) (lawEc hk c) (bitsOf x) false floodCj

/-- The view of hybrid 5 for the normal-form instance. -/
noncomputable def F5 (x : Date) (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) :
    PMF (PK hk c × CT hk c) :=
  reduction5 (S := Sdw (N := N) hk) lawRmBin (lawEc hk c) (bitsOf x) false i

/-- `H5`: the ciphertext's `(c₀, c₁, κ)` uniform. -/
noncomputable def V5 (x : Date) : PMF (PK hk c × CT hk c) :=
  h5View (Wd := Fin c.d) lawB₁u (lawEc hk c) (bitsOf x) false

/-- `H6`: the final view. -/
noncomputable def V6 (x : Date) : PMF (PK hk c × CT hk c) :=
  finalView (Wd := Fin c.d) lawB₁u (lawEc hk c) (bitsOf x) false

theorem V0_close (x : Date) : CloseTo (V0 hk c x) (V1 hk c x) (delta1 (Sdw (N := N) hk) (Fin c.d)) := by
  have h := (hybrid1 (Wd := Fin c.d) (lawB₁r hk c) (PMF.uniformOfFintype _)
    (lawCoins (lawRestC hk c) (lawEc hk c)) (bitsOf x) false).symm
  have h2 := viewW_real_eq (S := Sdw (N := N) hk) (Wd := Fin c.d) (lawB₁r hk c)
    (PMF.uniformOfFintype _) (lawRestC hk c) (lawEc hk c) (bitsOf x) false
  unfold V0 V1 realGame
  convert h using 2
  all_goals first | rfl | exact h2

theorem V1_close {ε : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestC hk c).support, ∀ w : JC (Sdw (N := N) hk) → (Fin c.d → Bool),
      CloseTo ((lawEc hk c).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hk c) ε)
    (x : Date) : CloseTo (V1 hk c x) (V2 hk c x) ε :=
  (hybrid4 (lawB₁r hk c) (PMF.uniformOfFintype _) (lawRestC hk c) (lawEc hk c) (bitsOf x) false
    hflood).symm

theorem V2_eq (x : Date) : V2 hk c x = (inst3Real (k := k) (χR c)).bind (F3 hk c x) := by
  unfold V2 lawB₁r
  refine (viewW_bind_B₁ (S := Sdw (N := N) hk) (Wd := Fin c.d) (lawRestC hk c) (lawEc hk c)
    _ _ (bitsOf x) false floodCj).trans ?_
  rw [PMF.bind_map]
  rfl

theorem V3_eq (x : Date) : V3 hk c x = inst3Unif.bind (F3 hk c x) := by
  unfold V3
  refine (viewW_bind_B₁ (S := Sdw (N := N) hk) (Wd := Fin c.d) (lawRestC hk c) (lawEc hk c)
    lawB₁u _ (bitsOf x) false floodCj).trans ?_
  rw [← inst3Unif_map (S := Sdw (N := N) hk), PMF.bind_map]
  rfl

theorem V3_eq' (x : Date) : V3 hk c x = (nfReal (χR c)).bind (F5 hk c x) :=
  real5_eq _ _ _ _ _

theorem V5_eq (x : Date) : V5 hk c x = nfUnif.bind (F5 hk c x) :=
  (unif5_eq _ _ _).symm

theorem V5_close (x : Date) : CloseTo (V5 hk c x) (V6 hk c x) (delta6 (Sdw (N := N) hk) (Fin c.d)) :=
  hybrid6 _ _ _ _

/-- A statistical step of the experiment. -/
theorem gameV_close (A : Machine 3) {V V' : Date → PMF (PK hk c × CT hk c)} {ε : ℝ≥0∞}
    (h : ∀ x, CloseTo (V x) (V' x) ε) :
    CloseTo (gameV hk c encMPK encCT KGi authB A V) (gameV hk c encMPK encCT KGi authB A V')
      (Fintype.card Date * ε) := by
  unfold gameV Machine.runWith
  have := Generic.closeTo_runWith_setup (specV hk c encMPK encCT KGi authB V)
    (A.machine.runOracle A.time (paramsWord dateUniverse params)) V' (fun _ => ε) h
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  exact this.map _

/-- A Ring-LWE step of the experiment: an average over one instance. -/
theorem gameV_bind (A : Machine 3) {Inst : Type} (inst : PMF Inst)
    (F : Date → Inst → PMF (PK hk c × CT hk c)) :
    gameV hk c encMPK encCT KGi authB A (fun x => inst.bind (F x)) =
      inst.bind fun i => gameV hk c encMPK encCT KGi authB A fun x => F x i := by
  unfold gameV Machine.runWith
  exact Generic.runWith_bind_setup (specV hk c encMPK encCT KGi authB fun x => inst.bind (F x))
    inst F _

/-- **The real experiment is close to the final one**, up to `1024` times the statistical terms
and the advantages `δ₃`, `δ₅` of the two experiments-as-distinguishers on Ring-LWE instances. -/
theorem chain_real (A : Machine 3) {β : Type} (Dc : _ → PMF β) {ε δ₃ δ₅ : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestC hk c).support, ∀ w : JC (Sdw (N := N) hk) → (Fin c.d → Bool),
      CloseTo ((lawEc hk c).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hk c) ε)
    (h₃ : CloseTo ((inst3Real (k := k) (χR c)).bind fun ab =>
        (gameV hk c encMPK encCT KGi authB A fun x => F3 hk c x ab).bind Dc)
      (inst3Unif.bind fun ab => (gameV hk c encMPK encCT KGi authB A fun x => F3 hk c x ab).bind Dc) δ₃)
    (h₅ : CloseTo ((nfReal (χR c)).bind fun i =>
        (gameV hk c encMPK encCT KGi authB A fun x => F5 hk c x i).bind Dc)
      (nfUnif.bind fun i => (gameV hk c encMPK encCT KGi authB A fun x => F5 hk c x i).bind Dc) δ₅) :
    CloseTo ((gameV hk c encMPK encCT KGi authB A (V0 hk c)).bind Dc)
      ((gameV hk c encMPK encCT KGi authB A (V6 hk c)).bind Dc)
      (Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + Fintype.card Date * ε + δ₃ + δ₅ +
        Fintype.card Date * delta6 (Sdw (N := N) hk) (Fin c.d)) := by
  have g01 := (gameV_close hk c encMPK encCT KGi authB A (V0_close hk c)).bind_left Dc
  have g12 := (gameV_close hk c encMPK encCT KGi authB A (V1_close hk c hflood)).bind_left Dc
  have g56 := (gameV_close hk c encMPK encCT KGi authB A (V5_close hk c)).bind_left Dc
  have e2 : gameV hk c encMPK encCT KGi authB A (V2 hk c) =
      (inst3Real (k := k) (χR c)).bind fun ab => gameV hk c encMPK encCT KGi authB A fun x => F3 hk c x ab := by
    rw [← gameV_bind]; congr 1; funext x; exact V2_eq hk c x
  have e3 : gameV hk c encMPK encCT KGi authB A (V3 hk c) =
      inst3Unif.bind fun ab => gameV hk c encMPK encCT KGi authB A fun x => F3 hk c x ab := by
    rw [← gameV_bind]; congr 1; funext x; exact V3_eq hk c x
  have e3' : gameV hk c encMPK encCT KGi authB A (V3 hk c) =
      (nfReal (χR c)).bind fun i => gameV hk c encMPK encCT KGi authB A fun x => F5 hk c x i := by
    rw [← gameV_bind]; congr 1; funext x; exact V3_eq' hk c x
  have e5 : gameV hk c encMPK encCT KGi authB A (V5 hk c) =
      nfUnif.bind fun i => gameV hk c encMPK encCT KGi authB A fun x => F5 hk c x i := by
    rw [← gameV_bind]; congr 1; funext x; exact V5_eq hk c x
  have h₃' : CloseTo ((gameV hk c encMPK encCT KGi authB A (V2 hk c)).bind Dc)
      ((gameV hk c encMPK encCT KGi authB A (V3 hk c)).bind Dc) δ₃ := by
    rw [e2, e3, PMF.bind_bind, PMF.bind_bind]; exact h₃
  have h₅' : CloseTo ((gameV hk c encMPK encCT KGi authB A (V3 hk c)).bind Dc)
      ((gameV hk c encMPK encCT KGi authB A (V5 hk c)).bind Dc) δ₅ := by
    rw [e3', e5, PMF.bind_bind, PMF.bind_bind]; exact h₅
  exact (((g01.trans g12).trans h₃').trans h₅').trans g56

end Views

/-! ### The ideal side -/

section Ideal

variable [NeZero c.d]

/-- The coins of `Enc`. -/
noncomputable def lawCoinsC : PMF (EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k)) :=
  lawCoins (lawRestC hk c) (lawEc hk c)

/-- `I0`: the ideal view, with the real public key and the simulator's uniform ciphertext. -/
noncomputable def VI0 (_ : Date) : PMF (PK hk c × CT hk c) :=
  idealView (S := Sdw (N := N) hk) (Wd := Fin c.d) (lawB₁r hk c)

/-- `I1`: `B_j = B₀ W_j + ψ_j G̲` for an internal encryption of `x`. -/
noncomputable def VI1 (x : Date) : PMF (PK hk c × CT hk c) :=
  hybI1 (lawB₁r hk c) (PMF.uniformOfFintype _) (lawCoinsC hk c) (bitsOf x)

/-- The view of the ideal side's Ring-LWE step for the pair `(a, b)`. -/
noncomputable def FI (x : Date)
    (ab : Matrix (Fin 1) (Col k) (Rg N K) × Matrix (Fin 1) (Col k) (Rg N K)) :
    PMF (PK hk c × CT hk c) :=
  hybI1 (PMF.pure (toB₁ (Sdw (N := N) hk) ab)) (PMF.uniformOfFintype _) (lawCoinsC hk c) (bitsOf x)

/-- `I2`: `B₁` uniform. -/
noncomputable def VI2 (x : Date) : PMF (PK hk c × CT hk c) :=
  hybI1 lawB₁u (PMF.uniformOfFintype _) (lawCoinsC hk c) (bitsOf x)

theorem VI1_close (x : Date) :
    CloseTo (VI0 hk c x) (VI1 hk c x) (delta1 (Sdw (N := N) hk) (Fin c.d)) :=
  (hybridI1 (S := Sdw (N := N) hk) (Wd := Fin c.d) (lawB₁r hk c) (lawCoinsC hk c) (bitsOf x)).symm

theorem VI1_eq (x : Date) : VI1 hk c x = (inst3Real (k := k) (χR c)).bind (FI hk c x) := by
  unfold VI1 lawB₁r
  refine (hybI1_bind_B₁ (S := Sdw (N := N) hk) (Wd := Fin c.d) _ _ _ (bitsOf x)).trans ?_
  rw [PMF.bind_map]
  rfl

theorem VI2_eq (x : Date) : VI2 hk c x = inst3Unif.bind (FI hk c x) := by
  unfold VI2
  refine (hybI1_bind_B₁ (S := Sdw (N := N) hk) (Wd := Fin c.d) lawB₁u _ _ (bitsOf x)).trans ?_
  rw [← inst3Unif_map (S := Sdw (N := N) hk), PMF.bind_map]
  rfl

theorem VI2_close (x : Date) :
    CloseTo (VI2 hk c x) (V6 hk c x) (delta1 (Sdw (N := N) hk) (Fin c.d)) := by
  have h := hybridI1 (S := Sdw (N := N) hk) (Wd := Fin c.d) lawB₁u (lawCoinsC hk c) (bitsOf x)
  rw [idealView_eq_final lawB₁u (lawEc hk c) (bitsOf x) false] at h
  exact h

/-- **The ideal experiment is close to the final one.** -/
theorem chain_ideal (A : Machine 3) {β : Type} (Dc : _ → PMF β) {δ : ℝ≥0∞}
    (h₃ : CloseTo ((inst3Real (k := k) (χR c)).bind fun ab =>
        (gameV hk c encMPK encCT KGi authB A fun x => FI hk c x ab).bind Dc)
      (inst3Unif.bind fun ab => (gameV hk c encMPK encCT KGi authB A fun x => FI hk c x ab).bind Dc) δ) :
    CloseTo ((gameV hk c encMPK encCT KGi authB A (VI0 hk c)).bind Dc)
      ((gameV hk c encMPK encCT KGi authB A (V6 hk c)).bind Dc)
      (Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + δ +
        Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d)) := by
  have g01 := (gameV_close hk c encMPK encCT KGi authB A (VI1_close hk c)).bind_left Dc
  have g23 := (gameV_close hk c encMPK encCT KGi authB A (VI2_close hk c)).bind_left Dc
  have e1 : gameV hk c encMPK encCT KGi authB A (VI1 hk c) =
      (inst3Real (k := k) (χR c)).bind fun ab => gameV hk c encMPK encCT KGi authB A fun x => FI hk c x ab := by
    rw [← gameV_bind]; congr 1; funext x; exact VI1_eq hk c x
  have e2 : gameV hk c encMPK encCT KGi authB A (VI2 hk c) =
      inst3Unif.bind fun ab => gameV hk c encMPK encCT KGi authB A fun x => FI hk c x ab := by
    rw [← gameV_bind]; congr 1; funext x; exact VI2_eq hk c x
  have h₃' : CloseTo ((gameV hk c encMPK encCT KGi authB A (VI1 hk c)).bind Dc)
      ((gameV hk c encMPK encCT KGi authB A (VI2 hk c)).bind Dc) δ := by
    rw [e1, e2, PMF.bind_bind, PMF.bind_bind]; exact h₃
  exact (g01.trans h₃').trans g23

end Ideal

end AdvancedEncryption.DualUse
