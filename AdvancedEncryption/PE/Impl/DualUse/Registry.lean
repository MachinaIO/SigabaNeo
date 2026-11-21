import PE.Impl.DualUse.Security
import SigabaNeo.Lib.Lattices.RingLWEInst

/-!
# The Ring-LWE instances of the security proof are the registry's

Over `R_q = ℤ_q[X]/(X^N + 1)`, with the error law `χ = polyOf χc` (independent coefficients from
`χc`), the instance laws of the reductions are images of the ring-level Ring-LWE laws
(`SigabaNeo.Lattices.ringRealOn`), which are the registry's (`ringLWE_realLaw_eq`):

* `nfReal_eq`, `nfUnif_eq`: hybrid 5, normal form (secret law = error law), with the samples
  indexed by `Wd ⊕ W ⊕ W ⊕ Unit` and the public parts negated.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open scoped ENNReal

variable {N q : ℕ} [NeZero q] {k : ℕ} {Wd : Type} [Fintype Wd] [DecidableEq Wd]

/-- The samples of hybrid 5: `B₀`, `a`, `z`, `p`. -/
abbrev Idx5 (Wd : Type) (k : ℕ) := Wd ⊕ Col k ⊕ Col k ⊕ Unit

/-- A uniform function on a sum is two independent uniform functions. -/
theorem uniform_sum_bind {α β γ R : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype R] [Nonempty R] (g : (α ⊕ β → R) → PMF γ) :
    (PMF.uniformOfFintype (α ⊕ β → R)).bind g =
      (PMF.uniformOfFintype (α → R)).bind fun f₁ =>
        (PMF.uniformOfFintype (β → R)).bind fun f₂ => g (Sum.elim f₁ f₂) := by
  rw [← bind_uniform_equiv (Equiv.sumArrowEquivProdArrow α β R).symm g, uniform_prod_bind]
  rfl

omit [NeZero q] in
/-- A uniform function on `Unit` is a uniform value. -/
theorem uniform_unit_bind {γ R : Type} [Fintype R] [Nonempty R] (g : (Unit → R) → PMF γ) :
    (PMF.uniformOfFintype (Unit → R)).bind g =
      (PMF.uniformOfFintype R).bind fun r => g fun _ => r := by
  rw [← bind_uniform_equiv (Equiv.funUnique Unit R).symm g]
  rfl

omit [NeZero q] in
/-- Independent coordinates on `Unit`: one draw. -/
theorem pi_unit {R : Type} [Finite R] (μ : PMF R) :
    PMF.pi (fun _ : Unit => μ) = μ.map fun r _ => r := by
  classical
  ext f
  rw [PMF.pi_apply, PMF.map_apply, tsum_eq_single (f ())]
  · rw [if_pos (by funext u; rfl)]; simp
  · intro r hr; rw [if_neg]; intro h; exact hr (by rw [h])

/-- A row from its entries. -/
def rowOf {ι R : Type} (f : ι → R) : Matrix (Fin 1) ι R := Matrix.of fun _ c => f c

omit [NeZero q] in
/-- A uniform row is a uniform function, negated. -/
theorem uniform_row_neg_bind {ι γ R : Type} [Fintype ι] [DecidableEq ι] [Fintype R] [Ring R]
    (g : Matrix (Fin 1) ι R → PMF γ) :
    (PMF.uniformOfFintype (Matrix (Fin 1) ι R)).bind g =
      (PMF.uniformOfFintype (ι → R)).bind fun f => g (-rowOf f) := by
  let e : (ι → R) ≃ Matrix (Fin 1) ι R :=
    { toFun := fun f => -rowOf f
      invFun := fun M c => -M 0 c
      left_inv := fun f => by funext c; simp [rowOf]
      right_inv := fun M => by ext i c; fin_cases i; simp [rowOf] }
  exact (bind_uniform_equiv e g).symm

/-- The instance of hybrid 5 from a ring-level pair: the public parts negated. -/
def split5 (v : (Idx5 Wd k → Negacyclic (ZMod q) N) × (Idx5 Wd k → Negacyclic (ZMod q) N)) :
    Pub Wd (Negacyclic (ZMod q) N) k × Pub Wd (Negacyclic (ZMod q) N) k :=
  ((-rowOf (fun c => v.1 (.inl c)), -rowOf (fun c => v.1 (.inr (.inl c))),
      -rowOf (fun c => v.1 (.inr (.inr (.inl c)))), -v.1 (.inr (.inr (.inr ())))),
    (rowOf (fun c => v.2 (.inl c)), rowOf (fun c => v.2 (.inr (.inl c))),
      rowOf (fun c => v.2 (.inr (.inr (.inl c)))), v.2 (.inr (.inr (.inr ())))))

omit [NeZero q] in
theorem uniform_unit_neg_bind {γ R : Type} [Fintype R] [Ring R] (g : (Unit → R) → PMF γ) :
    (PMF.uniformOfFintype (Unit → R)).bind g =
      (PMF.uniformOfFintype R).bind fun r => g fun _ => -r := by
  rw [uniform_unit_bind, ← bind_uniform_equiv (Equiv.neg R) (fun r => g fun _ => r)]
  rfl

/-- **Hybrid 5's real instances are the registry's** (normal form, secret law = error law). -/
theorem nfReal_eq (χc : PMF (ZMod q)) :
    nfReal (Wd := Wd) (k := k) (polyOf (N := N) χc) =
      (ringRealOn (Idx5 Wd k) χc χc).map split5 := by
  unfold nfReal ringRealOn rowLaw
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, uniform_sum_bind, uniform_unit_neg_bind, pi_sum, pi_unit,
    PMF.bind_bind, PMF.bind_map, uniform_row_neg_bind]
  refine congrArg (PMF.bind _) (funext fun σ => ?_)
  refine congrArg (PMF.bind _) (funext fun fd => ?_)
  refine congrArg (PMF.bind _) (funext fun fa => ?_)
  refine congrArg (PMF.bind _) (funext fun fz => ?_)
  refine congrArg (PMF.bind _) (funext fun pp => ?_)
  refine congrArg (PMF.bind _) (funext fun e₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun ea => ?_)
  refine congrArg (PMF.bind _) (funext fun ez => ?_)
  refine congrArg (PMF.bind _) (funext fun e' => ?_)
  simp only [Function.comp_apply, PMF.pure_map, split5]
  congr 1
  refine Prod.ext (by simp) ?_
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  all_goals first
    | (ext i c; fin_cases i; simp [rowOf, RingBTVW.scalar, Matrix.mul_apply, mul_comm])
    | (simp; ring)

/-- The split of hybrid 5 as a bijection. -/
def split5Equiv : ((Idx5 Wd k → Negacyclic (ZMod q) N) × (Idx5 Wd k → Negacyclic (ZMod q) N)) ≃
    (Pub Wd (Negacyclic (ZMod q) N) k × Pub Wd (Negacyclic (ZMod q) N) k) where
  toFun := split5
  invFun P := (Sum.elim (fun c => -P.1.1 0 c) (Sum.elim (fun c => -P.1.2.1 0 c)
      (Sum.elim (fun c => -P.1.2.2.1 0 c) fun _ => -P.1.2.2.2)),
    Sum.elim (fun c => P.2.1 0 c) (Sum.elim (fun c => P.2.2.1 0 c)
      (Sum.elim (fun c => P.2.2.2.1 0 c) fun _ => P.2.2.2.2)))
  left_inv v := by
    obtain ⟨A, b⟩ := v
    refine Prod.ext ?_ ?_ <;> funext i <;> rcases i with i | i | i | i <;> simp [split5, rowOf]
  right_inv P := by
    obtain ⟨⟨B₀, a, z, p⟩, ⟨c₀, ca, cz, cp⟩⟩ := P
    simp only [split5, Prod.mk.injEq]
    refine ⟨⟨?_, ?_, ?_, by simp⟩, ?_, ?_, ?_, rfl⟩ <;> (ext i c; fin_cases i; simp [rowOf])

/-- (Instance search does not find this product by itself.) -/
instance fintypePair5 :
    Fintype ((Idx5 Wd k → Negacyclic (ZMod q) N) × (Idx5 Wd k → Negacyclic (ZMod q) N)) :=
  instFintypeProd _ _

/-- **Hybrid 5's uniform instances are the registry's.** -/
theorem nfUnif_eq :
    nfUnif (Wd := Wd) (k := k) (R := Negacyclic (ZMod q) N) =
      (PMF.uniformOfFintype ((Idx5 Wd k → Negacyclic (ZMod q) N) ×
        (Idx5 Wd k → Negacyclic (ZMod q) N))).map split5 := by
  rw [show (split5 : _ → Pub Wd (Negacyclic (ZMod q) N) k × _) = split5Equiv from rfl,
    Cslib.Probability.PMF.uniformOfFintype_map_equiv]
  unfold nfUnif
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure]
  conv_rhs => rw [← PMF.bind_pure (PMF.uniformOfFintype (Pub Wd (Negacyclic (ZMod q) N) k ×
    Pub Wd (Negacyclic (ZMod q) N) k)), uniform_prod_bind]

end AdvancedEncryption.DualUse
