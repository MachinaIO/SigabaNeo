import SigabaNeo.Lib.Lattices.Research.Wall1.PrimitiveUnfolding

/-! Integral coordinates for an independent ordered pair. The two positive contents
measure primitivity in the ambient lattice and in the quotient by the first primitive vector. -/

noncomputable section
open Matrix SigabaNeo.Rogers
namespace SigabaNeo.Wall1.RankTwo

abbrev Prim (n : ℕ) := ContentFiber n 1
abbrev IV (n : ℕ) := Fin n → ℤ

def scaled {n : ℕ} (k : ℕ) (v : Prim n) : NonzeroIntVector n :=
  (scalePrimitive (Nat.succ_ne_zero k) v).val

theorem scaled_val {n : ℕ} (k : ℕ) (v : Prim n) :
    (scaled k v).val = ((k+1 : ℕ) : ℤ) • v.val.val := rfl

private theorem scaled_inj {n : ℕ} {k l : ℕ} {v w : Prim n}
    (h : (scaled k v).val = (scaled l w).val) : k = l ∧ v = w := by
  have eqn : k+1 = l+1 :=
    (scalePrimitive (Nat.succ_ne_zero k) v).property.symm.trans
    ((congrArg vectorContent (Subtype.ext h)).trans
      (scalePrimitive (Nat.succ_ne_zero l) w).property)
  obtain rfl : k = l := by omega
  exact ⟨rfl, (scalePrimitive_bijective (Nat.succ_ne_zero k)).injective
    (Subtype.ext (Subtype.ext h))⟩

private theorem exists_scaled {n : ℕ} (v : NonzeroIntVector n) :
    ∃ k u, scaled k u = v := by
  have h := vectorContent_ne_zero v
  let k := vectorContent v - 1
  have hk : vectorContent v = k+1 := by dsimp [k]; omega
  obtain ⟨u,hu⟩ := (scalePrimitive_bijective (Nat.succ_ne_zero k)).surjective ⟨v,hk⟩
  exact ⟨k,u,congrArg Subtype.val hu⟩

abbrev Core (m : ℕ) := Prim (m+1) × ℤ × Prim m
abbrev Indices (m : ℕ) := ℕ × ℕ × Core m

variable {m : ℕ} (hm : 1 ≤ m)

def completion (v : Prim (m+1)) : IV (m+1) ≃ₗ[ℤ] IV (m+1) :=
  (primitiveFrame (by omega : 2 ≤ m+1) v).toLin'

theorem completion_axis (v : Prim (m+1)) :
    completion hm v (Pi.single 0 1) = v.val.val := primitiveFrame_column (by omega) v

def first (a : ℕ) (p : Core m) := (scaled a p.1).val

def second (b : ℕ) (p : Core m) : IV (m+1) :=
  completion hm p.1 (Fin.cons p.2.1 (scaled b p.2.2).val)

private theorem first_coords (a : ℕ) (u : Prim (m+1)) :
    (completion hm u).symm (scaled a u).val = ((a+1 : ℕ) : ℤ) • Pi.single 0 1 := by
  apply (completion hm u).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, completion_axis, scaled_val]

theorem independent (a b : ℕ) (p : Core m) :
    LinearIndependent ℤ ![first a p, second hm b p] := by
  apply LinearIndependent.pair_iff.mpr
  intro s t h
  have eqn := congrArg (completion hm p.1).symm h
  simp only [first, second, map_add, map_smul, map_zero, LinearEquiv.symm_apply_apply,
    first_coords] at eqn
  have tail : t • (scaled b p.2.2).val = 0 := by
    funext j
    simpa [Pi.smul_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero j)] using congrFun eqn j.succ
  have ht : t = 0 := (smul_eq_zero.mp tail).resolve_right (scaled b p.2.2).property
  rw [ht, zero_smul, add_zero] at h
  exact ⟨(smul_eq_zero.mp h).resolve_right (scaled a p.1).property, ht⟩

def toPair (i : Indices m) : orderTwoIndependent (m+1) := by
  let z := ![first i.1 i.2.2, second hm i.2.1 i.2.2]
  have h : LinearIndependent ℤ z := independent hm ..
  exact ⟨fun j ↦ ⟨z j, h.ne_zero j⟩, h⟩

/-- Unique two-content and lift coordinates for every independent ordered pair. -/
theorem bijective_toPair : Function.Bijective (toPair hm) := by
  constructor
  · rintro ⟨a,b,u,t,v⟩ ⟨a',b',u',t',v'⟩ h
    have h₀ := congrArg (fun z : orderTwoIndependent (m+1) ↦ (z.val 0).val) h
    obtain ⟨rfl,rfl⟩ := scaled_inj (show (scaled a u).val = (scaled a' u').val from h₀)
    have h₁ := congrArg (fun z : orderTwoIndependent (m+1) ↦ (z.val 1).val) h
    have he := (completion hm u).injective h₁
    change (Fin.cons t (scaled b v).val : IV (m+1)) =
      (Fin.cons t' (scaled b' v').val : IV (m+1)) at he
    have ht : t = t' := congrFun he 0
    obtain ⟨rfl,rfl⟩ := scaled_inj (funext fun j ↦
      show (scaled b v).val j = (scaled b' v').val j from congrFun he j.succ)
    rw [ht]
  · intro z
    obtain ⟨a,u,hu⟩ := exists_scaled (z.val 0)
    let w := (completion hm u).symm (z.val 1).val
    let tail : IV m := fun j ↦ w j.succ
    have nonzero : tail ≠ 0 := by
      intro h
      have he : w = (w 0) • Pi.single 0 1 := by
        funext j
        refine Fin.cases (by simp) (fun i ↦ ?_) j
        simpa [Pi.single_eq_of_ne (Fin.succ_ne_zero i), tail] using congrFun h i
      have hy := congrArg (completion hm u) he
      change completion hm u ((completion hm u).symm _) = _ at hy
      rw [LinearEquiv.apply_symm_apply, map_smul, completion_axis] at hy
      have li : LinearIndependent ℤ ![(z.val 0).val,(z.val 1).val] := by
        have e : ![(z.val 0).val,(z.val 1).val] = (fun j ↦ (z.val j).val) := by
          funext j; fin_cases j <;> rfl
        exact e ▸ z.property
      have rel : (-(w 0)) • (z.val 0).val + ((a+1 : ℕ) : ℤ) • (z.val 1).val = 0 := by
        rw [← hu, scaled_val, hy, smul_smul, smul_smul, ← add_smul]
        simp [mul_comm]
      have := (LinearIndependent.pair_iff.mp li _ _ rel).2
      omega
    obtain ⟨b,v,hv⟩ := exists_scaled (⟨tail,nonzero⟩ : NonzeroIntVector m)
    refine ⟨⟨a,b,u,w 0,v⟩, Subtype.ext (funext fun j ↦ Subtype.ext ?_)⟩
    fin_cases j
    · exact congrArg Subtype.val hu
    · change completion hm u (Fin.cons (w 0) (scaled b v).val) = _
      apply (completion hm u).symm.injective
      rw [LinearEquiv.symm_apply_apply]
      exact funext fun j ↦ Fin.cases rfl (fun k ↦ congrFun (congrArg Subtype.val hv) k) j

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.bijective_toPair
