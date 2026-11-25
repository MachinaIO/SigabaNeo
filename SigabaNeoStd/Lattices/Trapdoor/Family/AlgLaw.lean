import SigabaNeoStd.Lattices.Trapdoor.Family.Alg
import SigabaNeoStd.Lattices.Trapdoor.Family.Helpers
import CslibFrontier.Crypto.Game.CloseTo.UniformNat

/-!
# Trapdoor sampler: the programs and their laws

* `genAlg (κ, Q)`: `Ā` entry by entry with `sampleModNat`, the codes of `R` with two fair bits
  each, and the public `B`. At `Q = q κ` its law is `(DA × uniform codes)` pushed through
  `(Ā, R) ↦ (B, Ā, R)` (`eval_genAlg`), and `DA` is within `n mb q / 2^{wdA}` of uniform
  (`closeTo_DA`).
* `preAlg ((κ, Q), (Ā, R), P)`: for each column `u` of `P`, `m` draws of `samp1` sent through
  `gsynL` (`colAlg`). Its law is `colsReal` (`eval_preAlg`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib Cslib.Probability
open scoped ENNReal Matrix Cslib.Probability.PMF

/-! ### Generic laws -/

theorem map_congr_support {α β : Type} (p : PMF α) {f g : α → β} (h : ∀ a ∈ p.support, f a = g a) :
    p.map f = p.map g := by
  ext b
  simp only [PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr ha]; simp

theorem bind_congr_support {α β : Type} (p : PMF α) {f g : α → PMF β} (h : ∀ a ∈ p.support, f a = g a) :
    p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr ha]; simp

theorem support_sampleList {α : Type} (d : PMF α) :
    ∀ (k : ℕ) (l : List α), l ∈ (sampleList d k).support → l.length = k ∧ ∀ x ∈ l, x ∈ d.support
  | 0, l, hl => by
    simp only [sampleList, PMF.support_pure, Set.mem_singleton_iff] at hl
    subst hl; simp
  | k + 1, l, hl => by
    simp only [sampleList, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hl
    obtain ⟨a, ha, l', hl', rfl⟩ := hl
    obtain ⟨h1, h2⟩ := support_sampleList d k l' hl'
    refine ⟨by simp [h1], fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact h2 x hx

theorem eval_mapM {α β : Type} (f : α → ProbComp β) :
    ∀ l : List α, (ProbComp.eval (l.mapM f)).map some =
      sampleOptList (l.map fun a => some (ProbComp.eval (f a)))
  | [] => by
    show (ProbComp.eval (pure [] : ProbComp (List β))).map some = PMF.pure (some [])
    rw [ProbComp.eval_pure, PMF.pure_map]
  | a :: l => by
    rw [List.mapM_cons, ProbComp.eval_bind, PMF.map_bind]
    show _ = (ProbComp.eval (f a)).bind fun b =>
      (sampleOptList (l.map fun a => some (ProbComp.eval (f a)))).map (Option.map (b :: ·))
    congr 1; funext b
    have h : ProbComp.eval (do let bs ← l.mapM f; pure (b :: bs)) =
        (ProbComp.eval (l.mapM f)).map (b :: ·) := by
      rw [ProbComp.eval_bind]; simp only [ProbComp.eval_pure]; rfl
    rw [h, ← eval_mapM f l, PMF.map_comp, PMF.map_comp]
    rfl

theorem sampleOptList_map {α β : Type} (f : α → β) : ∀ ds : List (PMF α),
    sampleOptList (ds.map fun d => some (d.map f)) =
      (sampleOptList (ds.map some)).map (Option.map (List.map f))
  | [] => by
    show PMF.pure (some []) = (PMF.pure (some [])).map _
    rw [PMF.pure_map]; rfl
  | d :: ds => by
    show (d.map f).bind (fun a => (sampleOptList (ds.map fun d => some (d.map f))).map
        (Option.map (a :: ·))) =
      (d.bind fun a => (sampleOptList (ds.map some)).map (Option.map (a :: ·))).map
        (Option.map (List.map f))
    rw [PMF.bind_map, PMF.map_bind, sampleOptList_map f ds]
    congr 1; funext a
    simp only [Function.comp_apply, PMF.map_comp]
    congr 1; funext o; cases o <;> rfl

/-! ### The programs -/

/-- Bits per entry of `Ā`. -/
def wdA (κ : ℕ) : ℕ := w κ + 1 + κ

/-- `GenTrap`: the public `B` and the trapdoor `(Ā, R)`. -/
noncomputable def genAlg (pub : ℕ × ℕ) : ProbComp (List ℕ × List ℕ × List ℕ) := do
  let aL ← OracleComp.replicate (n pub.1 * mb pub.1) (ProbComp.sampleModNat (wdA pub.1) pub.2)
  let rL ← OracleComp.replicate (mb pub.1 * mb pub.1) (ProbComp.sampleBinaryNat 2)
  pure (bL pub.1 pub.2 aL rL, aL, rL)

/-- One column: `((κ, Q), (Ā, R), u)`. -/
noncomputable def colAlg (c : (ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) : ProbComp (List ℤ) :=
  gsynL c.1.1 c.1.2 c.2.1.1 c.2.1.2 c.2.2 <$> OracleComp.replicate (m c.1.1) (samp1 c.1.1)

/-- The inputs of the columns of `P`. -/
def colInputs (inp : (ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) :
    List ((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) :=
  (List.range (k inp.1.1)).map fun j =>
    (inp.1, inp.2.1, (List.range (n inp.1.1)).map fun i => inp.2.2.getD (i * k inp.1.1 + j) 0)

/-- `SamplePre`: a preimage of each column of `P`, with the trapdoor. -/
noncomputable def preAlg (inp : (ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) : ProbComp (List (List ℤ)) :=
  (colInputs inp).mapM colAlg

section
variable (κ : ℕ)

/-! ### The column law -/

theorem eval_colAlg (A : MatA κ) (Rc : RCodes κ) (u : Fin (n κ) → ZMod (q κ)) :
    ProbComp.eval (colAlg ((κ, q κ), (encMat κ A, codesL κ Rc), synVals κ u)) =
      (colLawOf κ (μV κ) A (RofCodes κ Rc) u).map List.ofFn := by
  unfold colAlg colLawOf μV sampV
  rw [ProbComp.eval_map, PMF.map_comp, PMF.map_comp]
  congr 1; funext y
  exact gsynL_eq κ A Rc u y

/-- `K` as its list of columns. -/
def colsList (K : Matrix (Fin (m κ)) (Fin (k κ)) ℤ) : List (List ℤ) :=
  List.ofFn fun j => List.ofFn fun r => K r j

theorem colInputs_eq (A : MatA κ) (Rc : RCodes κ) (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    colInputs ((κ, q κ), (encMat κ A, codesL κ Rc), matVals P) =
      (List.finRange (k κ)).map fun j => ((κ, q κ), (encMat κ A, codesL κ Rc), synVals κ fun i => P i j) := by
  unfold colInputs
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_finRange, Prod.mk.injEq, true_and]
  unfold synVals
  refine List.ext_getElem (by simp) fun i g1 g2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
  have hi : i < n κ := by simpa using g1
  have hj : j < k κ := by simpa using h1
  exact getD_matVals P ⟨i, hi⟩ ⟨j, hj⟩

theorem eval_preAlg (A : MatA κ) (Rc : RCodes κ) (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    (ProbComp.eval (preAlg ((κ, q κ), (encMat κ A, codesL κ Rc), matVals P))).map some =
      (colsReal κ A (RofCodes κ Rc) P).map (Option.map (colsList κ)) := by
  unfold preAlg
  rw [eval_mapM, colInputs_eq, List.map_map]
  simp only [Function.comp_def, eval_colAlg]
  rw [show ((List.finRange (k κ)).map fun j =>
      some ((colLawOf κ (μV κ) A (RofCodes κ Rc) fun i => P i j).map List.ofFn)) =
      ((List.finRange (k κ)).map fun j => colLawOf κ (μV κ) A (RofCodes κ Rc) fun i => P i j).map
        (fun d => some (d.map List.ofFn)) by rw [List.map_map]; rfl,
    sampleOptList_map, List.map_map]
  unfold colsReal colsOf
  rw [PMF.map_comp]
  refine map_congr_support _ fun o ho => ?_
  have hs := support_sampleOptList _ o ho
  cases o with
  | none => rfl
  | some vs =>
    show some (vs.map List.ofFn) = some (colsList κ fun r j => (vs.getD j.val 0) r)
    congr 1
    have hlen : vs.length = k κ := by
      have := List.Forall₂.length_eq hs
      simpa using this
    unfold colsList
    refine List.ext_getElem (by simp [hlen]) fun j h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_ofFn]
    congr 1
    rw [List.getD_eq_getElem _ _ (by simpa [hlen] using h1)]

/-! ### The law of `GenTrap` -/

noncomputable def decA (aL : List ℕ) : MatA κ :=
  fun i a => ((aL.getD (i.val * mb κ + a.val) 0 : ℕ) : ZMod (q κ))

def decR (rL : List ℕ) : RCodes κ :=
  fun c a => ⟨rL.getD (c.val * mb κ + a.val) 0 % 4, Nat.mod_lt _ (by norm_num)⟩

theorem encMat_decA (aL : List ℕ) (hl : aL.length = n κ * mb κ) (hq : ∀ x ∈ aL, x < q κ) :
    encMat κ (decA κ aL) = aL := by
  refine List.ext_getElem (by simp [encMat, hl]) fun t h1 h2 => ?_
  simp only [encMat, List.getElem_ofFn, decA, Fin.coe_divNat, Fin.coe_modNat]
  rw [ZMod.val_natCast, Nat.div_add_mod', List.getD_eq_getElem _ _ h2,
    Nat.mod_eq_of_lt (hq _ (List.getElem_mem h2))]

theorem codesL_decR (rL : List ℕ) (hl : rL.length = mb κ * mb κ) (h4 : ∀ x ∈ rL, x < 4) :
    codesL κ (decR κ rL) = rL := by
  refine List.ext_getElem (by simp [codesL, hl]) fun t h1 h2 => ?_
  simp only [codesL, List.getElem_ofFn, decR, Fin.coe_divNat, Fin.coe_modNat]
  rw [Nat.div_add_mod', List.getD_eq_getElem _ _ h2,
    Nat.mod_eq_of_lt (h4 _ (List.getElem_mem h2))]

/-- Reindexing a flat array as an `r × c` array. -/
def flatEquiv (r c : ℕ) (β : Type) : (Fin (r * c) → β) ≃ (Fin r → Fin c → β) where
  toFun v i j := v (finProdFinEquiv (i, j))
  invFun M t := M (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  left_inv v := by funext t; simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv M := by funext i j; simp

theorem flat_getD {β : Type} (r c : ℕ) (f : ℕ → β) (i : Fin r) (j : Fin c) :
    f (finProdFinEquiv (i, j)).val = f (i.val * c + j.val) := by
  rw [finProdFinEquiv_apply_val]; congr 1; ring

theorem decR_uniform :
    (sampleList (ProbComp.eval (ProbComp.sampleBinaryNat 2)) (mb κ * mb κ)).map (decR κ) =
      PMF.uniformOfFintype (RCodes κ) := by
  classical
  set f : ℕ → Fin 4 := fun x => ⟨x % 4, Nat.mod_lt _ (by norm_num)⟩
  have hdec : decR κ = flatEquiv (mb κ) (mb κ) (Fin 4) ∘
      fun l (t : Fin (mb κ * mb κ)) => f (l.getD t default) := by
    funext l c a
    simp only [decR, flatEquiv, Equiv.coe_fn_mk, Function.comp_apply, f]
    rw [flat_getD (mb κ) (mb κ) (fun t => l.getD t default)]
    rfl
  have h4 : (ProbComp.eval (ProbComp.sampleBinaryNat 2)).map f = PMF.uniformOfFintype (Fin 4) := by
    rw [ProbComp.eval_sampleBinaryNat, PMF.map_comp]
    have : (f ∘ Fin.val : Fin (2 ^ 2) → Fin 4) = finCongr (by norm_num) := by
      funext x; ext; simp [f, Nat.mod_eq_of_lt (x.isLt.trans_le (show 2 ^ 2 ≤ 4 by norm_num))]
    rw [this, PMF.uniformOfFintype_map_equiv]
  rw [hdec, ← PMF.map_comp, sampleList_pi, h4, PMF.pi_uniformOfFintype,
    PMF.uniformOfFintype_map_equiv]

/-- The law of `Ā`. -/
noncomputable def dA : PMF ℕ := ProbComp.eval (ProbComp.sampleModNat (wdA κ) (q κ))

noncomputable def DA : PMF (MatA κ) := (sampleList (dA κ) (n κ * mb κ)).map (decA κ)

theorem dA_lt (x : ℕ) (hx : x ∈ (dA κ).support) : x < q κ := by
  unfold dA at hx
  rw [ProbComp.eval_sampleModNat, PMF.mem_support_map_iff] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))

theorem sampleBinaryNat_lt (x : ℕ) (hx : x ∈ (ProbComp.eval (ProbComp.sampleBinaryNat 2)).support) :
    x < 4 := by
  have := (ProbComp.mem_support_sampleBinaryNat_iff 2 x).mp hx
  simpa using this

/-- The law of the trapdoor. -/
noncomputable def DT : PMF (MatA κ × RCodes κ) :=
  (DA κ).bind fun A => (PMF.uniformOfFintype (RCodes κ)).map (A, ·)

theorem eval_genAlg :
    ProbComp.eval (genAlg (κ, q κ)) = (DT κ).map fun p =>
      (matVals (Bmat κ p.1 (RofCodes κ p.2)), encMat κ p.1, codesL κ p.2) := by
  unfold DT DA genAlg
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, eval_replicate_eq]
  rw [PMF.map_bind, PMF.bind_map]
  refine bind_congr_support _ fun aL haL => ?_
  obtain ⟨hl, hq⟩ := support_sampleList _ _ aL haL
  simp only [Function.comp_apply]
  rw [PMF.map_comp, ← decR_uniform κ, PMF.map_comp]
  show _ = PMF.map _ _
  rw [show (fun rL => PMF.pure (bL κ (q κ) aL rL, aL, rL)) =
    PMF.pure ∘ fun rL => (bL κ (q κ) aL rL, aL, rL) from rfl, ← PMF.map]
  refine map_congr_support _ fun rL hrL => ?_
  obtain ⟨hl', h4⟩ := support_sampleList _ _ rL hrL
  simp only [Function.comp_apply]
  rw [← bL_eq, encMat_decA κ aL hl fun x hx => dA_lt κ x (hq x hx),
    codesL_decR κ rL hl' fun x hx => sampleBinaryNat_lt x (h4 x hx)]

/-! ### `Ā` is close to uniform -/

/-- `n mb q / 2^{wdA}`. -/
noncomputable def εA : ℝ := (n κ * mb κ : ℕ) * ((q κ : ℝ) / 2 ^ wdA κ)

theorem closeTo_DA : CloseTo (DA κ) (PMF.uniformOfFintype (MatA κ)) (ENNReal.ofReal (εA κ)) := by
  classical
  have hdec : decA κ = flatEquiv (n κ) (mb κ) (ZMod (q κ)) ∘
      fun l (t : Fin (n κ * mb κ)) => ((l.getD t default : ℕ) : ZMod (q κ)) := by
    funext l i a
    simp only [decA, flatEquiv, Equiv.coe_fn_mk, Function.comp_apply]
    rw [flat_getD (n κ) (mb κ) (fun t => ((l.getD t default : ℕ) : ZMod (q κ)))]
    rfl
  have e : DA κ = ((sampleList (dA κ) (n κ * mb κ)).map
      fun l (t : Fin (n κ * mb κ)) => ((l.getD t default : ℕ) : ZMod (q κ))).map
        (flatEquiv (n κ) (mb κ) (ZMod (q κ))) := by
    unfold DA; rw [PMF.map_comp, hdec]; rfl
  have hu : PMF.uniformOfFintype (MatA κ) =
      (PMF.uniformOfFintype (Fin (n κ * mb κ) → ZMod (q κ))).map (flatEquiv (n κ) (mb κ) (ZMod (q κ))) :=
    (PMF.uniformOfFintype_map_equiv _).symm
  rw [e, hu, sampleList_pi, ← PMF.pi_uniformOfFintype]
  refine CloseTo.map ?_ _
  have hd := PMF.dist_pi_le_sum (fun _ : Fin (n κ * mb κ) => (dA κ).map (Nat.cast : ℕ → ZMod (q κ)))
    (fun _ => PMF.uniformOfFintype (ZMod (q κ)))
  have h1 : ∀ _i : Fin (n κ * mb κ), dist ((dA κ).map (Nat.cast : ℕ → ZMod (q κ)))
      (PMF.uniformOfFintype (ZMod (q κ))) ≤ (q κ : ℝ) / 2 ^ wdA κ := fun _ =>
    ProbComp.dist_map_natCast_eval_sampleModNat_le _ _
  have h2 : dist (PMF.pi fun _ : Fin (n κ * mb κ) => (dA κ).map (Nat.cast : ℕ → ZMod (q κ)))
      (PMF.pi fun _ => PMF.uniformOfFintype (ZMod (q κ))) ≤ εA κ := by
    refine hd.trans ?_
    calc ∑ _i : Fin (n κ * mb κ), dist ((dA κ).map (Nat.cast : ℕ → ZMod (q κ)))
          (PMF.uniformOfFintype (ZMod (q κ))) ≤ ∑ _i : Fin (n κ * mb κ), (q κ : ℝ) / 2 ^ wdA κ :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = εA κ := by simp [εA]
  exact closeTo_of_dist_le_ofReal h2

theorem closeTo_DT : CloseTo (DT κ) (PMF.uniformOfFintype (MatA κ × RCodes κ)) (ENNReal.ofReal (εA κ)) := by
  rw [← PMF.uniformOfFintype_prod]
  exact (closeTo_DA κ).bind_left _

end

end SigabaNeo.Lattices.Trapdoor.Family
