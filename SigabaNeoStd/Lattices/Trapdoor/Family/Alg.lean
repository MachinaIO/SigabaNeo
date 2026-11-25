import SigabaNeoStd.Lattices.Trapdoor.Family.Negl
import SigabaNeoStd.Lattices.Trapdoor.Family.PPT1
import SigabaNeoStd.Lattices.Trapdoor.Family.Helpers

/-!
# Trapdoor sampler: the algorithms on lists

The trapdoor is `(Ā, R)` as the list of entries of `Ā` (`encMat`) and the list of codes of `R`
(`codesL`), both row by row. On lists of numbers:

* `bL Q aL rL`: the entries of `B = [Ā | G − Ā R]` mod `Q`; `bL_eq`: it is `matVals (Bmat Ā R)`.
* `gsynL Q aL rL uL y`: `y + [R z; z]` with `z` the bits of `u − B y` mod `Q`; `gsynL_eq`: it is
  `gsyn Ā R u y` (the map of `Family/Law.lean`) as a list.
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib Cslib.Probability
open scoped Matrix

section
variable (κ : ℕ)

/-- A code `c < 4` of an entry of `R`. -/
def dec4N (x : ℕ) : ℤ := if x % 4 = 0 then -1 else if x % 4 = 3 then 1 else 0

theorem dec4N_val (c : Fin 4) : dec4N c.val = dec4 c := by
  fin_cases c <;> rfl

def aAtL (aL : List ℕ) (i a : ℕ) : ℤ := (aL.getD (i * mb κ + a) 0 : ℤ)
def rAtL (rL : List ℕ) (a c : ℕ) : ℤ := dec4N (rL.getD (c * mb κ + a) 0)
def gEntL (i c : ℕ) : ℤ := if c / (w κ + 1) = i then 2 ^ (c % (w κ + 1)) else 0

/-- Entry `(i, j)` of `B`, over `Z`. -/
def bEntZ (aL rL : List ℕ) (i j : ℕ) : ℤ :=
  if j < mb κ then aAtL κ aL i j
  else gEntL κ i (j - mb κ) -
    ((List.range (mb κ)).map fun a => aAtL κ aL i a * rAtL κ rL a (j - mb κ)).sum

def bEntL (Q : ℕ) (aL rL : List ℕ) (i j : ℕ) : ℕ := (bEntZ κ aL rL i j % (Q : ℤ)).toNat

/-- The entries of `B`. -/
def bL (Q : ℕ) (aL rL : List ℕ) : List ℕ :=
  (List.range (n κ)).flatMap fun i => (List.range (m κ)).map (bEntL κ Q aL rL i)

/-- Entry `i` of `u − B y` mod `Q`. -/
def synL (Q : ℕ) (aL rL uL : List ℕ) (y : List ℤ) (i : ℕ) : ℕ :=
  (((uL.getD i 0 : ℤ) - ((List.range (m κ)).map fun j => bEntZ κ aL rL i j * y.getD j 0).sum) %
    (Q : ℤ)).toNat

/-- Its bits. -/
def zL (Q : ℕ) (aL rL uL : List ℕ) (y : List ℤ) (c : ℕ) : ℤ :=
  if (synL κ Q aL rL uL y (c / (w κ + 1))).testBit (c % (w κ + 1)) then 1 else 0

/-- `[R z; z]`. -/
def xPreL (Q : ℕ) (aL rL uL : List ℕ) (y : List ℤ) (j : ℕ) : ℤ :=
  if j < mb κ then ((List.range (mb κ)).map fun c => rAtL κ rL j c * zL κ Q aL rL uL y c).sum
  else zL κ Q aL rL uL y (j - mb κ)

/-- `y + [R z; z]`. -/
def gsynL (Q : ℕ) (aL rL uL : List ℕ) (y : List ℤ) : List ℤ :=
  (List.range (m κ)).map fun j => y.getD j 0 + xPreL κ Q aL rL uL y j

/-! ### Encodings -/

/-- Entry `t` of a flattened `r × c` array: row `t / c`, column `t % c`. -/
theorem getD_ofFn_rc {r c : ℕ} (f : Fin r → Fin c → ℕ) (i : Fin r) (j : Fin c) :
    (List.ofFn fun t : Fin (r * c) => f t.divNat t.modNat).getD (i.val * c + j.val) 0 = f i j := by
  have hlt : i.val * c + j.val < r * c := by
    have := i.isLt; have := j.isLt; nlinarith
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [List.ofFnNthVal, dif_pos hlt, Option.getD_some]
  congr 1
  · ext; simp only [Fin.coe_divNat]; have := j.isLt
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt this, zero_add]
  · ext; simp only [Fin.coe_modNat]; have := j.isLt
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt this]

/-- The entries of `Ā`, row by row. -/
noncomputable def encMat (A : MatA κ) : List ℕ := List.ofFn fun t : Fin (n κ * mb κ) => (A t.divNat t.modNat).val

/-- The codes of `R`, at `c · mb + a` for `R a c`. -/
def codesL (Rc : RCodes κ) : List ℕ := List.ofFn fun t : Fin (mb κ * mb κ) => (Rc t.divNat t.modNat).val

/-- A syndrome. -/
noncomputable def synVals (u : Fin (n κ) → ZMod (q κ)) : List ℕ := (List.finRange (n κ)).map fun i => (u i).val

theorem getD_codesL (Rc : RCodes κ) (c a : Fin (mb κ)) :
    (codesL κ Rc).getD (c.val * mb κ + a.val) 0 = (Rc c a).val :=
  getD_ofFn_rc (fun c a => (Rc c a).val) c a

theorem getD_encMat (A : MatA κ) (i : Fin (n κ)) (a : Fin (mb κ)) :
    (encMat κ A).getD (i.val * mb κ + a.val) 0 = (A i a).val :=
  getD_ofFn_rc (fun i a => (A i a).val) i a

theorem getD_synVals (u : Fin (n κ) → ZMod (q κ)) (i : Fin (n κ)) :
    (synVals κ u).getD i.val 0 = (u i).val := by
  unfold synVals; simp [List.getD_eq_getElem?_getD]

theorem aAtL_encMat (A : MatA κ) (i : Fin (n κ)) (a : Fin (mb κ)) :
    aAtL κ (encMat κ A) i a = (A i a).val := by
  unfold aAtL; rw [getD_encMat]

theorem rAtL_codesL (Rc : RCodes κ) (a c : Fin (mb κ)) :
    rAtL κ (codesL κ Rc) a c = RofCodes κ Rc a c := by
  unfold rAtL RofCodes; rw [getD_codesL, dec4N_val]

theorem colEquiv_lt (j : Fin (m κ)) (h : j.val < mb κ) : colEquiv κ j = Sum.inl ⟨j.val, h⟩ := by
  unfold colEquiv
  rw [Equiv.trans_apply, Equiv.symm_apply_eq]
  ext; simp

theorem colEquiv_ge (j : Fin (m κ)) (h : ¬ j.val < mb κ) :
    colEquiv κ j = Sum.inr ⟨j.val - mb κ, by have := j.isLt; have := m_eq_mb κ; omega⟩ := by
  unfold colEquiv
  rw [Equiv.trans_apply, Equiv.symm_apply_eq]
  ext; simp; omega

theorem gRow_val (c : Fin (mb κ)) : (gRow κ c).val = c.val / (w κ + 1) := by
  unfold gRow; simp [finProdFinEquiv_symm_apply]

theorem gBit_val (c : Fin (mb κ)) : (gBit κ c).val = c.val % (w κ + 1) := by
  unfold gBit; simp [finProdFinEquiv_symm_apply]

theorem gadget_eq (i : Fin (n κ)) (c : Fin (mb κ)) :
    gadget κ i c = ((gEntL κ i c : ℤ) : ZMod (q κ)) := by
  unfold gadget gEntL
  rw [← gRow_val, ← gBit_val]
  by_cases h : gRow κ c = i
  · rw [if_pos h, if_pos (by rw [h])]; push_cast; rfl
  · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'))]; simp

theorem sum_fin_eq_list {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ j : Fin N, f j = ((List.range N).map f).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun j => f j), sum_range_eq_list]

theorem bEntZ_cast (A : MatA κ) (Rc : RCodes κ) (i : Fin (n κ)) (j : Fin (m κ)) :
    ((bEntZ κ (encMat κ A) (codesL κ Rc) i j : ℤ) : ZMod (q κ)) = Bmat κ A (RofCodes κ Rc) i j := by
  unfold Bmat bEntZ
  simp only [Matrix.submatrix_apply, id]
  by_cases h : j.val < mb κ
  · rw [if_pos h, colEquiv_lt κ j h, Matrix.fromCols_apply_inl,
      show aAtL κ (encMat κ A) i j = aAtL κ (encMat κ A) i (⟨j.val, h⟩ : Fin (mb κ)) from rfl,
      aAtL_encMat]
    simp
  · rw [if_neg h, colEquiv_ge κ j h, Matrix.fromCols_apply_inr, Matrix.sub_apply, Matrix.mul_apply,
      ← sum_fin_eq_list (mb κ) (fun a => aAtL κ (encMat κ A) i a *
      rAtL κ (codesL κ Rc) a (j.val - mb κ))]
    push_cast
    rw [gadget_eq]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [aAtL_encMat, show rAtL κ (codesL κ Rc) a (j.val - mb κ) =
      rAtL κ (codesL κ Rc) a (⟨j.val - mb κ, by have := j.isLt; have := m_eq_mb κ; omega⟩ :
        Fin (mb κ)) from rfl, rAtL_codesL]
    simp

theorem toNat_emod_eq_val (x : ℤ) : (x % (q κ : ℤ)).toNat = ((x : ZMod (q κ))).val := by
  have h := ZMod.val_intCast (n := q κ) x
  omega

theorem bEntL_eq (A : MatA κ) (Rc : RCodes κ) (i : Fin (n κ)) (j : Fin (m κ)) :
    bEntL κ (q κ) (encMat κ A) (codesL κ Rc) i j = (Bmat κ A (RofCodes κ Rc) i j).val := by
  unfold bEntL; rw [toNat_emod_eq_val, bEntZ_cast]

theorem bL_eq (A : MatA κ) (Rc : RCodes κ) :
    bL κ (q κ) (encMat κ A) (codesL κ Rc) = matVals (Bmat κ A (RofCodes κ Rc)) :=
  (matVals_eq_range _ _ fun i j => (bEntL_eq κ A Rc i j).symm).symm

theorem Bmul_cast (A : MatA κ) (Rc : RCodes κ) (y : List ℤ) (i : Fin (n κ)) :
    (Bmat κ A (RofCodes κ Rc) *ᵥ castV κ (vecOf κ y)) i =
      ((((List.range (m κ)).map fun j => bEntZ κ (encMat κ A) (codesL κ Rc) i j * y.getD j 0).sum : ℤ) :
        ZMod (q κ)) := by
  rw [← sum_fin_eq_list (m κ) (fun j => bEntZ κ (encMat κ A) (codesL κ Rc) i j * y.getD j 0)]
  simp only [Matrix.mulVec, dotProduct, castV, vecOf]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bEntZ_cast]; rfl

theorem synL_eq (A : MatA κ) (Rc : RCodes κ) (u : Fin (n κ) → ZMod (q κ)) (y : List ℤ) (i : Fin (n κ)) :
    synL κ (q κ) (encMat κ A) (codesL κ Rc) (synVals κ u) y i =
      ((u - Bmat κ A (RofCodes κ Rc) *ᵥ castV κ (vecOf κ y)) i).val := by
  unfold synL
  rw [toNat_emod_eq_val, getD_synVals, Pi.sub_apply, Bmul_cast]
  push_cast
  simp

theorem zL_eq (A : MatA κ) (Rc : RCodes κ) (u : Fin (n κ) → ZMod (q κ)) (y : List ℤ) (c : Fin (mb κ)) :
    zL κ (q κ) (encMat κ A) (codesL κ Rc) (synVals κ u) y c =
      gInv κ (u - Bmat κ A (RofCodes κ Rc) *ᵥ castV κ (vecOf κ y)) c := by
  unfold zL gInv
  rw [← gRow_val, ← gBit_val, synL_eq]

theorem xPreL_eq (A : MatA κ) (Rc : RCodes κ) (u : Fin (n κ) → ZMod (q κ)) (y : List ℤ) (j : Fin (m κ)) :
    xPreL κ (q κ) (encMat κ A) (codesL κ Rc) (synVals κ u) y j =
      xPre κ (RofCodes κ Rc) (u - Bmat κ A (RofCodes κ Rc) *ᵥ castV κ (vecOf κ y)) j := by
  unfold xPreL xPre
  simp only [Function.comp_apply]
  by_cases h : j.val < mb κ
  · rw [if_pos h, colEquiv_lt κ j h, Sum.elim_inl, Matrix.mulVec, dotProduct]
    rw [← sum_fin_eq_list (mb κ) (fun c => rAtL κ (codesL κ Rc) j c *
      zL κ (q κ) (encMat κ A) (codesL κ Rc) (synVals κ u) y c)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show rAtL κ (codesL κ Rc) j c = rAtL κ (codesL κ Rc) (⟨j.val, h⟩ : Fin (mb κ)) c from rfl,
      rAtL_codesL, zL_eq]
  · rw [if_neg h, colEquiv_ge κ j h, Sum.elim_inr]
    exact zL_eq κ A Rc u y ⟨j.val - mb κ, _⟩

theorem gsynL_eq (A : MatA κ) (Rc : RCodes κ) (u : Fin (n κ) → ZMod (q κ)) (y : List ℤ) :
    gsynL κ (q κ) (encMat κ A) (codesL κ Rc) (synVals κ u) y =
      List.ofFn (gsyn κ A (RofCodes κ Rc) u (vecOf κ y)) := by
  unfold gsynL gsyn
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, Pi.add_apply]
  rw [show xPreL κ (q κ) (encMat κ A) (codesL κ Rc) (synVals κ u) y j =
    xPreL κ (q κ) (encMat κ A) (codesL κ Rc) (synVals κ u) y (⟨j, by simpa using h1⟩ : Fin (m κ)) from rfl,
    xPreL_eq]
  rfl

end

end SigabaNeo.Lattices.Trapdoor.Family
