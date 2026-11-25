import PE.Impl.ExpLUT.Prog.DecCoefMath
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMFam

/-!
# Words representing the vectors and matrices of the evaluation (Dec, package F4)

At the dimensions `D`: a list of ring words **represents** a vector `v : Col K → R`
(`RepV`: `2K` words of `N K` bits, entry `c` at the position `cidx c = c.1 K + c.2` of the
enumeration of `Col K`), a matrix `M : Fin 2 × Col K → R` (`RepM`: `4K` words, row-major), a
family `Dig K → (Col K → R)` (`RepFV`, member `d` at `didx d`).

Bridges from the generic `RingVM` blocks to the scheme's operations:

* `ddotV_ginv`: the digit dot product with the column `col` of `M` is `(v G⁻¹(M))_col`;
* `mulAccV_eq`: the Mul sum of `exec_mulAccC` is `Σ_{ri} (F (ri.1, j, ri.2) G⁻¹(A))_{ri}`
  (`mulPK_eq`, `mulCT_eq` of `DecAlg`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT Matrix

variable {D : Dims}

/-- The position of a column in the enumeration of `Col K`. -/
def cidx (K : ℕ) (c : Col K) : ℕ := c.1.val * K + c.2.val

theorem cidx_lt {K : ℕ} (c : Col K) : cidx K c < 2 * K := by
  have := c.1.isLt; have := c.2.isLt; unfold cidx
  rcases (show c.1.val = 0 ∨ c.1.val = 1 by omega) with h | h <;> rw [h] <;> omega

/-- The position of a digit index `(r, j, i)` in the enumeration of `Dig K`. -/
def didx (K : ℕ) (d : Dig K) : ℕ := d.1.val * (2 * K * K) + cidx K d.2.1 * K + d.2.2.val

theorem didx_lt {K : ℕ} (d : Dig K) : didx K d < 2 * (2 * K) * K := by
  have h1 := d.1.isLt; have h2 := cidx_lt d.2.1; have h3 := d.2.2.isLt
  unfold didx
  have : cidx K d.2.1 * K + d.2.2.val < 2 * K * K := by nlinarith
  rcases (show d.1.val = 0 ∨ d.1.val = 1 by omega) with h | h <;> rw [h] <;> nlinarith

variable (D) in
/-- **A vector of `2K` words** representing `v`. -/
structure RepV (vs : List (List Bool)) (v : Col D.K → Rg D) : Prop where
  len : vs.length = 2 * D.K
  wid : ∀ x ∈ vs, x.length = D.N * D.K
  val : ∀ c, decRM D.N D.K (vs.getD (cidx D.K c) []) = v c

variable (D) in
/-- **A matrix of `4K` words** (row-major) representing `M`. -/
structure RepM (ms : List (List Bool)) (M : Matrix (Fin 2) (Col D.K) (Rg D)) : Prop where
  len : ms.length = 4 * D.K
  wid : ∀ x ∈ ms, x.length = D.N * D.K
  val : ∀ a c, decRM D.N D.K (ms.getD (2 * D.K * a.val + cidx D.K c) []) = M a c

variable (D) in
/-- **A family of vectors** indexed by the digit positions. -/
structure RepFV (fss : List (List (List Bool))) (F : Dig D.K → Col D.K → Rg D) : Prop where
  len : fss.length = 2 * (2 * D.K) * D.K
  ok : FamOK D.N D.K fss
  mem : ∀ d, RepV D (fss.getD (didx D.K d) []) (F d)

theorem getD_mem {α : Type*} {l : List α} {i : ℕ} {d : α} (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

/-- The rows of a represented matrix. -/
theorem RepM.of_rows {r₀ r₁ : List (List Bool)} {M : Matrix (Fin 2) (Col D.K) (Rg D)}
    (h₀ : RepV D r₀ (M 0)) (h₁ : RepV D r₁ (M 1)) : RepM D (r₀ ++ r₁) M where
  len := by rw [List.length_append, h₀.len, h₁.len]; ring
  wid x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · exact h₀.wid x hx
    · exact h₁.wid x hx
  val a c := by
    have hc := cidx_lt c
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
    · rw [List.getD_append _ _ _ _ (by rw [h₀.len]; simpa using hc)]
      simpa using h₀.val c
    · rw [List.getD_append_right _ _ _ _ (by rw [h₀.len]; simp)]
      rw [h₀.len, show 2 * D.K * (1 : Fin 2).val + cidx D.K c - 2 * D.K = cidx D.K c by simp]
      exact h₁.val c

theorem RepM.row₀ {ms : List (List Bool)} {M : Matrix (Fin 2) (Col D.K) (Rg D)} (h : RepM D ms M) :
    RepV D (ms.take (2 * D.K)) (M 0) where
  len := by rw [List.length_take, h.len]; omega
  wid x hx := h.wid x (List.mem_of_mem_take hx)
  val c := by
    have hc := cidx_lt c
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hc, ← List.getD_eq_getElem?_getD]
    simpa using h.val 0 c

theorem RepM.row₁ {ms : List (List Bool)} {M : Matrix (Fin 2) (Col D.K) (Rg D)} (h : RepM D ms M) :
    RepV D (ms.drop (2 * D.K)) (M 1) where
  len := by rw [List.length_drop, h.len]; omega
  wid x hx := h.wid x (List.mem_of_mem_drop hx)
  val c := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
    simpa using h.val 1 c

theorem RepM.eq_rows {ms : List (List Bool)} {M : Matrix (Fin 2) (Col D.K) (Rg D)} (_ : RepM D ms M) :
    ms = ms.take (2 * D.K) ++ ms.drop (2 * D.K) := (List.take_append_drop _ _).symm

/-! ### Bridges -/

theorem cidx_mk (r : Fin 2) (i : Fin D.K) : cidx D.K (r, i) = r.val * D.K + i.val := rfl

/-- **The digit dot product with a column is `(v G⁻¹(M))_col`.** -/
theorem ddotV_ginv {vs ms : List (List Bool)} {v : Col D.K → Rg D}
    {M : Matrix (Fin 2) (Col D.K) (Rg D)} (hv : RepV D vs v) (hm : RepM D ms M) (col : Col D.K) :
    ddotV (N := D.N) vs (ms.getD (cidx D.K col) []) (ms.getD (2 * D.K + cidx D.K col) []) =
      (v ᵥ* (setting D).ginv M) col := by
  have hg : (v ᵥ* (setting D).ginv M) col =
      ∑ c : Col D.K, v c * (setting D).D.d (M c.1 col) c.2 := by
    unfold Matrix.vecMul dotProduct
    refine Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨r, i⟩ := c
    fin_cases r <;> simp [Setting.ginv, Setting.gad, gswGadget, gadgetOf] <;> rfl
  rw [ddotV_eq, hg]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc := cidx_lt col
  have e0 : decRM D.N D.K (ms.getD (cidx D.K col) []) = M 0 col := by simpa using hm.val 0 col
  have e1 : decRM D.N D.K (ms.getD (2 * D.K + cidx D.K col) []) = M 1 col := by
    simpa using hm.val 1 col
  have w0 : (ms.getD (cidx D.K col) []).length = D.N * D.K :=
    hm.wid _ (getD_mem (by rw [hm.len]; omega))
  have w1 : (ms.getD (2 * D.K + cidx D.K col) []).length = D.N * D.K :=
    hm.wid _ (getD_mem (by rw [hm.len]; omega))
  rw [← cidx_mk, hv.val c]
  congr 1
  rcases (show c.1 = 0 ∨ c.1 = 1 by omega) with h | h
  · rw [if_pos h, opd_eq w0, e0, h]; rfl
  · rw [if_neg (by rw [h]; decide), opd_eq w1, e1, h]; rfl

/-- **The Mul sum is `Σ_{ri} (F (ri.1, j, ri.2) G⁻¹(A))_{ri}`.** -/
theorem mulAccV_eq {fss : List (List (List Bool))} {as : List (List Bool)}
    {F : Dig D.K → Col D.K → Rg D} {A : Matrix (Fin 2) (Col D.K) (Rg D)}
    (hF : RepFV D fss F) (hA : RepM D as A) (j : Col D.K) :
    mulAccV (N := D.N) fss as (cidx D.K j) =
      ∑ ri : Col D.K, (F (ri.1, j, ri.2) ᵥ* (setting D).ginv A) ri := by
  rw [mulAccV, iSum, iSum, Fintype.sum_prod_type, Fin.sum_univ_two, ← Fin.sum_univ_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := ddotV_ginv (hF.mem ((0 : Fin 2), j, i)) hA ((0 : Fin 2), i)
    simp only [didx, cidx, Fin.val_zero, zero_mul, zero_add] at this ⊢
    rw [← this]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := ddotV_ginv (hF.mem ((1 : Fin 2), j, i)) hA ((1 : Fin 2), i)
    simp only [didx, cidx, Fin.val_one, one_mul] at this ⊢
    rw [← this]
    congr 2 <;> ring_nf

end AdvancedEncryption.ExpLUT.Prog
