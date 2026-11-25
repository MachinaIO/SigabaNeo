import PE.Impl.ExpLUT.Prog.RedKeySimT
import PE.Impl.ExpLUT.Prog.RedKeyX
import PE.Impl.ExpLUT.Prog.RedKeySimSlab
/-!
# `KGsim` on the VM (module 6c at `D`): the rows of `R̂` from its slabs

`rowsWord R̂` (row-major over `LCol`, what module 5 reads from `rxRh`) is the row-major
transposition (`transOut`, computed by `transC`) of the `Ā` slabs (`inl w`, `w < m̄`), followed by
the transposition of the `η` slabs (`inr ρ`, `ρ` in `Enum (J × Col τ)` order): **`rowsWord_trans`**.
The slab rows are `slabRow`s of `RedKeySimSlab.slab`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib Matrix

/-- The row-major order of `n` slabs of `W` rows. -/
def transOut {α : Type} (rows : ℕ → ℕ → List α) (W n : ℕ) : List α :=
  (List.range W).flatMap fun i => (List.range n).flatMap fun k => rows k i

variable (D : Dims)

/-- The row `i` of the `Ā` slab `k` (words). -/
def rowsInl (Rh : LColS D → Fin 2 × Fin D.K → Rg D) (k i : ℕ) : List (Rg D) :=
  if h : i < 2 ^ D.b ∧ k < D.mb then vecL (Rh (.inl (⟨i, h.1⟩, ⟨k, h.2⟩))) else vecL 0

/-- The row `i` of the `η` slab `k` (words; `k` in `Enum (J × Col τ)` order). -/
def rowsInr (Rh : LColS D → Fin 2 × Fin D.K → Rg D) (k i : ℕ) : List (Rg D) :=
  if h : i < 2 ^ D.b ∧ k < (Enum.list (α := Jh D × (Fin 2 × Fin D.K))).length then
    vecL (Rh (.inr (⟨i, h.1⟩, (Enum.list (α := Jh D × (Fin 2 × Fin D.K)))[k]))) else vecL 0

theorem length_rowsInl (Rh : LColS D → Fin 2 × Fin D.K → Rg D) (k i : ℕ) :
    (rowsInl D Rh k i).length = 2 * D.K := by
  unfold rowsInl; split_ifs <;> exact length_vecL _

theorem length_rowsInr (Rh : LColS D → Fin 2 × Fin D.K → Rg D) (k i : ℕ) :
    (rowsInr D Rh k i).length = 2 * D.K := by
  unfold rowsInr; split_ifs <;> exact length_vecL _

/-- **The rows of `R̂` are the transposed slabs.** -/
theorem rowsWord_trans (Rh : LColS D → Fin 2 × Fin D.K → Rg D) :
    rowsWord (N := D.N) (K := D.K) (α := LColS D) (β := Fin 2 × Fin D.K) Rh =
      transOut (rowsInl D Rh) (2 ^ D.b) D.mb ++
        transOut (rowsInr D Rh) (2 ^ D.b) (Enum.list (α := Jh D × (Fin 2 × Fin D.K))).length := by
  unfold rowsWord
  rw [← List.flatMap]
  show ((Enum.list (α := Fin (2 ^ D.b) × Wb D)).map Sum.inl ++
    (Enum.list (α := Fin (2 ^ D.b) × (Jh D × (Fin 2 × Fin D.K)))).map Sum.inr).flatMap _ = _
  have hW : (Enum.list (α := Fin (2 ^ D.b))).length = 2 ^ D.b := by simp [Enum.list]
  have hm : (Enum.list (α := Fin D.mb)).length = D.mb := by simp [Enum.list]
  refine List.flatMap_append.trans (congrArg₂ (· ++ ·) ?_ ?_)
  · refine (List.flatMap_map ..).trans ?_
    show ((Enum.list (α := Fin (2 ^ D.b))).product (Enum.list (α := Fin D.mb))).flatMap _ = _
    rw [product_flatMap, flatMap_range_getElem _ _ (fun i => (List.range D.mb).flatMap
      fun k => rowsInl D Rh k i) (fun i hi => ?_), hW]
    · rfl
    · symm
      rw [flatMap_range_getElem _ _ (fun k => rowsInl D Rh k i) (fun k hk => ?_), hm]
      have hi' : i < 2 ^ D.b := by rwa [hW] at hi
      have hk' : k < D.mb := by rwa [hm] at hk
      simp only [rowsInl, hi', hk', and_self, ↓reduceDIte]
      simp [Enum.list]
      rfl
  · refine (List.flatMap_map ..).trans ?_
    show ((Enum.list (α := Fin (2 ^ D.b))).product
      (Enum.list (α := Jh D × (Fin 2 × Fin D.K)))).flatMap _ = _
    rw [product_flatMap, flatMap_range_getElem _ _ (fun i =>
      (List.range (Enum.list (α := Jh D × (Fin 2 × Fin D.K))).length).flatMap
        fun k => rowsInr D Rh k i) (fun i hi => ?_), hW]
    · rfl
    · symm
      rw [flatMap_range_getElem _ _ (fun k => rowsInr D Rh k i) (fun k hk => ?_)]
      have hi' : i < 2 ^ D.b := by rwa [hW] at hi
      simp only [rowsInr, hi', hk, and_self, ↓reduceDIte]
      simp [Enum.list]
      rfl

/-- The `Ā` slab rows are rows of the slabs (`RedKeySimSlab.slab`). -/
theorem rowsInl_slab (Rh : SimMat (Wb D) (Jh D) (setting D)) {k i : ℕ} (hi : i < 2 ^ D.b)
    (hk : k < D.mb) :
    rowsInl D (fun ℓ c => Rh ℓ c) k i = vecL (slab Rh (.inl ⟨k, hk⟩) ⟨i, hi⟩) := by
  simp only [rowsInl, hi, hk, and_self, ↓reduceDIte]
  rfl

/-- The `η` slab rows are rows of the slabs. -/
theorem rowsInr_slab (Rh : SimMat (Wb D) (Jh D) (setting D)) {k i : ℕ} (hi : i < 2 ^ D.b)
    (hk : k < (Enum.list (α := Jh D × (Fin 2 × Fin D.K))).length) :
    rowsInr D (fun ℓ c => Rh ℓ c) k i =
      vecL (slab Rh (.inr (Enum.list (α := Jh D × (Fin 2 × Fin D.K)))[k]) ⟨i, hi⟩) := by
  simp only [rowsInr, hi, hk, and_self, ↓reduceDIte]
  rfl

end AdvancedEncryption.ExpLUT.Prog
