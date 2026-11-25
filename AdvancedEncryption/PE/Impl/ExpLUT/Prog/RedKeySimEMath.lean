import PE.Impl.ExpLUT.Prog.RedKeySimES
import PE.Impl.ExpLUT.Prog.RedKeySimSlab
import PE.Impl.ExpLUT.Prog.KeyEval

/-!
# `KGsim` on the VM (module 6b, part 5): slabs as lists of rows (bridges at `D`)

At the dimensions `D`, a slab `s : Slab (setting D)` (`W` rows of `2K` ring elements) is the list
of its rows `seSlabL s` (`List.finRange W` order), the order of the generic VM evaluator
(`RedKeySimE*`). The slab operations of `RedKeySimSlab` become the list operations of the VM:

* `σ_{g^m}` is `σ_g` iterated `m` times (**`seSigIdx`**);
* rows `· G⁻¹(C)` is `map (seGRow · C)` (**`seSlabL_ginv`**);
* `slabPerm (2^t)` is `σ_g^{2^t}` on every row, then the rows rotated right by `2^t`
  (`List.rotate (W − 2^t)`, **`seSlabL_perm`**);
* adding a vector to one row is `seAddAt` (**`seSlabL_addRow`**);
* sums of slabs are `zipWith seRowAdd` (**`seSlabL_add`**).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib Matrix

variable (D : Dims)

/-- **`σ_{g^m}` is `σ_g` iterated `m` times.** -/
theorem seSigIdx (m : ℕ) (a : Rg D) :
    (setting D).E.σ ((setting D).idx m) a = (aut D.N (gD D))^[m] a := by
  rw [aut_iterate D (odd_gD D)]
  show autσ D.N (gD D ^ m) a = _
  rw [autσ_of_odd ((odd_gD D).pow)]

/-- **The rows of a slab**, in the order of `Fin W`. -/
noncomputable def seSlabL (s : Slab (setting D)) : List (Fin 2 × Fin D.K → Rg D) :=
  (List.finRange (setting D).E.W).map fun i c => s i c

theorem length_seSlabL (s : Slab (setting D)) : (seSlabL D s).length = (setting D).E.W := by
  simp [seSlabL]

theorem getElem_seSlabL (s : Slab (setting D)) (i : ℕ) (h : i < (seSlabL D s).length) :
    (seSlabL D s)[i] = fun c => s ⟨i, by rw [length_seSlabL] at h; exact h⟩ c := by
  simp [seSlabL]

/-- `v · G⁻¹(C)` for a row, at `D`, is `seGRow`. -/
theorem vecMul_ginv_eq (v : Col (setting D).τ → Rg D) (C : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    (fun c => (v ᵥ* (setting D).ginv C) c) = seGRow (K := D.K) (fun c => v c) (fun a c => C a c) := by
  have h := mul_ginv_eq D (Matrix.of fun _ => v) C
  funext col
  exact congrFun (congrFun h 0) col

/-- **Rows `· G⁻¹(C)`.** -/
theorem seSlabL_ginv (s : Slab (setting D)) (C : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    seSlabL D (fun i => s i ᵥ* (setting D).ginv C) =
      (seSlabL D s).map fun v => seGRow v (fun a c => C a c) := by
  simp only [seSlabL, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  exact vecMul_ginv_eq D (s i) C

/-- **Sums of slabs.** -/
theorem seSlabL_add (s s' : Slab (setting D)) :
    seSlabL D (s + s') = List.zipWith seRowAdd (seSlabL D s) (seSlabL D s') := by
  simp only [seSlabL, List.zipWith_map, List.zipWith_self]
  rfl

/-- **Adding `v` to the row `i₀`.** -/
theorem seSlabL_addRow (s : Slab (setting D)) (i₀ : Fin (setting D).E.W)
    (v : Fin 2 × Fin D.K → Rg D) :
    seSlabL D (fun i c => s i c + if i = i₀ then v c else 0) = seAddAt (seSlabL D s) i₀.val v := by
  unfold seAddAt
  apply List.ext_getElem (by simp [seSlabL, List.length_modify])
  intro i h1 h2
  rw [List.getElem_modify, getElem_seSlabL]
  have hi : i < (setting D).E.W := by rw [length_seSlabL] at h1; exact h1
  by_cases h3 : (i₀ : ℕ) = i
  · rw [if_pos h3]
    have e : (⟨i, hi⟩ : Fin (setting D).E.W) = i₀ := Fin.ext h3.symm
    funext c
    simp only [seRowAdd, getElem_seSlabL, e, ↓reduceIte]
  · rw [if_neg h3]
    have e : (⟨i, hi⟩ : Fin (setting D).E.W) ≠ i₀ := fun e => h3 (by rw [← e])
    funext c
    simp only [getElem_seSlabL, e, ↓reduceIte, add_zero]

theorem seW_eq : (setting D).E.W = 2 ^ D.b := rfl

/-- The inverse rotation by `p < W`, on indices. -/
theorem rotEquiv_symm_val {p : ℕ} (hp : p < (setting D).E.W) (i : Fin (setting D).E.W) :
    ((rotEquiv (S := setting D) p).symm i).val = (i.val + ((setting D).E.W - p)) % (setting D).E.W := by
  have hW : 0 < (setting D).E.W := (setting D).E.W_pos
  have key : rotEquiv (S := setting D) p
      ⟨(i.val + ((setting D).E.W - p)) % (setting D).E.W, Nat.mod_lt _ hW⟩ = i := by
    rw [rotEquiv_apply]
    apply Fin.ext
    simp only [Setting.rot, Fin.val_add, Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt hp, Nat.mod_add_mod, Nat.add_assoc,
      Nat.sub_add_cancel hp.le, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  have e : (rotEquiv (S := setting D) p).symm i =
      ⟨(i.val + ((setting D).E.W - p)) % (setting D).E.W, Nat.mod_lt _ hW⟩ := by
    rw [Equiv.symm_apply_eq]; exact key.symm
  rw [e]

/-- **`slabPerm (2^t)`**: `σ_g^{2^t}` on every row, the rows rotated right by `2^t`. -/
theorem seSlabL_perm {t : ℕ} (ht : t < D.b) (s : Slab (setting D)) :
    seSlabL D (slabPerm (2 ^ t) s) = ((seSlabL D s).map (seRowAut (gD D) (2 ^ t))).rotate
      ((setting D).E.W - 2 ^ t) := by
  have hp : 2 ^ t < (setting D).E.W := by rw [seW_eq]; exact Nat.pow_lt_pow_right (by norm_num) ht
  apply List.ext_getElem (by simp [seSlabL])
  intro i h1 h2
  have hi : i < (setting D).E.W := by rw [length_seSlabL] at h1; exact h1
  rw [List.getElem_rotate, List.getElem_map, getElem_seSlabL, getElem_seSlabL]
  funext c
  simp only [slabPerm, seRowAut, List.length_map, length_seSlabL]
  rw [seSigIdx]
  congr 2
  apply Fin.ext
  rw [rotEquiv_symm_val D hp]

/-! ### `Mul` on a slab with fresh data on one row -/

/-- The digit term of `slabMul` for digit slabs supported on the row `i₀`. -/
theorem slabMul_digit_row (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (i₀ i : Fin (setting D).E.W)
    (ρ : Dig (setting D).τ → Col (setting D).τ → Rg D) (j : Col (setting D).τ) :
    (∑ ri : Col (setting D).τ, ((fun i' c => if i' = i₀ then ρ (ri.1, j, ri.2) c else 0) i ᵥ*
      (setting D).ginv A) ri) =
      if i = i₀ then mulPKm (K := D.K) (fun a c => A a c) (fun d _ c => ρ d c) 0 j else 0 := by
  have h := mulPK_eq_mulPKm D A (fun d => Matrix.of fun _ => ρ d)
  split_ifs with hi
  · have := congrFun (congrFun h 0) j
    simp only [hi, ↓reduceIte]
    exact this
  · refine Finset.sum_eq_zero fun ri _ => ?_
    have e : (fun c => if i = i₀ then ρ (ri.1, j, ri.2) c else 0) = (0 : Col (setting D).τ → Rg D) := by
      funext c; exact if_neg hi
    show ((fun c => if i = i₀ then ρ (ri.1, j, ri.2) c else 0) ᵥ* (setting D).ginv A) ri = 0
    rw [e, Matrix.zero_vecMul]; rfl

/-- **`slabMul` with `Z`, `R^in` on the row `0`** is `seLc`. -/
theorem seSlabL_slabMul (A C : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (μ : Rg D)
    (sc : Slab (setting D)) (z : Col (setting D).τ → Rg D)
    (ρ : Dig (setting D).τ → Col (setting D).τ → Rg D) :
    seSlabL D (slabMul A C μ sc (fun i c => if i = (setting D).row0 then z c else 0)
      (fun d i c => if i = (setting D).row0 then ρ d c else 0)) =
      seLc (fun a c => A a c) (fun a c => C a c) μ (fun c => z c) (fun d _ c => ρ d c)
        (seSlabL D sc) := by
  have e : slabMul A C μ sc (fun i c => if i = (setting D).row0 then z c else 0)
      (fun d i c => if i = (setting D).row0 then ρ d c else 0) =
      fun i c => ((fun i => sc i ᵥ* (setting D).ginv C) i c +
        if i = (setting D).row0 then seRowSmul (K := D.K) μ (fun c => z c) c else 0) +
        if i = (setting D).row0 then mulPKm (K := D.K) (fun a c => A a c) (fun d _ c => ρ d c) 0 c
          else 0 := by
    funext i c
    simp only [slabMul]
    rw [slabMul_digit_row D A (setting D).row0 i ρ c]
    by_cases hi : i = (setting D).row0
    · simp only [hi, ↓reduceIte, seRowSmul]; ring
    · simp only [hi, ↓reduceIte, mul_zero, add_zero, zero_add]
  rw [e, seSlabL_addRow, seSlabL_addRow, seSlabL_ginv]
  rfl

/-! ### `Aut` on a slab with fresh data on the rows `0` and `2^t` -/

theorem autMat_seMatAut (m : ℕ) (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    (fun (a : Fin 2) (c : Fin 2 × Fin D.K) => autMat (setting D) ((setting D).idx m) A a c) =
      seMatAut (K := D.K) (gD D) m (fun a c => A a c) := by
  funext a c; exact seSigIdx D m (A a c)

theorem autMid_eq (m : ℕ) (Aaut : Dig (setting D).τ → Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    (fun (a : Fin 2) (c : Fin 2 × Fin D.K) => autMid (setting D) ((setting D).idx m) Aaut A a c) =
      mulPKm (K := D.K) (seMatAut (gD D) m (fun a c => A a c)) (fun d a c => Aaut d a c) := by
  rw [← autMat_seMatAut]
  funext a c
  exact congrFun (congrFun (mulPK_eq_mulPKm D (autMat (setting D) ((setting D).idx m) A) Aaut) a) c

/-- A row supported on `i₀` times `G⁻¹(Y)`. -/
theorem vecMul_ginv_row (i₀ i : Fin (setting D).E.W) (h : Col (setting D).τ → Rg D)
    (Y : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (c : Col (setting D).τ) :
    ((fun i' c => if i' = i₀ then h c else 0) i ᵥ* (setting D).ginv Y) c =
      if i = i₀ then seGRow (K := D.K) (fun c => h c) (fun a c => Y a c) c else 0 := by
  split_ifs with hi
  · simp only [hi, ↓reduceIte]
    exact congrFun (vecMul_ginv_eq D h Y) c
  · have e : (fun c => if i = i₀ then h c else 0) = (0 : Col (setting D).τ → Rg D) := by
      funext c; exact if_neg hi
    show ((fun c => if i = i₀ then h c else 0) ᵥ* (setting D).ginv Y) c = 0
    rw [e, Matrix.zero_vecMul]; rfl

/-- **`slabAut (2^t)`** with `R_{H}` on the row `0` and `R_C`, `R^aut` on the row `rowT t`
is the slab part of `seStep`. -/
theorem seSlabL_slabAut {t : ℕ} (ht : t < D.b) (Hk' : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Aaut : Dig (setting D).τ → Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (hk' : Col (setting D).τ → Rg D) (μ : Rg D)
    (h cr : Col (setting D).τ → Rg D) (ρ : Dig (setting D).τ → Col (setting D).τ → Rg D)
    (sc : Slab (setting D)) :
    seSlabL D (slabAut (2 ^ t) Hk' Aaut A hk' μ
      (fun i c => if i = (setting D).row0 then h c else 0)
      (fun i c => if i = (setting D).rowT t then cr c else 0)
      (fun d i c => if i = (setting D).rowT t then ρ d c else 0) sc) =
      seAddAt (seAddAt (seAddAt ((((seSlabL D sc).map (seRowAut (gD D) (2 ^ t))).rotate
        ((setting D).E.W - 2 ^ t)).map fun v => seGRow v
          (fun a c => gcAut (setting D) ((setting D).idx (2 ^ t)) Hk' hk' a c)) (2 ^ t)
        (mulPKm (seMatAut (gD D) (2 ^ t) (fun a c => A a c)) (fun d _ c => ρ d c) 0)) (2 ^ t)
        (seRowSmul ((aut D.N (gD D))^[2 ^ t] μ) (fun c => cr c))) 0
        (seGRow (fun c => h c) (mulPKm (seMatAut (gD D) (2 ^ t) (fun a c => A a c))
          (fun d a c => Aaut d a c))) := by
  have hT : ((setting D).rowT t).val = 2 ^ t := rowT_val ht
  have e : slabAut (2 ^ t) Hk' Aaut A hk' μ
      (fun i c => if i = (setting D).row0 then h c else 0)
      (fun i c => if i = (setting D).rowT t then cr c else 0)
      (fun d i c => if i = (setting D).rowT t then ρ d c else 0) sc =
      fun i c => (((fun i => slabPerm (2 ^ t) sc i ᵥ* (setting D).ginv
        (gcAut (setting D) ((setting D).idx (2 ^ t)) Hk' hk')) i c +
        if i = (setting D).rowT t then
          mulPKm (K := D.K) (seMatAut (gD D) (2 ^ t) (fun a c => A a c)) (fun d _ c => ρ d c) 0 c
          else 0) +
        if i = (setting D).rowT t then
          seRowSmul (K := D.K) ((aut D.N (gD D))^[2 ^ t] μ) (fun c => cr c) c else 0) +
        if i = (setting D).row0 then seGRow (K := D.K) (fun c => h c)
          (mulPKm (seMatAut (gD D) (2 ^ t) (fun a c => A a c)) (fun d a c => Aaut d a c)) c
          else 0 := by
    funext i c
    simp only [slabAut, slabMul, Pi.add_apply]
    rw [vecMul_ginv_row D (setting D).row0 i h, slabMul_digit_row D _ ((setting D).rowT t) i ρ c,
      autMid_eq, autMat_seMatAut, seSigIdx]
    by_cases h1 : i = (setting D).rowT t <;> by_cases h0 : i = (setting D).row0
    · simp only [if_pos h1, if_pos h0, seRowSmul]; ring
    · simp only [if_pos h1, if_neg h0, seRowSmul]; ring
    · simp only [if_neg h1, if_pos h0, seRowSmul, mul_zero, add_zero]; ring
    · simp only [if_neg h1, if_neg h0, seRowSmul, mul_zero, add_zero, zero_add]
  rw [e, seSlabL_addRow, seSlabL_addRow, seSlabL_addRow, seSlabL_ginv, seSlabL_perm D ht, hT]
  rfl

end AdvancedEncryption.ExpLUT.Prog
