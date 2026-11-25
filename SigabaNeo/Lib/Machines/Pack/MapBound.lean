import SigabaNeo.Lib.Machines.Pack.Restrict

/-!
# Per-tape bounds of a relabelled program

For an embedding `e : Fin n ↪ Fin k` and `p : Prog n`:

* **`Prog.lenBoundT_map`**: `lenBoundT (map e p) ℓ = embedF e ℓ (lenBoundT p (ℓ ∘ e))`;
* **`Prog.timeBoundT_le_map`**: `timeBoundT p (ℓ ∘ e) ≤ timeBoundT (map e p) ℓ` (the relabelled
  program's primitives sweep more tapes);
* `embedF_trans'`: embedding in two steps, for any value type.
-/

namespace SigabaNeo.Tape

open Function

variable {n k : ℕ}

theorem embedF_trans' {α : Type} {K : ℕ} (e : Fin n ↪ Fin k) (σ : Fin k ↪ Fin K) (S : Fin K → α)
    (a : Fin n → α) : embedF σ S (embedF e (fun j => S (σ j)) a) = embedF (e.trans σ) S a := by
  rw [XProg.embedF_eq_extend, XProg.embedF_eq_extend, XProg.embedF_eq_extend]
  funext x
  by_cases hx : ∃ i, σ i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [σ.injective.extend_apply]
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [e.injective.extend_apply]
      exact ((e.trans σ).injective.extend_apply a S j).symm
    · rw [Function.extend_apply' _ _ _ hi, Function.extend_apply']
      rintro ⟨j, hj⟩
      exact hi ⟨j, σ.injective hj⟩
  · rw [Function.extend_apply' _ _ _ hx, Function.extend_apply']
    rintro ⟨j, hj⟩
    exact hx ⟨e j, hj⟩

theorem embedF_comp_self' {α : Type} (e : Fin n ↪ Fin k) (f : Fin k → α) (g : Fin n → α) :
    (fun j => embedF e f g (e j)) = g := funext fun j => embedF_apply_self e f g j

theorem embedF_embedF' {α : Type} (e : Fin n ↪ Fin k) (f : Fin k → α) (a b : Fin n → α) :
    embedF e (embedF e f a) b = embedF e f b := by
  funext l
  rcases embedF_cases e f b l with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · simp only [embedF, hn, Option.elim]
  · simp

theorem tailB_comp (e : Fin n ↪ Fin k) (i : Fin n) (ℓ : Fin k → ℕ) :
    (fun j => tailB (e i) ℓ (e j)) = tailB i (fun j => ℓ (e j)) := by
  funext j
  by_cases h : j = i
  · subst h; simp [tailB]
  · simp [tailB, Function.update_apply, h, e.injective.eq_iff]

theorem supB_comp_le (e : Fin n ↪ Fin k) (ℓ : Fin k → ℕ) : supB (fun j => ℓ (e j)) ≤ supB ℓ :=
  Finset.sup_le fun j _ => le_supB ℓ (e j)

namespace Prog

/-- The bounds of a relabelled program, on the relabelled tapes. -/
theorem lenBoundT_map_apply (e : Fin n ↪ Fin k) :
    ∀ (p : Prog n) (ℓ : Fin k → ℕ) (j : Fin n),
      lenBoundT (map e p) ℓ (e j) = lenBoundT p (fun j => ℓ (e j)) j
  | prim a, ℓ, j => Sym.lenT_map e.injective a ℓ j
  | coin i, ℓ, j => by
    simp only [map, lenBoundT, Function.update_apply, e.injective.eq_iff]
  | seq p q, ℓ, j => by
    simp only [map, lenBoundT]
    rw [lenBoundT_map_apply e q]
    congr 1
    funext j'
    exact lenBoundT_map_apply e p ℓ j'
  | ifBlank i p q, ℓ, j => by
    simp only [map, lenBoundT]
    rw [lenBoundT_map_apply e p, lenBoundT_map_apply e q]
  | ifBit i p q, ℓ, j => by
    simp only [map, lenBoundT]
    rw [lenBoundT_map_apply e p, lenBoundT_map_apply e q]
  | loop i b, ℓ, j => by
    simp only [map, lenBoundT, iterSupT]
    have key : ∀ m : ℕ, (fun j => ((fun ℓ' => lenBoundT (map e b) (tailB (e i) ℓ'))^[m] ℓ) (e j)) =
        (fun ℓ' => lenBoundT b (tailB i ℓ'))^[m] (fun j => ℓ (e j)) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
        funext j'
        rw [lenBoundT_map_apply e b, tailB_comp]
    congr 1
    funext m
    exact congrFun (key m) j

/-- **The bounds of a relabelled program.** -/
theorem lenBoundT_map (e : Fin n ↪ Fin k) (p : Prog n) (ℓ : Fin k → ℕ) :
    lenBoundT (map e p) ℓ = embedF e ℓ (lenBoundT p (fun j => ℓ (e j))) := by
  funext t
  rcases embedF_cases e ℓ (lenBoundT p (fun j => ℓ (e j))) t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h]
    refine lenBoundT_of_preserves t _ (preserves_map_of_not_mem (fun m hm => ?_) p) ℓ
    subst hm
    rw [partialInv_self] at hn
    exact Option.some_ne_none _ hn
  · rw [h, lenBoundT_map_apply]

theorem lenBoundT_map_comp (e : Fin n ↪ Fin k) (p : Prog n) (ℓ : Fin k → ℕ) :
    (fun j => lenBoundT (map e p) ℓ (e j)) = lenBoundT p (fun j => ℓ (e j)) :=
  funext fun j => lenBoundT_map_apply e p ℓ j

/-- **The clock of a relabelled program** is at least that of the program. -/
theorem timeBoundT_le_map (e : Fin n ↪ Fin k) :
    ∀ (p : Prog n) (ℓ : Fin k → ℕ), timeBoundT p (fun j => ℓ (e j)) ≤ timeBoundT (map e p) ℓ
  | prim a, ℓ => by
    have := supB_comp_le e ℓ
    simp only [map, timeBoundT, Prim.pad_map]
    omega
  | coin i, ℓ => by
    have := supB_comp_le e ℓ
    simp only [map, timeBoundT]
    omega
  | seq p q, ℓ => by
    simp only [map, timeBoundT]
    have h1 := timeBoundT_le_map e p ℓ
    have h2 := timeBoundT_le_map e q (lenBoundT (map e p) ℓ)
    rw [lenBoundT_map_comp] at h2
    omega
  | ifBlank i p q, ℓ => by
    simp only [map, timeBoundT]
    have h1 := timeBoundT_le_map e p ℓ
    have h2 := timeBoundT_le_map e q ℓ
    omega
  | ifBit i p q, ℓ => by
    simp only [map, timeBoundT]
    have h1 := timeBoundT_le_map e p ℓ
    have h2 := timeBoundT_le_map e q ℓ
    omega
  | loop i b, ℓ => by
    simp only [map, timeBoundT]
    have key : ∀ m : ℕ, (fun j => ((loopStepT (e i) (map e b))^[m] ℓ) (e j)) =
        (loopStepT i b)^[m] (fun j => ℓ (e j)) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
        funext j'
        simp only [loopStepT]
        rw [lenBoundT_map_apply e b, tailB_comp]
    refine Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right ?_ 1)) 2
    refine Finset.sup_mono_fun fun m _ => ?_
    rw [← key m]
    simp only [roundTimeT]
    have h1 := supB_comp_le e ((loopStepT (e i) (map e b))^[m] ℓ)
    have h2 := timeBoundT_le_map e b (tailB (e i) ((loopStepT (e i) (map e b))^[m] ℓ))
    rw [tailB_comp] at h2
    omega

end Prog

end SigabaNeo.Tape
