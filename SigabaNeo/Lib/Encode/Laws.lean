import SigabaNeo.Lib.Encode.Ring
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.Product
import Mathlib.Data.List.NodupEquivFin

/-!
# Laws of encoded values

The words a sampling program writes are concatenations of independent pieces. Here the laws of
words, for the fixed-length encodings of `SigabaNeo.Encode.Enum`:

* `catPow μ n`: `n` independent words from `μ`, concatenated (first drawn first);
  `catPow_succ'` (the first piece first), `catPow_uniformList` (uniform pieces give a uniform word);
* `pi_map_flatMap`: the values of an independent family on an enumerated type, mapped to words and
  concatenated in the order of the enumeration, are `catPow`; `fun_enc_pi`: the same for
  `FixedEnc.fun`;
* `uniform_map_enc`: a fixed-length encoding of a type with exactly `2^n` elements sends the
  uniform law to the uniform law on words of `n` bits; `prod_enc_bind`: an independent pair is
  encoded as the concatenation of independent words.
-/

namespace SigabaNeo.Encode

open Cslib Cslib.Probability

/-! ### Concatenated independent words -/

/-- `n` independent words from `μ`, concatenated in the order they are drawn. -/
noncomputable def catPow (μ : PMF (List Bool)) : ℕ → PMF (List Bool)
  | 0 => PMF.pure []
  | n + 1 => (catPow μ n).bind fun u => μ.map (u ++ ·)

@[simp] theorem catPow_zero (μ : PMF (List Bool)) : catPow μ 0 = PMF.pure [] := rfl

theorem catPow_succ (μ : PMF (List Bool)) (n : ℕ) :
    catPow μ (n + 1) = (catPow μ n).bind fun u => μ.map (u ++ ·) := rfl

/-- The first piece first. -/
theorem catPow_succ' (μ : PMF (List Bool)) : ∀ n : ℕ,
    catPow μ (n + 1) = μ.bind fun u => (catPow μ n).map (u ++ ·)
  | 0 => by
    simp only [catPow, PMF.pure_bind, PMF.pure_map, List.nil_append, List.append_nil]
    rw [show (fun x : List Bool => x) = id from rfl, PMF.map_id]
    exact (PMF.bind_pure μ).symm
  | n + 1 => by
    conv_lhs => rw [catPow_succ μ (n + 1), catPow_succ' μ n, PMF.bind_bind]
    congr 1
    funext u
    rw [catPow_succ μ n, PMF.map_bind, PMF.bind_map]
    congr 1
    funext v
    simp only [Function.comp_apply, PMF.map_comp]
    congr 1
    funext w
    simp

/-- Every word of `catPow μ n` has length `n · m` if every word of `μ` has length `m`. -/
theorem length_of_mem_support_catPow {μ : PMF (List Bool)} {m : ℕ}
    (hμ : ∀ u ∈ μ.support, u.length = m) : ∀ (n : ℕ) (u : List Bool),
    u ∈ (catPow μ n).support → u.length = n * m
  | 0, u, h => by simpa using h
  | n + 1, u, h => by
    rw [catPow_succ, PMF.mem_support_bind_iff] at h
    obtain ⟨v, hv, h⟩ := h
    rw [PMF.mem_support_map_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    rw [List.length_append, length_of_mem_support_catPow hμ n v hv, hμ w hw, Nat.succ_mul]

/-- **Uniform pieces give a uniform word.** -/
theorem catPow_uniformList (m : ℕ) : ∀ n : ℕ,
    catPow (BitString.uniformList m) n = BitString.uniformList (n * m)
  | 0 => by simp
  | n + 1 => by rw [catPow_succ, catPow_uniformList m n, Nat.succ_mul, BitString.uniformList_add]

/-- `catPow` of an image. -/
theorem catPow_congr {μ ν : PMF (List Bool)} (h : μ = ν) (n : ℕ) : catPow μ n = catPow ν n := by
  rw [h]

/-! ### Independent families along an enumeration -/

/-- Independent coordinates are invariant under reindexing. -/
theorem pi_comp_equiv' {ι κ β : Type} [Fintype ι] [Fintype κ] [Finite β] (d : PMF β)
    (e : κ ≃ ι) :
    (PMF.pi fun _ : ι => d).map (fun v => v ∘ e) = PMF.pi fun _ : κ => d := by
  classical
  ext w
  rw [PMF.map_apply, tsum_eq_single (w ∘ e.symm)]
  · rw [if_pos (by funext k; simp), PMF.pi_apply, PMF.pi_apply]
    exact Fintype.prod_equiv e.symm _ _ (fun i => rfl)
  · intro v hv
    rw [if_neg]
    intro h
    exact hv (by funext i; rw [h]; simp)

/-- Along `Fin n`. -/
theorem pi_fin_map_flatMap {β : Type} [Finite β] (ν : PMF β) (g : β → List Bool) : ∀ n : ℕ,
    (PMF.pi fun _ : Fin n => ν).map (fun T => (List.ofFn T).flatMap g) = catPow (ν.map g) n
  | 0 => by
    rw [catPow_zero]
    ext T
    rw [PMF.map_apply, tsum_eq_single (fun i => Fin.elim0 i)]
    · simp [PMF.pi_apply]
    · intro b hb; exact absurd (funext fun i => Fin.elim0 i) hb
  | n + 1 => by
    rw [PMF.pi_fin_succ, PMF.map_bind, catPow_succ', PMF.bind_map]
    congr 1
    funext a
    rw [← pi_fin_map_flatMap ν g n]
    show _ = PMF.map (g a ++ ·) (PMF.map _ _)
    rw [PMF.map_comp, PMF.map_comp]
    congr 1
    funext T
    simp [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- **An independent family on an enumerated type, concatenated in the enumeration's order.** -/
theorem pi_map_flatMap {α β : Type} [Enum α] [Fintype α] [DecidableEq α] [Finite β] (ν : PMF β)
    (g : β → List Bool) :
    (PMF.pi fun _ : α => ν).map (fun T => ((Enum.list (α := α)).map T).flatMap g) =
      catPow (ν.map g) (Enum.list (α := α)).length := by
  let e : Fin (Enum.list (α := α)).length ≃ α :=
    List.Nodup.getEquivOfForallMemList _ Enum.nodup Enum.complete
  rw [← pi_fin_map_flatMap ν g, ← pi_comp_equiv' ν e, PMF.map_comp]
  congr 1
  funext T
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [e, List.Nodup.getEquivOfForallMemList]

/-- **Independent values, encoded as a function.** -/
theorem fun_enc_pi {α β : Type} [Enum α] [Fintype α] [DecidableEq α] [Finite β] {n : ℕ}
    (e : FixedEnc β n) (ν : PMF β) :
    (PMF.pi fun _ : α => ν).map (FixedEnc.fun (α := α) e).enc =
      catPow (ν.map e.enc) (Enum.list (α := α)).length :=
  pi_map_flatMap ν e.enc

/-! ### Uniform laws -/

/-- **A full fixed-length encoding sends the uniform law to uniform words.** -/
theorem uniform_map_enc {α : Type} [Fintype α] [Nonempty α] {n : ℕ} (e : FixedEnc α n)
    (h : Fintype.card α = 2 ^ n) :
    (PMF.uniformOfFintype α).map e.enc = BitString.uniformList n := by
  let g : α → (Fin n → Bool) := fun a i => (e.enc a)[i.val]'(by rw [e.length]; exact i.isLt)
  have hg : ∀ a, List.ofFn (g a) = e.enc a := fun a =>
    List.ext_getElem (by simp [e.length]) (fun i h1 h2 => by simp [g])
  have hinj : Function.Injective g := fun a b hab => e.inj (by rw [← hg, ← hg, hab])
  have hbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [h]⟩
  let eq : α ≃ (Fin n → Bool) := Equiv.ofBijective g hbij
  have : e.enc = List.ofFn ∘ eq := funext fun a => (hg a).symm
  rw [this, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]
  rfl

/-- **An independent pair is encoded as two independent words.** -/
theorem prod_enc_bind {β γ : Type} {n m : ℕ} (e : FixedEnc β n) (f : FixedEnc γ m) (μ : PMF β)
    (ν : PMF γ) :
    (μ.bind fun b => ν.map fun c => (b, c)).map (e.prod f).enc =
      (μ.map e.enc).bind fun u => (ν.map f.enc).map (u ++ ·) := by
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext b
  show _ = PMF.map (e.enc b ++ ·) (PMF.map f.enc ν)
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- The uniform law on a product. -/
theorem uniform_prod_eq {β γ : Type} [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ] :
    PMF.uniformOfFintype (β × γ) =
      (PMF.uniformOfFintype β).bind fun b => (PMF.uniformOfFintype γ).map fun c => (b, c) := by
  rw [← PMF.uniformOfFintype_prod]

end SigabaNeo.Encode
