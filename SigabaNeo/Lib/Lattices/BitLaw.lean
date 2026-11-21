import SigabaNeo.Lib.Lattices.CoinMaps

/-!
# Laws realized by fair coins

`BitLaw μ m`: the law `μ` is the image of `m` uniform bits. Such a law is realized exactly by a
machine that draws `m` fair coins (`SigabaNeo.Machine.exists_randomized`). Bit laws are closed
under `pure`, `map` (`BitLaw.map`), `bind` (`BitLaw.bind`, the bits add up) and independent
products over a finite index (`BitLaw.pi`); the uniform law on a type of `2^m` elements is one
(`BitLaw.uniform_equiv`), and so is the uniform residue mod `2^K` (`BitLaw.uniform_zmod`).
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Probability

/-- `μ` is the image of `m` uniform bits. -/
def BitLaw {α : Type*} (μ : PMF α) (m : ℕ) : Prop :=
  ∃ g : List Bool → α, μ = (BitString.uniformList m).map g

namespace BitLaw

theorem pure {α : Type*} (a : α) : BitLaw (PMF.pure a) 0 :=
  ⟨fun _ => a, by simp [BitString.uniformList_zero]⟩

theorem map {α β : Type*} {μ : PMF α} {m : ℕ} (h : BitLaw μ m) (f : α → β) :
    BitLaw (μ.map f) m := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨f ∘ g, by rw [PMF.map_comp]⟩

theorem bind {α β : Type*} {μ : PMF α} {m₁ m₂ : ℕ} {f : α → PMF β} (h₁ : BitLaw μ m₁)
    (h₂ : ∀ a, BitLaw (f a) m₂) : BitLaw (μ.bind f) (m₁ + m₂) := by
  classical
  obtain ⟨g₁, rfl⟩ := h₁
  choose g₂ hg₂ using h₂
  refine ⟨fun tape => g₂ (g₁ (tape.take m₁)) (tape.drop m₁), ?_⟩
  rw [PMF.bind_map, PMF.map]
  have h := BitString.uniformList_bind_split m₁ m₂ (fun a b => PMF.pure (g₂ (g₁ a) b))
  simp only [Function.comp_def] at h ⊢
  rw [h]
  congr 1
  funext a
  rw [hg₂, PMF.map]
  rfl

theorem congr_bits {α : Type*} {μ : PMF α} {m m' : ℕ} (h : BitLaw μ m) (hm : m = m') :
    BitLaw μ m' := hm ▸ h

/-- The uniform law on a type in bijection with `m` bits. -/
theorem uniform_equiv {α : Type} [Fintype α] [Nonempty α] (m : ℕ) (e : (Fin m → Bool) ≃ α) :
    BitLaw (PMF.uniformOfFintype α) m := by
  refine ⟨fun l => e fun i => l.getD i false, ?_⟩
  rw [BitString.uniformList, PMF.map_comp, ← Cslib.Probability.PMF.uniformOfFintype_map_equiv e]
  congr 1
  funext b
  simp

/-- **The uniform residue mod `2^K`.** -/
theorem uniform_zmod (K : ℕ) : BitLaw (PMF.uniformOfFintype (ZMod (2 ^ K))) K := by
  refine ⟨fun l => bitsToZMod K fun i => l.getD i false, ?_⟩
  rw [BitString.uniformList, PMF.map_comp, ← uniform_bitsToZMod]
  congr 1
  funext b
  simp

/-- **Independent draws.** -/
theorem pi_fin {α : Type} [Finite α] {μ : PMF α} {m : ℕ} (h : BitLaw μ m) :
    ∀ n, BitLaw (PMF.pi fun _ : Fin n => μ) (n * m)
  | 0 => by
    have : PMF.pi (fun _ : Fin 0 => μ) = PMF.pure Fin.elim0 := by
      ext f; rw [PMF.pi_apply, PMF.pure_apply, if_pos (funext fun i => i.elim0)]; simp
    rw [this, Nat.zero_mul]; exact pure _
  | n + 1 => by
    rw [PMF.pi_fin_succ]
    obtain ⟨g, hg⟩ := pi_fin h n
    have hb : BitLaw (μ.bind fun a => (PMF.pi fun _ : Fin n => μ).map
        (fun v : Fin n → α => (Fin.cons a v : Fin (n + 1) → α))) (m + n * m) := by
      refine bind h fun a => ?_
      rw [hg]
      exact ⟨(fun v : Fin n → α => (Fin.cons a v : Fin (n + 1) → α)) ∘ g, by rw [PMF.map_comp]⟩
    exact hb.congr_bits (by ring)

/-- **Independent draws over any finite index.** -/
theorem pi {ι α : Type} [Fintype ι] [Finite α] {μ : PMF α} {m : ℕ} (h : BitLaw μ m) :
    BitLaw (PMF.pi fun _ : ι => μ) (Fintype.card ι * m) := by
  rw [← pi_comp_equiv μ (Fintype.equivFin ι)]
  exact (pi_fin h _).map _

end BitLaw

end SigabaNeo.Lattices
