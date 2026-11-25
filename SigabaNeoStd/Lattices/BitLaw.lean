import SigabaNeoStd.Lattices.CoinMaps
import SigabaNeoStd.Lattices.Flood

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

/-- A ring element with independent coefficients from a bit law. -/
theorem polyOf {N q : ℕ} [NeZero q] {χ : PMF (ZMod q)} {m : ℕ} (h : BitLaw χ m) :
    BitLaw (Lattices.polyOf (N := N) χ) (N * m) := by
  have := (pi (ι := Fin N) h).map Negacyclic.ofCoeffs
  simpa [Lattices.polyOf] using this

/-- **A uniform ring element** of `ℤ_{2^K}[X]/(X^N + 1)`: `N · K` bits. -/
theorem uniform_ring (N K : ℕ) :
    BitLaw (PMF.uniformOfFintype (Negacyclic (ZMod (2 ^ K)) N)) (N * K) := by
  have : NeZero (2 ^ K) := ⟨by positivity⟩
  have h := (pi (ι := Fin N) (uniform_zmod K)).map Negacyclic.ofCoeffs
  rw [Cslib.Probability.PMF.pi_uniformOfFintype] at h
  have he := Cslib.Probability.PMF.uniformOfFintype_map_equiv
    (Negacyclic.coeffsEquiv (R := ZMod (2 ^ K)) (n := N)).symm
  simp only [Fintype.card_fin] at h
  rw [show (Negacyclic.ofCoeffs : (Fin N → ZMod (2 ^ K)) → _) =
    (Negacyclic.coeffsEquiv (R := ZMod (2 ^ K)) (n := N)).symm from rfl, he] at h
  exact h

/-- **Centered binomial coefficients**: `2η` bits. -/
theorem cbd {q : ℕ} [NeZero q] (η : ℕ) : BitLaw (ModuleLWE.coeffLaw q (.cbd η)) (η + η) := by
  let e : (Fin (η + η) → Bool) ≃ (Fin η → Bool) × (Fin η → Bool) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  exact (uniform_equiv (η + η) e).map _

/-- The uniform law on `{0, …, 2^w − 1}`: `w` bits. -/
theorem uniform_fin_pow (w : ℕ) : BitLaw (PMF.uniformOfFintype (Fin (2 ^ w))) w :=
  uniform_equiv w ((Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv)

/-- Uniform functions from a finite type to a bit law's uniform type. -/
theorem uniform_fun {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α] {m : ℕ}
    (h : BitLaw (PMF.uniformOfFintype α) m) :
    BitLaw (PMF.uniformOfFintype (ι → α)) (Fintype.card ι * m) := by
  rw [← Cslib.Probability.PMF.pi_uniformOfFintype]
  exact pi h

/-- **Uniform binary vectors**: one bit each. -/
theorem uniform_bits (ι : Type) [Fintype ι] [DecidableEq ι] :
    BitLaw (PMF.uniformOfFintype (ι → Bool)) (Fintype.card ι) :=
  uniform_equiv _ (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl Bool))

/-- **Flooding errors** with width `2^w`. -/
theorem floodLaw {N Q : ℕ} [NeZero Q] (ι : Type) [Fintype ι] [DecidableEq ι] (w : ℕ) :
    haveI : NeZero (2 ^ w) := ⟨by positivity⟩
    BitLaw (Lattices.floodLaw (N := N) (Q := Q) ι (2 ^ w)) (Fintype.card (ι × Fin N) * w) := by
  have : NeZero (2 ^ w) := ⟨by positivity⟩
  exact (uniform_fun (uniform_fin_pow w)).map _

/-- **The uniform law on the image of an embedding of `m` bits.** -/
theorem uniformOfFinset_map {α : Type} [DecidableEq α] (m : ℕ) (emb : (Fin m → Bool) ↪ α) :
    BitLaw (PMF.uniformOfFinset (Finset.univ.map emb) (Finset.univ_nonempty.map)) m := by
  classical
  refine ⟨fun l => emb fun i => l.getD i false, ?_⟩
  rw [BitString.uniformList, PMF.map_comp]
  ext a
  rw [PMF.uniformOfFinset_apply, PMF.map_apply]
  split_ifs with ha
  · obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp ha
    rw [tsum_eq_single b]
    · simp [Finset.card_map, Fintype.card_bool]
    · intro b' hb'
      simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      rw [if_neg]
      intro h
      apply hb'
      have := emb.injective h.symm
      funext i
      have := congrFun this i
      simpa using this
  · refine (tsum_eq_zero_iff.mpr fun b => ?_).symm
    rw [if_neg]
    intro h
    apply ha
    rw [h]
    exact Finset.mem_map_of_mem _ (Finset.mem_univ _)

end BitLaw

end SigabaNeo.Lattices
