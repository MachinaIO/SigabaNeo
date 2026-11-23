module

public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Geometry
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Geometry
import Mathlib.Tactic

/-! The full-rank integer graph, exact closest-point oracle, and the isometric
change to affine residual coordinates used in the translated-ball count. -/

public section
namespace SigabaNeo.Wall1.Width638
open QaryMembership SigabaNeo.SampleDeletion Matrix Finset Module

variable {r n q : ℕ} [Fact q.Prime]

def graph (A : Design r n q) : Submodule ℤ (Grid r n) where
  carrier := {x | ∀ i, (x (.inl i) : ZMod q) = ∑ j, A i j * (x (.inr j) : ZMod q)}
  zero_mem' := by simp
  add_mem' {x y} hx hy i := by
    simp [Pi.add_apply, hx i, hy i, mul_add, sum_add_distrib]
  smul_mem' k x hx i := by
    simp [Pi.smul_apply, hx i, mul_left_comm, mul_sum]

theorem graph_rank (A : Design r n q) : finrank ℤ (graph A) = r+n := by
  let f : Grid r n →ₗ[ℤ] Grid r n := (q : ℤ) • LinearMap.id
  have hf (x : Grid r n) : f x ∈ graph A := by
    intro i
    simp [f, zsmul_eq_mul, Pi.smul_apply]
  let g := f.codRestrict (graph A) hf
  have inj : Function.Injective g := by
    intro x y h
    funext i
    have e := congrArg (fun z : graph A ↦ z.val i) h
    change (q : ℤ)*x i = (q : ℤ)*y i at e
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr (Fact.out : Nat.Prime q).ne_zero) e
  have dim : finrank ℤ (Grid r n) = r+n := by simp [Grid]
  exact ((Submodule.finrank_le _).trans dim.le).antisymm (dim.ge.trans (g.finrank_le_finrank_of_injective inj))

def target (t : Fin r → ℤ) : Grid r n := Sum.elim t (fun _ ↦ 0)

/-- This involution takes graph points to residuals and back. -/
def switch (t : Fin r → ℤ) (w : Grid r n) : Grid r n :=
  Sum.elim (fun i ↦ t i - w (.inl i)) (fun j ↦ w (.inr j))

theorem switch_switch (t : Fin r → ℤ) (w : Grid r n) : switch t (switch t w) = w := by
  funext i
  cases i <;> simp [switch]

theorem switch_norm (t : Fin r → ℤ) (w : Grid r n) :
    normSq (switch t w) = normSq (w - target t) := by
  unfold normSq
  apply sum_congr rfl
  intro i _
  cases i with
  | inr j => simp [switch, target]
  | inl i =>
    simp only [switch, target, Sum.elim_inl, Pi.sub_apply]
    rw [← Int.natAbs_neg (t i - w (.inl i)), neg_sub]

theorem switch_mem (A : Design r n q) (t : Fin r → ℤ) (w : Grid r n) :
    switch t w ∈ graph A ↔ output A w = (fun i ↦ (t i : ZMod q)) := by
  change (∀ i, ((t i - w (.inl i) : ℤ) : ZMod q) = _) ↔ _
  rw [funext_iff]
  apply forall_congr'
  intro i
  simp only [Int.cast_sub, output, Pi.add_apply, mulVec, dotProduct, switch, Sum.elim_inr]
  exact sub_eq_iff_eq_add'.trans eq_comm

structure GraphOracle (r n q : ℕ) [Fact q.Prime] where
  closest : Design r n q → (Fin r → ℤ) → Grid r n
  mem : ∀ A t, closest A t ∈ graph A
  minimal : ∀ A t w, w ∈ graph A → normSq (closest A t - target t) ≤ normSq (w - target t)

/-- Existence is by well-ordering squared integer distances. -/
theorem graphOracle_nonempty : Nonempty (GraphOracle r n q) := by
  classical
  have ex (A : Design r n q) (t : Fin r → ℤ) :
      ∃ k : ℕ, ∃ w ∈ graph A, normSq (w - target t) = k :=
    ⟨_, 0, (graph A).zero_mem, rfl⟩
  choose f hf he using fun A t ↦ Nat.find_spec (ex A t)
  exact ⟨⟨f, hf, fun A t w hw ↦ (he A t).trans_le (Nat.find_min' (ex A t) ⟨w,hw,rfl⟩)⟩⟩

def affineOracle (O : GraphOracle r n q) : CVPOracle r n q where
  closest A y := let t i := ((y i).val : ℤ); switch t (O.closest A t)
  feasible A y := by
    let t i := ((y i).val : ℤ)
    have h := (switch_mem A t (switch t (O.closest A t))).mp (by rw [switch_switch]; exact O.mem A t)
    simpa [t] using h
  minimal A y w hw := by
    let t i := ((y i).val : ℤ)
    have hm : switch t w ∈ graph A := (switch_mem ..).mpr (by simpa [t] using hw)
    have h := O.minimal A t _ hm
    rwa [← switch_norm, ← switch_norm, switch_switch] at h

end SigabaNeo.Wall1.Width638
#print axioms SigabaNeo.Wall1.Width638.graph_rank
#print axioms SigabaNeo.Wall1.Width638.graphOracle_nonempty
#print axioms SigabaNeo.Wall1.Width638.affineOracle
