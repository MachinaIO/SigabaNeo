import SigabaNeo.Lib.Lattices.Research.Wall1.RawScalarMajorant

/-! Kernel-checked sums of the one-coordinate weight for all nontrivial field scalars. -/
namespace SigabaNeo.Wall1.RawScalarWeights

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem block (i : Fin 52) : ∀ k : Fin 64,
    64*i.val+2+k.val < 3328 → smallRow (64*i.val+2+k.val) ≤ 93700 := by
  fin_cases i <;> decide +kernel

theorem smallRow_le (a : ℕ) (lo : 2 ≤ a) (hi : a < 3328) : smallRow a ≤ 93700 := by
  let i : Fin 52 := ⟨(a-2)/64, by omega⟩
  let k : Fin 64 := ⟨(a-2)%64, by omega⟩
  have e : 64*i.val+2+k.val = a := by dsimp [i,k]; omega
  simpa only [e] using block i k (e ▸ hi)

#print axioms smallRow_le
end SigabaNeo.Wall1.RawScalarWeights
