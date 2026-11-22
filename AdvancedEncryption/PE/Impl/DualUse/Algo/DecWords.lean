import PE.Impl.DualUse.Algo.KeyTry

/-!
# The end of decryption on words

`decFinW`: from the words of `c₀`, `k₀`, `c₁`, `k₁`, `c_f̂`, `k₂` and `κ`, the value
`κ − (c₀ k₀ + c₁ k₁ + c_f̂ k₂)` (three dot products, two sums and a difference) and the rounding of
its constant coefficient: `true` iff its centered absolute value exceeds `2^(K−2) − 1`, i.e.
`decodeBit` (`decFinW_eq`, for `K ≥ 2`).
-/

namespace AdvancedEncryption.DualUse.Algo

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo Matrix
  AdvancedEncryption.RingBTVW

variable {N K k : ℕ}

/-- The value `κ − (c₀ k₀ + c₁ k₁ + c_f̂ k₂)` on words. -/
def decValW (N K d L k : ℕ) (c0 k0 c1 k1 cf k2 κ : List Bool) : List Bool :=
  subRW N K κ (addRW N K (addRW N K (dotW N K d c0 k0) (dotW N K L c1 k1)) (dotW N K (2 * k) cf k2))

/-- The radius of the rounding: `2^(K−2) − 1`. -/
def decRadW (K : ℕ) : List Bool := toBits K (2 ^ (K - 2) - 1)

/-- **The end of decryption on words.** -/
def decFinW (N K d L k : ℕ) (c0 k0 c1 k1 cf k2 κ : List Bool) : Bool :=
  !ballW 1 K (decRadW K) (decValW N K d L k c0 k0 c1 k1 cf k2 κ)

theorem decodeZMod_eq (hK : 2 ≤ K) (x : ZMod (2 ^ K)) :
    decodeZMod (2 ^ K) x = !decide (zabs x ≤ val (decRadW K)) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 2 := ⟨K - 2, by omega⟩
  have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hlt : 2 ^ m - 1 < 2 ^ (m + 2) := by rw [pow_add]; omega
  rw [decRadW, show m + 2 - 2 = m by omega, val_toBits, Nat.mod_eq_of_lt hlt, decodeZMod, zabs]
  have h : ((2 ^ (m + 2) : ℕ) : ℤ) ≤ 4 * |x.valMinAbs| ↔ ¬ x.valMinAbs.natAbs ≤ 2 ^ m - 1 := by
    rw [Int.abs_eq_natAbs]
    generalize x.valMinAbs.natAbs = a
    have e : ((2 ^ (m + 2) : ℕ) : ℤ) = 4 * ((2 ^ m : ℕ) : ℤ) := by push_cast; ring
    rw [e]
    omega
  by_cases h' : x.valMinAbs.natAbs ≤ 2 ^ m - 1
  · rw [decide_eq_false (by rw [h]; exact not_not.mpr h'), decide_eq_true h']; rfl
  · rw [decide_eq_true (h.mpr h'), decide_eq_false h']; rfl

/-- **`decFinW` is the decoded bit of the value.** -/
theorem decFinW_value (hK : 2 ≤ K) (hN : 0 < N) {d L : ℕ} (c0 k0 c1 k1 cf k2 κ : List Bool)
    (v : Rq N K) (hv : decValW N K d L k c0 k0 c1 k1 cf k2 κ = (ringEnc N K).enc v) :
    decFinW N K d L k c0 k0 c1 k1 cf k2 κ = decodeBit hN v := by
  have hs : (decRadW K).length = K := length_toBits _ _
  rw [decFinW, hv, ballW, allN, allN, Bool.true_and,
    absLeW_eq (length_block (length_ringEnc N K v) hN) hs, dec_block_ringEnc, coefOf,
    dite_eq_left_of_eq_true (eq_true hN), decodeBit, decodeZMod_eq hK]

/-- **The value on the words of the matrices.** -/
theorem decValW_eq {d : ℕ} (k0 : Matrix (Fin d) (Fin 1) (Rq N K))
    (k1 : Matrix (DualUse.TrapCol k) (Fin 1) (Rq N K)) (k2 : Matrix (Col k) (Fin 1) (Rq N K))
    (c0 : Matrix (Fin 1) (Fin d) (Rq N K)) (c1 : Matrix (Fin 1) (DualUse.TrapCol k) (Rq N K))
    (E : Matrix (Fin 1) (Col k) (Rq N K)) (κ : Rq N K) :
    decValW N K d (nT k) k (vecW N K (c0 0)) (vecW N K (fun i => k0 i 0)) (vecW N K (c1 0))
      (vecW N K (fun i => k1 i 0)) (rowW N K k E) (vecW N K (fun i => k2 i 0)) ((ringEnc N K).enc κ) =
      (ringEnc N K).enc (κ - (c0 * k0 + c1 * k1 + E * k2) 0 0) := by
  have h0 := dotW_vecW (N := N) (K := K) (c0 0) (fun i => k0 i 0)
  have h1 := dotW_vecW (N := N) (K := K) (c1 0) (fun i => k1 i 0)
  have h2 := dotW_vecW (N := N) (K := K) (E 0) (fun i => k2 i 0)
  rw [len_fin] at h0
  rw [len_trapCol] at h1
  rw [len_col] at h2
  rw [decValW, h0, h1, rowW_eq_vecW, h2, addRW_enc, addRW_enc, subRW_enc]
  congr 2

end AdvancedEncryption.DualUse.Algo
