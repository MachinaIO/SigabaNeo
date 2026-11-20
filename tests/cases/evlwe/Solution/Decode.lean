import Solution.Attack

/-!
# Reading an encoded sample

`entryAt κ (encEntries (W κ) L) idx` is `L[idx] mod 2^W`; for the samples of the experiments,
the attack's readers `qOf`, `cAt`, `kAt`, `auxAt` return `q` and the representatives of the
entries of `C`, `K` and `aux`.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE

theorem listSum_range' {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- Folding `Nat.bit` over the `W` low bits of `v` gives `v mod 2^W`. -/
theorem foldr_bit_bitsOf (W v : ℕ) : (bitsOf W v).foldr Nat.bit 0 = v % 2 ^ W := by
  induction W generalizing v with
  | zero => simp [bitsOf, Nat.mod_one]
  | succ W ih =>
    have h : bitsOf (W + 1) v = v.testBit 0 :: bitsOf W (v / 2) := by
      simp only [bitsOf, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      simp [Nat.testBit_div_two]
    rw [h, List.foldr_cons, ih, Nat.bit_val, pow_succ]
    have h0 : (v.testBit 0).toNat = v % 2 := by
      rw [Nat.testBit_zero]; rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    rw [h0, show 2 ^ W * 2 = 2 * 2 ^ W by ring, Nat.mod_mul]
    ring

theorem length_bitsOf (W v : ℕ) : (bitsOf W v).length = W := by simp [bitsOf]

/-- `entryAt` reads the numbers of an encoding back. -/
theorem binaryEntry_encEntries (W : ℕ) (L : List ℕ) {idx : ℕ} (h : idx < L.length) :
    Cslib.Matrix.binaryEntry 1 W (encEntries W L) idx 0 = L[idx] % 2 ^ W := by
  unfold Cslib.Matrix.binaryEntry encEntries
  rw [show idx * 1 + 0 = idx by ring, ← List.append_nil (L.flatMap (bitsOf W)),
    Cslib.BitString.listRow_flatMap_append (bitsOf W) L (fun a _ => length_bitsOf W a) [] idx h,
    foldr_bit_bitsOf]

/-! ### The sample's layout -/

section
variable (κ : ℕ)

theorem q_lt_W : q κ < 2 ^ W κ := by
  have h : q κ ≤ 2 * 2 ^ w κ := (exists_q κ).choose_spec.2.2
  have h4 : 2 ^ W κ = 4 * 2 ^ w κ := by unfold W; rw [pow_add]; ring
  have := Nat.one_le_two_pow (n := w κ)
  omega

theorem val_lt_W (x : ZMod (q κ)) : x.val < 2 ^ W κ := (ZMod.val_lt x).trans (q_lt_W κ)

variable {κ} (Cq : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)))
  (Kq : Matrix (Fin (m κ)) (Fin (k κ)) (ZMod (q κ)))
  (Aq : Matrix (Fin (ell κ)) (Fin (k κ)) (ZMod (q κ)))

/-- The encoded Post sample. -/
noncomputable def postWord : List Bool := encSample κ (matVals Cq ++ matVals Kq ++ matVals Aq)

theorem entryAt_postWord (idx : ℕ)
    (h : idx < 1 + m κ + m κ * k κ + k κ) :
    entryAt κ (postWord Cq Kq Aq) idx =
      (q κ :: (matVals Cq ++ matVals Kq ++ matVals Aq)).getD idx 0 := by
  have hlen : idx < (q κ :: (matVals Cq ++ matVals Kq ++ matVals Aq)).length := by
    rw [List.length_cons, List.length_append, List.length_append, length_matVals, length_matVals,
      length_matVals]
    simp only [ell]; omega
  unfold entryAt postWord encSample
  rw [binaryEntry_encEntries _ _ hlen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
    Option.getD_some]
  apply Nat.mod_eq_of_lt
  have hall : ∀ x ∈ matVals Cq ++ matVals Kq ++ matVals Aq, x < 2 ^ W κ := by
    intro x hx
    simp only [matVals, List.mem_append, List.mem_flatMap, List.mem_map] at hx
    rcases hx with ((⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) | ⟨_, _, _, _, rfl⟩) <;>
      exact val_lt_W κ _
  cases idx with
  | zero => simpa using q_lt_W κ
  | succ i =>
    simp only [List.getElem_cons_succ]
    exact hall _ (List.getElem_mem _)

theorem k_eq : k κ = m κ + 1 := rfl

/-- The only row of `C` and `aux`. -/
def i0 (κ : ℕ) : Fin (ell κ) := ⟨0, Nat.zero_lt_one⟩

theorem qOf_postWord : qOf κ (postWord Cq Kq Aq) = q κ := by
  unfold qOf; rw [entryAt_postWord _ _ _ 0 (by omega)]; rfl

theorem cAt_postWord (r : Fin (m κ)) : cAt κ (postWord Cq Kq Aq) r = (Cq (i0 κ) r).val := by
  unfold cAt
  rw [entryAt_postWord _ _ _ _ (by have := r.isLt; omega), add_comm 1, List.getD_cons_succ,
    List.getD_append _ _ _ _ (by rw [List.length_append, length_matVals, ell]; omega),
    List.getD_append _ _ _ _ (by rw [length_matVals, ell]; omega)]
  have := getD_matVals Cq (i0 κ) r
  rwa [show (i0 κ).val = 0 from rfl, zero_mul, zero_add] at this

theorem kAt_postWord (r : Fin (m κ)) (j : Fin (k κ)) :
    kAt κ (postWord Cq Kq Aq) r j = (Kq r j).val := by
  unfold kAt
  have hr := r.isLt; have hj := j.isLt
  have hrk : r.val * k κ + j.val < m κ * k κ := by nlinarith
  rw [entryAt_postWord _ _ _ _ (by omega),
    show 1 + m κ + r.val * k κ + j.val = (m κ + r.val * k κ + j.val) + 1 by ring,
    List.getD_cons_succ,
    List.getD_append _ _ _ _ (by rw [List.length_append, length_matVals, length_matVals, ell]; omega),
    List.getD_append_right _ _ _ _ (by rw [length_matVals, ell]; omega)]
  rw [length_matVals, ell, one_mul, show m κ + r.val * k κ + j.val - m κ = r.val * k κ + j.val by omega]
  exact getD_matVals Kq r j

theorem auxAt_postWord (j : Fin (k κ)) : auxAt κ (postWord Cq Kq Aq) j = (Aq (i0 κ) j).val := by
  unfold auxAt
  have hj := j.isLt
  rw [entryAt_postWord _ _ _ _ (by omega),
    show 1 + m κ + m κ * k κ + j.val = (m κ + m κ * k κ + j.val) + 1 by ring,
    List.getD_cons_succ,
    List.getD_append_right _ _ _ _ (by rw [List.length_append, length_matVals, length_matVals, ell]; omega)]
  have hl : (matVals Cq ++ matVals Kq).length = m κ + m κ * k κ := by
    rw [List.length_append, length_matVals, length_matVals]; simp [ell]
  rw [hl, show m κ + m κ * k κ + j.val - (m κ + m κ * k κ) = j.val by omega]
  have := getD_matVals Aq (i0 κ) j
  rwa [show (i0 κ).val = 0 from rfl, zero_mul, zero_add] at this

end

end TestCase.EvLWE
