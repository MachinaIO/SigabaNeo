import PE.Impl.RingBTVW.Laws

/-!
# The noise of decryption

A bound on the noise of `decryptRaw_eq` over `R_q = ℤ_q[X]/(X^N + 1)` from bounds on the coins and
the key: if every coefficient of the errors of `Enc` is at most `Bχ` (centered) and every
coefficient of the key at most `K`, then the noise is at most `noiseBound` (`cnorm_noise_le`),
with `WN = |W| · N = 2kN`:

  `Bχ + WN · Bχ · K + WN · (∑_b WN · E(f̂_b) + E(f)) · K`,

where `E(g) = errBound WN Bχ g` grows by `WN` at each NAND on the left (`rnorm_evalErr_le`).
Decryption is then correct whenever `4 · noiseBound + 2 < q` (`decrypt_correct_of_bounds`): the
noise is no longer a hypothesis but a function of the parameters and the circuits. With an error
law bounded by `Bχ` (a truncated Gaussian), every coin of `Enc` meets the bound
(`encCoinsLaw_bounded`), so every ciphertext decrypts (`scheme_correct_bounded`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Cslib Cslib.Probability

variable {N q k : ℕ} [NeZero q] (hk : q ≤ 2 ^ k) {Attr : Type} [Fintype Attr]

/-- The noise bound. -/
noncomputable def noiseBound (Bχ K : ℕ) (f : Circuit Attr) : ℕ :=
  let WN := Fintype.card (Col k) * N
  Bχ + WN * Bχ * K +
    WN * (∑ b, WN * errBound WN Bχ ((ringSetting N q k hk Attr).fhat f b) + errBound WN Bχ f) * K

omit [NeZero q] in
theorem bitR_bit {R : Type*} [CommRing R] (b : Bool) : bitR (R := R) b = 0 ∨ bitR (R := R) b = 1 := by
  cases b <;> simp [bitR]

/-- **The noise is bounded** by the errors of `Enc` and the key. -/
theorem cnorm_noise_le (mpk : MPK (ringSetting N q k hk Attr)) (x : Attr → Bool)
    (f : Circuit Attr) (sk : SecretKey (R := Negacyclic (ZMod q) N) (k := k))
    (r : EncCoins (ringSetting N q k hk Attr)) (Bχ K : ℕ)
    (he' : cnorm r.e' ≤ Bχ) (he₀ : rnorm r.e₀ ≤ Bχ) (heΨ : ∀ i, rnorm (r.eΨ i) ≤ Bχ)
    (hej : ∀ j, rnorm (r.ej j) ≤ Bχ)
    (hk₁ : ∀ c d, cnorm (sk.k₁ c d) ≤ K) (hk₂ : ∀ c d, cnorm (sk.k₂ c d) ≤ K) :
    cnorm (noise mpk x f sk r) ≤ noiseBound (N := N) hk Bχ K f := by
  set Ψ := fun i => stackKey (r.a i) (r.eΨ i) r.s + bitR (R := Negacyclic (ZMod q) N) (x i) • (ringSetting N q k hk Attr).Γ.G
  have hΓ₁ : ∀ A c c', cnorm ((ringSetting N q k hk Attr).Γ₁.ginv A c c') ≤ 1 := fun A c c' =>
    cnorm_gadgetOf_binary_ginv_le hk (fun _ : Fin 1 => (0 : Fin 2)) _ A c c'
  have hΓ : ∀ A c c', cnorm ((ringSetting N q k hk Attr).Γ.ginv A c c') ≤ 1 := fun A c c' =>
    cnorm_gadgetOf_binary_ginv_le hk id _ A c c'
  -- The BGG+ inputs are bits.
  have hψ : ∀ j, bitsOf (ringSetting N q k hk Attr) Ψ j = 0 ∨ bitsOf (ringSetting N q k hk Attr) Ψ j = 1 := fun j => by
    have hb := coeffBits_isBoolean (N := N) hk (Fin 2) (Ψ j.1) j.2
    rcases bitR_bit (R := Negacyclic (ZMod q) N) (coeffBool (Ψ j.1) j.2) with h | h
    · exact Or.inl (hb.trans h)
    · exact Or.inr (hb.trans h)
  -- The BGG+ error.
  have hB : rnorm (∑ b, evalErr (ringSetting N q k hk Attr).Γ₁ mpk.Bj (bitsOf (ringSetting N q k hk Attr) Ψ) r.ej ((ringSetting N q k hk Attr).fhat f b) *
      (ringSetting N q k hk Attr).Γ₁.ginv ((ringSetting N q k hk Attr).rowBits.V b)) ≤ ∑ b, (Fintype.card (Col k) * N) * errBound (Fintype.card (Col k) * N) Bχ ((ringSetting N q k hk Attr).fhat f b) := by
    refine (rnorm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine (rnorm_mul_le _ _ 1 (hΓ₁ _)).trans ?_
    rw [mul_one]
    exact Nat.mul_le_mul_left _ (rnorm_evalErr_le (ringSetting N q k hk Attr).Γ₁ hΓ₁ mpk.Bj _ hψ r.ej Bχ hej _)
  -- The Ring-GSW error.
  have hG : rnorm (evalErr (ringSetting N q k hk Attr).Γ Ψ (fun i => bitR (R := Negacyclic (ZMod q) N) (x i))
      (fun i => -r.eΨ i) f) ≤ errBound (Fintype.card (Col k) * N) Bχ f :=
    rnorm_evalErr_le (ringSetting N q k hk Attr).Γ hΓ _ _ (fun i => bitR_bit _) _ Bχ
      (fun i => by rw [rnorm_neg]; exact heΨ i) f
  -- The whole noise.
  simp only [noise, noiseBound]
  rw [add_assoc]
  refine (cnorm_sub_le _ _).trans ?_
  refine Nat.add_le_add he' ?_
  have h1 := rnorm_mul_le r.e₀ sk.k₁ K hk₁
  have h2 := rnorm_mul_le (∑ b, evalErr (ringSetting N q k hk Attr).Γ₁ mpk.Bj (bitsOf (ringSetting N q k hk Attr) Ψ) r.ej ((ringSetting N q k hk Attr).fhat f b) *
      (ringSetting N q k hk Attr).Γ₁.ginv ((ringSetting N q k hk Attr).rowBits.V b) - evalErr (ringSetting N q k hk Attr).Γ Ψ (fun i => bitR (R := Negacyclic (ZMod q) N) (x i))
        (fun i => -r.eΨ i) f) sk.k₂ K hk₂
  have hsub := rnorm_sub_le (∑ b, evalErr (ringSetting N q k hk Attr).Γ₁ mpk.Bj (bitsOf (ringSetting N q k hk Attr) Ψ) r.ej ((ringSetting N q k hk Attr).fhat f b) *
      (ringSetting N q k hk Attr).Γ₁.ginv ((ringSetting N q k hk Attr).rowBits.V b)) (evalErr (ringSetting N q k hk Attr).Γ Ψ (fun i => bitR (R := Negacyclic (ZMod q) N) (x i))
        (fun i => -r.eΨ i) f)
  refine (cnorm_le_rnorm _ 0).trans ((rnorm_add_le _ _).trans ?_)
  calc rnorm (r.e₀ * sk.k₁) + rnorm ((∑ b, evalErr (ringSetting N q k hk Attr).Γ₁ mpk.Bj (bitsOf (ringSetting N q k hk Attr) Ψ) r.ej ((ringSetting N q k hk Attr).fhat f b) *
        (ringSetting N q k hk Attr).Γ₁.ginv ((ringSetting N q k hk Attr).rowBits.V b) - evalErr (ringSetting N q k hk Attr).Γ Ψ (fun i => bitR (R := Negacyclic (ZMod q) N) (x i))
          (fun i => -r.eΨ i) f) * sk.k₂)
      ≤ (Fintype.card (Col k) * N) * rnorm r.e₀ * K + (Fintype.card (Col k) * N) * (rnorm (∑ b, evalErr (ringSetting N q k hk Attr).Γ₁ mpk.Bj (bitsOf (ringSetting N q k hk Attr) Ψ) r.ej ((ringSetting N q k hk Attr).fhat f b) *
        (ringSetting N q k hk Attr).Γ₁.ginv ((ringSetting N q k hk Attr).rowBits.V b)) + rnorm (evalErr (ringSetting N q k hk Attr).Γ Ψ
          (fun i => bitR (R := Negacyclic (ZMod q) N) (x i)) (fun i => -r.eΨ i) f)) * K :=
        Nat.add_le_add h1 (h2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsub)))
    _ ≤ (Fintype.card (Col k) * N) * Bχ * K + (Fintype.card (Col k) * N) * (∑ b, (Fintype.card (Col k) * N) * errBound (Fintype.card (Col k) * N) Bχ ((ringSetting N q k hk Attr).fhat f b) + errBound (Fintype.card (Col k) * N) Bχ f) * K := by
        exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he₀))
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add hB hG)))

/-- **Correctness from bounds.** If the errors of `Enc` have coefficients at most `Bχ`, the key
coefficients at most `K`, `f(x) = 0`, and `4 · noiseBound + 2 < q`, decryption returns `M`. -/
theorem decrypt_correct_of_bounds (hN : 0 < N) (mpk : MPK (ringSetting N q k hk Attr))
    (x : Attr → Bool) (M : Bool) (r : EncCoins (ringSetting N q k hk Attr)) (f : Circuit Attr)
    (sk : SecretKey) (hsk : ValidKey mpk f sk) (hfx : f.evalBool x = false) (Bχ K : ℕ)
    (he' : cnorm r.e' ≤ Bχ) (he₀ : rnorm r.e₀ ≤ Bχ) (heΨ : ∀ i, rnorm (r.eΨ i) ≤ Bχ)
    (hej : ∀ j, rnorm (r.ej j) ≤ Bχ)
    (hk₁ : ∀ c d, cnorm (sk.k₁ c d) ≤ K) (hk₂ : ∀ c d, cnorm (sk.k₂ c d) ≤ K)
    (hq : 4 * noiseBound (N := N) hk Bχ K f + 2 < q) :
    decodeBit hN (decryptRaw mpk f sk (encrypt mpk x M r)) = M := by
  refine decrypt_correct hk hN mpk x M r f sk hsk hfx ?_
  have h := (zabs_coeffs_le_cnorm _ ⟨0, hN⟩).trans
    (cnorm_noise_le hk mpk x f sk r Bχ K he' he₀ heΨ hej hk₁ hk₂)
  have h' : |((noise mpk x f sk r).coeffs ⟨0, hN⟩).valMinAbs| ≤ (noiseBound (N := N) hk Bχ K f : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h
  have hq' : (4 * noiseBound (N := N) hk Bχ K f + 2 : ℤ) < q := by exact_mod_cast hq
  linarith

/-! ### Bounded error laws -/

omit [Fintype Attr] [NeZero q] in
/-- A ring element with coefficients from a law bounded by `B` has norm at most `B`. -/
theorem polyLaw_bounded {χ : PMF (ZMod q)} {B : ℕ} (hχ : ∀ e ∈ χ.support, zabs e ≤ B)
    {a : Negacyclic (ZMod q) N} (ha : a ∈ (polyLaw χ).support) : cnorm a ≤ B := by
  rw [polyLaw, PMF.mem_support_map_iff] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  rw [cnorm_le_iff]; intro j
  rcases sampleFun_support χ hc j with h | h
  · exact hχ _ h
  · simp only [h]
    exact (le_of_eq zabs_zero).trans (Nat.zero_le _)

omit [Fintype Attr] [NeZero q] in
/-- A row with entries from a law bounded by `B` has norm at most `B`. -/
theorem matLaw_bounded {d : PMF (Negacyclic (ZMod q) N)} {B : ℕ}
    (hd : ∀ a ∈ d.support, cnorm a ≤ B) {e : Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N)}
    (he : e ∈ (matLaw d).support) : rnorm e ≤ B := by
  rw [matLaw, PMF.mem_support_map_iff] at he
  obtain ⟨g, hg, rfl⟩ := he
  rw [rnorm_le_iff]; intro c
  rw [Matrix.of_apply]
  rcases sampleFun_support d hg (0, c) with h | h
  · exact hd _ h
  · rw [h]; exact (le_of_eq cnorm_zero).trans (Nat.zero_le _)

omit [Fintype Attr] [NeZero q] in
/-- Rows of independent bounded rows are bounded. -/
theorem sampleFun_matLaw_bounded {ι : Type} [Fintype ι] {d : PMF (Negacyclic (ZMod q) N)} {B : ℕ}
    (hd : ∀ a ∈ d.support, cnorm a ≤ B)
    {F : ι → Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N)}
    (hF : F ∈ (sampleFun (matLaw d)).support) (i : ι) : rnorm (F i) ≤ B := by
  rcases sampleFun_support _ hF i with h | h
  · exact matLaw_bounded hd h
  · rw [h]
    rw [rnorm_le_iff]; intro c
    exact (le_of_eq cnorm_zero).trans (Nat.zero_le _)

variable [DecidableEq Attr]

/-- **The errors of `Enc` are bounded** when the error law is bounded by `Bχ` (a truncated
discrete Gaussian, as the samplers of mxx record their cutoffs). -/
theorem encCoinsLaw_bounded {χ : PMF (ZMod q)} {Bχ : ℕ} (hχ : ∀ e ∈ χ.support, zabs e ≤ Bχ)
    {r : EncCoins (ringSetting N q k hk Attr)} (hr : r ∈ (encCoinsLaw hk Attr χ).support) :
    cnorm r.e' ≤ Bχ ∧ rnorm r.e₀ ≤ Bχ ∧ (∀ i, rnorm (r.eΨ i) ≤ Bχ) ∧ (∀ j, rnorm (r.ej j) ≤ Bχ) := by
  have hp : ∀ a ∈ (polyLaw (N := N) χ).support, cnorm a ≤ Bχ := fun a ha => polyLaw_bounded hχ ha
  simp only [encCoinsLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hr
  obtain ⟨s, -, a, -, eΨ, heΨ, e₀, he₀, ej, hej, e', he', rfl⟩ := hr
  exact ⟨hp _ he', matLaw_bounded hp he₀, sampleFun_matLaw_bounded hp heΨ,
    sampleFun_matLaw_bounded hp hej⟩

/-- **Correctness for every coin of `Enc`**: with an error law bounded by `Bχ`, a valid key with
coefficients at most `K`, `f(x) = 0` and `4 · noiseBound + 2 < q`, every ciphertext decrypts to
`M`. -/
theorem scheme_correct_bounded (hN : 0 < N) (mpk : MPK (ringSetting N q k hk Attr))
    (f : Circuit Attr) (sk : SecretKey) (hsk : ValidKey mpk f sk) (K : ℕ)
    (hk₁ : ∀ c d, cnorm (sk.k₁ c d) ≤ K) (hk₂ : ∀ c d, cnorm (sk.k₂ c d) ≤ K)
    {χ : PMF (ZMod q)} {Bχ : ℕ} (hχ : ∀ e ∈ χ.support, zabs e ≤ Bχ)
    (hq : 4 * noiseBound (N := N) hk Bχ K f + 2 < q) (x : Attr → Bool) (hfx : f.evalBool x = false)
    (M : Bool) (r : EncCoins (ringSetting N q k hk Attr)) (hr : r ∈ (encCoinsLaw hk Attr χ).support) :
    decodeBit hN (decryptRaw mpk f sk (encrypt mpk x M r)) = M := by
  obtain ⟨he', he₀, heΨ, hej⟩ := encCoinsLaw_bounded hk hχ hr
  exact decrypt_correct_of_bounds hk hN mpk x M r f sk hsk hfx Bχ K he' he₀ heΨ hej hk₁ hk₂ hq

end AdvancedEncryption.RingBTVW
