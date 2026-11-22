import PE.Impl.DualUse.Impl

/-!
# Correctness of the dual-use implementation for date windows

The scheme's bound of `correct_of_scheme` from the conditions on the parameters
(`scheme_bound`): the gadget decomposition inverts the gadget, the big box covers the small box
shifted by the real trapdoor, the coins of `Enc`, the small box and the decompositions are short,
the noise bound of every window predicate stays below `q / 4`, and an inner box of
the big box, whose shift by the trapdoor stays in the small box, leaves an abort probability at
most `2^{-κ}`. Then the implementation is correct (`correct`).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped ENNReal

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)
variable {M : SEMachines hk c}

/-- A gate list whose last gate is `false` on `x` gives a predicate that is `false` on `x`. -/
theorem evalBool_predC {x : Date} {C : List Bool} (h : evalGates (encDate x, parse C) = false) :
    SLP.evalBool (bitsOf x) (predC C).1 (predC C).2 = false := by
  have hne : parse C ≠ [] := by
    intro he
    rw [he] at h
    exact absurd h (by simp [evalGates])
  rw [predC, ← evalGates_predOf (bitsOf x) _ hne, ofFn_bitsOf]
  exact h

/-- The trapdoor of `msk` is a trapdoor of the key row. -/
theorem realTrap_spec (mpk : PK hk c) (Tm : Matrix (TrapCol k) (Col k) (Rg N K))
    (hT : mpk.B₁ * Tm = (Sdw (N := N) hk).Γ₁.G) (f : SLP (Fin 10) × Wire (Fin 10))
    (z : Col k → Rg N K) :
    shortMap mpk (realTrap (S := Sdw (N := N) hk) Tm (keyMatrix mpk f) z) +
      gadgetMap (S := Sdw (N := N) hk) z = (keyMatrix mpk f *ᵥ z) 0 := by
  rw [shortMap_realTrap mpk Tm hT, gadgetMap_eq, Matrix.sub_mulVec]
  simp

/-- A law on `Bool` puts `1 − p false` on `true`. -/
theorem PMF.apply_true_eq (p : PMF Bool) : p true = 1 - p false := by
  have h := p.tsum_coe
  rw [tsum_bool] at h
  exact ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top _ _) (by rw [add_comm]; exact h)

/-- A law whose every branch gives `a` with probability at least `1 − ε`. -/
theorem PMF.bind_apply_ge {α β : Type} (μ : PMF α) (F : α → PMF β) (a : β) (ε : ℝ≥0∞)
    (h : ∀ v ∈ μ.support, 1 - ε ≤ F v a) : 1 - ε ≤ (μ.bind F) a := by
  rw [PMF.bind_apply]
  calc 1 - ε = ∑' v, μ v * (1 - ε) := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
    _ ≤ ∑' v, μ v * F v a := tsum_le_tsum fun v => by
        by_cases hv : v ∈ μ.support
        · gcongr; exact h v hv
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hv]

/-- **The scheme's bound** from the conditions on the parameters. -/
theorem scheme_bound (hd : 0 < c.d)
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (Bχ Kb : ℕ) (Inner : Finset (KeyShort (Fin c.d) (TrapCol k) (Rg N K))) (hIn : Inner ⊆ c.Big)
    (hcov : ∀ v ∈ (setupM hk c).support, ∀ w : Window,
      ∀ y ∈ c.Small, ∀ u, y + realTrap (S := Sdw (N := N) hk) (trapMat v.2.2.1 v.2.2.2)
        (keyMatrix v.1 (predC (winWord w))) (c.dec u) ∈ c.Big)
    (hInner : ∀ v ∈ (setupM hk c).support, ∀ w : Window,
      ∀ p ∈ Inner, ∀ u, p - realTrap (S := Sdw (N := N) hk) (trapMat v.2.2.1 v.2.2.2)
        (keyMatrix v.1 (predC (winWord w))) (c.dec u) ∈ c.Small)
    (habort : ((c.Big.card - Inner.card : ℕ) : ℝ≥0∞) / c.Big.card ≤
      ((2 : ℝ≥0∞) ^ params.corrBits)⁻¹)
    (hSmall : ∀ v ∈ c.Small, (∀ i, cnorm (v.1 i) ≤ Kb) ∧ ∀ i, cnorm (v.2 i) ≤ Kb)
    (hdecK : ∀ u i, cnorm (c.dec u i) ≤ Kb)
    (hr : ∀ r ∈ (coinsM hk c).support, cnorm r.e' ≤ Bχ ∧ rnorm r.e₀ ≤ Bχ ∧ rnorm r.e₁ ≤ Bχ ∧
      (∀ i a b, cnorm (r.Rm i a b) ≤ 1) ∧ ∀ j, rnorm (r.ej j) ≤ Bχ)
    (hq : ∀ w : Window, 4 * noiseBound (Wd := Fin c.d) (Wt := TrapCol k) (N := N) hk Bχ Kb
      (predC (winWord w)) + 2 < 2 ^ K)
    (x : Date) (w : Window) (hev : evalGates (encDate x, parse (winWord w)) = false) (b : Bool) :
    1 - ((2 : ℝ) ^ params.corrBits)⁻¹ ≤
      (((setupM hk c).bind fun v => (keyM hk c v.2 (winWord w)).bind fun sk =>
        (encM hk c v.1 x b).map fun ct => decM hk c sk (winWord w) ct) [b]).toReal := by
  set C := winWord w
  set ε : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ params.corrBits)⁻¹
  have hfx := evalBool_predC hev
  have key : 1 - ε ≤ ((setupM hk c).bind fun v => (keyM hk c v.2 C).bind fun sk =>
      (encM hk c v.1 x b).map fun ct => decM hk c sk C ct) [b] := by
    refine PMF.bind_apply_ge _ _ _ _ fun v hv => ?_
    obtain ⟨hT, hm⟩ := msk_trapdoor _ v hv
    set T := realTrap (S := Sdw (N := N) hk) (trapMat v.2.2.1 v.2.2.2) (keyMatrix v.1 (predC C))
    have hTv : ∀ z, shortMap v.1 (T z) + gadgetMap (S := Sdw (N := N) hk) z =
        (keyMatrix v.1 (predC C) *ᵥ z) 0 := realTrap_spec hk c v.1 _ hT _
    have hfail := decrypt_fail_le hk c.hN (by simpa using hd) v.1 (bitsOf x) b (predC C) hfx
      c.Big c.Small c.hBig c.dec hdec T hTv (hcov v hv w) (coinsM hk c) Bχ Kb hSmall hdecK hr
      (hq w)
    have hab := boxSample_none_le c.Big c.hBig c.Small (shortMap v.1) c.dec T v.1.p Inner hIn
      (hInner v hv w)
    -- the law of the output is the image of the law of success
    have hlaw : ((keyM hk c v.2 C).bind fun sk => (encM hk c v.1 x b).map fun ct =>
        decM hk c sk C ct) = ((keyLaw c.Big c.Small c.hBig c.dec v.1 T).bind fun o =>
          (coinsM hk c).map fun r => decide (decodeBit c.hN (decryptRaw v.1 (predC C)
            (keyOfOutput o) (encrypt v.1 (bitsOf x) b r)) = b)).map
          fun β => if β then [b] else [!b] := by
      rw [keyM_eq hk c _ _ ⟨w, rfl⟩, hm, PMF.bind_map, PMF.map_bind]
      refine congrArg (PMF.bind _) (funext fun o => ?_)
      simp only [Function.comp_apply, encM, PMF.map_comp]
      refine congrArg (fun g => PMF.map g (coinsM hk c)) (funext fun r => ?_)
      simp only [Function.comp_apply, decM]
      cases decodeBit c.hN (decryptRaw v.1 (predC C) (keyOfOutput o)
        (encrypt v.1 (bitsOf x) b r)) <;> cases b <;> rfl
    rw [hlaw, PMF.map_apply, tsum_bool]
    rw [PMF.apply_true_eq]
    simp only [Bool.false_eq_true, ↓reduceIte, List.cons.injEq, and_true,
      show (b = !b) = False from by cases b <;> simp, zero_add]
    refine tsub_le_tsub_left (hfail.trans (le_trans ?_ habort)) 1
    exact hab
  have hle : 1 - ε ≤ 1 := tsub_le_self
  have hε : ε ≤ 1 := ENNReal.inv_le_one.mpr (one_le_pow₀ one_le_two)
  have := ENNReal.toReal_mono (PMF.apply_ne_top _ _) key
  rw [ENNReal.toReal_sub_of_le hε ENNReal.one_ne_top, ENNReal.toReal_one] at this
  simpa [ε, ENNReal.toReal_inv, ENNReal.toReal_pow] using this

/-- **Correctness** of the implementation under the conditions on the parameters. -/
theorem correct (hd : 0 < c.d)
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (Bχ Kb : ℕ) (Inner : Finset (KeyShort (Fin c.d) (TrapCol k) (Rg N K))) (hIn : Inner ⊆ c.Big)
    (hcov : ∀ v ∈ (setupM hk c).support, ∀ w : Window,
      ∀ y ∈ c.Small, ∀ u, y + realTrap (S := Sdw (N := N) hk) (trapMat v.2.2.1 v.2.2.2)
        (keyMatrix v.1 (predC (winWord w))) (c.dec u) ∈ c.Big)
    (hInner : ∀ v ∈ (setupM hk c).support, ∀ w : Window,
      ∀ p ∈ Inner, ∀ u, p - realTrap (S := Sdw (N := N) hk) (trapMat v.2.2.1 v.2.2.2)
        (keyMatrix v.1 (predC (winWord w))) (c.dec u) ∈ c.Small)
    (habort : ((c.Big.card - Inner.card : ℕ) : ℝ≥0∞) / c.Big.card ≤
      ((2 : ℝ≥0∞) ^ params.corrBits)⁻¹)
    (hSmall : ∀ v ∈ c.Small, (∀ i, cnorm (v.1 i) ≤ Kb) ∧ ∀ i, cnorm (v.2 i) ≤ Kb)
    (hdecK : ∀ u i, cnorm (c.dec u i) ≤ Kb)
    (hr : ∀ r ∈ (coinsM hk c).support, cnorm r.e' ≤ Bχ ∧ rnorm r.e₀ ≤ Bχ ∧ rnorm r.e₁ ≤ Bχ ∧
      (∀ i a b, cnorm (r.Rm i a b) ≤ 1) ∧ ∀ j, rnorm (r.ej j) ≤ Bχ)
    (hq : ∀ w : Window, 4 * noiseBound (Wd := Fin c.d) (Wt := TrapCol k) (N := N) hk Bχ Kb
      (predC (winWord w)) + 2 < 2 ^ K) :
    Correct dateUniverse params (impl hk c M) :=
  correct_of_scheme hk c M fun x w _ hev b => scheme_bound hk c hd hdec Bχ Kb Inner hIn hcov hInner
    habort hSmall hdecK hr hq x w hev b

end AdvancedEncryption.DualUse
