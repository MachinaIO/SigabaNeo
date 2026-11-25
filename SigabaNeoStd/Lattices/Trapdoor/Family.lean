import SigabaNeoStd.Lattices.Trapdoor.Family.AlgPPT

/-!
# A trapdoor sampler for one parameter family

At `n = κ + 1`, `w = 8(κ + 1)`, a prime `q ∈ (2^w, 2^{w+1}]`, `m = 2n(w + 1)`, `k = m + 1` targets
and width `τ = 2^{κ+3}` (`Family/Params.lean`), the coset Gaussian preimage (`Trapdoor.ideal`)
can be sampled in polynomial time with an [MP12] gadget trapdoor:

* `genAlg` (`GenTrap`, input `(κ, q)`): `B = [Ā | G − Ā R]` for a uniform `Ā` and a short
  `R ∈ {−1, 0, 1}^{mb×mb}`, and the trapdoor `(Ā, R)`;
* `preAlg` (`SamplePre`, input `(κ, q)`, the trapdoor and `P`): one preimage per column of `P`.

Both are strict PPT in cslib-frontier's sense (`genAlg_isPPT`, `preAlg_isPPT`), and for all large
`κ` and every `P`, the pair `(B, K)` they produce is within the negligible `errAll κ` of
`Trapdoor.ideal P τ` (`trapdoor_sampling`). Hence `exists_sampler : Trapdoor.Exists n m k q τ`.

Only this family is proved; other parameters are later work.
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

section
variable (κ : ℕ)

/-- The ideal joint law is `Trapdoor.ideal`. -/
theorem idealJ_eq (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    idealJ κ P = Trapdoor.ideal P (τ κ) (τ_pos κ) := rfl

/-- The trapdoor holder: `GenTrap (κ, q)`, then `SamplePre` on `P`. The output is `B` and the
columns of `K`. -/
noncomputable def trapPipe (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    ProbComp (List ℕ × Option (List (List ℤ))) := do
  let g ← genAlg (κ, q κ)
  let K ← preAlg ((κ, q κ), g.2, matVals P)
  pure (g.1, some K)

/-- `(B, K)` as lists. -/
noncomputable def encBK (x : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) × Option (Matrix (Fin (m κ)) (Fin (k κ)) ℤ)) :
    List ℕ × Option (List (List ℤ)) := (matVals x.1, x.2.map (colsList κ))

theorem eval_trapPipe (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    ProbComp.eval (trapPipe κ P) =
      ((DT κ).bind fun p => (colsReal κ p.1 (RofCodes κ p.2) P).map
        (Bmat κ p.1 (RofCodes κ p.2), ·)).map (encBK κ) := by
  unfold trapPipe
  rw [ProbComp.eval_bind, eval_genAlg, PMF.bind_map, PMF.map_bind]
  congr 1; funext p
  simp only [Function.comp_apply, ProbComp.eval_bind, ProbComp.eval_pure]
  have h := eval_preAlg κ p.1 p.2 P
  calc (ProbComp.eval (preAlg ((κ, q κ), (encMat κ p.1, codesL κ p.2), matVals P))).bind
        (fun K => PMF.pure (matVals (Bmat κ p.1 (RofCodes κ p.2)), some K))
      = ((ProbComp.eval (preAlg ((κ, q κ), (encMat κ p.1, codesL κ p.2), matVals P))).map some).map
          (fun o => (matVals (Bmat κ p.1 (RofCodes κ p.2)), o)) := by
        rw [PMF.map_comp]; rfl
    _ = _ := by rw [h, PMF.map_comp, PMF.map_comp]; rfl

theorem εA_le : εA κ ≤ ((m κ ^ 2 : ℕ) : ℝ) * (1 / 2 ^ κ) := by
  have hq : (q κ : ℝ) ≤ 2 ^ (w κ + 1) := by exact_mod_cast q_le_two_pow κ
  have hnm : n κ * mb κ ≤ m κ ^ 2 := by
    have h1 : n κ ≤ m κ := by unfold m; nlinarith
    have h2 : mb κ ≤ m κ := by rw [m_eq_mb]; omega
    calc n κ * mb κ ≤ m κ * m κ := Nat.mul_le_mul h1 h2
      _ = m κ ^ 2 := (sq _).symm
  have hd : (q κ : ℝ) / 2 ^ wdA κ ≤ 1 / 2 ^ κ := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, wdA, pow_add]
    exact mul_le_mul_of_nonneg_right hq (by positivity)
  unfold εA
  exact mul_le_mul (by exact_mod_cast hnm) hd (by positivity) (by positivity)

/-- The total error: `errTd κ + m² / 2^κ`. -/
noncomputable def errAll : ℝ≥0 := errTd κ + ((m κ ^ 2 : ℕ) : ℝ≥0) * ((1 : ℝ≥0) / 2 ^ κ)

end

theorem polyM2 : PolynomiallyBounded fun κ => m κ ^ 2 := by
  rw [polynomiallyBounded_iff_le]
  refine ⟨19 ^ 2, 4, fun κ => ?_⟩
  have : m κ ≤ 19 * (κ + 1) ^ 2 := by unfold m n w; nlinarith
  calc m κ ^ 2 ≤ (19 * (κ + 1) ^ 2) ^ 2 := by gcongr
    _ = 19 ^ 2 * (κ + 1) ^ 4 := by ring

theorem errAll_negligible : Negligible errAll :=
  errTd_negligible.add (negligible_one_div_two_pow.polynomiallyBounded_mul polyM2)

/-- **The trapdoor sampler.** `GenTrap` and `SamplePre` are strict PPT, and for all large `κ` and
every `P`, the `(B, K)` they produce (as lists) is within the negligible `errAll κ` of a uniform
`B` with the coset Gaussian preimage of `P` (`idealJ`, which is `Trapdoor.ideal`). -/
theorem trapdoor_sampling :
    IsPPTOn encPub (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) genAlg ∧
    IsPPTOn encInp (encList (encList encIntBin)) preAlg ∧
    Negligible errAll ∧
    ∀ᶠ κ in Filter.atTop, ∀ P, CloseTo (ProbComp.eval (trapPipe κ P))
      ((idealJ κ P).map (encBK κ)) (errAll κ) := by
  refine ⟨genAlg_isPPT, preAlg_isPPT, errAll_negligible, ?_⟩
  filter_upwards [joint_negligible] with κ hκ P
  rw [eval_trapPipe]
  refine CloseTo.map ?_ _
  have h1 : CloseTo ((DT κ).bind fun p => (colsReal κ p.1 (RofCodes κ p.2) P).map
      (Bmat κ p.1 (RofCodes κ p.2), ·)) (realJ κ P) (ENNReal.ofReal (εA κ)) :=
    (closeTo_DT κ).bind_left _
  refine (h1.trans (hκ P)).mono ?_
  unfold errAll
  rw [ENNReal.coe_add, add_comm]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have := εA_le κ
  push_cast at this ⊢
  linarith

/-- The sampler of the family: `genAlg` and `preAlg`, with the trapdoor `(Ā, R)` as two lists. -/
noncomputable def sampler : Trapdoor.Sampler n m k q τ τ_pos where
  T := List ℕ × List ℕ
  encT := encPair (encList encNat) (encList encNat)
  gen := genAlg
  pre := preAlg
  gen_isPPT := trapdoor_sampling.1
  pre_isPPT := trapdoor_sampling.2.1
  err := errAll
  err_negligible := trapdoor_sampling.2.2.1
  close := trapdoor_sampling.2.2.2

/-- **A trapdoor sampler exists** for `n = κ + 1`, `w = 8(κ + 1)`, the prime `q ∈ (2^w, 2^{w+1}]`,
`m = 2n(w + 1)`, `k = m + 1` targets and width `τ = 2^{κ+3}`. -/
theorem exists_sampler : Trapdoor.Exists n m k q τ τ_pos := ⟨sampler⟩

end SigabaNeo.Lattices.Trapdoor.Family
