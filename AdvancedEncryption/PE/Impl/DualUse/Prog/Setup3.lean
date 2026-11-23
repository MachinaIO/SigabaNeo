import PE.Impl.DualUse.Prog.Setup5

/-!
# The setup of the reduction of hybrid 3 as a tape program

`setup3P Pχ : XProg 7` (layout of `Setup5`): on the instance word `w` and `encAttr x`, appends the
word of `σ ← setup3 x` (`sec3Enc`): `encAttr x`, fair bits for `B₀`, `w`, `p`, then the coins
`rest` (`restP`: `N · K` fair bits for `s`, χ coefficients for `e₀`, for `e₁ = [σ | ea | ez]`,
binary `Rᵢ`, χ coefficients for `e'`), then the flooding coefficients.

The error law `χc` of the configuration is abstract (`Conf.hχ` only says it is *some* image of
fair bits), so the χ coefficient sampler is a parameter: any `Pχ : XProg 7` appending the word
`zmodEnc K` of a χ sample to tape `0` with its scratch among the tapes `2, 3, 4`
(`AppendLaw Pχ 0 P3 (μχ c)`), leaving tape `6` alone.

**`law_setup3P`**, **`wf_setup3P`**.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg Matrix
  AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (Pχ : XProg 7)

/-- The coins `rest`. -/
def restP : XProg 7 :=
  seq (coinsF (N * K)) (seq (repF ((Enum.list (α := Fin c.d)).length * N) Pχ)
    (seq (seq (repF N Pχ) (seq (repF ((Enum.list (α := RingBTVW.Col k)).length * N) Pχ)
        (repF ((Enum.list (α := RingBTVW.Col k)).length * N) Pχ)))
      (seq (repF (nR hk c) (entB N K)) (repF N Pχ))))

theorem law_restP (hχ : AppendLaw Pχ 0 P3 (μχ c)) (hN : 0 < N) (hK : 0 < K) [NeZero c.d] :
    AppendLaw (restP hk c Pχ) 0 P5 ((lawRestC hk c).map (restEnc c).enc) := by
  rw [restLaw_enc hk c hN hK]
  simp only [catPow_mul]
  exact AppendLaw.seq (law_coinsF5 _) (AppendLaw.seq (law_repF hχ _)
    (AppendLaw.seq (AppendLaw.seq (law_repF hχ _) (AppendLaw.seq (law_repF hχ _) (law_repF hχ _)
      P5_upd0) P5_upd0)
      (AppendLaw.seq (law_repF law_entB _) (law_repF hχ _) P5_upd0) P5_upd0) P5_upd0) P5_upd0

/-- The random part of the secret of hybrid 3. -/
def tail3P : XProg 7 :=
  seq (coinsF ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K))))
    (seq (coinsF (nW hk c)) (seq (coinsF (N * K)) (seq (restP hk c Pχ) (repF (nE (N := N) hk) (entF K c.w)))))

/-- **The setup of hybrid 3.** -/
def setup3P : XProg 7 := seq (appendTapeP 0 1 3 4) (tail3P hk c Pχ)

/-- **The law of the setup of hybrid 3**: on the instance word of `ab` and the date `x`, the word
of the packed secret `(ab, σ)`, `σ ← setup3 x`. -/
theorem law_setup3P (hχ : AppendLaw Pχ 0 P3 (μχ c)) [NeZero c.d] (hN : 0 < N) (hK : 0 < K)
    (ab : Inst3T N K k) (x : PUniv.Attr) :
    (setup3P hk c Pχ).law (ioS (R := 5) ((inst3Enc (N := N) (K := K) (k := k)).enc ab)
      (encAttr x) []) =
      (setup3 hk c x).map fun σ =>
        ioS (R := 5) (((inst3Enc (N := N) (K := K) (k := k)).prod (sec3Enc hk c)).enc (ab, σ))
          [] [] := by
  set w := (inst3Enc (N := N) (K := K) (k := k)).enc ab
  rw [setup3P, law_seq, law_appendTapeP (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) _ rfl rfl, PMF.pure_bind]
  have hP : P5 (Function.update (Function.update (ioS (R := 5) w (encAttr x) []) 0
      (ioS (R := 5) w (encAttr x) [] 0 ++ ioS (R := 5) w (encAttr x) [] 1)) 1 []) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> rfl
  have ht : AppendLaw (tail3P hk c Pχ) 0 P5 _ :=
    AppendLaw.seq (law_coinsF5 _) (AppendLaw.seq (law_coinsF5 _) (AppendLaw.seq (law_coinsF5 _)
      (AppendLaw.seq (law_restP hk c Pχ hχ hN hK) (law_repF (law_entF _) _) P5_upd0) P5_upd0)
      P5_upd0) P5_upd0
  rw [ht _ hP]
  have hR : (setup3 hk c x).map (fun σ => ioS (R := 5)
      (((inst3Enc (N := N) (K := K) (k := k)).prod (sec3Enc hk c)).enc (ab, σ)) [] []) =
      ((setup3 hk c x).map (sec3Enc hk c).enc).map (fun v => ioS (R := 5) (w ++ v) [] []) := by
    exact (PMF.map_comp (fun σ : Sec3 hk c => (sec3Enc hk c).enc σ) (setup3 hk c x)
      (fun v => ioS (R := 5) (w ++ v) [] [])).symm
  rw [hR, setup3_enc hk c x, cat_pure_left, PMF.map_comp]
  congr 1
  funext u
  funext j
  fin_cases j <;> simp [ioS, List.append_assoc]

/-- **`setup3P` is well formed**, for a well-formed sampler leaving tape `6` alone. -/
theorem wf_setup3P (hwf : Pχ.WF) (h6 : Pχ.Preserves 6) : (setup3P hk c Pχ).WF :=
  ⟨wf_appendTapeP (by decide) (by decide), wf_coinsF _, wf_coinsF _, wf_coinsF _,
    ⟨wf_coinsF _, wf_repF hwf h6 _, ⟨wf_repF hwf h6 _, wf_repF hwf h6 _, wf_repF hwf h6 _⟩,
      wf_repF (body := entB N K) ⟨wf_coinAp _ _, wf_zerosF _⟩
        ⟨preserves_coinAp (by decide) (by decide), preserves_zerosF _ (by decide)⟩ _,
      wf_repF hwf h6 _⟩,
    wf_repF (body := entF K c.w) ⟨wf_coinsF _, wf_zerosF _⟩
      ⟨preserves_coinsF _ (by decide), preserves_zerosF _ (by decide)⟩ _⟩

end AdvancedEncryption.DualUse.Prog
