import PE.Impl.DualUse.Prog.Setup3

/-!
# The setup of the reduction of the ideal side as a tape program

`setupIP Pχ : XProg 7` (layout of `Setup5`): on the instance word `w` and `encAttr x`, appends the
word of `σ ← setupI x` (`secIEnc`): `encAttr x`, fair bits for `B₀`, `w`, `p`, the coins of `Enc`
(`coinsP'`: as `restP` with the flooding coefficients of the encodings before `e'`), and the
simulator's uniform ciphertext (fair bits, field by field). χ coefficients as in `Setup3`.

**`law_setupIP`**, **`wf_setupIP`**.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg Matrix
  AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (Pχ : XProg 7)

/-- The coins of `Enc`. -/
def encCoinsP : XProg 7 :=
  seq (coinsF (N * K)) (seq (repF ((Enum.list (α := Fin c.d)).length * N) Pχ)
    (seq (seq (repF N Pχ) (seq (repF ((Enum.list (α := RingBTVW.Col k)).length * N) Pχ)
        (repF ((Enum.list (α := RingBTVW.Col k)).length * N) Pχ)))
      (seq (repF (nR hk c) (entB N K)) (seq (repF (nE (N := N) hk) (entF K c.w)) (repF N Pχ)))))

theorem law_encCoinsP (hχ : AppendLaw Pχ 0 P3 (μχ c)) (hN : 0 < N) (hK : 0 < K) [NeZero c.d] :
    AppendLaw (encCoinsP hk c Pχ) 0 P5 ((lawCoinsC hk c).map (coinsEnc hk c).enc) := by
  rw [coinsLaw_enc hk c hN hK]
  simp only [catPow_mul]
  exact AppendLaw.seq (law_coinsF5 _) (AppendLaw.seq (law_repF hχ _)
    (AppendLaw.seq (AppendLaw.seq (law_repF hχ _) (AppendLaw.seq (law_repF hχ _) (law_repF hχ _)
      P5_upd0) P5_upd0)
      (AppendLaw.seq (law_repF law_entB _) (AppendLaw.seq (law_repF (law_entF _) _)
        (law_repF hχ _) P5_upd0) P5_upd0) P5_upd0) P5_upd0) P5_upd0

/-- The uniform ciphertext. -/
def ctP : XProg 7 :=
  seq (coinsF (nPsi (N := N) hk)) (seq (coinsF (nC0 (N := N) (K := K) c))
    (seq (coinsF (nC1 (N := N) (K := K) (k := k))) (seq (coinsF (nCj (N := N) hk)) (coinsF (N * K)))))

theorem law_ctP : AppendLaw (ctP hk c) 0 P5 ((ctUc hk c).map (ctEnc hk c).enc) := by
  rw [ctLaw_enc]
  exact AppendLaw.seq (law_coinsF5 _) (AppendLaw.seq (law_coinsF5 _) (AppendLaw.seq (law_coinsF5 _)
    (AppendLaw.seq (law_coinsF5 _) (law_coinsF5 _) P5_upd0) P5_upd0) P5_upd0) P5_upd0

/-- The random part of the secret of the ideal side. -/
def tailIP : XProg 7 :=
  seq (coinsF ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K))))
    (seq (coinsF (nW hk c)) (seq (coinsF (N * K)) (seq (encCoinsP hk c Pχ) (ctP hk c))))

/-- **The setup of the ideal side.** -/
def setupIP : XProg 7 := seq (appendTapeP 0 1 3 4) (tailIP hk c Pχ)

/-- **The law of the setup of the ideal side**: on the instance word of `ab` and the date `x`,
the word of the packed secret `(ab, σ)`, `σ ← setupI x`. -/
theorem law_setupIP (hχ : AppendLaw Pχ 0 P3 (μχ c)) [NeZero c.d] (hN : 0 < N) (hK : 0 < K)
    (ab : Inst3T N K k) (x : PUniv.Attr) :
    (setupIP hk c Pχ).law (ioS (R := 5) ((inst3Enc (N := N) (K := K) (k := k)).enc ab)
      (encAttr x) []) =
      (setupI hk c x).map fun σ =>
        ioS (R := 5) (((inst3Enc (N := N) (K := K) (k := k)).prod (secIEnc hk c)).enc (ab, σ))
          [] [] := by
  set w := (inst3Enc (N := N) (K := K) (k := k)).enc ab
  rw [setupIP, law_seq, law_appendTapeP (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) _ rfl rfl, PMF.pure_bind]
  have hP : P5 (Function.update (Function.update (ioS (R := 5) w (encAttr x) []) 0
      (ioS (R := 5) w (encAttr x) [] 0 ++ ioS (R := 5) w (encAttr x) [] 1)) 1 []) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> rfl
  have ht : AppendLaw (tailIP hk c Pχ) 0 P5 _ :=
    AppendLaw.seq (law_coinsF5 _) (AppendLaw.seq (law_coinsF5 _) (AppendLaw.seq (law_coinsF5 _)
      (AppendLaw.seq (law_encCoinsP hk c Pχ hχ hN hK) (law_ctP hk c) P5_upd0) P5_upd0)
      P5_upd0) P5_upd0
  rw [ht _ hP]
  have hR : (setupI hk c x).map (fun σ => ioS (R := 5)
      (((inst3Enc (N := N) (K := K) (k := k)).prod (secIEnc hk c)).enc (ab, σ)) [] []) =
      ((setupI hk c x).map (secIEnc hk c).enc).map (fun v => ioS (R := 5) (w ++ v) [] []) := by
    exact (PMF.map_comp (fun σ : SecI hk c => (secIEnc hk c).enc σ) (setupI hk c x)
      (fun v => ioS (R := 5) (w ++ v) [] [])).symm
  rw [hR, setupI_enc hk c x, cat_pure_left, PMF.map_comp]
  congr 1
  funext u
  funext j
  fin_cases j <;> simp [ioS, List.append_assoc]

/-- **`setupIP` is well formed**, for a well-formed sampler leaving tape `6` alone. -/
theorem wf_setupIP (hwf : Pχ.WF) (h6 : Pχ.Preserves 6) : (setupIP hk c Pχ).WF :=
  ⟨wf_appendTapeP (by decide) (by decide), wf_coinsF _, wf_coinsF _, wf_coinsF _,
    ⟨wf_coinsF _, wf_repF hwf h6 _, ⟨wf_repF hwf h6 _, wf_repF hwf h6 _, wf_repF hwf h6 _⟩,
      wf_repF (body := entB N K) ⟨wf_coinAp _ _, wf_zerosF _⟩
        ⟨preserves_coinAp (by decide) (by decide), preserves_zerosF _ (by decide)⟩ _,
      wf_repF (body := entF K c.w) ⟨wf_coinsF _, wf_zerosF _⟩
        ⟨preserves_coinsF _ (by decide), preserves_zerosF _ (by decide)⟩ _,
      wf_repF hwf h6 _⟩,
    wf_coinsF _, wf_coinsF _, wf_coinsF _, wf_coinsF _, wf_coinsF _⟩

end AdvancedEncryption.DualUse.Prog
