import PE.Impl.ExpLUT.Prog.KeyCandidate

/-! Load the master secret key codec into the actual KeyGen evaluator. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib Cslib.Probability Cslib.BitString

/-- The master secret key codec concatenates its public key and trapdoor. -/
theorem mskEnc_append (D : Dims) (msk : MSKt D) :
    (mskEnc D).enc msk = (mpkEnc D).enc msk.mpk ++
      (matE D (Wb D) (Fin D.K)).enc msk.T := rfl

/-- Read the saved input MSK0 into MPK17 and trapdoor16. -/
noncomputable def keyInputC (D : Dims) : Code :=
  .seq (.clr 6) <| .seq (bitsC 5 rB1 6) <|
  .seq (readFieldC 0 17 0 (codecSize (mpkEnc D)))
    (readFieldC 0 16 (codecSize (mpkEnc D)) (codecSize (matE D (Wb D) (Fin D.K))))

theorem wf_keyInputC (D : Dims) : (keyInputC D).WFc :=
  ⟨trivial, by repeat constructor, wf_readFieldC _ _ _ _, wf_readFieldC _ _ _ _⟩

theorem keyInputC_pred (D : Dims) : (keyInputC D).writes rCs = false := by
  simp [keyInputC, bitsC, Code.writes,
    readFieldC_frame 0 17 _ _ rCs (by decide) (by decide) (by decide),
    readFieldC_frame 0 16 _ _ rCs (by decide) (by decide) (by decide)]

theorem exec_keyInputC (D : Dims) (msk : MSKt D) (w : St)
    (hM : w 0 = (mskEnc D).enc msk) :
    let v := exec D.N D.K (keyInputC D) w
    v 17 = (mpkEnc D).enc msk.mpk ∧
    v 16 = (matE D (Wb D) (Fin D.K)).enc msk.T := by
  let u := Function.update (Function.update (Function.update w 6 []) 5 [true]) rB1 [false]
  have hu : u 0 = (mpkEnc D).enc msk.mpk ++ (matE D (Wb D) (Fin D.K)).enc msk.T := by
    simpa [u, mskEnc_append] using hM
  have hb : u rB1 = [false] := by simp [u]
  have hp := exec_readFieldC (N := D.N) (K := D.K) 0 17 (by decide) (by decide)
    [] ((mpkEnc D).enc msk.mpk) ((matE D (Wb D) (Fin D.K)).enc msk.T) u
    (by simpa using hu) hb
  have hlp : ((mpkEnc D).enc msk.mpk).length = codecSize (mpkEnc D) :=
    (mpkEnc D).length msk.mpk
  have hlt : ((matE D (Wb D) (Fin D.K)).enc msk.T).length =
      codecSize (matE D (Wb D) (Fin D.K)) := (matE D (Wb D) (Fin D.K)).length msk.T
  rw [hlp] at hp
  let v := exec D.N D.K (readFieldC 0 17 0 (codecSize (mpkEnc D))) u
  have hv (r : Fin 64) (h29 : r ≠ 29) (h30 : r ≠ 30) (h17 : r ≠ 17) : v r = u r :=
    exec_writes _ _ _ (readFieldC_frame _ _ _ _ r h29 h30 h17)
  have ht := exec_readFieldC (N := D.N) (K := D.K) 0 16 (by decide) (by decide)
    ((mpkEnc D).enc msk.mpk) ((matE D (Wb D) (Fin D.K)).enc msk.T) [] v
    (by rw [hv 0 (by decide) (by decide) (by decide), hu]; simp)
    ((hv rB1 (by decide) (by decide) (by decide)).trans hb)
  rw [hlp, hlt] at ht
  dsimp only
  rw [keyInputC, exec_seq, exec_seq,
    exec_bitsC _ _ _ (by decide) (by decide) (by decide) _ (by simp), exec_seq]
  constructor
  · rw [exec_writes _ _ _ (readFieldC_frame _ _ _ _ 17 (by decide) (by decide) (by decide))]
    exact hp
  · exact ht

/-- Initialize and evaluate directly from MSK0 and predicate3. -/
noncomputable def keyPrepareC (D : Dims) : Code := .seq (keyInputC D) (keyEvalPrepareC D)

theorem wf_keyPrepareC (D : Dims) : (keyPrepareC D).WFc :=
  ⟨wf_keyInputC D, wf_keyEvalPrepareC D⟩

theorem exec_keyPrepareC (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (msk : MSKt D) (C : List Bool) (w : St)
    (hM : w 0 = (mskEnc D).enc msk) (hp : w rCs = C) :
    let v := exec D.N D.K (keyPrepareC D) w
    v 14 = (mpkEnc D).enc msk.mpk ∧
    v 8 = encL D.N D.K (matL (keyPK (helperMap D) msk.mpk (bpOf (progOf C)))) ∧
    v 16 = (matE D (Wb D) (Fin D.K)).enc msk.T := by
  obtain ⟨hpub, htrap⟩ := exec_keyInputC D msk w hM
  exact exec_keyEvalPrepareC D hb hn msk C _ hpub htrap
    ((exec_writes _ _ _ (keyInputC_pred D)).trans hp)

/-- Exact law of preparation, followed by fresh coins and the actual initialized candidate tail. -/
theorem map_coins_keyCore (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (B r : ℕ) (hB : 2 ^ B ≤ D.q) (hBK : B ≤ D.K)
    (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q) (hcount : 2 * (D.K - B) < D.q)
    (msk : MSKt D) (C : List Bool) (w : St)
    (hM : w 0 = (mskEnc D).enc msk) (hp : w rCs = C) :
    (uniformList (nPI D * D.N * B)).map (fun cs ↦
      exec D.N D.K (candidateTryC D B r)
        (Function.update (exec D.N D.K (keyPrepareC D) w) rCoin cs) 19) =
    (keyGenLaw (S := setting D) (kbOf D B hB r).Big (kbOf D B hB r).Small
      (kbOf D B hB r).hBig gadDec (helperMap D) msk (bpOf (progOf C))).map (keyEnc D).enc := by
  obtain ⟨hpub, hA, htrap⟩ := exec_keyPrepareC D hb hn msk C w hM hp
  exact map_coins_candidateTryC D B r hB hBK hr hq hcount msk (bpOf (progOf C)) _
    hpub hA htrap

end AdvancedEncryption.ExpLUT.Prog
