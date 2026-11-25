import PE.Impl.ExpLUT.Prog.RedSetup
/-!
# The complete random tape for encryption

The queue is in `EncCoins` field order: secret, base errors, helper errors, four flooding
blocks, and message error. `encCoinsP` samples this queue using seven tapes; the law theorem
connects the actual sampler to `encCoinsLaw`, including the independence of all fields.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg
  Cslib Cslib.Probability AdvancedEncryption.RingBTVW.Prog

variable (D : Dims)

/-- Base-law ring elements before the flooding blocks: secret, `e_b`, and `e_h`. -/
abbrev nEncSmall : ℕ := 1 + ((Enum.list (α := BCol (Wb D) D.K)).length +
  (Enum.list (α := Jh D)).length * (Enum.list (α := Col D.K)).length)

/-- The coin queue consumed by the deterministic encryption core. -/
noncomputable def encCoinWord (r : EncCoins (setting D) (Wb D) (Jh D) Pos) : List Bool :=
  (rEnc D).enc r.s ++ ((vecE D (BCol (Wb D) D.K)).enc r.eb ++
    ((matE D (Jh D) (Col D.K)).enc r.eh ++
      ((floodEnc D).enc (r.eaut, r.ein, r.edin, r.e0) ++ (rEnc D).enc r.em)))

/-- Independent encoded blocks, with the same base law for secret and base errors. -/
noncomputable def encCoinWordLaw (χ χfl : PMF (Rg D)) : PMF (List Bool) :=
  cat (catPow (χ.map (rEnc D).enc) (nEncSmall D))
    (cat (catPow (χfl.map (rEnc D).enc) (nFl D)) (χ.map (rEnc D).enc))

/-- Encoding the scheme's independent coins gives exactly the three sampler blocks. -/
theorem encCoinsLaw_word (χ : PMF (Rg D)) {e : ℕ} (he : e < D.K) :
    (encCoinsLaw (setting D) (Wb D) (Jh D) Pos χ χ (floodR D e)).map (encCoinWord D) =
      encCoinWordLaw D χ (floodR D e) := by
  have h1 : (encCoinsLaw (setting D) (Wb D) (Jh D) Pos χ χ (floodR D e)).map (encCoinWord D) =
      cat (χ.map (rEnc D).enc)
        (cat ((iidLaw χ (BCol (Wb D) D.K)).map (vecE D (BCol (Wb D) D.K)).enc)
          (cat ((iidFam χ (Jh D) (Col D.K)).map (matE D (Jh D) (Col D.K)).enc)
            (cat ((floodLaw (setting D) Pos (floodR D e)).map (floodEnc D).enc)
              (χ.map (rEnc D).enc)))) := by
    unfold encCoinWord
    dsimp only [encCoinsLaw, floodLaw, setting, canonSetting]
    simp only [cat, PMF.map_bind, PMF.bind_map,
      PMF.map_comp, PMF.bind_bind, Function.comp_def]
  rw [h1, lawVec, lawMat, floodLaw_enc he, encCoinWordLaw, nEncSmall]
  rw [← cat_assoc, ← cat_assoc]
  have hone : χ.map (rEnc D).enc = catPow (χ.map (rEnc D).enc) 1 :=
    (catPow_one _).symm
  conv_lhs => arg 1; arg 1; arg 1; rw [hone]
  rw [← catPow_add, ← catPow_add]
  congr 2
  omega

/-- Sample `n` independent centered-binomial ring words using coefficient loops. -/
def cbdManyP (η L n : ℕ) : XProg 7 := repF (n * D.N) (cbdPM η L D.K)

theorem law_cbdManyP {η L : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) (n : ℕ) :
    AppendLaw (cbdManyP D η L n) 0 P5
      (catPow ((cbdR D η).map (rEnc D).enc) n) := by
  rw [cbdR, ringLawD_enc, catPow_mul]
  exact law_repF (law_cbdPM η L D.K D.hK hL hLK hη) (n * D.N)

/-- Sample `n` independent flooding ring words using coefficient loops. -/
def floodManyP (e n : ℕ) : XProg 7 := repF (n * D.N) (entF D.K e)

theorem law_floodManyP {e : ℕ} (he : e < D.K) (n : ℕ) :
    AppendLaw (floodManyP D e n) 0 P5
      (catPow ((floodR D e).map (rEnc D).enc) n) := by
  rw [floodR_enc he, catPow_mul]
  exact law_repF (law_entF e) (n * D.N)

/-- The complete encryption sampler, preserving tape 1 and clearing scratch tapes 2–6. -/
noncomputable def encCoinsP (η L e : ℕ) : XProg 7 :=
  seq (cbdManyP D η L (nEncSmall D))
    (seq (floodManyP D e (nFl D)) (cbdRP D η L))

theorem appendLaw_encCoinsP {η L e : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) (he : e < D.K) :
    AppendLaw (encCoinsP D η L e) 0 P5
      ((encCoinsLaw (setting D) (Wb D) (Jh D) Pos
        (cbdR D η) (cbdR D η) (floodR D e)).map (encCoinWord D)) := by
  rw [encCoinsLaw_word D _ he]
  exact (law_cbdManyP D hL hLK hη (nEncSmall D)).seq
    ((law_floodManyP D he (nFl D)).seq (law_cbdRP D hL hLK hη) P5_upd0) P5_upd0


/-- The one's-complement leaf choice preserves the original sampler's control invariant. -/
theorem wf_chainPM (K L η : ℕ) : ∀ f j, (chainPM K L η f j).WF
  | 0, _ => wf_leafP K L _
  | f + 1, j => ⟨wf_leafP K L _, trivial, wf_chainPM K L η f (j + 1)⟩

theorem preserves_chainPM (K L η : ℕ) {i : Fin 7} (hi : Outside i) :
    ∀ f j, (chainPM K L η f j).Preserves i
  | 0, _ => preserves_leafP K L _ hi
  | f + 1, j => ⟨preserves_leafP K L _ hi,
      preserves_prim (by simp [Prim.writes, hi.2.2.1]),
      preserves_chainPM K L η hi f (j + 1)⟩

theorem wf_cbdPM (η L K : ℕ) : (cbdPM η L K).WF :=
  ⟨wf_repX (wf_coinAp 2 4) _, wf_repX (wf_bitAp 3 true) _, wf_repX wf_upStep _,
    wf_repX wf_downStep _, wf_chainPM K L η _ _⟩

theorem preserves_cbdPM (η L K : ℕ) {i : Fin 7} (hi : Outside i) :
    (cbdPM η L K).Preserves i := by
  obtain ⟨h0, h2, h3, h4⟩ := hi
  have tl : ∀ j : Fin 7, i ≠ j → (prog (.prim (.tail j)) : XProg 7).Preserves i :=
    fun j hj ↦ preserves_prim (by simp [Prim.writes, hj])
  have hu : upStep.Preserves i :=
    ⟨⟨preserves_bitAp _ (Ne.symm h3), preserves_nopX i h2⟩, tl 2 h2⟩
  have hd : downStep.Preserves i := ⟨⟨tl 3 h3, preserves_nopX i h2⟩, tl 2 h2⟩
  exact ⟨preserves_repX h2 (preserves_coinAp (Ne.symm h2) (Ne.symm h4)) _,
    preserves_repX h2 (preserves_bitAp _ (Ne.symm h3)) _, preserves_repX h2 hu _,
    preserves_repX h2 hd _, preserves_chainPM K L η ⟨h0, h2, h3, h4⟩ _ _⟩

theorem wf_encCoinsP (η L e : ℕ) : (encCoinsP D η L e).WF :=
  ⟨wf_repF (wf_cbdPM η L D.K) (preserves_cbdPM η L D.K (by simp [Outside])) _,
    wf_repF (by unfold entF; exact ⟨wf_coinsF _, wf_zerosF _⟩) (preserves6_entF _ _) _,
    wf_repF (wf_cbdPM η L D.K) (preserves_cbdPM η L D.K (by simp [Outside])) _⟩

/-- The sampler's law on the actual two-input handler layout. -/
theorem law_encCoinsP {η L e : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) (he : e < D.K) (pref input : List Bool) :
    (encCoinsP D η L e).law (io2 (R := 5) pref input []) =
      (encCoinsLaw (setting D) (Wb D) (Jh D) Pos
        (cbdR D η) (cbdR D η) (floodR D e)).map
          (fun r ↦ io2 (R := 5) (pref ++ encCoinWord D r) input []) := by
  rw [appendLaw_encCoinsP D hL hLK hη he _ (by simp [P5, P3, io2]), PMF.map_comp]
  congr 1
  funext r t
  by_cases ht : t = 0
  · subst ht; simp [io2]
  · simp [io2, Function.update_apply, ht]

end AdvancedEncryption.ExpLUT.Prog
