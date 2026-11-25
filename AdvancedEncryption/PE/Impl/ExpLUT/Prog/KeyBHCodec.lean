import PE.Impl.ExpLUT.Prog.KeyRowAut

/-! The B/H source of the coefficient generator is the actual public-key prefix. -/
namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

/-- A matrix codec follows the product enumeration used by indexed VM reads. -/
theorem matE_enc_product (D : Dims) {α β : Type} [Enum α] [Enum β]
    (A : α → β → Rg D) :
    (matE D α β).enc A = encL D.N D.K
      ((Enum.list (α := α × β)).map (fun ab ↦ A ab.1 ab.2)) := by
  simp only [matE, FixedEnc.fun, FixedEnc.encList, encL, List.flatMap_map]
  change _ = ((Enum.list (α := α)).product (Enum.list (α := β))).flatMap _
  simp [List.product, List.flatMap_assoc, List.flatMap_map, rEnc]

/-- The H family codec follows the nested helper/row/column enumeration. -/
theorem hEnc_product (D : Dims) (mpk : MPKt D) :
    (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H =
    encL D.N D.K ((Enum.list (α := Jh D × Fin 2 × Col D.K)).map
      (fun krc ↦ mpk.H krc.1 krc.2.1 krc.2.2)) := by
  simp only [FixedEnc.fun, FixedEnc.encList, encL, List.flatMap_map]
  change _ = ((Enum.list (α := Jh D)).product
    ((Enum.list (α := Fin 2)).product (Enum.list (α := Col D.K)))).flatMap _
  simp [List.product, List.flatMap_assoc, List.flatMap_map, rEnc]

/-- The B/H source word is the concatenation of the first two public-key codec fields. -/
theorem bhSource_codec (D : Dims) (mpk : MPKt D) :
    encL D.N D.K ((Enum.list (α := BHSource D)).map (bhSource D mpk)) =
      (matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B ++
      (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H := by
  change encL D.N D.K
    (((Enum.list (α := Fin 2 × (Wb D ⊕ Fin (setting D).τ))).map Sum.inl ++
      (Enum.list (α := Jh D × Fin 2 × Col (setting D).τ)).map Sum.inr).map
      (bhSource D mpk)) = _
  simp only [List.map_append, List.map_map, encL_append, Function.comp_def, bhSource]
  exact congrArg₂ (· ++ ·)
    (matE_enc_product D (α := Fin 2) (β := Wb D ⊕ Fin (setting D).τ) mpk.B).symm
    (hEnc_product D mpk).symm

/-- The source stream is a prefix of the actual public-key word. -/
theorem mpkEnc_bhPrefix (D : Dims) (mpk : MPKt D) :
    ∃ tail, (mpkEnc D).enc mpk =
      encL D.N D.K (Enum.list.map (bhSource D mpk)) ++ tail := by
  rw [bhSource_codec]
  simp only [mpkEnc, FixedEnc.comap, FixedEnc.prod]
  refine ⟨(FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a ++
    (matE D (Fin 2) (Col D.K)).enc mpk.A0 ++
    (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Ain ++
    (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut ++
    (vecE D (Fin 2)).enc mpk.d, ?_⟩
  simp only [List.append_assoc]

/-- Retain a fixed-length prefix in register zero. -/
def prefixC (n : ℕ) : Code := .seq (natC 2 rB1 n)
  (.seq (takeC 3 0 2) (.cp 0 3))

theorem wf_prefixC (n : ℕ) : (prefixC n).WFc :=
  ⟨natC_wfc _ _ _, ⟨trivial, trivial⟩, trivial⟩

theorem prefixC_preserves (n : ℕ) (r : Fin 64)
    (h0 : r ≠ 0) (h2 : r ≠ 2) (h3 : r ≠ 3) :
    (prefixC n).writes r = false := by
  simp [prefixC, takeC, Code.writes, natC_writes _ _ _ r h2,
    Ne.symm h0, Ne.symm h3]

theorem exec_prefixC {N K : ℕ} (u tail : List Bool) (w : St)
    (hS : w 0 = u ++ tail) (h1 : w rB1 = [false]) :
    exec N K (prefixC u.length) w 0 = u := by
  rw [prefixC, exec_seq, exec_natC _ _ (by decide) _ w h1, exec_seq,
    exec_takeC _ _ _ (by decide) _ u.length (by simp)]
  simp only [exec_cp, Function.update_self, Function.update_of_ne (by decide : (0 : Fin 64) ≠ 2), hS]
  rw [takeD_eq_take (by simp)]
  simp

/-- Public-key prefix size, independent of its contents. -/
noncomputable def bhPrefixLength (D : Dims) : ℕ :=
  (Enum.list (α := BHSource D)).length * (D.N * D.K)

noncomputable def mpkBHC (D : Dims) (i : ℕ) : Code :=
  .seq (prefixC (bhPrefixLength D)) (gatherBHC D i)

theorem wf_mpkBHC (D : Dims) (i : ℕ) : (mpkBHC D i).WFc :=
  ⟨wf_prefixC _, wf_gatherBHC _ _⟩

/-- Generate the B/H coefficients directly from the encoded public key. -/
theorem exec_mpkBHC (D : Dims) (i : ℕ) (mpk : MPKt D) (w : St)
    (hS : w 0 = (mpkEnc D).enc mpk)
    (h1 : w rB1 = [false]) (hZ : w rZ = SigabaNeo.Lattices.Algo.encRM D.N D.K 0) :
    exec D.N D.K (mpkBHC D i) w 4 = encL D.N D.K
      (Enum.list.map (fun t : BHRow D ↦ (setting D).E.σ ((setting D).idx i)
        (bhSource D mpk (bhSelection D t)))) := by
  obtain ⟨tail, ht⟩ := mpkEnc_bhPrefix D mpk
  have hl : (encL D.N D.K (Enum.list.map (bhSource D mpk))).length = bhPrefixLength D := by
    simp [length_encL, bhPrefixLength]
  rw [mpkBHC, exec_seq]
  apply exec_gatherBHC
  · rw [← hl]
    exact exec_prefixC _ tail w (hS.trans ht) h1
  · rw [exec_writes _ _ _ (prefixC_preserves _ rB1 (by decide) (by decide) (by decide)), h1]
  · rw [exec_writes _ _ _ (prefixC_preserves _ rZ (by decide) (by decide) (by decide)), hZ]

end AdvancedEncryption.ExpLUT.Prog
