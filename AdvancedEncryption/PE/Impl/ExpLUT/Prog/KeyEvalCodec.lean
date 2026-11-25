import PE.Impl.ExpLUT.Prog.KeyTryLaw
/-! Public-key field codecs in the exact stream order consumed by EvalPK. -/
set_option backward.isDefEq.respectTransparency false

namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- A bounded natural-index stream agrees with its finite-index enumeration. -/
theorem range_map_enum {α : Type} (n : ℕ) (f : ℕ → α) (g : Fin n → α)
    (h : ∀ i : Fin n, f i.val = g i) : (List.range n).map f = Enum.list.map g := by
  change (List.range n).map f = (List.finRange n).map g
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simpa using h ⟨j, by simpa using hj⟩

theorem HfK_fin (D : Dims) (mpk : MPKt D) (t : Fin D.b) :
    HfK D mpk t.val = mpk.H (t, 0) := by
  have h : finExt (S := setting D) (fun u ↦ mpk.H ((helperMap D).fwd u)) t.val =
      mpk.H (t, 0) := dite_eq_left t.isLt
  exact congrArg (fun M ↦ fun a c ↦ M a c) h

theorem HiK_fin (D : Dims) (mpk : MPKt D) (t : Fin D.b) :
    HiK D mpk t.val = mpk.H (t, 1) := by
  have h : finExt (S := setting D) (fun u ↦ mpk.H ((helperMap D).inv u)) t.val =
      mpk.H (t, 1) := dite_eq_left t.isLt
  exact congrArg (fun M ↦ fun a c ↦ M a c) h

theorem AaK_fin (D : Dims) (mpk : MPKt D) (t : Fin D.b) :
    AaK D mpk t.val = mpk.Aaut t := by
  have h : finExt (S := setting D) mpk.Aaut t.val = mpk.Aaut t := dite_eq_left t.isLt
  exact congrArg (fun M ↦ fun d a c ↦ M d a c) h

theorem AinK_fin (D : Dims) (mpk : MPKt D) (t : Pos) :
    AinK D mpk t.val = mpk.Ain t := by
  have he : (⟨t.val % 16, Nat.mod_lt _ (by decide)⟩ : Pos) = t :=
    Fin.ext (Nat.mod_eq_of_lt t.isLt)
  exact congrArg (fun u : Pos ↦ fun d a c ↦ mpk.Ain u d a c) he

/-- A family codec is a flat map of the element codec. -/
theorem family_codec_flatMap {α β : Type} [Enum α] {n : ℕ}
    (e : FixedEnc β n) (f : α → β) :
    (FixedEnc.fun e).enc f = Enum.list.flatMap (fun i ↦ e.enc (f i)) := by
  simp only [FixedEnc.fun, FixedEnc.encList, List.flatMap_map]


/-- The helper codec lists the forward and inverse matrix for each bit position. -/
theorem helper_codec_hL (D : Dims) (mpk : MPKt D) :
    (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H =
      encL D.N D.K (hL (HfK D mpk) (HiK D mpk) (List.range D.b)) := by
  have he := range_map_enum D.b
    (fun t ↦ matL (HfK D mpk t) ++ matL (HiK D mpk t))
    (fun t ↦ matL (mpk.H (t, 0)) ++ matL (mpk.H (t, 1)))
    (by intro t; exact congrArg₂ (· ++ ·) (congrArg matL (HfK_fin D mpk t)) (congrArg matL (HiK_fin D mpk t)))
  simp only [hL, List.flatMap_def, he]
  rw [family_codec_flatMap]
  change ((Enum.list (α := Fin D.b)).product (Enum.list (α := Fin 2))).flatMap
    (fun t ↦ (matE D (Fin 2) (Col D.K)).enc (mpk.H t)) = _
  simp only [List.product, List.flatMap_assoc, List.flatMap_map, enum_fin2,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, matE_enc,
    encL, List.flatMap_append, ← List.flatMap_def, List.flatMap_assoc, List.flatMap_map]

/-- The automorphism digit-matrix codec follows the evaluator's round stream. -/
theorem aaut_codec_aautL (D : Dims) (mpk : MPKt D) :
    (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut =
      encL D.N D.K (aautL (AaK D mpk) (List.range D.b)) := by
  have he := range_map_enum D.b (fun t ↦ adL (AaK D mpk t))
    (fun t ↦ adL (mpk.Aaut t)) (by intro t; exact congrArg adL (AaK_fin D mpk t))
  simp only [aautL, List.flatMap_def, he]
  rw [family_codec_flatMap]
  change (Enum.list (α := Fin D.b)).flatMap (fun t ↦
    (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc (mpk.Aaut t)) = _
  simp only [digE_enc, encL, ← List.flatMap_def, List.flatMap_assoc]
  rfl

/-- The input digit-matrix codec follows the sixteen predicate positions. -/
theorem ain_codec_ainL (D : Dims) (mpk : MPKt D) :
    (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc mpk.Ain =
      encL D.N D.K (ainL (AinK D mpk) (List.range 16)) := by
  have he := range_map_enum 16 (fun t ↦ adL (AinK D mpk t))
    (fun t ↦ adL (mpk.Ain t)) (by intro t; exact congrArg adL (AinK_fin D mpk t))
  simp only [ainL, List.flatMap_def, he]
  rw [family_codec_flatMap]
  change (Enum.list (α := Pos)).flatMap (fun t ↦
    (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc (mpk.Ain t)) = _
  simp only [digE_enc, encL, ← List.flatMap_def, List.flatMap_assoc]
  rfl

/-- The existing evaluator computes keyPK when supplied with its exact streams and templates. -/
theorem exec_evalC_keyPK (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (mpk : MPKt D) (C : List Bool) (w : St)
    (hi : StepIn w (gD D) D.b (2 ^ D.b) tlK (HfK D mpk) (HiK D mpk) (AaK D mpk)
      (xInvG (ZMod D.q) D.N))
    (hc : CoefIn w 14 (2 ^ D.b) D.b (xcK D))
    (ha : w rA = (matE D (Fin 2) (Col D.K)).enc mpk.A0)
    (hs : w rAinS = (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc mpk.Ain)
    (hp : w rCs = C) (h15 : w rT15 = List.replicate 15 false) :
    exec D.N D.K evalC w rA =
      encL D.N D.K (matL (keyPK (helperMap D) mpk (bpOf (progOf C)))) := by
  have h := exec_evalC D.N_pos D.K_pos w (gD D) D.b (2 ^ D.b) tlK 14
    (odd_gD D).pos D.hb hn (HfK D mpk) (HiK D mpk) (AaK D mpk)
    (xInvG (ZMod D.q) D.N) (xcK D) hi hc (AinK D mpk) mpk.A0 C
    (ha.trans (matE_enc D mpk.A0)) (hs.trans (ain_codec_ainL D mpk)) hp h15
  have he := keyPK_eq_evalVM D hb mpk C
  exact h.trans (congrArg (fun A ↦ encL D.N D.K (matL A)) he).symm

end AdvancedEncryption.ExpLUT.Prog
