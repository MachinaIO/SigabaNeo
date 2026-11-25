import PE.Impl.ExpLUT.Prog.RedKeyPktPubLoop
/-!
# The packet stream, part 13: the public words at `D`

The fields of the public-key word `mpkEnc.enc mpk` (`B`, `H`, `a`, `A₀`, `A^in`, `A^aut`, `d`) and of
the ciphertext word `ctEnc.enc ct` (`b`, `h`, `c^aut`, `cinBot`, …) at their offsets (`pbOffH`, …),
as the queues of `exec_pbPubC`; **`pbG_eq`**: `pbGL (σ_g^{2^t})` of the rows of `H_{(t,1)}`, `h_{(t,1)}`
is `G_t = matL C_{g_t}` (`ptG`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

variable (D : Dims) (mpk : MPKt D) (ct : CTt D)

/-! ### The rows of `G_t` -/

/-- Row `0` of `H_{(t,1)}`. -/
noncomputable def pbR0 (t : ℕ) : List (Rg D) := (Enum.list (α := Col D.K)).map (HiK D mpk t 0)
/-- Row `1` of `H_{(t,1)}`. -/
noncomputable def pbR1 (t : ℕ) : List (Rg D) := (Enum.list (α := Col D.K)).map (HiK D mpk t 1)
/-- `h_{(t,1)}` as a function. -/
noncomputable def pbHi (t : ℕ) : Fin 2 × Fin D.K → Rg D := fun c => (evalData (helperMap D) mpk ct).aut.hi t c

/-- `h_{(t,1)}`. -/
noncomputable def pbR2 (t : ℕ) : List (Rg D) :=
  (Enum.list (α := Col D.K)).map (pbHi D mpk ct t)

theorem matL_two {N K : ℕ} (A : Fin 2 → Fin 2 × Fin K → Rq N K) :
    matL A = (Enum.list (α := Fin 2 × Fin K)).map (A 0) ++ (Enum.list (α := Fin 2 × Fin K)).map (A 1) := by
  simp [matL, enum_fin2]

theorem ptG_eq' (t : ℕ) : ptG D mpk ct t = matL (fun a c =>
    (setting D).E.σ ((setting D).idx (2 ^ t)) (HiK D mpk t a c) -
      if a = 1 then (setting D).E.σ ((setting D).idx (2 ^ t)) (pbHi D mpk ct t c) else 0) := rfl

/-- **`G_t`.** -/
theorem pbG_eq (t : ℕ) :
    pbGL (pbSig (gD D) (2 ^ t)) (pbR0 D mpk t) (pbR1 D mpk t) (pbR2 D mpk ct t) = ptG D mpk ct t := by
  rw [ptG_eq', matL_two, pbGL, pbR0, pbR1, pbR2]
  simp only [List.zipWith_map, List.zipWith_self, List.map_map]
  congr 1
  · refine List.map_congr_left fun c _ => ?_
    simp [seSigIdx, pbSig]
  · refine List.map_congr_left fun c _ => ?_
    simp [seSigIdx, pbSig]

/-! ### Families as queues -/

theorem pbFun_enc {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) (f : α → β) :
    (FixedEnc.fun (α := α) e).enc f = (Enum.list (α := α)).flatMap fun a => e.enc (f a) := by
  show ((Enum.list (α := α)).map f).flatMap _ = _
  rw [List.flatMap_map]

theorem pbVecE_enc {α : Type} [Enum α] (f : α → Rg D) :
    (vecE D α).enc f = encL D.N D.K ((Enum.list (α := α)).map f) := by
  show ((Enum.list (α := α)).map f).flatMap _ = _
  rfl

/-- A family over `Fin n` as a queue over `ℕ`. -/
theorem pbFin_range {β : Type*} (n : ℕ) (g : Fin n → List β) (G : ℕ → List β)
    (hG : ∀ m (h : m < n), G m = g ⟨m, h⟩) :
    (List.finRange n).flatMap g = (List.range n).flatMap G := by
  have e := flatMap_range_eq (List.finRange n) g G (fun m hm => by
    rw [List.length_finRange] at hm; rw [hG m hm, List.getElem_finRange]; rfl)
  rw [List.length_finRange] at e
  exact e.symm

theorem pbJh_flatMap {β : Type} (f : Jh D → List β) :
    (Enum.list (α := Jh D)).flatMap f =
      (List.finRange D.b).flatMap fun t => f (t, 0) ++ f (t, 1) := by
  show ((List.finRange D.b).product (List.finRange 2)).flatMap f = _
  rw [product_flatMap]
  refine List.flatMap_congr fun t _ => ?_
  simp [List.finRange_succ]

/-! ### The queues of the bit loop -/

/-- `H_k` as a function. -/
noncomputable def pbHk (k : Jh D) : Fin 2 → Fin 2 × Fin D.K → Rg D := fun a c => mpk.H k a c

/-- `h_{(t,0)}` (discarded). -/
noncomputable def pbH0W (t : ℕ) : List Bool :=
  encL D.N D.K ((Enum.list (α := Col D.K)).map fun c : Fin 2 × Fin D.K =>
    (evalData (helperMap D) mpk ct).aut.hf t c)

theorem pbHf_eq {t : ℕ} (ht : t < D.b) :
    ptHfW D mpk t = (matE D (Fin 2) (Col D.K)).enc (mpk.H (⟨t, ht⟩, 0)) := by
  refine Eq.trans ?_ (matE_enc D _).symm
  show encL D.N D.K (matL fun a c => finExt (S := setting D)
    (fun t => mpk.H ((helperMap D).fwd t)) t a c) = _
  rw [finExt_of_lt (S := setting D) _ ht]; rfl

theorem pbR01_eq {t : ℕ} (ht : t < D.b) :
    encL D.N D.K (pbR0 D mpk t ++ pbR1 D mpk t) = (matE D (Fin 2) (Col D.K)).enc (mpk.H (⟨t, ht⟩, 1)) := by
  refine Eq.trans ?_ (matE_enc D _).symm
  rw [matL_two, pbR0, pbR1]
  show encL D.N D.K ((Enum.list (α := Col D.K)).map (fun c => finExt (S := setting D)
    (fun t => mpk.H ((helperMap D).inv t)) t 0 c) ++ (Enum.list (α := Col D.K)).map (fun c =>
      finExt (S := setting D) (fun t => mpk.H ((helperMap D).inv t)) t 1 c)) = _
  rw [finExt_of_lt (S := setting D) _ ht]; rfl

/-- **The `H` field.** -/
theorem pbFH_eq : (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H =
    (List.range D.b).flatMap fun t => ptHfW D mpk t ++ encL D.N D.K (pbR0 D mpk t ++ pbR1 D mpk t) := by
  have e1 : (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H =
      (Enum.list (α := Jh D)).flatMap fun k => (matE D (Fin 2) (Col D.K)).enc (mpk.H k) :=
    pbFun_enc _ _
  rw [e1, pbJh_flatMap]
  refine pbFin_range _ _ _ fun m hm => ?_
  rw [pbHf_eq D mpk hm, pbR01_eq D mpk hm]

theorem pbh0_eq {t : ℕ} (ht : t < D.b) :
    pbH0W D mpk ct t = (vecE D (Col D.K)).enc (ct.h (⟨t, ht⟩, 0)) := by
  refine Eq.trans ?_ (pbVecE_enc D _).symm
  show encL D.N D.K ((Enum.list (α := Col D.K)).map (fun c => finExt (S := setting D)
    (fun t => ct.h ((helperMap D).fwd t)) t c)) = _
  rw [finExt_of_lt (S := setting D) _ ht]; rfl

theorem pbR2_eq {t : ℕ} (ht : t < D.b) :
    encL D.N D.K (pbR2 D mpk ct t) = (vecE D (Col D.K)).enc (ct.h (⟨t, ht⟩, 1)) := by
  refine Eq.trans ?_ (pbVecE_enc D _).symm
  show encL D.N D.K ((Enum.list (α := Col D.K)).map (fun c => finExt (S := setting D)
    (fun t => ct.h ((helperMap D).inv t)) t c)) = _
  rw [finExt_of_lt (S := setting D) _ ht]; rfl

/-- **The `h` field.** -/
theorem pbFh_eq : (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc ct.h =
    (List.range D.b).flatMap fun t => pbH0W D mpk ct t ++ encL D.N D.K (pbR2 D mpk ct t) := by
  have e1 : (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc ct.h =
      (Enum.list (α := Jh D)).flatMap fun k => (vecE D (Col D.K)).enc (ct.h k) := pbFun_enc _ _
  rw [e1, pbJh_flatMap]
  refine pbFin_range _ _ _ fun m hm => ?_
  rw [pbh0_eq D mpk ct hm, pbR2_eq D mpk ct hm]

/-- **The `A^aut` field.** -/
theorem pbFAa_eq : (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
    (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut = (List.range D.b).flatMap (ptAaW D mpk) := by
  have e1 : (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut = (List.finRange D.b).flatMap fun t =>
        (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc (mpk.Aaut t) := pbFun_enc _ _
  rw [e1]
  refine pbFin_range _ _ _ fun m hm => ?_
  refine Eq.trans ?_ (digE_enc D _).symm
  show encL D.N D.K (adL fun d a c => finExt (S := setting D) mpk.Aaut m d a c) = _
  rw [finExt_of_lt (S := setting D) _ hm]

/-! ### The queues of the step loop -/

/-- `a_{i mod 16}`. -/
noncomputable def pbAW (i : ℕ) : List Bool :=
  encL D.N D.K ((Enum.list (α := Col D.K)).map fun c : Fin 2 × Fin D.K => mpk.a ⟨i % 16, Nat.mod_lt _ (by decide)⟩ c)

/-- `cinBot_{i mod 16}`. -/
noncomputable def pbCbW (i : ℕ) : List Bool :=
  encL D.N D.K ((Enum.list (α := Col D.K)).map fun c : Fin 2 × Fin D.K => ct.cinBot ⟨i % 16, Nat.mod_lt _ (by decide)⟩ c)

/-- `A^in_{i mod 16}`. -/
noncomputable def pbAinW (i : ℕ) : List Bool := encL D.N D.K (adL (AinK D mpk i))

theorem pbPos_range {β : Type*} (g : Pos → List β) :
    (List.finRange 16).flatMap g = (List.range 16).flatMap fun i => g ⟨i % 16, Nat.mod_lt _ (by decide)⟩ :=
  pbFin_range 16 g _ fun m hm => by congr 1; exact Fin.ext (Nat.mod_eq_of_lt hm)

/-- **The `a` field.** -/
theorem pbFa_eq : (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a =
    (List.range 16).flatMap (pbAW D mpk) :=
  (pbFun_enc _ _).trans (pbPos_range _)

/-- **The `cinBot` field.** -/
theorem pbFcb_eq : (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot =
    (List.range 16).flatMap (pbCbW D ct) :=
  (pbFun_enc _ _).trans (pbPos_range _)

/-- **The `A^in` field.** -/
theorem pbFAin_eq : (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K)
    (matE D (Fin 2) (Col D.K)))).enc mpk.Ain = (List.range 16).flatMap (pbAinW D mpk) := by
  refine (pbFun_enc _ _).trans ((pbPos_range _).trans (List.flatMap_congr fun i _ => ?_))
  exact digE_enc D _

/-! ### The step records -/

variable (C : List Bool) (x : Pos → ℕ)

/-- `X^{z_i}`. -/
noncomputable def pbZW (i : ℕ) : List Bool :=
  encRM D.N D.K ((setting D).E.X ^ (bpOf (progOf C)).state x i)

/-- `X^{z_i + w x_{read i}}`. -/
noncomputable def pbUW (i : ℕ) : List Bool :=
  encRM D.N D.K ((setting D).E.X ^ ((bpOf (progOf C)).state x i +
    (bpOf (progOf C)).w * x ((bpOf (progOf C)).read i)))

theorem pbPU_eq (i : ℕ) : ptPUW D C x i = pbUW D C x i := by
  simp only [ptPUW, ptPU, pbUW, encL_singleton]

/-- **`SP_i`.** -/
theorem pbSP_eq (i : ℕ) :
    pbAinW D mpk i ++ (pbAW D mpk i ++ (pbCbW D ct i ++ pbZW D C x i)) = ptSPW D mpk ct C x i := by
  rw [ptSPW, ptSP, encL_append, encL_append, encL_singleton, matL_two, encL_append]
  simp only [List.append_assoc]
  rfl

/-! ### Lengths -/

theorem pbLenColS : (Enum.list (α := Col (setting D).τ)).length = 2 * D.K := length_enum_col
theorem pbLenCol : (Enum.list (α := Col D.K)).length = 2 * D.K := length_enum_col

theorem pbLen_G (t : ℕ) : (ptGW D mpk ct t).length = 4 * D.K * (D.N * D.K) := by
  simp [ptGW, ptG]

theorem pbLen_Hf (t : ℕ) : (ptHfW D mpk t).length = 4 * D.K * (D.N * D.K) := by
  simp [ptHfW, ptHf]

theorem pbLen_Aa (t : ℕ) : (ptAaW D mpk t).length = 16 * D.K ^ 3 * (D.N * D.K) := by
  simp [ptAaW, ptAa, length_adL]

theorem pbLen_Ain (i : ℕ) : (pbAinW D mpk i).length = 16 * D.K ^ 3 * (D.N * D.K) := by
  simp [pbAinW, length_adL]

theorem pbLen_R (t : ℕ) : (pbR0 D mpk t).length = 2 * D.K ∧ (pbR1 D mpk t).length = 2 * D.K ∧
    (pbR2 D mpk ct t).length = 2 * D.K := by
  simp only [pbR0, pbR1, pbR2, List.length_map, pbLenCol, and_self]

theorem pbLen_H01 (t : ℕ) :
    (encL D.N D.K (pbR0 D mpk t ++ pbR1 D mpk t)).length = 4 * D.K * (D.N * D.K) := by
  simp only [length_encL, List.length_append, pbR0, pbR1, List.length_map, pbLenCol]; ring

theorem pbLen_V (t : ℕ) : (pbH0W D mpk ct t).length = 2 * D.K * (D.N * D.K) ∧
    (encL D.N D.K (pbR2 D mpk ct t)).length = 2 * D.K * (D.N * D.K) ∧
    (pbAW D mpk t).length = 2 * D.K * (D.N * D.K) ∧ (pbCbW D ct t).length = 2 * D.K * (D.N * D.K) := by
  simp only [pbH0W, pbR2, pbAW, pbCbW, length_encL, List.length_map, pbLenCol, pbLenColS,
    and_self]

theorem pbLen_ZU (i : ℕ) : (pbZW D C x i).length = D.N * D.K ∧ (pbUW D C x i).length = D.N * D.K := by
  simp [pbZW, pbUW, length_encRM']

theorem pbLen_SP (i : ℕ) :
    (ptSPW D mpk ct C x i).length = (16 * D.K ^ 3 + 4 * D.K + 1) * (D.N * D.K) := by
  rw [← pbSP_eq]
  simp only [List.length_append, pbLen_Ain, (pbLen_V D mpk ct i).2.2.1, (pbLen_V D mpk ct i).2.2.2,
    (pbLen_ZU D C x i).1]
  ring

theorem pbLen_PU (i : ℕ) : (ptPUW D C x i).length = D.N * D.K := by
  rw [pbPU_eq]; exact (pbLen_ZU D C x i).2

theorem pbLen_A0 : (ptA0W D mpk).length = 4 * D.K * (D.N * D.K) := by
  simp [ptA0W, ptA0L]

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
