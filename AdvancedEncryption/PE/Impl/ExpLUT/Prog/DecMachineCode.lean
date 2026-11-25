import PE.Impl.ExpLUT.Prog.DecEnc
import PE.Impl.ExpLUT.Prog.DecFinalD
import PE.Impl.ExpLUT.Prog.DecSplit

/-!
# The whole code of `Dec` on the ring-word machine (package F4)

`decCode = splitSkC ; splitCtC ; fixC ; devalC ; finC`: the fields of `sk` (register `76`) and
`ct` (register `77`) are popped into the registers `58 … 72` (`DecSplit`), the templates the
evaluation needs on `76`, `77` are copied from `188`, `189` (`fixC`; the raw words are not needed
any more), the evaluation `devalC` leaves `A_F` on `177` and `c_F` on `176` (`exec_evalC_regs`),
and the end of decryption `finC` leaves the decoded bit on `179` (`exec_finC_D`).

`DInit D sk C ct w`: the registers before the code — the constants and templates, the
predicate word `C` on `73`, the words of `sk`, `ct` on `76`, `77`.

**`exec_decCode`**: for a predicate word of `predLen` bits (and `D.b = 22`), register `179` ends
with `[decodeBit D (decryptRaw (helperMap D) sk.1 (bpOf (progOf C)) sk.2 ct)]`.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix

/-- The templates of the evaluation on `76`, `77` (after the split). -/
def fixC : Code := .seq (.cp 76 188) (.cp 77 189)

/-- **The code of `Dec`.** -/
def decCode : Code := .seq splitSkC (.seq splitCtC (.seq fixC (.seq devalC finC)))

variable (D : Dims)

/-! ### Sizes of the enumerations -/

/-- `|BCol|`. -/
abbrev dmBC : ℕ := (Enum.list (α := BCol (Wb D) D.K)).length
/-- `|Jh × Col|`. -/
abbrev dmJC : ℕ := (Enum.list (α := Jh D × Col D.K)).length
/-- `|Jh|`. -/
abbrev dmJ : ℕ := (Enum.list (α := Jh D)).length
/-- `|Col|`. -/
abbrev dmCol : ℕ := (Enum.list (α := Col D.K)).length
/-- `|Dig|`. -/
abbrev dmDig : ℕ := (Enum.list (α := Dig D.K)).length
/-- `|Pos|`. -/
abbrev dmPos : ℕ := (Enum.list (α := Pos)).length
/-- `b`, as the size of `Fin b`. -/
abbrev dmB : ℕ := (Enum.list (α := Fin D.b)).length
/-- `2`, as the size of `Fin 2`. -/
abbrev dm2 : ℕ := (Enum.list (α := Fin 2)).length

/-- **The registers before the code.** -/
structure DInit (sk : SKt D) (C : List Bool) (ct : CTt D) (w : St) : Prop where
  c : Consts D.N D.K w
  r3 : w 3 = true :: List.replicate (D.N * D.K - 1) false
  r5 : w 5 = List.replicate (D.K - 1) false
  r6 : w 6 = List.replicate (2 * D.K * (D.N * D.K)) false
  r7 : w 7 = List.replicate (4 * D.K * (D.N * D.K)) false
  r8 : w 8 = List.replicate (2 * D.K) false
  r9 : w 9 = List.replicate 2 false
  r10 : w 10 = List.replicate (2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))) false
  r12 : w 12 = List.replicate (2 ^ 22) false
  r13 : w 13 = List.replicate 22 false
  r14 : w 14 = List.replicate 14 false
  r15 : (w 15).length = D.K - 2
  r16 : (w 16).length = dmBC D * (D.N * D.K)
  r17 : (w 17).length = dmBC D
  r18 : (w 18).length = dmJC D
  r19 : (w 19).length = dmJC D * (D.N * D.K)
  kap : ∀ t < 22, w (kReg t) = List.replicate (κD D t) false
  rho : ∀ b' < 14, w (rReg b') = List.replicate (ρD D.N b') false
  r56 : w 56 = List.replicate (D.K * (D.N * D.K)) false
  r73 : w 73 = C
  r74 : (w 74).length = dmJ D
  r75 : w 75 = [true]
  r76 : w 76 = (skEnc D).enc sk
  r77 : w 77 = (ctEnc D).enc ct
  r78 : w 78 = List.replicate (14 * 2 ^ 22) false
  r180 : (w 180).length = dm2 * (dmBC D * (D.N * D.K))
  r181 : (w 181).length = dmJ D * (dm2 * (dmCol D * (D.N * D.K)))
  r182 : (w 182).length = dmPos * (dmCol D * (D.N * D.K))
  r183 : (w 183).length = dmPos * (dmDig D * (dm2 * (dmCol D * (D.N * D.K))))
  r184 : (w 184).length = dmB D * (dmDig D * (dm2 * (dmCol D * (D.N * D.K))))
  r185 : (w 185).length = dm2 * (D.N * D.K)
  r186 : (w 186).length = dmB D * (dmDig D * (dmCol D * (D.N * D.K)))
  r187 : (w 187).length = dmPos * (dmDig D * (dmCol D * (D.N * D.K)))
  r188 : w 188 = List.replicate (4 * D.K) false
  r189 : w 189 = List.replicate (famMLen D) false

/-! ### The encodings as word lists -/

variable {D}

theorem vecE_enc_eq {α : Type} [Enum α] (v : α → Rg D) :
    (vecE D α).enc v = ((Enum.list (α := α)).map fun c => encRM D.N D.K (v c)).flatten := by
  show ((Enum.list (α := α)).map v).flatMap _ = _
  simp [List.flatMap, List.map_map, Function.comp_def, rEnc_enc]

theorem fun_enc_eq {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) (f : α → β) :
    (FixedEnc.fun (α := α) e).enc f = ((Enum.list (α := α)).map fun a => e.enc (f a)).flatten := by
  show ((Enum.list (α := α)).map f).flatMap _ = _
  simp [List.flatMap, List.map_map, Function.comp_def]

theorem matE2_enc_eq {α : Type} [Enum α] (M : Matrix (Fin 2) α (Rg D)) :
    (matE D (Fin 2) α).enc M = (vecE D α).enc (M 0) ++ (vecE D α).enc (M 1) := by
  show ((Enum.list (α := Fin 2)).map M).flatMap (vecE D α).enc = _
  show List.flatMap (vecE D α).enc [M 0, M 1] = _
  simp [List.flatMap]

theorem len_fin2 : dm2 = 2 := by simp [dm2, enum_fin]

theorem dmlen_col : dmCol D = 2 * D.K := length_col D

theorem len_jc : dmJC D = dmJ D * (2 * D.K) := by
  rw [dmJC, length_enum_prod, length_col]

/-- The words of a function into `Jh → Col → Rg` are the words over `Jh × Col`. -/
theorem funJh_enc_eq (h : Jh D → Col D.K → Rg D) :
    (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc h =
      ((Enum.list (α := Jh D × Col D.K)).map fun p => encRM D.N D.K (h p.1 p.2)).flatten := by
  rw [fun_enc_eq]
  show _ = (((Enum.list (α := Jh D)).product (Enum.list (α := Col D.K))).map _).flatten
  rw [map_product, List.flatten_flatten, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  rw [vecE_enc_eq]
  rfl

theorem funJhM_enc_eq (mpk : MPKt D) :
    (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H =
      ((HpsW D mpk).map fun p => p.1.flatten ++ p.2.flatten).flatten := by
  refine (fun_enc_eq (α := Jh D) (matE D (Fin 2) (Col D.K)) mpk.H).trans ?_
  rw [HpsW, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  refine (matE2_enc_eq (D := D) (α := Col D.K) (mpk.H j)).trans ?_
  exact congrArg₂ (· ++ ·) (vecE_enc_eq _) (vecE_enc_eq _)

theorem vecE2_enc_eq (d : Fin 2 → Rg D) :
    (vecE D (Fin 2)).enc d = encRM D.N D.K (d 0) ++ encRM D.N D.K (d 1) := by
  rw [vecE_enc_eq]
  show (([0, 1] : List (Fin 2)).map _).flatten = _
  simp

/-- **The word of `sk`, field by field.** -/
theorem skEnc_split (sk : SKt D) : (skEnc D).enc sk =
    ((vecE D (BCol (Wb D) D.K)).enc (sk.1.B 0) ++ (vecE D (BCol (Wb D) D.K)).enc (sk.1.B 1)) ++
      ((FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc sk.1.H ++
      ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc sk.1.a ++
      ((matE D (Fin 2) (Col D.K)).enc sk.1.A0 ++
      ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc
        sk.1.Ain ++
      ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc
        sk.1.Aaut ++
      ((vecE D (Fin 2)).enc sk.1.d ++ (keyEnc D).enc sk.2)))))) := by
  show ((matE D (Fin 2) (BCol (Wb D) D.K)).enc sk.1.B ++
      ((FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc sk.1.H ++
      ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc sk.1.a ++
      ((matE D (Fin 2) (Col D.K)).enc sk.1.A0 ++
      ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc
        sk.1.Ain ++
      ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc
        sk.1.Aaut ++ (vecE D (Fin 2)).enc sk.1.d)))))) ++ (keyEnc D).enc sk.2 = _
  rw [matE2_enc_eq (D := D) (α := BCol (Wb D) D.K) sk.1.B]
  simp only [List.append_assoc]

/-- The word of `ct`, field by field. -/
theorem ctEnc_split (ct : CTt D) : (ctEnc D).enc ct =
    (vecE D (BCol (Wb D) D.K)).enc ct.b ++
      ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc ct.h ++
      ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.caut ++
      ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot ++
      ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.cin ++
      ((vecE D (Col D.K)).enc ct.c0 ++ (rEnc D).enc ct.cm))))) := rfl

theorem cidx_getElem {e : ℕ} (he : e < (Enum.list (α := Col D.K)).length) :
    cidx D.K (Enum.list (α := Col D.K))[e] = e := by
  set c := (Enum.list (α := Col D.K))[e]
  have hc : cidx D.K c < (Enum.list (α := Col D.K)).length := by
    rw [length_col]; exact cidx_lt c
  have h1 := getElem_enum_col D.K c hc
  exact (List.Nodup.getElem_inj_iff Enum.nodup).mp h1

theorem length_ksW (hb : D.b = 22) (k : Keyt D) :
    (ksW D k).length = 2 ^ 22 * dmBC D + (2 ^ 22 * dmJC D + 2 * D.K) := by
  rw [ksW_split]
  simp only [List.length_append, List.length_map, length_enum_prod, enum_fin,
    List.length_finRange, hb]

/-! ### The whole code -/

theorem exec_seq_eq {N K : ℕ} (p q : Code) (w : St) :
    exec N K (.seq p q) w = exec N K q (exec N K p w) := rfl

theorem exec_decCode_eq {N K : ℕ} (w : St) : exec N K decCode w =
    exec N K finC (exec N K devalC (exec N K fixC (exec N K splitCtC (exec N K splitSkC w)))) := by
  rw [decCode, exec_seq_eq, exec_seq_eq, exec_seq_eq, exec_seq_eq]

set_option maxHeartbeats 1600000 in
/-- **The code of `Dec`**: register `179` holds the decoded bit. -/
theorem exec_decCode (hb : D.b = 22) {sk : SKt D} {C : List Bool} {ct : CTt D}
    (hC : C.length = predLen) {w : St} (h : DInit D sk C ct w) :
    (exec D.N D.K decCode w) 179 =
      [decodeBit D (decryptRaw (helperMap D) sk.1 (bpOf (progOf C)) sk.2 ct)] := by
  obtain ⟨mpk, k⟩ := sk
  have hNK := D.N_pos
  rw [exec_decCode_eq]
  -- the fields of `sk`
  obtain ⟨s58, s59, s60, s61, s62, s63, s64, s65, sf⟩ := exec_splitSkC (N := D.N) (K := D.K) w
    (fB0 := (vecE D (BCol (Wb D) D.K)).enc (mpk.B 0))
    (fB1 := (vecE D (BCol (Wb D) D.K)).enc (mpk.B 1))
    (fH := (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H)
    (fa := (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a)
    (fA0 := (matE D (Fin 2) (Col D.K)).enc mpk.A0)
    (fAin := (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc mpk.Ain)
    (fAaut := (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut)
    (fd := (vecE D (Fin 2)).enc mpk.d) (fk := (keyEnc D).enc k)
    (by rw [h.r76]; exact skEnc_split (mpk, k))
    (by erw [List.length_append, FixedEnc.length, FixedEnc.length, h.r180, len_fin2]; ring)
    (by erw [FixedEnc.length, h.r16])
    (by erw [FixedEnc.length, h.r181])
    (by erw [FixedEnc.length, h.r182])
    (by erw [FixedEnc.length, h.r7]
        simp only [List.length_replicate, enum_fin, List.length_finRange, length_col]; ring)
    (by erw [FixedEnc.length, h.r183])
    (by erw [FixedEnc.length, h.r184])
    (by erw [FixedEnc.length, h.r185])
  set w1 := exec D.N D.K splitSkC w with hw1
  have w1m : ∀ j : Fin 200, j = 73 ∨ j = 74 ∨ j = 75 → w1 j = w j := by
    intro j hj
    refine exec_not_mem _ _ _ ?_
    rcases hj with rfl | rfl | rfl <;> decide
  -- the fields of `ct`
  obtain ⟨t66, t67, t68, t69, t70, t71, t72, tf⟩ := exec_splitCtC (N := D.N) (K := D.K) w1
    (gb := (vecE D (BCol (Wb D) D.K)).enc ct.b)
    (gh := (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc ct.h)
    (gca := (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
      ct.caut)
    (gcb := (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot)
    (gci := (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.cin)
    (gc0 := (vecE D (Col D.K)).enc ct.c0) (gcm := (rEnc D).enc ct.cm)
    (by rw [sf 77 (by decide), h.r77]; exact ctEnc_split ct)
    (by erw [FixedEnc.length, sf 16 (by decide), h.r16])
    (by erw [FixedEnc.length, sf 19 (by decide), h.r19, len_jc, length_col]; ring)
    (by erw [FixedEnc.length, sf 186 (by decide), h.r186])
    (by erw [FixedEnc.length, sf 182 (by decide), h.r182])
    (by erw [FixedEnc.length, sf 187 (by decide), h.r187])
    (by erw [FixedEnc.length, sf 6 (by decide), h.r6, length_col, List.length_replicate])
  set w2 := exec D.N D.K splitCtC w1 with hw2
  have w2m : ∀ j : Fin 200, j = 73 ∨ j = 74 ∨ j = 75 → w2 j = w1 j := by
    intro j hj
    refine exec_not_mem _ _ _ ?_
    rcases hj with rfl | rfl | rfl <;> decide
  -- the templates on `76`, `77`
  set w3 := exec D.N D.K fixC w2 with hw3
  have e3 : w3 = Function.update (Function.update w2 76 (w2 188)) 77
      (Function.update w2 76 (w2 188) 189) := rfl
  have w3lo : ∀ j : Fin 200, j.val < 58 ∨ 77 < j.val ∨ j = 73 ∨ j = 74 ∨ j = 75 → w3 j = w j := by
    intro j hj
    have h76 : j ≠ 76 := by rintro rfl; omega
    have h77 : j ≠ 77 := by rintro rfl; omega
    rw [e3, Function.update_of_ne h77, Function.update_of_ne h76]
    rcases hj with hj | hj | hj
    · rw [tf j (Or.inl (by omega)), sf j (Or.inl hj)]
    · rw [tf j (Or.inr hj), sf j (Or.inr (by omega))]
    · rw [w2m j hj, w1m j hj]
  have w3mid : ∀ j : Fin 200, 58 ≤ j.val → j.val ≤ 65 → w3 j = w1 j := by
    intro j h1 h2
    have h76 : j ≠ 76 := by rintro rfl; simp at h2
    have h77 : j ≠ 77 := by rintro rfl; simp at h2
    rw [e3, Function.update_of_ne h77, Function.update_of_ne h76, tf j (Or.inl (by omega))]
  have w3ct : ∀ j : Fin 200, 66 ≤ j.val → j.val ≤ 72 → w3 j = w2 j := by
    intro j h1 h2
    have h76 : j ≠ 76 := by rintro rfl; simp at h2
    have h77 : j ≠ 77 := by rintro rfl; simp at h2
    rw [e3, Function.update_of_ne h77, Function.update_of_ne h76]
  have w3_76 : w3 76 = List.replicate (4 * D.K) false := by
    rw [e3, Function.update_of_ne (by decide), Function.update_self, tf 188 (by decide),
      sf 188 (by decide), h.r188]
  have w3_77 : w3 77 = List.replicate (famMLen D) false := by
    rw [e3, Function.update_self, Function.update_of_ne (by decide), tf 189 (by decide),
      sf 189 (by decide), h.r189]
  -- the registers of the evaluation
  have ck : CK D.N D.K (2 ^ 22) 22 (κD D) (ρD D.N) w3 :=
    { c := consts_of_agree h.c fun j hj => w3lo j (Or.inl (by omega))
      one := by rw [w3lo 3 (by decide)]; exact h.r3
      km1 := by rw [w3lo 5 (by decide)]; exact h.r5
      mat := by rw [w3lo 7 (by decide)]; exact h.r7
      tw := by rw [w3lo 12 (by decide)]; exact h.r12
      tb := by rw [w3lo 13 (by decide)]; exact h.r13
      t14 := by rw [w3lo 14 (by decide)]; exact h.r14
      vk := by rw [w3lo 56 (by decide)]; exact h.r56
      kap := fun t ht => by
        rw [w3lo _ (Or.inl (by simp [kReg]; omega))]; exact h.kap t ht
      rho := fun b' hb' => by
        rw [w3lo _ (Or.inl (by simp [rReg]; omega))]; exact h.rho b' hb' }
  have regs : DecRegs D mpk ct C w3 :=
    { lc := ⟨⟨ck, by rw [w3lo 6 (by decide)]; exact h.r6, by rw [w3lo 8 (by decide)]; exact h.r8,
        by rw [w3lo 9 (by decide)]; exact h.r9, by rw [w3lo 10 (by decide)]; exact h.r10, w3_76⟩,
        w3_77⟩
      r78 := by rw [w3lo 78 (by decide)]; exact h.r78
      hC := by rw [w3lo 73 (by decide)]; exact h.r73
      H := by rw [w3mid 59 (by decide) (by decide)]; exact s59
      Aa := by rw [w3mid 63 (by decide) (by decide)]; exact s63
      A0 := by rw [w3mid 61 (by decide) (by decide)]; exact s61
      Ain := by rw [w3mid 62 (by decide) (by decide)]; exact s62
      a := by rw [w3mid 60 (by decide) (by decide)]; exact s60
      h := by rw [w3ct 67 (by decide) (by decide)]; exact t67
      ca := by rw [w3ct 68 (by decide) (by decide)]; exact t68
      c0 := by rw [w3ct 71 (by decide) (by decide)]; exact t71
      cin := by rw [w3ct 70 (by decide) (by decide)]; exact t70
      cb := by rw [w3ct 69 (by decide) (by decide)]; exact t69 }
  -- the evaluation
  obtain ⟨⟨as, has, hA⟩, ⟨cs, hcs, hcF⟩, hlo⟩ := exec_evalC_regs hb hC regs
  set w4 := exec D.N D.K devalC w3 with hw4
  have v : ∀ j : Fin 200, j.val < 58 ∨ (77 < j.val ∧ j.val < 80) ∨ j = 73 ∨ j = 74 ∨ j = 75 →
      w4 j = w j := by
    intro j hj
    rw [hlo j (by omega), w3lo j (by omega)]
  have v1 : ∀ j : Fin 200, 58 ≤ j.val → j.val ≤ 65 → w4 j = w1 j := fun j h1 h2 => by
    rw [hlo j (by omega), w3mid j h1 h2]
  have v2 : ∀ j : Fin 200, 66 ≤ j.val → j.val ≤ 72 → w4 j = w2 j := fun j h1 h2 => by
    rw [hlo j (by omega), w3ct j h1 h2]
  have hAl := hA.len
  have hc4 : Consts D.N D.K w4 := consts_of_agree h.c fun j hj => v j (Or.inl (by omega))
  have l17 : (w4 17).length = dmBC D := by rw [v 17 (by decide)]; exact h.r17
  have l18 : (w4 18).length = dmJC D := by rw [v 18 (by decide)]; exact h.r18
  have l12 : (w4 12).length = 2 ^ 22 := by rw [v 12 (by decide), h.r12, List.length_replicate]
  have l74 : (w4 74).length = dmJ D := by rw [v 74 (by decide)]; exact h.r74
  have hks := length_ksW hb k
  have fin : FinD D w4 mpk (bpOf (progOf C)) k ct cs (as.take (2 * D.K)) (as.drop (2 * D.K)) :=
    { all :=
      { fin :=
        { c := hc4
          r16 := by rw [v 16 (by decide), h.r16, l17]
          b := by rw [v2 66 (by decide) (by decide), t66]; exact vecE_enc_eq _
          B2 := by rw [v1 58 (by decide) (by decide), s58]; exact vecE_enc_eq _
          key := by rw [v1 65 (by decide) (by decide), s65]; exact vecE_enc_eq _
          bsl := by rw [l17, bsW, List.length_map]
          B2l := by rw [l17, B2W, List.length_map]
          ksl := by rw [l12, l17, hks]; omega
          bsw := fun x hx => by
            obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _
          B2w := fun x hx => by
            obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _
          ksw := fun x hx => by
            obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _ }
        r3 := by
          rw [v 3 (by decide), h.r3, List.length_cons, List.length_replicate]
          have := Nat.mul_pos hNK (show 0 < D.K by have := D.hK; omega); omega
        r5 := by rw [v 5 (by decide), h.r5, List.length_replicate]
        r6 := by rw [v 6 (by decide)]; exact h.r6
        r8 := by rw [v 8 (by decide), h.r8, List.length_replicate]
        r15 := by rw [v 15 (by decide)]; exact h.r15
        r18 := by rw [l18, l74, len_jc]
        r19 := by rw [v 19 (by decide), h.r19, l18]
        r75 := by rw [v 75 (by decide)]; exact h.r75
        H := by rw [v1 59 (by decide) (by decide), s59]; exact funJhM_enc_eq mpk
        Hl := by rw [l74, HpsW, List.length_map]
        Hw := fun p hp => by
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
          refine ⟨by simp [length_col], by simp [length_col], fun x hx => ?_, fun x hx => ?_⟩
          · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _
          · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _
        h := by rw [v2 67 (by decide) (by decide), t67]; exact funJh_enc_eq ct.h
        hl := by rw [l18, hsW, List.length_map]
        hw := fun x hx => by
          obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _
        ksl := by rw [l12, l17, l18, hks]; omega
        cF := by rw [hcs]
        AF := by rw [has, ← List.flatten_append, List.take_append_drop]
        cFl := hcF.len
        A0l := by rw [List.length_take, hAl]; omega
        A1l := by rw [List.length_drop, hAl]; omega
        cFw := hcF.wid
        A0w := fun x hx => hA.wid x (List.mem_of_mem_take hx)
        A1w := fun x hx => hA.wid x (List.mem_of_mem_drop hx)
        d := by rw [v1 64 (by decide) (by decide), s64]; exact vecE2_enc_eq _
        d0l := length_encRM _ _ _
        d1l := length_encRM _ _ _
        cm := by rw [v2 72 (by decide) (by decide), t72]; exact (rEnc D).length _ }
      r3 := by rw [v 3 (by decide)]; exact h.r3
      r12 := by rw [l12, hb]
      r17 := l17
      r18 := l18
      r20 := by
        rw [v 20 (by decide)]
        have := h.kap 0 (by decide)
        rw [show kReg 0 = 20 from rfl] at this
        rw [this, List.length_replicate]
      r72 := by rw [v2 72 (by decide) (by decide), t72]; rfl
      cF := fun e he => by
        have := hcF.val (Enum.list (α := Col D.K))[e]
        rwa [cidx_getElem he] at this
      AF1 := fun e he => by
        have := hA.val 1 (Enum.list (α := Col D.K))[e]
        rw [cidx_getElem he, show 2 * D.K * (1 : Fin 2).val = 2 * D.K from by simp] at this
        rw [dgetD_drop']
        exact this }
  exact exec_finC_D D fin

end AdvancedEncryption.ExpLUT.Prog
