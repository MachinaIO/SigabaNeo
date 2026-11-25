import PE.Impl.ExpLUT.Prog.RedKeyPktLoopR
/-!
# The packet stream, part 8: the loops compute the stream of `sePkOf` (at `D`)

With the words `O = encRM 1`, `Z = encRM 0`, `Z2 = encL (ptZRow D)`, `ZL = encL (2^b − 1 zero rows)`
and the programming rows `ptRowOf zr i = (bits zr i w)_{w < m̄}` in the order of `zrEnc`
(`ptZRWord zr = (ptRZ ++ ptRR0 ++ ptRRin ++ ptRA).flatten = zrEnc.enc zr`), the `Ā` packets of
`ptInlLoopC` are `encL (sePkOf … (inl w₀))` (**`ptInlPk_eq`**) and the `η` packets of `ptInrLoopC`
are `encL (sePkOf … (inr ((t₀, s), c_j)))` (**`ptJPk_eq`**); together **`ptLoops_eq`**: the two
loop outputs are `encL ((seRestL D).flatMap (sePkOf …))`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Generic list lemmas -/

theorem take_drop_flatMap_block {α β : Type*} (l : List α) (f : α → List β) (L : ℕ)
    (hf : ∀ a, (f a).length = L) : ∀ (i : ℕ) (hi : i < l.length),
      ((l.flatMap f).drop (i * L)).take L = f l[i]
  | 0, hi => by
    obtain ⟨a, l', rfl⟩ : ∃ a l', l = a :: l' := by
      cases l with
      | nil => simp at hi
      | cons a l' => exact ⟨a, l', rfl⟩
    simp [List.flatMap_cons, List.take_append_of_le_length (le_of_eq (hf a).symm), ← hf a]
  | i + 1, hi => by
    obtain ⟨a, l', rfl⟩ : ∃ a l', l = a :: l' := by
      cases l with
      | nil => simp at hi
      | cons a l' => exact ⟨a, l', rfl⟩
    rw [List.flatMap_cons, show (i + 1) * L = (f a).length + i * L by rw [hf a]; ring,
      ← List.drop_drop, List.drop_left]
    exact take_drop_flatMap_block l' f L hf i (by simpa using hi)

theorem flatMap_range_eq {α β : Type*} (l : List α) (g : α → List β) (G : ℕ → List β)
    (hG : ∀ m (h : m < l.length), G m = g l[m]) :
    (List.range l.length).flatMap G = l.flatMap g := by
  induction l generalizing G with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_cons,
      List.flatMap_map, hG 0 (by simp)]
    congr 1
    exact ih _ fun m hm => by rw [hG (m + 1) (by simp; omega)]; rfl

theorem ptDigW_flatMap {δ : Type*} (O Z : List Bool) (w0 nC : ℕ) (l : List δ)
    (g : δ → List (List Bool)) (hg : ∀ d, (g d).length = nC) :
    ptDigW O Z w0 nC l.length (l.flatMap g) =
      l.flatMap fun d => ptEmit O Z (ptCol w0 (g d)) ++ ptEmit O Z (ptCol w0 (g d)) := by
  unfold ptDigW
  refine flatMap_range_eq l _ _ fun m hm => ?_
  rw [take_drop_flatMap_block l g nC hg m hm]

/-- `encL` of a `flatMap`. -/
theorem encL_flatMap' {N K : ℕ} {δ : Type*} (l : List δ) (f : δ → List (Rq N K)) :
    encL N K (l.flatMap f) = l.flatMap fun d => encL N K (f d) := by
  simp [encL, List.flatMap_assoc]

/-- **Emitted bits are ring words.** -/
theorem ptEmit_eq_encL {N K : ℕ} (bs : List Bool) :
    ptEmit (encRM N K 1) (encRM N K 0) bs = encL N K (bs.map fun b => (bitVal b : Rq N K)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [ptEmit, List.map_cons, List.flatten_cons, encL_cons] at ih ⊢
    rw [ih]
    cases b <;> simp [bitVal]

theorem getElem_nodup_map_ite {α β : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) (j : ℕ)
    (hj : j < l.length) (a b : β) :
    l.map (fun c => if l[j] = c then a else b) =
      List.replicate j b ++ a :: List.replicate (l.length - j - 1) b := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  rw [List.getElem_map]
  have hi : i < l.length := by simpa using h1
  by_cases hij : i = j
  · subst hij; simp [List.getElem_append_right]
  · have hne : l[j] ≠ l[i] := fun e => hij ((hl.getElem_inj_iff).mp e.symm)
    rw [if_neg hne]
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · rw [List.getElem_append_left (by simpa using h)]; simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_replicate]
      obtain ⟨k, hk⟩ : ∃ k, i - j = k + 1 := ⟨i - j - 1, by omega⟩
      simp [hk]

/-! ### The programming rows -/

variable (D : Dims) (zr : PrI (setting D) Pos → Wb D → Bool)

/-- The row of the programming column `i`. -/
def ptRowOf (i : PrI (setting D) Pos) : List Bool := (List.finRange D.mb).map (zr i)

/-- The rows of `Z`. -/
noncomputable def ptRZ : List (List Bool) :=
  (Enum.list (α := Pos × Col (setting D).τ)).map fun j => ptRowOf D zr (.inl j)
/-- The rows of `R₀`. -/
noncomputable def ptRR0 : List (List Bool) :=
  (Enum.list (α := Col (setting D).τ)).map fun j => ptRowOf D zr (.inr (.inl j))
/-- The rows of `R^in`. -/
noncomputable def ptRRin : List (List Bool) :=
  (Enum.list (α := Pos × Dig (setting D).τ × Col (setting D).τ)).map fun j =>
    ptRowOf D zr (.inr (.inr (.inl j)))
/-- The rows of `R^aut`. -/
noncomputable def ptRA : List (List Bool) :=
  (Enum.list (α := Fin (setting D).b × Dig (setting D).τ × Col (setting D).τ)).map fun j =>
    ptRowOf D zr (.inr (.inr (.inr j)))

theorem zrEnc_eq_flatMap : (zrEnc D).enc zr =
    (Enum.list (α := PrI (setting D) Pos)).flatMap (ptRowOf D zr) := by
  show ((Enum.list (α := PrI (setting D) Pos)).map zr).flatMap
    (fun f => ((Enum.list (α := Wb D)).map f).flatMap bitEnc.enc) = _
  rw [List.flatMap_map]
  refine List.flatMap_congr fun i _ => ?_
  show ((Enum.list (α := Wb D)).map (zr i)).flatMap (fun a => [a]) = _
  rw [List.flatMap_singleton']; rfl

theorem ptZRWord_eq : (ptRZ D zr ++ (ptRR0 D zr ++ (ptRRin D zr ++ ptRA D zr))).flatten =
    (zrEnc D).enc zr := by
  rw [zrEnc_eq_flatMap]
  show _ = ((Enum.list (α := Pos × Col (setting D).τ)).map Sum.inl ++
    ((Enum.list (α := Col (setting D).τ)).map Sum.inl ++
      ((Enum.list (α := Pos × Dig (setting D).τ × Col (setting D).τ)).map Sum.inl ++
        (Enum.list (α := Fin (setting D).b × Dig (setting D).τ × Col (setting D).τ)).map
          Sum.inr).map Sum.inr).map Sum.inr).flatMap (ptRowOf D zr)
  simp only [ptRZ, ptRR0, ptRRin, ptRA, List.flatten_append, List.flatMap_append, List.map_append,
    List.flatMap_map, ← List.flatMap_def]

/-! ### The segments of an `Ā` slab -/

/-- The width of a row, `2K`. -/
abbrev ptNC : ℕ := 2 * D.K
/-- The number of digit positions. -/
abbrev ptND : ℕ := (Enum.list (α := DigI D.K)).length

theorem length_enumCol : (Enum.list (α := Fin 2 × Fin D.K)).length = ptNC D := length_enum_col

theorem ptRowB_enc (f : Fin 2 × Fin D.K → Bool) :
    encL D.N D.K (ptRowB D f) =
      ptEmit (encRM D.N D.K 1) (encRM D.N D.K 0) ((Enum.list (α := Fin 2 × Fin D.K)).map f) := by
  rw [ptEmit_eq_encL, List.map_map]; rfl

theorem ptCol_rowOf {γ : Type*} (w0 : ℕ) (hw : w0 < D.mb) (l : List γ) (F : γ → PrI (setting D) Pos) :
    ptCol w0 (l.map fun j => ptRowOf D zr (F j)) = l.map fun j => zr (F j) ⟨w0, hw⟩ := by
  simp only [ptCol, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, ptRowOf]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

theorem enum_prod_map {α β γ : Type} [Enum α] [Enum β] (f : α × β → γ) :
    (Enum.list (α := α × β)).map f =
      (Enum.list (α := α)).flatMap fun a => (Enum.list (α := β)).map fun b => f (a, b) :=
  product_map _ _ f

theorem length_enum_prod' {α β : Type} [Enum α] [Enum β] :
    (Enum.list (α := α × β)).length = (Enum.list (α := α)).length * (Enum.list (α := β)).length :=
  List.length_product _ _

theorem take_drop_finRange_block {γ : Type*} (n L : ℕ) (f : Fin n → List γ)
    (hf : ∀ a, (f a).length = L) (i : ℕ) (hi : i < n) :
    (((List.finRange n).flatMap f).drop (i * L)).take L = f ⟨i, hi⟩ := by
  rw [take_drop_flatMap_block _ f L hf i (by simpa using hi)]
  simp

theorem length_enumColS : (Enum.list (α := Col (setting D).τ)).length = ptNC D := length_enum_col

theorem length_enumDCS :
    (Enum.list (α := Dig (setting D).τ × Col (setting D).τ)).length = ptND D * ptNC D := by
  rw [length_enum_prod', length_enumColS]; rfl

theorem ptDigEnc (w0 : ℕ) (hw : w0 < D.mb) (F : Dig (setting D).τ → Col (setting D).τ → PrI (setting D) Pos) :
    ptDigW (encRM D.N D.K 1) (encRM D.N D.K 0) w0 (ptNC D) (ptND D)
        ((Enum.list (α := Dig (setting D).τ)).flatMap fun d =>
          (Enum.list (α := Col (setting D).τ)).map fun c => ptRowOf D zr (F d c)) =
      encL D.N D.K (ptDig D fun d => ptRowB D fun c => zr (F d c) ⟨w0, hw⟩) := by
  refine (ptDigW_flatMap _ _ _ _ _ _ fun d => by rw [List.length_map, length_enumColS]).trans ?_
  rw [ptDig, encL_flatMap']
  exact List.flatMap_congr fun d _ => by
    rw [encL_append, ptRowB_enc, ptCol_rowOf D zr w0 hw]; rfl

theorem ptAdLW_eq (w0 : ℕ) (hw : w0 < D.mb) {t : ℕ} (ht : t < D.b) :
    ptAdLW w0 (ptNC D) (ptND D) (encRM D.N D.K 1) (encRM D.N D.K 0) (ptRA D zr) t =
      encL D.N D.K (ptAd D zr (.inl ⟨w0, hw⟩) t) := by
  have e2 : ptRA D zr = (List.finRange (setting D).b).flatMap (fun t' =>
      (Enum.list (α := Dig (setting D).τ × Col (setting D).τ)).map fun dc =>
        ptRowOf D zr (.inr (.inr (.inr (t', dc))))) := enum_prod_map _
  rw [ptAdLW, e2, take_drop_finRange_block (setting D).b _ _
    (fun a => by rw [List.length_map, length_enumDCS]) t (show t < (setting D).b from ht), enum_prod_map, ptDigEnc D zr w0 hw]
  simp only [ptAd, dif_pos ht]

theorem ptL0LW_eq (w0 : ℕ) (hw : w0 < D.mb) :
    ptL0LW w0 (ptNC D) (encRM D.N D.K 1) (encRM D.N D.K 0)
        (encL D.N D.K (List.replicate (2 ^ D.b - 1) (ptZRow D)).flatten) (ptRR0 D zr) =
      encL D.N D.K (ptL0 D zr (.inl ⟨w0, hw⟩)) := by
  have hl : (ptRR0 D zr).length = ptNC D := by rw [ptRR0, List.length_map]; exact length_enumColS D
  rw [ptL0LW, ← hl, List.take_length, ptRR0, ptCol_rowOf D zr w0 hw, ptL0, encL_append,
    ptRowB_enc]
  rfl

theorem ptZLW_eq (w0 : ℕ) (hw : w0 < D.mb) {i : ℕ} (hi : i < 16) :
    ptZLW w0 (ptNC D) (encRM D.N D.K 1) (encRM D.N D.K 0) (ptRZ D zr) i =
      encL D.N D.K (ptZ D zr (.inl ⟨w0, hw⟩) i) := by
  have e2 : ptRZ D zr = (List.finRange w8.len).flatMap (fun t' =>
      (Enum.list (α := Col (setting D).τ)).map fun c => ptRowOf D zr (.inl (t', c))) :=
    enum_prod_map _
  rw [ptZLW, e2, take_drop_finRange_block w8.len _ _
    (fun a => by rw [List.length_map, length_enumColS]) i (show i < w8.len from hi), ptCol_rowOf D zr w0 hw, ptZ, ptRowB_enc]
  have : (⟨i % 16, Nat.mod_lt _ (by decide)⟩ : Pos) = ⟨i, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
  rw [this]
  rfl

theorem ptRdLW_eq (w0 : ℕ) (hw : w0 < D.mb) {i : ℕ} (hi : i < 16) :
    ptRdLW w0 (ptNC D) (ptND D) (encRM D.N D.K 1) (encRM D.N D.K 0) (ptRRin D zr) i =
      encL D.N D.K (ptRd D zr (.inl ⟨w0, hw⟩) i) := by
  have e2 : ptRRin D zr = (List.finRange w8.len).flatMap (fun t' =>
      (Enum.list (α := Dig (setting D).τ × Col (setting D).τ)).map fun dc =>
        ptRowOf D zr (.inr (.inr (.inl (t', dc))))) := enum_prod_map _
  rw [ptRdLW, e2, take_drop_finRange_block w8.len _ _
    (fun a => by rw [List.length_map, length_enumDCS]) i (show i < w8.len from hi), enum_prod_map, ptDigEnc D zr w0 hw]
  have : (⟨i % 16, Nat.mod_lt _ (by decide)⟩ : Pos) = ⟨i, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
  simp only [ptRd, this]

/-! ### The segments of an `η` slab -/

/-- The word of the zero row. -/
noncomputable abbrev ptZ2W : List Bool := encL D.N D.K (ptZRow D)
/-- The word of `2^b − 1` zero rows. -/
noncomputable abbrev ptZLW' : List Bool := encL D.N D.K (List.replicate (2 ^ D.b - 1) (ptZRow D)).flatten

theorem ptAdRW_eq (ρ : Jh D × Col (setting D).τ) (t : ℕ) :
    ptAdRW (ptND D) (ptZ2W D) = encL D.N D.K (ptAd D zr (.inr ρ) t) := by
  rw [ptAd, ptDig, encL_flatMap', flatMap_const_zero, ptAdRW, encL_append]

theorem ptRdRW_eq (ρ : Jh D × Col (setting D).τ) (i : ℕ) :
    ptAdRW (ptND D) (ptZ2W D) = encL D.N D.K (ptRd D zr (.inr ρ) i) := by
  rw [ptRd, ptDig, encL_flatMap', flatMap_const_zero, ptAdRW, encL_append]

theorem ptL0RW_eq (ρ : Jh D × Col (setting D).τ) :
    ptZ2W D ++ ptZLW' D = encL D.N D.K (ptL0 D zr (.inr ρ)) := by
  rw [ptL0, ← encL_append]
  congr 1
  obtain ⟨n, hn⟩ : ∃ n, 2 ^ D.b = n + 1 := ⟨2 ^ D.b - 1, by have := Nat.one_le_two_pow (n := D.b); omega⟩
  rw [hn, Nat.add_sub_cancel, List.replicate_succ, List.flatten_cons]

theorem ptSelVM_getD (b t0 : ℕ) (s : Bool) (ht0 : t0 < b) {t : ℕ} (ht : t < b) :
    (ptSelVM b t0 s).getD (2 * t) false = decide (t0 = t ∧ s = true) ∧
      (ptSelVM b t0 s).getD (2 * t + 1) false = decide (t0 = t ∧ s = false) := by
  unfold ptSelVM
  rcases Nat.lt_trichotomy t t0 with h | rfl | h
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_replicate, show t0 ≠ t by omega]
  · constructor
    · rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_replicate, Nat.sub_self]
      cases s <;> rfl
    · rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_replicate, show 2 * t + 1 - 2 * t = 1 by omega]
      cases s <;> rfl
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_replicate]
    rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_cons, List.length_nil]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
    simp [show t0 ≠ t by omega]

/-- The `j`-th column. -/
noncomputable def ptColJ (j : ℕ) (hj : j < ptNC D) : Col (setting D).τ :=
  (Enum.list (α := Col (setting D).τ))[j]'(by rw [length_enumColS]; exact hj)

theorem ptUnitVM_eq (j : ℕ) (hj : j < ptNC D) :
    ptUnitVM (encRM D.N D.K 1) (encRM D.N D.K 0) (ptNC D) j = encL D.N D.K (ptUnit D (ptColJ D j hj)) := by
  have hl : (Enum.list (α := Col (setting D).τ)).length = ptNC D := length_enumColS D
  have e := getElem_nodup_map_ite (Enum.list (α := Col (setting D).τ)) Enum.nodup j (by rw [hl]; exact hj)
    (1 : Rg D) 0
  have eu : ptUnit D (ptColJ D j hj) = List.replicate j 0 ++ 1 :: List.replicate (ptNC D - j - 1) 0 := by
    rw [← hl]; exact e
  have hflat : ∀ n, (List.replicate n (List.replicate (D.N * D.K) false)).flatten =
      List.replicate (n * (D.N * D.K)) false := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [List.replicate_succ, List.flatten_cons, ih, ← List.replicate_add]; congr 1; ring
  rw [eu, ptUnitVM, encL_append, encL_cons, encL_replicate_zero, encL_replicate_zero, encRM_zero]
  simp only [List.length_replicate, hflat, List.drop_replicate]
  congr 3
  rw [Nat.sub_sub, Nat.sub_mul, Nat.add_mul, one_mul]

/-! ### The packets and the stream -/

variable (mpk : MPKt D) (ct : CTt D) (C : List Bool) (x : Pos → ℕ)

/-- The public words. -/
noncomputable abbrev ptGW (t : ℕ) : List Bool := encL D.N D.K (ptG D mpk ct t)
noncomputable abbrev ptAaW (t : ℕ) : List Bool := encL D.N D.K (ptAa D mpk t)
noncomputable abbrev ptHfW (t : ℕ) : List Bool := encL D.N D.K (ptHf D mpk t)
noncomputable abbrev ptSPW (i : ℕ) : List Bool := encL D.N D.K (ptSP D mpk ct C x i)
noncomputable abbrev ptPUW (i : ℕ) : List Bool := encL D.N D.K (ptPU D C x i)
noncomputable abbrev ptA0W : List Bool := encL D.N D.K (ptA0L D mpk)

theorem encL_ptPacket {N K : ℕ} (b : ℕ) (G ad cr Aa hr Hf : ℕ → List (Rq N K)) (l0 A0 : List (Rq N K))
    (SP z rd PU : ℕ → List (Rq N K)) :
    encL N K (ptPacket b G ad cr Aa hr Hf l0 A0 SP z rd PU) =
      ptPacket b (fun t => encL N K (G t)) (fun t => encL N K (ad t)) (fun t => encL N K (cr t))
        (fun t => encL N K (Aa t)) (fun t => encL N K (hr t)) (fun t => encL N K (Hf t))
        (encL N K l0) (encL N K A0) (fun i => encL N K (SP i)) (fun i => encL N K (z i))
        (fun i => encL N K (rd i)) (fun i => encL N K (PU i)) :=
  flatMap_ptPacket _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The packet of the `Ā` slab `w₀`.** -/
theorem ptInlPk_eq (w0 : ℕ) (hw : w0 < D.mb) :
    ptInlPk D.b (ptNC D) (ptND D) (encRM D.N D.K 1) (encRM D.N D.K 0) (ptZ2W D) (ptZLW' D)
        (ptRA D zr) (ptRR0 D zr) (ptRZ D zr) (ptRRin D zr) (ptGW D mpk ct) (ptAaW D mpk)
        (ptHfW D mpk) (ptSPW D mpk ct C x) (ptPUW D C x) (ptA0W D mpk) w0 =
      encL D.N D.K (sePkOf D mpk C ct x (ExpLUT.progOf zr) (.inl ⟨w0, hw⟩)) := by
  rw [sePkOf_eq, encL_ptPacket, ptInlPk]
  exact ptPacket_congr (fun _ _ => rfl) (fun t ht => ptAdLW_eq D zr w0 hw ht) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (ptL0LW_eq D zr w0 hw) rfl (fun _ _ => rfl)
    (fun i hi => ptZLW_eq D zr w0 hw hi) (fun i hi => ptRdLW_eq D zr w0 hw hi) (fun _ _ => rfl)

/-- The helper of the `η` slab `(t₀, s)`. -/
def ptJh (t0 : ℕ) (h : t0 < D.b) (s : Bool) : Jh D := (⟨t0, h⟩, if s then 1 else 0)

/-- **The packet of the `η` slab `((t₀, s), c_j)`.** -/
theorem ptInrPk_eq (t0 : ℕ) (h0 : t0 < D.b) (s : Bool) (j : ℕ) (hj : j < ptNC D) :
    ptInrPk D.b (ptND D) (ptZ2W D) (ptZLW' D) (ptGW D mpk ct) (ptAaW D mpk) (ptHfW D mpk)
        (ptSPW D mpk ct C x) (ptPUW D C x) (ptA0W D mpk) (ptSelVM D.b t0 s)
        (ptUnitVM (encRM D.N D.K 1) (encRM D.N D.K 0) (ptNC D) j) =
      encL D.N D.K (sePkOf D mpk C ct x (ExpLUT.progOf zr) (.inr (ptJh D t0 h0 s, ptColJ D j hj))) := by
  rw [sePkOf_eq, encL_ptPacket, ptInrPk]
  refine ptPacket_congr (fun _ _ => rfl) (fun t _ => ptAdRW_eq D zr _ t) ?_ (fun _ _ => rfl) ?_
    (fun _ _ => rfl) (ptL0RW_eq D zr _) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun i _ => ptRdRW_eq D zr _ i) (fun _ _ => rfl)
  · intro t ht
    rw [ptCrRW, (ptSelVM_getD D.b t0 s h0 ht).1, ptUnitVM_eq D j hj, ptCr]
    simp only [ptJh]
    cases s
    · simp
    · by_cases e : t0 = t
      · subst e; simp
      · simp [e]
  · intro t ht
    rw [ptHrRW, (ptSelVM_getD D.b t0 s h0 ht).2, ptUnitVM_eq D j hj, ptHr]
    simp only [ptJh]
    cases s
    · by_cases e : t0 = t
      · subst e; simp
      · simp [e]
    · simp

/-- **The packets of `(t₀, s)`.** -/
theorem ptJPk_eq (t0 : ℕ) (h0 : t0 < D.b) (s : Bool) :
    ptJPk D.b (ptNC D) (ptND D) (encRM D.N D.K 1) (encRM D.N D.K 0) (ptZ2W D) (ptZLW' D)
        (ptGW D mpk ct) (ptAaW D mpk) (ptHfW D mpk) (ptSPW D mpk ct C x) (ptPUW D C x)
        (ptA0W D mpk) t0 s =
      (Enum.list (α := Col (setting D).τ)).flatMap fun c' =>
        encL D.N D.K (sePkOf D mpk C ct x (ExpLUT.progOf zr) (.inr (ptJh D t0 h0 s, c'))) := by
  have e := flatMap_range_eq (Enum.list (α := Col (setting D).τ))
    (fun c' => encL D.N D.K (sePkOf D mpk C ct x (ExpLUT.progOf zr) (.inr (ptJh D t0 h0 s, c'))))
    (fun j => ptInrPk D.b (ptND D) (ptZ2W D) (ptZLW' D) (ptGW D mpk ct) (ptAaW D mpk) (ptHfW D mpk)
        (ptSPW D mpk ct C x) (ptPUW D C x) (ptA0W D mpk) (ptSelVM D.b t0 s)
        (ptUnitVM (encRM D.N D.K 1) (encRM D.N D.K 0) (ptNC D) j))
    (fun m hm => ptInrPk_eq D zr mpk ct C x t0 h0 s m (by rw [← length_enumColS D]; exact hm))
  rw [length_enumColS] at e
  exact e

theorem flatMap_finRange_two {α : Type*} (f : Fin 2 → List α) :
    (List.finRange 2).flatMap f = f 0 ++ f 1 := by
  simp [List.finRange_succ]

/-- **The two loops write the stream of `sePkOf`.** -/
theorem ptStream_eq :
    (List.range D.mb).flatMap (ptInlPk D.b (ptNC D) (ptND D) (encRM D.N D.K 1) (encRM D.N D.K 0)
        (ptZ2W D) (ptZLW' D) (ptRA D zr) (ptRR0 D zr) (ptRZ D zr) (ptRRin D zr) (ptGW D mpk ct)
        (ptAaW D mpk) (ptHfW D mpk) (ptSPW D mpk ct C x) (ptPUW D C x) (ptA0W D mpk)) ++
      (List.range D.b).flatMap (fun t0 =>
        ptJPk D.b (ptNC D) (ptND D) (encRM D.N D.K 1) (encRM D.N D.K 0) (ptZ2W D) (ptZLW' D)
          (ptGW D mpk ct) (ptAaW D mpk) (ptHfW D mpk) (ptSPW D mpk ct C x) (ptPUW D C x)
          (ptA0W D mpk) t0 false ++
        ptJPk D.b (ptNC D) (ptND D) (encRM D.N D.K 1) (encRM D.N D.K 0) (ptZ2W D) (ptZLW' D)
          (ptGW D mpk ct) (ptAaW D mpk) (ptHfW D mpk) (ptSPW D mpk ct C x) (ptPUW D C x)
          (ptA0W D mpk) t0 true) =
    encL D.N D.K ((seRestL D).flatMap (sePkOf D mpk C ct x (ExpLUT.progOf zr))) := by
  have hs : (seRestL D).flatMap (sePkOf D mpk C ct x (ExpLUT.progOf zr)) =
      ((List.finRange D.mb).map Sum.inl).flatMap (sePkOf D mpk C ct x (ExpLUT.progOf zr)) ++
      ((Enum.list (α := Jh D × Col (setting D).τ)).map Sum.inr).flatMap
        (sePkOf D mpk C ct x (ExpLUT.progOf zr)) := List.flatMap_append
  rw [hs, encL_append, List.flatMap_map, List.flatMap_map, encL_flatMap', encL_flatMap']
  congr 1
  · have e := flatMap_range_eq (List.finRange D.mb)
      (fun w => encL D.N D.K (sePkOf D mpk C ct x (ExpLUT.progOf zr) (.inl w))) _
      (fun m hm => by
        rw [List.getElem_finRange]
        exact ptInlPk_eq D zr mpk ct C x m (by simpa using hm))
    rw [List.length_finRange] at e
    exact e
  · show _ = (((List.finRange D.b).product (List.finRange 2)).product
      (Enum.list (α := Col (setting D).τ))).flatMap _
    rw [product_flatMap, product_flatMap]
    have e := flatMap_range_eq (List.finRange D.b) (fun t0 => (List.finRange 2).flatMap fun s =>
        (Enum.list (α := Col (setting D).τ)).flatMap fun c' =>
          encL D.N D.K (sePkOf D mpk C ct x (ExpLUT.progOf zr) (.inr ((t0, s), c'))))
      (fun t0 =>
        ptJPk D.b (ptNC D) (ptND D) (encRM D.N D.K 1) (encRM D.N D.K 0) (ptZ2W D) (ptZLW' D)
          (ptGW D mpk ct) (ptAaW D mpk) (ptHfW D mpk) (ptSPW D mpk ct C x) (ptPUW D C x)
          (ptA0W D mpk) t0 false ++
        ptJPk D.b (ptNC D) (ptND D) (encRM D.N D.K 1) (encRM D.N D.K 0) (ptZ2W D) (ptZLW' D)
          (ptGW D mpk ct) (ptAaW D mpk) (ptHfW D mpk) (ptSPW D mpk ct C x) (ptPUW D C x)
          (ptA0W D mpk) t0 true)
      (fun m hm => by
        have hm' : m < D.b := by simpa using hm
        rw [ptJPk_eq D zr mpk ct C x m hm' false, ptJPk_eq D zr mpk ct C x m hm' true]
        simp only [List.getElem_finRange, Fin.cast_mk, flatMap_finRange_two]
        rfl)
    rw [List.length_finRange] at e
    exact e

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
