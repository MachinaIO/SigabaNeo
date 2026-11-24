import PE.Impl.ExpLUT.Prog.DecSteps

/-!
# The words of the encodings represent the scheme's vectors and matrices (Dec, package F4)

The fixed-length encodings of `Words.lean` (`vecE`, `matE`, families over `Dig`) are
concatenations of the words of their entries in the order of `Enum`; as lists of words
(`vecWords`, `matWords`, `famVWords`, `famMWords₀/₁`) they represent (`RepV`, `RepM`, `RepFV`)
the encoded objects: positions `cidx`, `2K a + cidx c`, `didx` are the positions in `Enum`.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT Matrix

variable {D : Dims}

theorem getD_flatten_eqLen {α : Type*} {m : ℕ} (d : α) :
    ∀ (L : List (List α)), (∀ x ∈ L, x.length = m) → ∀ i j, i < L.length → j < m →
      L.flatten.getD (i * m + j) d = (L.getD i []).getD j d
  | [], _, i, j, hi, _ => by simp at hi
  | x :: L, hL, 0, j, _, hj => by
    rw [List.flatten_cons, zero_mul, zero_add, List.getD_append _ _ _ _ (by rw [hL x (by simp)]; exact hj)]
    simp
  | x :: L, hL, i + 1, j, hi, hj => by
    rw [List.flatten_cons, List.getD_append_right _ _ _ _ (by rw [hL x (by simp)]; nlinarith),
      hL x (by simp), show (i + 1) * m + j - m = i * m + j by rw [Nat.succ_mul]; omega,
      getD_flatten_eqLen d L (fun y hy => hL y (by simp [hy])) i j (by simp at hi; omega) hj]
    simp

theorem getD_map_product {β γ δ : Type*} (l₁ : List β) (l₂ : List γ) (g : β × γ → δ) (d : δ)
    {a b : ℕ} (ha : a < l₁.length) (hb : b < l₂.length) :
    ((l₁.product l₂).map g).getD (a * l₂.length + b) d = g (l₁[a], l₂[b]) := by
  have e : (l₁.product l₂).map g = (l₁.map fun x => l₂.map fun y => g (x, y)).flatten := by
    simp [List.product, List.map_flatten, List.flatMap, List.map_map, Function.comp_def]
  rw [e, getD_flatten_eqLen d _ (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx; simp) a b (by simpa using ha) hb]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb, Option.map_some, Option.getD_some]

theorem len_prod {β γ : Type*} (l₁ : List β) (l₂ : List γ) :
    (l₁.product l₂).length = l₁.length * l₂.length := List.length_product l₁ l₂

theorem dlen_col (K : ℕ) : (Enum.list (α := Col K)).length = 2 * K := by
  show ((List.finRange 2).product (List.finRange K)).length = 2 * K
  have := List.length_product (l₁ := List.finRange 2) (l₂ := List.finRange K)
  simp only [List.length_finRange] at this
  exact this

/-- `cidx` is the position in the enumeration. -/
theorem getD_map_col {δ : Type*} (K : ℕ) (g : Col K → δ) (d : δ) (c : Col K) :
    ((Enum.list (α := Col K)).map g).getD (cidx K c) d = g c := by
  show (((List.finRange 2).product (List.finRange K)).map g).getD _ d = _
  have := getD_map_product (List.finRange 2) (List.finRange K) g d (a := c.1.val) (b := c.2.val)
    (by simpa using c.1.isLt) (by simpa using c.2.isLt)
  simp only [List.length_finRange, List.getElem_finRange] at this
  rw [cidx, this]; rfl

/-- The words of a vector. -/
noncomputable def vecWords (v : Col D.K → Rg D) : List (List Bool) :=
  (Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (v c)

theorem flatten_vecWords (v : Col D.K → Rg D) : (vecWords v).flatten = (vecE D (Col D.K)).enc v := by
  show _ = ((Enum.list (α := Col D.K)).map v).flatMap _
  simp [vecWords, List.flatMap, List.map_map, Function.comp_def, rEnc_enc]

theorem repV_vecWords (v : Col D.K → Rg D) : RepV D (vecWords v) v where
  len := by rw [vecWords, List.length_map, dlen_col]
  wid x hx := by obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _
  val c := by rw [vecWords, getD_map_col, decRM_encRM D.K_pos]

/-! ### Matrices -/

/-- The words of a matrix (row-major). -/
noncomputable def matWords (M : Matrix (Fin 2) (Col D.K) (Rg D)) : List (List Bool) :=
  vecWords (M 0) ++ vecWords (M 1)

theorem flatten_matWords (M : Matrix (Fin 2) (Col D.K) (Rg D)) :
    (matWords M).flatten = (matE D (Fin 2) (Col D.K)).enc M := by
  show _ = ((Enum.list (α := Fin 2)).map M).flatMap _
  rw [matWords, List.flatten_append, flatten_vecWords, flatten_vecWords]
  show _ = List.flatMap (vecE D (Col D.K)).enc [M 0, M 1]
  simp [List.flatMap]

theorem repM_matWords (M : Matrix (Fin 2) (Col D.K) (Rg D)) : RepM D (matWords M) M :=
  RepM.of_rows (repV_vecWords _) (repV_vecWords _)

/-! ### Families over the digit positions -/

theorem dlen_dig (K : ℕ) : (Enum.list (α := Dig K)).length = 2 * (2 * K) * K := by
  show ((List.finRange 2).product ((Enum.list (α := Col K)).product (List.finRange K))).length = _
  rw [len_prod, len_prod, dlen_col]; simp; ring

theorem getElem_enum_col (K : ℕ) (c : Col K) (h : cidx K c < (Enum.list (α := Col K)).length) :
    (Enum.list (α := Col K))[cidx K c] = c := by
  have := getD_map_col K id c c
  rw [List.map_id, List.getD_eq_getElem _ _ h] at this
  exact this

theorem getD_map_dig {δ : Type*} (K : ℕ) (g : Dig K → δ) (x : δ) (d : Dig K) :
    ((Enum.list (α := Dig K)).map g).getD (didx K d) x = g d := by
  show (((List.finRange 2).product ((Enum.list (α := Col K)).product (List.finRange K))).map g).getD
    _ x = _
  have hc := cidx_lt d.2.1
  have hi := d.2.2.isLt
  have hl : ((Enum.list (α := Col K)).product (List.finRange K)).length = 2 * K * K := by
    rw [len_prod, dlen_col]; simp
  have hb : cidx K d.2.1 * K + d.2.2.val < ((Enum.list (α := Col K)).product (List.finRange K)).length := by
    rw [hl]; nlinarith
  have := getD_map_product (List.finRange 2) ((Enum.list (α := Col K)).product (List.finRange K)) g x
    (a := d.1.val) (b := cidx K d.2.1 * K + d.2.2.val) (by simpa using d.1.isLt) hb
  rw [hl] at this
  rw [didx, add_assoc, this]
  have inner := getD_map_product (Enum.list (α := Col K)) (List.finRange K) id d.2
    (a := cidx K d.2.1) (b := d.2.2.val) (by rw [dlen_col]; exact hc) (by simpa using hi)
  rw [List.map_id, List.getD_eq_getElem _ _ (by simpa [dlen_col] using hb)] at inner
  simp only [List.length_finRange] at inner
  rw [inner, getElem_enum_col]
  simp

/-- The words of a family of vectors. -/
noncomputable def famVWords (F : Dig D.K → Col D.K → Rg D) : List (List (List Bool)) :=
  (Enum.list (α := Dig D.K)).map fun d => vecWords (F d)

theorem repFV_famVWords (F : Dig D.K → Col D.K → Rg D) : RepFV D (famVWords F) F where
  len := by rw [famVWords, List.length_map, dlen_dig]
  ok v hv := by
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hv
    exact ⟨(repV_vecWords _).len, (repV_vecWords _).wid⟩
  mem d := by rw [famVWords, getD_map_dig]; exact repV_vecWords _

theorem famVW_famVWords (F : Dig D.K → Col D.K → Rg D) :
    famVW (famVWords F) = (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc F := by
  show _ = ((Enum.list (α := Dig D.K)).map F).flatMap _
  simp [famVW, famVWords, List.flatMap, List.map_map, Function.comp_def, flatten_vecWords]

/-- The row families of a family of matrices. -/
noncomputable def famMWords (Ad : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)) (r : Fin 2) :
    List (List (List Bool)) :=
  famVWords fun d => Ad d r

theorem famMW_famMWords (Ad : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)) :
    famMW (famMWords Ad 0) (famMWords Ad 1) =
      (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc Ad := by
  show _ = ((Enum.list (α := Dig D.K)).map Ad).flatMap _
  simp only [famMW, famMWords, famVWords, List.map_map, Function.comp_def, List.zipWith_map,
    List.zipWith_self, List.flatMap]
  congr 1
  erw [List.map_map]
  refine List.map_congr_left fun d _ => ?_
  show (vecWords (Ad d 0)).flatten ++ (vecWords (Ad d 1)).flatten = (matE D (Fin 2) (Col D.K)).enc (Ad d)
  rw [← flatten_matWords, matWords, List.flatten_append]

/-! ### Segments of position-indexed encodings -/

theorem seg_fun {β : Type} {n : ℕ} (e : FixedEnc β n) (f : Pos → β) (i : ℕ) (hi : i < 16) :
    (((FixedEnc.fun (α := Pos) e).enc f).drop (i * n)).take n = e.enc (f ⟨i, hi⟩) ∧
      (i + 1) * n ≤ ((FixedEnc.fun (α := Pos) e).enc f).length := by
  have hl : (Enum.list (α := Pos)).length = 16 := len_fin 16
  have h := FixedEnc.fun_block (α := Pos) e f i (by rw [hl]; exact hi)
  rw [Enum.getElem_fin] at h
  refine ⟨h, ?_⟩
  rw [FixedEnc.length, hl]; nlinarith

theorem read_bpOf (C : List Bool) (i : ℕ) (hi : i < 16) : (bpOf (progOf C)).read i = ⟨i, hi⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hi)

theorem len_vecE_col (v : Col D.K → Rg D) : ((vecE D (Col D.K)).enc v).length = 2 * D.K * (D.N * D.K) := by
  rw [FixedEnc.length, dlen_col]

/-! ### The helper streams -/

theorem dmap_finRange_val {α : Type*} (n : ℕ) (g : ℕ → α) :
    (List.finRange n).map (fun t => g t.val) = (List.range' 0 n).map g := by
  rw [← List.range_eq_range']
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp

theorem enc_jh {β : Type} {n : ℕ} (e : FixedEnc β n) (f : Jh D → β) :
    (FixedEnc.fun (α := Jh D) e).enc f =
      ((List.finRange D.b).map fun t => e.enc (f (t, 0)) ++ e.enc (f (t, 1))).flatten := by
  show ((Enum.list (α := Jh D)).map f).flatMap e.enc = _
  show (((List.finRange D.b).product (List.finRange 2)).map f).flatMap e.enc = _
  have h2 : List.finRange 2 = [0, 1] := rfl
  rw [h2]
  simp [List.product, List.flatMap, List.map_flatten, List.flatten_flatten, Function.comp_def]

theorem enc_finb {β : Type} {n : ℕ} (e : FixedEnc β n) (f : Fin D.b → β) :
    (FixedEnc.fun (α := Fin D.b) e).enc f = ((List.finRange D.b).map fun t => e.enc (f t)).flatten := by
  show ((List.finRange D.b).map f).flatMap e.enc = _
  simp [List.flatMap, Function.comp_def]

/-- The word data of the rounds from `mpk` and `ct`. -/
noncomputable def rdOf (mpk : MPKt D) (ct : CTt D) : RData where
  Hf t := if h : t < D.b then matWords (mpk.H (⟨t, h⟩, 0)) else []
  Hi t := if h : t < D.b then matWords (mpk.H (⟨t, h⟩, 1)) else []
  hf t := if h : t < D.b then vecWords (ct.h (⟨t, h⟩, 0)) else []
  hi t := if h : t < D.b then vecWords (ct.h (⟨t, h⟩, 1)) else []
  A0 t := if h : t < D.b then famMWords (mpk.Aaut ⟨t, h⟩) 0 else []
  A1 t := if h : t < D.b then famMWords (mpk.Aaut ⟨t, h⟩) 1 else []
  cw t := if h : t < D.b then famVWords (ct.caut ⟨t, h⟩) else []

theorem sH_rdOf (hb : D.b = 22) (mpk : MPKt D) (ct : CTt D) :
    sH (rdOf mpk ct) 0 = (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H := by
  refine Eq.trans ?_ (enc_jh (D := D) (matE D (Fin 2) (Col D.K)) mpk.H).symm
  rw [sH, show 22 - 0 = D.b by omega, ← dmap_finRange_val]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [rdOf, dif_pos t.isLt, Fin.eta]
  exact congrArg₂ (· ++ ·) (flatten_matWords _) (flatten_matWords _)

theorem sh_rdOf (hb : D.b = 22) (mpk : MPKt D) (ct : CTt D) :
    sh (rdOf mpk ct) 0 = (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc ct.h := by
  refine Eq.trans ?_ (enc_jh (D := D) (vecE D (Col D.K)) ct.h).symm
  rw [sh, show 22 - 0 = D.b by omega, ← dmap_finRange_val]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [rdOf, dif_pos t.isLt, Fin.eta]
  exact congrArg₂ (· ++ ·) (flatten_vecWords _) (flatten_vecWords _)

theorem sA_rdOf (hb : D.b = 22) (mpk : MPKt D) (ct : CTt D) :
    sA (rdOf mpk ct) 0 = (FixedEnc.fun (α := Fin D.b)
      (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut := by
  refine Eq.trans ?_ (enc_finb (D := D) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))
    mpk.Aaut).symm
  rw [sA, show 22 - 0 = D.b by omega, ← dmap_finRange_val]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [rdOf, dif_pos t.isLt, Fin.eta]
  exact famMW_famMWords _

theorem sc_rdOf (hb : D.b = 22) (mpk : MPKt D) (ct : CTt D) :
    sc (rdOf mpk ct) 0 = (FixedEnc.fun (α := Fin D.b)
      (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.caut := by
  refine Eq.trans ?_ (enc_finb (D := D) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))
    ct.caut).symm
  rw [sc, show 22 - 0 = D.b by omega, ← dmap_finRange_val]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [rdOf, dif_pos t.isLt, Fin.eta]
  exact famVW_famVWords _

/-- The word data of `mpk`, `ct` represent the helper data of the evaluation. -/
theorem rdOk_rdOf (hb : D.b = 22) (mpk : MPKt D) (ct : CTt D) :
    RDOk D (rdOf mpk ct) (evalPub (helperMap D) mpk).aut (evalData (helperMap D) mpk ct).aut := by
  intro t ht
  have ht' : t < D.b := by omega
  simp only [rdOf, dif_pos ht', evalPub, evalData, finExt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (if h : t < (setting D).b then mpk.H ((helperMap D).fwd ⟨t, h⟩) else 0) =
        mpk.H (⟨t, ht'⟩, 0) := dif_pos ht'
    rw [this]; exact repM_matWords _
  · have : (if h : t < (setting D).b then mpk.H ((helperMap D).inv ⟨t, h⟩) else 0) =
        mpk.H (⟨t, ht'⟩, 1) := dif_pos ht'
    rw [this]; exact repM_matWords _
  · have : (if h : t < (setting D).b then ct.h ((helperMap D).fwd ⟨t, h⟩) else 0) =
        ct.h (⟨t, ht'⟩, 0) := dif_pos ht'
    rw [this]; exact repV_vecWords _
  · have : (if h : t < (setting D).b then ct.h ((helperMap D).inv ⟨t, h⟩) else 0) =
        ct.h (⟨t, ht'⟩, 1) := dif_pos ht'
    rw [this]; exact repV_vecWords _
  · have : (if h : t < (setting D).b then mpk.Aaut ⟨t, h⟩ else 0) = mpk.Aaut ⟨t, ht'⟩ := dif_pos ht'
    rw [this]; exact repFV_famVWords _
  · have : (if h : t < (setting D).b then mpk.Aaut ⟨t, h⟩ else 0) = mpk.Aaut ⟨t, ht'⟩ := dif_pos ht'
    rw [this]; exact repFV_famVWords _
  · have : (if h : t < (setting D).b then ct.caut ⟨t, h⟩ else 0) = ct.caut ⟨t, ht'⟩ := dif_pos ht'
    rw [this]; exact repFV_famVWords _

/-! ### The registers of the evaluation from the encodings -/

theorem seg_fun' {β : Type} {n : ℕ} (e : FixedEnc β n) (f : Pos → β) (i : ℕ) (hi : i < 16) (m : ℕ)
    (hm : n = m) :
    (((FixedEnc.fun (α := Pos) e).enc f).drop (i * m)).take m = e.enc (f ⟨i, hi⟩) ∧
      (i + 1) * m ≤ ((FixedEnc.fun (α := Pos) e).enc f).length := by
  subst hm; exact seg_fun e f i hi

variable (D) in
/-- **The registers below `80`** holding the encodings of `mpk`, `ct`, the predicate word and the
constants of the evaluation. -/
structure DecRegs (mpk : MPKt D) (ct : CTt D) (C : List Bool) (w : St) : Prop where
  lc : LC D w
  r78 : w 78 = List.replicate (14 * 2 ^ 22) false
  hC : w 73 = C
  H : w 59 = (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H
  Aa : w 63 = (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc
    mpk.Aaut
  A0 : w 61 = (matE D (Fin 2) (Col D.K)).enc mpk.A0
  Ain : w 62 = (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc
    mpk.Ain
  a : w 60 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a
  h : w 67 = (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc ct.h
  ca : w 68 = (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.caut
  c0 : w 71 = (vecE D (Col D.K)).enc ct.c0
  cin : w 70 = (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.cin
  cb : w 69 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot

theorem evIn_of_regs (hb : D.b = 22) {mpk : MPKt D} {ct : CTt D} {C : List Bool} {w : St}
    (h : DecRegs D mpk ct C w) :
    EvIn D C (evalPub (helperMap D) mpk) (evalData (helperMap D) mpk ct) (rdOf mpk ct) w where
  lc := h.lc
  hC73 := h.hC
  r78 := h.r78
  ok := rdOk_rdOf hb mpk ct
  H := by rw [h.H, sH_rdOf hb]
  h := by rw [h.h, sh_rdOf hb]
  Aa := by rw [h.Aa, sA_rdOf hb]
  ca := by rw [h.ca, sc_rdOf hb]
  A0 := ⟨matWords mpk.A0, by rw [h.A0]; exact (flatten_matWords _).symm, repM_matWords _⟩
  c0 := ⟨vecWords ct.c0, by rw [h.c0]; exact (flatten_vecWords _).symm, repV_vecWords _⟩
  Ain i hi := by
    rw [read_bpOf C i hi, h.Ain]
    obtain ⟨s1, s2⟩ := seg_fun' (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))) mpk.Ain i hi
      (famMLen D) (by rw [dlen_dig, len_fin, dlen_col]; ring)
    exact ⟨famMWords (mpk.Ain ⟨i, hi⟩) 0, famMWords (mpk.Ain ⟨i, hi⟩) 1,
      s1.trans (famMW_famMWords _).symm, s2, repFV_famVWords _, repFV_famVWords _⟩
  cin i hi := by
    rw [read_bpOf C i hi, h.cin]
    obtain ⟨s1, s2⟩ := seg_fun' (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))) ct.cin i hi
      (2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))) (by rw [dlen_dig, dlen_col])
    exact ⟨famVWords (ct.cin ⟨i, hi⟩), s1.trans (famVW_famVWords _).symm, s2, repFV_famVWords _⟩
  a i hi := by
    rw [read_bpOf C i hi, h.a]
    obtain ⟨s1, s2⟩ := seg_fun' (vecE D (Col D.K)) mpk.a i hi (2 * D.K * (D.N * D.K))
      (by rw [dlen_col])
    exact ⟨vecWords (mpk.a ⟨i, hi⟩), s1.trans (flatten_vecWords _).symm, s2, repV_vecWords _⟩
  bot i hi := by
    rw [read_bpOf C i hi, h.cb]
    obtain ⟨s1, s2⟩ := seg_fun' (vecE D (Col D.K)) ct.cinBot i hi (2 * D.K * (D.N * D.K))
      (by rw [dlen_col])
    exact ⟨vecWords (ct.cinBot ⟨i, hi⟩), s1.trans (flatten_vecWords _).symm, s2, repV_vecWords _⟩

/-- **The evaluation of `Dec` from the encodings**: if the registers below `80` hold the encodings of
`mpk`, `ct` and the predicate word `C` (`DecRegs`), `devalC` leaves words representing
`A_F = keyPK (helperMap D) mpk (bpOf (progOf C))` on `177` and
`c_F = evalCiphertext (helperMap D) mpk (bpOf (progOf C)) ct` on `176`. -/
theorem exec_evalC_regs (hb : D.b = 22) {mpk : MPKt D} {ct : CTt D} {C : List Bool}
    (hC : C.length = predLen) {w : St} (h : DecRegs D mpk ct C w) :
    (∃ as, (exec D.N D.K devalC w) 177 = as.flatten ∧
        RepM D as (keyPK (helperMap D) mpk (bpOf (progOf C)))) ∧
      (∃ cs, (exec D.N D.K devalC w) 176 = cs.flatten ∧
        RepV D cs (evalCiphertext (helperMap D) mpk (bpOf (progOf C)) ct)) ∧
      ∀ r : Fin 200, r.val < 80 → (exec D.N D.K devalC w) r = w r :=
  exec_evalC_scheme hb hC (evIn_of_regs hb h)

end AdvancedEncryption.ExpLUT.Prog
