import PE.Impl.ExpLUT.Prog.RedKeyXMath
/-!
# `KGsim` on the VM (module 5): `X = simX M (h1Of mpk) A_F R̂` into register `16`

At the dimensions `D`: with the rows of `R̂` in register `rxRh` (`rowsWord R̂`, row-major over
`LCol × Col τ`), the helpers `H_k` (`k ∈ Fin b × Fin 2`, in `Enum` order) in `rxH`, the
automorphism count `gD D` in `rKc` (unary), the templates (`XIn`, `MulTmpl`), the row count
`2^b · m̄` of the `Ā` rows in `rxTs` and the word of `1` in `rxOne`,

  **`exec_simXC`**: `simXC` leaves `rowsWord (simX M (h1Of mpk) A_F R̂)` in register `16`,

exactly what `SimTryReady.rows` (`RedKeyTry`) asks for. The helper queue is the `H` field of the
public key (`xHL_eq`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib Matrix
open SigabaNeo.Lattices.Algo (encRM)

/-! ### Lists indexed by positions -/

theorem flatMap_range_getElem {α β : Type} (L : List α) (g : α → List β) (G : ℕ → List β)
    (hG : ∀ m (h : m < L.length), G m = g L[m]) :
    L.flatMap g = (List.range L.length).flatMap G := by
  induction L generalizing G with
  | nil => rfl
  | cons a L ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_cons,
      List.flatMap_map, hG 0 (by simp)]
    congr 1
    exact ih (fun m => G (m + 1)) fun m h => by rw [hG (m + 1) (by simpa using h)]; rfl

variable (D : Dims)

/-- The column of position `m` (`m < 2K`). -/
abbrev colAt (m : ℕ) (h : m < 2 * D.K) : Fin 2 × Fin D.K :=
  (Enum.list (α := Fin 2 × Fin D.K))[m]'(by rw [length_enum_col]; exact h)

/-- The `η` row `(i, (s, d), col m)` of a family indexed by positions. -/
def atB {β : Type} (z : β) (φ : Fin (2 ^ D.b) × Jh D × (Fin 2 × Fin D.K) → β)
    (i s d m : ℕ) : β :=
  if h : i < 2 ^ D.b ∧ s < D.b ∧ d < 2 ∧ m < 2 * D.K then
    φ (⟨i, h.1⟩, (⟨s, h.2.1⟩, ⟨d, h.2.2.1⟩), colAt D m h.2.2.2) else z

theorem flatMap_col {β : Type} (φ : Fin 2 × Fin D.K → List β) (G : ℕ → List β)
    (hG : ∀ m (h : m < 2 * D.K), G m = φ (colAt D m h)) :
    (Enum.list (α := Fin 2 × Fin D.K)).flatMap φ = (List.range (2 * D.K)).flatMap G := by
  rw [flatMap_range_getElem _ φ G (fun m h => hG m (by rwa [length_enum_col] at h)),
    length_enum_col]

/-- **The `η` rows, by positions.** -/
theorem enumB_flatMap {β : Type} (φ : Fin (2 ^ D.b) × Jh D × (Fin 2 × Fin D.K) → List β) :
    (Enum.list (α := Fin (2 ^ D.b) × Jh D × (Fin 2 × Fin D.K))).flatMap φ =
      (List.range (2 ^ D.b)).flatMap fun i => (List.range D.b).flatMap fun s =>
        (List.range (2 * D.K)).flatMap (atB D [] φ i s 0) ++
          (List.range (2 * D.K)).flatMap (atB D [] φ i s 1) := by
  show ((Enum.list (α := Fin (2 ^ D.b))).product (((Enum.list (α := Fin D.b)).product
    (Enum.list (α := Fin 2))).product (Enum.list (α := Fin 2 × Fin D.K)))).flatMap φ = _
  have h1 : (Enum.list (α := Fin (2 ^ D.b))).length = 2 ^ D.b := by simp [Enum.list]
  have h2 : (Enum.list (α := Fin D.b)).length = D.b := by simp [Enum.list]
  rw [product_flatMap, flatMap_range_getElem _ _ (fun i => (List.range D.b).flatMap fun s =>
      (List.range (2 * D.K)).flatMap (atB D [] φ i s 0) ++
        (List.range (2 * D.K)).flatMap (atB D [] φ i s 1)) (fun i hi => ?_), h1]
  symm
  rw [product_flatMap, product_flatMap, flatMap_range_getElem _ _ (fun s =>
      (List.range (2 * D.K)).flatMap (atB D [] φ i s 0) ++
        (List.range (2 * D.K)).flatMap (atB D [] φ i s 1)) (fun s hs => ?_), h2]
  simp only [enum_fin2, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hi' : i < 2 ^ D.b := by rwa [h1] at hi
  have hs' : s < D.b := by rwa [h2] at hs
  congr 1
  · exact (flatMap_col D _ _ fun m hm => by
      simp [atB, hi', hs', hm, Enum.list]).symm
  · exact (flatMap_col D _ _ fun m hm => by
      simp [atB, hi', hs', hm, Enum.list]).symm

/-! ### Unit rows and the tag `11` -/

theorem unitRow_colAt (m : ℕ) (h : m < 2 * D.K) :
    unitRow D (colAt D m h) = eV (N := D.N) (K := D.K) m := by
  funext c
  unfold unitRow eV colAt
  have hc : c ∈ Enum.list (α := Fin 2 × Fin D.K) := Enum.complete c
  by_cases e : (Enum.list (α := Fin 2 × Fin D.K))[m]'(by rw [length_enum_col]; exact h) = c
  · rw [if_pos e, if_pos]
    rw [← e, List.Nodup.idxOf_getElem Enum.nodup]
  · rw [if_neg e, if_neg]
    intro e'
    apply e
    have := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hc)
    simp only [e'] at this
    exact this

theorem xRow_ttW {N K : ℕ} (g : ℕ) (Hs : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (e e' v : Fin 2 × Fin K → Rq N K) : ∀ t j, xRow g Hs ttW e v t j = xRow g Hs ttW e' v t j
  | 0, _ => rfl
  | t + 1, j => by
    simp only [xRow]
    split_ifs
    · exact xRow_ttW g Hs e e' v t j
    · rw [xRow_ttW g Hs e e' v t (j - 2 ^ t)]
      simp [xStep, curW_ne_ttW]

theorem xOut_ttW {N K : ℕ} (g b : ℕ) (Hs : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (e e' v : Fin 2 × Fin K → Rq N K) : xOut g Hs ttW e v b = xOut g Hs ttW e' v b := by
  unfold xOut
  simp only [xRow_ttW g Hs e e' v]

/-! ### The orders of the rows -/

/-- The `Ā` rows of `R̂`, by position. -/
def rhA (Rh : LColS D → Fin 2 × Fin D.K → Rg D) (m : ℕ) : Fin 2 × Fin D.K → Rg D :=
  if h : m < (Enum.list (α := Fin (2 ^ D.b) × Wb D)).length then
    Rh (.inl (Enum.list (α := Fin (2 ^ D.b) × Wb D))[m]) else 0

/-- The `η` rows of `R̂`, by positions. -/
def rhB (Rh : LColS D → Fin 2 × Fin D.K → Rg D) (i s d m : ℕ) : Fin 2 × Fin D.K → Rg D :=
  atB D 0 (fun q => Rh (.inr q)) i s d m

theorem length_enumA : (Enum.list (α := Fin (2 ^ D.b) × Wb D)).length = 2 ^ D.b * D.mb := by
  show ((Enum.list (α := Fin (2 ^ D.b))).product (Enum.list (α := Fin D.mb))).length = _
  simp [Enum.list, List.product, List.length_flatMap, List.map_const', List.sum_replicate]

theorem atB_pos {β : Type} (z : β) (φ : Fin (2 ^ D.b) × Jh D × (Fin 2 × Fin D.K) → β)
    {i s d m : ℕ} (hi : i < 2 ^ D.b) (hs : s < D.b) (hd : d < 2) (hm : m < 2 * D.K) :
    atB D z φ i s d m = φ (⟨i, hi⟩, (⟨s, hs⟩, ⟨d, hd⟩), colAt D m hm) := by
  simp [atB, hi, hs, hd, hm]

/-- **The `R̂` stream** in the order of the drivers. -/
theorem rowsWord_rh (Rh : LColS D → Fin 2 × Fin D.K → Rg D) :
    rowsWord (N := D.N) (K := D.K) (α := LColS D) (β := Fin 2 × Fin D.K) Rh =
      (List.range (2 ^ D.b * D.mb)).flatMap (fun m => vecL (rhA D Rh m)) ++
        (List.range (2 ^ D.b)).flatMap (fun i => (List.range D.b).flatMap (xBlkS (rhB D Rh i))) := by
  unfold rowsWord
  rw [← List.flatMap]
  show ((Enum.list (α := Fin (2 ^ D.b) × Wb D)).map Sum.inl ++
    (Enum.list (α := Fin (2 ^ D.b) × Jh D × (Fin 2 × Fin D.K))).map Sum.inr).flatMap _ = _
  refine List.flatMap_append.trans (congrArg₂ (· ++ ·) ?_ ?_)
  · refine (List.flatMap_map ..).trans ?_
    rw [flatMap_range_getElem _ _ (fun m => vecL (rhA D Rh m)) (fun m h => by
      simp only [rhA, h, ↓reduceDIte]; rfl), length_enumA]
  · refine (List.flatMap_map ..).trans ?_
    rw [enumB_flatMap]
    refine List.flatMap_congr fun i hi => List.flatMap_congr fun s hs => ?_
    rw [List.mem_range] at hi hs
    unfold xBlkS
    congr 1
    · refine List.flatMap_congr fun m hm => ?_
      rw [List.mem_range] at hm
      rw [atB_pos D _ _ hi hs (show (0 : ℕ) < 2 by norm_num) hm, rhB,
        atB_pos D _ _ hi hs (show (0 : ℕ) < 2 by norm_num) hm]; rfl
    · refine List.flatMap_congr fun m hm => ?_
      rw [List.mem_range] at hm
      rw [atB_pos D _ _ hi hs (show (1 : ℕ) < 2 by norm_num) hm, rhB,
        atB_pos D _ _ hi hs (show (1 : ℕ) < 2 by norm_num) hm]; rfl

/-- **The rows of `X`** in the order of the drivers. -/
theorem rowsWord_simX_drive (mpk : MPKt D) (AF : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Rh : SimMat (Wb D) (Jh D) (setting D)) :
    rowsWord (N := D.N) (K := D.K) (α := PIdxS D) (β := ZIdxS D)
        (simX (helperMap D) (h1Of mpk) AF Rh) =
      (List.range (2 ^ D.b * D.mb)).flatMap (fun m =>
          xOut (gD D) (xHs D mpk) ttW 0 (fun c => -rhA D (fun ℓ c => Rh ℓ c) m c) D.b) ++
        ((List.range (2 ^ D.b)).flatMap (fun i => (List.range D.b).flatMap
          (xOutS (gD D) D.b (xHs D mpk) i (rhB D (fun ℓ c => Rh ℓ c) i))) ++
        (List.range (2 * D.K)).flatMap (fun m =>
          xOut (gD D) (xHs D mpk) ttW (eV m) (eV m) D.b)) := by
  rw [rowsWord_simX]
  show ((Enum.list (α := Fin (2 ^ D.b) × Wb D)).map Sum.inl ++
    ((Enum.list (α := Fin (2 ^ D.b) × Jh D × (Fin 2 × Fin D.K))).map Sum.inl ++
      (Enum.list (α := Fin 2 × Fin D.K)).map Sum.inr).map Sum.inr).flatMap _ = _
  refine List.flatMap_append.trans (congrArg₂ (· ++ ·) ?_ ?_)
  · refine (List.flatMap_map ..).trans ?_
    rw [flatMap_range_getElem _ _ (fun m =>
      xOut (gD D) (xHs D mpk) ttW 0 (fun c => -rhA D (fun ℓ c => Rh ℓ c) m c) D.b) (fun m h => by
        conv_lhs => rw [rhA, dif_pos h]
        rfl), length_enumA]
  · refine (List.flatMap_map ..).trans ?_
    refine List.flatMap_append.trans (congrArg₂ (· ++ ·) ?_ ?_)
    · refine (List.flatMap_map ..).trans ?_
      rw [enumB_flatMap]
      refine List.flatMap_congr fun i hi => List.flatMap_congr fun s hs => ?_
      rw [List.mem_range] at hi hs
      unfold xOutS
      congr 1
      · refine List.flatMap_congr fun m hm => ?_
        rw [List.mem_range] at hm
        rw [atB_pos D _ _ hi hs (show (0 : ℕ) < 2 by norm_num) hm, rhB,
          atB_pos D _ _ hi hs (show (0 : ℕ) < 2 by norm_num) hm, ← unitRow_colAt D m hm]
        rfl
      · refine List.flatMap_congr fun m hm => ?_
        rw [List.mem_range] at hm
        rw [atB_pos D _ _ hi hs (show (1 : ℕ) < 2 by norm_num) hm, rhB,
          atB_pos D _ _ hi hs (show (1 : ℕ) < 2 by norm_num) hm, ← unitRow_colAt D m hm]
        rfl
    · refine (List.flatMap_map ..).trans ?_
      refine flatMap_col D _ _ fun m hm => ?_
      rw [← unitRow_colAt D m hm, xOut_ttW _ _ _ (unitRow D (colAt D m hm)) 0]
      rfl

/-- **Module 5: `X` into register `16`.** With the rows of `R̂` in `rxRh`, the helpers in `rxH`
(`xHL_eq`), the inputs `XIn` (templates, `σ_g` count `gD D`), the `Ā` row count in `rxTs` and
the word of `1` in `rxOne`, `simXC` leaves the rows of `X = simX M (h1Of mpk) A_F R̂` in `16`. -/
theorem exec_simXC (mpk : MPKt D) (AF : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Rh : SimMat (Wb D) (Jh D) (setting D)) (w : St)
    (hI : XIn (gD D) D.b (xHs D mpk) (xHi D mpk) w)
    (hS : w rxRh = encL D.N D.K
      (rowsWord (α := LColS D) (β := Fin 2 × Fin D.K) (fun ℓ c => Rh ℓ c)))
    (hA : (w rxTs).length = 2 ^ D.b * D.mb) (hOne : w rxOne = encRM D.N D.K 1) :
    exec D.N D.K simXC w 16 = encL D.N D.K (rowsWord (α := PIdxS D) (β := ZIdxS D)
      (simX (helperMap D) (h1Of mpk) AF Rh)) ∧
    XIn (gD D) D.b (xHs D mpk) (xHi D mpk) (exec D.N D.K simXC w) := by
  have h := exec_simXC_gen D.N_pos D.K_pos ((odd_gD D).pos) w hI (2 ^ D.b * D.mb)
    (rhA D fun ℓ c => Rh ℓ c) (rhB D fun ℓ c => Rh ℓ c) (by rw [hS, rowsWord_rh]) hA hOne
  refine ⟨?_, h.2⟩
  rw [h.1, rowsWord_simX_drive, List.append_assoc]

/-- **The helper queue is the `H` field of the public key** (`H_k`, `k ∈ Fin b × Fin 2`, in `Enum`
order, each row-major). -/
theorem xHL_eq (mpk : MPKt D) :
    xHL (xHs D mpk) (xHi D mpk) (List.range D.b) =
      (Enum.list (α := Jh D)).flatMap fun k => matL (N := D.N) (K := D.K) fun a c => mpk.H k a c := by
  show _ = ((Enum.list (α := Fin D.b)).product (Enum.list (α := Fin 2))).flatMap _
  rw [product_flatMap, flatMap_range_getElem _ _ (fun t => matL (xHs D mpk t) ++ matL (xHi D mpk t))
    (fun t h => ?_)]
  · simp [xHL, Enum.list]
  · have ht : t < D.b := by simpa [Enum.list] using h
    simp only [enum_fin2, List.flatMap_cons, List.flatMap_nil, List.append_nil, xHs, xHi, ht,
      ↓reduceDIte]
    simp [Enum.list]

end AdvancedEncryption.ExpLUT.Prog
