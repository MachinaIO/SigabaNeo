import PE.Impl.RingBTVW.Prog.WordLemmas

/-!
# The words of the reductions' values

The block outputs of the components, evaluated on the codec's words:

* `trW_rm`: the `Rᵢ` from their column-major word (`rmTEnc`) to their row-major word (`rmEnc`);
* the Ring-GSW ciphertexts `Ψᵢ = [B₀; c₀] Rᵢ + xᵢ G` (`psiA`, `psiMM`, `psiPre`, `gswG_word`,
  `psiSel`, `psiAdd`): the word of `A = [B₀; c₀]` is the join of the rows, `A Rᵢ` comes from one
  product of the stacked `Rᵢᵀ` with `Aᵀ` and a transpose, the shifts `xᵢ G` are blocks selected by
  the bits of the date;
* the bits `ψ_j` of the `Ψᵢ` (`psiBits`) and the rows `ψ_j G̲` (`psiRows`);
* `hash_rows`: `V W_j + E_j` for the binary matrices `W_j` (the public keys `B_j` and the
  encodings `c_j`);
* `wMat_word`: the word of the `W_j`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape Matrix
  AdvancedEncryption.RingBTVW.Fresh
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ}

theorem len_fin (n : ℕ) : (Enum.list (α := Fin n)).length = n := by simp [Enum.list]

theorem len_col : (Enum.list (α := RingBTVW.Fresh.Col k)).length = 2 * k := by
  rw [Enum.length_prod]; simp [Enum.list]

theorem enum_fin_one : (Enum.list (α := Fin 1)) = [0] := by simp [Enum.list, List.finRange_succ]

theorem enum_fin_two : (Enum.list (α := Fin 2)) = [0, 1] := by
  simp [Enum.list, List.finRange_succ]

theorem flatMap_replicate {α : Type} (l : List α) (c : ℕ) :
    (l.flatMap fun _ => List.replicate c false) = List.replicate (l.length * c) false := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, ih, List.length_cons, ← List.replicate_add]; congr 1; ring

theorem matEnc_zero {r s : Type} [Enum r] [Enum s] :
    (RingBTVW.matEnc (N := N) (K := K) r s).enc 0 =
      List.replicate ((Enum.list (α := r)).length * ((Enum.list (α := s)).length * (N * K))) false := by
  rw [matEnc_flatMap]
  simp only [Matrix.zero_apply, enc_zeroR, zeroW, flatMap_replicate]

theorem length_matEnc {r s : Type} [Enum r] [Enum s] (M : Matrix r s (Rq N K)) :
    ((RingBTVW.matEnc (N := N) (K := K) r s).enc M).length =
      (Enum.list (α := r)).length * ((Enum.list (α := s)).length * (N * K)) :=
  (RingBTVW.matEnc (N := N) (K := K) r s).length M

/-! ### Lengths as numerals -/

theorem trW_fun_matEnc' {α r s : Type} [Enum α] [Enum r] [Enum s] {m a b : ℕ}
    (hm : (Enum.list (α := α)).length = m) (ha : (Enum.list (α := r)).length = a)
    (hb : (Enum.list (α := s)).length = b) (F : α → Matrix r s (Rq N K)) :
    trW m a b (N * K) 0 ((FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) r s)).enc F) =
      (FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) s r)).enc fun i => (F i)ᵀ := by
  subst hm ha hb; exact trW_fun_matEnc F

theorem trW_matEnc' {r s : Type} [Enum r] [Enum s] {a b : ℕ} (ha : (Enum.list (α := r)).length = a)
    (hb : (Enum.list (α := s)).length = b) (M : Matrix r s (Rq N K)) :
    trW 1 a b (N * K) 0 ((RingBTVW.matEnc (N := N) (K := K) r s).enc M) =
      (RingBTVW.matEnc (N := N) (K := K) s r).enc Mᵀ := by
  subst ha hb; exact trW_matEnc M

theorem matEnc_mul' {r s t : Type} [Enum r] [Enum s] [Enum t] [Fintype s] {a b e : ℕ}
    (ha : (Enum.list (α := r)).length = a) (hb : (Enum.list (α := s)).length = b)
    (he : (Enum.list (α := t)).length = e) (M : Matrix r s (Rq N K)) (M' : Matrix s t (Rq N K)) :
    matMulW N K a b e ((RingBTVW.matEnc (N := N) (K := K) r s).enc M)
        ((RingBTVW.matEnc (N := N) (K := K) s t).enc M') =
      (RingBTVW.matEnc (N := N) (K := K) r t).enc (M * M') := by
  subst ha hb he; exact matEnc_mul M M'

theorem matAddW_fun_matEnc' {α r s : Type} [Enum α] [Enum r] [Enum s] {m a b : ℕ}
    (hm : (Enum.list (α := α)).length = m) (ha : (Enum.list (α := r)).length = a)
    (hb : (Enum.list (α := s)).length = b) (F G : α → Matrix r s (Rq N K)) :
    matAddW N K (m * (a * b)) ((FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) r s)).enc F)
        ((FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) r s)).enc G) =
      (FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) r s)).enc (F + G) := by
  subst hm ha hb; exact matAddW_fun_matEnc F G

theorem matAddW_matEnc' {r s : Type} [Enum r] [Enum s] {a b : ℕ}
    (ha : (Enum.list (α := r)).length = a) (hb : (Enum.list (α := s)).length = b)
    (M M' : Matrix r s (Rq N K)) :
    matAddW N K (a * b) ((RingBTVW.matEnc (N := N) (K := K) r s).enc M)
        ((RingBTVW.matEnc (N := N) (K := K) r s).enc M') =
      (RingBTVW.matEnc (N := N) (K := K) r s).enc (M + M') := by
  subst ha hb; exact matAddW_matEnc M M'

/-! ### The matrices `Rᵢ` -/

variable (c : Conf N K k)

theorem rmTEnc_eq (Rm : Fin nA → Matrix (Fin c.d) (RingBTVW.Fresh.Col k) (Rg N K)) :
    (rmTEnc c).enc Rm =
      (FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) (RingBTVW.Fresh.Col k) (Fin c.d))).enc fun i => (Rm i)ᵀ := by
  rw [rmTEnc, funEnc_flatMap, funEnc_flatMap]; rfl

/-- **The `Rᵢ` row-major.** -/
theorem trW_rm (Rm : Fin nA → Matrix (Fin c.d) (RingBTVW.Fresh.Col k) (Rg N K)) :
    trW nA (2 * k) c.d (N * K) 0 ((rmTEnc c).enc Rm) = (rmEnc c).enc Rm := by
  rw [rmTEnc_eq, trW_fun_matEnc' (len_fin nA) len_col (len_fin c.d)]
  rfl

/-! ### The Ring-GSW ciphertexts -/

/-- The word of `A = [B₀; c₀]` is the join of the rows. -/
theorem psiA (B₀ c₀ : Matrix (Fin 1) (Fin c.d) (Rg N K)) :
    takeD (c.d * (N * K)) ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc B₀) ++
        takeD (c.d * (N * K)) ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc c₀) ++
        takeD 0 [] =
      (RingBTVW.matEnc (N := N) (K := K) (Fin 2) (Fin c.d)).enc (gswPK B₀ c₀) := by
  have hl : ∀ M : Matrix (Fin 1) (Fin c.d) (Rg N K),
      ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc M).length = c.d * (N * K) := by
    intro M; rw [length_matEnc, len_fin, len_fin, one_mul]
  rw [takeD_of_length' (hl B₀), takeD_of_length' (hl c₀)]
  simp only [matEnc_flatMap, enum_fin_one, enum_fin_two, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, gswPK, Matrix.of_apply]
  simp [takeD]

/-- The stacked transposes: the row `(i, c)` is the column `c` of `Rᵢ`. -/
def stkR (Rm : Fin nA → Matrix (Fin c.d) (RingBTVW.Fresh.Col k) (Rg N K)) :
    Matrix (Fin nA × RingBTVW.Fresh.Col k) (Fin c.d) (Rg N K) :=
  Matrix.of fun ic a => Rm ic.1 a ic.2

theorem rmTEnc_stk (Rm : Fin nA → Matrix (Fin c.d) (RingBTVW.Fresh.Col k) (Rg N K)) :
    (rmTEnc c).enc Rm =
      (RingBTVW.matEnc (N := N) (K := K) (Fin nA × RingBTVW.Fresh.Col k) (Fin c.d)).enc (stkR c Rm) := by
  rw [rmTEnc_eq, funEnc_flatMap, matEnc_flatMap]
  show _ = ((Enum.list (α := Fin nA)).product (Enum.list (α := RingBTVW.Fresh.Col k))).flatMap _
  rw [Algo.flatMap_product]
  simp only [matEnc_flatMap]
  rfl

/-- **One product for all the `A Rᵢ`**: the stacked `Rᵢᵀ` times `Aᵀ`. -/
theorem psiMM (A : Matrix (Fin 2) (Fin c.d) (Rg N K))
    (Rm : Fin nA → Matrix (Fin c.d) (RingBTVW.Fresh.Col k) (Rg N K)) :
    matMulW N K (nA * (2 * k)) c.d 2 ((rmTEnc c).enc Rm)
        (trW 1 2 c.d (N * K) 0 ((RingBTVW.matEnc (N := N) (K := K) (Fin 2) (Fin c.d)).enc A)) =
      (RingBTVW.matEnc (N := N) (K := K) (Fin nA × RingBTVW.Fresh.Col k) (Fin 2)).enc (stkR c Rm * Aᵀ) := by
  rw [trW_matEnc' (len_fin 2) (len_fin c.d), rmTEnc_stk,
    matEnc_mul' (by rw [Enum.length_prod, len_fin, len_col]) (len_fin c.d) (len_fin 2)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The `A Rᵢ`** from the product, by transposes. -/
theorem psiPre (A : Matrix (Fin 2) (Fin c.d) (Rg N K))
    (Rm : Fin nA → Matrix (Fin c.d) (RingBTVW.Fresh.Col k) (Rg N K)) :
    trW nA (2 * k) 2 (N * K) 0
        ((RingBTVW.matEnc (N := N) (K := K) (Fin nA × RingBTVW.Fresh.Col k) (Fin 2)).enc (stkR c Rm * Aᵀ)) =
      (FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k))).enc
        fun i => A * Rm i := by
  have h := trW_fun_matEnc' (N := N) (K := K) (len_fin nA) len_col (len_fin 2)
    (fun i => (Matrix.of fun (cc : RingBTVW.Fresh.Col k) (r : Fin 2) => (stkR c Rm * Aᵀ) (i, cc) r))
  have hw : (RingBTVW.matEnc (N := N) (K := K) (Fin nA × RingBTVW.Fresh.Col k) (Fin 2)).enc (stkR c Rm * Aᵀ) =
      (FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) (RingBTVW.Fresh.Col k) (Fin 2))).enc
        (fun i => (Matrix.of fun (cc : RingBTVW.Fresh.Col k) (r : Fin 2) => (stkR c Rm * Aᵀ) (i, cc) r)) := by
    rw [matEnc_flatMap, funEnc_flatMap]
    show ((Enum.list (α := Fin nA)).product (Enum.list (α := RingBTVW.Fresh.Col k))).flatMap _ = _
    rw [Algo.flatMap_product]
    simp only [matEnc_flatMap, Matrix.of_apply]
  rw [hw]
  erw [h]
  refine congrArg _ (funext fun i => Matrix.ext fun r cc => ?_)
  simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.mul_apply, stkR]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

variable (hk : 2 ^ K < 2 ^ k)

theorem gadW_eq_matEnc :
    gadW N K k = (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k)).enc (Sdw (N := N) hk).Γ₁.G := by
  rw [Algo.matEnc_row, gadW_enc hk.le]
  rfl

theorem gswG_apply (a : Fin 2) (cc : RingBTVW.Fresh.Col k) :
    (Sdw (N := N) hk).Γ.G a cc =
      if a = cc.1 then algebraMap (ZMod (2 ^ K)) (Rq N K) (2 ^ (cc.2 : ℕ)) else 0 := rfl

theorem gswG1_apply (cc : RingBTVW.Fresh.Col k) :
    (Sdw (N := N) hk).Γ₁.G 0 cc =
      if 0 = cc.1 then algebraMap (ZMod (2 ^ K)) (Rq N K) (2 ^ (cc.2 : ℕ)) else 0 := rfl

theorem enum_col_eq : (Enum.list (α := RingBTVW.Fresh.Col k)) =
    (Enum.list (α := Fin 2)).product (Enum.list (α := Fin k)) := rfl

/-- The entries `2^c₂` of the gadget, as words. -/
def gHalf (N K k : ℕ) : List Bool :=
  (List.finRange k).flatMap fun c₂ : Fin k =>
    (ringEnc N K).enc (algebraMap (ZMod (2 ^ K)) (Rq N K) (2 ^ (c₂ : ℕ)))

theorem length_gHalf : (gHalf N K k).length = k * (N * K) := by
  rw [gHalf, length_flatMap_const _ (N * K) _ (fun _ => (ringEnc N K).length _), List.length_finRange]

theorem zeros_k : ((List.finRange k).flatMap fun _ : Fin k => (ringEnc N K).enc (0 : Rq N K)) =
    List.replicate (k * (N * K)) false := by
  simp only [enc_zeroR, zeroW]
  rw [flatMap_replicate, List.length_finRange]

include hk in
theorem gadW_split : gadW N K k = gHalf N K k ++ List.replicate (k * (N * K)) false := by
  have h0 : ∀ c₂ : Fin k, (Sdw (N := N) hk).Γ₁.G 0 (0, c₂) =
      algebraMap (ZMod (2 ^ K)) (Rq N K) (2 ^ (c₂ : ℕ)) := fun c₂ => by
    rw [gswG1_apply]; exact if_pos rfl
  have h1 : ∀ c₂ : Fin k, (Sdw (N := N) hk).Γ₁.G 0 (1, c₂) = 0 := fun c₂ => by
    rw [gswG1_apply]; exact if_neg (by simp)
  rw [gadW_eq_matEnc hk, matEnc_flatMap, enum_fin_one, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, enum_col_eq, Algo.flatMap_product, enum_fin_two, List.flatMap_cons,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [h0, h1]
  rw [← zeros_k]
  rfl

/-- **The word of the Ring-GSW gadget**: `G̲`, then `k` zero entries and the first half of `G̲`. -/
theorem gswG_word :
    takeD (2 * k * (N * K)) (gadW N K k) ++ takeD (k * (N * K)) [] ++ takeD (k * (N * K)) (gadW N K k) =
      (RingBTVW.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc (Sdw (N := N) hk).Γ.G := by
  have h00 : ∀ c₂ : Fin k, (Sdw (N := N) hk).Γ.G 0 (0, c₂) =
      algebraMap (ZMod (2 ^ K)) (Rq N K) (2 ^ (c₂ : ℕ)) := fun c₂ => by
    rw [gswG_apply]; exact if_pos rfl
  have h01 : ∀ c₂ : Fin k, (Sdw (N := N) hk).Γ.G 0 (1, c₂) = 0 := fun c₂ => by
    rw [gswG_apply]; exact if_neg (by simp)
  have h10 : ∀ c₂ : Fin k, (Sdw (N := N) hk).Γ.G 1 (0, c₂) = 0 := fun c₂ => by
    rw [gswG_apply]; exact if_neg (by simp)
  have h11 : ∀ c₂ : Fin k, (Sdw (N := N) hk).Γ.G 1 (1, c₂) =
      algebraMap (ZMod (2 ^ K)) (Rq N K) (2 ^ (c₂ : ℕ)) := fun c₂ => by
    rw [gswG_apply]; exact if_pos rfl
  have hlen : (gadW N K k).length = 2 * k * (N * K) := by
    rw [gadW_split hk, List.length_append, length_gHalf, List.length_replicate]; ring
  rw [takeD_of_length' hlen, takeD_nil, gadW_split hk, takeD_eq_take (by simp [length_gHalf]),
    List.take_left' length_gHalf, matEnc_flatMap, enum_fin_two, List.flatMap_cons,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, enum_col_eq, Algo.flatMap_product,
    Algo.flatMap_product, enum_fin_two, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [h00, h01, h10, h11]
  rw [← zeros_k]
  simp only [List.append_assoc]
  rfl

theorem encAttr_map (x : PUniv.Attr) : encAttr x = (List.finRange nA).map (attrBits x) := by
  apply List.ext_getElem (by rw [List.length_map, List.length_finRange]; exact length_encAttr x)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_finRange]
  show _ = (encAttr x).getD i false
  simp [List.getD_eq_getElem?_getD, h1]

theorem bitR_smul_word {r s : Type} [Enum r] [Enum s] {L : ℕ}
    (hL : (Enum.list (α := r)).length * ((Enum.list (α := s)).length * (N * K)) = L)
    (b : Bool) (M : Matrix r s (Rq N K)) :
    takeD L (if b then (RingBTVW.matEnc (N := N) (K := K) r s).enc M else []) =
      (RingBTVW.matEnc (N := N) (K := K) r s).enc (bitR (R := Rq N K) b • M) := by
  subst hL
  cases b
  · simp [bitR, takeD_nil, matEnc_zero]
  · simp [bitR, takeD_of_length' (length_matEnc M)]

set_option maxRecDepth 20000 in
/-- **The shifts `xᵢ G`**: blocks selected by the bits of the attribute. -/
theorem psiSel (x : PUniv.Attr) :
    selW nA (2 * (2 * k) * (N * K)) (encAttr x)
        ((RingBTVW.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc (Sdw (N := N) hk).Γ.G) [] =
      (FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k))).enc
        fun i => bitR (R := Rg N K) (attrBits x i) • (Sdw (N := N) hk).Γ.G := by
  have h := selW_map (List.finRange nA) (attrBits x) (2 * (2 * k) * (N * K))
    ((RingBTVW.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc (Sdw (N := N) hk).Γ.G) []
  simp only [List.length_finRange] at h
  rw [encAttr_map, h, funEnc_flatMap]
  exact congrArg₂ List.flatMap (funext fun i => bitR_smul_word (by rw [len_fin, len_col]; ring) _ _)
    rfl

/-- **The `Ψᵢ`**: the sum of the `A Rᵢ` and the shifts. -/
theorem psiAdd (F G : Fin nA → Matrix (Fin 2) (RingBTVW.Fresh.Col k) (Rg N K)) :
    matAddW N K (nA * (2 * (2 * k)))
        ((FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k))).enc F)
        ((FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k))).enc G) =
      (FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k))).enc
        fun i => F i + G i := by
  exact matAddW_fun_matEnc' (len_fin nA) (len_fin 2) len_col F G

end AdvancedEncryption.RingBTVW.Prog
