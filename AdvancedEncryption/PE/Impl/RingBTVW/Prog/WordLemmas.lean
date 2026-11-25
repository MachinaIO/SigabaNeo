import PE.Impl.RingBTVW.Prog.Blocks
import SigabaNeo.Lib.Lattices.Algo.BoxWords

/-!
# The word functions of the blocks on encodings

The blocks of `PE.Impl.RingBTVW.Prog.Blocks` compute word functions (`trW`, `selW`, `hashW`,
`matMulW`, `matAddW`). Here they are evaluated on concatenations of fixed-length blocks
(`List.flatMap`), the shape of the codec's encodings (`FixedEnc.fun`, `matEnc`):

* `trW_flatMap`: the transposes of block matrices given as nested `flatMap`s;
* `trW_fun_matEnc`: on the word of a family of matrices, the word of their transposes;
* `matEnc_eq_matW`, `matEnc_mul` (`matMulW`), `matAddW_matEnc`, `matAddW_flatMap`: products and
  entrywise sums of matrices on any enumerated index types;
* `selW_map`: blocks selected by a list of bits;
* `hashW_flatMap`: sums selected by bits.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape Matrix

/-! ### Blocks of concatenations -/

section Lists

variable {α β γ : Type}

theorem length_flatMap_const (g : α → List Bool) (c : ℕ) (l : List α) (h : ∀ x, (g x).length = c) :
    (l.flatMap g).length = l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.flatMap_cons, List.length_append, ih, h, List.length_cons]; ring

theorem drop_flatMap_const (g : α → List Bool) (c : ℕ) (h : ∀ x, (g x).length = c) :
    ∀ (l : List α) (i : ℕ), (l.flatMap g).drop (i * c) = (l.drop i).flatMap g
  | [], i => by simp
  | x :: l, 0 => by simp
  | x :: l, i + 1 => by
    rw [List.flatMap_cons, Nat.succ_mul, Nat.add_comm, ← List.drop_drop,
      List.drop_left' (h x), drop_flatMap_const g c h l i]
    rfl

/-- The block `i` of a concatenation, followed by the rest. -/
theorem drop_flatMap_append (g : α → List Bool) (c : ℕ) (h : ∀ x, (g x).length = c) (l : List α)
    (rest : List Bool) {i : ℕ} (hi : i < l.length) :
    (l.flatMap g ++ rest).drop (i * c) = g l[i] ++ ((l.drop (i + 1)).flatMap g ++ rest) := by
  have hle : i * c ≤ (l.flatMap g).length := by
    rw [length_flatMap_const g c l h]; exact Nat.mul_le_mul_right c hi.le
  rw [List.drop_append_of_le_length hle, drop_flatMap_const g c h, List.drop_eq_getElem_cons hi,
    List.flatMap_cons, List.append_assoc]

theorem takeD_flatMap_append (g : α → List Bool) (c : ℕ) (h : ∀ x, (g x).length = c) (l : List α)
    (rest : List Bool) {i : ℕ} (hi : i < l.length) :
    takeD c ((l.flatMap g ++ rest).drop (i * c)) = g l[i] := by
  rw [drop_flatMap_append g c h l rest hi, takeD_eq_take (by simp [h]), List.take_left' (h _)]

theorem takeD_flatMap (g : α → List Bool) (c : ℕ) (h : ∀ x, (g x).length = c) (l : List α)
    {i : ℕ} (hi : i < l.length) : takeD c ((l.flatMap g).drop (i * c)) = g l[i] := by
  have := takeD_flatMap_append g c h l [] hi
  rwa [List.append_nil] at this

/-- **One transpose** of a block matrix given row by row. -/
theorem matTW_flatMap (li : List β) (lj : List γ) (f : β → γ → List Bool) (B : ℕ)
    (hf : ∀ i j, (f i j).length = B) (rest : List Bool) :
    matTW li.length lj.length B ((li.flatMap fun i => lj.flatMap fun j => f i j) ++ rest) =
      lj.flatMap fun j => li.flatMap fun i => f i j := by
  have hrow : ∀ i, (lj.flatMap fun j => f i j).length = lj.length * B := fun i =>
    length_flatMap_const _ B lj (hf i)
  unfold matTW colTW
  conv_rhs => rw [Algo.flatMap_eq_concatN lj]
  refine concatN_congr fun j hj => ?_
  rw [dite_eq_left_of_eq_true (eq_true hj)]
  conv_rhs => rw [Algo.flatMap_eq_concatN li]
  refine concatN_congr fun i hi => ?_
  rw [dite_eq_left_of_eq_true (eq_true hi), List.drop_drop, Nat.add_comm, ← List.drop_drop,
    show i * (lj.length * B) = i * (lj.length * B) from rfl,
    drop_flatMap_append _ (lj.length * B) hrow li rest hi]
  exact takeD_flatMap_append (f li[i]) B (hf li[i]) lj _ hj

/-- **The transposes of block matrices** given as nested concatenations. -/
theorem trW_flatMap {δ : Type} (lq : List δ) (li : List β) (lj : List γ) (f : δ → β → γ → List Bool)
    (B Z : ℕ) (hf : ∀ q i j, (f q i j).length = B) :
    trW lq.length li.length lj.length B Z
        (lq.flatMap fun q => li.flatMap fun i => lj.flatMap fun j => f q i j) =
      lq.flatMap fun q => (lj.flatMap fun j => li.flatMap fun i => f q i j) ++
        List.replicate Z false := by
  have hmat : ∀ q, (li.flatMap fun i => lj.flatMap fun j => f q i j).length =
      li.length * (lj.length * B) := fun q =>
    length_flatMap_const _ _ li fun i => length_flatMap_const _ B lj (hf q i)
  unfold trW
  conv_rhs => rw [Algo.flatMap_eq_concatN lq]
  refine concatN_congr fun q hq => ?_
  rw [dite_eq_left_of_eq_true (eq_true hq)]
  have := drop_flatMap_append _ _ hmat lq [] hq
  rw [List.append_nil] at this
  rw [this, matTW_flatMap li lj (f lq[q]) B (hf lq[q])]

end Lists

/-! ### Matrices on enumerated index types -/

section Mat

variable {N K : ℕ}

theorem matEnc_flatMap {r s : Type} [Enum r] [Enum s] (M : Matrix r s (Rq N K)) :
    (RingBTVW.matEnc (N := N) (K := K) r s).enc M =
      (Enum.list (α := r)).flatMap fun i => (Enum.list (α := s)).flatMap fun j =>
        (ringEnc N K).enc (M i j) := by
  show ((Enum.list (α := r)).map (fun i => (M i : s → Rq N K))).flatMap
    (fun row => ((Enum.list (α := s)).map row).flatMap (ringEnc N K).enc) = _
  rw [List.flatMap_map]
  congr 1
  funext i
  rw [List.flatMap_map]

theorem funEnc_flatMap {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) (F : α → β) :
    (FixedEnc.fun e).enc F = (Enum.list (α := α)).flatMap fun a => e.enc (F a) := by
  rw [fun_enc_eq, List.flatMap_map]

/-- **The transposes of a family of matrices.** -/
theorem trW_fun_matEnc {α r s : Type} [Enum α] [Enum r] [Enum s] (F : α → Matrix r s (Rq N K)) :
    trW (Enum.list (α := α)).length (Enum.list (α := r)).length (Enum.list (α := s)).length (N * K) 0
        ((FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) r s)).enc F) =
      (FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) s r)).enc fun a => (F a)ᵀ := by
  rw [funEnc_flatMap, funEnc_flatMap]
  simp only [matEnc_flatMap]
  rw [trW_flatMap _ _ _ (fun q i j => (ringEnc N K).enc (F q i j)) (N * K) 0
    (fun _ _ _ => (ringEnc N K).length _)]
  simp [Matrix.transpose_apply]

/-- A single matrix as a family indexed by `Fin 1`. -/
theorem fun_fin_one {β : Type} {n : ℕ} (e : FixedEnc β n) (F : Fin 1 → β) :
    (FixedEnc.fun (α := Fin 1) e).enc F = e.enc (F 0) := by
  rw [funEnc_flatMap]; simp [Enum.list, List.finRange_succ]

/-- **The transpose of a matrix.** -/
theorem trW_matEnc {r s : Type} [Enum r] [Enum s] (M : Matrix r s (Rq N K)) :
    trW 1 (Enum.list (α := r)).length (Enum.list (α := s)).length (N * K) 0
        ((RingBTVW.matEnc (N := N) (K := K) r s).enc M) =
      (RingBTVW.matEnc (N := N) (K := K) s r).enc Mᵀ := by
  have := trW_fun_matEnc (α := Fin 1) (fun _ => M)
  rwa [fun_fin_one, fun_fin_one, show (Enum.list (α := Fin 1)).length = 1 by simp [Enum.list]] at this

/-- The positions of an enumeration. -/
theorem enum_bijective {s : Type} [Enum s] :
    Function.Bijective (fun x : Fin (Enum.list (α := s)).length => (Enum.list (α := s))[x]) := by
  refine ⟨fun x y h => Fin.ext ((Enum.nodup (α := s)).getElem_inj_iff.mp h), fun y => ?_⟩
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem (Enum.complete (α := s) y)
  exact ⟨⟨i, hi⟩, e⟩

/-- **The word of a matrix on enumerated types** is the word of its reindexing by positions. -/
theorem matEnc_eq_matW {r s : Type} [Enum r] [Enum s] (M : Matrix r s (Rq N K)) :
    (RingBTVW.matEnc (N := N) (K := K) r s).enc M =
      matW N K (Enum.list (α := r)).length (Enum.list (α := s)).length
        (Matrix.of fun (p : Fin (Enum.list (α := r)).length) (q : Fin (Enum.list (α := s)).length) =>
          M (Enum.list (α := r))[p] (Enum.list (α := s))[q]) := by
  rw [matEnc_flatMap, matW, concatN_mul]
  conv_lhs => rw [Algo.flatMap_eq_concatN]
  refine concatN_congr fun i hi => ?_
  rw [dite_eq_left_of_eq_true (eq_true hi)]
  conv_lhs => rw [Algo.flatMap_eq_concatN]
  refine concatN_congr fun j hj => ?_
  have hij : i * (Enum.list (α := s)).length + j <
      (Enum.list (α := r)).length * (Enum.list (α := s)).length := by
    have := Nat.mul_le_mul_right (Enum.list (α := s)).length
      (show i + 1 ≤ (Enum.list (α := r)).length from hi)
    rw [Nat.add_mul] at this; omega
  rw [dite_eq_left_of_eq_true (eq_true hj), dite_eq_left_of_eq_true (eq_true hij)]
  have h1 : (i * (Enum.list (α := s)).length + j) / (Enum.list (α := s)).length = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : (i * (Enum.list (α := s)).length + j) % (Enum.list (α := s)).length = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [Matrix.of_apply, Fin.getElem_fin, h1, h2]

/-- **Products of matrices on enumerated types.** -/
theorem matEnc_mul {r s t : Type} [Enum r] [Enum s] [Enum t] [Fintype s] (M : Matrix r s (Rq N K))
    (M' : Matrix s t (Rq N K)) :
    matMulW N K (Enum.list (α := r)).length (Enum.list (α := s)).length (Enum.list (α := t)).length
        ((RingBTVW.matEnc (N := N) (K := K) r s).enc M) ((RingBTVW.matEnc (N := N) (K := K) s t).enc M') =
      (RingBTVW.matEnc (N := N) (K := K) r t).enc (M * M') := by
  rw [matEnc_eq_matW, matEnc_eq_matW, matEnc_eq_matW, matMulW_enc]
  congr 1
  refine Matrix.ext fun p q => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  apply Fintype.sum_bijective _ (enum_bijective (s := s))
  intro x; rfl

/-- **Entrywise sums of matrices on enumerated types.** -/
theorem matAddW_matEnc {r s : Type} [Enum r] [Enum s] (M M' : Matrix r s (Rq N K)) :
    matAddW N K ((Enum.list (α := r)).length * (Enum.list (α := s)).length)
        ((RingBTVW.matEnc (N := N) (K := K) r s).enc M) ((RingBTVW.matEnc (N := N) (K := K) r s).enc M') =
      (RingBTVW.matEnc (N := N) (K := K) r s).enc (M + M') := by
  rw [matEnc_eq_matW, matEnc_eq_matW, matEnc_eq_matW, matAddW_enc]
  rfl

theorem rget_append_left {x₁ x₂ : List Bool} {L₁ p : ℕ} (h : x₁.length = L₁ * (N * K)) (hp : p < L₁) :
    rget N K p (x₁ ++ x₂) = rget N K p x₁ := by
  have hle : p * (N * K) + N * K ≤ x₁.length := by
    rw [h]; have := Nat.mul_le_mul_right (N * K) (show p + 1 ≤ L₁ from hp); rw [Nat.add_mul] at this
    omega
  rw [rget, rget, block, block, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

theorem rget_append_right {x₁ x₂ : List Bool} {L₁ : ℕ} (h : x₁.length = L₁ * (N * K)) (p : ℕ) :
    rget N K (L₁ + p) (x₁ ++ x₂) = rget N K p x₂ := by
  rw [rget, rget, block, block, Nat.add_mul, ← List.drop_drop, ← h, List.drop_left]

theorem matAddW_append {L₁ L₂ : ℕ} {x₁ x₂ y₁ y₂ : List Bool} (hx : x₁.length = L₁ * (N * K))
    (hy : y₁.length = L₁ * (N * K)) :
    matAddW N K (L₁ + L₂) (x₁ ++ x₂) (y₁ ++ y₂) = matAddW N K L₁ x₁ y₁ ++ matAddW N K L₂ x₂ y₂ := by
  unfold matAddW
  rw [concatN_add]
  congr 1
  · exact concatN_congr fun p hp => by rw [rget_append_left hx hp, rget_append_left hy hp]
  · exact concatN_congr fun p _ => by rw [rget_append_right hx, rget_append_right hy]

/-- **Entrywise sums of concatenations** of words of `L` entries. -/
theorem matAddW_flatMap {α : Type} (X Y : α → List Bool) (L : ℕ) (hX : ∀ a, (X a).length = L * (N * K))
    (hY : ∀ a, (Y a).length = L * (N * K)) : ∀ l : List α,
    matAddW N K (l.length * L) (l.flatMap X) (l.flatMap Y) = l.flatMap fun a => matAddW N K L (X a) (Y a)
  | [] => by simp [matAddW, concatN]
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.length_cons, Nat.succ_mul,
      Nat.add_comm, matAddW_append (hX a) (hY a), matAddW_flatMap X Y L hX hY l]

/-- **Entrywise sums of families of matrices.** -/
theorem matAddW_fun_matEnc {α r s : Type} [Enum α] [Enum r] [Enum s] (F G : α → Matrix r s (Rq N K)) :
    matAddW N K ((Enum.list (α := α)).length * ((Enum.list (α := r)).length * (Enum.list (α := s)).length))
        ((FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) r s)).enc F)
        ((FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) r s)).enc G) =
      (FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) r s)).enc (F + G) := by
  have hl : ∀ M : Matrix r s (Rq N K), ((RingBTVW.matEnc (N := N) (K := K) r s).enc M).length =
      (Enum.list (α := r)).length * (Enum.list (α := s)).length * (N * K) := fun M => by
    rw [(RingBTVW.matEnc (N := N) (K := K) r s).length]; ring
  rw [funEnc_flatMap, funEnc_flatMap, funEnc_flatMap, matAddW_flatMap _ _ _ (fun a => hl (F a))
    (fun a => hl (G a))]
  simp only [matAddW_matEnc, Pi.add_apply]

end Mat

/-! ### Selections -/

section Sel

theorem hd_drop_map {α : Type} (b : α → Bool) (l : List α) {j : ℕ} (hj : j < l.length) :
    hd ((l.map b).drop j) = b l[j] := by
  rw [← List.map_drop, List.drop_eq_getElem_cons hj]; rfl

/-- **Blocks selected by a list of bits.** -/
theorem selW_map {α : Type} (l : List α) (b : α → Bool) (B : ℕ) (X Y : List Bool) :
    Tape.selW l.length B (l.map b) X Y = l.flatMap fun q => takeD B (if b q then X else Y) := by
  unfold Tape.selW
  rw [Algo.flatMap_eq_concatN]
  refine concatN_congr fun j hj => ?_
  rw [dite_eq_left_of_eq_true (eq_true hj), hd_drop_map b l hj]

end Sel

/-! ### Sums selected by bits -/

section Hash

variable {N K : ℕ}

/-- **The selected sum on words.** -/
theorem csum_eq (d : ℕ) (ws : List Bool) (g : ℕ → Bool) (hg : ∀ a < d, hd (ws.drop a) = g a)
    (v : Fin d → Rq N K) : ∀ a ≤ d,
    csum N K a ws ((List.finRange d).flatMap fun a => (ringEnc N K).enc (v a)) =
      (ringEnc N K).enc (∑ a' ∈ Finset.range a, if h : a' < d then (if g a' then v ⟨a', h⟩ else 0) else 0)
  | 0, _ => by simp [csum, enc_zeroR]
  | a + 1, ha => by
    have hv : takeD (N * K) (((List.finRange d).flatMap fun a => (ringEnc N K).enc (v a)).drop
        (a * (N * K))) = (ringEnc N K).enc (v ⟨a, ha⟩) := by
      rw [takeD_flatMap _ _ (fun _ => (ringEnc N K).length _) _ (by simpa using ha)]
      simp
    have ha' : a < d := ha
    rw [csum, Finset.sum_range_succ, dite_eq_left_of_eq_true (eq_true ha'), hg a ha',
      csum_eq d ws g hg v a (by omega)]
    cases g a
    · simp
    · simp only [ite_true]
      rw [hv, addRW_enc]

/-- **Sums selected by bits** over a family of entries. -/
theorem hashW_flatMap {α : Type} (l : List α) (d : ℕ) (g : α → Fin d → Bool) (v : Fin d → Rq N K)
    (e : α → Rq N K) :
    hashW l.length d N K (l.flatMap fun q => (List.finRange d).map (g q))
        ((List.finRange d).flatMap fun a => (ringEnc N K).enc (v a))
        (l.flatMap fun q => (ringEnc N K).enc (e q)) =
      l.flatMap fun q => (ringEnc N K).enc ((∑ a, if g q a then v a else 0) + e q) := by
  unfold hashW
  conv_rhs => rw [Algo.flatMap_eq_concatN l]
  refine concatN_congr fun p hp => ?_
  rw [dite_eq_left_of_eq_true (eq_true hp)]
  have hw : (l.flatMap fun q => (List.finRange d).map (g q)).drop (p * d) =
      ((List.finRange d).map (g l[p])) ++ ((l.drop (p + 1)).flatMap fun q => (List.finRange d).map (g q)) := by
    have := drop_flatMap_append (fun q => (List.finRange d).map (g q)) d (fun _ => by simp) l [] hp
    rwa [List.append_nil, List.append_nil] at this
  have he := takeD_flatMap (fun q => (ringEnc N K).enc (e q)) (N * K) (fun _ => (ringEnc N K).length _) l hp
  rw [he, hw, csum_eq d _ (fun a => if h : a < d then g l[p] ⟨a, h⟩ else false) (fun a ha => by
      rw [List.drop_append_of_le_length (by simp; omega), dite_eq_left_of_eq_true (eq_true ha)]
      have : a < ((List.finRange d).map (g l[p])).length := by simpa using ha
      rw [List.drop_eq_getElem_cons this]
      simp) v d le_rfl, addRW_enc]
  congr 2
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [a.isLt]

end Hash

end AdvancedEncryption.RingBTVW.Prog
