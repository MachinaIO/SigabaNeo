import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VMRing

/-!
# Matrix routines of the Mersenne VM

Routines on fixed registers (the library's registers are `40 … 63`; callers use `0 … 39`):

* `digAccC`: `acc += Σ_{i<K} e_i · digit_i(x)` for the next `K` elements `e_i` of the stream `rDE`
  (`exec_digAccC`).
-/

namespace SigabaNeo.Tape

namespace MVM

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo Prog Cslib

variable {N K : ℕ}

/-- **One step of a VM code**: the head instruction of a `seq` is executed (registers named by
`vmreg`, instruction lemmas, decided register equalities). -/
macro "vm_step" : tactic => `(tactic| (rw [exec_seq]; simp only [vmreg, exec_cp, exec_clr, exec_tl,
  exec_mvR, exec_mv, exec_drop, exec_add, exec_sub, exec_mul, exec_neg, exec_aut, exec_rho, exec_rot,
  exec_dig, exec_nop, Fin.reduceEq, ite_false, ite_true, false_or, or_false, or_self]))

/-! ### Registers -/

/-- The canonical word of `0`. -/
@[simp, vmreg] abbrev rZ : Fin 64 := 63
/-- The unary template of `K`. -/
@[simp, vmreg] abbrev rTK : Fin 64 := 62
/-- The unary template of `K − 1`. -/
@[simp, vmreg] abbrev rTK1 : Fin 64 := 61
/-- `digAccC`: the accumulator, the element, the stream. -/
@[simp, vmreg] abbrev rDA : Fin 64 := 49
@[simp, vmreg] abbrev rDX : Fin 64 := 48
@[simp, vmreg] abbrev rDE : Fin 64 := 47
/-- `digAccC`: work. -/
@[simp, vmreg] abbrev rDn : Fin 64 := 54
@[simp, vmreg] abbrev rUp : Fin 64 := 53
@[simp, vmreg] abbrev rEl : Fin 64 := 52
@[simp, vmreg] abbrev rDg : Fin 64 := 51
@[simp, vmreg] abbrev rPr : Fin 64 := 50

/-! ### The digit accumulation -/

/-- One round: `e := pop rDE`, `acc += e · digit_m(x)` (`m = K − 1 − |rDn|`). -/
def digAccBody : Code :=
  .seq (.cp rUp rTK1) <| .seq (.drop rUp rDn) <| .seq (.mvR rEl rDE) <|
  .seq (.op .dig rDg rDX rUp) <| .seq (.op .mul rPr rEl rDg) (.op .add rDA rDA rPr)

/-- **`acc += Σ_{i<K} e_i · digit_i(x)`.** -/
def digAccC : Code := .seq (.cp rDn rTK) <| .seq (.cp rEl rZ) <| .seq (.rep rDn digAccBody) <|
  .seq (.clr rUp) <| .seq (.clr rEl) <| .seq (.clr rDg) (.clr rPr)

theorem drop_range_map (f : ℕ → Rq N K) {m n : ℕ} (h : m < n) :
    ((List.range n).map f).drop m = f m :: ((List.range n).map f).drop (m + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

/-- **The digit accumulation.** -/
theorem exec_digAccC (hK : 0 < K) (w : St) (acc x : Rq N K) (f : ℕ → Rq N K)
    (rest : List (Rq N K)) (hA : w rDA = encRM N K acc) (hX : w rDX = encRM N K x)
    (hE : w rDE = encL N K ((List.range K).map f ++ rest))
    (hTK : w rTK = List.replicate K false) (hTK1 : w rTK1 = List.replicate (K - 1) false)
    (hZ : w rZ = encRM N K 0) :
    exec N K digAccC w = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update w rDn []) rUp []) rEl []) rDg []) rPr [])
      rDA (encRM N K (acc + ∑ i ∈ Finset.range K, f i * binaryDigit x i))) rDE (encL N K rest) := by
  simp only [digAccC, exec_seq, exec_cp, exec_clr]
  rw [show Function.update w rDn (w rTK) rZ = w rZ from Function.update_of_ne (by decide) _ _]
  set w1 := Function.update (Function.update w rDn (w rTK)) rEl (w rZ)
  have h1 : (w1 rDn).length = K := by simp [w1, hTK]
  have key := exec_rep_inv (N := N) (K := K) rDn digAccBody (by decide)
    (fun m w' => w' rDA = encRM N K (acc + ∑ i ∈ Finset.range m, f i * binaryDigit x i) ∧
      w' rDE = encL N K (((List.range K).map f).drop m ++ rest) ∧ w' rDX = encRM N K x ∧
      w' rTK1 = List.replicate (K - 1) false ∧ ∃ y, w' rEl = encRM N K y) w1
    ⟨by simp [w1, hA], by simp [w1, hE], by simp [w1, hX], by simp [w1, hTK1],
      ⟨0, by simp [w1, hZ]⟩⟩ ?_
  · rw [h1] at key
    have hdn := exec_rep_inv (N := N) (K := K) rDn digAccBody (by decide)
      (fun m w' => w' rDn = (w1 rDn).drop m) w1 rfl (fun m w' _ _ h => by
        rw [exec_writes digAccBody _ rDn (by decide), Function.update_self, h, List.tail_drop])
    rw [h1, List.drop_of_length_le (by simp [w1, hTK])] at hdn
    funext r
    by_cases hDE : r = rDE
    · subst hDE; simp [key.2.1, List.drop_of_length_le]
    by_cases hDA : r = rDA
    · subst hDA; simp [key.1]
    simp only [Function.update_apply, hDE, hDA, if_false]
    split_ifs with h1 h2 h3 h4 h5
    · rfl
    · rfl
    · rfl
    · rfl
    · subst h5; exact hdn
    · rw [exec_writes _ _ r (by
        simp only [Code.writes, digAccBody, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        and_intros <;> (intro e; subst e; simp at *))]
      simp [w1, Function.update_apply, h5, h3]
  · intro m w' hm hP hc
    rw [h1] at hm
    obtain ⟨hA', hE', hX', hT', y, hy⟩ := hP
    have hc' : w1 rDn = List.replicate K false := by simp [w1, hTK]
    rw [hc'] at hc
    rw [drop_range_map f hm, List.cons_append, encL_cons] at hE'
    have hlen : K - 1 - (K - m - 1) = m := by omega
    simp only [digAccBody, exec_seq, exec_cp, exec_drop, exec_mvR, exec_dig, exec_mul, exec_add]
    simp [hA', hE', hX', hT', hy, hc, takeD_encRM, canonW_dig hK, canonW_mul hK,
      canonW_add hK, Finset.sum_range_succ, hlen, add_assoc]

end MVM

end SigabaNeo.Tape

namespace SigabaNeo.Tape

namespace MVM

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Encode Prog Cslib

variable {N K : ℕ}

/-! ### Matrices as lists -/

/-- A function on `Fin K` as a function on `ℕ` (zero outside). -/
def extF (K : ℕ) (g : Fin K → Rq N K) (i : ℕ) : Rq N K := if h : i < K then g ⟨i, h⟩ else 0

theorem finRange_map_eq (g : Fin K → Rq N K) :
    (List.finRange K).map g = (List.range K).map (extF K g) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, extF]
  rw [dif_pos (by simpa using h1)]
  rfl

theorem sum_extF (g : Fin K → Rq N K) (x : Rq N K) :
    ∑ i ∈ Finset.range K, extF K g i * binaryDigit x i = ∑ i : Fin K, g i * binaryDigit x i := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [extF, i.isLt]

theorem enum_fin2 : (Enum.list (α := Fin 2)) = [0, 1] := rfl

theorem product_flatMap {α β γ : Type} (l₁ : List α) (l₂ : List β) (f : α × β → List γ) :
    (l₁.product l₂).flatMap f = l₁.flatMap fun a => l₂.flatMap fun b => f (a, b) := by
  simp [List.product, List.flatMap_assoc, List.flatMap_map]

theorem product_map {α β γ : Type} (l₁ : List α) (l₂ : List β) (f : α × β → γ) :
    (l₁.product l₂).map f = l₁.flatMap fun a => l₂.map fun b => f (a, b) := by
  simp [List.product, List.map_flatMap]
  rfl

/-- A row segment `(A a (r, i))_{i < K}`. -/
def segL (A : Fin 2 → Fin 2 × Fin K → Rq N K) (a r : Fin 2) : List (Rq N K) :=
  (List.finRange K).map fun i => A a (r, i)

@[simp] theorem length_segL (A : Fin 2 → Fin 2 × Fin K → Rq N K) (a r : Fin 2) :
    (segL A a r).length = K := by simp [segL]

/-- **The list of a `2 × 2K` matrix**, row-major (the order of `FixedEnc.fun`). -/
def matL (A : Fin 2 → Fin 2 × Fin K → Rq N K) : List (Rq N K) :=
  (Enum.list (α := Fin 2)).flatMap fun a => (Enum.list (α := Fin 2 × Fin K)).map (A a)

theorem rowL_eq (f : Fin 2 × Fin K → Rq N K) :
    (Enum.list (α := Fin 2 × Fin K)).map f =
      (List.finRange K).map (fun i => f (0, i)) ++ (List.finRange K).map (fun i => f (1, i)) := by
  show ((Enum.list (α := Fin 2)).product (Enum.list (α := Fin K))).map f = _
  rw [product_map, enum_fin2]
  simp
  rfl

theorem matL_eq (A : Fin 2 → Fin 2 × Fin K → Rq N K) :
    matL A = segL A 0 0 ++ segL A 0 1 ++ (segL A 1 0 ++ segL A 1 1) := by
  rw [matL, enum_fin2]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, rowL_eq]
  rfl

@[simp] theorem length_matL (A : Fin 2 → Fin 2 × Fin K → Rq N K) : (matL A).length = 4 * K := by
  rw [matL_eq]; simp; ring

/-- The digit matrices `A_{(r, j, i)}`. -/
abbrev DigI (K : ℕ) := Fin 2 × (Fin 2 × Fin K) × Fin K

/-- **The list of a family of digit matrices** (the order of `FixedEnc.fun`). -/
def adL (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) : List (Rq N K) :=
  (Enum.list (α := DigI K)).flatMap fun d => matL (Ad d)

theorem adL_eq (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) :
    adL Ad = (Enum.list (α := Fin 2)).flatMap fun r => (Enum.list (α := Fin 2 × Fin K)).flatMap
      fun j => (List.finRange K).flatMap fun i => matL (Ad (r, j, i)) := by
  show ((Enum.list (α := Fin 2)).product ((Enum.list (α := Fin 2 × Fin K)).product
    (Enum.list (α := Fin K)))).flatMap _ = _
  rw [product_flatMap]
  congr 1; funext r
  rw [product_flatMap]
  rfl

/-- **`EvalPK` of `Mul` with binary digits**:
`A'_{a, j} = Σ_{(r, i)} Σ_c Ad_{(r, j, i)}[a, c] · digit_{c.2}(A_{c.1, (r, i)})`. -/
def mulPKm (A : Fin 2 → Fin 2 × Fin K → Rq N K) (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) :
    Fin 2 → Fin 2 × Fin K → Rq N K :=
  fun a j => ∑ ri : Fin 2 × Fin K, ∑ c : Fin 2 × Fin K,
    Ad (ri.1, j, ri.2) a c * binaryDigit (A c.1 ri) c.2

/-! ### `mulPK`: registers and the inner body -/

@[simp, vmreg] abbrev rMA : Fin 64 := 32
@[simp, vmreg] abbrev rMAd : Fin 64 := 33
@[simp, vmreg] abbrev rMOut : Fin 64 := 34
@[simp, vmreg] abbrev rS : Fin 64 := 35
@[simp, vmreg] abbrev rS2 : Fin 64 := 36
@[simp, vmreg] abbrev rAc0 : Fin 64 := 37
@[simp, vmreg] abbrev rAc1 : Fin 64 := 38
@[simp, vmreg] abbrev rCo0 : Fin 64 := 39
@[simp, vmreg] abbrev rCo1 : Fin 64 := 40
@[simp, vmreg] abbrev rRo0 : Fin 64 := 41
@[simp, vmreg] abbrev rRo1 : Fin 64 := 42
@[simp, vmreg] abbrev rX0 : Fin 64 := 43
@[simp, vmreg] abbrev rX1 : Fin 64 := 44
@[simp, vmreg] abbrev rCj : Fin 64 := 45
@[simp, vmreg] abbrev rCi : Fin 64 := 46
@[simp, vmreg] abbrev rTmp : Fin 64 := 55
@[simp, vmreg] abbrev rT2K : Fin 64 := 57
@[simp, vmreg] abbrev rT4KNK : Fin 64 := 58
@[simp, vmreg] abbrev rT2KNK : Fin 64 := 59
@[simp, vmreg] abbrev rTKNK : Fin 64 := 60

/-- One element of each row stream, then the four digit accumulations of a digit matrix. -/
def iBody : Code :=
  .seq (.cp rX0 rZ) <| .seq (.mvR rX0 rCo0) <| .seq (.cp rX1 rZ) <| .seq (.mvR rX1 rCo1) <|
  .seq (.cp rDE rMAd) <|
  .seq (.cp rDA rAc0) <| .seq (.cp rDX rX0) <| .seq digAccC <| .seq (.cp rDX rX1) <| .seq digAccC <|
  .seq (.cp rAc0 rDA) <|
  .seq (.cp rDA rAc1) <| .seq (.cp rDX rX0) <| .seq digAccC <| .seq (.cp rDX rX1) <| .seq digAccC <|
  .seq (.cp rAc1 rDA) (.cp rMAd rDE)

/-- The contribution of one digit matrix `M` to the accumulator of row `a`, with the column
entries `X 0`, `X 1`. -/
def digRow (M : Fin 2 → Fin 2 × Fin K → Rq N K) (X : Fin 2 → Rq N K) (a : Fin 2) : Rq N K :=
  ∑ c : Fin 2 × Fin K, M a c * binaryDigit (X c.1) c.2

theorem digRow_eq (M : Fin 2 → Fin 2 × Fin K → Rq N K) (X : Fin 2 → Rq N K) (a : Fin 2) :
    digRow M X a = ∑ i ∈ Finset.range K, extF K (fun i => M a (0, i)) i * binaryDigit (X 0) i +
      ∑ i ∈ Finset.range K, extF K (fun i => M a (1, i)) i * binaryDigit (X 1) i := by
  rw [sum_extF, sum_extF, digRow, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem exec_iBody (hK : 0 < K) (w : St) (u0 u1 a0 a1 : Rq N K) (U0 U1 rest : List (Rq N K))
    (M : Fin 2 → Fin 2 × Fin K → Rq N K)
    (hC0 : w rCo0 = encL N K (u0 :: U0)) (hC1 : w rCo1 = encL N K (u1 :: U1))
    (hA0 : w rAc0 = encRM N K a0) (hA1 : w rAc1 = encRM N K a1)
    (hE : w rMAd = encL N K (matL M ++ rest))
    (hTK : w rTK = List.replicate K false) (hTK1 : w rTK1 = List.replicate (K - 1) false)
    (hZ : w rZ = encRM N K 0) :
    exec N K iBody w rAc0 = encRM N K (a0 + digRow M ![u0, u1] 0) ∧
    exec N K iBody w rAc1 = encRM N K (a1 + digRow M ![u0, u1] 1) ∧
    exec N K iBody w rCo0 = encL N K U0 ∧ exec N K iBody w rCo1 = encL N K U1 ∧
    exec N K iBody w rMAd = encL N K rest := by
  rw [matL_eq, segL, segL, segL, segL, finRange_map_eq, finRange_map_eq, finRange_map_eq,
    finRange_map_eq] at hE
  simp only [List.append_assoc] at hE
  set f00 := extF K fun i => M 0 (0, i)
  set f01 := extF K fun i => M 0 (1, i)
  set f10 := extF K fun i => M 1 (0, i)
  set f11 := extF K fun i => M 1 (1, i)
  unfold iBody
  vm_step; vm_step; vm_step; vm_step; vm_step; vm_step; vm_step
  rw [exec_seq, exec_digAccC hK _ a0 u0 f00 ((List.range K).map f01 ++ ((List.range K).map f10 ++
    ((List.range K).map f11 ++ rest))) (by simp [hA0]) (by simp [hZ, hC0]) (by simp [hE])
    (by simp [hTK]) (by simp [hTK1]) (by simp [hZ])]
  vm_step
  rw [exec_seq, exec_digAccC hK _ (a0 + ∑ i ∈ Finset.range K, f00 i * binaryDigit u0 i) u1 f01
    ((List.range K).map f10 ++ ((List.range K).map f11 ++
    rest)) (by simp) (by simp [hZ, hC1]) (by simp) (by simp [hTK]) (by simp [hTK1]) (by simp [hZ])]
  vm_step; vm_step; vm_step
  rw [exec_seq, exec_digAccC hK _ a1 u0 f10 ((List.range K).map f11 ++ rest) (by simp [hA1])
    (by simp [hZ, hC0]) (by simp) (by simp [hTK]) (by simp [hTK1]) (by simp [hZ])]
  vm_step
  rw [exec_seq, exec_digAccC hK _ (a1 + ∑ i ∈ Finset.range K, f10 i * binaryDigit u0 i) u1 f11 rest (by simp) (by simp [hZ, hC1]) (by simp)
    (by simp [hTK]) (by simp [hTK1]) (by simp [hZ])]
  vm_step
  simp [hC0, hC1, digRow_eq, add_assoc, f00, f01, f10, f11]

/-! ### The `ι` loop -/

theorem drop_range_cons {m n : ℕ} (h : m < n) : (List.range n).drop m = m :: (List.range n).drop (m + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

theorem iBody_writes_rCi : iBody.writes rCi = false := by decide

/-- **The `ι` loop**: `K` rounds of `iBody`. -/
theorem exec_iLoop (hK : 0 < K) (w : St) (s0 s1 : Rq N K) (U0 U1 : ℕ → Rq N K)
    (M : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (rest : List (Rq N K))
    (hCi : w rCi = List.replicate K false)
    (hC0 : w rCo0 = encL N K ((List.range K).map U0)) (hC1 : w rCo1 = encL N K ((List.range K).map U1))
    (hA0 : w rAc0 = encRM N K s0) (hA1 : w rAc1 = encRM N K s1)
    (hE : w rMAd = encL N K ((List.range K).flatMap (fun i => matL (M i)) ++ rest))
    (hTK : w rTK = List.replicate K false) (hTK1 : w rTK1 = List.replicate (K - 1) false)
    (hZ : w rZ = encRM N K 0) :
    exec N K (.rep rCi iBody) w rAc0 =
      encRM N K (s0 + ∑ i ∈ Finset.range K, digRow (M i) ![U0 i, U1 i] 0) ∧
    exec N K (.rep rCi iBody) w rAc1 =
      encRM N K (s1 + ∑ i ∈ Finset.range K, digRow (M i) ![U0 i, U1 i] 1) ∧
    exec N K (.rep rCi iBody) w rMAd = encL N K rest := by
  have key := exec_rep_inv (N := N) (K := K) rCi iBody iBody_writes_rCi
    (fun m w' => w' rAc0 = encRM N K (s0 + ∑ i ∈ Finset.range m, digRow (M i) ![U0 i, U1 i] 0) ∧
      w' rAc1 = encRM N K (s1 + ∑ i ∈ Finset.range m, digRow (M i) ![U0 i, U1 i] 1) ∧
      w' rCo0 = encL N K (((List.range K).map U0).drop m) ∧
      w' rCo1 = encL N K (((List.range K).map U1).drop m) ∧
      w' rMAd = encL N K (((List.range K).drop m).flatMap (fun i => matL (M i)) ++ rest) ∧
      w' rTK = List.replicate K false ∧ w' rTK1 = List.replicate (K - 1) false ∧
      w' rZ = encRM N K 0) w
    ⟨by simp [hA0], by simp [hA1], by simp [hC0], by simp [hC1], by simp [hE], hTK, hTK1, hZ⟩ ?_
  · rw [hCi, List.length_replicate] at key
    obtain ⟨k1, k2, -, -, k5, -⟩ := key
    refine ⟨k1, k2, ?_⟩
    rw [k5, List.drop_of_length_le (by simp)]
    rfl
  · intro m w' hm hP _
    rw [hCi, List.length_replicate] at hm
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hP
    rw [drop_range_map U0 hm] at h3
    rw [drop_range_map U1 hm] at h4
    rw [drop_range_cons hm, List.flatMap_cons, List.append_assoc] at h5
    have hb := exec_iBody hK (Function.update w' rCi (w' rCi).tail) (U0 m) (U1 m) _ _ _ _
      (((List.range K).drop (m + 1)).flatMap (fun i => matL (M i)) ++ rest) (M m)
      (by simpa using h3) (by simpa using h4) (by simpa using h1) (by simpa using h2)
      (by simpa using h5) (by simpa using h6) (by simpa using h7) (by simpa using h8)
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb
    refine ⟨by rw [b1, Finset.sum_range_succ, add_assoc], by rw [b2, Finset.sum_range_succ, add_assoc],
      b3, b4, b5, ?_, ?_, ?_⟩
    · rw [exec_writes _ _ _ (by decide)]; simpa using h6
    · rw [exec_writes _ _ _ (by decide)]; simpa using h7
    · rw [exec_writes _ _ _ (by decide)]; simpa using h8

/-! ### The `j` body -/

/-- Before the `ι` loop: pop the partial sums of `(j, 0)`, `(j, 1)`, reset the row streams. -/
def jPre : Code :=
  .seq (.cp rAc0 rZ) <| .seq (.mvR rAc0 rS) <| .seq (.cp rAc1 rZ) <| .seq (.mvR rAc1 rS) <|
  .seq (.cp rCo0 rRo0) <| .seq (.cp rCo1 rRo1) (.cp rCi rTK)

/-- After the `ι` loop: push the two sums. -/
def jPost : Code := .seq (.mvR rS2 rAc0) (.mvR rS2 rAc1)

/-- One column `j`. -/
def jBody : Code := .seq jPre (.seq (.rep rCi iBody) jPost)

/-- The `simp` set of straight-line VM code. -/
macro "vm_simp" : tactic => `(tactic| simp only [vmreg, exec_seq, exec_cp, exec_clr, exec_tl,
  exec_mvR, exec_mv, exec_drop, exec_add, exec_sub, exec_mul, exec_neg, exec_aut, exec_rho, exec_rot,
  exec_dig, exec_nop, Fin.reduceEq, ite_false, ite_true, false_or, or_false, or_self])

theorem exec_jBody (hK : 0 < K) (w : St) (s0 s1 z0 z1 : Rq N K) (S T : List (Rq N K))
    (U0 U1 : ℕ → Rq N K) (M : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (rest : List (Rq N K))
    (hS : w rS = encL N K (s0 :: s1 :: S)) (hS2 : w rS2 = encL N K (z0 :: z1 :: T))
    (hR0 : w rRo0 = encL N K ((List.range K).map U0)) (hR1 : w rRo1 = encL N K ((List.range K).map U1))
    (hE : w rMAd = encL N K ((List.range K).flatMap (fun i => matL (M i)) ++ rest))
    (hTK : w rTK = List.replicate K false) (hTK1 : w rTK1 = List.replicate (K - 1) false)
    (hZ : w rZ = encRM N K 0) :
    exec N K jBody w rS = encL N K S ∧
    exec N K jBody w rS2 = encL N K (T ++ [s0 + ∑ i ∈ Finset.range K, digRow (M i) ![U0 i, U1 i] 0,
      s1 + ∑ i ∈ Finset.range K, digRow (M i) ![U0 i, U1 i] 1]) ∧
    exec N K jBody w rMAd = encL N K rest := by
  show exec N K jPost (exec N K (.rep rCi iBody) (exec N K jPre w)) rS = _ ∧
    exec N K jPost (exec N K (.rep rCi iBody) (exec N K jPre w)) rS2 = _ ∧
    exec N K jPost (exec N K (.rep rCi iBody) (exec N K jPre w)) rMAd = _
  set W1 := exec N K jPre w with hW1
  have f : W1 rCi = List.replicate K false ∧ W1 rCo0 = encL N K ((List.range K).map U0) ∧
      W1 rCo1 = encL N K ((List.range K).map U1) ∧ W1 rAc0 = encRM N K s0 ∧
      W1 rAc1 = encRM N K s1 ∧
      W1 rMAd = encL N K ((List.range K).flatMap (fun i => matL (M i)) ++ rest) ∧
      W1 rTK = List.replicate K false ∧ W1 rTK1 = List.replicate (K - 1) false ∧
      W1 rZ = encRM N K 0 ∧ W1 rS = encL N K S ∧ W1 rS2 = encL N K (z0 :: z1 :: T) := by
    rw [hW1]; unfold jPre; vm_simp
    simp [hS, hS2, hR0, hR1, hE, hTK, hTK1, hZ]
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := f
  obtain ⟨k1, k2, k3⟩ := exec_iLoop hK W1 s0 s1 U0 U1 M rest f1 f2 f3 f4 f5 f6 f7 f8 f9
  have g10 : exec N K (.rep rCi iBody) W1 rS = encL N K S := by
    rw [exec_writes _ _ _ (by decide)]; exact f10
  have g11 : exec N K (.rep rCi iBody) W1 rS2 = encL N K (z0 :: z1 :: T) := by
    rw [exec_writes _ _ _ (by decide)]; exact f11
  set W2 := exec N K (.rep rCi iBody) W1
  unfold jPost; vm_simp
  simp [g10, g11, k1, k2, k3]

/-! ### The `j` loop -/

theorem jBody_writes_rCj : jBody.writes rCj = false := by decide

/-- The result of the `j` loop at column `t`, row `a`. -/
def jRes (p : ℕ → Fin 2 → Rq N K) (U0 U1 : ℕ → Rq N K)
    (Mj : ℕ → ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (t : ℕ) (a : Fin 2) : Rq N K :=
  p t a + ∑ i ∈ Finset.range K, digRow (Mj t i) ![U0 i, U1 i] a

/-- **The `j` loop**: `n` columns. -/
theorem exec_jLoop (hK : 0 < K) (w : St) (n : ℕ) (p : ℕ → Fin 2 → Rq N K) (U0 U1 : ℕ → Rq N K)
    (Mj : ℕ → ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (rest : List (Rq N K))
    (hCj : w rCj = List.replicate n false)
    (hS : w rS = encL N K ((List.range n).flatMap fun t => [p t 0, p t 1]))
    (hS2 : w rS2 = encL N K (List.replicate (2 * n) 0))
    (hR0 : w rRo0 = encL N K ((List.range K).map U0)) (hR1 : w rRo1 = encL N K ((List.range K).map U1))
    (hE : w rMAd = encL N K ((List.range n).flatMap
      (fun t => (List.range K).flatMap fun i => matL (Mj t i)) ++ rest))
    (hTK : w rTK = List.replicate K false) (hTK1 : w rTK1 = List.replicate (K - 1) false)
    (hZ : w rZ = encRM N K 0) :
    exec N K (.rep rCj jBody) w rS2 =
      encL N K ((List.range n).flatMap fun t => [jRes p U0 U1 Mj t 0, jRes p U0 U1 Mj t 1]) ∧
    exec N K (.rep rCj jBody) w rMAd = encL N K rest := by
  have key := exec_rep_inv (N := N) (K := K) rCj jBody jBody_writes_rCj
    (fun m w' => w' rS = encL N K (((List.range n).drop m).flatMap fun t => [p t 0, p t 1]) ∧
      w' rS2 = encL N K (List.replicate (2 * (n - m)) 0 ++
        (List.range m).flatMap fun t => [jRes p U0 U1 Mj t 0, jRes p U0 U1 Mj t 1]) ∧
      w' rMAd = encL N K (((List.range n).drop m).flatMap
        (fun t => (List.range K).flatMap fun i => matL (Mj t i)) ++ rest) ∧
      w' rRo0 = encL N K ((List.range K).map U0) ∧ w' rRo1 = encL N K ((List.range K).map U1) ∧
      w' rTK = List.replicate K false ∧ w' rTK1 = List.replicate (K - 1) false ∧
      w' rZ = encRM N K 0) w
    ⟨by simp [hS], by simp [hS2], by simp [hE], hR0, hR1, hTK, hTK1, hZ⟩ ?_
  · rw [hCj, List.length_replicate] at key
    obtain ⟨-, k2, k3, -⟩ := key
    refine ⟨by rw [k2]; simp, ?_⟩
    rw [k3, List.drop_of_length_le (by simp)]
    rfl
  · intro m w' hm hP _
    rw [hCj, List.length_replicate] at hm
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hP
    rw [drop_range_cons hm, List.flatMap_cons] at h1 h3
    have e2 : 2 * (n - m) = 2 + (2 * (n - (m + 1))) := by omega
    rw [e2, List.replicate_add] at h2
    have hb := exec_jBody hK (Function.update w' rCj (w' rCj).tail) (p m 0) (p m 1) 0 0
      (((List.range n).drop (m + 1)).flatMap fun t => [p t 0, p t 1])
      (List.replicate (2 * (n - (m + 1))) 0 ++
        (List.range m).flatMap fun t => [jRes p U0 U1 Mj t 0, jRes p U0 U1 Mj t 1])
      U0 U1 (Mj m) (((List.range n).drop (m + 1)).flatMap
        (fun t => (List.range K).flatMap fun i => matL (Mj t i)) ++ rest)
      (by simpa using h1) (by simpa [List.replicate_succ] using h2) (by simpa using h4)
      (by simpa using h5) (by simpa [List.append_assoc] using h3) (by simpa using h6)
      (by simpa using h7) (by simpa using h8)
    obtain ⟨b1, b2, b3⟩ := hb
    refine ⟨b1, ?_, b3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [b2, List.range_succ, List.flatMap_append]
      simp [jRes]
    · rw [exec_writes _ _ _ (by decide)]; simpa using h4
    · rw [exec_writes _ _ _ (by decide)]; simpa using h5
    · rw [exec_writes _ _ _ (by decide)]; simpa using h6
    · rw [exec_writes _ _ _ (by decide)]; simpa using h7
    · rw [exec_writes _ _ _ (by decide)]; simpa using h8

/-! ### Blocks of queues -/

theorem takeD_encL (l rest : List (Rq N K)) {c : ℕ} (h : l.length = c) :
    takeD (c * (N * K)) (encL N K (l ++ rest)) = encL N K l := by
  rw [encL_append, ← h, ← length_encL]
  exact takeD_append_of_length _ rfl

theorem drop_encL (l rest : List (Rq N K)) {c : ℕ} (h : l.length = c) :
    (encL N K (l ++ rest)).drop (c * (N * K)) = encL N K rest := by
  rw [encL_append, ← h, ← length_encL, List.drop_left]

theorem shiftIn_encL (l l' x rest : List (Rq N K)) {c : ℕ} (hl : l.length = c) (hx : x.length = c) :
    ValVM.shiftIn (c * (N * K)) (encL N K (l ++ l')) (encL N K (x ++ rest)) = encL N K (l' ++ x) := by
  unfold ValVM.shiftIn
  rw [takeD_encL x rest hx, encL_append, List.append_assoc, ← hl, ← length_encL, List.drop_left,
    encL_append]

@[simp] theorem takeD_encL' (x : List (Rq N K)) (u : List Bool) {c : ℕ} (h : x.length = c) :
    takeD (c * (N * K)) (encL N K x ++ u) = encL N K x := by
  rw [← h, ← length_encL]; exact takeD_append_of_length _ rfl

@[simp] theorem takeD_encL'' (x : List (Rq N K)) {c : ℕ} (h : x.length = c) :
    takeD (c * (N * K)) (encL N K x) = encL N K x := by
  rw [← h, ← length_encL]; exact takeD_of_length _

@[simp] theorem drop_encL' (x : List (Rq N K)) (u : List Bool) {c : ℕ} (h : x.length = c) :
    (encL N K x ++ u).drop (c * (N * K)) = u := by
  rw [← h, ← length_encL, List.drop_left]

@[simp] theorem drop_encL'' (x : List (Rq N K)) {c : ℕ} (h : x.length = c) :
    (encL N K x).drop (c * (N * K)) = [] := by
  rw [← h, ← length_encL, List.drop_length]

@[simp] theorem shiftIn_encL' (l : List (Rq N K)) (s : List Bool) {c : ℕ} (h : l.length = c) :
    ValVM.shiftIn (c * (N * K)) (encL N K l) s = takeD (c * (N * K)) s := by
  unfold ValVM.shiftIn
  rw [← h, ← length_encL, List.drop_left]

theorem encL_replicate_eq (m : ℕ) :
    List.replicate (m * (N * K)) false = encL N K (List.replicate m (0 : Rq N K)) :=
  (encL_replicate_zero N K m).symm

/-! ### One `r` -/

/-- The column of index `t` (in the order of `Enum`). -/
def colOf (hK : 0 < K) (t : ℕ) : Fin 2 × Fin K := (Enum.list (α := Fin 2 × Fin K)).getD t (0, ⟨0, hK⟩)

/-- The digit index `i`. -/
def finOf (hK : 0 < K) (i : ℕ) : Fin K := (List.finRange K).getD i ⟨0, hK⟩

/-- The digit matrices of `r`, by column index `t` and digit index `i`. -/
def adMj (hK : 0 < K) (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (r : Fin 2) :
    ℕ → ℕ → Fin 2 → Fin 2 × Fin K → Rq N K :=
  fun t i => Ad (r, colOf hK t, finOf hK i)

/-- The part `r` of the stream of digit matrices. -/
def adBlock (hK : 0 < K) (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (r : Fin 2) :
    List (Rq N K) :=
  (List.range (2 * K)).flatMap fun t => (List.range K).flatMap fun i => matL (adMj hK Ad r t i)

/-- The rows of part `r`. -/
def rowF (A : Fin 2 → Fin 2 × Fin K → Rq N K) (a r : Fin 2) : ℕ → Rq N K :=
  extF K fun i => A a (r, i)

/-- Before the `j` loop of `r`: the row segments `A_{a, (r, ·)}`, the templates. -/
def rPre (r : Fin 2) : Code :=
  .seq (.cp rTmp rMA) <| .seq (if r = 1 then .drop rTmp rTKNK else .nop) <|
  .seq (.cp rRo0 rTKNK) <| .seq (.mv rRo0 rTmp rTKNK) <| .seq (.drop rTmp rTKNK) <|
  .seq (.cp rRo1 rTKNK) <| .seq (.mv rRo1 rTmp rTKNK) <|
  .seq (.cp rS2 rT4KNK) (.cp rCj rT2K)

/-- One `r`: the row segments, the `j` loop. -/
def rPart (r : Fin 2) : Code := .seq (rPre r) (.seq (.rep rCj jBody) (.cp rS rS2))

theorem ne_of_val_lt {a q : Fin 64} (h : a.val < q.val) : a ≠ q := fun e => by
  subst e; exact lt_irrefl _ h

theorem rPre_writes (r : Fin 2) (q : Fin 64) (hq : 57 ≤ q.val) : (rPre r).writes q = false := by
  have h1 : (55 : Fin 64) ≠ q := ne_of_val_lt (by simp; omega)
  have h2 : (41 : Fin 64) ≠ q := ne_of_val_lt (by simp; omega)
  have h3 : (42 : Fin 64) ≠ q := ne_of_val_lt (by simp; omega)
  have h4 : (36 : Fin 64) ≠ q := ne_of_val_lt (by simp; omega)
  have h5 : (45 : Fin 64) ≠ q := ne_of_val_lt (by simp; omega)
  fin_cases r <;> simp [rPre, Code.writes, h1, h2, h3, h4, h5]

/-- The templates of `mulPKC`. -/
structure MulTmpl (N K : ℕ) (w : St) : Prop where
  tK : w rTK = List.replicate K false
  tK1 : w rTK1 = List.replicate (K - 1) false
  z : w rZ = encRM N K 0
  t2K : w rT2K = List.replicate (2 * K) false
  tKNK : w rTKNK = encL N K (List.replicate K 0)
  t2KNK : w rT2KNK = encL N K (List.replicate (2 * K) 0)
  t4KNK : w rT4KNK = encL N K (List.replicate (2 * (2 * K)) 0)

theorem MulTmpl.of_writes {w w' : St} (h : MulTmpl N K w)
    (hw : ∀ r : Fin 64, 57 ≤ r.val → w' r = w r) : MulTmpl N K w' :=
  ⟨by rw [hw _ (by decide)]; exact h.tK, by rw [hw _ (by decide)]; exact h.tK1,
    by rw [hw _ (by decide)]; exact h.z, by rw [hw _ (by decide)]; exact h.t2K,
    by rw [hw _ (by decide)]; exact h.tKNK, by rw [hw _ (by decide)]; exact h.t2KNK,
    by rw [hw _ (by decide)]; exact h.t4KNK⟩

theorem segL_eq_rowF (A : Fin 2 → Fin 2 × Fin K → Rq N K) (a r : Fin 2) :
    segL A a r = (List.range K).map (rowF A a r) := by
  rw [segL, finRange_map_eq]; rfl

theorem exec_rPart (hK : 0 < K) (r : Fin 2) (w : St) (A : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (p : ℕ → Fin 2 → Rq N K) (rest : List (Rq N K))
    (hMA : w rMA = encL N K (matL A))
    (hS : w rS = encL N K ((List.range (2 * K)).flatMap fun t => [p t 0, p t 1]))
    (hE : w rMAd = encL N K (adBlock hK Ad r ++ rest)) (hT : MulTmpl N K w) :
    exec N K (rPart r) w rS = encL N K ((List.range (2 * K)).flatMap fun t =>
      [jRes p (rowF A 0 r) (rowF A 1 r) (adMj hK Ad r) t 0,
        jRes p (rowF A 0 r) (rowF A 1 r) (adMj hK Ad r) t 1]) ∧
    exec N K (rPart r) w rMAd = encL N K rest := by
  have hA := matL_eq A
  rw [segL_eq_rowF, segL_eq_rowF, segL_eq_rowF, segL_eq_rowF] at hA
  rw [hA] at hMA
  simp only [List.append_assoc] at hMA
  have pre : ∃ W1, exec N K (rPre r) w = W1 ∧
      W1 rRo0 = encL N K ((List.range K).map (rowF A 0 r)) ∧
      W1 rRo1 = encL N K ((List.range K).map (rowF A 1 r)) ∧
      W1 rS2 = encL N K (List.replicate (2 * (2 * K)) 0) ∧ W1 rCj = List.replicate (2 * K) false ∧
      W1 rS = w rS ∧ W1 rMAd = w rMAd := by
    refine ⟨_, rfl, ?_⟩
    unfold rPre
    fin_cases r
    · vm_simp
      simp [hMA, hT.tKNK, hT.t4KNK, hT.t2K]
    · vm_simp
      simp [hMA, hT.tKNK, hT.t4KNK, hT.t2K]
  obtain ⟨W1, hW1, p1, p2, p3, p4, p5, p6⟩ := pre
  have hT1 : MulTmpl N K W1 := hT.of_writes fun q hq => by
    rw [← hW1]; exact exec_writes _ _ _ (rPre_writes r q hq)
  show exec N K (.seq (.rep rCj jBody) (.cp rS rS2)) (exec N K (rPre r) w) rS = _ ∧
    exec N K (.seq (.rep rCj jBody) (.cp rS rS2)) (exec N K (rPre r) w) rMAd = _
  rw [hW1]
  obtain ⟨k1, k2⟩ := exec_jLoop hK W1 (2 * K) p (rowF A 0 r) (rowF A 1 r) (adMj hK Ad r) rest p4
    (by rw [p5, hS]) p3 p1 p2 (by rw [p6, hE]; rfl) hT1.tK hT1.tK1 hT1.z
  rw [exec_seq]
  simp only [exec_cp, Function.update_self]
  refine ⟨k1, ?_⟩
  rw [Function.update_of_ne (by decide), k2]

end MVM

end SigabaNeo.Tape
