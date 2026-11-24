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
  exec_app, exec_eqb,
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
  exec_app, exec_eqb,
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

/-! ### The transposition and `mulPKC` -/

/-- Move the sums of `(t, 0)` and `(t, 1)` to the row queues. -/
def tBody : Code :=
  .seq (.cp rAc0 rZ) <| .seq (.mvR rAc0 rS) <| .seq (.mvR rCo0 rAc0) <|
  .seq (.cp rAc1 rZ) <| .seq (.mvR rAc1 rS) (.mvR rCo1 rAc1)

/-- The templates of the transposition. -/
def tPre : Code := .seq (.cp rCo0 rT2KNK) <| .seq (.cp rCo1 rT2KNK) (.cp rCj rT2K)

/-- The transposition loop. -/
def tLoop : Code := .seq tPre (.rep rCj tBody)

/-- The output: row `0`, then row `1`. -/
def tOut : Code := .seq (.cp rMOut rT4KNK) <| .seq (.mv rMOut rCo0 rT2KNK) (.mv rMOut rCo1 rT2KNK)

/-- **`EvalPK` of `Mul`** with binary digits: `rMOut := mulPKm A Ad` from `A` (`rMA`) and the
stream of the digit matrices `Ad` (`rMAd`, consumed). -/
def mulPKC : Code :=
  .seq (.cp rS rT4KNK) <| .seq (rPart 0) <| .seq (rPart 1) <| .seq tLoop tOut

theorem tBody_writes_rCj : tBody.writes rCj = false := by decide

theorem exec_tLoop (w : St) (R : ℕ → Fin 2 → Rq N K) (hT : MulTmpl N K w)
    (hS : w rS = encL N K ((List.range (2 * K)).flatMap fun t => [R t 0, R t 1])) :
    exec N K tLoop w rCo0 = encL N K ((List.range (2 * K)).map fun t => R t 0) ∧
    exec N K tLoop w rCo1 = encL N K ((List.range (2 * K)).map fun t => R t 1) := by
  show exec N K (.rep rCj tBody) (exec N K tPre w) rCo0 = _ ∧
    exec N K (.rep rCj tBody) (exec N K tPre w) rCo1 = _
  set W1 := exec N K tPre w with hW1
  have f : W1 rS = w rS ∧ W1 rCo0 = encL N K (List.replicate (2 * K) 0) ∧
      W1 rCo1 = encL N K (List.replicate (2 * K) 0) ∧ W1 rZ = encRM N K 0 ∧
      W1 rCj = List.replicate (2 * K) false := by
    rw [hW1]; unfold tPre; vm_simp; simp [hT.t2KNK, hT.z, hT.t2K]
  have key := exec_rep_inv (N := N) (K := K) rCj tBody tBody_writes_rCj
    (fun m w' => w' rS = encL N K (((List.range (2 * K)).drop m).flatMap fun t => [R t 0, R t 1]) ∧
      w' rCo0 = encL N K (List.replicate (2 * K - m) 0 ++ (List.range m).map fun t => R t 0) ∧
      w' rCo1 = encL N K (List.replicate (2 * K - m) 0 ++ (List.range m).map fun t => R t 1) ∧
      w' rZ = encRM N K 0) W1
    ⟨by simp [f.1, hS], by simp [f.2.1], by simp [f.2.2.1], f.2.2.2.1⟩ ?_
  · have hl : (W1 rCj).length = 2 * K := by simp [f.2.2.2.2]
    rw [hl] at key
    exact ⟨by rw [key.2.1]; simp, by rw [key.2.2.1]; simp⟩
  · intro m w' hm hP _
    have hl : (W1 rCj).length = 2 * K := by simp [f.2.2.2.2]
    rw [hl] at hm
    obtain ⟨h1, h2, h3, h4⟩ := hP
    rw [drop_range_cons hm, List.flatMap_cons] at h1
    have e : 2 * K - m = (2 * K - (m + 1)) + 1 := by omega
    rw [e, List.replicate_succ] at h2 h3
    unfold tBody
    vm_step; vm_step; vm_step; vm_step; vm_step
    refine ⟨by simp [h1, h4], by simp [h1, h2, h4, List.range_succ], by simp [h1, h3, h4,
      List.range_succ], by simp [h4]⟩

theorem shiftIn_encL_gen (l l' x : List (Rq N K)) {c : ℕ} (hl : l.length = c) (hx : x.length = c) :
    ValVM.shiftIn (c * (N * K)) (encL N K (l ++ l')) (encL N K x) = encL N K (l' ++ x) := by
  unfold ValVM.shiftIn
  rw [takeD_encL'' x hx, encL_append, List.append_assoc, ← hl, ← length_encL, List.drop_left,
    encL_append]

theorem exec_tOut (w : St) (x y : List (Rq N K)) (hx : x.length = 2 * K) (hy : y.length = 2 * K)
    (hT : MulTmpl N K w) (h0 : w rCo0 = encL N K x) (h1 : w rCo1 = encL N K y) :
    exec N K tOut w rMOut = encL N K (x ++ y) := by
  unfold tOut
  vm_step; vm_step
  simp only [exec_mv, vmreg, Fin.reduceEq, ite_false, or_self, Function.update_self]
  simp only [Function.update_apply, Fin.reduceEq, ite_false, if_true, hT.t2KNK, hT.t4KNK, h0, h1,
    length_encL, List.length_replicate]
  rw [show 2 * (2 * K) = 2 * K + 2 * K by ring, List.replicate_add,
    shiftIn_encL_gen _ _ _ (List.length_replicate ..) hx,
    shiftIn_encL_gen _ x _ (List.length_replicate ..) hy]

/-! ### The main theorem of `mulPKC` -/

theorem map_eq_range_getD {α β : Type} (L : List α) (d : α) (f : α → β) :
    (List.range L.length).map (fun t => f (L.getD t d)) = L.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem flatMap_eq_range_getD {α β : Type} (L : List α) (d : α) (g : α → List β) :
    L.flatMap g = (List.range L.length).flatMap (fun t => g (L.getD t d)) := by
  rw [List.flatMap_def, List.flatMap_def, ← map_eq_range_getD L d g]

theorem length_enum_col : (Enum.list (α := Fin 2 × Fin K)).length = 2 * K := by
  show ((Enum.list (α := Fin 2)).product (Enum.list (α := Fin K))).length = _
  have : (Enum.list (α := Fin K)) = List.finRange K := rfl
  simp [List.product, enum_fin2, this]; ring

theorem adL_blocks (hK : 0 < K) (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) :
    adL Ad = adBlock hK Ad 0 ++ adBlock hK Ad 1 := by
  rw [adL_eq, enum_fin2]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, adBlock]
  congr 1 <;>
  · rw [flatMap_eq_range_getD _ (0, ⟨0, hK⟩), length_enum_col]
    congr 1; funext t
    rw [flatMap_eq_range_getD (List.finRange K) ⟨0, hK⟩, List.length_finRange]
    rfl

theorem zeros_eq_flatMap (n : ℕ) :
    List.replicate (2 * n) (0 : Rq N K) = (List.range n).flatMap fun _ => [0, 0] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ← ih, show 2 * (n + 1) = 2 * n + 2 by ring,
      List.replicate_add]
    rfl

theorem matL_eq_range (hK : 0 < K) (M : Fin 2 → Fin 2 × Fin K → Rq N K) :
    matL M = (List.range (2 * K)).map (fun t => M 0 (colOf hK t)) ++
      (List.range (2 * K)).map (fun t => M 1 (colOf hK t)) := by
  rw [matL, enum_fin2]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← map_eq_range_getD _ (0, ⟨0, hK⟩), ← map_eq_range_getD _ (0, ⟨0, hK⟩), length_enum_col]
  rfl

theorem finOf_val (hK : 0 < K) (i : Fin K) : finOf hK i.val = i := by
  rw [finOf, List.getD_eq_getElem _ _ (by simp)]; simp

theorem mulPKm_eq (hK : 0 < K) (A : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (t : ℕ) (a : Fin 2) :
    jRes (jRes (fun _ _ => 0) (rowF A 0 0) (rowF A 1 0) (adMj hK Ad 0)) (rowF A 0 1) (rowF A 1 1)
      (adMj hK Ad 1) t a = mulPKm A Ad a (colOf hK t) := by
  simp only [jRes, zero_add, mulPKm, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_range]
  congr 1 <;>
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [adMj, finOf_val, digRow, rowF, extF, i.isLt, dite_true, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    simp

theorem mulPKC_writes_rMA : mulPKC.writes rMA = false := by decide
theorem rPart_writes_ge (r : Fin 2) : ∀ q : Fin 64, 57 ≤ q.val → (rPart r).writes q = false := by
  fin_cases r <;> decide

/-- **`mulPKC` computes `EvalPK` of `Mul`**: from the list of `A` in `rMA` and the stream
`adL Ad ++ rest` in `rMAd`, it writes the list of `mulPKm A Ad` in `rMOut` and leaves `rest` in
`rMAd`. -/
theorem exec_mulPKC (hK : 0 < K) (w : St) (A : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (rest : List (Rq N K))
    (hMA : w rMA = encL N K (matL A)) (hE : w rMAd = encL N K (adL Ad ++ rest))
    (hT : MulTmpl N K w) :
    exec N K mulPKC w rMOut = encL N K (matL (mulPKm A Ad)) ∧
    exec N K mulPKC w rMAd = encL N K rest := by
  show exec N K (.seq tLoop tOut) (exec N K (rPart 1) (exec N K (rPart 0)
      (exec N K (.cp rS rT4KNK) w))) rMOut = _ ∧
    exec N K (.seq tLoop tOut) (exec N K (rPart 1) (exec N K (rPart 0)
      (exec N K (.cp rS rT4KNK) w))) rMAd = _
  rw [adL_blocks hK, List.append_assoc] at hE
  set W0 := exec N K (.cp rS rT4KNK) w with hW0
  have hT0 : MulTmpl N K W0 := hT.of_writes fun q hq => by
    rw [hW0, exec_cp, Function.update_of_ne (fun e => by subst e; simp at hq)]
  have hS0 : W0 rS = encL N K ((List.range (2 * K)).flatMap fun t =>
      [(fun (_ : ℕ) (_ : Fin 2) => (0 : Rq N K)) t 0, (fun (_ : ℕ) (_ : Fin 2) => (0 : Rq N K)) t 1]) := by
    rw [hW0, exec_cp, Function.update_self, hT.t4KNK, zeros_eq_flatMap]
  obtain ⟨a1, a2⟩ := exec_rPart hK 0 W0 A Ad (fun _ _ => 0) _ (by rw [hW0, exec_cp,
    Function.update_of_ne (by decide), hMA]) hS0 (by rw [hW0, exec_cp,
    Function.update_of_ne (by decide), hE]) hT0
  set W1 := exec N K (rPart 0) W0 with hW1
  have hT1 : MulTmpl N K W1 := hT0.of_writes fun q hq => exec_writes _ _ _ (rPart_writes_ge 0 q hq)
  have hMA1 : W1 rMA = encL N K (matL A) := by
    rw [hW1, exec_writes _ _ _ (by decide), hW0, exec_cp, Function.update_of_ne (by decide), hMA]
  obtain ⟨b1, b2⟩ := exec_rPart hK 1 W1 A Ad _ rest hMA1 a1 a2 hT1
  set W2 := exec N K (rPart 1) W1 with hW2
  have hT2 : MulTmpl N K W2 := hT1.of_writes fun q hq => exec_writes _ _ _ (rPart_writes_ge 1 q hq)
  obtain ⟨c1, c2⟩ := exec_tLoop W2 _ hT2 b1
  rw [exec_seq]
  set W3 := exec N K tLoop W2 with hW3
  have hT3 : MulTmpl N K W3 := hT2.of_writes fun q hq => exec_writes _ _ _ (by revert q; decide)
  refine ⟨?_, ?_⟩
  · rw [exec_tOut W3 _ _ (by simp) (by simp) hT3 c1 c2, matL_eq_range hK]
    simp only [mulPKm_eq]
  · rw [exec_writes _ _ _ (by decide), hW3, exec_writes _ _ _ (by decide), b2]

/-! ### `X · G⁻¹(Y)` -/

@[simp, vmreg] abbrev rGX : Fin 64 := 56

/-- `(X · G⁻¹(Y))_{a, col} = Σ_c X_{a, c} · digit_{c.2}(Y_{c.1, col})` (binary digits). -/
def ginvMulm (X Y : Fin 2 → Fin 2 × Fin K → Rq N K) : Fin 2 → Fin 2 × Fin K → Rq N K :=
  fun a col => digRow X ![Y 0 col, Y 1 col] a

/-- Before the column loop: the rows of `Y` (`rMA`). -/
def gPre : Code :=
  .seq (.cp rTmp rMA) <| .seq (.cp rCo0 rT2KNK) <| .seq (.mv rCo0 rTmp rT2KNK) <|
  .seq (.cp rCo1 rT2KNK) <| .seq (.mv rCo1 rTmp rT2KNK) <| .seq (.cp rS2 rT4KNK) (.cp rCj rT2K)

/-- One column of `Y`: the two digit accumulations against `X` (`rGX`). -/
def gBody : Code :=
  .seq (.cp rAc0 rZ) <| .seq (.cp rAc1 rZ) <| .seq (.cp rMAd rGX) <| .seq iBody <|
  .seq (.mvR rS2 rAc0) (.mvR rS2 rAc1)

/-- **`rMOut := X · G⁻¹(Y)`** (`X` in `rGX`, `Y` in `rMA`). -/
def ginvMulC : Code := .seq gPre <| .seq (.rep rCj gBody) <| .seq (.cp rS rS2) <| .seq tLoop tOut

theorem gBody_writes_rCj : gBody.writes rCj = false := by decide

theorem exec_gLoop (hK : 0 < K) (w : St) (n : ℕ) (X : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Y0 Y1 : ℕ → Rq N K) (hCj : w rCj = List.replicate n false)
    (hC0 : w rCo0 = encL N K ((List.range n).map Y0)) (hC1 : w rCo1 = encL N K ((List.range n).map Y1))
    (hS2 : w rS2 = encL N K (List.replicate (2 * n) 0)) (hGX : w rGX = encL N K (matL X))
    (hTK : w rTK = List.replicate K false) (hTK1 : w rTK1 = List.replicate (K - 1) false)
    (hZ : w rZ = encRM N K 0) :
    exec N K (.rep rCj gBody) w rS2 = encL N K ((List.range n).flatMap fun t =>
      [digRow X ![Y0 t, Y1 t] 0, digRow X ![Y0 t, Y1 t] 1]) := by
  have key := exec_rep_inv (N := N) (K := K) rCj gBody gBody_writes_rCj
    (fun m w' => w' rCo0 = encL N K (((List.range n).map Y0).drop m) ∧
      w' rCo1 = encL N K (((List.range n).map Y1).drop m) ∧
      w' rS2 = encL N K (List.replicate (2 * (n - m)) 0 ++ (List.range m).flatMap fun t =>
        [digRow X ![Y0 t, Y1 t] 0, digRow X ![Y0 t, Y1 t] 1]) ∧
      w' rGX = encL N K (matL X) ∧ w' rTK = List.replicate K false ∧
      w' rTK1 = List.replicate (K - 1) false ∧ w' rZ = encRM N K 0) w
    ⟨by simp [hC0], by simp [hC1], by simp [hS2], hGX, hTK, hTK1, hZ⟩ ?_
  · rw [hCj, List.length_replicate] at key
    rw [key.2.2.1]; simp
  · intro m w' hm hP _
    rw [hCj, List.length_replicate] at hm
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
    rw [drop_range_map Y0 hm] at h1
    rw [drop_range_map Y1 hm] at h2
    have e2 : 2 * (n - m) = 2 + (2 * (n - (m + 1))) := by omega
    rw [e2, List.replicate_add] at h3
    have eB : ∀ v, exec N K gBody v = exec N K (.seq (.mvR rS2 rAc0) (.mvR rS2 rAc1))
        (exec N K iBody (exec N K (.seq (.cp rAc0 rZ) <| .seq (.cp rAc1 rZ) (.cp rMAd rGX)) v)) :=
      fun v => rfl
    rw [eB]
    set W1 := exec N K (.seq (.cp rAc0 rZ) <| .seq (.cp rAc1 rZ) (.cp rMAd rGX))
      (Function.update w' rCj (w' rCj).tail) with hW1
    obtain ⟨b1, b2, b3, b4, -⟩ := exec_iBody hK W1 (Y0 m) (Y1 m) 0 0
      (((List.range n).map Y0).drop (m + 1)) (((List.range n).map Y1).drop (m + 1)) [] X
      (by rw [hW1]; vm_simp; simp [h1]) (by rw [hW1]; vm_simp; simp [h2])
      (by rw [hW1]; vm_simp; simp [h7]) (by rw [hW1]; vm_simp; simp [h7])
      (by rw [hW1]; vm_simp; simp [h4]) (by rw [hW1]; vm_simp; simp [h5])
      (by rw [hW1]; vm_simp; simp [h6]) (by rw [hW1]; vm_simp; simp [h7])
    have f3 : exec N K iBody W1 rS2 = w' rS2 := by
      rw [exec_writes _ _ _ (by decide), hW1]; vm_simp; simp
    have fo : ∀ r : Fin 64, iBody.writes r = false → r ≠ rAc0 → r ≠ rAc1 → r ≠ rMAd → r ≠ rCj →
        exec N K iBody W1 r = w' r := by
      intro r hr h0 h1' h2' h3'
      rw [exec_writes _ _ _ hr, hW1]; vm_simp
      simp [Function.update_apply, h0, h1', h2', h3']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · vm_simp; simp [b3]
    · vm_simp; simp [b4]
    · vm_simp; simp [b1, b2, f3, h3, List.range_succ]
    · vm_simp; simp [fo rGX (by decide) (by decide) (by decide) (by decide) (by decide), h4]
    · vm_simp; simp [fo rTK (by decide) (by decide) (by decide) (by decide) (by decide), h5]
    · vm_simp; simp [fo rTK1 (by decide) (by decide) (by decide) (by decide) (by decide), h6]
    · vm_simp; simp [fo rZ (by decide) (by decide) (by decide) (by decide) (by decide), h7]

theorem gPre_writes_ge : ∀ q : Fin 64, 57 ≤ q.val → gPre.writes q = false := by decide
theorem gLoop_writes_ge : ∀ q : Fin 64, 57 ≤ q.val → (Code.rep rCj gBody).writes q = false := by
  decide

/-- **`ginvMulC` computes `X · G⁻¹(Y)`.** -/
theorem exec_ginvMulC (hK : 0 < K) (w : St) (X Y : Fin 2 → Fin 2 × Fin K → Rq N K)
    (hGX : w rGX = encL N K (matL X)) (hMA : w rMA = encL N K (matL Y)) (hT : MulTmpl N K w) :
    exec N K ginvMulC w rMOut = encL N K (matL (ginvMulm X Y)) := by
  show exec N K (.seq tLoop tOut) (exec N K (.cp rS rS2) (exec N K (.rep rCj gBody)
    (exec N K gPre w))) rMOut = _
  have hY := matL_eq_range hK Y
  rw [hY] at hMA
  set W1 := exec N K gPre w with hW1
  have f : W1 rCj = List.replicate (2 * K) false ∧
      W1 rCo0 = encL N K ((List.range (2 * K)).map fun t => Y 0 (colOf hK t)) ∧
      W1 rCo1 = encL N K ((List.range (2 * K)).map fun t => Y 1 (colOf hK t)) ∧
      W1 rS2 = encL N K (List.replicate (2 * (2 * K)) 0) ∧ W1 rGX = encL N K (matL X) := by
    rw [hW1]; unfold gPre; vm_simp
    simp [hMA, hT.t2KNK, hT.t4KNK, hT.t2K, hGX]
  obtain ⟨f1, f2, f3, f4, f5⟩ := f
  have hT1 : MulTmpl N K W1 := hT.of_writes fun q hq => exec_writes _ _ _ (gPre_writes_ge q hq)
  have g := exec_gLoop hK W1 (2 * K) X _ _ f1 f2 f3 f4 f5 hT1.tK hT1.tK1 hT1.z
  set W2 := exec N K (.rep rCj gBody) W1 with hW2
  have hT2 : MulTmpl N K W2 := hT1.of_writes fun q hq => exec_writes _ _ _ (gLoop_writes_ge q hq)
  set W3 := exec N K (.cp rS rS2) W2 with hW3
  have hT3 : MulTmpl N K W3 := hT2.of_writes fun q hq => by
    rw [hW3, exec_cp, Function.update_of_ne (fun e => by subst e; simp at hq)]
  obtain ⟨c1, c2⟩ := exec_tLoop W3 (fun t a => digRow X ![Y 0 (colOf hK t), Y 1 (colOf hK t)] a)
    hT3 (by rw [hW3, exec_cp, Function.update_self, g])
  rw [exec_seq]
  set W4 := exec N K tLoop W3 with hW4
  have hT4 : MulTmpl N K W4 := hT3.of_writes fun q hq => exec_writes _ _ _ (by revert q; decide)
  rw [exec_tOut W4 _ _ (by simp) (by simp) hT4 c1 c2, matL_eq_range hK]
  rfl

/-! ### `σ_k` on every entry -/

/-- The count register of `autMatC` (read only). -/
@[simp, vmreg] abbrev rKc : Fin 64 := 31

/-- Two entries: `σ_k` on each. -/
def aBody : Code :=
  .seq (.cp rX0 rZ) <| .seq (.mvR rX0 rTmp) <| .seq (.op .aut rX1 rX0 rKc) <| .seq (.mvR rS2 rX1) <|
  .seq (.cp rX0 rZ) <| .seq (.mvR rX0 rTmp) <| .seq (.op .aut rX1 rX0 rKc) (.mvR rS2 rX1)

/-- The setup of `autMatC`. -/
def aPre : Code := .seq (.cp rTmp rMA) <| .seq (.cp rS2 rT4KNK) (.cp rCj rT2K)

/-- **`rMOut := σ_k(A)` entrywise**, `k = |rKc|` (`A` in `rMA`). -/
def autMatC : Code := .seq aPre <| .seq (.rep rCj aBody) (.cp rMOut rS2)

theorem aBody_writes_rCj : aBody.writes rCj = false := by decide

theorem drop_two_cons {α : Type} (L : List α) {m n : ℕ} (hL : L.length = 2 * n) (hm : m < n) :
    L.drop (2 * m) = L[2 * m]'(by omega) :: L[2 * m + 1]'(by omega) :: L.drop (2 * (m + 1)) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
  congr 2

theorem take_two_succ {α : Type} (L : List α) {m n : ℕ} (hL : L.length = 2 * n) (hm : m < n) :
    L.take (2 * (m + 1)) = L.take (2 * m) ++ [L[2 * m]'(by omega), L[2 * m + 1]'(by omega)] := by
  have e : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
  rw [e, List.take_add_one, List.take_add_one,
    List.getElem?_eq_getElem (show 2 * m < L.length by omega),
    List.getElem?_eq_getElem (show 2 * m + 1 < L.length by omega)]
  simp only [Option.toList_some, List.append_assoc, List.cons_append, List.nil_append]

theorem exec_aLoop (hN : 0 < N) (hK : 0 < K) (w : St) (n : ℕ) (L : List (Rq N K))
    (hL : L.length = 2 * n) (hk : 0 < (w rKc).length) (hCj : w rCj = List.replicate n false)
    (hTmp : w rTmp = encL N K L) (hS2 : w rS2 = encL N K (List.replicate (2 * n) 0))
    (hZ : w rZ = encRM N K 0) :
    exec N K (.rep rCj aBody) w rS2 = encL N K (L.map (aut N (w rKc).length)) := by
  have key := exec_rep_inv (N := N) (K := K) rCj aBody aBody_writes_rCj
    (fun m w' => w' rTmp = encL N K (L.drop (2 * m)) ∧
      w' rS2 = encL N K (List.replicate (2 * (n - m)) 0 ++
        (L.take (2 * m)).map (aut N (w rKc).length)) ∧
      w' rKc = w rKc ∧ w' rZ = encRM N K 0) w
    ⟨by simp [hTmp], by simp [hS2], rfl, hZ⟩ ?_
  · rw [hCj, List.length_replicate] at key
    rw [key.2.1, ← hL, List.take_length]; simp
  · intro m w' hm hP _
    rw [hCj, List.length_replicate] at hm
    obtain ⟨h1, h2, h3, h4⟩ := hP
    rw [drop_two_cons L hL hm] at h1
    have e2 : 2 * (n - m) = 2 + (2 * (n - (m + 1))) := by omega
    rw [e2, List.replicate_add] at h2
    unfold aBody
    vm_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [h1, h4]
    · simp [h1, h2, h3, h4, take_two_succ L hL hm, canonW_aut hK hN hk]
    · simp [h3]
    · simp [h4]

theorem aPre_writes_ge : ∀ q : Fin 64, 57 ≤ q.val → aPre.writes q = false := by decide
theorem aLoop_writes_ge : ∀ q : Fin 64, 57 ≤ q.val → (Code.rep rCj aBody).writes q = false := by
  decide

/-- **`autMatC` applies `σ_k` (`k = |rKc| > 0`) to every entry.** -/
theorem exec_autMatC (hN : 0 < N) (hK : 0 < K) (w : St) (A : Fin 2 → Fin 2 × Fin K → Rq N K)
    (hMA : w rMA = encL N K (matL A)) (hk : 0 < (w rKc).length) (hT : MulTmpl N K w) :
    exec N K autMatC w rMOut = encL N K (matL fun a c => aut N (w rKc).length (A a c)) ∧
    (∀ q : Fin 64, 57 ≤ q.val → exec N K autMatC w q = w q) := by
  refine ⟨?_, fun q hq => exec_writes _ _ _ (by revert q; decide)⟩
  show exec N K (.cp rMOut rS2) (exec N K (.rep rCj aBody) (exec N K aPre w)) rMOut = _
  set W1 := exec N K aPre w with hW1
  have f : W1 rCj = List.replicate (2 * K) false ∧ W1 rTmp = encL N K (matL A) ∧
      W1 rS2 = encL N K (List.replicate (2 * (2 * K)) 0) ∧ W1 rZ = encRM N K 0 ∧
      W1 rKc = w rKc := by
    rw [hW1]; unfold aPre; vm_simp; simp [hMA, hT.t4KNK, hT.t2K, hT.z]
  obtain ⟨f1, f2, f3, f4, f5⟩ := f
  have g := exec_aLoop hN hK W1 (2 * K) (matL A) (by simp; ring) (by rw [f5]; exact hk) f1 f2 f3 f4
  rw [exec_cp, Function.update_self, g, f5]
  congr 1
  simp only [matL, List.map_flatMap, List.map_map]
  rfl

/-! ### `EvalPK` of `Aut` -/

/-- The repetition count of `autPKC` (read only). -/
@[simp, vmreg] abbrev rP : Fin 64 := 30

/-- `rMA := σ_k(rMA)` (`k = |rKc|`). -/
def aStep : Code := .seq autMatC (.cp rMA rMOut)

theorem aStep_writes_rP : aStep.writes rP = false := by decide

/-- A saved stream (`autPKC`). -/
@[simp, vmreg] abbrev rSv : Fin 64 := 29

/-- **`EvalPK` of `Aut`**: `rMOut := H · G⁻¹(mulPK(σ_k^{m}(A), Aaut))`, with `A` in `rMA`,
`k = |rKc|`, `m = |rP|`, the digit matrices `Aaut` streamed from `rMAd`, `H` in `rGX`. -/
def autPKC : Code := .seq (.rep rP aStep) <| .seq mulPKC <| .seq (.cp rSv rMAd) <|
  .seq (.cp rMA rMOut) <| .seq ginvMulC (.cp rMAd rSv)

theorem exec_aRep (hN : 0 < N) (hK : 0 < K) (w : St) (A : Fin 2 → Fin 2 × Fin K → Rq N K)
    (hMA : w rMA = encL N K (matL A)) (hk : 0 < (w rKc).length) (hT : MulTmpl N K w) :
    exec N K (.rep rP aStep) w rMA =
      encL N K (matL fun a c => (aut N (w rKc).length)^[(w rP).length] (A a c)) ∧
    MulTmpl N K (exec N K (.rep rP aStep) w) := by
  have key := exec_rep_inv (N := N) (K := K) rP aStep aStep_writes_rP
    (fun m w' => w' rMA = encL N K (matL fun a c => (aut N (w rKc).length)^[m] (A a c)) ∧
      w' rKc = w rKc ∧ MulTmpl N K w') w ⟨by simp [hMA], rfl, hT⟩ ?_
  · exact ⟨key.1, key.2.2⟩
  · intro m w' _ hP _
    obtain ⟨h1, h2, h3⟩ := hP
    set W := Function.update w' rP (w' rP).tail with hW
    have hT' : MulTmpl N K W := h3.of_writes fun q hq => by
      rw [hW, Function.update_of_ne (fun e => by subst e; simp at hq)]
    have hKc : W rKc = w rKc := by rw [hW, Function.update_of_ne (by decide), h2]
    have hMA' : W rMA = encL N K (matL fun a c => (aut N (w rKc).length)^[m] (A a c)) := by
      rw [hW, Function.update_of_ne (by decide), h1]
    obtain ⟨a1, a2⟩ := exec_autMatC hN hK W (fun a c => (aut N (w rKc).length)^[m] (A a c))
      hMA' (by rw [hKc]; exact hk) hT'
    refine ⟨?_, ?_, ?_⟩
    · show Function.update (exec N K autMatC W) rMA (exec N K autMatC W rMOut) rMA = _
      rw [Function.update_self, a1, hKc]
      congr 2; funext a c; rw [Function.iterate_succ_apply']
    · show Function.update (exec N K autMatC W) rMA (exec N K autMatC W rMOut) rKc = _
      rw [Function.update_of_ne (by decide), exec_writes _ _ _ (by decide), hKc]
    · exact (hT'.of_writes a2).of_writes fun q hq => by
        show Function.update (exec N K autMatC W) rMA (exec N K autMatC W rMOut) q = _
        rw [Function.update_of_ne (fun e => by subst e; simp at hq)]

theorem aRep_writes : ∀ q : Fin 64, (q = rMAd ∨ q = rGX) → (Code.rep rP aStep).writes q = false := by
  decide

theorem mulPKC_writes_rGX : mulPKC.writes rGX = false := by decide
theorem mulPKC_writes_ge : ∀ q : Fin 64, 57 ≤ q.val → mulPKC.writes q = false := by decide

/-- **`autPKC` computes `EvalPK` of `Aut`.** -/
theorem exec_autPKC (hN : 0 < N) (hK : 0 < K) (w : St) (A H : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aaut : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (rest : List (Rq N K))
    (hMA : w rMA = encL N K (matL A)) (hE : w rMAd = encL N K (adL Aaut ++ rest))
    (hGX : w rGX = encL N K (matL H)) (hk : 0 < (w rKc).length) (hT : MulTmpl N K w) :
    exec N K autPKC w rMOut = encL N K (matL (ginvMulm H (mulPKm
      (fun a c => (aut N (w rKc).length)^[(w rP).length] (A a c)) Aaut))) ∧
    exec N K autPKC w rMAd = encL N K rest := by
  obtain ⟨r1, r2⟩ := exec_aRep hN hK w A hMA hk hT
  set W1 := exec N K (.rep rP aStep) w with hW1
  have e1 : W1 rMAd = w rMAd := exec_writes _ _ _ (aRep_writes _ (Or.inl rfl))
  have e2 : W1 rGX = w rGX := exec_writes _ _ _ (aRep_writes _ (Or.inr rfl))
  obtain ⟨m1, m2⟩ := exec_mulPKC hK W1 _ Aaut rest r1 (by rw [e1, hE]) r2
  set W2 := exec N K mulPKC W1 with hW2
  have hT2 : MulTmpl N K W2 := r2.of_writes fun q hq => exec_writes _ _ _ (mulPKC_writes_ge q hq)
  have e3 : W2 rGX = w rGX := by rw [hW2, exec_writes _ _ _ mulPKC_writes_rGX, e2]
  set W3 := exec N K (.seq (.cp rSv rMAd) (.cp rMA rMOut)) W2 with hW3
  have hT3 : MulTmpl N K W3 := hT2.of_writes fun q hq => by
    rw [hW3, exec_seq, exec_cp, exec_cp, Function.update_of_ne (fun e => by subst e; simp at hq),
      Function.update_of_ne (fun e => by subst e; simp at hq)]
  have hGX3 : W3 rGX = encL N K (matL H) := by
    rw [hW3]; vm_simp; simp [e3, hGX]
  have hMA3 : W3 rMA = encL N K (matL (mulPKm
      (fun a c => (aut N (w rKc).length)^[(w rP).length] (A a c)) Aaut)) := by
    rw [hW3]; vm_simp; simp [m1]
  have hSv3 : W3 rSv = encL N K rest := by rw [hW3]; vm_simp; simp [m2]
  have g := exec_ginvMulC hK W3 H _ hGX3 hMA3 hT3
  show exec N K (.seq ginvMulC (.cp rMAd rSv)) W3 rMOut = _ ∧
    exec N K (.seq ginvMulC (.cp rMAd rSv)) W3 rMAd = _
  rw [exec_seq, exec_cp, exec_writes _ _ rSv (by decide), hSv3, Function.update_self,
    Function.update_of_ne (by decide), g]
  exact ⟨rfl, rfl⟩

end MVM

end SigabaNeo.Tape
