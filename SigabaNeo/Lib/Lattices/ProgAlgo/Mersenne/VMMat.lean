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

end MVM

end SigabaNeo.Tape
