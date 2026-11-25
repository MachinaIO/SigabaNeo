import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.Ring

/-!
# Explicit enumerations and fixed-length encodings

An algorithm reading a function `f : α → β` on a finite type needs an order on `α`. `Enum α` is an
explicit list of all elements of `α`, without repetition: `List.finRange` for `Fin n`, the
lexicographic product for `α × β`, the left elements before the right ones for `α ⊕ β`.

`FixedEnc β n`: an encoding of `β` by words of length exactly `n`. Concatenating the encodings of
the values of `f` in the order of `Enum α` (`encFun`) is a fixed-length encoding of `α → β`
(`FixedEnc.fun`), and products of fixed-length encodings are fixed-length encodings
(`FixedEnc.prod`).
-/

namespace SigabaNeo.Encode

/-- An explicit enumeration of a finite type. -/
class Enum (α : Type) where
  /-- All elements, in order. -/
  list : List α
  /-- No element twice. -/
  nodup : list.Nodup
  /-- Every element. -/
  complete : ∀ a, a ∈ list

instance (n : ℕ) : Enum (Fin n) where
  list := List.finRange n
  nodup := List.nodup_finRange n
  complete := List.mem_finRange

instance {α β : Type} [Enum α] [Enum β] : Enum (α × β) where
  list := (Enum.list (α := α)).product (Enum.list (α := β))
  nodup := (Enum.nodup).product Enum.nodup
  complete := fun ⟨a, b⟩ => List.mem_product.mpr ⟨Enum.complete a, Enum.complete b⟩

instance {α β : Type} [Enum α] [Enum β] : Enum (α ⊕ β) where
  list := (Enum.list (α := α)).map Sum.inl ++ (Enum.list (α := β)).map Sum.inr
  nodup := by
    refine List.nodup_append.mpr ⟨(Enum.nodup).map Sum.inl_injective,
      (Enum.nodup).map Sum.inr_injective, ?_⟩
    intro a ha b hb hab
    rw [List.mem_map] at ha hb
    obtain ⟨a', -, rfl⟩ := ha
    obtain ⟨b', -, rfl⟩ := hb
    cases hab
  complete := fun
    | .inl a => List.mem_append_left _ (List.mem_map.mpr ⟨a, Enum.complete a, rfl⟩)
    | .inr b => List.mem_append_right _ (List.mem_map.mpr ⟨b, Enum.complete b, rfl⟩)

instance : Enum Unit where
  list := [()]
  nodup := List.nodup_singleton _
  complete := fun _ => List.mem_singleton_self _

/-- An encoding by words of length exactly `n`. -/
structure FixedEnc (β : Type) (n : ℕ) where
  /-- The encoding. -/
  enc : β → List Bool
  /-- It is injective. -/
  inj : Function.Injective enc
  /-- Every word has length `n`. -/
  length : ∀ b, (enc b).length = n

namespace FixedEnc

/-- Fixed-length words are determined by their concatenation. -/
theorem append_inj {n : ℕ} {u v u' v' : List Bool} (hu : u.length = n) (hu' : u'.length = n)
    (h : u ++ v = u' ++ v') : u = u' ∧ v = v' :=
  List.append_inj h (hu.trans hu'.symm)

/-- **Products.** -/
def prod {β γ : Type} {n m : ℕ} (e : FixedEnc β n) (f : FixedEnc γ m) : FixedEnc (β × γ) (n + m) where
  enc p := e.enc p.1 ++ f.enc p.2
  inj p q h := by
    obtain ⟨h1, h2⟩ := append_inj (e.length _) (e.length _) h
    exact Prod.ext (e.inj h1) (f.inj h2)
  length p := by simp [e.length, f.length]

/-- The concatenation of the encodings of a list of values. -/
def encList {β : Type} {n : ℕ} (e : FixedEnc β n) (l : List β) : List Bool := l.flatMap e.enc

theorem length_encList {β : Type} {n : ℕ} (e : FixedEnc β n) (l : List β) :
    (e.encList l).length = l.length * n := by
  induction l with
  | nil => simp [encList]
  | cons b l ih =>
    simp only [encList, List.flatMap_cons, List.length_append, e.length, List.length_cons] at ih ⊢
    rw [ih]; ring

theorem encList_inj {β : Type} {n : ℕ} (e : FixedEnc β n) :
    ∀ {l l' : List β}, l.length = l'.length → e.encList l = e.encList l' → l = l'
  | [], [], _, _ => rfl
  | b :: l, b' :: l', hl, h => by
    simp only [encList, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := append_inj (e.length _) (e.length _) h
    rw [e.inj h1, encList_inj e (by simpa using hl) h2]

/-- **Functions on an enumerated type**: the values in the order of the enumeration. -/
def «fun» {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) :
    FixedEnc (α → β) ((Enum.list (α := α)).length * n) where
  enc f := e.encList ((Enum.list (α := α)).map f)
  inj f g h := by
    have := encList_inj e (by simp) h
    funext a
    exact List.map_inj_left.mp this a (Enum.complete a)
  length f := by rw [length_encList]; simp

/-! ### Reading blocks back -/

theorem prod_enc {β γ : Type} {n m : ℕ} (e : FixedEnc β n) (f : FixedEnc γ m) (p : β × γ) :
    (e.prod f).enc p = e.enc p.1 ++ f.enc p.2 := rfl

/-- The first field of a product is its first `n` bits. -/
theorem prod_take {β γ : Type} {n m : ℕ} (e : FixedEnc β n) (f : FixedEnc γ m) (p : β × γ) :
    ((e.prod f).enc p).take n = e.enc p.1 := by
  rw [prod_enc, List.take_append_of_le_length (le_of_eq (e.length _).symm),
    List.take_of_length_le (le_of_eq (e.length _))]

/-- The second field of a product is what follows the first `n` bits. -/
theorem prod_drop {β γ : Type} {n m : ℕ} (e : FixedEnc β n) (f : FixedEnc γ m) (p : β × γ) :
    ((e.prod f).enc p).drop n = f.enc p.2 := by
  rw [prod_enc, List.drop_append_of_le_length (le_of_eq (e.length _).symm),
    List.drop_of_length_le (le_of_eq (e.length _)), List.nil_append]

/-- **The block of the `i`-th value** in a concatenation of fixed-length encodings. -/
theorem encList_block {β : Type} {n : ℕ} (e : FixedEnc β n) :
    ∀ (l : List β) (i : ℕ) (hi : i < l.length), ((e.encList l).drop (i * n)).take n = e.enc l[i]
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | b :: l, 0, _ => by
    simp only [encList, List.flatMap_cons, zero_mul, List.drop_zero, List.getElem_cons_zero]
    rw [List.take_append_of_le_length (le_of_eq (e.length _).symm),
      List.take_of_length_le (le_of_eq (e.length _))]
  | b :: l, i + 1, hi => by
    have ih := encList_block e l i (by simpa using hi)
    simp only [encList, List.flatMap_cons, List.getElem_cons_succ] at ih ⊢
    rw [show (i + 1) * n = n + i * n by ring, ← List.drop_drop,
      List.drop_append_of_le_length (le_of_eq (e.length _).symm),
      List.drop_of_length_le (le_of_eq (e.length _)), List.nil_append]
    exact ih

/-- **The block of the value at the `i`-th element** of the enumeration. -/
theorem fun_block {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) (f : α → β) (i : ℕ)
    (hi : i < (Enum.list (α := α)).length) :
    (((FixedEnc.fun e).enc f).drop (i * n)).take n = e.enc (f (Enum.list (α := α))[i]) := by
  have := encList_block e ((Enum.list (α := α)).map f) i (by simpa using hi)
  rw [List.getElem_map] at this
  exact this

end FixedEnc

/-! ### Positions in the enumerations -/

namespace Enum

theorem getElem_fin {n : ℕ} (i : ℕ) (hi : i < (Enum.list (α := Fin n)).length) :
    (Enum.list (α := Fin n))[i] = ⟨i, by simpa [Enum.list] using hi⟩ := by
  simp [Enum.list]

theorem length_prod {α β : Type} [Enum α] [Enum β] :
    (Enum.list (α := α × β)).length = (Enum.list (α := α)).length * (Enum.list (α := β)).length := by
  exact List.length_product _ _

theorem getElem_product {α β : Type} (la : List α) (lb : List β) (i j : ℕ) (hi : i < la.length)
    (hj : j < lb.length) (h : i * lb.length + j < (la.product lb).length) :
    (la.product lb)[i * lb.length + j] = (la[i], lb[j]) := by
  induction la generalizing i with
  | nil => simp at hi
  | cons a la ih =>
    have hc : (a :: la).product lb = lb.map (Prod.mk a) ++ la.product lb := List.product_cons a la lb
    simp only [hc] at h ⊢
    cases i with
    | zero =>
      simp only [zero_mul, zero_add, List.getElem_cons_zero]
      rw [List.getElem_append_left (by simpa using hj)]
      simp
    | succ i =>
      have hlen : (lb.map (Prod.mk a)).length ≤ (i + 1) * lb.length + j := by
        simp only [List.length_map]
        exact Nat.le_add_right_of_le (by rw [Nat.succ_mul]; exact Nat.le_add_left _ _)
      rw [List.getElem_append_right hlen]
      simp only [List.length_map, List.getElem_cons_succ]
      have e : (i + 1) * lb.length + j - lb.length = i * lb.length + j := by
        rw [Nat.succ_mul]; omega
      simp only [e]
      exact ih i (by simpa using hi) _

/-- **The element at `i · |β| + j`** of the enumeration of `α × β` is the pair of the `i`-th and
the `j`-th elements. -/
theorem getElem_prod {α β : Type} [Enum α] [Enum β] (i j : ℕ) (hi : i < (Enum.list (α := α)).length)
    (hj : j < (Enum.list (α := β)).length)
    (h : i * (Enum.list (α := β)).length + j < (Enum.list (α := α × β)).length) :
    (Enum.list (α := α × β))[i * (Enum.list (α := β)).length + j] =
      ((Enum.list (α := α))[i], (Enum.list (α := β))[j]) :=
  getElem_product _ _ i j hi hj h

/-- The position of an element in the enumeration. -/
def index {α : Type} [Enum α] [DecidableEq α] (a : α) : ℕ := (Enum.list (α := α)).idxOf a

theorem index_lt {α : Type} [Enum α] [DecidableEq α] (a : α) :
    index a < (Enum.list (α := α)).length :=
  List.idxOf_lt_length_iff.mpr (Enum.complete a)

theorem getElem_index {α : Type} [Enum α] [DecidableEq α] (a : α) :
    (Enum.list (α := α))[index a]'(index_lt a) = a :=
  List.getElem_idxOf _

end Enum

end SigabaNeo.Encode
