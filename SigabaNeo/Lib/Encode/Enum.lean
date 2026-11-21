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

end FixedEnc

end SigabaNeo.Encode
