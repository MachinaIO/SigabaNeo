import SigabaNeo.Lib.Lattices.Homomorphic.BoolBuild
import Mathlib.Tactic.Ring

/-!
# Comparing wires with constants

Bits most significant first (`msbVal`). `geConst p xs as` and `leConst p xs bs` append gates
comparing the number on the wires `xs` with a constant: its value is `msbVal as ≤ value of xs`
(`geConst_spec`), respectively `value of xs ≤ msbVal bs` (`leConst_spec`).

`BExp`: Boolean combinations of such comparisons of inputs, compiled into a program by `compile`
(`compile_spec`).
-/

namespace SigabaNeo.Lattices

/-- The number whose bits, most significant first, are the given list. -/
def msbVal : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat * 2 ^ bs.length + msbVal bs

theorem msbVal_lt : ∀ bs : List Bool, msbVal bs < 2 ^ bs.length
  | [] => by simp [msbVal]
  | b :: bs => by
    have := msbVal_lt bs
    cases b <;> simp [msbVal, pow_succ] <;> omega

theorem foldl_msb (acc : ℕ) (bs : List Bool) :
    bs.foldl (fun acc b => 2 * acc + b.toNat) acc = acc * 2 ^ bs.length + msbVal bs := by
  induction bs generalizing acc with
  | nil => simp [msbVal]
  | cons b bs ih => rw [List.foldl_cons, ih]; simp [msbVal, pow_succ]; ring

/-- Comparing most significant first. -/
theorem msbVal_cons_le (a x : Bool) (as xs : List Bool) (h : as.length = xs.length) :
    msbVal (a :: as) ≤ msbVal (x :: xs) ↔ (a = false ∧ x = true) ∨ (a = x ∧ msbVal as ≤ msbVal xs) := by
  have ha := msbVal_lt as
  have hx := msbVal_lt xs
  rw [h] at ha
  simp only [msbVal, h]
  generalize 2 ^ xs.length = P at ha hx
  cases a <;> cases x <;> simp <;> omega

namespace SLP

variable {ι : Type*}

/-- `msbVal as ≤` the number on `xs`. -/
def geConst (p : SLP ι) : List (Wire ι) → List Bool → SLP ι × Wire ι
  | x :: xs, a :: as =>
    let r := geConst p xs as
    if a then andW r.1 x r.2 else orW r.1 x r.2
  | _, _ => (p, .one)

/-- The number on `xs` `≤ msbVal bs`. -/
def leConst (p : SLP ι) : List (Wire ι) → List Bool → SLP ι × Wire ι
  | x :: xs, b :: bs =>
    let r := leConst p xs bs
    let n := notW r.1 x
    if b then orW n.1 n.2 r.2 else andW n.1 n.2 r.2
  | _, _ => (p, .one)

theorem one_spec (x : ι → Bool) (p : SLP ι) : Spec1 x p (p, .one) true :=
  ⟨Ext.refl p, trivial, rfl⟩

theorem geConst_spec (x : ι → Bool) (p : SLP ι) :
    ∀ (xs : List (Wire ι)) (as : List Bool), xs.length = as.length → (∀ w ∈ xs, Valid p w) →
      Spec1 x p (geConst p xs as) (decide (msbVal as ≤ msbVal (xs.map (bv x p))))
  | [], [], _, _ => by simpa [geConst, msbVal] using one_spec x p
  | w :: xs, a :: as, hl, hv => by
    have hr := geConst_spec x p xs as (by simpa using hl) (fun w h => hv w (by simp [h]))
    have hw : Valid (geConst p xs as).1 w := (hv w (by simp)).ext hr.ext
    have hle := msbVal_cons_le a (bv x p w) as (xs.map (bv x p)) (by simpa using hl.symm)
    cases a
    · have h := orW_spec x _ w _ hw hr.valid
      refine ⟨hr.ext.trans h.ext, h.valid, ?_⟩
      simp only [geConst, Bool.false_eq_true, ↓reduceIte, List.map_cons]
      rw [h.value, hr.value, bv_ext x hr.ext (hv w (by simp))]
      rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq] at hle ⊢
      rw [hle]; cases bv x p w <;> simp
    · have h := andW_spec x _ w _ hw hr.valid
      refine ⟨hr.ext.trans h.ext, h.valid, ?_⟩
      simp only [geConst, ↓reduceIte, List.map_cons]
      rw [h.value, hr.value, bv_ext x hr.ext (hv w (by simp))]
      rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq] at hle ⊢
      rw [hle]; cases bv x p w <;> simp

theorem leConst_spec (x : ι → Bool) (p : SLP ι) :
    ∀ (xs : List (Wire ι)) (bs : List Bool), xs.length = bs.length → (∀ w ∈ xs, Valid p w) →
      Spec1 x p (leConst p xs bs) (decide (msbVal (xs.map (bv x p)) ≤ msbVal bs))
  | [], [], _, _ => by simpa [leConst, msbVal] using one_spec x p
  | w :: xs, b :: bs, hl, hv => by
    have hr := leConst_spec x p xs bs (by simpa using hl) (fun w h => hv w (by simp [h]))
    have hw : Valid (leConst p xs bs).1 w := (hv w (by simp)).ext hr.ext
    have hn := notW_spec x _ w hw
    have hle := msbVal_cons_le (bv x p w) b (xs.map (bv x p)) bs (by simpa using hl)
    have hrv := hr.valid.ext hn.ext
    cases b
    · have h := andW_spec x _ _ _ hn.valid hrv
      refine ⟨hr.ext.trans (hn.ext.trans h.ext), h.valid, ?_⟩
      simp only [leConst, Bool.false_eq_true, ↓reduceIte, List.map_cons]
      rw [h.value, bv_ext x hn.ext hr.valid, hn.value, hr.value, bv_ext x hr.ext (hv w (by simp))]
      rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq] at hle ⊢
      rw [hle]; cases bv x p w <;> simp
    · have h := orW_spec x _ _ _ hn.valid hrv
      refine ⟨hr.ext.trans (hn.ext.trans h.ext), h.valid, ?_⟩
      simp only [leConst, ↓reduceIte, List.map_cons]
      rw [h.value, bv_ext x hn.ext hr.valid, hn.value, hr.value, bv_ext x hr.ext (hv w (by simp))]
      rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq] at hle ⊢
      rw [hle]; cases bv x p w <;> simp

/-! ### Boolean combinations of comparisons -/

/-- Boolean combinations of comparisons of inputs (most significant first) with constants. -/
inductive BExp (ι : Type*) where
  /-- `msbVal as ≤` the number on the inputs `is`. -/
  | ge (is : List ι) (as : List Bool)
  /-- The number on the inputs `is` `≤ msbVal bs`. -/
  | le (is : List ι) (bs : List Bool)
  | not (e : BExp ι)
  | and (e f : BExp ι)
  | or (e f : BExp ι)

namespace BExp

/-- The value of an expression. -/
def eval (x : ι → Bool) : BExp ι → Bool
  | ge is as => decide (msbVal as ≤ msbVal (is.map x))
  | le is bs => decide (msbVal (is.map x) ≤ msbVal bs)
  | not e => !e.eval x
  | and e f => e.eval x && f.eval x
  | or e f => e.eval x || f.eval x

/-- Every comparison has a constant of the right length. -/
def WF : BExp ι → Prop
  | ge is as => is.length = as.length
  | le is bs => is.length = bs.length
  | not e => e.WF
  | and e f => e.WF ∧ f.WF
  | or e f => e.WF ∧ f.WF

end BExp

/-- Compile an expression after the program `p`. -/
def compile (p : SLP ι) : BExp ι → SLP ι × Wire ι
  | .ge is as => geConst p (is.map .input) as
  | .le is bs => leConst p (is.map .input) bs
  | .not e => let r := compile p e; notW r.1 r.2
  | .and e f => let r := compile p e; let s := compile r.1 f; andW s.1 r.2 s.2
  | .or e f => let r := compile p e; let s := compile r.1 f; orW s.1 r.2 s.2

theorem map_bv_input (x : ι → Bool) (p : SLP ι) (is : List ι) :
    (is.map Wire.input).map (bv x p) = is.map x := by
  simp only [List.map_map]; rfl

/-- **The compiled program computes the expression.** -/
theorem compile_spec (x : ι → Bool) : ∀ (e : BExp ι) (p : SLP ι), e.WF →
    Spec1 x p (compile p e) (e.eval x)
  | .ge is as, p, h => by
    have := geConst_spec x p (is.map .input) as (by simpa [BExp.WF] using h)
      (fun w hw => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hw; trivial)
    rwa [map_bv_input] at this
  | .le is bs, p, h => by
    have := leConst_spec x p (is.map .input) bs (by simpa [BExp.WF] using h)
      (fun w hw => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hw; trivial)
    rwa [map_bv_input] at this
  | .not e, p, h => by
    have he := compile_spec x e p h
    have hn := notW_spec x _ _ he.valid
    exact ⟨he.ext.trans hn.ext, hn.valid, by
      simp only [compile]; rw [hn.value, he.value]; rfl⟩
  | .and e f, p, h => by
    have he := compile_spec x e p h.1
    have hf := compile_spec x f (compile p e).1 h.2
    have ha := andW_spec x _ _ _ (he.valid.ext hf.ext) hf.valid
    refine ⟨he.ext.trans (hf.ext.trans ha.ext), ha.valid, ?_⟩
    simp only [compile]
    rw [ha.value, bv_ext x hf.ext he.valid, he.value, hf.value]; rfl
  | .or e f, p, h => by
    have he := compile_spec x e p h.1
    have hf := compile_spec x f (compile p e).1 h.2
    have ha := orW_spec x _ _ _ (he.valid.ext hf.ext) hf.valid
    refine ⟨he.ext.trans (hf.ext.trans ha.ext), ha.valid, ?_⟩
    simp only [compile]
    rw [ha.value, bv_ext x hf.ext he.valid, he.value, hf.value]; rfl

end SLP

namespace SLP

variable {ι : Type*}

theorem length_notW (p : SLP ι) (a : Wire ι) : (notW p a).1.length = p.length + 1 := by
  simp [notW, addNand]

theorem length_andW (p : SLP ι) (a b : Wire ι) : (andW p a b).1.length = p.length + 2 := by
  simp [andW, notW, addNand]

theorem length_orW (p : SLP ι) (a b : Wire ι) : (orW p a b).1.length = p.length + 3 := by
  simp [orW, notW, addNand]

theorem length_geConst (p : SLP ι) : ∀ (xs : List (Wire ι)) (as : List Bool),
    (geConst p xs as).1.length ≤ p.length + 3 * xs.length
  | x :: xs, a :: as => by
    have ih := length_geConst p xs as
    simp only [geConst, List.length_cons]
    split_ifs
    · rw [length_andW]; omega
    · rw [length_orW]; omega
  | [], _ => by simp [geConst]
  | _ :: _, [] => by simp [geConst]

theorem length_leConst (p : SLP ι) : ∀ (xs : List (Wire ι)) (bs : List Bool),
    (leConst p xs bs).1.length ≤ p.length + 4 * xs.length
  | x :: xs, b :: bs => by
    have ih := length_leConst p xs bs
    simp only [leConst, List.length_cons]
    split_ifs
    · rw [length_orW, length_notW]; omega
    · rw [length_andW, length_notW]; omega
  | [], _ => by simp [leConst]
  | _ :: _, [] => by simp [leConst]

end SLP

namespace SLP.BExp

variable {ι : Type*}

/-- A bound on the number of gates of the compiled expression. -/
def size : BExp ι → ℕ
  | ge is _ => 3 * is.length
  | le is _ => 4 * is.length
  | not e => e.size + 1
  | and e f => e.size + f.size + 2
  | or e f => e.size + f.size + 3

end SLP.BExp

namespace SLP

variable {ι : Type*}

theorem length_compile : ∀ (e : BExp ι) (p : SLP ι), (compile p e).1.length ≤ p.length + e.size
  | .ge is as, p => by simpa [compile, BExp.size] using length_geConst p (is.map .input) as
  | .le is bs, p => by simpa [compile, BExp.size] using length_leConst p (is.map .input) bs
  | .not e, p => by
    have := length_compile e p
    simp only [compile, length_notW, BExp.size]; omega
  | .and e f, p => by
    have h1 := length_compile e p
    have h2 := length_compile f (compile p e).1
    simp only [compile, length_andW, BExp.size]; omega
  | .or e f, p => by
    have h1 := length_compile e p
    have h2 := length_compile f (compile p e).1
    simp only [compile, length_orW, BExp.size]; omega

end SLP

end SigabaNeo.Lattices
