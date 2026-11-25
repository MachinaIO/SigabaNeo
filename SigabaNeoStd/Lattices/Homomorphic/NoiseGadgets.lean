import SigabaNeoStd.Lattices.Homomorphic.BoolArith
import SigabaNeoStd.Lattices.Homomorphic.SLPEval

/-!
# The noise of the Boolean gadgets

The noise bound of a wire (`slpBound WN E`: `E` at the inputs, `0` at `1`, `WN · E_a + E_b` at a
NAND) through the gadgets of `BoolBuild` and `BoolArith`, with `W₁ = WN + 1`:

* `notW` is free (`NAND(1, a)`); `andW`, `orW` multiply by `W₁`; `xorW` by `2 W₁²` (of the sum of
  the bounds); `muxW` by `W₁²` (of the sum);
* `fullAdd`: the carry grows by `2 W₁² A` only (the incoming carry enters gates on the right);
* `rippleAdd` on `n` bits: at most `(4n + 10) W₁⁴ A`;
* `modAdd`, `modSub` on `w` bits: at most `modFactor WN w · A`.
-/

namespace SigabaNeo.Lattices

namespace SLP

variable {ι : Type*} (WN E : ℕ)

/-- The noise bound of a wire. -/
abbrev nb (p : SLP ι) (w : Wire ι) : ℕ := slpBound WN E p w

theorem nb_ext {p p' : SLP ι} (h : Ext p p') {w : Wire ι} (hw : Valid p w) :
    nb WN E p' w = nb WN E p w :=
  valueOf_ext _ _ _ h hw

theorem nb_one (p : SLP ι) : nb WN E p .one = 0 := rfl

theorem nb_input (p : SLP ι) (i : ι) : nb WN E p (.input i) = E := rfl

/-- The value of the wire of an appended gate. -/
theorem valueOf_addNand {α : Type*} (inp : ι → α) (one : α) (step : α → α → α) (p : SLP ι)
    (a b : Wire ι) :
    valueOf inp one step (addNand p a b).1 (addNand p a b).2 =
      step (valueOf inp one step p a) (valueOf inp one step p b) := by
  simp only [valueOf, addNand, values, wireVal]
  rw [run_append]
  simp only [run]
  have hlen : (run inp one step p []).length = p.length := length_values inp one step p
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hlen, List.length_singleton]; omega),
    List.getElem_append_right (by rw [hlen])]
  simp only [hlen, Nat.sub_self, List.getElem_singleton]
  rfl

theorem nb_addNand (p : SLP ι) (a b : Wire ι) :
    nb WN E (addNand p a b).1 (addNand p a b).2 = WN * nb WN E p a + nb WN E p b :=
  valueOf_addNand _ _ _ p a b

/-- Chaining for noise: a gate whose inputs are valid in an earlier program. -/
theorem nb_addNand_of {p p' : SLP ι} (h : Ext p p') {a b : Wire ι} (ha : Valid p a)
    (hb : Valid p b) :
    nb WN E (addNand p' a b).1 (addNand p' a b).2 = WN * nb WN E p a + nb WN E p b := by
  rw [nb_addNand, nb_ext WN E h ha, nb_ext WN E h hb]

theorem nb_addNand_ext (p : SLP ι) (a b : Wire ι) {w : Wire ι} (hw : Valid p w) :
    nb WN E (addNand p a b).1 w = nb WN E p w :=
  nb_ext WN E (addNand_ext p a b) hw

theorem valid_addNand_of (p : SLP ι) (a b : Wire ι) {w : Wire ι} (hw : Valid p w) :
    Valid (addNand p a b).1 w :=
  hw.ext (addNand_ext p a b)

theorem valid_one (p : SLP ι) : Valid p (.one : Wire ι) := trivial

/-! ### Logic gates -/

theorem nb_notW (p : SLP ι) (a : Wire ι) : nb WN E (notW p a).1 (notW p a).2 = nb WN E p a := by
  simp [notW, nb_addNand, nb_one]

theorem nb_andW (p : SLP ι) (a b : Wire ι) :
    nb WN E (andW p a b).1 (andW p a b).2 = WN * nb WN E p a + nb WN E p b := by
  simp only [andW, nb_notW, nb_addNand]

theorem nb_orW (p : SLP ι) (a b : Wire ι) (ha : Valid p a) (hb : Valid p b) :
    nb WN E (orW p a b).1 (orW p a b).2 = WN * nb WN E p a + nb WN E p b := by
  simp only [orW, notW, nb_addNand, nb_one, nb_addNand_ext WN E _ _ _ (valid_addNand_of _ _ _ hb),
    nb_addNand_ext WN E _ _ _ (addNand_valid _ _ _), nb_addNand_ext WN E _ _ _ hb]
  ring

theorem nb_xorW (p : SLP ι) (a b : Wire ι) (ha : Valid p a) (hb : Valid p b) :
    nb WN E (xorW p a b).1 (xorW p a b).2 =
      WN * (WN * nb WN E p a + (WN * nb WN E p a + nb WN E p b)) +
        (WN * nb WN E p b + (WN * nb WN E p a + nb WN E p b)) := by
  have h1 := addNand_valid p a b
  have ha1 := valid_addNand_of p a b ha
  have hb1 := valid_addNand_of p a b hb
  have h2 := addNand_valid (addNand p a b).1 a (addNand p a b).2
  have hb2 := valid_addNand_of _ a (addNand p a b).2 hb1
  have h12 := valid_addNand_of _ a (addNand p a b).2 h1
  simp only [xorW, nb_addNand, nb_addNand_ext WN E _ _ _ h2, nb_addNand_ext WN E _ _ _ hb1,
    nb_addNand_ext WN E _ _ _ h1, nb_addNand_ext WN E _ _ _ ha, nb_addNand_ext WN E _ _ _ hb,
    nb_addNand_ext WN E _ _ _ h12, nb_addNand_ext WN E _ _ _ hb2]

theorem nb_muxW (p : SLP ι) (s a b : Wire ι) (hs : Valid p s) (ha : Valid p a) (hb : Valid p b) :
    nb WN E (muxW p s a b).1 (muxW p s a b).2 =
      WN * (WN * nb WN E p s + nb WN E p a) + (WN * nb WN E p s + nb WN E p b) := by
  have h1 := addNand_valid p .one s
  have hs1 := valid_addNand_of p .one s hs
  have ha1 := valid_addNand_of p .one s ha
  have hb1 := valid_addNand_of p .one s hb
  have h12 := valid_addNand_of _ s a h1
  have hb2 := valid_addNand_of _ s a hb1
  have h2 := addNand_valid (addNand p .one s).1 s a
  simp only [muxW, notW, nb_addNand, nb_one, nb_addNand_ext WN E _ _ _ h2,
    nb_addNand_ext WN E _ _ _ h12, nb_addNand_ext WN E _ _ _ hb2, nb_addNand_ext WN E _ _ _ hs1,
    nb_addNand_ext WN E _ _ _ ha1, nb_addNand_ext WN E _ _ _ hb1, nb_addNand_ext WN E _ _ _ h1,
    nb_addNand_ext WN E _ _ _ hs, nb_addNand_ext WN E _ _ _ ha, nb_addNand_ext WN E _ _ _ hb]
  ring

/-! ### Bounds -/

theorem xor_bound (WN X Y : ℕ) :
    WN * (WN * X + (WN * X + Y)) + (WN * Y + (WN * X + Y)) ≤ 2 * (WN + 1) ^ 2 * (X + Y) := by
  nlinarith [Nat.zero_le WN, Nat.zero_le X, Nat.zero_le Y, Nat.zero_le (WN * X), Nat.zero_le (WN * Y),
    Nat.zero_le (WN * WN * X), Nat.zero_le (WN * WN * Y)]

theorem nb_xorW_le (p : SLP ι) (a b : Wire ι) (ha : Valid p a) (hb : Valid p b) {X Y : ℕ}
    (hX : nb WN E p a ≤ X) (hY : nb WN E p b ≤ Y) :
    nb WN E (xorW p a b).1 (xorW p a b).2 ≤ 2 * (WN + 1) ^ 2 * (X + Y) := by
  rw [nb_xorW WN E p a b ha hb]
  refine le_trans ?_ (xor_bound WN X Y)
  gcongr

/-! ### The full adder -/

/-- The noise of a full adder: the sum bit within `2 W₁² (2 W₁² A + C)`, the carry within
`2 W₁² A + C`, for inputs within `A` and the incoming carry within `C`. -/
theorem nb_fullAdd (p : SLP ι) (a b c : Wire ι) (ha : Valid p a) (hb : Valid p b)
    (hc : Valid p c) {A C : ℕ} (hA : nb WN E p a ≤ A) (hB : nb WN E p b ≤ A)
    (hC : nb WN E p c ≤ C) :
    nb WN E (fullAdd p a b c).1 (fullAdd p a b c).2.1 ≤
        2 * (WN + 1) ^ 2 * (2 * (WN + 1) ^ 2 * (A + A) + C) ∧
      nb WN E (fullAdd p a b c).1 (fullAdd p a b c).2.2 ≤ 2 * (WN + 1) * WN * A + C := by
  let x₀ : ι → Bool := fun _ => true
  have h1 := xorW_spec x₀ p a b ha hb
  have h2 := xorW_spec x₀ _ _ c h1.valid (hc.ext h1.ext)
  have e12 := h1.ext.trans h2.ext
  have h3 := addNand_spec x₀ _ a b (ha.ext e12) (hb.ext e12)
  have e13 := e12.trans h3.ext
  have h4 := orW_spec x₀ _ a b (ha.ext e13) (hb.ext e13)
  have e14 := e13.trans h4.ext
  have h5 := addNand_spec x₀ _ _ c h4.valid (hc.ext e14)
  have h6 := addNand_spec x₀ _ _ _ (h3.valid.ext (h4.ext.trans h5.ext)) h5.valid
  have e36 := h3.ext.trans (h4.ext.trans (h5.ext.trans h6.ext))
  -- the sum bit
  have ht := nb_xorW_le WN E p a b ha hb hA hB
  have hs := nb_xorW_le WN E _ _ c h1.valid (hc.ext h1.ext) (Y := C) ht
    (by rw [nb_ext WN E h1.ext hc]; exact hC)
  refine ⟨?_, ?_⟩
  · simp only [fullAdd]
    rw [nb_ext WN E e36 h2.valid]
    exact hs
  · simp only [fullAdd]
    rw [nb_addNand, nb_ext WN E (h4.ext.trans h5.ext) h3.valid, nb_addNand, nb_addNand, nb_orW WN E _ a b (ha.ext e13) (hb.ext e13),
      nb_ext WN E e13 ha, nb_ext WN E e13 hb, nb_ext WN E e12 ha, nb_ext WN E e12 hb,
      nb_ext WN E e14 hc]
    have : WN * (WN * nb WN E p a + nb WN E p b) +
        (WN * (WN * nb WN E p a + nb WN E p b) + nb WN E p c) ≤
        WN * (WN * A + A) + (WN * (WN * A + A) + C) := by gcongr
    refine this.trans (le_of_eq ?_)
    ring

/-- All wires of a list are within `A`. -/
def NBL (p : SLP ι) (ws : List (Wire ι)) (A : ℕ) : Prop := ∀ w ∈ ws, nb WN E p w ≤ A

theorem NBL.ext {p p' : SLP ι} (h : Ext p p') {ws : List (Wire ι)} (hv : AllValid p ws) {A : ℕ}
    (hA : NBL WN E p ws A) : NBL WN E p' ws A := fun w hw => by
  rw [nb_ext WN E h (hv w hw)]; exact hA w hw

theorem NBL.mono {p : SLP ι} {ws : List (Wire ι)} {A B : ℕ} (hA : NBL WN E p ws A) (h : A ≤ B) :
    NBL WN E p ws B := fun w hw => (hA w hw).trans h

/-- **The noise of a ripple adder**: the carry grows additively along the bits. -/
theorem nb_rippleAdd : ∀ (p : SLP ι) (as bs : List (Wire ι)) (c : Wire ι),
    AllValid p as → AllValid p bs → Valid p c → as.length = bs.length → ∀ {A C : ℕ},
    NBL WN E p as A → NBL WN E p bs A → nb WN E p c ≤ C →
    NBL WN E (rippleAdd p as bs c).1 (rippleAdd p as bs c).2
      (2 * (WN + 1) ^ 2 * (2 * (WN + 1) ^ 2 * (A + A) + (C + as.length * (2 * (WN + 1) * WN * A))))
  | p, [], [], c, _, _, _, _, A, C, _, _, hC => by
    intro w hw
    simp only [rippleAdd, List.mem_singleton] at hw
    subst hw
    refine hC.trans ?_
    have : 0 < 2 * (WN + 1) ^ 2 := by positivity
    calc C ≤ 2 * (WN + 1) ^ 2 * C := Nat.le_mul_of_pos_left _ this
      _ ≤ _ := by gcongr; simp
  | p, a :: as, b :: bs, c, ha, hb, hc, hlen, A, C, hA, hB, hC => by
    let x₀ : ι → Bool := fun _ => true
    have ha0 := ha a (List.mem_cons_self ..)
    have hb0 := hb b (List.mem_cons_self ..)
    obtain ⟨e1, hs, hk, -⟩ := fullAdd_spec x₀ p a b c ha0 hb0 hc
    obtain ⟨hns, hnk⟩ := nb_fullAdd WN E p a b c ha0 hb0 hc (hA a (List.mem_cons_self ..))
      (hB b (List.mem_cons_self ..)) hC
    have has : AllValid (fullAdd p a b c).1 as := fun v hv => (ha v (List.mem_cons_of_mem _ hv)).ext e1
    have hbs : AllValid (fullAdd p a b c).1 bs := fun v hv => (hb v (List.mem_cons_of_mem _ hv)).ext e1
    have hAs : NBL WN E (fullAdd p a b c).1 as A :=
      NBL.ext WN E e1 (fun v hv => ha v (List.mem_cons_of_mem _ hv))
        (fun v hv => hA v (List.mem_cons_of_mem _ hv))
    have hBs : NBL WN E (fullAdd p a b c).1 bs A :=
      NBL.ext WN E e1 (fun v hv => hb v (List.mem_cons_of_mem _ hv))
        (fun v hv => hB v (List.mem_cons_of_mem _ hv))
    have ih := nb_rippleAdd (fullAdd p a b c).1 as bs (fullAdd p a b c).2.2 has hbs hk
      (by simpa using hlen) hAs hBs hnk
    have hspec := rippleAdd_spec x₀ (fullAdd p a b c).1 as bs (fullAdd p a b c).2.2 has hbs hk
      (by simpa using hlen)
    have heq : 2 * (WN + 1) * WN * A + C + as.length * (2 * (WN + 1) * WN * A) =
        C + (a :: as).length * (2 * (WN + 1) * WN * A) := by
      simp only [List.length_cons]; ring
    intro w hw
    simp only [rippleAdd, List.mem_cons] at hw
    rcases hw with rfl | hw
    · change nb WN E (rippleAdd (fullAdd p a b c).1 as bs (fullAdd p a b c).2.2).1 _ ≤ _
      rw [nb_ext WN E hspec.ext hs]
      refine hns.trans ?_
      gcongr
      exact Nat.le_add_right _ _
    · have := ih w hw
      rw [heq] at this
      exact this
  | p, [], _ :: _, _, _, _, _, hlen, _, _, _, _, _ => by simp at hlen
  | p, _ :: _, [], _, _, _, _, hlen, _, _, _, _, _ => by simp at hlen

/-! ### Bitwise gadgets -/

theorem nb_andL (d : Wire ι) : ∀ (p : SLP ι) (as : List (Wire ι)), Valid p d → AllValid p as →
    ∀ {D A : ℕ}, nb WN E p d ≤ D → NBL WN E p as A →
    NBL WN E (andL d p as).1 (andL d p as).2 (WN * D + A)
  | p, [], _, _, _, _, _, _ => by simp [NBL, andL]
  | p, a :: as, hd, ha, D, A, hD, hA => by
    let x₀ : ι → Bool := fun _ => true
    have ha0 := ha a (List.mem_cons_self ..)
    have h1 := andW_spec x₀ p d a hd ha0
    have has : AllValid (andW p d a).1 as := fun v hv => (ha v (List.mem_cons_of_mem _ hv)).ext h1.ext
    have ih := nb_andL d (andW p d a).1 as (hd.ext h1.ext) has (D := D)
      (by rw [nb_ext WN E h1.ext hd]; exact hD)
      (NBL.ext WN E h1.ext (fun v hv => ha v (List.mem_cons_of_mem _ hv))
        (fun v hv => hA v (List.mem_cons_of_mem _ hv)))
    have hspec := andL_spec x₀ d (andW p d a).1 as (hd.ext h1.ext) has
    intro w hw
    simp only [andL, List.mem_cons] at hw
    rcases hw with rfl | hw
    · change nb WN E (andL d (andW p d a).1 as).1 _ ≤ _
      rw [nb_ext WN E hspec.ext h1.valid, nb_andW]
      gcongr
      exact hA a (List.mem_cons_self ..)
    · exact ih w hw

theorem nb_notL : ∀ (p : SLP ι) (as : List (Wire ι)), AllValid p as → ∀ {A : ℕ},
    NBL WN E p as A → NBL WN E (notL p as).1 (notL p as).2 A
  | p, [], _, _, _ => by simp [NBL, notL]
  | p, a :: as, ha, A, hA => by
    let x₀ : ι → Bool := fun _ => true
    have ha0 := ha a (List.mem_cons_self ..)
    have h1 := notW_spec x₀ p a ha0
    have has : AllValid (notW p a).1 as := fun v hv => (ha v (List.mem_cons_of_mem _ hv)).ext h1.ext
    have ih := nb_notL (notW p a).1 as has
      (NBL.ext WN E h1.ext (fun v hv => ha v (List.mem_cons_of_mem _ hv))
        (fun v hv => hA v (List.mem_cons_of_mem _ hv)))
    have hspec := notL_spec x₀ (notW p a).1 as has
    intro w hw
    simp only [notL, List.mem_cons] at hw
    rcases hw with rfl | hw
    · change nb WN E (notL (notW p a).1 as).1 _ ≤ _
      rw [nb_ext WN E hspec.ext h1.valid, nb_notW]
      exact hA a (List.mem_cons_self ..)
    · exact ih w hw

theorem nb_muxL (s : Wire ι) : ∀ (p : SLP ι) (as bs : List (Wire ι)), Valid p s →
    AllValid p as → AllValid p bs → as.length = bs.length → ∀ {S A : ℕ}, nb WN E p s ≤ S →
    NBL WN E p as A → NBL WN E p bs A →
    NBL WN E (muxL s p as bs).1 (muxL s p as bs).2 (WN * (WN * S + A) + (WN * S + A))
  | p, [], [], _, _, _, _, _, _, _, _, _ => by simp [NBL, muxL]
  | p, a :: as, b :: bs, hs, ha, hb, hlen, S, A, hS, hA, hB => by
    let x₀ : ι → Bool := fun _ => true
    have ha0 := ha a (List.mem_cons_self ..)
    have hb0 := hb b (List.mem_cons_self ..)
    have h1 := muxW_spec x₀ p s a b hs ha0 hb0
    have has : AllValid (muxW p s a b).1 as := fun v hv => (ha v (List.mem_cons_of_mem _ hv)).ext h1.ext
    have hbs : AllValid (muxW p s a b).1 bs := fun v hv => (hb v (List.mem_cons_of_mem _ hv)).ext h1.ext
    have ih := nb_muxL s (muxW p s a b).1 as bs (hs.ext h1.ext) has hbs (by simpa using hlen)
      (S := S) (by rw [nb_ext WN E h1.ext hs]; exact hS)
      (NBL.ext WN E h1.ext (fun v hv => ha v (List.mem_cons_of_mem _ hv))
        (fun v hv => hA v (List.mem_cons_of_mem _ hv)))
      (NBL.ext WN E h1.ext (fun v hv => hb v (List.mem_cons_of_mem _ hv))
        (fun v hv => hB v (List.mem_cons_of_mem _ hv)))
    have hspec := muxL_spec x₀ s (muxW p s a b).1 as bs (hs.ext h1.ext) has hbs (by simpa using hlen)
    intro w hw
    simp only [muxL, List.mem_cons] at hw
    rcases hw with rfl | hw
    · change nb WN E (muxL s (muxW p s a b).1 as bs).1 _ ≤ _
      rw [nb_ext WN E hspec.ext h1.valid, nb_muxW WN E p s a b hs ha0 hb0]
      have := hA a (List.mem_cons_self ..)
      have := hB b (List.mem_cons_self ..)
      gcongr
    · exact ih w hw
  | p, [], _ :: _, _, _, _, hlen, _, _, _, _, _ => by simp at hlen
  | p, _ :: _, [], _, _, _, hlen, _, _, _, _, _ => by simp at hlen

theorem nb_constL (p : SLP ι) (z : Wire ι) : ∀ (w m : ℕ), NBL WN E p (constL z w m) (nb WN E p z)
  | 0, _ => by simp [NBL, constL]
  | w + 1, m => by
    intro v hv
    simp only [constL, List.mem_cons] at hv
    rcases hv with rfl | hv
    · split_ifs
      · simp [nb_one]
      · exact le_rfl
    · exact nb_constL p z w (m / 2) v hv

theorem AllValid_constL (p : SLP ι) (z : Wire ι) (hz : Valid p z) :
    ∀ (w m : ℕ), AllValid p (constL z w m)
  | 0, _ => by simp [AllValid, constL]
  | w + 1, m => by
    intro v hv
    simp only [constL, List.mem_cons] at hv
    rcases hv with rfl | hv
    · split_ifs
      · trivial
      · exact hz
    · exact AllValid_constL p z hz w (m / 2) v hv

/-! ### Modular addition and subtraction -/

/-- The bound of a ripple adder on `n` bits with inputs and carry within `X`. -/
theorem ripple_bound (WN X n : ℕ) :
    2 * (WN + 1) ^ 2 * (2 * (WN + 1) ^ 2 * (X + X) + (X + n * (2 * (WN + 1) * WN * X))) ≤
      (4 * n + 10) * (WN + 1) ^ 4 * X := by
  have h1 : 1 ≤ (WN + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : (WN + 1) * WN ≤ (WN + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (by omega)
  calc 2 * (WN + 1) ^ 2 * (2 * (WN + 1) ^ 2 * (X + X) + (X + n * (2 * (WN + 1) * WN * X)))
      ≤ 2 * (WN + 1) ^ 2 * (2 * (WN + 1) ^ 2 * (X + X) + ((WN + 1) ^ 2 * X +
          n * (2 * (WN + 1) ^ 2 * X))) := by
        have e1 : X ≤ (WN + 1) ^ 2 * X := Nat.le_mul_of_pos_left _ h1
        have e2 : 2 * (WN + 1) * WN * X ≤ 2 * (WN + 1) ^ 2 * X := by
          rw [show 2 * (WN + 1) * WN * X = 2 * ((WN + 1) * WN) * X by ring]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
        exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.add_le_add e1
          (Nat.mul_le_mul_left _ e2)) _)
    _ = (4 * n + 10) * (WN + 1) ^ 4 * X := by ring

theorem nb_getD {p : SLP ι} {ws : List (Wire ι)} {A : ℕ} (h : NBL WN E p ws A) (i : ℕ) :
    nb WN E p (ws.getD i .one) ≤ A := by
  by_cases hlt : i < ws.length
  · rw [List.getD_eq_getElem _ _ hlt]; exact h _ (List.getElem_mem hlt)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]; simp [nb_one]

theorem valid_getD {p : SLP ι} {ws : List (Wire ι)} (h : AllValid p ws) (i : ℕ) :
    Valid p (ws.getD i .one) := by
  by_cases hlt : i < ws.length
  · rw [List.getD_eq_getElem _ _ hlt]; exact h _ (List.getElem_mem hlt)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]; trivial

theorem length_constL (z : Wire ι) : ∀ (w m : ℕ), (constL z w m).length = w
  | 0, _ => rfl
  | w + 1, m => by simp [constL, length_constL z w (m / 2)]

/-- The factor of a modular addition or subtraction of `w`-bit numbers. -/
def modFactor (WN w : ℕ) : ℕ := (4 * w + 14) ^ 2 * (WN + 1) ^ 10

theorem mux_bound (WN X : ℕ) : WN * (WN * X + X) + (WN * X + X) = (WN + 1) ^ 2 * X := by ring

/-- **The noise of a modular addition.** -/
theorem nb_modAdd (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) (hz : Valid p z)
    (ha : AllValid p as) (hb : AllValid p bs) (hla : as.length = w) (hlb : bs.length = w)
    {A : ℕ} (hzA : nb WN E p z ≤ A) (hA : NBL WN E p as A) (hB : NBL WN E p bs A) :
    NBL WN E (modAdd z q w p as bs).1 (modAdd z q w p as bs).2 (modFactor WN w * A) := by
  let x₀ : ι → Bool := fun _ => true
  set r₁ := rippleAdd p as bs z with hr₁
  set K := constL z (w + 1) (2 ^ (w + 1) - q) with hK
  set r₂ := rippleAdd r₁.1 r₁.2 K z with hr₂
  set c := r₂.2.getD (w + 1) .one with hc
  set r₃ := muxL c r₂.1 (r₂.2.take (w + 1)) r₁.2 with hr₃
  have h1 := rippleAdd_spec x₀ p as bs z ha hb hz (by rw [hla, hlb])
  rw [← hr₁, hla] at h1
  have hz1 : Valid r₁.1 z := hz.ext h1.ext
  have hKv : AllValid r₁.1 K := AllValid_constL r₁.1 z hz1 _ _
  have hKl : K.length = w + 1 := length_constL z _ _
  set W₁ := WN + 1 with hW₁
  have hA1 : 1 ≤ W₁ := by omega
  -- the first adder
  have n1 := nb_rippleAdd WN E p as bs z ha hb hz (by rw [hla, hlb]) (A := A) (C := A) hA hB hzA
  rw [← hr₁, hla] at n1
  have n1' := n1.mono WN E (ripple_bound WN A w)
  set R₁ := (4 * w + 10) * (WN + 1) ^ 4 * A with hR₁
  have hAR : A ≤ R₁ := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by positivity))
  -- the second adder
  have h2 := rippleAdd_spec x₀ r₁.1 r₁.2 K z h1.valid hKv hz1 (by rw [h1.length, hKl])
  rw [← hr₂] at h2
  have hzR : nb WN E r₁.1 z ≤ R₁ := by rw [nb_ext WN E h1.ext hz]; exact hzA.trans hAR
  have n2 := nb_rippleAdd WN E r₁.1 r₁.2 K z h1.valid hKv hz1 (by rw [h1.length, hKl])
    (A := R₁) (C := R₁) n1' ((nb_constL WN E r₁.1 z _ _).mono WN E hzR) hzR
  rw [← hr₂, h1.length] at n2
  have n2' := n2.mono WN E (ripple_bound WN R₁ (w + 1))
  set R₂ := (4 * (w + 1) + 10) * (WN + 1) ^ 4 * R₁ with hR₂
  have hR12 : R₁ ≤ R₂ := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by positivity))
  -- the selection
  have hcv : Valid r₂.1 c := valid_getD h2.valid _
  have htake : AllValid r₂.1 (r₂.2.take (w + 1)) := fun v hv => h2.valid v (List.mem_of_mem_take hv)
  have h3 := muxL_spec x₀ c r₂.1 (r₂.2.take (w + 1)) r₁.2 hcv htake (h1.valid.ext h2.ext)
    (by simp only [List.length_take, h2.length, h1.length]; omega)
  have n3 := nb_muxL WN E c r₂.1 (r₂.2.take (w + 1)) r₁.2 hcv htake (h1.valid.ext h2.ext)
    (by simp only [List.length_take, h2.length, h1.length]; omega) (S := R₂) (A := R₂)
    (nb_getD WN E n2' _) (fun v hv => n2' v (List.mem_of_mem_take hv))
    ((NBL.ext WN E h2.ext h1.valid n1').mono WN E hR12)
  rw [← hr₃, mux_bound] at n3
  intro v hv
  have hv' : v ∈ r₃.2 := List.mem_of_mem_take hv
  refine (n3 v hv').trans (le_of_eq_of_le rfl ?_)
  rw [hR₂, hR₁, modFactor]
  calc (WN + 1) ^ 2 * ((4 * (w + 1) + 10) * (WN + 1) ^ 4 * ((4 * w + 10) * (WN + 1) ^ 4 * A))
      = (4 * w + 14) * (4 * w + 10) * (WN + 1) ^ 10 * A := by ring
    _ ≤ (4 * w + 14) * (4 * w + 14) * (WN + 1) ^ 10 * A := by gcongr; omega
    _ = (4 * w + 14) ^ 2 * (WN + 1) ^ 10 * A := by ring

/-- **The noise of a modular subtraction.** -/
theorem nb_modSub (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) (hz : Valid p z)
    (ha : AllValid p as) (hb : AllValid p bs) (hla : as.length = w) (hlb : bs.length = w)
    {A : ℕ} (hzA : nb WN E p z ≤ A) (hA : NBL WN E p as A) (hB : NBL WN E p bs A) :
    NBL WN E (modSub z q w p as bs).1 (modSub z q w p as bs).2 (modFactor WN w * A) := by
  let x₀ : ι → Bool := fun _ => true
  set r₁ := notL p bs with hr₁
  set r₂ := rippleAdd r₁.1 as r₁.2 .one with hr₂
  set K := constL z w q with hK
  set r₃ := rippleAdd r₂.1 (r₂.2.take w) K z with hr₃
  have h1 := notL_spec x₀ p bs hb
  rw [← hr₁] at h1
  have n1 := nb_notL WN E p bs hb hB
  rw [← hr₁] at n1
  have h2 := rippleAdd_spec x₀ r₁.1 as r₁.2 .one (ha.ext h1.ext) h1.valid trivial
    (by rw [hla, h1.length, hlb])
  rw [← hr₂, hla] at h2
  have n2 := nb_rippleAdd WN E r₁.1 as r₁.2 .one (ha.ext h1.ext) h1.valid trivial
    (by rw [hla, h1.length, hlb]) (A := A) (C := A) (NBL.ext WN E h1.ext ha hA) n1
    (by simp [nb_one])
  rw [← hr₂, hla] at n2
  have n2' := n2.mono WN E (ripple_bound WN A w)
  set R₁ := (4 * w + 10) * (WN + 1) ^ 4 * A with hR₁
  have hAR : A ≤ R₁ := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by positivity))
  have hz2 : Valid r₂.1 z := hz.ext (h1.ext.trans h2.ext)
  have hzR : nb WN E r₂.1 z ≤ R₁ := by
    rw [nb_ext WN E (h1.ext.trans h2.ext) hz]; exact hzA.trans hAR
  have htake2 : AllValid r₂.1 (r₂.2.take w) := fun v hv => h2.valid v (List.mem_of_mem_take hv)
  have hKv : AllValid r₂.1 K := AllValid_constL r₂.1 z hz2 _ _
  have hlt : (r₂.2.take w).length = K.length := by
    simp only [List.length_take, h2.length, hK, length_constL]; omega
  have h3 := rippleAdd_spec x₀ r₂.1 (r₂.2.take w) K z htake2 hKv hz2 hlt
  rw [← hr₃] at h3
  have n3 := nb_rippleAdd WN E r₂.1 (r₂.2.take w) K z htake2 hKv hz2 hlt (A := R₁) (C := R₁)
    (fun v hv => n2' v (List.mem_of_mem_take hv)) ((nb_constL WN E r₂.1 z _ _).mono WN E hzR) hzR
  rw [← hr₃] at n3
  have hlw : (r₂.2.take w).length = w := by simp only [List.length_take, h2.length]; omega
  rw [hlw] at n3
  have n3' := n3.mono WN E (ripple_bound WN R₁ w)
  set R₂ := (4 * w + 10) * (WN + 1) ^ 4 * R₁ with hR₂
  have hR12 : R₁ ≤ R₂ := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by positivity))
  have hcv : Valid r₃.1 (r₂.2.getD w .one) := (valid_getD h2.valid _).ext h3.ext
  have htake3 : AllValid r₃.1 (r₃.2.take w) := fun v hv => h3.valid v (List.mem_of_mem_take hv)
  have hl3 : (r₂.2.take w).length = (r₃.2.take w).length := by
    simp only [List.length_take, h3.length, h2.length, hlw]; omega
  have n4 := nb_muxL WN E (r₂.2.getD w .one) r₃.1 (r₂.2.take w) (r₃.2.take w) hcv
    (htake2.ext h3.ext) htake3 hl3 (S := R₂) (A := R₂)
    (by rw [nb_ext WN E h3.ext (valid_getD h2.valid _)]; exact (nb_getD WN E n2' _).trans hR12)
    ((NBL.ext WN E h3.ext htake2 fun v hv => n2' v (List.mem_of_mem_take hv)).mono WN E hR12)
    (fun v hv => n3' v (List.mem_of_mem_take hv))
  rw [mux_bound] at n4
  intro v hv
  refine (n4 v hv).trans (le_of_eq_of_le rfl ?_)
  rw [hR₂, hR₁, modFactor]
  calc (WN + 1) ^ 2 * ((4 * w + 10) * (WN + 1) ^ 4 * ((4 * w + 10) * (WN + 1) ^ 4 * A))
      = (4 * w + 10) * (4 * w + 10) * (WN + 1) ^ 10 * A := by ring
    _ ≤ (4 * w + 14) * (4 * w + 14) * (WN + 1) ^ 10 * A := by gcongr <;> omega
    _ = (4 * w + 14) ^ 2 * (WN + 1) ^ 10 * A := by ring

end SLP

end SigabaNeo.Lattices
