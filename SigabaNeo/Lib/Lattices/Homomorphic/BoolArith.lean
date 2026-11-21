import SigabaNeo.Lib.Lattices.Homomorphic.BoolBuild
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic

/-!
# Arithmetic on wires

Numbers are lists of wires, least significant bit first; `nv x p ws` is their value.

* `fullAdd`, `rippleAdd`: `nv` of the sum of two `w`-bit numbers and a carry, in `w + 1` bits
  (`rippleAdd_spec`).
* `constL z w m`: the `w` low bits of `m`, from `1` and a wire `z` of value `false`.
* `muxL`, `andL`, `notL`: bitwise, with their values.
* `modAdd`, `modSub`: addition and subtraction modulo `q` of numbers below `q ≤ 2^w`, in `w` bits
  (`modAdd_spec`, `modSub_spec`).
-/

namespace SigabaNeo.Lattices

namespace SLP

variable {ι : Type*} (x : ι → Bool)

/-- The value of a list of wires, least significant first. -/
def nv (p : SLP ι) : List (Wire ι) → ℕ
  | [] => 0
  | w :: ws => (bv x p w).toNat + 2 * nv p ws

/-- Every wire of the list is valid. -/
def AllValid (p : SLP ι) (ws : List (Wire ι)) : Prop := ∀ w ∈ ws, Valid p w

theorem AllValid.ext {p p' : SLP ι} (h : Ext p p') {ws : List (Wire ι)} (hw : AllValid p ws) :
    AllValid p' ws := fun w hw' => (hw w hw').ext h

theorem nv_ext {p p' : SLP ι} (h : Ext p p') {ws : List (Wire ι)} (hw : AllValid p ws) :
    nv x p' ws = nv x p ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [nv]
    rw [bv_ext x h (hw w (List.mem_cons_self ..)), ih fun v hv => hw v (List.mem_cons_of_mem _ hv)]

theorem nv_lt (p : SLP ι) (ws : List (Wire ι)) : nv x p ws < 2 ^ ws.length := by
  induction ws with
  | nil => simp [nv]
  | cons w ws ih =>
    simp only [nv, List.length_cons, pow_succ]
    have : (bv x p w).toNat ≤ 1 := Bool.toNat_le _
    omega

theorem nv_take (p : SLP ι) : ∀ (ws : List (Wire ι)) (n : ℕ), nv x p (ws.take n) = nv x p ws % 2 ^ n
  | [], n => by simp [nv]
  | w :: ws, 0 => by simp [nv, Nat.mod_one]
  | w :: ws, n + 1 => by
    simp only [List.take_succ_cons, nv, nv_take p ws n]
    rw [Nat.pow_succ', Nat.mod_mul]
    have : (bv x p w).toNat ≤ 1 := Bool.toNat_le _
    rw [show ((bv x p w).toNat + 2 * nv x p ws) / 2 = nv x p ws by omega,
      show ((bv x p w).toNat + 2 * nv x p ws) % 2 = (bv x p w).toNat by omega]

/-- The top bit: `nv ws = nv (take n ws) + 2^n · bit n` for a list of `n + 1` wires. -/
theorem nv_split (p : SLP ι) (ws : List (Wire ι)) (n : ℕ) (hn : ws.length = n + 1) :
    nv x p ws = nv x p (ws.take n) + 2 ^ n * (bv x p (ws.getD n .one)).toNat := by
  induction ws generalizing n with
  | nil => simp at hn
  | cons w ws ih =>
    cases n with
    | zero =>
      simp only [List.length_cons, Nat.add_left_inj] at hn
      cases ws with
      | nil => simp [nv]
      | cons _ _ => simp at hn
    | succ n =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
      simp only [nv, List.take_succ_cons, List.getD_cons_succ, ih n hn, Nat.pow_succ']
      ring

/-- A specification of a gadget returning a number. -/
structure SpecN (p : SLP ι) (r : SLP ι × List (Wire ι)) (len val : ℕ) : Prop where
  ext : Ext p r.1
  valid : AllValid r.1 r.2
  length : r.2.length = len
  value : nv x r.1 r.2 = val

/-! ### Adders -/

/-- A full adder: the sum bit and the carry. The carry is
`NAND(NAND(a, b), NAND(a ∨ b, c))`, with the incoming carry `c` only on the right of a gate, so its
noise is added, not multiplied (`slpBound`). -/
def fullAdd (p : SLP ι) (a b c : Wire ι) : SLP ι × Wire ι × Wire ι :=
  let (p₁, t) := xorW p a b
  let (p₂, s) := xorW p₁ t c
  let (p₃, n₁) := addNand p₂ a b
  let (p₄, o) := orW p₃ a b
  let (p₅, n₂) := addNand p₄ o c
  let (p₆, k) := addNand p₅ n₁ n₂
  (p₆, s, k)

theorem fullAdd_spec (p : SLP ι) (a b c : Wire ι) (ha : Valid p a) (hb : Valid p b)
    (hc : Valid p c) :
    let r := fullAdd p a b c
    Ext p r.1 ∧ Valid r.1 r.2.1 ∧ Valid r.1 r.2.2 ∧
      (bv x r.1 r.2.1).toNat + 2 * (bv x r.1 r.2.2).toNat =
        (bv x p a).toNat + (bv x p b).toNat + (bv x p c).toNat := by
  have h1 := xorW_spec x p a b ha hb
  have h2 := xorW_spec x _ _ c h1.valid (hc.ext h1.ext)
  have e12 := h1.ext.trans h2.ext
  have h3 := addNand_spec x _ a b (ha.ext e12) (hb.ext e12)
  have e13 := e12.trans h3.ext
  have h4 := orW_spec x _ a b (ha.ext e13) (hb.ext e13)
  have e14 := e13.trans h4.ext
  have h5 := addNand_spec x _ _ c h4.valid (hc.ext e14)
  have h6 := addNand_spec x _ _ _ (h3.valid.ext (h4.ext.trans h5.ext)) h5.valid
  have e36 := h3.ext.trans (h4.ext.trans (h5.ext.trans h6.ext))
  refine ⟨e14.trans (h5.ext.trans h6.ext), h2.valid.ext e36, h6.valid, ?_⟩
  simp only [fullAdd]
  rw [bv_ext x e36 h2.valid, h2.value, h6.value, bv_ext x (h4.ext.trans h5.ext) h3.valid,
    h3.value, h5.value, h4.value, h1.value, bv_ext x h1.ext hc, bv_ext x e12 ha, bv_ext x e12 hb,
    bv_ext x e13 ha, bv_ext x e13 hb, bv_ext x e14 hc]
  cases bv x p a <;> cases bv x p b <;> cases bv x p c <;> rfl

/-- The sum of two numbers of the same length and a carry, one bit longer. -/
def rippleAdd : SLP ι → List (Wire ι) → List (Wire ι) → Wire ι → SLP ι × List (Wire ι)
  | p, [], _, c => (p, [c])
  | p, _ :: _, [], c => (p, [c])
  | p, a :: as, b :: bs, c =>
    let r := fullAdd p a b c
    let r' := rippleAdd r.1 as bs r.2.2
    (r'.1, r.2.1 :: r'.2)

theorem rippleAdd_spec : ∀ (p : SLP ι) (as bs : List (Wire ι)) (c : Wire ι),
    AllValid p as → AllValid p bs → Valid p c → as.length = bs.length →
    SpecN x p (rippleAdd p as bs c) (as.length + 1) (nv x p as + nv x p bs + (bv x p c).toNat)
  | p, [], [], c, _, _, hc, _ => ⟨Ext.refl p, by
      intro v hv; simp only [rippleAdd, List.mem_singleton] at hv; subst hv; exact hc, rfl,
      by simp [rippleAdd, nv]⟩
  | p, a :: as, b :: bs, c, ha, hb, hc, hlen => by
    have hfa := fullAdd_spec x p a b c (ha a (List.mem_cons_self ..)) (hb b (List.mem_cons_self ..)) hc
    obtain ⟨e1, hs, hk, hval⟩ := hfa
    have has : AllValid (fullAdd p a b c).1 as := fun v hv => (ha v (List.mem_cons_of_mem _ hv)).ext e1
    have hbs : AllValid (fullAdd p a b c).1 bs := fun v hv => (hb v (List.mem_cons_of_mem _ hv)).ext e1
    have ih := rippleAdd_spec (fullAdd p a b c).1 as bs (fullAdd p a b c).2.2 has hbs hk
      (by simpa using hlen)
    refine ⟨e1.trans ih.ext, ?_, by simp [rippleAdd, ih.length], ?_⟩
    · intro v hv
      simp only [rippleAdd, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hs.ext ih.ext
      · exact ih.valid v hv
    · simp only [rippleAdd, nv]
      rw [ih.value, bv_ext x ih.ext hs, nv_ext x e1 (fun v hv => ha v (List.mem_cons_of_mem _ hv)),
        nv_ext x e1 (fun v hv => hb v (List.mem_cons_of_mem _ hv))]
      omega
  | p, [], _ :: _, _, _, _, _, hlen => by simp at hlen
  | p, _ :: _, [], _, _, _, _, hlen => by simp at hlen

/-! ### Bitwise operations and constants -/

/-- The `w` low bits of `m`, from `1` and a wire `z` of value `false`. -/
def constL (z : Wire ι) : ℕ → ℕ → List (Wire ι)
  | 0, _ => []
  | w + 1, m => (if m % 2 = 1 then .one else z) :: constL z w (m / 2)

theorem constL_spec (p : SLP ι) (z : Wire ι) (hz : Valid p z) (hz0 : bv x p z = false) :
    ∀ w m, AllValid p (constL z w m) ∧ (constL z w m).length = w ∧ nv x p (constL z w m) = m % 2 ^ w
  | 0, m => ⟨by simp [constL, AllValid], rfl, by simp [constL, nv, Nat.mod_one]⟩
  | w + 1, m => by
    obtain ⟨hv, hl, hn⟩ := constL_spec p z hz hz0 w (m / 2)
    refine ⟨?_, by simp [constL, hl], ?_⟩
    · intro v hv'
      simp only [constL, List.mem_cons] at hv'
      rcases hv' with rfl | hv'
      · split_ifs <;> trivial
      · exact hv v hv'
    · simp only [constL, nv, hn]
      rw [Nat.pow_succ', Nat.mod_mul]
      have hbit : (bv x p (if m % 2 = 1 then Wire.one else z)).toNat = m % 2 := by
        split_ifs with h
        · simp [bv, evalBool, valueOf, wireVal, h]
        · rw [hz0]; simp; omega
      rw [hbit]

/-- Bitwise `if s then a else b`. -/
def muxL (s : Wire ι) : SLP ι → List (Wire ι) → List (Wire ι) → SLP ι × List (Wire ι)
  | p, [], _ => (p, [])
  | p, _ :: _, [] => (p, [])
  | p, a :: as, b :: bs =>
    let r := muxW p s a b
    let r' := muxL s r.1 as bs
    (r'.1, r.2 :: r'.2)

theorem muxL_spec (s : Wire ι) : ∀ (p : SLP ι) (as bs : List (Wire ι)), Valid p s →
    AllValid p as → AllValid p bs → as.length = bs.length →
    SpecN x p (muxL s p as bs) as.length (if bv x p s then nv x p as else nv x p bs)
  | p, [], [], _, _, _, _ => ⟨Ext.refl p, by simp [AllValid, muxL], rfl, by simp [muxL, nv]⟩
  | p, a :: as, b :: bs, hs, ha, hb, hlen => by
    have h1 := muxW_spec x p s a b hs (ha a (List.mem_cons_self ..)) (hb b (List.mem_cons_self ..))
    have ih := muxL_spec s (muxW p s a b).1 as bs (hs.ext h1.ext)
      (fun v hv => (ha v (List.mem_cons_of_mem _ hv)).ext h1.ext)
      (fun v hv => (hb v (List.mem_cons_of_mem _ hv)).ext h1.ext) (by simpa using hlen)
    refine ⟨h1.ext.trans ih.ext, ?_, by simp [muxL, ih.length], ?_⟩
    · intro v hv
      simp only [muxL, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact h1.valid.ext ih.ext
      · exact ih.valid v hv
    · simp only [muxL, nv]
      rw [ih.value, bv_ext x ih.ext h1.valid, h1.value, bv_ext x h1.ext hs,
        nv_ext x h1.ext (fun v hv => ha v (List.mem_cons_of_mem _ hv)),
        nv_ext x h1.ext (fun v hv => hb v (List.mem_cons_of_mem _ hv))]
      split_ifs <;> rfl
  | p, [], _ :: _, _, _, _, hlen => by simp at hlen
  | p, _ :: _, [], _, _, _, hlen => by simp at hlen

/-- Bitwise `d ∧ a`. -/
def andL (d : Wire ι) : SLP ι → List (Wire ι) → SLP ι × List (Wire ι)
  | p, a :: as =>
    let r := andW p d a
    let r' := andL d r.1 as
    (r'.1, r.2 :: r'.2)
  | p, [] => (p, [])

theorem andL_spec (d : Wire ι) : ∀ (p : SLP ι) (as : List (Wire ι)), Valid p d → AllValid p as →
    SpecN x p (andL d p as) as.length (if bv x p d then nv x p as else 0)
  | p, [], _, _ => ⟨Ext.refl p, by simp [AllValid, andL], rfl, by simp [andL, nv]⟩
  | p, a :: as, hd, ha => by
    have h1 := andW_spec x p d a hd (ha a (List.mem_cons_self ..))
    have ih := andL_spec d (andW p d a).1 as (hd.ext h1.ext)
      (fun v hv => (ha v (List.mem_cons_of_mem _ hv)).ext h1.ext)
    refine ⟨h1.ext.trans ih.ext, ?_, by simp [andL, ih.length], ?_⟩
    · intro v hv
      simp only [andL, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact h1.valid.ext ih.ext
      · exact ih.valid v hv
    · simp only [andL, nv]
      rw [ih.value, bv_ext x ih.ext h1.valid, h1.value, bv_ext x h1.ext hd,
        nv_ext x h1.ext (fun v hv => ha v (List.mem_cons_of_mem _ hv))]
      cases bv x p d <;> simp

/-- Bitwise `¬a`. -/
def notL : SLP ι → List (Wire ι) → SLP ι × List (Wire ι)
  | p, a :: as =>
    let r := notW p a
    let r' := notL r.1 as
    (r'.1, r.2 :: r'.2)
  | p, [] => (p, [])

theorem notL_spec : ∀ (p : SLP ι) (as : List (Wire ι)), AllValid p as →
    SpecN x p (notL p as) as.length (2 ^ as.length - 1 - nv x p as)
  | p, [], _ => ⟨Ext.refl p, by simp [AllValid, notL], rfl, by simp [notL, nv]⟩
  | p, a :: as, ha => by
    have h1 := notW_spec x p a (ha a (List.mem_cons_self ..))
    have ih := notL_spec (notW p a).1 as (fun v hv => (ha v (List.mem_cons_of_mem _ hv)).ext h1.ext)
    refine ⟨h1.ext.trans ih.ext, ?_, by simp [notL, ih.length], ?_⟩
    · intro v hv
      simp only [notL, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact h1.valid.ext ih.ext
      · exact ih.valid v hv
    · have hlt := nv_lt x (notW p a).1 as
      simp only [notL, nv]
      rw [ih.value, bv_ext x ih.ext h1.valid, h1.value,
        nv_ext x h1.ext (fun v hv => ha v (List.mem_cons_of_mem _ hv))]
      rw [nv_ext x h1.ext (fun v hv => ha v (List.mem_cons_of_mem _ hv))] at hlt
      simp only [List.length_cons, pow_succ]
      cases bv x p a <;> simp <;> omega

/-! ### Modular addition and subtraction -/

/-- `(a + b) mod q` for `w`-bit numbers below `q ≤ 2^w`; `z` is a wire of value `false`. -/
def modAdd (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) : SLP ι × List (Wire ι) :=
  let r₁ := rippleAdd p as bs z
  let r₂ := rippleAdd r₁.1 r₁.2 (constL z (w + 1) (2 ^ (w + 1) - q)) z
  let r₃ := muxL (r₂.2.getD (w + 1) .one) r₂.1 (r₂.2.take (w + 1)) r₁.2
  (r₃.1, r₃.2.take w)

theorem modAdd_spec (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) (hz : Valid p z)
    (hz0 : bv x p z = false) (ha : AllValid p as) (hb : AllValid p bs) (hla : as.length = w)
    (hlb : bs.length = w) (hq : 0 < q) (hqw : q ≤ 2 ^ w) (hav : nv x p as < q)
    (hbv : nv x p bs < q) :
    SpecN x p (modAdd z q w p as bs) w ((nv x p as + nv x p bs) % q) := by
  set r₁ := rippleAdd p as bs z with hr₁
  set K := constL z (w + 1) (2 ^ (w + 1) - q) with hK
  set r₂ := rippleAdd r₁.1 r₁.2 K z with hr₂
  set c := r₂.2.getD (w + 1) .one with hc
  set r₃ := muxL c r₂.1 (r₂.2.take (w + 1)) r₁.2 with hr₃
  have h1 := rippleAdd_spec x p as bs z ha hb hz (by rw [hla, hlb])
  rw [← hr₁, hz0, Bool.toNat_false, add_zero, hla] at h1
  have hz1 : Valid r₁.1 z := hz.ext h1.ext
  have hz01 : bv x r₁.1 z = false := by rw [bv_ext x h1.ext hz]; exact hz0
  obtain ⟨hcv, hcl, hcn⟩ := constL_spec x r₁.1 z hz1 hz01 (w + 1) (2 ^ (w + 1) - q)
  rw [← hK] at hcv hcl hcn
  have h2 := rippleAdd_spec x r₁.1 r₁.2 K z h1.valid hcv hz1 (by rw [h1.length, hcl])
  rw [← hr₂, h1.value, hcn, hz01, Bool.toNat_false, add_zero, h1.length] at h2
  have hP : 2 ^ (w + 1) = 2 * 2 ^ w := Nat.pow_succ'
  rw [Nat.mod_eq_of_lt (by omega)] at h2
  have hsplit := nv_split x r₂.1 r₂.2 (w + 1) h2.length
  rw [← hc, h2.value] at hsplit
  have hlow := nv_lt x r₂.1 (r₂.2.take (w + 1))
  rw [List.length_take, h2.length, min_eq_left (by omega)] at hlow
  have hcarry : Valid r₂.1 c := by
    by_cases hlt : w + 1 < r₂.2.length
    · rw [hc, List.getD_eq_getElem _ _ hlt]; exact h2.valid _ (List.getElem_mem hlt)
    · rw [hc, List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]; trivial
  have htake : AllValid r₂.1 (r₂.2.take (w + 1)) := fun v hv => h2.valid v (List.mem_of_mem_take hv)
  have h3 := muxL_spec x c r₂.1 (r₂.2.take (w + 1)) r₁.2 hcarry htake (h1.valid.ext h2.ext)
    (by rw [List.length_take, h2.length, h1.length]; omega)
  rw [← hr₃, nv_ext x h2.ext h1.valid, h1.value] at h3
  refine ⟨h1.ext.trans (h2.ext.trans h3.ext), fun v hv => h3.valid v (List.mem_of_mem_take hv),
    ?_, ?_⟩
  · show (r₃.2.take w).length = w
    rw [List.length_take, h3.length, List.length_take, h2.length]; omega
  · show nv x r₃.1 (r₃.2.take w) = _
    rw [nv_take, h3.value]
    have hbit := Bool.toNat_le (bv x r₂.1 c)
    rw [hP] at hsplit hlow
    cases hcb : bv x r₂.1 c
    · rw [hcb] at hsplit
      simp only [Bool.toNat_false, mul_zero, add_zero, Bool.false_eq_true, ite_false] at hsplit ⊢
      rw [Nat.mod_eq_of_lt (show nv x p as + nv x p bs < q by omega), Nat.mod_eq_of_lt (by omega)]
    · rw [hcb] at hsplit
      simp only [Bool.toNat_true, mul_one, ite_true] at hsplit ⊢
      have hge : q ≤ nv x p as + nv x p bs := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

/-- `(a − b) mod q` for `w`-bit numbers below `q ≤ 2^w`; `z` is a wire of value `false`. -/
def modSub (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) : SLP ι × List (Wire ι) :=
  let r₁ := notL p bs
  let r₂ := rippleAdd r₁.1 as r₁.2 .one
  let r₃ := rippleAdd r₂.1 (r₂.2.take w) (constL z w q) z
  muxL (r₂.2.getD w .one) r₃.1 (r₂.2.take w) (r₃.2.take w)

theorem modSub_spec (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) (hz : Valid p z)
    (hz0 : bv x p z = false) (ha : AllValid p as) (hb : AllValid p bs) (hla : as.length = w)
    (hlb : bs.length = w) (hqw : q < 2 ^ w) (_hav : nv x p as < q) (hbv : nv x p bs < q) :
    SpecN x p (modSub z q w p as bs) w
      (if nv x p bs ≤ nv x p as then nv x p as - nv x p bs else nv x p as + q - nv x p bs) := by
  set r₁ := notL p bs with hr₁
  set r₂ := rippleAdd r₁.1 as r₁.2 .one with hr₂
  set K := constL z w q with hK
  set r₃ := rippleAdd r₂.1 (r₂.2.take w) K z with hr₃
  set c := r₂.2.getD w .one with hc
  have h1 := notL_spec x p bs hb
  rw [← hr₁, hlb] at h1
  have h2 := rippleAdd_spec x r₁.1 as r₁.2 .one (ha.ext h1.ext) h1.valid trivial
    (by rw [h1.length, hla])
  rw [← hr₂, nv_ext x h1.ext ha, h1.value, hla] at h2
  have hone : (bv x r₁.1 (Wire.one : Wire ι)).toNat = 1 := by simp [bv, evalBool, valueOf, wireVal]
  rw [hone] at h2
  have hbl := nv_lt x p bs
  rw [hlb] at hbl
  have hsplit := nv_split x r₂.1 r₂.2 w h2.length
  rw [← hc, h2.value] at hsplit
  have hlow := nv_lt x r₂.1 (r₂.2.take w)
  rw [List.length_take, h2.length, min_eq_left (by omega)] at hlow
  have htake : AllValid r₂.1 (r₂.2.take w) := fun v hv => h2.valid v (List.mem_of_mem_take hv)
  have hz2 : Valid r₂.1 z := hz.ext (h1.ext.trans h2.ext)
  have hz02 : bv x r₂.1 z = false := by rw [bv_ext x (h1.ext.trans h2.ext) hz]; exact hz0
  obtain ⟨hcv, hcl, hcn⟩ := constL_spec x r₂.1 z hz2 hz02 w q
  rw [← hK] at hcv hcl hcn
  have h3 := rippleAdd_spec x r₂.1 (r₂.2.take w) K z htake hcv hz2
    (by rw [List.length_take, h2.length, hcl]; omega)
  rw [← hr₃, hcn, hz02, Bool.toNat_false, add_zero, Nat.mod_eq_of_lt (by omega)] at h3
  have hcarry : Valid r₂.1 c := by
    by_cases hlt : w < r₂.2.length
    · rw [hc, List.getD_eq_getElem _ _ hlt]; exact h2.valid _ (List.getElem_mem hlt)
    · rw [hc, List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]; trivial
  have h4 := muxL_spec x c r₃.1 (r₂.2.take w) (r₃.2.take w) (hcarry.ext h3.ext) (htake.ext h3.ext)
    (fun v hv => h3.valid v (List.mem_of_mem_take hv))
    (by rw [List.length_take, List.length_take, h2.length, h3.length, List.length_take,
      h2.length]; omega)
  rw [bv_ext x h3.ext hcarry, nv_ext x h3.ext htake, nv_take x r₃.1 r₃.2 w, h3.value] at h4
  rw [show modSub z q w p as bs = muxL c r₃.1 (r₂.2.take w) (r₃.2.take w) from rfl]
  refine ⟨h1.ext.trans (h2.ext.trans (h3.ext.trans h4.ext)), h4.valid, ?_, ?_⟩
  · rw [h4.length, List.length_take, h2.length]; omega
  · rw [h4.value]
    have hbit := Bool.toNat_le (bv x r₂.1 c)
    cases hcb : bv x r₂.1 c
    · rw [hcb] at hsplit
      simp only [Bool.toNat_false, mul_zero, add_zero, Bool.false_eq_true, ite_false] at hsplit ⊢
      have hlt : ¬ nv x p bs ≤ nv x p as := by omega
      simp only [hlt, ↓reduceIte]
      rw [show nv x r₂.1 (r₂.2.take w) + q = (nv x p as + q - nv x p bs) + 2 ^ w by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [hcb] at hsplit
      simp only [Bool.toNat_true, mul_one, ite_true] at hsplit ⊢
      have hle : nv x p bs ≤ nv x p as := by omega
      simp only [hle, ↓reduceIte]
      omega

/-! ### Numbers of bits, and `ℤ_q` -/

/-- The wires of the bits of a number, least significant first, from a function on bit positions. -/
def bitsL (k : ℕ) (f : Fin k → Wire ι) : List (Wire ι) := List.ofFn f

theorem nv_bitsL (p : SLP ι) : ∀ (k : ℕ) (f : Fin k → Wire ι) (v : ℕ),
    (∀ i, bv x p (f i) = v.testBit i) → nv x p (bitsL k f) = v % 2 ^ k
  | 0, f, v, _ => by simp [bitsL, nv, Nat.mod_one]
  | k + 1, f, v, h => by
    simp only [bitsL, List.ofFn_succ, nv]
    rw [show List.ofFn (fun i : Fin k => f i.succ) = bitsL k (fun i => f i.succ) from rfl,
      nv_bitsL p k (fun i => f i.succ) (v / 2) (fun i => by rw [h i.succ]; simp [Nat.testBit_succ]),
      h 0, Nat.pow_succ', Nat.mod_mul]
    congr 1
    simp only [Fin.val_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one v with h0 | h1 <;> simp [*]

theorem length_bitsL (k : ℕ) (f : Fin k → Wire ι) : (bitsL k f).length = k := by simp [bitsL]

theorem modAdd_val {q : ℕ} [NeZero q] (a b : ℕ) :
    (a + b) % q = ((a : ZMod q) + b).val := by
  rw [← Nat.cast_add, ZMod.val_natCast]

theorem modSub_val {q : ℕ} [NeZero q] {a b : ℕ} (ha : a < q) (hb : b < q) :
    (if b ≤ a then a - b else a + q - b) = ((a : ZMod q) - b).val := by
  split_ifs with h
  · rw [← Nat.cast_sub h, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  · have : ((a : ZMod q) - b) = ((a + q - b : ℕ) : ZMod q) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

end SLP

end SigabaNeo.Lattices
