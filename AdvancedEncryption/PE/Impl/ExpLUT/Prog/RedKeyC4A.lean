import PE.Impl.ExpLUT.Prog.RedKeyTK

/-!
# Cost certificate of `mid`, phase M4 (part 1): a **verified** static bound analyzer for MVM codes

The ninth session's exploration analyzer (`RedKeyCA`) made sound and kernel-friendly, for the
register envelopes `KeyTime.layout M N K x` (`x : Fin 64 → ℕ` the register bounds; scratch tapes
at the cap `M`, ring templates exact).

* An **entry** `C4E` `⟨a, some (s, m, δ)⟩` bounds an output register by `max a (m · x s + δ)`,
  `⟨a, none⟩` by `a` (`C4E.ev`; the multiplier `m` covers doubling loops, `app d d`). A
  **transformer** `C4T` is a sparse list of entries (keys = registers; a missing key is the
  identity, `tget`); `tAp t x` is its action, `tcomp` composition (exact, `tAp_tcomp`), `tjoin` an
  upper bound of two branches.
* **`an M N K c E hs`** analyzes the code `c` on the box `E` (a list of `64` register bounds; the
  envelope is every `x ≤ bx E`) and returns the transformer, a time bound, the output box and the
  unused hints. Instructions use F3's per-instruction certificates (`layout_copy_update`,
  `layout_append`, `RedKeyT.rktOpU` (the counter charged with its box bound), …).
  **Loops** `rep c body` (count `R = E c`) take the next hint `C4H`:
  * `.box h` (**linear rule**): one analysis of the body on `B = max E h`; the iterates
    `G_j = tAp (tloop t B j) x` (self entries `m^j (max a x + j δ)`, `m > 1` only for `R ≤ 64`,
    `loopOK`) must stay in `B ≤ M` (`chk`); cost `R (2 M + T + 4) + 2` (`KeyTime.rep_family`);
  * `.unroll`: `R` body analyses on the joined prefixes (`uiter`, `sound_unroll`).
* **`AC`**: a code with `natC` leaves (`natC` is well-founded recursion, not kernel-reducible) of
  bounded argument (`AC.Er ac c`: `ac` describes `c`).
* **`c4Ok_cert`**: `c4Ok M N K ac E hs Eo T = true` (decidable, by `decide +kernel`) and
  `AC.Er ac c` give `Cert (compile c) (layout M N K x) (layout M N K (bx Eo)) T` for every
  `x ≤ bx E`.

Soundness: `an_sound` (induction on the code), `anA_sound`. Kernel lesson: every box operation is
a single list walk (`leL`, `topL`, `mkBoxG`, `boxV` sets only the keys); `List.range 64` with
`getD` made each loop cost `≈ 50 MB` of kernel memory (now `≈ 5 MB`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC4

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.KeyTime

/-! ### Entries -/

/-- An entry: `≤ max a (m x s + δ)` (`src = some (s, m, δ)`), or `≤ a`. -/
structure C4E where
  a : ℕ
  src : Option (ℕ × ℕ × ℕ)

/-- `x s` for an index `s` (`0` past `64`). -/
def xN (x : Fin 64 → ℕ) (s : ℕ) : ℕ := if h : s < 64 then x ⟨s, h⟩ else 0

theorem xN_mono {x y : Fin 64 → ℕ} (h : x ≤ y) (s : ℕ) : xN x s ≤ xN y s := by
  unfold xN; split_ifs
  · exact h _
  · exact le_rfl

@[simp] theorem xN_fin (x : Fin 64 → ℕ) (r : Fin 64) : xN x r.val = x r := by
  simp [xN, r.isLt]

/-- The bound of an entry. -/
def C4E.ev (e : C4E) (x : Fin 64 → ℕ) : ℕ :=
  match e.src with
  | none => e.a
  | some (s, m, δ) => max e.a (m * xN x s + δ)

theorem C4E.ev_mono (e : C4E) {x y : Fin 64 → ℕ} (h : x ≤ y) : e.ev x ≤ e.ev y := by
  rcases e with ⟨a, _ | ⟨s, m, δ⟩⟩
  · exact le_rfl
  · simp only [C4E.ev]
    exact max_le_max le_rfl (Nat.add_le_add_right (Nat.mul_le_mul_left m (xN_mono h s)) _)

/-! ### Boxes (lists of `64` bounds) -/

/-- A box as a bound vector. -/
def bx (E : List ℕ) : Fin 64 → ℕ := fun r => E.getD r.val 0

/-- `E s` (`0` past `64`). -/
def lget (E : List ℕ) (s : ℕ) : ℕ := if s < 64 then E.getD s 0 else 0

theorem xN_bx (E : List ℕ) (s : ℕ) : xN (bx E) s = lget E s := by
  unfold xN lget bx; split_ifs <;> rfl

/-- An entry on a box. -/
def C4E.evL (e : C4E) (E : List ℕ) : ℕ :=
  match e.src with
  | none => e.a
  | some (s, m, δ) => max e.a (m * lget E s + δ)

theorem C4E.evL_eq (e : C4E) (E : List ℕ) : e.evL E = e.ev (bx E) := by
  rcases e with ⟨a, _ | ⟨s, m, δ⟩⟩ <;> simp [C4E.evL, C4E.ev, xN_bx]

theorem bx_set (E : List ℕ) (hE : E.length = 64) (d : Fin 64) (v : ℕ) :
    bx (E.set d.val v) = Function.update (bx E) d v := by
  funext r
  simp only [bx, Function.update_apply]
  by_cases h : r = d
  · subst h
    rw [if_pos rfl, List.getD_eq_getElem _ _ (by simp [hE, r.isLt])]
    simp
  · rw [if_neg h, List.getD_eq_getElem _ _ (by simp [hE, r.isLt]),
      List.getD_eq_getElem _ _ (by simp [hE, r.isLt])]
    rw [List.getElem_set_ne (fun e => h (Fin.ext e.symm))]

theorem bx_range (f : ℕ → ℕ) : bx ((List.range 64).map f) = fun r => f r.val := by
  funext r
  simp only [bx]
  rw [List.getD_eq_getElem _ _ (by simp [r.isLt])]
  simp

/-- Pointwise comparison of boxes (one walk). -/
def leL : List ℕ → List ℕ → Bool
  | [], _ => true
  | a :: A, [] => Nat.beq a 0 && leL A []
  | a :: A, b :: B => Nat.ble a b && leL A B

theorem leL_getD : ∀ {A B : List ℕ}, leL A B = true → ∀ i, A.getD i 0 ≤ B.getD i 0
  | [], _, _, i => by simp
  | a :: A, [], h, i => by
    simp only [leL, Bool.and_eq_true, Nat.beq_eq] at h
    cases i with
    | zero => simp [h.1]
    | succ i => simpa using leL_getD h.2 i
  | a :: A, b :: B, h, i => by
    simp only [leL, Bool.and_eq_true, Nat.ble_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using leL_getD h.2 i

theorem leL_sound {A B : List ℕ} (h : leL A B = true) : bx A ≤ bx B :=
  fun r => leL_getD h r.val

/-- All bounds of a box at most `M` (one walk). -/
def topL : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: A, M => Nat.ble a M && topL A M

theorem topL_getD : ∀ {A : List ℕ} {M : ℕ}, topL A M = true → ∀ i, A.getD i 0 ≤ M
  | [], M, _, i => by simp
  | a :: A, M, h, i => by
    simp only [topL, Bool.and_eq_true, Nat.ble_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using topL_getD h.2 i

theorem topL_sound {A : List ℕ} {M : ℕ} (h : topL A M = true) : ∀ r, bx A r ≤ M :=
  fun r => topL_getD h r.val

/-! ### Transformers -/

/-- A sparse transformer (keys = registers). -/
abbrev C4T := List (ℕ × C4E)

/-- The identity entry of register `r`. -/
def c4Id (r : ℕ) : C4E := ⟨0, some (r, 1, 0)⟩

/-- The entry of register `r` (the first with key `r`, else the identity). -/
def tget : C4T → ℕ → C4E
  | [], r => c4Id r
  | p :: t, r => if Nat.beq p.1 r then p.2 else tget t r

/-- The action of a transformer. -/
def tAp (t : C4T) (x : Fin 64 → ℕ) : Fin 64 → ℕ := fun r => (tget t r.val).ev x

theorem ev_c4Id (x : Fin 64 → ℕ) (r : Fin 64) : (c4Id r.val).ev x = x r := by
  simp [c4Id, C4E.ev]

theorem tAp_mono (t : C4T) {x y : Fin 64 → ℕ} (h : x ≤ y) : tAp t x ≤ tAp t y :=
  fun r => (tget t r.val).ev_mono h

theorem tAp_nil (x : Fin 64 → ℕ) : tAp [] x = x := funext fun r => ev_c4Id x r

theorem tAp_one (d : Fin 64) (e : C4E) (x : Fin 64 → ℕ) :
    tAp [(d.val, e)] x = Function.update x d (e.ev x) := by
  funext r
  simp only [tAp, tget, Function.update_apply]
  by_cases h : r = d
  · subst h; simp
  · have : Nat.beq d.val r.val = false := by
      rcases hb : Nat.beq d.val r.val
      · rfl
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hb)).symm h
    rw [this, if_neg h]
    exact ev_c4Id x r

/-! #### Key lists -/

/-- Membership of a key. -/
def kmem : List ℕ → ℕ → Bool
  | [], _ => false
  | k :: ks, r => Nat.beq k r || kmem ks r

/-- The keys of a transformer. -/
def keys (t : C4T) : List ℕ := t.map Prod.fst

/-- The transformer with keys `ks` and entries `g`. -/
def tmk (ks : List ℕ) (g : ℕ → C4E) : C4T := ks.map fun k => (k, g k)

theorem tget_tmk (ks : List ℕ) (g : ℕ → C4E) (r : ℕ) :
    tget (tmk ks g) r = if kmem ks r then g r else c4Id r := by
  induction ks with
  | nil => simp [tmk, tget, kmem]
  | cons k ks ih =>
    simp only [tmk, List.map_cons, tget, kmem] at ih ⊢
    by_cases h : Nat.beq k r = true
    · have := Nat.eq_of_beq_eq_true h; subst this; simp [h]
    · simp only [Bool.not_eq_true] at h
      simp [h, ih]

theorem tget_not_key (t : C4T) (r : ℕ) (h : kmem (keys t) r = false) : tget t r = c4Id r := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    simp only [keys, List.map_cons, kmem, Bool.or_eq_false_iff] at h
    simp only [tget, h.1, Bool.false_eq_true, ↓reduceIte]
    exact ih h.2

/-- The union of two key lists. -/
def kunion (a b : List ℕ) : List ℕ := a ++ b.filter fun k => !kmem a k

theorem kmem_append (a b : List ℕ) (r : ℕ) : kmem (a ++ b) r = (kmem a r || kmem b r) := by
  induction a with
  | nil => simp [kmem]
  | cons k a ih => simp [kmem, ih, Bool.or_assoc]

theorem kmem_iff (a : List ℕ) (r : ℕ) : kmem a r = true ↔ r ∈ a := by
  induction a with
  | nil => simp [kmem]
  | cons k a ih =>
    simp only [kmem, Bool.or_eq_true, ih, List.mem_cons, Nat.beq_eq]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem kmem_kunion (a b : List ℕ) (r : ℕ) : kmem (kunion a b) r = (kmem a r || kmem b r) := by
  rw [kunion, kmem_append]
  cases ha : kmem a r
  · simp only [Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    rw [kmem_iff, kmem_iff, List.mem_filter]
    simp [ha]
  · simp

/-! #### Composition -/

/-- The entry of `s` for composition (`⟨0, none⟩` past `64`). -/
def tget' (t : C4T) (s : ℕ) : C4E := if s < 64 then tget t s else ⟨0, none⟩

theorem xN_tAp (t : C4T) (x : Fin 64 → ℕ) (s : ℕ) : xN (tAp t x) s = (tget' t s).ev x := by
  unfold xN tget' tAp
  split_ifs <;> simp [C4E.ev]

theorem mul_max' (m a b : ℕ) : m * max a b = max (m * a) (m * b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_left m h)]
  · rw [max_eq_left h, max_eq_left (Nat.mul_le_mul_left m h)]

/-- `e` after `t1`. -/
def C4E.comp (t1 : C4T) (e : C4E) : C4E :=
  match e.src with
  | none => e
  | some (s, m, d) =>
    match (tget' t1 s).src with
    | none => ⟨max e.a (m * (tget' t1 s).a + d), none⟩
    | some (s1, m1, d1) => ⟨max e.a (m * (tget' t1 s).a + d), some (s1, m * m1, m * d1 + d)⟩

theorem C4E.comp_ev (t1 : C4T) (e : C4E) (x : Fin 64 → ℕ) :
    (e.comp t1).ev x = e.ev (tAp t1 x) := by
  rcases e with ⟨a, _ | ⟨s, m, d⟩⟩
  · rfl
  · simp only [C4E.comp, C4E.ev, xN_tAp]
    generalize tget' t1 s = f
    rcases f with ⟨fa, _ | ⟨s1, m1, d1⟩⟩
    · simp [C4E.ev]
    · simp only [C4E.ev]
      rw [mul_max', show m * (m1 * xN x s1 + d1) = m * m1 * xN x s1 + m * d1 by ring]
      omega

/-- **Composition**: `tAp (tcomp t1 t2) = tAp t2 ∘ tAp t1`. -/
def tcomp (t1 t2 : C4T) : C4T := tmk (kunion (keys t2) (keys t1)) fun k => (tget t2 k).comp t1

theorem tAp_tcomp (t1 t2 : C4T) (x : Fin 64 → ℕ) : tAp (tcomp t1 t2) x = tAp t2 (tAp t1 x) := by
  funext r
  simp only [tAp, tcomp, tget_tmk, kmem_kunion]
  split_ifs with h
  · exact C4E.comp_ev _ _ _
  · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    rw [tget_not_key _ _ h.1, ev_c4Id, ev_c4Id]
    show x r = (tget t1 r.val).ev x
    rw [tget_not_key _ _ h.2, ev_c4Id]

/-! #### Join (both branches of `ifb`) -/

/-- An upper bound of two entries on the box `E`. -/
def C4E.join (E : List ℕ) (e1 e2 : C4E) : C4E :=
  match e1.src, e2.src with
  | none, none => ⟨max e1.a e2.a, none⟩
  | some p, none => ⟨max e1.a e2.a, some p⟩
  | none, some p => ⟨max e1.a e2.a, some p⟩
  | some (s1, m1, d1), some (s2, m2, d2) =>
    if s1 = s2 then ⟨max e1.a e2.a, some (s1, max m1 m2, max d1 d2)⟩
    else ⟨max e1.a (e2.evL E), some (s1, m1, d1)⟩

theorem C4E.join_ge (E : List ℕ) (e1 e2 : C4E) (x : Fin 64 → ℕ) (hx : x ≤ bx E) :
    e1.ev x ≤ (e1.join E e2).ev x ∧ e2.ev x ≤ (e1.join E e2).ev x := by
  have h2 := e2.ev_mono hx
  rw [← C4E.evL_eq] at h2
  rcases e1 with ⟨a1, _ | ⟨s1, m1, d1⟩⟩ <;> rcases e2 with ⟨a2, _ | ⟨s2, m2, d2⟩⟩
  · simp [C4E.join, C4E.ev]
  · simp only [C4E.join, C4E.ev]; omega
  · simp only [C4E.join, C4E.ev]; omega
  · simp only [C4E.join]
    split_ifs with h
    · subst h; simp only [C4E.ev]
      have := Nat.mul_le_mul_right (xN x s1) (le_max_left m1 m2)
      have := Nat.mul_le_mul_right (xN x s1) (le_max_right m1 m2)
      omega
    · simp only [C4E.ev] at h2 ⊢; omega

/-- The join of two transformers on the box `E`. -/
def tjoin (E : List ℕ) (t1 t2 : C4T) : C4T :=
  tmk (kunion (keys t1) (keys t2)) fun k => (tget t1 k).join E (tget t2 k)

theorem tAp_tjoin (E : List ℕ) (t1 t2 : C4T) (x : Fin 64 → ℕ) (hx : x ≤ bx E) :
    tAp t1 x ≤ tAp (tjoin E t1 t2) x ∧ tAp t2 x ≤ tAp (tjoin E t1 t2) x := by
  constructor <;> intro r <;> simp only [tAp, tjoin, tget_tmk, kmem_kunion] <;> split_ifs with h
  · exact (C4E.join_ge E _ _ x hx).1
  · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    rw [tget_not_key _ _ h.1]
  · exact (C4E.join_ge E _ _ x hx).2
  · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    rw [tget_not_key _ _ h.2]

/-! #### Loops -/

/-- `m ^ R` (without computing `1 ^ R`). -/
def pw (m R : ℕ) : ℕ := if m = 1 then 1 else m ^ R

theorem pw_eq (m R : ℕ) : pw m R = m ^ R := by
  unfold pw; split_ifs with h
  · subst h; simp
  · rfl

/-- The entry of register `i` after `R` rounds of a body with entry `e` (box `B`). -/
def C4E.loop (i : ℕ) (B : List ℕ) (R : ℕ) (e : C4E) : C4E :=
  match e.src with
  | none => ⟨e.a, some (i, 1, 0)⟩
  | some (s, m, δ) =>
    if s = i then
      ⟨pw (max m 1) R * (e.a + R * δ), some (i, pw (max m 1) R, pw (max m 1) R * (R * δ))⟩
    else ⟨max e.a (m * lget B s + δ), some (i, 1, 0)⟩

/-- The transformer of `R` rounds. -/
def tloop (t : C4T) (B : List ℕ) (R : ℕ) : C4T := tmk (keys t) fun k => (tget t k).loop k B R

/-- Multipliers `> 1` of self entries only for few rounds (`pw` stays small). -/
def loopOK (t : C4T) (R : ℕ) : Bool :=
  Nat.ble R 64 || (keys t).all fun k =>
    match (tget t k).src with
    | some (s, m, _) => !(Nat.beq s k) || Nat.ble m 1
    | none => true

theorem tAp_tloop (t : C4T) (B : List ℕ) (R : ℕ) (x : Fin 64 → ℕ) (r : Fin 64) :
    tAp (tloop t B R) x r = ((tget t r.val).loop r.val B R).ev x := by
  simp only [tAp, tloop, tget_tmk]
  split_ifs with h
  · rfl
  · rw [Bool.not_eq_true] at h
    rw [tget_not_key _ _ h]
    simp [c4Id, C4E.loop, C4E.ev, pw]

theorem one_le_pw (m R : ℕ) : 1 ≤ pw (max m 1) R := by
  rw [pw_eq]; exact Nat.one_le_pow _ _ (by omega)

/-- The self entry after `R` rounds: `P (max a x + R δ)`. -/
theorem loop_self_ev (a m δ R : ℕ) (r : Fin 64) (x : Fin 64 → ℕ) :
    (⟨pw (max m 1) R * (a + R * δ), some (r.val, pw (max m 1) R, pw (max m 1) R * (R * δ))⟩ :
      C4E).ev x = pw (max m 1) R * (max a (x r) + R * δ) := by
  simp only [C4E.ev, xN_fin]
  rw [Nat.mul_add, Nat.mul_add, mul_max']
  rcases le_total (pw (max m 1) R * a) (pw (max m 1) R * x r) with h | h
  · rw [max_eq_right h, max_eq_right (by omega)]
  · rw [max_eq_left h, max_eq_left (by omega)]

theorem loop_ge (e : C4E) (r : Fin 64) (B : List ℕ) (R : ℕ) (x : Fin 64 → ℕ) :
    x r ≤ (e.loop r.val B R).ev x := by
  rcases e with ⟨a, _ | ⟨s, m, δ⟩⟩
  · simp [C4E.loop, C4E.ev]
  · simp only [C4E.loop]
    split_ifs with hs
    · rw [loop_self_ev]
      have := one_le_pw m R
      have h1 : max a (x r) + R * δ ≤ pw (max m 1) R * (max a (x r) + R * δ) :=
        Nat.le_mul_of_pos_left _ this
      have h2 : x r ≤ max a (x r) := le_max_right _ _
      omega
    · simp [C4E.ev]

theorem loop_mono_R (e : C4E) (r : Fin 64) (B : List ℕ) {j R : ℕ} (h : j ≤ R) (x : Fin 64 → ℕ) :
    (e.loop r.val B j).ev x ≤ (e.loop r.val B R).ev x := by
  rcases e with ⟨a, _ | ⟨s, m, δ⟩⟩
  · simp [C4E.loop, C4E.ev]
  · simp only [C4E.loop]
    split_ifs with hs
    · rw [loop_self_ev, loop_self_ev, pw_eq, pw_eq]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) h)
        (Nat.add_le_add_left (Nat.mul_le_mul_right δ h) _)
    · exact le_rfl

/-- One more round stays in the family, as long as the iterate is in the box. -/
theorem loop_step (t : C4T) (B : List ℕ) (j : ℕ) (x : Fin 64 → ℕ)
    (hB : tAp (tloop t B j) x ≤ bx B) :
    tAp t (tAp (tloop t B j) x) ≤ tAp (tloop t B (j + 1)) x := by
  intro r
  rw [tAp_tloop]
  simp only [tAp]
  generalize he : tget t r.val = e
  rcases e with ⟨a, _ | ⟨s, m, δ⟩⟩
  · simp [C4E.loop, C4E.ev]
  · simp only [C4E.loop]
    split_ifs with hs
    · subst hs
      rw [loop_self_ev]
      simp only [C4E.ev, xN_fin]
      rw [tAp_tloop, he]
      simp only [C4E.loop, if_true]
      rw [loop_self_ev]
      set A := max a (x r)
      have hP : pw (max m 1) (j + 1) = max m 1 * pw (max m 1) j := by
        rw [pw_eq, pw_eq, pow_succ, Nat.mul_comm]
      have h1 : m * (pw (max m 1) j * (A + j * δ)) ≤ pw (max m 1) (j + 1) * (A + j * δ) := by
        rw [hP, Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (le_max_left m 1)
      have h2 : δ ≤ pw (max m 1) (j + 1) * δ := Nat.le_mul_of_pos_left _ (one_le_pw m _)
      have h3 : A ≤ pw (max m 1) (j + 1) * (A + (j + 1) * δ) :=
        (Nat.le_add_right A _).trans (Nat.le_mul_of_pos_left _ (one_le_pw m _))
      have h4 : pw (max m 1) (j + 1) * (A + (j + 1) * δ) =
          pw (max m 1) (j + 1) * (A + j * δ) + pw (max m 1) (j + 1) * δ := by ring
      have ha : a ≤ A := le_max_left _ _
      omega
    · have h1 : xN (tAp (tloop t B j) x) s ≤ lget B s := by
        rw [← xN_bx]; exact xN_mono hB s
      have := Nat.mul_le_mul_left m h1
      simp only [C4E.ev]
      omega

/-- The loop check: the iterates on the entry box `E` stay in `B`, and `B ≤ M`. -/
def chk (Gs B : List ℕ) (M : ℕ) : Bool := leL Gs B && topL B M

theorem chk_sound {Gs B : List ℕ} {M : ℕ} (h : chk Gs B M = true) :
    bx Gs ≤ bx B ∧ ∀ r, bx B r ≤ M := by
  simp only [chk, Bool.and_eq_true] at h
  exact ⟨leL_sound h.1, topL_sound h.2⟩

/-! ### The analyzer -/

/-- A loop hint: a sparse loop box (linear rule), or unrolling (small counts, no inner hints). -/
inductive C4H where
  | box (h : List (ℕ × ℕ))
  | unroll

/-- The result: transformer, time, output box, remaining hints. -/
structure C4R where
  t : C4T
  T : ℕ
  out : List ℕ
  hs : List C4H

/-- A sparse hint. -/
def hget : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: h, i => if Nat.beq p.1 i then p.2 else hget h i

/-- The loop box `max E h`. -/
def mkBoxG (h : List (ℕ × ℕ)) : List ℕ → ℕ → List ℕ
  | [], _ => []
  | e :: E, i => max e (hget h i) :: mkBoxG h E (i + 1)

theorem mkBoxG_length (h : List (ℕ × ℕ)) : ∀ (E : List ℕ) (i : ℕ), (mkBoxG h E i).length = E.length
  | [], _ => rfl
  | _ :: E, i => by simp [mkBoxG, mkBoxG_length h E (i + 1)]

/-- The loop box `max E h`. -/
def mkBox (E : List ℕ) (h : List (ℕ × ℕ)) : List ℕ := mkBoxG h E 0

/-- The box of a transformer on the box `E`. -/
def boxV : C4T → List ℕ → List ℕ
  | [], E => E
  | p :: V, E => (boxV V E).set p.1 (p.2.evL E)

theorem boxV_length : ∀ (V : C4T) (E : List ℕ), (boxV V E).length = E.length
  | [], _ => rfl
  | _ :: V, E => by simp [boxV, boxV_length V E]

theorem bx_boxV (V : C4T) (E : List ℕ) (hE : E.length = 64) : bx (boxV V E) = tAp V (bx E) := by
  induction V with
  | nil => funext r; simp [boxV, tAp, tget, ev_c4Id]
  | cons p V ih =>
    funext r
    simp only [boxV, tAp, tget]
    by_cases h : Nat.beq p.1 r.val = true
    · have e := Nat.eq_of_beq_eq_true h
      rw [if_pos h, ← C4E.evL_eq]
      simp only [bx]
      rw [List.getD_eq_getElem _ _ (by simp [boxV_length, hE, r.isLt]), List.getElem_set]
      simp [e]
    · rw [if_neg h]
      have hne : p.1 ≠ r.val := fun e => h (by rw [e]; exact Nat.beq_refl _)
      have := congrFun ih r
      simp only [bx, tAp] at this ⊢
      rw [← this]
      by_cases hl : r.val < (boxV V E).length
      · rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getD_eq_getElem _ _ hl,
          List.getElem_set_ne hne]
      · rw [List.getD_eq_default _ _ (by simpa using hl), List.getD_eq_default _ _ (by omega)]

/-- One unrolled round: analyze the body on the current box, join the new prefix. -/
def ustep (f : List ℕ → List C4H → Option C4R) (E : List ℕ) (M : ℕ) (p : C4T × ℕ × List C4H) :
    Option (C4T × ℕ × List C4H) :=
  if topL (boxV p.1 E) M then
    match f (boxV p.1 E) p.2.2 with
    | none => none
    | some r => some (tjoin E p.1 (tcomp p.1 r.t), max p.2.1 r.T, r.hs)
  else none

/-- `j` unrolled rounds (the joined prefixes, the largest body time, the remaining hints). -/
def uiter (f : List ℕ → List C4H → Option C4R) (E : List ℕ) (M : ℕ) (hs : List C4H) :
    ℕ → Option (C4T × ℕ × List C4H)
  | 0 => some ([], 0, hs)
  | j + 1 => (uiter f E M hs j).bind (ustep f E M)

/-- The entry of `app d s` (`2 x d` for `d = s`). -/
def appE (d s : Fin 64) (E : List ℕ) : C4E :=
  if d = s then ⟨0, some (d.val, 2, 0)⟩ else ⟨0, some (d.val, 1, E.getD s.val 0)⟩

theorem appE_evL (d s : Fin 64) (E : List ℕ) :
    (appE d s E).evL E = E.getD d.val 0 + E.getD s.val 0 := by
  unfold appE; split_ifs with h
  · subst h; simp [C4E.evL, lget, d.isLt]; omega
  · simp [C4E.evL, lget, d.isLt]

theorem appE_ev (d s : Fin 64) (E : List ℕ) (x : Fin 64 → ℕ) (hx : x ≤ bx E) :
    x d + x s ≤ (appE d s E).ev x := by
  unfold appE; split_ifs with h
  · subst h; simp [C4E.ev]; omega
  · have := hx s; simp only [bx] at this; simp only [C4E.ev, xN_fin, one_mul]; omega

/-- **The analyzer.** -/
def an (M N K : ℕ) : Code → List ℕ → List C4H → Option C4R
  | .op _ d _ c, E, hs =>
    some ⟨[(d.val, ⟨N * K, none⟩)], operationBound M N K (E.getD c.val 0), E.set d.val (N * K), hs⟩
  | .mv _ _ c, E, hs => some ⟨[], (2 * M + 5) * (20 + 10 * E.getD c.val 0), E, hs⟩
  | .mvR _ _, E, hs => some ⟨[], (2 * M + 5) * (20 + 10 * (N * K)), E, hs⟩
  | .cp d s, E, hs =>
    some ⟨[(d.val, ⟨0, some (s.val, 1, 0)⟩)], 2 * M + 5, E.set d.val (E.getD s.val 0), hs⟩
  | .drop _ c, E, hs => some ⟨[], (2 * M + 5) * (20 + 10 * E.getD c.val 0), E, hs⟩
  | .clr d, E, hs => some ⟨[(d.val, ⟨0, none⟩)], 2 * M + 5, E.set d.val 0, hs⟩
  | .tl _, E, hs => some ⟨[], 2 * M + 5, E, hs⟩
  | .app d s, E, hs =>
    if E.getD d.val 0 + E.getD s.val 0 ≤ M then
      some ⟨[(d.val, appE d s E)], (4 * E.getD s.val 0 + 6) * (2 * M + 5),
        E.set d.val (E.getD d.val 0 + E.getD s.val 0), hs⟩
    else none
  | .eqb f a b, E, hs =>
    if f = a ∨ f = b ∨ a = b then some ⟨[], 2 * M + 5, E, hs⟩
    else some ⟨[(f.val, ⟨1, none⟩)], 2 * M + 5, E.set f.val 1, hs⟩
  | .nop, E, hs => some ⟨[], 2 * M + 5, E, hs⟩
  | .seq p q, E, hs =>
    match an M N K p E hs with
    | none => none
    | some r1 =>
      match an M N K q r1.out r1.hs with
      | none => none
      | some r2 => some ⟨tcomp r1.t r2.t, r1.T + r2.T, r2.out, r2.hs⟩
  | .ifb _ p q, E, hs =>
    match an M N K p E hs with
    | none => none
    | some r1 =>
      match an M N K q E r1.hs with
      | none => none
      | some r2 =>
        if topL (boxV (tjoin E r1.t r2.t) E) M then
          some ⟨tjoin E r1.t r2.t, max r1.T r2.T + 1, boxV (tjoin E r1.t r2.t) E, r2.hs⟩
        else none
  | .rep c body, E, hs =>
    match hs.headD (.box []) with
    | .box h =>
      match an M N K body (mkBox E h) hs.tail with
      | none => none
      | some r =>
        if loopOK r.t (E.getD c.val 0) &&
            chk (boxV (tloop r.t (mkBox E h) (E.getD c.val 0)) E) (mkBox E h) M then
          some ⟨tloop r.t (mkBox E h) (E.getD c.val 0), E.getD c.val 0 * (2 * M + r.T + 4) + 2,
            boxV (tloop r.t (mkBox E h) (E.getD c.val 0)) E, r.hs⟩
        else none
    | .unroll =>
      match uiter (fun B hs' => an M N K body B hs') E M hs.tail (E.getD c.val 0) with
      | none => none
      | some p =>
        if topL (boxV p.1 E) M then
          some ⟨p.1, E.getD c.val 0 * (2 * M + p.2.1 + 4) + 2, boxV p.1 E, p.2.2⟩
        else none

/-! ### Code equality (Boolean, kernel-friendly) -/

/-- Structural equality of codes. -/
def codeEq : Code → Code → Bool
  | .op o d a b, .op o' d' a' b' =>
    decide (o = o') && Nat.beq d.val d'.val && Nat.beq a.val a'.val && Nat.beq b.val b'.val
  | .mv d s c, .mv d' s' c' => Nat.beq d.val d'.val && Nat.beq s.val s'.val && Nat.beq c.val c'.val
  | .mvR d s, .mvR d' s' => Nat.beq d.val d'.val && Nat.beq s.val s'.val
  | .cp d s, .cp d' s' => Nat.beq d.val d'.val && Nat.beq s.val s'.val
  | .drop d s, .drop d' s' => Nat.beq d.val d'.val && Nat.beq s.val s'.val
  | .clr d, .clr d' => Nat.beq d.val d'.val
  | .tl d, .tl d' => Nat.beq d.val d'.val
  | .app d s, .app d' s' => Nat.beq d.val d'.val && Nat.beq s.val s'.val
  | .eqb f a b, .eqb f' a' b' => Nat.beq f.val f'.val && Nat.beq a.val a'.val && Nat.beq b.val b'.val
  | .rep c b, .rep c' b' => Nat.beq c.val c'.val && codeEq b b'
  | .seq p q, .seq p' q' => codeEq p p' && codeEq q q'
  | .ifb t p q, .ifb t' p' q' => Nat.beq t.val t'.val && codeEq p p' && codeEq q q'
  | .nop, .nop => true
  | _, _ => false

theorem fin_of_beq {a b : Fin 64} (h : Nat.beq a.val b.val = true) : a = b :=
  Fin.ext (Nat.eq_of_beq_eq_true h)

theorem codeEq_eq : ∀ a b : Code, codeEq a b = true → a = b := by
  intro a
  induction a with
  | rep c body ih =>
    intro b h; cases b <;> simp only [codeEq, Bool.and_eq_true, reduceCtorEq] at h
    exact (Code.rep.injEq _ _ _ _).mpr ⟨fin_of_beq h.1, ih _ h.2⟩
  | seq p q ihp ihq =>
    intro b h; cases b <;> simp only [codeEq, Bool.and_eq_true, reduceCtorEq] at h
    exact (Code.seq.injEq _ _ _ _).mpr ⟨ihp _ h.1, ihq _ h.2⟩
  | ifb t p q ihp ihq =>
    intro b h; cases b <;> simp only [codeEq, Bool.and_eq_true, reduceCtorEq] at h
    exact (Code.ifb.injEq _ _ _ _ _ _).mpr ⟨fin_of_beq h.1.1, ihp _ h.1.2, ihq _ h.2⟩
  | _ => intro b h; cases b <;> simp_all [codeEq, Fin.ext_iff]

/-! ### Soundness -/

section Sound

variable {M N K : ℕ}

/-- The property established for an analysis result. -/
def Sound (M N K : ℕ) (c : Code) (E : List ℕ) (r : C4R) : Prop :=
  r.out.length = 64 ∧ (∀ i, bx r.out i ≤ M) ∧
    ∀ x, x ≤ bx E → tAp r.t x ≤ bx r.out ∧
      Cert (compile c) (layout M N K x) (layout M N K (tAp r.t x)) r.T

theorem inputs_of (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) {E : List ℕ}
    (hE : ∀ i, bx E i ≤ M) {x : Fin 64 → ℕ} (hx : x ≤ bx E) :
    RingInputs M N K (layout M N K x) :=
  layout_inputs M N K x (fun r => (hx r).trans (hE r)) hNK hN hK

/-- A leaf that writes one register. -/
theorem sound_one (c : Code) (E : List ℕ) (hE64 : E.length = 64) (hE : ∀ i, bx E i ≤ M)
    (d : Fin 64) (e : C4E) (T v : ℕ) (hvE : e.evL E = v) (hv : v ≤ M)
    (hc : ∀ x, x ≤ bx E →
      Cert (compile c) (layout M N K x) (layout M N K (Function.update x d (e.ev x))) T)
    (hs : List C4H) :
    Sound M N K c E ⟨[(d.val, e)], T, E.set d.val v, hs⟩ := by
  subst hvE
  refine ⟨by simp [hE64], ?_, fun x hx => ⟨?_, ?_⟩⟩
  · rw [bx_set E hE64]
    intro i
    by_cases h : i = d
    · subst h; simpa using hv
    · rw [Function.update_of_ne h]; exact hE i
  · rw [tAp_one, bx_set E hE64, C4E.evL_eq]
    intro i
    by_cases h : i = d
    · subst h; simpa using e.ev_mono hx
    · simp only [Function.update_of_ne h]; exact hx i
  · simp only; rw [tAp_one]; exact hc x hx

/-- A leaf that writes nothing. -/
theorem sound_nil (c : Code) (E : List ℕ) (hE64 : E.length = 64) (hE : ∀ i, bx E i ≤ M) (T : ℕ)
    (hc : ∀ x, x ≤ bx E → Cert (compile c) (layout M N K x) (layout M N K x) T)
    (hs : List C4H) : Sound M N K c E ⟨[], T, E, hs⟩ :=
  ⟨hE64, hE, fun x hx => ⟨by rw [tAp_nil]; exact hx, by simp only; rw [tAp_nil]; exact hc x hx⟩⟩

theorem le_E (E : List ℕ) (r : Fin 64) {x : Fin 64 → ℕ} (hx : x ≤ bx E) : x r ≤ E.getD r.val 0 :=
  hx r

theorem mkBox_length (E : List ℕ) (h : List (ℕ × ℕ)) (hE : E.length = 64) :
    (mkBox E h).length = 64 := by
  simp [mkBox, mkBoxG_length, hE]

theorem uiter_prefix (f : List ℕ → List C4H → Option C4R) (E : List ℕ) (M : ℕ) (hs : List C4H) :
    ∀ R p, uiter f E M hs R = some p → ∀ j ≤ R, ∃ q, uiter f E M hs j = some q := by
  intro R
  induction R with
  | zero => intro p h j hj; exact ⟨p, by rw [Nat.le_zero.mp hj]; exact h⟩
  | succ R ih =>
    intro p h j hj
    rcases Nat.lt_or_ge j (R + 1) with hj' | hj'
    · simp only [uiter] at h
      rcases hq : uiter f E M hs R with _ | q
      · rw [hq] at h; simp at h
      · exact ih q hq j (by omega)
    · exact ⟨p, by rw [show j = R + 1 by omega]; exact h⟩

theorem uiter_succ {f : List ℕ → List C4H → Option C4R} {E : List ℕ} {M j : ℕ} {hs : List C4H}
    {q' : C4T × ℕ × List C4H} (h : uiter f E M hs (j + 1) = some q') :
    ∃ q r, uiter f E M hs j = some q ∧ topL (boxV q.1 E) M = true ∧ f (boxV q.1 E) q.2.2 = some r ∧
      q' = (tjoin E q.1 (tcomp q.1 r.t), max q.2.1 r.T, r.hs) := by
  simp only [uiter] at h
  rcases hq : uiter f E M hs j with _ | q
  · rw [hq] at h; simp at h
  · rw [hq, Option.bind_some] at h
    unfold ustep at h
    split_ifs at h with ht
    split at h
    · simp at h
    · rename_i r hr
      simp only [Option.some.injEq] at h
      exact ⟨q, r, rfl, ht, hr, h.symm⟩

theorem uiter_T {f : List ℕ → List C4H → Option C4R} {E : List ℕ} {M : ℕ} {hs : List C4H} :
    ∀ k j q p, uiter f E M hs j = some q → uiter f E M hs (j + k) = some p → q.2.1 ≤ p.2.1 := by
  intro k
  induction k with
  | zero => intro j q p h1 h2; rw [Nat.add_zero, h1] at h2; cases h2; exact le_rfl
  | succ k ih =>
    intro j q p h1 h2
    obtain ⟨q', r, h3, -, -, rfl⟩ := uiter_succ (show uiter f E M hs (j + k + 1) = some p from h2)
    exact (ih j q q' h1 h3).trans (le_max_left _ _)

/-- **The unrolling rule.** -/
theorem sound_unroll (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) (c : Fin 64) (body : Code)
    (ihb : ∀ B hs r, an M N K body B hs = some r → B.length = 64 → (∀ i, bx B i ≤ M) →
      Sound M N K body B r)
    (E : List ℕ) (hE64 : E.length = 64) (hs : List C4H) (p : C4T × ℕ × List C4H)
    (hp : uiter (fun B hs' => an M N K body B hs') E M hs (E.getD c.val 0) = some p)
    (htop : topL (boxV p.1 E) M = true) :
    Sound M N K (.rep c body) E
      ⟨p.1, E.getD c.val 0 * (2 * M + p.2.1 + 4) + 2, boxV p.1 E, p.2.2⟩ := by
  set f := fun B hs' => an M N K body B hs'
  set R := E.getD c.val 0
  let V : ℕ → C4T := fun j => ((uiter f E M hs j).getD ([], 0, [])).1
  have hV : ∀ j q, uiter f E M hs j = some q → V j = q.1 := fun j q h => by simp [V, h]
  have step : ∀ j < R, ∃ q r, uiter f E M hs j = some q ∧ topL (boxV q.1 E) M = true ∧
      f (boxV q.1 E) q.2.2 = some r ∧
      uiter f E M hs (j + 1) = some (tjoin E q.1 (tcomp q.1 r.t), max q.2.1 r.T, r.hs) := by
    intro j hj
    obtain ⟨q', hq'⟩ := uiter_prefix f E M hs R p hp (j + 1) hj
    obtain ⟨q, r, h1, h2, h3, rfl⟩ := uiter_succ hq'
    exact ⟨q, r, h1, h2, h3, hq'⟩
  refine ⟨by rw [boxV_length]; exact hE64, topL_sound htop, fun x hx => ⟨?_, ?_⟩⟩
  · rw [bx_boxV _ _ hE64]; exact tAp_mono _ hx
  · have hmono1 : ∀ j < R, tAp (V j) x ≤ tAp (V (j + 1)) x := by
      intro j hj
      obtain ⟨q, r, h1, -, -, h4⟩ := step j hj
      rw [hV _ _ h1, hV _ _ h4]
      exact (tAp_tjoin E _ _ x hx).1
    have hmono : ∀ k j, j + k ≤ R → tAp (V j) x ≤ tAp (V (j + k)) x := by
      intro k
      induction k with
      | zero => intro j _; exact le_rfl
      | succ k ih => intro j hjk; exact (ih j (by omega)).trans (hmono1 (j + k) (by omega))
    have hVR : V R = p.1 := hV R p hp
    have hV0 : V 0 = [] := by simp [V, uiter]
    have hcert := rep_family c body (fun j => layout M N K (tAp (V j) x)) R p.2.1 (layout M N K x)
      (by rw [hV0, tAp_nil]) (by rw [layout_register]; exact hx c) (fun j hj => ?_) M
      (fun j hj => ?_) (fun j hj => layout_mono M N K (by
        have := hmono (R - j) j (by omega)
        rwa [show j + (R - j) = R by omega] at this))
    · simp only [hVR] at hcert; exact hcert
    · obtain ⟨q, r, h1, h2, h3, h4⟩ := step j hj
      have hsd := ihb _ _ r h3 (by rw [boxV_length]; exact hE64) (topL_sound h2)
      have hin : tAp q.1 x ≤ bx (boxV q.1 E) := by rw [bx_boxV _ _ hE64]; exact tAp_mono _ hx
      obtain ⟨-, cb⟩ := hsd.2.2 _ hin
      simp only [hV _ _ h1, hV _ _ h4]
      refine cb.mono (tailB_le (tR c) _) (layout_mono M N K ?_) ?_
      · rw [← tAp_tcomp]; exact (tAp_tjoin E _ _ x hx).2
      · exact (le_max_right q.2.1 r.T).trans (uiter_T (R - (j + 1)) (j + 1) _ p h4
          (by rw [show j + 1 + (R - (j + 1)) = R by omega]; exact hp))
    · obtain ⟨q, r, h1, h2, -, -⟩ := step j hj
      simp only [hV _ _ h1]
      exact supB_le_of (layout_top M N K _ (fun i => (tAp_mono q.1 hx i).trans
        (by rw [← bx_boxV _ _ hE64]; exact topL_sound h2 i)) hNK hN hK)

theorem an_sound (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) (hM1 : 1 ≤ M) :
    ∀ (c : Code) (E : List ℕ) (hs : List C4H) (r : C4R),
      an M N K c E hs = some r → E.length = 64 → (∀ i, bx E i ≤ M) → Sound M N K c E r := by
  intro c
  induction c with
  | op o d s c =>
    intro E hs r h hE64 hE
    simp only [an, Option.some.injEq] at h; subst h
    refine sound_one _ E hE64 hE d ⟨N * K, none⟩ _ _ rfl hNK (fun x hx => ?_) hs
    have h := RedKeyT.rktOpU M N K (E.getD c.val 0) x (inputs_of hNK hN hK hE hx) o d s c (hx c)
    simpa [C4E.ev] using h
  | mv d s c =>
    intro E hs r h hE64 hE
    simp only [an, Option.some.injEq] at h; subst h
    refine sound_nil _ E hE64 hE _ (fun x hx => ?_) hs
    have ht := layout_top M N K x (fun r => (hx r).trans (hE r)) hNK hN hK
    by_cases hd : d = s ∨ d = c ∨ s = c
    · exact (compile_mv_overlap d s c hd _ M ht).mono le_rfl le_rfl
        (by have := Nat.mul_le_mul_left (2 * M + 5) (show 1 ≤ 20 + 10 * E.getD c.val 0 by omega); omega)
    · refine (compile_mv_scratch d s c hd _ M ht).mono le_rfl le_rfl ?_
      have := hx c
      simp only [layout_register]
      exact Nat.mul_le_mul (by omega) (by simp only [bx] at this; omega)
  | mvR d s =>
    intro E hs r h hE64 hE
    simp only [an, Option.some.injEq] at h; subst h
    refine sound_nil _ E hE64 hE _ (fun x hx => ?_) hs
    have ht := layout_top M N K x (fun r => (hx r).trans (hE r)) hNK hN hK
    by_cases hd : d = s
    · subst hd
      exact (compile_mvR_self d _ M ht).mono le_rfl le_rfl (by
        have := Nat.mul_le_mul_left (2 * M + 5) (show 1 ≤ 20 + 10 * (N * K) by omega); omega)
    · refine (compile_mvR_scratch d s hd _ M ht).mono le_rfl le_rfl ?_
      have h37 : layout M N K x 37 = N * K := by simp [layout]
      rw [h37]
      exact Nat.mul_le_mul (by omega) le_rfl
  | cp d s =>
    intro E hs r h hE64 hE
    simp only [an, Option.some.injEq] at h; subst h
    refine sound_one _ E hE64 hE d ⟨0, some (s.val, 1, 0)⟩ _ (E.getD s.val 0)
      (by simp only [C4E.evL, lget, s.isLt, if_true, one_mul, add_zero]; exact max_eq_right (Nat.zero_le _))
      (hE s) (fun x hx => ?_) hs
    have ht := layout_top M N K x (fun r => (hx r).trans (hE r)) hNK hN hK
    simpa [C4E.ev] using layout_copy_update M N K x ht d s
  | drop t c =>
    intro E hs r h hE64 hE
    simp only [an, Option.some.injEq] at h; subst h
    refine sound_nil _ E hE64 hE _ (fun x hx => ?_) hs
    have ht := layout_top M N K x (fun r => (hx r).trans (hE r)) hNK hN hK
    by_cases hd : t = c
    · subst hd
      exact (compile_drop_self t _ M ht).mono le_rfl le_rfl (by have := Nat.mul_le_mul_left (2 * M + 5) (show 1 ≤ 20 + 10 * E.getD t.val 0 by omega); omega)
    · refine (compile_drop_scratch t c hd _ M ht).mono le_rfl le_rfl ?_
      have := hx c
      simp only [layout_register]
      exact Nat.mul_le_mul (by omega) (by simp only [bx] at this; omega)
  | clr d =>
    intro E hs r h hE64 hE
    simp only [an, Option.some.injEq] at h; subst h
    refine sound_one _ E hE64 hE d ⟨0, none⟩ _ _ rfl (Nat.zero_le _) (fun x hx => ?_) hs
    have ht := layout_top M N K x (fun r => (hx r).trans (hE r)) hNK hN hK
    simpa [C4E.ev] using layout_clear_update M N K x ht d
  | tl d =>
    intro E hs r h hE64 hE
    simp only [an, Option.some.injEq] at h; subst h
    refine sound_nil _ E hE64 hE _ (fun x hx => ?_) hs
    exact layout_tail M N K x (layout_top M N K x (fun r => (hx r).trans (hE r)) hNK hN hK) d
  | app d s =>
    intro E hs r h hE64 hE
    simp only [an] at h
    split_ifs at h with hM
    simp only [Option.some.injEq] at h; subst h
    refine sound_one _ E hE64 hE d (appE d s E) _ _ (appE_evL d s E) hM (fun x hx => ?_) hs
    have ht := layout_top M N K x (fun r => (hx r).trans (hE r)) hNK hN hK
    have hxd := hx d
    have hxs := hx s
    simp only [bx] at hxd hxs
    have h := layout_append M N K x ht d s (by omega)
    refine h.mono le_rfl (layout_mono M N K ?_) ?_
    · intro i
      by_cases hi : i = d
      · subst hi; simp only [Function.update_self]; exact appE_ev i s E x hx
      · simp [Function.update_of_ne hi]
    · exact Nat.mul_le_mul (by omega) le_rfl
  | eqb f a b =>
    intro E hs r h hE64 hE
    simp only [an] at h
    split_ifs at h with hd
    · simp only [Option.some.injEq] at h; subst h
      refine sound_nil _ E hE64 hE _ (fun x hx => ?_) hs
      exact (compile_eqb_overlap f a b hd _ M
        (layout_top M N K x (fun r => (hx r).trans (hE r)) hNK hN hK)).mono le_rfl le_rfl (by omega)
    · simp only [Option.some.injEq] at h; subst h
      refine sound_one _ E hE64 hE f ⟨1, none⟩ _ _ rfl hM1 (fun x hx => ?_) hs
      have h := compile_eqb_cert f a b hd _ M
        (layout_top M N K x (fun r => (hx r).trans (hE r)) hNK hN hK)
      rw [← layout_update] at h
      simpa [C4E.ev, show 2 * (M + 1) + 3 = 2 * M + 5 by omega] using h
  | nop =>
    intro E hs r h hE64 hE
    simp only [an, Option.some.injEq] at h; subst h
    refine sound_nil _ E hE64 hE _ (fun x hx => ?_) hs
    exact (compile_nop _ M (layout_top M N K x (fun r => (hx r).trans (hE r)) hNK hN hK)).mono
      le_rfl le_rfl (by omega)
  | seq p q ihp ihq =>
    intro E hs r h hE64 hE
    simp only [an] at h
    split at h
    · simp at h
    · rename_i r1 h1
      split at h
      · simp at h
      · rename_i r2 h2
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨l1, t1, s1⟩ := ihp E hs r1 h1 hE64 hE
        obtain ⟨l2, t2, s2⟩ := ihq r1.out r1.hs r2 h2 l1 t1
        refine ⟨l2, t2, fun x hx => ?_⟩
        obtain ⟨o1, c1⟩ := s1 x hx
        obtain ⟨o2, c2⟩ := s2 _ o1
        rw [tAp_tcomp]
        exact ⟨o2, c1.seq c2⟩
  | ifb i p q ihp ihq =>
    intro E hs r h hE64 hE
    simp only [an] at h
    split at h
    · simp at h
    · rename_i r1 h1
      split at h
      · simp at h
      · rename_i r2 h2
        split_ifs at h with htop
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨-, -, s1⟩ := ihp E hs r1 h1 hE64 hE
        obtain ⟨-, -, s2⟩ := ihq E r1.hs r2 h2 hE64 hE
        refine ⟨by rw [boxV_length]; exact hE64, topL_sound htop, fun x hx => ⟨?_, ?_⟩⟩
        · rw [bx_boxV _ _ hE64]; exact tAp_mono _ hx
        · obtain ⟨-, c1⟩ := s1 x hx
          obtain ⟨-, c2⟩ := s2 x hx
          have j := tAp_tjoin E r1.t r2.t x hx
          exact Cert.ifBit (tR i) (c1.mono le_rfl (layout_mono M N K j.1) le_rfl)
            (c2.mono le_rfl (layout_mono M N K j.2) le_rfl)
  | rep c body ih =>
    intro E hs r h hE64 hE
    simp only [an] at h
    rcases hhd : hs.headD (C4H.box []) with hb | _ <;> simp only [hhd] at h
    swap
    · split at h
      · simp at h
      · rename_i p hp
        split_ifs at h with htop
        simp only [Option.some.injEq] at h; subst h
        exact sound_unroll hNK hN hK c body (fun B hs' r hr hB64 hB => ih B hs' r hr hB64 hB) E
          hE64 hs.tail p hp htop
    split at h
    · simp at h
    · rename_i rb hrb
      split_ifs at h with hchk'
      simp only [Option.some.injEq] at h; subst h
      have hchk := (Bool.and_eq_true _ _).mp hchk' |>.2
      set B := mkBox E hb
      set R := E.getD c.val 0
      obtain ⟨hGB, hBM⟩ := chk_sound hchk
      obtain ⟨-, -, sb⟩ := ih B hs.tail rb hrb (mkBox_length _ _ hE64) hBM
      have hG : bx (boxV (tloop rb.t B R) E) = tAp (tloop rb.t B R) (bx E) := bx_boxV _ _ hE64
      have hGx : ∀ x, x ≤ bx E → ∀ j ≤ R, tAp (tloop rb.t B j) x ≤ bx B := by
        intro x hx j hj q
        have h1 : tAp (tloop rb.t B j) x q ≤ tAp (tloop rb.t B R) x q := by
          rw [tAp_tloop, tAp_tloop]; exact loop_mono_R _ q B hj x
        have h2 := tAp_mono (tloop rb.t B R) hx q
        rw [← hG] at h2
        exact h1.trans (h2.trans (hGB q))
      refine ⟨by rw [boxV_length]; exact hE64, fun i => (hGB i).trans (hBM i), fun x hx => ⟨?_, ?_⟩⟩
      · rw [hG]; exact tAp_mono _ hx
      · simp only
        refine rep_family c body (fun j => layout M N K (tAp (tloop rb.t B j) x)) R rb.T
          (layout M N K x) (layout_mono M N K fun q => by rw [tAp_tloop]; exact loop_ge _ q B 0 x)
          (by rw [layout_register]; exact hx c) (fun j hj => ?_) M (fun j hj => ?_)
          (fun j hj => layout_mono M N K fun q => by
            rw [tAp_tloop, tAp_tloop]; exact loop_mono_R _ q B hj x)
        · have hy := hGx x hx j hj.le
          obtain ⟨-, cb⟩ := sb _ hy
          exact cb.mono (tailB_le (tR c) _) (layout_mono M N K (loop_step rb.t B j x hy)) le_rfl
        · exact supB_le_of (layout_top M N K _ (fun q => (hGx x hx j hj.le q).trans (hBM q))
            hNK hN hK)

/-! ### Codes with `natC` leaves -/

/-- A code with bounded `natC` leaves. -/
inductive AC where
  | c (c : Code)
  | nat (r u : Fin 64) (v : ℕ)
  | s (p q : AC)

/-- `ac` describes the code `c` (`natC r u n` with `n ≤ v` at a leaf `nat r u v`). -/
inductive AC.Er : AC → Code → Prop
  | c (c : Code) : AC.Er (.c c) c
  | nat (r u : Fin 64) (v n : ℕ) (h : n ≤ v) : AC.Er (.nat r u v) (natC r u n)
  | s {p q : AC} {cp cq : Code} : AC.Er p cp → AC.Er q cq → AC.Er (.s p q) (.seq cp cq)

/-- The analyzer on `AC`. -/
def anA (M N K : ℕ) : AC → List ℕ → List C4H → Option C4R
  | .c c, E, hs => an M N K c E hs
  | .nat r u v, E, hs =>
    if r ≠ u ∧ E.getD u.val 0 ≤ 1 ∧ v ≤ M then
      some ⟨[(u.val, ⟨1, some (u.val, 1, 0)⟩), (r.val, ⟨v, none⟩)], (32 * v + 4) * (2 * M + 5),
        (E.set u.val 1).set r.val v, hs⟩
    else none
  | .s p q, E, hs =>
    match anA M N K p E hs with
    | none => none
    | some r1 =>
      match anA M N K q r1.out r1.hs with
      | none => none
      | some r2 => some ⟨tcomp r1.t r2.t, r1.T + r2.T, r2.out, r2.hs⟩

theorem tAp_two (u r : Fin 64) (hru : r ≠ u) (e f : C4E) (x : Fin 64 → ℕ) :
    tAp [(u.val, e), (r.val, f)] x = Function.update (Function.update x u (e.ev x)) r (f.ev x) := by
  funext q
  simp only [tAp, tget, Function.update_apply]
  by_cases h1 : q = r
  · subst h1
    have : Nat.beq u.val q.val = false := by
      rcases hb : Nat.beq u.val q.val
      · rfl
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hb)).symm hru
    simp [this]
  · by_cases h2 : q = u
    · subst h2; simp [h1]
    · have b1 : Nat.beq u.val q.val = false := by
        rcases hb : Nat.beq u.val q.val
        · rfl
        · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hb)).symm h2
      have b2 : Nat.beq r.val q.val = false := by
        rcases hb : Nat.beq r.val q.val
        · rfl
        · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hb)).symm h1
      simp only [b1, b2, Bool.false_eq_true, ↓reduceIte, h1, h2]
      exact ev_c4Id x q

theorem anA_sound (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) (hM1 : 1 ≤ M) :
    ∀ (ac : AC) (c : Code), AC.Er ac c → ∀ (E : List ℕ) (hs : List C4H) (r : C4R),
      anA M N K ac E hs = some r → E.length = 64 → (∀ i, bx E i ≤ M) → Sound M N K c E r := by
  intro ac c hac
  induction hac with
  | c c => exact an_sound hNK hN hK hM1 c
  | nat r u v n hn =>
    intro E hs res h hE64 hE
    simp only [anA] at h
    split_ifs at h with hc
    obtain ⟨hru, hu, hv⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    have hb : bx ((E.set u.val 1).set r.val v) = Function.update (Function.update (bx E) u 1) r v := by
      rw [bx_set _ (by simp [hE64]), bx_set _ hE64]
    refine ⟨by simp [hE64], ?_, fun x hx => ⟨?_, ?_⟩⟩
    · rw [hb]; intro i
      simp only [Function.update_apply]; split_ifs
      · exact hv
      · exact hM1
      · exact hE i
    · rw [hb, tAp_two u r hru]; intro i
      simp only [Function.update_apply, C4E.ev, xN_fin]
      have := hx u
      simp only [bx] at this
      split_ifs
      · exact le_rfl
      · omega
      · exact hx i
    · rw [tAp_two u r hru]
      have hx1 : x ≤ Function.update x u 1 := by
        intro i; by_cases h : i = u
        · subst h; have := hx i; simp only [bx] at this; simp; omega
        · simp [Function.update_of_ne h]
      have hin : RingInputs M N K (layout M N K (Function.update x u 1)) :=
        layout_inputs M N K _ (fun i => by
          by_cases h : i = u
          · subst h; simpa using hM1
          · simpa [Function.update_of_ne h] using (hx i).trans (hE i)) hNK hN hK
      have hc := layout_nat_update M N K (Function.update x u 1) hin r u hru n (by simp)
        (hn.trans hv)
      refine hc.mono (layout_mono M N K hx1) (layout_mono M N K ?_) ?_
      · intro i
        simp only [Function.update_apply, C4E.ev, xN_fin]
        split_ifs <;> omega
      · exact Nat.mul_le_mul (by omega) le_rfl
  | s hp hq ihp ihq =>
    intro E hs r h hE64 hE
    simp only [anA] at h
    split at h
    · simp at h
    · rename_i r1 h1
      split at h
      · simp at h
      · rename_i r2 h2
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨l1, t1, s1⟩ := ihp E hs r1 h1 hE64 hE
        obtain ⟨l2, t2, s2⟩ := ihq r1.out r1.hs r2 h2 l1 t1
        refine ⟨l2, t2, fun x hx => ?_⟩
        obtain ⟨o1, c1⟩ := s1 x hx
        obtain ⟨o2, c2⟩ := s2 _ o1
        rw [tAp_tcomp]
        exact ⟨o2, c1.seq c2⟩

/-- **The check**: `ac` on the input box `E` (length `64`, `≤ M`) with hints `hs` gives an output
box `≤ Eo` and a time `≤ T`. -/
def c4Ok (M N K : ℕ) (ac : AC) (E : List ℕ) (hs : List C4H) (Eo : List ℕ) (T : ℕ) : Bool :=
  match anA M N K ac E hs with
  | none => false
  | some r => Nat.beq E.length 64 && topL E M && leL r.out Eo && Nat.ble r.T T

/-- **The certificate of a checked code.** -/
theorem c4Ok_cert (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) (hM1 : 1 ≤ M)
    {ac : AC} {c : Code} (hac : AC.Er ac c) {E : List ℕ} {hs : List C4H} {Eo : List ℕ}
    {T : ℕ} (h : c4Ok M N K ac E hs Eo T = true) (x : Fin 64 → ℕ) (hx : x ≤ bx E) :
    Cert (compile c) (layout M N K x) (layout M N K (bx Eo)) T := by
  unfold c4Ok at h
  split at h
  · simp at h
  · rename_i r hr
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨h64, htop⟩, hle⟩, hT⟩ := h
    obtain ⟨-, -, hs⟩ := anA_sound hNK hN hK hM1 ac c hac E _ r hr h64 (topL_sound htop)
    obtain ⟨ho, hc⟩ := hs x hx
    exact hc.mono le_rfl (layout_mono M N K (ho.trans (leL_sound hle))) hT

end Sound

end AdvancedEncryption.ExpLUT.Prog.RedKeyC4
