import SigabaNeo.Lib.Lattices.Homomorphic.RegProg

/-!
# Multiplexer trees as register programs

A mux tree of `n` levels selects one of `2^n` leaf bits by `n` selector bits, level `1` (at the
leaves) by the first selector. As a register program of NAND gates (`MuxTree.tree`), in post-order:

* level `1` is not a gate: the pair of leaves `(c₀, c₁)` is the source `zero` (a register holding
  `0`) if `(0, 0)`, `1` if `(1, 1)`, the selector `s 1` if `(0, 1)`, its negation `ns 1` if
  `(1, 0)` (`src1`);
* a node of level `ℓ ≥ 2` with children `lo` (selector `0`) and `hi` (selector `1`) is three gates
  `X1 := NAND(s ℓ, hi)`, `X2 := NAND(ns ℓ, lo)`, `dst := NAND(X1, X2)` (`node`);
* the result of a level-`ℓ` node goes to the register `lo ℓ` or `hi ℓ` of its side, the root to
  the destination.

Everything is generic in the layout (`Layout`: the selector sources, the registers) and in the
leaves (a function `ℕ → Bool`, read at `base, base + 1, …`), so nothing is ever enumerated.

**`MuxTree.run_tree`**: on any value type, running the tree of `m + 2` levels writes at the
destination the value `muxVal m.succ base` of the recursive formula of the tree, and changes only
registers of the tree (`Wr`). Two instances follow:

* `evalBool`-type values: the leaf at `base + idx b (m + 2)` (`muxVal_bool`);
* depths: at most `depthBound` (`muxVal_depth`), the level `ℓ` adding `2` to the larger of its
  selectors' and its children's depths.

`length_tree`: `3 (2^(m+1) − 1)` gates (`length_tree_add`).
-/

namespace SigabaNeo.Lattices

namespace MuxTree

variable {ι : Type*} {W : ℕ}

/-- The layout of a tree: selectors and their negations by level, the register holding `0`, the
registers of the children of each level, and two temporaries. -/
structure Layout (ι : Type*) (W : ℕ) where
  /-- The selector of level `ℓ`. -/
  s : ℕ → Src ι W
  /-- Its negation. -/
  ns : ℕ → Src ι W
  /-- A register holding `0`. -/
  zero : Fin W
  /-- The register of the `lo` child of level `ℓ`. -/
  lo : ℕ → Fin W
  /-- The register of the `hi` child of level `ℓ`. -/
  hi : ℕ → Fin W
  /-- Temporaries. -/
  x1 : Fin W
  /-- Temporaries. -/
  x2 : Fin W

variable (L : Layout ι W) (leaf : ℕ → Bool)

/-- The level-`1` value of the leaves `base`, `base + 1`, as a source. -/
def src1 (base : ℕ) : Src ι W :=
  if leaf base then (if leaf (base + 1) then .one else L.ns 1)
  else (if leaf (base + 1) then L.s 1 else .reg L.zero)

/-- A node of level `ℓ`. -/
def node (ℓ : ℕ) (lo hi : Src ι W) (dst : Fin W) : RP ι W :=
  [⟨L.x1, L.s ℓ, hi⟩, ⟨L.x2, L.ns ℓ, lo⟩, ⟨dst, .reg L.x1, .reg L.x2⟩]

/-- **The tree of `m + 2` levels** on the leaves `base … base + 2^(m+2) − 1`, its root written to
`dst`, in post-order. -/
def tree : ℕ → ℕ → Fin W → RP ι W
  | 0, base, dst => node L 2 (src1 L leaf base) (src1 L leaf (base + 2)) dst
  | m + 1, base, dst =>
    tree m base (L.lo (m + 2)) ++ tree m (base + 2 ^ (m + 2)) (L.hi (m + 2)) ++
      node L (m + 3) (.reg (L.lo (m + 2))) (.reg (L.hi (m + 2))) dst

/-! ### Length -/

theorem length_tree_add (m base : ℕ) (dst : Fin W) :
    (tree L leaf m base dst).length + 3 = 3 * 2 ^ (m + 1) := by
  induction m generalizing base dst with
  | zero => simp [tree, node]
  | succ m ih =>
    simp only [tree, List.length_append, node, List.length_cons, List.length_nil]
    have h1 := ih base (L.lo (m + 2))
    have h2 := ih (base + 2 ^ (m + 2)) (L.hi (m + 2))
    have h3 : 2 ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 := pow_succ _ _
    omega

/-- The tree of `m + 2` levels has `3 (2^(m+1) − 1)` gates. -/
theorem length_tree (m base : ℕ) (dst : Fin W) :
    (tree L leaf m base dst).length = 3 * (2 ^ (m + 1) - 1) := by
  have := length_tree_add L leaf m base dst
  have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  omega

/-! ### Values on any type -/

section Generic

variable {α : Type*} (one : α) (step : α → α → α) (sv nsv : ℕ → α) (z : α)

/-- The value of the level-`1` pair at `base`. -/
def val1 (base : ℕ) : α :=
  if leaf base then (if leaf (base + 1) then one else nsv 1)
  else (if leaf (base + 1) then sv 1 else z)

/-- **The value of a tree** of `j + 1` levels at `base`, from the values `sv ℓ`, `nsv ℓ` of the
selectors and their negations and the value `z` of `zero`. -/
def muxVal : ℕ → ℕ → α
  | 0, base => val1 leaf one sv nsv z base
  | j + 1, base =>
    step (step (sv (j + 2)) (muxVal j (base + 2 ^ (j + 1))))
      (step (nsv (j + 2)) (muxVal j base))

end Generic

/-- The registers a tree of `m + 2` levels with root `dst` may write. -/
def Wr (m : ℕ) (dst r : Fin W) : Prop :=
  r = L.x1 ∨ r = L.x2 ∨ r = dst ∨ ∃ ℓ, 2 ≤ ℓ ∧ ℓ < m + 2 ∧ (r = L.lo ℓ ∨ r = L.hi ℓ)

/-- The hypotheses on the layout for a tree of `m + 2` levels with root `dst`: the registers it
writes are distinct where they must be, and the selectors and `zero` are not among them. -/
structure Good (m : ℕ) (dst : Fin W) : Prop where
  x12 : L.x1 ≠ L.x2
  lohi : ∀ ℓ ℓ', 2 ≤ ℓ → ℓ < m + 2 → 2 ≤ ℓ' → ℓ' < m + 2 →
    L.lo ℓ ≠ L.hi ℓ' ∧ (L.lo ℓ = L.lo ℓ' → ℓ = ℓ') ∧ (L.hi ℓ = L.hi ℓ' → ℓ = ℓ')
  lox : ∀ ℓ, 2 ≤ ℓ → ℓ < m + 2 → L.lo ℓ ≠ L.x1 ∧ L.lo ℓ ≠ L.x2 ∧ L.hi ℓ ≠ L.x1 ∧ L.hi ℓ ≠ L.x2
  dstx : dst ≠ L.x1 ∧ dst ≠ L.x2
  dstl : ∀ ℓ, 2 ≤ ℓ → ℓ < m + 2 → dst ≠ L.lo ℓ ∧ dst ≠ L.hi ℓ
  sel : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ m + 2 → ∀ r, Wr L m dst r → L.s ℓ ≠ .reg r ∧ L.ns ℓ ≠ .reg r
  zero : ¬ Wr L m dst L.zero

theorem Src.val_eq_of {α : Type*} {inp : ι → α} {one : α} {R R' : Fin W → α} (s : Src ι W)
    (h : ∀ r, s = .reg r → R' r = R r) : s.val inp one R' = s.val inp one R := by
  cases s with
  | input i => rfl
  | one => rfl
  | reg r => exact h r rfl

theorem Good.sub_lo {m : ℕ} {dst : Fin W} (h : Good L (m + 1) dst) : Good L m (L.lo (m + 2)) where
  x12 := h.x12
  lohi ℓ ℓ' h1 h2 h3 h4 := h.lohi ℓ ℓ' h1 (by omega) h3 (by omega)
  lox ℓ h1 h2 := h.lox ℓ h1 (by omega)
  dstx := ⟨(h.lox (m + 2) (by omega) (by omega)).1, (h.lox (m + 2) (by omega) (by omega)).2.1⟩
  dstl ℓ h1 h2 := ⟨fun e => by have := (h.lohi _ _ (by omega) (by omega) h1 (by omega)).2.1 e; omega,
    (h.lohi _ _ (by omega) (by omega) h1 (by omega)).1⟩
  sel ℓ h1 h2 r hr := h.sel ℓ h1 (by omega) r (by
    rcases hr with hr | hr | hr | ⟨ℓ', h3, h4, hr⟩
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inr ⟨m + 2, by omega, by omega, Or.inl hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ℓ', h3, by omega, hr⟩)))
  zero hz := h.zero (by
    rcases hz with hr | hr | hr | ⟨ℓ', h3, h4, hr⟩
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inr ⟨m + 2, by omega, by omega, Or.inl hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ℓ', h3, by omega, hr⟩)))

theorem Good.sub_hi {m : ℕ} {dst : Fin W} (h : Good L (m + 1) dst) : Good L m (L.hi (m + 2)) where
  x12 := h.x12
  lohi ℓ ℓ' h1 h2 h3 h4 := h.lohi ℓ ℓ' h1 (by omega) h3 (by omega)
  lox ℓ h1 h2 := h.lox ℓ h1 (by omega)
  dstx := ⟨(h.lox (m + 2) (by omega) (by omega)).2.2.1, (h.lox (m + 2) (by omega) (by omega)).2.2.2⟩
  dstl ℓ h1 h2 := ⟨fun e => (h.lohi _ _ h1 (by omega) (by omega) (by omega)).1 e.symm,
    fun e => by have := (h.lohi _ _ (by omega) (by omega) h1 (by omega)).2.2 e; omega⟩
  sel ℓ h1 h2 r hr := h.sel ℓ h1 (by omega) r (by
    rcases hr with hr | hr | hr | ⟨ℓ', h3, h4, hr⟩
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inr ⟨m + 2, by omega, by omega, Or.inr hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ℓ', h3, by omega, hr⟩)))
  zero hz := h.zero (by
    rcases hz with hr | hr | hr | ⟨ℓ', h3, h4, hr⟩
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inr ⟨m + 2, by omega, by omega, Or.inr hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ℓ', h3, by omega, hr⟩)))

section Run

variable {α : Type*} (inp : ι → α) (one : α) (step : α → α → α)

/-- One node: `X1`, `X2`, then the destination. -/
theorem run_node (ℓ : ℕ) (a b : Src ι W) (dst : Fin W) (R : Fin W → α) :
    RP.run inp one step (node L ℓ a b dst) R =
      let R1 := Function.update R L.x1 (step ((L.s ℓ).val inp one R) (b.val inp one R))
      let R2 := Function.update R1 L.x2 (step ((L.ns ℓ).val inp one R1) (a.val inp one R1))
      Function.update R2 dst (step (R2 L.x1) (R2 L.x2)) := rfl

/-- **The run of a tree**: the root holds `muxVal`, and only registers of `Wr` change. -/
theorem run_tree (m : ℕ) (base : ℕ) (dst : Fin W) (R : Fin W → α) (sv nsv : ℕ → α) (z : α)
    (hg : Good L m dst)
    (hs : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ m + 2 → (L.s ℓ).val inp one R = sv ℓ ∧ (L.ns ℓ).val inp one R = nsv ℓ)
    (hz : R L.zero = z) :
    RP.run inp one step (tree L leaf m base dst) R dst =
        muxVal leaf one step sv nsv z (m + 1) base ∧
      ∀ r, ¬ Wr L m dst r → RP.run inp one step (tree L leaf m base dst) R r = R r := by
  induction m generalizing base dst R with
  | zero =>
    have hsrc1 : ∀ b, (∀ r, Wr L 0 dst r → (src1 L leaf b) ≠ .reg r) ∧
        (src1 L leaf b).val inp one R = val1 leaf one sv nsv z b := by
      intro b
      have h1 := hs 1 le_rfl (by omega)
      unfold src1 val1
      split_ifs
      · exact ⟨fun r _ h => (by cases h), rfl⟩
      · exact ⟨fun r hr => (hg.sel 1 le_rfl (by omega) r hr).2, h1.2⟩
      · exact ⟨fun r hr => (hg.sel 1 le_rfl (by omega) r hr).1, h1.1⟩
      · exact ⟨fun r hr e => hg.zero (Src.reg.inj e ▸ hr), hz⟩
    have wx1 : Wr L 0 dst L.x1 := Or.inl rfl
    have wx2 : Wr L 0 dst L.x2 := Or.inr (Or.inl rfl)
    have h2 := hs 2 (by omega) le_rfl
    refine ⟨?_, fun r hr => ?_⟩
    · simp only [tree, run_node, Function.update_self]
      rw [Function.update_of_ne hg.x12, Function.update_self]
      rw [Src.val_eq_of (L.ns 2) (fun r e => by
            rw [Function.update_of_ne]; rintro rfl; exact (hg.sel 2 (by omega) le_rfl _ wx1).2 e),
        Src.val_eq_of (src1 L leaf base) (fun r e => by
            rw [Function.update_of_ne]; rintro rfl; exact (hsrc1 base).1 _ wx1 e),
        h2.1, h2.2, (hsrc1 base).2, (hsrc1 (base + 2)).2]
      rfl
    · simp only [tree, run_node]
      have n1 : r ≠ L.x1 := fun e => hr (Or.inl e)
      have n2 : r ≠ L.x2 := fun e => hr (Or.inr (Or.inl e))
      have n3 : r ≠ dst := fun e => hr (Or.inr (Or.inr (Or.inl e)))
      rw [Function.update_of_ne n3, Function.update_of_ne n2, Function.update_of_ne n1]
  | succ m ih =>
    have glo := hg.sub_lo
    have ghi := hg.sub_hi
    -- the lo subtree
    set R1 := RP.run inp one step (tree L leaf m base (L.lo (m + 2))) R with hR1
    have hsub : ∀ r, Wr L m (L.lo (m + 2)) r → Wr L (m + 1) dst r := by
      intro r hr
      rcases hr with hr | hr | hr | ⟨ℓ', h3, h4, hr⟩
      · exact Or.inl hr
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr (Or.inr ⟨m + 2, by omega, by omega, Or.inl hr⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ℓ', h3, by omega, hr⟩))
    have hsubh : ∀ r, Wr L m (L.hi (m + 2)) r → Wr L (m + 1) dst r := by
      intro r hr
      rcases hr with hr | hr | hr | ⟨ℓ', h3, h4, hr⟩
      · exact Or.inl hr
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr (Or.inr ⟨m + 2, by omega, by omega, Or.inr hr⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ℓ', h3, by omega, hr⟩))
    obtain ⟨e1, f1⟩ := ih base (L.lo (m + 2)) R glo (fun ℓ h1 h2 => hs ℓ h1 (by omega)) hz
    rw [← hR1] at e1 f1
    -- the selectors and `zero` are unchanged
    have hs1 : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ m + 3 →
        (L.s ℓ).val inp one R1 = sv ℓ ∧ (L.ns ℓ).val inp one R1 = nsv ℓ := by
      intro ℓ h1 h2
      have hh := hs ℓ h1 h2
      refine ⟨?_, ?_⟩
      · rw [Src.val_eq_of (L.s ℓ) (fun r e => f1 r (fun hr => (hg.sel ℓ h1 h2 r (hsub r hr)).1 e)),
          hh.1]
      · rw [Src.val_eq_of (L.ns ℓ) (fun r e => f1 r (fun hr => (hg.sel ℓ h1 h2 r (hsub r hr)).2 e)),
          hh.2]
    have hz1 : R1 L.zero = z := by rw [f1 _ (fun hr => hg.zero (hsub _ hr)), hz]
    -- the hi subtree
    set R2 := RP.run inp one step (tree L leaf m (base + 2 ^ (m + 2)) (L.hi (m + 2))) R1 with hR2
    obtain ⟨e2, f2⟩ := ih (base + 2 ^ (m + 2)) (L.hi (m + 2)) R1 ghi
      (fun ℓ h1 h2 => hs1 ℓ h1 (by omega)) hz1
    rw [← hR2] at e2 f2
    have hs2 : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ m + 3 →
        (L.s ℓ).val inp one R2 = sv ℓ ∧ (L.ns ℓ).val inp one R2 = nsv ℓ := by
      intro ℓ h1 h2
      have hh := hs1 ℓ h1 h2
      refine ⟨?_, ?_⟩
      · rw [Src.val_eq_of (L.s ℓ) (fun r e => f2 r (fun hr => (hg.sel ℓ h1 h2 r (hsubh r hr)).1 e)),
          hh.1]
      · rw [Src.val_eq_of (L.ns ℓ) (fun r e => f2 r (fun hr => (hg.sel ℓ h1 h2 r (hsubh r hr)).2 e)),
          hh.2]
    -- the lo child survives the hi subtree
    have hlo2 : R2 (L.lo (m + 2)) = muxVal leaf one step sv nsv z (m + 1) base := by
      rw [f2 _ (fun hr => ?_), e1]
      rcases hr with hr | hr | hr | ⟨ℓ', h3, h4, hr⟩
      · exact (hg.lox (m + 2) (by omega) (by omega)).1 hr
      · exact (hg.lox (m + 2) (by omega) (by omega)).2.1 hr
      · exact (hg.lohi (m + 2) (m + 2) (by omega) (by omega) (by omega) (by omega)).1 hr
      · rcases hr with hr | hr
        · have := (hg.lohi _ _ (by omega) (by omega) h3 (by omega)).2.1 hr; omega
        · exact (hg.lohi _ _ (by omega) (by omega) h3 (by omega)).1 hr
    have wx1 : Wr L (m + 1) dst L.x1 := Or.inl rfl
    have hlox := hg.lox (m + 2) (by omega) (by omega)
    have h3 := hs2 (m + 3) (by omega) le_rfl
    have htree : tree L leaf (m + 1) base dst =
        tree L leaf m base (L.lo (m + 2)) ++ tree L leaf m (base + 2 ^ (m + 2)) (L.hi (m + 2)) ++
          node L (m + 3) (.reg (L.lo (m + 2))) (.reg (L.hi (m + 2))) dst := rfl
    refine ⟨?_, fun r hr => ?_⟩
    · rw [htree, RP.run_append, RP.run_append, ← hR1, ← hR2, run_node]
      simp only [Function.update_self]
      rw [Function.update_of_ne hg.x12, Function.update_self]
      rw [Src.val_eq_of (L.ns (m + 3)) (fun r e => by
            rw [Function.update_of_ne]; rintro rfl; exact (hg.sel _ (by omega) le_rfl _ wx1).2 e)]
      rw [h3.1, h3.2]
      simp only [Src.val]
      rw [Function.update_of_ne hlox.1, e2, hlo2]
      rfl
    · rw [htree, RP.run_append, RP.run_append, ← hR1, ← hR2, run_node]
      have n1 : r ≠ L.x1 := fun e => hr (Or.inl e)
      have n2 : r ≠ L.x2 := fun e => hr (Or.inr (Or.inl e))
      have n3 : r ≠ dst := fun e => hr (Or.inr (Or.inr (Or.inl e)))
      simp only
      rw [Function.update_of_ne n3, Function.update_of_ne n2, Function.update_of_ne n1,
        f2 r (fun h => hr (hsubh r h)), f1 r (fun h => hr (hsub r h))]

end Run

/-- `muxVal` of `j + 1` levels reads the selectors of levels `1 … j + 1` only. -/
theorem muxVal_congr {α : Type*} (one : α) (step : α → α → α) (sv nsv sv' nsv' : ℕ → α) (z : α)
    (j : ℕ) (h : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ j + 1 → sv ℓ = sv' ℓ ∧ nsv ℓ = nsv' ℓ) (base : ℕ) :
    muxVal leaf one step sv nsv z j base = muxVal leaf one step sv' nsv' z j base := by
  induction j generalizing base with
  | zero =>
    simp only [muxVal, val1]
    rw [(h 1 le_rfl le_rfl).1, (h 1 le_rfl le_rfl).2]
  | succ j ih =>
    simp only [muxVal]
    rw [ih (fun ℓ h1 h2 => h ℓ h1 (by omega)), ih (fun ℓ h1 h2 => h ℓ h1 (by omega)),
      (h (j + 2) (by omega) le_rfl).1, (h (j + 2) (by omega) le_rfl).2]

/-! ### Boolean values -/

/-- The index selected by the bits `b 1, b 2, …, b n`, `b 1` least significant. -/
def idx (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => idx b n + (b (n + 1)).toNat * 2 ^ n

theorem idx_lt (b : ℕ → Bool) (n : ℕ) : idx b n < 2 ^ n := by
  induction n with
  | zero => simp [idx]
  | succ n ih =>
    simp only [idx, pow_succ]
    cases b (n + 1) <;> simp <;> omega

/-- **The Boolean value of a tree**: the leaf selected by the selector bits. -/
theorem muxVal_bool (b : ℕ → Bool) (j base : ℕ) :
    muxVal leaf true (fun x y => !(x && y)) (fun ℓ => b ℓ) (fun ℓ => !b ℓ) false j base =
      leaf (base + idx b (j + 1)) := by
  induction j generalizing base with
  | zero =>
    simp only [muxVal, val1, idx, zero_add, pow_zero, mul_one]
    cases h0 : leaf base <;> cases h1 : leaf (base + 1) <;> cases hb : b 1 <;> simp [h0, h1]
  | succ j ih =>
    simp only [muxVal, ih]
    have : idx b (j + 1 + 1) = idx b (j + 1) + (b (j + 2)).toNat * 2 ^ (j + 1) := rfl
    rw [this]
    have e : base + 2 ^ (j + 1) + idx b (j + 1) = base + (idx b (j + 1) + 1 * 2 ^ (j + 1)) := by
      omega
    cases b (j + 2)
    · simp
    · rw [e]; simp

/-- The index of the bits of `v` is `v` mod `2^n`. -/
theorem idx_testBit (v n : ℕ) : idx (fun ℓ => v.testBit (ℓ - 1)) n = v % 2 ^ n := by
  induction n with
  | zero => simp [idx, Nat.mod_one]
  | succ n ih =>
    simp only [idx, ih, Nat.add_sub_cancel]
    rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ n) with h | h <;> simp [h, Nat.mul_comm]

theorem idx_congr (b b' : ℕ → Bool) (n : ℕ) (h : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ n → b ℓ = b' ℓ) :
    idx b n = idx b' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [idx]
    rw [ih (fun ℓ h1 h2 => h ℓ h1 (by omega)), h (n + 1) (by omega) le_rfl]

/-- The bits of an index are the selector bits. -/
theorem testBit_idx (b : ℕ → Bool) (n j : ℕ) :
    (idx b n).testBit j = (decide (j < n) && b (j + 1)) := by
  induction n with
  | zero => simp [idx]
  | succ n ih =>
    simp only [idx]
    rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (idx_lt b n)]
    by_cases hj : j < n
    · rw [if_pos hj, ih]; simp [hj, show j < n + 1 by omega]
    · rw [if_neg hj]
      by_cases e : j = n
      · subst e; cases b (j + 1) <;> simp
      · obtain ⟨t, ht⟩ : ∃ t, j - n = t + 1 := ⟨j - n - 1, by omega⟩
        have h1 : Nat.testBit 1 (j - n) = false := by rw [ht, Nat.testBit_succ]; simp
        cases b (n + 1) <;> simp [show ¬ j < n + 1 by omega, h1]

/-! ### Depths -/

/-- The depth bound of a tree of `j + 1` levels: level `ℓ ≥ 2` adds `2` to the larger of its
selectors' and its children's bounds; `e1` bounds the level-`1` sources. -/
def depthBound (ds : ℕ → ℕ) (e1 : ℕ) : ℕ → ℕ
  | 0 => e1
  | j + 1 => max (ds (j + 2)) (depthBound ds e1 j) + 2

theorem muxVal_depth (sv nsv : ℕ → ℕ) (z : ℕ) (ds : ℕ → ℕ) (e1 : ℕ)
    (j : ℕ) (hs : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ j + 1 → sv ℓ ≤ ds ℓ ∧ nsv ℓ ≤ ds ℓ) (hz : z ≤ e1)
    (h1 : ds 1 ≤ e1) (base : ℕ) :
    muxVal leaf 0 (fun x y => max x y + 1) sv nsv z j base ≤ depthBound ds e1 j := by
  induction j generalizing base with
  | zero =>
    simp only [muxVal, val1, depthBound]
    have := hs 1 le_rfl le_rfl
    split_ifs <;> omega
  | succ j ih =>
    simp only [muxVal, depthBound]
    have := hs (j + 2) (by omega) le_rfl
    have := ih (fun ℓ h1 h2 => hs ℓ h1 (by omega)) base
    have := ih (fun ℓ h1 h2 => hs ℓ h1 (by omega)) (base + 2 ^ (j + 1))
    omega

end MuxTree

end SigabaNeo.Lattices
