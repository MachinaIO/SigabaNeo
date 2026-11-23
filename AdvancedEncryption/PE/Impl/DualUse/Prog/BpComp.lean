import SigabaNeo.Lib.Machines.Prog.AppendW

/-!
# The compiler of branching programs: the tree code

The compiler (`BP_PLAN.md` §5.2) writes the instruction stream `rpW 512 (bpRP (tablesOf C))` of the
predicate circuit from the predicate word `C`. It is a coin-free tape program on `64` tapes
(`Prog 64`), outside the word machine `ValVM` (which cannot lengthen a word: the stream is
`≈ 2^60` bits). This file holds the layout, the specification of the words written (by slots, as
`unaryW 512`), and the code and law of one **mux tree**:

* `blk j`: slot `j` in unary on `512` bits; `insW d a b` one instruction;
* `treeW Y leaf m base d`: the word of the tree of `m + 2` levels on the leaves
  `leaf base, …, leaf (base + 2^(m+2) − 1)`, root at slot `d`, in post-order (the recursion of
  `MuxTree.tree`);
* `treeP m dE`: the code; `run_treeP`: from a table cursor `TT = T₀.drop (base · w)` (entries of
  `w = |JZ| + 1 + |JB|` bits, the leaf the bit after `|JZ|` bits) it appends
  `treeW Y (lfT T₀) m base d` and advances the cursor by `2^(m+2)` entries.

The selector emitters are parameters (`sE`, `nsE`) with laws `Em`; the destination of a node is
chosen by the loop counter of its parent level.
-/

namespace AdvancedEncryption.DualUse.BpComp

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open scoped Prog

/-! ### Words -/

/-- Slot `j` in unary on `512` bits. -/
def blk (j : ℕ) : List Bool := List.replicate j true ++ List.replicate (512 - j) false

/-- One instruction: destination, left and right slots. -/
def insW (d a b : ℕ) : List Bool := blk d ++ blk a ++ blk b

/-- The slots of a tree: selectors and negations by level, `zero`, temporaries, children. -/
structure SLay where
  s : ℕ → ℕ
  ns : ℕ → ℕ
  zero : ℕ
  x1 : ℕ
  x2 : ℕ
  lo : ℕ → ℕ
  hi : ℕ → ℕ

variable (Y : SLay) (leaf : ℕ → Bool)

/-- The level-`1` source of the leaves `base`, `base + 1`. -/
def src1W (base : ℕ) : ℕ :=
  if leaf base then (if leaf (base + 1) then 0 else Y.ns 1)
  else (if leaf (base + 1) then Y.s 1 else Y.zero)

/-- A node of level `ℓ`. -/
def nodeW (ℓ lo hi d : ℕ) : List Bool :=
  insW Y.x1 (Y.s ℓ) hi ++ insW Y.x2 (Y.ns ℓ) lo ++ insW d Y.x1 Y.x2

/-- **The word of a tree** of `m + 2` levels. -/
def treeW : ℕ → ℕ → ℕ → List Bool
  | 0, base, d => nodeW Y 2 (src1W Y leaf base) (src1W Y leaf (base + 2)) d
  | m + 1, base, d =>
    treeW m base (Y.lo (m + 2)) ++ treeW m (base + 2 ^ (m + 2)) (Y.hi (m + 2)) ++
      nodeW Y (m + 3) (Y.lo (m + 2)) (Y.hi (m + 2)) d

/-! ### Tapes -/

abbrev tIN : Fin 64 := 0
abbrev tO : Fin 64 := 1
abbrev tTT : Fin 64 := 2
abbrev tA : Fin 64 := 3
abbrev tB : Fin 64 := 4
abbrev tb0 : Fin 64 := 5
abbrev tb1 : Fin 64 := 6
abbrev tb2 : Fin 64 := 7
abbrev tb3 : Fin 64 := 8
/-- Bits of an entry before the leaf bit. -/
abbrev tJZ : Fin 64 := 9
/-- Bits of an entry after the leaf bit. -/
abbrev tJB : Fin 64 := 10
abbrev tCUR : Fin 64 := 11
abbrev tIB : Fin 64 := 12
abbrev tIZ : Fin 64 := 13
abbrev tPB : Fin 64 := 14
abbrev tPZ : Fin 64 := 15
abbrev tQB : Fin 64 := 16
abbrev tQZ : Fin 64 := 17
abbrev tJC : Fin 64 := 18
abbrev tSC : Fin 64 := 19

/-- The loop counter of the tree of `m + 3` levels. -/
def tc (m : ℕ) : Fin 64 := ⟨22 + m % 38, by omega⟩

theorem tc_val (m : ℕ) : (tc m).val = 22 + m % 38 := rfl

theorem tc_inj {m m' : ℕ} (hm : m < 38) (hm' : m' < 38) (h : tc m = tc m') : m = m' := by
  have := congrArg Fin.val h
  simp only [tc_val] at this
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hm'] at this
  omega

theorem tc_ne {m : ℕ} {t : Fin 64} (ht : t.val < 22) : tc m ≠ t := fun h => by
  have := congrArg Fin.val h; rw [tc_val] at this; omega

/-! ### Emitters -/

/-- `E` appends `v` to the output on every store satisfying `P`. -/
def Em (E : Prog 64) (P : Store 64 → Prop) (v : List Bool) : Prop :=
  ∀ s, P s → run E s = Function.update s tO (s tO ++ v)

/-- `P` survives appending to the output. -/
def OStable (P : Store 64 → Prop) : Prop := ∀ s w, P s → P (Function.update s tO w)

theorem Em.seq {E F : Prog 64} {P : Store 64 → Prop} {v u : List Bool} (hP : OStable P)
    (hE : Em E P v) (hF : Em F P u) : Em (E ⨾ F) P (v ++ u) := by
  intro s hs
  rw [run_seq, hE s hs, hF _ (hP s _ hs), Function.update_self, Function.update_idem,
    List.append_assoc]

theorem Em.mono {E : Prog 64} {P P' : Store 64 → Prop} {v : List Bool} (h : Em E P v)
    (hP : ∀ s, P' s → P s) : Em E P' v := fun s hs => h s (hP s hs)

theorem em_emitU (P : Store 64 → Prop) (j : ℕ) : Em (emitU tO 512 j) P (blk j) :=
  fun s _ => run_emitU tO 512 j s

theorem em_ifBit' {E F : Prog 64} {P : Store 64 → Prop} {v u : List Bool} (i : Fin 64) (c : Bool)
    (hE : Em E P v) (hF : Em F P u) :
    Em (ifBit i E F) (fun s => P s ∧ hd (s i) = c) (if c then v else u) := by
  intro s ⟨hs, hc⟩
  rw [run_ifBit, hc]
  cases c
  · simp [hF s hs]
  · simp [hE s hs]

theorem em_ifBlank {E F : Prog 64} {P : Store 64 → Prop} {v u : List Bool} (i : Fin 64) (w : List Bool)
    (hE : Em E P v) (hF : Em F P u) :
    Em (ifBlank i E F) (fun s => P s ∧ s i = w) (if w = [] then v else u) := by
  intro s ⟨hs, hc⟩
  rw [run_ifBlank, hc]
  split_ifs
  · exact hE s hs
  · exact hF s hs

/-! ### The tree code -/

variable (sE nsE : ℕ → Prog 64)

/-- Read the next leaf into `b`: skip `|JZ|` bits, pop one, skip `|JB|` bits. -/
def readL (b : Fin 64) : Prog 64 := dropT tTT tJZ tA ⨾ pp tTT b ⨾ dropT tTT tJB tA

/-- The level-`1` source of the leaf bits on `b`, `b'`. -/
def srcP (Y : SLay) (b b' : Fin 64) : Prog 64 :=
  ifBit b (ifBit b' (emitU tO 512 0) (nsE 1)) (ifBit b' (sE 1) (emitU tO 512 Y.zero))

/-- A node of level `ℓ`. -/
def nodeP (Y : SLay) (ℓ : ℕ) (loE hiE dE : Prog 64) : Prog 64 :=
  emitU tO 512 Y.x1 ⨾ sE ℓ ⨾ hiE ⨾ emitU tO 512 Y.x2 ⨾ nsE ℓ ⨾ loE ⨾ dE ⨾
    emitU tO 512 Y.x1 ⨾ emitU tO 512 Y.x2

/-- **The tree code** of `m + 2` levels, the root's destination emitted by `dE`. -/
def treeP (Y : SLay) : ℕ → Prog 64 → Prog 64
  | 0, dE => readL tb0 ⨾ readL tb1 ⨾ readL tb2 ⨾ readL tb3 ⨾
      nodeP sE nsE Y 2 (srcP sE nsE Y tb0 tb1) (srcP sE nsE Y tb2 tb3) dE ⨾
      clr tb0 ⨾ clr tb1 ⨾ clr tb2 ⨾ clr tb3
  | m + 1, dE => prim (.cons (tc m) true) ⨾ prim (.cons (tc m) true) ⨾
      loop (tc m) (treeP Y m (ifBlank (tc m) (emitU tO 512 (Y.hi (m + 2)))
        (emitU tO 512 (Y.lo (m + 2))))) ⨾
      nodeP sE nsE Y (m + 3) (emitU tO 512 (Y.lo (m + 2))) (emitU tO 512 (Y.hi (m + 2))) dE

end AdvancedEncryption.DualUse.BpComp
