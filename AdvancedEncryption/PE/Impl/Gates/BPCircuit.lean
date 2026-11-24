import PE.Impl.Gates.BP14
import SigabaNeo.Lib.Lattices.Homomorphic.MuxTree
import SigabaNeo.Lib.Lattices.Homomorphic.Depth

/-!
# The predicate circuit of a branching program

The NAND circuit of a branching program `F` (`PE.BranchingProgram`, 14-bit states, 8-bit
symbols) as a register program on 93 registers (`bpRP F`), whose unfolding is the predicate of the
math layer (`bpPred F`). Each step is one mux tree per output bit (`SigabaNeo.Lattices.MuxTree`) of
22 levels, the leaf `u = 256 z + a` being the bit of the table entry at `(z, a)`.

**Inputs.** Input `8 i + m` is bit `m` (most significant first) of symbol `i` (`inIdx`), as in
`encAttr` (`bitsOfBP_inIdx`).

**Registers** (`Reg = Fin 93`): `ZERO` (`rZERO`), two state banks `Z₀`, `Z₁` of 14 bits
(`rZ b j`; step `i` reads bank `i mod 2` and writes bank `(i + 1) mod 2`), the negated state `NZ`
(`rNZ`), the negated symbol bits `NA` (`rNA`), the children registers `L_ℓ`, `H_ℓ` of the levels
`2 … 21` (`rLo`, `rHi`), and two temporaries. The output is bit `0` of bank `0` after the last
step (`rOUT`).

**Selectors** (`lay i`): levels `1 … 8` select by the bits of symbol `i`, least significant first;
levels `9 … 22` by the bits of the state, least significant first.

**Program** (`bpRP`): `ZERO` and bank `0` cleared (`initRP`, 15 gates); steps `0 … 14`
(`stepRP`): the negations (`negs`, 22 gates), then 14 trees; the last step (`lastRP`): the
negations and one tree of the output table.

Proved for every `F`, without enumerating tables, states or gates:

* `evalBool_bpPred`: the circuit computes `output F x` on the bits of `encAttr x`;
* `depth_bpPred`: its depth is at most `478` (`max (δ + 29) 43` per step);
* `length_bpRP`: it has `633 · 2^21 − 266` instructions;
* `bnd_bpRP`: every slot of an instruction is below `222 = 1 + 128 + 93`.

The values on registers are computed once, for every value type (`run_stepRP`, `run_lastRP`), and
instantiated for Booleans and depths.
-/

namespace AdvancedEncryption.PE.Gates.BPCircuit

open SigabaNeo.Lattices SigabaNeo.Lattices.MuxTree AdvancedEncryption.PE.BranchingProgram

/-! ### Registers, inputs, layout -/

/-- The registers. -/
abbrev Reg := Fin 93

/-- A register program on the attribute bits. -/
abbrev BRP := RP (Fin 128) 93

/-- `ZERO`. -/
def rZERO : Reg := ⟨0, by omega⟩
/-- Bit `j` of the state bank `b mod 2`. -/
def rZ (b j : ℕ) : Reg := ⟨1 + 14 * (b % 2) + j % 14, by omega⟩
/-- Bit `j` of the negated state. -/
def rNZ (j : ℕ) : Reg := ⟨29 + j % 14, by omega⟩
/-- Bit `m` of the negated symbol. -/
def rNA (m : ℕ) : Reg := ⟨43 + m % 8, by omega⟩
/-- The `lo` child of level `ℓ`. -/
def rLo (ℓ : ℕ) : Reg := ⟨51 + (ℓ - 2) % 20, by omega⟩
/-- The `hi` child of level `ℓ`. -/
def rHi (ℓ : ℕ) : Reg := ⟨71 + (ℓ - 2) % 20, by omega⟩
/-- Temporaries. -/
def rX1 : Reg := ⟨91, by omega⟩
/-- Temporaries. -/
def rX2 : Reg := ⟨92, by omega⟩
/-- The output register: bit `0` of the bank after the last step. -/
def rOUT : Reg := rZ 16 0

/-- The input of bit `m` of symbol `i`. -/
def inIdx (i m : ℕ) : Fin 128 := ⟨(8 * i + m) % 128, Nat.mod_lt _ (by omega)⟩

/-- The source of bit `m` of symbol `i`. -/
def inX (i m : ℕ) : Src (Fin 128) 93 := .input (inIdx i m)

/-- The layout of the trees of step `i`. -/
def lay (i : ℕ) : Layout (Fin 128) 93 where
  s ℓ := if ℓ ≤ 8 then inX i (8 - ℓ) else .reg (rZ i (ℓ - 9))
  ns ℓ := if ℓ ≤ 8 then .reg (rNA (8 - ℓ)) else .reg (rNZ (ℓ - 9))
  zero := rZERO
  lo := rLo
  hi := rHi
  x1 := rX1
  x2 := rX2

/-! ### Leaves and the program -/

theorem div_256_lt {u : ℕ} (h : u < 2 ^ 22) : u / 256 < 2 ^ 14 := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  exact lt_of_lt_of_eq h (by norm_num)

/-- The leaves of a table: leaf `u = 256 z + a` is the entry at `(z, a)`. -/
def tblLeaf (f : State → Sym → Bool) (u : ℕ) : Bool :=
  if h : u < 2 ^ 22 then f ⟨u / 256, div_256_lt h⟩ ⟨u % 256, Nat.mod_lt _ (by omega)⟩ else false

/-- The leaves of bit `j` of the transition table of step `i`. -/
def leafStep (F : BP) (i j : ℕ) : ℕ → Bool :=
  tblLeaf fun z a => if h : i < 15 then (F.step ⟨i, h⟩ z a).val.testBit j else false

/-- The leaves of the output table. -/
def leafOut (F : BP) : ℕ → Bool := tblLeaf F.out

/-- `ZERO` and bank `0` cleared: `NAND(1, 1)`. -/
def initRP : BRP :=
  ⟨rZERO, .one, .one⟩ :: (List.range 14).map fun j => ⟨rZ 0 j, .one, .one⟩

/-- The negations of step `i`: the symbol bits, then the state bits. -/
def negs (i : ℕ) : BRP :=
  (List.range 8).map (fun m => ⟨rNA m, inX i m, inX i m⟩) ++
    (List.range 14).map fun j => ⟨rNZ j, .reg (rZ i j), .reg (rZ i j)⟩

/-- The trees of step `i`, one per bit of the next state. -/
def treesRP (F : BP) (i k : ℕ) : BRP :=
  (List.range k).flatMap fun j => tree (lay i) (leafStep F i j) 20 0 (rZ (i + 1) j)

/-- Step `i < 15`. -/
def stepRP (F : BP) (i : ℕ) : BRP := negs i ++ treesRP F i 14

/-- Steps `0 … n − 1`. -/
def stepsRP (F : BP) : ℕ → BRP
  | 0 => []
  | i + 1 => stepsRP F i ++ stepRP F i

/-- The last step: the output table. -/
def lastRP (F : BP) : BRP := negs 15 ++ tree (lay 15) (leafOut F) 20 0 rOUT

/-- **The register program of a branching program.** -/
def bpRP (F : BP) : BRP := initRP ++ stepsRP F 15 ++ lastRP F

/-- **The predicate of a branching program**: the unfolding of `bpRP F` at the output. -/
def bpPred (F : BP) : SLP (Fin 128) × Wire (Fin 128) := RP.pred (bpRP F) rOUT

/-! ### Facts on registers -/

theorem rZ_mod (b j : ℕ) : rZ b (j % 14) = rZ b j := by
  simp [rZ, Nat.mod_mod]

theorem rNZ_mod (j : ℕ) : rNZ (j % 14) = rNZ j := by
  simp [rNZ, Nat.mod_mod]

theorem rZ_ne_succ (i x j : ℕ) : rZ i x ≠ rZ (i + 1) j := by
  simp only [rZ, ne_eq, Fin.mk.injEq]; omega

theorem rZ_lt (b j : ℕ) : (rZ b j).val < 29 := by simp only [rZ]; omega

/-- The registers read by the selectors are below `51` and outside the bank written. -/
theorem sel_reads {i ℓ : ℕ} {r : Reg} (h : (lay i).s ℓ = .reg r ∨ (lay i).ns ℓ = .reg r) :
    r.val < 51 ∧ ∀ j, r ≠ rZ (i + 1) j := by
  simp only [lay] at h
  rcases h with h | h <;> split_ifs at h with hl
  · cases h
  · cases h; exact ⟨by simp only [rZ]; omega, fun j => rZ_ne_succ _ _ _⟩
  · cases h
    refine ⟨by simp only [rNA]; omega, fun j e => ?_⟩
    simp only [rNA, rZ, Fin.mk.injEq] at e; omega
  · cases h
    refine ⟨by simp only [rNZ]; omega, fun j e => ?_⟩
    simp only [rNZ, rZ, Fin.mk.injEq] at e; omega

theorem notWr {i j : ℕ} {r : Reg} (h : r.val < 51) (hne : r ≠ rZ (i + 1) j) :
    ¬ Wr (lay i) 20 (rZ (i + 1) j) r := by
  simp only [Wr, lay]
  rintro (e | e | e | ⟨ℓ, -, -, e | e⟩)
  · subst e; simp [rX1] at h
  · subst e; simp [rX2] at h
  · exact hne e
  · subst e; simp only [rLo] at h; omega
  · subst e; simp only [rHi] at h; omega

theorem good_lay (i j : ℕ) : Good (lay i) 20 (rZ (i + 1) j) where
  x12 := by simp [lay, rX1, rX2]
  lohi ℓ ℓ' h1 h2 h3 h4 := by
    simp only [lay, rLo, rHi, ne_eq, Fin.mk.injEq]; omega
  lox ℓ h1 h2 := by
    simp only [lay, rLo, rHi, rX1, rX2, ne_eq, Fin.mk.injEq]; omega
  dstx := by simp only [lay, rZ, rX1, rX2, ne_eq, Fin.mk.injEq]; omega
  dstl ℓ h1 h2 := by simp only [lay, rZ, rLo, rHi, ne_eq, Fin.mk.injEq]; omega
  sel ℓ _ _ r hr := by
    refine ⟨fun e => ?_, fun e => ?_⟩
    · obtain ⟨h1, h2⟩ := sel_reads (Or.inl e)
      exact notWr h1 (h2 j) hr
    · obtain ⟨h1, h2⟩ := sel_reads (Or.inr e)
      exact notWr h1 (h2 j) hr
  zero := notWr (by simp [lay, rZERO]) (by simp only [lay, rZERO, rZ, ne_eq, Fin.mk.injEq]; omega)

/-! ### Values on any type -/

section Generic

variable {α : Type*} (inp : Fin 128 → α) (one : α) (step : α → α → α)

/-- The value of the selector of level `ℓ` of step `i` before the step. -/
def svOf (R : Reg → α) (i ℓ : ℕ) : α :=
  if ℓ ≤ 8 then inp (inIdx i (8 - ℓ)) else R (rZ i (ℓ - 9))

/-- The value of its negation. -/
def nsvOf (R : Reg → α) (i ℓ : ℕ) : α :=
  if ℓ ≤ 8 then step (inp (inIdx i (8 - ℓ))) (inp (inIdx i (8 - ℓ)))
  else step (R (rZ i (ℓ - 9))) (R (rZ i (ℓ - 9)))

theorem run_initRP (R : Reg → α) :
    RP.run inp one step initRP R rZERO = step one one ∧
      ∀ j, j < 14 → RP.run inp one step initRP R (rZ 0 j) = step one one := by
  have hm := RP.run_map_dup inp one step (fun j => rZ 0 j) (fun _ => .one) (fun _ => False)
    (fun _ _ h => by cases h) 14 (fun _ _ h => h)
    (fun m m' h1 h2 e => by simp only [rZ, Fin.ext_iff] at e; omega)
    (Function.update R rZERO (step one one))
  simp only [initRP, RP.run_cons, Src.val]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hm.2 _ (fun m _ e => by simp only [rZ, rZERO, Fin.ext_iff] at e; omega),
      Function.update_self]
  · exact hm.1 j hj

theorem run_negs (i : ℕ) (R : Reg → α) :
    (∀ m, m < 8 → RP.run inp one step (negs i) R (rNA m) =
        step (inp (inIdx i m)) (inp (inIdx i m))) ∧
      (∀ j, RP.run inp one step (negs i) R (rNZ j) = step (R (rZ i j)) (R (rZ i j))) ∧
      ∀ r : Reg, r.val < 29 → RP.run inp one step (negs i) R r = R r := by
  have h1 := RP.run_map_dup inp one step rNA (inX i) (fun _ => False) (fun _ _ h => by cases h) 8
    (fun _ _ h => h) (fun m m' h1 h2 e => by simp only [rNA, Fin.mk.injEq] at e; omega) R
  set R1 := RP.run inp one step ((List.range 8).map fun m => (⟨rNA m, inX i m, inX i m⟩ :
    Instr (Fin 128) 93)) R
  have h2 := RP.run_map_dup inp one step rNZ (fun j => .reg (rZ i j)) (fun r => r.val < 29)
    (fun m r h => by cases h; exact rZ_lt _ _) 14 (fun m _ h => by simp only [rNZ] at h; omega)
    (fun m m' h1 h2 e => by simp only [rNZ, Fin.mk.injEq] at e; omega) R1
  have hR1 : ∀ r : Reg, r.val < 29 → R1 r = R r := fun r hr =>
    h1.2 r (fun m _ e => by subst e; simp only [rNA] at hr; omega)
  simp only [negs, RP.run_append]
  refine ⟨fun m hm => ?_, fun j => ?_, fun r hr => ?_⟩
  · rw [h2.2 _ (fun j _ e => by simp only [rNZ, rNA, Fin.mk.injEq] at e; omega), h1.1 m hm]
    rfl
  · rw [← rNZ_mod, h2.1 _ (Nat.mod_lt _ (by omega))]
    simp only [Src.val]
    rw [hR1 _ (rZ_lt _ _), rZ_mod]
  · rw [h2.2 _ (fun j _ e => by subst e; simp only [rNZ] at hr; omega), hR1 r hr]

/-- The trees of step `i` on the registers `R'` after the negations. -/
theorem run_treesRP (F : BP) (i : ℕ) (R' : Reg → α) (k : ℕ) (hk : k ≤ 14) :
    (∀ j, j < k → RP.run inp one step (treesRP F i k) R' (rZ (i + 1) j) =
        muxVal (leafStep F i j) one step (fun ℓ => ((lay i).s ℓ).val inp one R')
          (fun ℓ => ((lay i).ns ℓ).val inp one R') (R' rZERO) 21 0) ∧
      ∀ r : Reg, r.val < 51 → (∀ j, j < k → r ≠ rZ (i + 1) j) →
        RP.run inp one step (treesRP F i k) R' r = R' r := by
  induction k with
  | zero => exact ⟨fun j h => absurd h (Nat.not_lt_zero _), fun r _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hsplit : treesRP F i (k + 1) =
        treesRP F i k ++ tree (lay i) (leafStep F i k) 20 0 (rZ (i + 1) k) := by
      simp [treesRP, List.range_succ, List.flatMap_append]
    set Rk := RP.run inp one step (treesRP F i k) R'
    have hsel : ∀ ℓ, ((lay i).s ℓ).val inp one Rk = ((lay i).s ℓ).val inp one R' ∧
        ((lay i).ns ℓ).val inp one Rk = ((lay i).ns ℓ).val inp one R' := fun ℓ =>
      ⟨Src.val_eq_of _ (fun r e => by
          obtain ⟨h1, h2⟩ := sel_reads (Or.inl e); exact ih2 r h1 (fun j _ => h2 j)),
        Src.val_eq_of _ (fun r e => by
          obtain ⟨h1, h2⟩ := sel_reads (Or.inr e); exact ih2 r h1 (fun j _ => h2 j))⟩
    have hz : Rk rZERO = R' rZERO :=
      ih2 _ (by simp [rZERO]) (fun j _ => by simp only [rZERO, rZ, ne_eq, Fin.mk.injEq]; omega)
    obtain ⟨t1, t2⟩ := run_tree (lay i) (leafStep F i k) inp one step 20 0 (rZ (i + 1) k) Rk
      (fun ℓ => ((lay i).s ℓ).val inp one R') (fun ℓ => ((lay i).ns ℓ).val inp one R') (R' rZERO)
      (good_lay i k) (fun ℓ _ _ => hsel ℓ) hz
    rw [hsplit, RP.run_append]
    refine ⟨fun j hj => ?_, fun r hr hne => ?_⟩
    · by_cases e : j = k
      · subst e; exact t1
      · have hne : rZ (i + 1) j ≠ rZ (i + 1) k := by
          simp only [rZ, ne_eq, Fin.mk.injEq]; omega
        rw [t2 _ (notWr (rZ_lt _ _ |>.trans (by omega)) hne), ih1 j (by omega)]
    · rw [t2 r (notWr hr (hne k (by omega))), ih2 r hr (fun j hj => hne j (by omega))]

/-- The selectors after the negations of step `i` are those of `svOf`, `nsvOf` at the levels
`1 … 22`. -/
theorem sel_after_negs (i : ℕ) (R : Reg → α) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 22) :
    ((lay i).s ℓ).val inp one (RP.run inp one step (negs i) R) = svOf inp R i ℓ ∧
      ((lay i).ns ℓ).val inp one (RP.run inp one step (negs i) R) = nsvOf inp step R i ℓ := by
  obtain ⟨n1, n2, n3⟩ := run_negs inp one step i R
  simp only [lay, svOf, nsvOf]
  split_ifs with hl
  · exact ⟨rfl, n1 _ (by omega)⟩
  · exact ⟨n3 _ (rZ_lt _ _), n2 _⟩

/-- **One step `i`**: `ZERO` is kept and bit `j` of the next bank is the tree of bit `j`. -/
theorem run_stepRP (F : BP) (i : ℕ) (R : Reg → α) :
    RP.run inp one step (stepRP F i) R rZERO = R rZERO ∧
      ∀ j, j < 14 → RP.run inp one step (stepRP F i) R (rZ (i + 1) j) =
        muxVal (leafStep F i j) one step (svOf inp R i) (nsvOf inp step R i) (R rZERO) 21 0 := by
  obtain ⟨_, _, n3⟩ := run_negs inp one step i R
  obtain ⟨t1, t2⟩ := run_treesRP inp one step F i (RP.run inp one step (negs i) R) 14 le_rfl
  simp only [stepRP, RP.run_append]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [t2 _ (by simp [rZERO]) (fun j _ => by simp only [rZERO, rZ, ne_eq, Fin.mk.injEq]; omega),
      n3 _ (by simp [rZERO])]
  · rw [t1 j hj, n3 _ (by simp [rZERO])]
    exact muxVal_congr _ _ _ _ _ _ _ _ _ (fun ℓ h1 h2 => sel_after_negs inp one step i R ℓ h1 h2) _

/-- **The last step**: the output register is the tree of the output table. -/
theorem run_lastRP (F : BP) (R : Reg → α) :
    RP.run inp one step (lastRP F) R rOUT =
      muxVal (leafOut F) one step (svOf inp R 15) (nsvOf inp step R 15) (R rZERO) 21 0 := by
  obtain ⟨_, _, n3⟩ := run_negs inp one step 15 R
  obtain ⟨t1, _⟩ := run_tree (lay 15) (leafOut F) inp one step 20 0 (rZ (15 + 1) 0)
    (RP.run inp one step (negs 15) R)
    (fun ℓ => ((lay 15).s ℓ).val inp one (RP.run inp one step (negs 15) R))
    (fun ℓ => ((lay 15).ns ℓ).val inp one (RP.run inp one step (negs 15) R))
    (RP.run inp one step (negs 15) R rZERO) (good_lay 15 0) (fun ℓ _ _ => ⟨rfl, rfl⟩) rfl
  simp only [lastRP, RP.run_append]
  rw [show rOUT = rZ (15 + 1) 0 from rfl, t1, n3 _ (by simp [rZERO])]
  exact muxVal_congr _ _ _ _ _ _ _ _ _ (fun ℓ h1 h2 => sel_after_negs inp one step 15 R ℓ h1 h2) _

end Generic

/-! ### The Boolean value -/

/-- The 128 bits of an attribute, as the inputs of the circuit. -/
def bitsOfBP (x : Attr) (k : Fin 128) : Bool := (encAttr x).getD k false

theorem encAttr_eq_ofFn (x : Attr) :
    encAttr x = List.ofFn (fun k : Fin (16 * 8) =>
      (x ⟨k.val / 8, by omega⟩).val.testBit (7 - k.val % 8)) := by
  rw [List.ofFn_mul]
  show (List.ofFn x).flatMap symBits = _
  rw [List.flatMap_def, List.map_ofFn]
  congr 1

theorem bitsOfBP_inIdx (x : Attr) {i m : ℕ} (hi : i < 16) (hm : m < 8) :
    bitsOfBP x (inIdx i m) = (x ⟨i, hi⟩).val.testBit (7 - m) := by
  have hv : (inIdx i m).val = 8 * i + m := by simp only [inIdx]; omega
  unfold bitsOfBP
  rw [encAttr_eq_ofFn, hv, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega), List.getElem_ofFn]
  have e1 : (8 * i + m) / 8 = i := by omega
  have e2 : (8 * i + m) % 8 = m := by omega
  simp only [e1, e2]

/-- The state after `i` steps. -/
def zs (F : BP) (x : Attr) : ℕ → State
  | 0 => 0
  | i + 1 => if h : i < 15 then F.step ⟨i, h⟩ (zs F x i) (x ⟨i, by omega⟩) else zs F x i

theorem foldl_eq_zs (F : BP) (x : Attr) :
    ∀ n (hn : n ≤ 15), Fin.foldl n (fun z (i : Fin n) =>
      F.step ⟨i.val, by omega⟩ z (x ⟨i.val, by omega⟩)) 0 = zs F x n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [Fin.foldl_succ_last]
    have := foldl_eq_zs F x n (by omega)
    simp only [Fin.val_castSucc, Fin.val_last] at this ⊢
    rw [this]
    simp [zs, show n < 15 by omega]

theorem run_eq_zs (F : BP) (x : Attr) : run F x = zs F x 15 :=
  foldl_eq_zs F x 15 le_rfl

/-- The leaf index of step `i`: `256 z + a`. -/
theorem leaf_index (z a : ℕ) (ha : a < 256) (ℓ : ℕ) (h1 : 1 ≤ ℓ) :
    (256 * z + a).testBit (ℓ - 1) = if ℓ ≤ 8 then a.testBit (ℓ - 1) else z.testBit (ℓ - 9) := by
  rw [show 256 * z + a = 2 ^ 8 * z + a by norm_num, Nat.testBit_two_pow_mul_add _ (by omega)]
  split_ifs with h h' h' <;> first | rfl | omega

/-- The Boolean selectors of step `i` are the bits of `256 z_i + x_i`. -/
theorem sel_bool (x : Attr) (R : Reg → Bool) (i : ℕ) (hi : i < 16) (z : ℕ)
    (hR : ∀ j, j < 14 → R (rZ i j) = z.testBit j) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 22) :
    svOf (bitsOfBP x) R i ℓ = (256 * z + (x ⟨i, hi⟩).val).testBit (ℓ - 1) ∧
      nsvOf (bitsOfBP x) (fun a b => !(a && b)) R i ℓ =
        !(256 * z + (x ⟨i, hi⟩).val).testBit (ℓ - 1) := by
  rw [leaf_index _ _ (x ⟨i, hi⟩).isLt ℓ h1]
  simp only [svOf, nsvOf, Bool.and_self]
  split_ifs with hl
  · rw [bitsOfBP_inIdx x hi (by omega), show 7 - (8 - ℓ) = ℓ - 1 by omega]
    exact ⟨rfl, rfl⟩
  · rw [hR _ (by omega)]; exact ⟨rfl, rfl⟩

theorem tblLeaf_eq (f : State → Sym → Bool) (z : State) (a : Sym) :
    tblLeaf f (0 + (256 * z.val + a.val) % 2 ^ 22) = f z a := by
  have hz := z.isLt
  have ha := a.isLt
  have hlt : 256 * z.val + a.val < 2 ^ 22 := by
    have : (2 : ℕ) ^ 22 = 256 * 2 ^ 14 := by norm_num
    omega
  rw [zero_add, Nat.mod_eq_of_lt hlt]
  unfold tblLeaf
  rw [dite_cond_eq_true (eq_true hlt)]
  congr 1 <;> ext <;> simp <;> omega

theorem muxVal_step_bool (F : BP) (x : Attr) (R : Reg → Bool) (i : ℕ) (hi : i < 16)
    (z : State) (hR : ∀ j, j < 14 → R (rZ i j) = z.val.testBit j) (f : State → Sym → Bool) :
    muxVal (tblLeaf f) true (fun a b => !(a && b)) (svOf (bitsOfBP x) R i)
      (nsvOf (bitsOfBP x) (fun a b => !(a && b)) R i) false 21 0 = f z (x ⟨i, hi⟩) := by
  set v := 256 * z.val + (x ⟨i, hi⟩).val
  rw [muxVal_congr _ _ _ _ _ (fun ℓ => v.testBit (ℓ - 1)) (fun ℓ => !v.testBit (ℓ - 1)) _ _
      (fun ℓ h1 h2 => sel_bool x R i hi z.val hR ℓ h1 h2),
    muxVal_bool _ (fun ℓ => v.testBit (ℓ - 1)), idx_testBit]
  exact tblLeaf_eq f z (x ⟨i, hi⟩)

/-- The invariant of the Boolean run: `ZERO` is `0` and bank `i` holds `z_i`. -/
def BInv (F : BP) (x : Attr) (i : ℕ) (R : Reg → Bool) : Prop :=
  R rZERO = false ∧ ∀ j, j < 14 → R (rZ i j) = (zs F x i).val.testBit j

theorem bInv_stepsRP (F : BP) (x : Attr) :
    ∀ n, n ≤ 15 → BInv F x n
      (RP.run (bitsOfBP x) true (fun a b => !(a && b)) (initRP ++ stepsRP F n) (fun _ => true))
  | 0, _ => by
    obtain ⟨h1, h2⟩ := run_initRP (bitsOfBP x) true (fun a b => !(a && b)) (fun _ => true)
    refine ⟨by simpa [stepsRP] using h1, fun j hj => ?_⟩
    simp only [stepsRP, List.append_nil]
    rw [h2 j hj]
    simp [zs]
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := bInv_stepsRP F x n (by omega)
    rw [stepsRP, ← List.append_assoc, RP.run_append]
    obtain ⟨s1, s2⟩ := run_stepRP (bitsOfBP x) true (fun a b => !(a && b)) F n
      (RP.run (bitsOfBP x) true (fun a b => !(a && b)) (initRP ++ stepsRP F n) (fun _ => true))
    refine ⟨s1.trans h1, fun j hj => ?_⟩
    rw [s2 j hj, h1]
    unfold leafStep
    rw [muxVal_step_bool F x _ n (by omega) (zs F x n) h2]
    simp [zs, show n < 15 by omega]

/-- **The circuit computes the branching program.** -/
theorem evalBool_bpPred (F : BP) (x : Attr) :
    SLP.evalBool (bitsOfBP x) (bpPred F).1 (bpPred F).2 = output F x := by
  show SLP.valueOf _ _ _ _ _ = _
  rw [bpPred, RP.valueOf_pred, bpRP, RP.run_append]
  obtain ⟨h1, h2⟩ := bInv_stepsRP F x 15 le_rfl
  rw [run_lastRP, h1, output, run_eq_zs]
  unfold leafOut
  exact muxVal_step_bool F x _ 15 (by omega) (zs F x 15) h2 F.out

/-! ### The depth -/

/-- The depth bound of a tree of step `i` from a state of depth at most `δ`. -/
theorem depthBound_le (δ : ℕ) :
    ∀ j, depthBound (fun ℓ => if ℓ ≤ 8 then 1 else δ + 1) 1 j ≤ max (δ + 2 * j - 13) (2 * j + 1)
  | 0 => by simp [depthBound]
  | j + 1 => by
    have := depthBound_le δ j
    simp only [depthBound]
    split_ifs <;> omega

theorem muxVal_step_depth (R : Reg → ℕ) (i δ : ℕ) (hR : ∀ j, j < 14 → R (rZ i j) ≤ δ)
    (hz : R rZERO ≤ 1) (leaf : ℕ → Bool) :
    muxVal leaf 0 (fun a b => max a b + 1) (svOf (fun _ => 0) R i)
      (nsvOf (fun _ => 0) (fun a b => max a b + 1) R i) (R rZERO) 21 0 ≤ max (δ + 29) 43 := by
  refine (muxVal_depth leaf _ _ _ (fun ℓ => if ℓ ≤ 8 then 1 else δ + 1) 1 21
    (fun ℓ h1 h2 => ?_) hz (by simp) 0).trans ?_
  · simp only [svOf, nsvOf]
    split_ifs with hl
    · omega
    · have := hR (ℓ - 9) (by omega); omega
  · have := depthBound_le δ 21; omega

theorem depth_stepsRP (F : BP) :
    ∀ n, n ≤ 15 →
      RP.run (fun _ => 0) 0 (fun a b => max a b + 1) (initRP ++ stepsRP F n) (fun _ => 0) rZERO ≤ 1 ∧
      ∀ j, j < 14 → RP.run (fun _ => 0) 0 (fun a b => max a b + 1) (initRP ++ stepsRP F n)
        (fun _ => 0) (rZ n j) ≤ 14 + 29 * n
  | 0, _ => by
    obtain ⟨h1, h2⟩ := run_initRP (fun _ => (0 : ℕ)) 0 (fun a b => max a b + 1) (fun _ => 0)
    simp only [stepsRP, List.append_nil]
    exact ⟨by rw [h1]; simp, fun j hj => by rw [h2 j hj]; simp⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := depth_stepsRP F n (by omega)
    rw [stepsRP, ← List.append_assoc, RP.run_append]
    obtain ⟨s1, s2⟩ := run_stepRP (fun _ => (0 : ℕ)) 0 (fun a b => max a b + 1) F n
      (RP.run (fun _ => 0) 0 (fun a b => max a b + 1) (initRP ++ stepsRP F n) (fun _ => 0))
    refine ⟨s1.trans_le h1, fun j hj => ?_⟩
    rw [s2 j hj]
    have := muxVal_step_depth _ n _ h2 h1 (leafStep F n j)
    omega

/-- **The depth of the circuit is at most `478`.** -/
theorem depth_bpPred (F : BP) : SLP.depth (bpPred F).1 (bpPred F).2 ≤ 478 := by
  show SLP.valueOf _ _ _ _ _ ≤ _
  rw [bpPred, RP.valueOf_pred, bpRP, RP.run_append]
  obtain ⟨h1, h2⟩ := depth_stepsRP F 15 le_rfl
  rw [run_lastRP]
  have := muxVal_step_depth _ 15 _ h2 h1 (leafOut F)
  omega

/-! ### Length and slots -/

/-- The number of gates of a tree of 22 levels. -/
abbrev treeLen : ℕ := 3 * (2 ^ 21 - 1)

theorem length_treesRP (F : BP) (i : ℕ) : ∀ k, (treesRP F i k).length = k * treeLen
  | 0 => rfl
  | k + 1 => by
    have hsplit : treesRP F i (k + 1) =
        treesRP F i k ++ tree (lay i) (leafStep F i k) 20 0 (rZ (i + 1) k) := by
      simp [treesRP, List.range_succ, List.flatMap_append]
    rw [hsplit, List.length_append, length_treesRP F i k, length_tree]
    ring

theorem length_negs (i : ℕ) : (negs i).length = 22 := by simp [negs]

theorem length_stepsRP (F : BP) : ∀ n, (stepsRP F n).length = n * (22 + 14 * treeLen)
  | 0 => rfl
  | n + 1 => by
    rw [stepsRP, List.length_append, length_stepsRP F n, stepRP, List.length_append, length_negs,
      length_treesRP]
    ring

/-- **The number of instructions**: `633 · 2^21 − 266`, for every program. -/
theorem length_bpRP (F : BP) : (bpRP F).length = 633 * 2 ^ 21 - 266 := by
  rw [bpRP, List.length_append, List.length_append, length_stepsRP, lastRP, List.length_append,
    length_negs, length_tree]
  simp only [initRP, List.length_cons, List.length_map, List.length_range]
  norm_num

/-- **Every slot is below `222`**: the constant, 128 inputs and 93 registers. -/
theorem bnd_bpRP (F : BP) : ∀ ins ∈ bpRP F,
    RP.regSlot 128 ins.dst < 222 ∧ ins.a.slot < 222 ∧ ins.b.slot < 222 := fun ins _ =>
  ⟨by simp only [RP.regSlot]; omega, Src.slot_lt ins.a, Src.slot_lt ins.b⟩

end AdvancedEncryption.PE.Gates.BPCircuit

