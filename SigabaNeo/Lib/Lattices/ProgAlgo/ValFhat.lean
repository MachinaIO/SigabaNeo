import SigabaNeo.Lib.Lattices.ProgAlgo.ValGates
import SigabaNeo.Lib.Lattices.Algo.FhatShadow
import SigabaNeo.Lib.Machines.GatesSLP

/-!
# The output bundle of `f̂` on the word machine

* `bw`, `ubw`: a bundle as a word (its values in the order of `BI`) and back;
* `blockSpec_nandC`: the NAND block `nandC` is a block of the gate loop on slots of `|BI| V` bits,
  with `F = nandW` (`nandV` on the bundles of the two words); `blockSpec_gate`: the single `gate`
  is a block on slots of `V` bits with `F = fV V f`;
* **`gl_nandW`**: the results of the gate loop with `nandW` are the words of the bundles of the
  blocks of `f̂` (`compileStepV`), so its last result is the word of `fhatV` at the predicate's
  output wire (`getLast_gl_nandW`);
* **`fhatV_fV`** (shadows over `fV` equal shadows over the step on `V`-bit values).
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo SigabaNeo.Encode

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-! ### Words of bundles -/

/-- The index of a bundle position. -/
def biIx {N k : ℕ} (b : BI N k) : ℕ := (Enum.list (α := BI N k)).idxOf b

/-- The bundle of a word: the value at `b` is the block of `V` bits at its index. -/
def ubw {N k : ℕ} (V : ℕ) (x : List Bool) : BI N k → List Bool := fun b =>
  (x.drop (biIx b * V)).take V

theorem biIx_lt {N k : ℕ} (b : BI N k) : biIx b < (Enum.list (α := BI N k)).length :=
  List.idxOf_lt_length_of_mem (Enum.complete b)

theorem getElem_biIx {N k : ℕ} (b : BI N k) :
    (Enum.list (α := BI N k))[biIx b]'(biIx_lt b) = b := List.getElem_idxOf _

theorem biIx_getElem {N k : ℕ} (i : ℕ) (h : i < (Enum.list (α := BI N k)).length) :
    biIx ((Enum.list (α := BI N k))[i]) = i :=
  List.Nodup.idxOf_getElem Enum.nodup i h

theorem length_bw {N k : ℕ} {A : BI N k → List Bool} (hA : ∀ b, (A b).length = V) :
    (bw A).length = (Enum.list (α := BI N k)).length * V := by
  rw [bw, length_flatten_of (fun x hx => by
    simp only [List.mem_map] at hx; obtain ⟨b, -, rfl⟩ := hx; exact hA b), List.length_map]

theorem ubw_bw {N k : ℕ} {A : BI N k → List Bool} (hA : ∀ b, (A b).length = V) :
    ubw V (bw A) = A := by
  funext b
  have hu : UV V ((Enum.list (α := BI N k)).map A) := fun x hx => by
    simp only [List.mem_map] at hx; obtain ⟨b, -, rfl⟩ := hx; exact hA b
  have hl : biIx b < ((Enum.list (α := BI N k)).map A).length := by simpa using biIx_lt b
  rw [ubw, bw, drop_flatten_uv hu, flatten_drop_cons hl, List.take_left' (hu _ (List.getElem_mem _))]
  simp [getElem_biIx]

theorem bw_ubw {N k : ℕ} {x : List Bool} (hx : x.length = (Enum.list (α := BI N k)).length * V) :
    bw (ubw (N := N) (k := k) V x) = x := by
  set L := Enum.list (α := BI N k)
  have key : ∀ (i : ℕ), i ≤ L.length → ((L.drop i).map (ubw V x)).flatten = x.drop (i * V) := by
    intro i hi
    induction h : L.length - i generalizing i with
    | zero =>
      have : i = L.length := by omega
      subst this
      rw [List.drop_length, List.map_nil, List.flatten_nil, ← hx, List.drop_length]
    | succ n ih =>
      have hlt : i < L.length := by omega
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.flatten_cons, ih (i + 1) (by omega)
        (by omega), ubw, biIx_getElem i hlt, Nat.succ_mul, ← List.drop_drop]
      exact List.take_append_drop V _
  have := key 0 (Nat.zero_le _)
  simpa [bw] using this

/-! ### The two blocks -/

/-- The NAND on bundle words. -/
def nandW (V N K : ℕ) (f : List Bool → List Bool → List Bool) (one zv : List Bool)
    (x y : List Bool) : List Bool :=
  bw (nandV one (fV V f) (enumT N (K + 1)) (enumO N (K + 1)) (gvExp (2 ^ K)) zv (2 ^ K)
    (ubw (N := N) (k := K + 1) V x) (ubw V y))

theorem nctxW_lt : ∀ j ∈ nctxW, j.val < 100 ∧ j ≠ IA ∧ j ≠ IB ∧ j ≠ RES := by decide

theorem wr_nandC_lt : ∀ j ∈ wr nandC, j.val < 100 := by decide +kernel

theorem ubw_len {N k : ℕ} (x : List Bool)
    (hx : x.length = (Enum.list (α := BI N k)).length * V) (b : BI N k) :
    (ubw (N := N) (k := k) V x b).length = V := by
  have h := biIx_lt b
  rw [ubw, List.length_take, List.length_drop, hx]
  have : (biIx b + 1) * V ≤ (Enum.list (α := BI N k)).length * V := Nat.mul_le_mul_right _ h
  rw [Nat.succ_mul] at this; omega

/-- **The NAND block is a block of the gate loop.** -/
theorem blockSpec_nandC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {N K : ℕ} (hN : 0 < N) (one zv : List Bool) (h1 : one.length = V) (hz : zv.length = V) :
    BlockSpec V f nandC ((Enum.list (α := BI N (K + 1))).length * V) (nandW V N K f one zv)
      (NCtx V K N one zv) where
  run w ctx hA hB hR := by
    have hA' := ubw_len (w IA) hA
    have hB' := ubw_len (w IB) hB
    obtain ⟨r, -, -⟩ := exec_nandC (V := V) (f := f) hf hN (ubw V (w IA)) (ubw V (w IB)) hA' hB'
      w ctx (bw_ubw hA).symm (bw_ubw hB).symm
    rw [r, nandW, List.drop_left' (by rw [hR, length_bw (nandV_len hf h1 hz _ _ hA' hB')])]
  len x y hx hy := by
    rw [nandW, length_bw (nandV_len hf h1 hz _ _ (ubw_len x hx) (ubw_len y hy))]
  ctx w ctx := ctx.exec _ (by decide +kernel)
  frame w w' ctx h := ctx.of_eq fun j hj => h j (nctxW_lt j hj).1 (nctxW_lt j hj).2.1
    (nctxW_lt j hj).2.2.1 (nctxW_lt j hj).2.2.2
  wr := wr_nandC_lt

/-- **A single gate is a block of the gate loop.** -/
theorem blockSpec_gate (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) :
    BlockSpec V f (.gate RES IA IB) V (fV V f) (fun _ => True) where
  run w _ _ _ _ := by simp [exec, fV]
  len a b _ _ := by rw [fV]; exact hf _ _ (by simp) (by simp)
  ctx _ _ := trivial
  frame _ _ _ _ := trivial
  wr := by decide

/-! ### The results of the gate loop are the bundles of `f̂` -/

section Fhat

variable {N K : ℕ} (one zv : List Bool) (inB : Fin 10 → BI N (K + 1) → List Bool)

/-- The slot of the operand `j` is the word of the bundle of the wire `ofIdx 10 j`. -/
theorem slotOf_rep (gv : OI N (K + 1) → ℕ) (bs : List (BI N (K + 1) → List Bool)) (j : ℕ) :
    slotOf (bw (constRepVV one zv gv)) ((List.finRange 10).map fun i => bw (inB i)) (bs.map bw) j =
      bw (repV one inB zv gv bs (ofIdx 10 j)) := by
  unfold slotOf ofIdx
  by_cases h0 : j = 0
  · subst h0; simp [repV]
  · by_cases h1 : j - 1 < 10
    · rw [if_neg h0, dif_pos h1, repV]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [List.cons_append, List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa using h1)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_getElem (by simpa using h1)]
      simp
    · rw [if_neg h0, dif_neg h1, repV]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 11 := ⟨j - 11, by omega⟩
      rw [show j' + 11 = (j' + 10) + 1 by omega, List.cons_append, List.getD_cons_succ,
        List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_finRange,
        show j' + 10 - 10 = j' by omega, show j' + 10 + 1 - 1 - 10 = j' by omega, List.getD_map]

theorem constRepVV_len (h1 : one.length = V) (hz : zv.length = V) (gv : OI N (K + 1) → ℕ)
    (b : BI N (K + 1)) : (constRepVV one zv gv b).length = V := by
  unfold constRepVV
  rw [List.getD_eq_getElem?_getD]
  rcases e : (constV one zv (K + 1) (gv (b.1, b.2.1, b.2.2.2)))[b.2.2.1.val]? with _ | x
  · simpa using h1
  · exact constV_vals h1 hz _ _ x (List.mem_of_getElem? e)

theorem repV_len (_hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    (h1 : one.length = V) (hz : zv.length = V) (hin : ∀ i b, (inB i b).length = V)
    (gv : OI N (K + 1) → ℕ) (bs : List (BI N (K + 1) → List Bool))
    (hbs : ∀ A ∈ bs, ∀ b, (A b).length = V) (w : Wire (Fin 10)) (b : BI N (K + 1)) :
    (repV one inB zv gv bs w b).length = V := by
  cases w with
  | input i => exact hin i b
  | one => exact constRepVV_len one zv h1 hz gv b
  | gate m =>
    simp only [repV]
    rw [List.getD_eq_getElem?_getD]
    rcases e : bs[m]? with _ | A
    · exact constRepVV_len one zv h1 hz gv b
    · exact hbs A (List.mem_of_getElem? e) b

/-- **The results of the gate loop with `nandW`** are the words of the bundles of the NAND blocks
of `f̂` (`compileStepV`, at the orders `enumT`, `enumO` and the coefficients `gvExp q`). -/
theorem gl_nandW (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    (h1 : one.length = V) (hz : zv.length = V) (hin : ∀ i b, (inB i b).length = V)
    (gs : GateList) :
    gl (nandW V N K f one zv) (bw (N := N) (k := K + 1) (constRepVV one zv (gvExp (2 ^ K))))
        ((List.finRange 10).map fun i => bw (inB i)) gs =
      ((fromGates 10 gs).foldl (compileStepV one (fV V f) (enumT N (K + 1)) (enumO N (K + 1))
        (gvExp (2 ^ K)) inB zv (2 ^ K)) []).map bw := by
  have key : ∀ (gs : GateList) (bs : List (BI N (K + 1) → List Bool)),
      (∀ A ∈ bs, ∀ b, (A b).length = V) →
      gs.foldl (glStep (nandW V N K f one zv) (bw (N := N) (k := K + 1) (constRepVV one zv (gvExp (2 ^ K))))
          ((List.finRange 10).map fun i => bw (inB i))) (bs.map bw) =
        ((fromGates 10 gs).foldl (compileStepV one (fV V f) (enumT N (K + 1)) (enumO N (K + 1))
          (gvExp (2 ^ K)) inB zv (2 ^ K)) bs).map bw ∧
        ∀ A ∈ (fromGates 10 gs).foldl (compileStepV one (fV V f) (enumT N (K + 1))
          (enumO N (K + 1)) (gvExp (2 ^ K)) inB zv (2 ^ K)) bs, ∀ b, (A b).length = V := by
    intro gs
    induction gs with
    | nil => intro bs h; exact ⟨rfl, h⟩
    | cons g gs ih =>
      intro bs hbs
      have hg : glStep (nandW V N K f one zv) (bw (N := N) (k := K + 1) (constRepVV one zv (gvExp (2 ^ K))))
          ((List.finRange 10).map fun i => bw (inB i)) (bs.map bw) g =
          (compileStepV one (fV V f) (enumT N (K + 1)) (enumO N (K + 1)) (gvExp (2 ^ K)) inB zv
            (2 ^ K) bs ⟨ofIdx 10 g.1, ofIdx 10 g.2⟩).map bw := by
        rw [glStep, slotOf_rep, slotOf_rep, compileStepV, List.map_append, List.map_singleton,
          nandW, ubw_bw (repV_len one zv inB hf h1 hz hin _ bs hbs _),
          ubw_bw (repV_len one zv inB hf h1 hz hin _ bs hbs _)]
      have hbs' : ∀ A ∈ compileStepV one (fV V f) (enumT N (K + 1)) (enumO N (K + 1))
          (gvExp (2 ^ K)) inB zv (2 ^ K) bs ⟨ofIdx 10 g.1, ofIdx 10 g.2⟩, ∀ b, (A b).length = V := by
        intro A hA b
        rw [compileStepV, List.mem_append, List.mem_singleton] at hA
        rcases hA with hA | rfl
        · exact hbs A hA b
        · exact nandV_len hf h1 hz _ _ (repV_len one zv inB hf h1 hz hin _ bs hbs _)
            (repV_len one zv inB hf h1 hz hin _ bs hbs _) b
      rw [List.foldl_cons, hg]
      exact ih _ hbs'
  exact (key gs [] (fun _ h => by simp at h)).1

theorem length_foldl_compileStepV (gv : OI N (K + 1) → ℕ) (step : List Bool → List Bool → List Bool)
    (ordT : List ((Fin 2 × Fin (K + 1)) × Fin N)) (ordO : List (OI N (K + 1))) (q : ℕ) :
    ∀ (p : SLP (Fin 10)) (bs : List (BI N (K + 1) → List Bool)),
      (p.foldl (compileStepV one step ordT ordO gv inB zv q) bs).length = bs.length + p.length
  | [], bs => by simp
  | g :: p, bs => by
    rw [List.foldl_cons, length_foldl_compileStepV gv step ordT ordO q p, compileStepV]; simp; omega

/-- **The last result of the gate loop is the word of `fhatV`** at the predicate's output wire. -/
theorem getLast_gl_nandW (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    (h1 : one.length = V) (hz : zv = fV V f one one) (hin : ∀ i b, (inB i b).length = V)
    (gs : GateList) (hne : gs ≠ []) :
    (gl (nandW V N K f one zv) (bw (N := N) (k := K + 1) (constRepVV one zv (gvExp (2 ^ K))))
        ((List.finRange 10).map fun i => bw (inB i)) gs).getLastD [] =
      bw (fhatV one (fV V f) inB (enumT N (K + 1)) (enumO N (K + 1)) (gvExp (2 ^ K)) (2 ^ K)
        (predOf 10 gs).1 (predOf 10 gs).2) := by
  have hzl : zv.length = V := by rw [hz, fV]; exact hf _ _ (by simp) (by simp)
  rw [gl_nandW one zv inB hf h1 hzl hin gs, fhatV, ← hz, predOf]
  set bs := (fromGates 10 gs).foldl (compileStepV one (fV V f) (enumT N (K + 1))
    (enumO N (K + 1)) (gvExp (2 ^ K)) inB zv (2 ^ K)) []
  have hl : bs.length = gs.length := by
    rw [length_foldl_compileStepV]; simp [fromGates]
  have hpos : 0 < gs.length := List.length_pos_iff.mpr hne
  rw [repV, List.getD_eq_getElem _ _ (by omega), List.getLastD_eq_getLast?, List.getLast?_map,
    List.getLast?_eq_getElem?]
  simp only [List.length_map, hl]
  rw [List.getElem?_eq_getElem (by simp [hl]; omega)]
  simp

end Fhat

/-! ### The step on values of `V` bits -/

/-- **Shadows over the machine's step are shadows over the step**, when the inputs and `1` have
`V` bits and the step keeps `V` bits: `valueOf … (fV V f) = valueOf … f`. -/
theorem valueOf_fV {ι : Type*} (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    (inp : ι → List Bool) (one : List Bool) (hin : ∀ i, (inp i).length = V) (h1 : one.length = V)
    (p : SLP ι) (w : Wire ι) :
    valueOf inp one (fV V f) p w = valueOf inp one f p w := by
  let α := {x : List Bool // x.length = V}
  let st : α → α → α := fun a b => ⟨f a.1 b.1, hf _ _ a.2 b.2⟩
  have e1 := SLP.valueOf_map (fun i => (⟨inp i, hin i⟩ : α)) ⟨one, h1⟩ st inp one (fV V f)
    Subtype.val (fun _ => rfl) rfl (fun a b => by
      show f a.1 b.1 = f (takeD V a.1) (takeD V b.1)
      rw [takeD_of_length' a.2, takeD_of_length' b.2]) p w
  have e2 := SLP.valueOf_map (fun i => (⟨inp i, hin i⟩ : α)) ⟨one, h1⟩ st inp one f
    Subtype.val (fun _ => rfl) rfl (fun _ _ => rfl) p w
  rw [← e1, ← e2]

end ValVM

end SigabaNeo.Tape
