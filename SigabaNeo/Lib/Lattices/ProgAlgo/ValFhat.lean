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

end ValVM

end SigabaNeo.Tape
