import PE.Impl.ExpLUT.Prog.RedChalVM

/-!
# Generic `RingVM` kernels of `pubP` (package G2)

* `pbuf b₀ acc`: a shift register `b₀` after the bits `acc` were shifted in; **`exec_mv_blk`**:
  `mv d s c` shifts the next `|c|` bits of the stream `s` into it (any block width);
  `pbuf_full`: a register pre-sized to the total width ends holding exactly the bits;
* `exec_drop_blk`: dropping a block from a stream;
* words lists: `flatten_drop_words`, `flatten_drop_cons`;
* **`exec_strided`**: the loop `rep n (mv d s c; drop s k)` pushes the words `L[i J + k₀]`
  (`i < n`) of the stream `s = (L.drop k₀).flatten` (a strided read).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices.Algo

variable {N K : ℕ}

/-! ### Shift registers of bits -/

/-- The shift register `b₀` after the bits `acc` were shifted in. -/
def pbuf (b₀ acc : List Bool) : List Bool := (b₀ ++ acc).drop acc.length

theorem pbuf_nil (b₀ : List Bool) : pbuf b₀ [] = b₀ := by simp [pbuf]

theorem pbuf_push (b₀ acc v : List Bool) :
    (pbuf b₀ acc ++ v).drop v.length = pbuf b₀ (acc ++ v) := by
  unfold pbuf
  rw [← List.drop_append_of_le_length (by simp), List.drop_drop, List.length_append,
    List.append_assoc, Nat.add_comm]

theorem pbuf_full {b₀ acc : List Bool} (h : b₀.length = acc.length) : pbuf b₀ acc = acc := by
  unfold pbuf; rw [← h, List.drop_left]

theorem length_pbuf (b₀ acc : List Bool) : (pbuf b₀ acc).length = b₀.length := by
  simp [pbuf]

/-- **Shift a block into a shift register.** -/
theorem exec_mv_blk {d s c : Fin 200} (h : ¬(d = s ∨ d = c ∨ s = c)) {w : St}
    {b₀ acc v L : List Bool} (hd : w d = pbuf b₀ acc) (hv : v.length = (w c).length)
    (hs : w s = v ++ L) :
    exec N K (.mv d s c) w = Function.update (Function.update w s L) d (pbuf b₀ (acc ++ v)) := by
  simp only [exec, if_neg h, ValVM.shiftIn, hs, hd]
  rw [takeD_eq_take (by simp; omega), List.take_left' hv, ← hv, List.drop_left, pbuf_push]

/-- **Drop a block from a stream.** -/
theorem exec_drop_blk {t c : Fin 200} (h : t ≠ c) {w : St} {v L : List Bool}
    (hv : (w c).length = v.length) (hs : w t = v ++ L) :
    exec N K (.drop t c) w = Function.update w t L := by
  simp only [exec, h, ite_false, hs, hv, List.drop_left]

theorem exec_drop_eq {t c : Fin 200} (h : t ≠ c) (w : St) :
    exec N K (.drop t c) w = Function.update w t ((w t).drop (w c).length) := by
  simp only [exec, h, ite_false]

/-! ### Lists of words -/

theorem flatten_drop_words {W : ℕ} : ∀ (L : List (List Bool)), (∀ x ∈ L, x.length = W) →
    ∀ j, L.flatten.drop (j * W) = (L.drop j).flatten
  | [], _, j => by simp
  | x :: L, hL, 0 => by simp
  | x :: L, hL, j + 1 => by
    rw [List.flatten_cons, Nat.succ_mul, Nat.add_comm, ← List.drop_drop,
      List.drop_left' (hL x (by simp)), flatten_drop_words L (fun y hy => hL y (by simp [hy])) j]
    rfl

theorem flatten_drop_cons {L : List (List Bool)} {m : ℕ} (hm : m < L.length) :
    (L.drop m).flatten = L[m] ++ (L.drop (m + 1)).flatten := by
  rw [List.drop_eq_getElem_cons hm, List.flatten_cons]

theorem flatten_drop_drop {W : ℕ} {L : List (List Bool)} (hL : ∀ x ∈ L, x.length = W) (m j : ℕ) :
    (L.drop m).flatten.drop (j * W) = (L.drop (m + j)).flatten := by
  rw [flatten_drop_words (L.drop m) (fun x hx => hL x (List.mem_of_mem_drop hx)), List.drop_drop]

theorem length_flatten_words {W : ℕ} {L : List (List Bool)} (hL : ∀ x ∈ L, x.length = W) :
    L.flatten.length = L.length * W := length_flatten_of hL

/-! ### The strided read -/

/-- One round of a strided read: push a word of the stream `s`, skip `|k|` bits. -/
def sBody (d s c k : Fin 200) : Code := .seq (.mv d s c) (.drop s k)

/-- **The strided read**: `n` words `L[i J + k₀]` of the stream `s`. -/
theorem exec_strided {d s c k cnt : Fin 200} (hds : d ≠ s) (hdc : d ≠ c) (hsc : s ≠ c)
    (hsk : s ≠ k) (hcd : cnt ≠ d) (hcs : cnt ≠ s) (hck : cnt ≠ k) (hcc : cnt ≠ c)
    (hdk : d ≠ k) (w : St)
    (W J n k₀ : ℕ) (hJ : 0 < J) (L : List (List Bool)) (hL : ∀ x ∈ L, x.length = W)
    (hlen : ∀ i < n, i * J + k₀ < L.length)
    (b₀ acc : List Bool) (hd : w d = pbuf b₀ acc) (hs : w s = (L.drop k₀).flatten)
    (hc : (w c).length = W) (hk : (w k).length = (J - 1) * W) (hn : (w cnt).length = n) :
    exec N K (.rep cnt (sBody d s c k)) w d =
        pbuf b₀ (acc ++ ((List.range n).map fun i => L.getD (i * J + k₀) []).flatten) ∧
      exec N K (.rep cnt (sBody d s c k)) w s = (L.drop (n * J + k₀)).flatten ∧
      ∀ j, j ≠ d → j ≠ s → j ≠ cnt → exec N K (.rep cnt (sBody d s c k)) w j = w j := by
  let P : ℕ → St → Prop := fun i w' =>
    w' d = pbuf b₀ (acc ++ ((List.range i).map fun i => L.getD (i * J + k₀) []).flatten) ∧
      w' s = (L.drop (i * J + k₀)).flatten ∧ ∀ j, j ≠ d → j ≠ s → j ≠ cnt → w' j = w j
  have hwr : cnt ∉ wr (sBody d s c k) := by
    simp only [sBody, wr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨hcd, hcs⟩, hcs⟩
  have h0 : P 0 w := ⟨by simp [hd], by simp [hs], fun _ _ _ _ => rfl⟩
  have key := exec_rep_inv (N := N) (K := K) cnt (sBody d s c k) hwr P w h0 (fun i hi w' hP _ => by
    rw [hn] at hi
    obtain ⟨hd', hs', hfr⟩ := hP
    set u := Function.update w' cnt (w' cnt).tail
    have hu : ∀ j, j ≠ cnt → u j = w' j := fun j hj => Function.update_of_ne hj _ _
    have hm := hlen i hi
    have hx := hL _ (List.getElem_mem hm)
    have e1 := exec_mv_blk (N := N) (K := K) (d := d) (s := s) (c := c) (w := u)
      (by simp only [not_or]; exact ⟨hds, hdc, hsc⟩) (b₀ := b₀)
      (acc := acc ++ ((List.range i).map fun i => L.getD (i * J + k₀) []).flatten)
      (v := L[i * J + k₀]) (L := (L.drop (i * J + k₀ + 1)).flatten)
      (by rw [hu d hcd.symm, hd']) (by rw [hx, hu c hcc.symm, hfr c hdc.symm hsc.symm hcc.symm, hc])
      (by rw [hu s hcs.symm, hs', flatten_drop_cons hm])
    have e2 := exec_drop_eq (N := N) (K := K) hsk (Function.update (Function.update u s
      (L.drop (i * J + k₀ + 1)).flatten) d
        (pbuf b₀ ((acc ++ ((List.range i).map fun i => L.getD (i * J + k₀) []).flatten) ++
          L[i * J + k₀])))
    have ek : (Function.update (Function.update u s (L.drop (i * J + k₀ + 1)).flatten) d
        (pbuf b₀ ((acc ++ ((List.range i).map fun i => L.getD (i * J + k₀) []).flatten) ++
          L[i * J + k₀]))) k = w k := by
      rw [Function.update_of_ne hdk.symm, Function.update_of_ne hsk.symm, hu k hck.symm,
        hfr k hdk.symm hsk.symm hck.symm]
    have es : (Function.update (Function.update u s (L.drop (i * J + k₀ + 1)).flatten) d
        (pbuf b₀ ((acc ++ ((List.range i).map fun i => L.getD (i * J + k₀) []).flatten) ++
          L[i * J + k₀]))) s = (L.drop (i * J + k₀ + 1)).flatten := by
      rw [Function.update_of_ne hds.symm, Function.update_self]
    have ex : exec N K (sBody d s c k) u = Function.update (Function.update (Function.update u s
        (L.drop (i * J + k₀ + 1)).flatten) d
        (pbuf b₀ ((acc ++ ((List.range i).map fun i => L.getD (i * J + k₀) []).flatten) ++
          L[i * J + k₀]))) s ((L.drop ((i + 1) * J + k₀)).flatten) := by
      show exec N K (.drop s k) (exec N K (.mv d s c) u) = _
      rw [e1, e2, ek, es, hk, flatten_drop_drop hL]
      congr 3
      have : 1 ≤ J := hJ
      rw [Nat.succ_mul]; omega
    rw [ex]
    refine ⟨?_, ?_, ?_⟩
    · rw [Function.update_of_ne hds, Function.update_self, List.range_succ, List.map_append,
        List.flatten_append, List.map_singleton, List.flatten_singleton, List.append_assoc,
        List.getD_eq_getElem _ _ hm]
    · rw [Function.update_self]
    · intro j h1 h2 h3
      rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h2, hu j h3,
        hfr j h1 h2 h3])
  rw [hn] at key
  exact key

end AdvancedEncryption.ExpLUT.Prog.RedPubP
