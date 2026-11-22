import PE.Impl.DualUse.Prog.Layout
import PE.Impl.DualUse.Algo.SimKey
import SigabaNeo.Lib.Machines.Prog.Lookup

/-!
# The bits `ψ_j` of the attribute ciphertexts, read off the simulation data

The inputs of the simulation of `f̂` include the `0/1` ring words `psiBitsW … j` of the bits of the
`Ψᵢ` (`PE.Impl.DualUse.Algo.SimKey`): for `j = (i, a, (c₁, c₂), b, t)` the bit `b` of the
coefficient `t` of the entry `(a, c₁ k + c₂)` of `Ψᵢ`, as a constant ring word. In the word
`sdEnc d` of the simulation data (`PE.Impl.DualUse.Prog.Layout`) that bit sits at the explicit
position `posBit j` (after `mpk`, `c₀`, the `Rᵢ`, the `Wⱼ`, then the block of `Ψᵢ`), when `b < K`;
otherwise the bit is `0` (`psiBitsW_sd`, `psiBitsW_sd_ge`).

`psiBitP j : Prog 3` (tape `0` the word `sdEnc d`, `1` scratch, `2` the output) writes
`psiBitsW … j` (`run_psiBitP`), the bit by `bitAtP` (a copy, `posBit j` drops, one bit, then
`N K - 1` zeros): at most `posBit j + N K + 4` primitives (`pcount_psiBitP_le`). Likewise
`xBitP i` writes the ring word `constW N K (bitW K (bitsOf d.x i))` of the bit `i` of the attribute
(the inputs of the Ring-GSW simulation, `run_xBitP`), read at `posX i` (the last field).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo Matrix
  AdvancedEncryption.RingBTVW SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates.DateWindow

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The length of a fixed-length encoding. -/
def fixLen {β : Type} {n : ℕ} (_ : FixedEnc β n) : ℕ := n

theorem length_enc_fixLen {β : Type} {n : ℕ} (e : FixedEnc β n) (b : β) :
    (e.enc b).length = fixLen e := e.length b

/-- The length of the word of one `Ψᵢ`. -/
abbrev lenPsi (N K k : ℕ) : ℕ := fixLen (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))

/-- The offset of the `Ψᵢ` in `sdEnc`. -/
def offPsi : ℕ :=
  fixLen (pkEnc hk c) + (fixLen (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)) + (fixLen (rmEnc c) +
    fixLen (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
      (matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Col k)))))

/-- **The position of the bit `j`** in `sdEnc d`. -/
def posBit (j : Fin 10 × BI N k) : ℕ :=
  offPsi hk c + (j.1.val * lenPsi N K k +
    ((j.2.1.val * (2 * k) + (j.2.2.1.1.val * k + j.2.2.1.2.val)) * (N * K) +
      (j.2.2.2.2.val * K + j.2.2.2.1.val)))

theorem getD_take_drop (l : List Bool) {a b r : ℕ} (hr : r < b) :
    ((l.drop a).take b).getD r false = l.getD (a + r) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hr, List.getElem?_drop]

theorem getD_append_len (A B : List Bool) (r : ℕ) : (A ++ B).getD (A.length + r) false = B.getD r false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem lenPsi_eq : lenPsi N K k = 2 * (2 * k) * (N * K) := by
  simp only [lenPsi, fixLen, matEnc, Enum.length_prod]
  simp [Enum.list]; ring

theorem lt_NK (t : Fin N) (b : Fin k) (hb : b.val < K) : t.val * K + b.val < N * K := by
  have h3 : (t.val + 1) * K ≤ N * K := Nat.mul_le_mul_right _ t.isLt
  rw [Nat.add_mul, one_mul] at h3; omega

theorem inner_lt (a c₁ : Fin 2) (c₂ : Fin k) (t : Fin N) (b : Fin k) (hb : b.val < K) :
    (a.val * (2 * k) + (c₁.val * k + c₂.val)) * (N * K) + (t.val * K + b.val) < lenPsi N K k := by
  have hq : a.val * (2 * k) + (c₁.val * k + c₂.val) + 1 ≤ 2 * (2 * k) := by
    have := index_lt c₁ c₂; have := a.isLt
    have h4 : a.val * (2 * k) + 2 * k ≤ 2 * (2 * k) := by
      have := Nat.mul_le_mul_right (2 * k) (show a.val + 1 ≤ 2 from a.isLt); rw [Nat.add_mul] at this; omega
    omega
  have h3 := Nat.mul_le_mul_right (N * K) hq
  rw [Nat.add_mul, one_mul] at h3
  have := lt_NK t b hb
  rw [lenPsi_eq]; omega

theorem fixLen_psiFun :
    fixLen (FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))) =
      10 * lenPsi N K k := by simp [fixLen, Enum.list]

/-- **The bit `j` in the simulation data** (`b < K`). -/
theorem psiBitsW_sd (d : SimData hk c) (j : Fin 10 × BI N k) (hb : j.2.2.2.1.val < K) :
    Algo.psiBitsW N K k (fun i => colsW N K k 2 (d.Ψ i)) j =
      constW N K (bitW K (((sdEnc hk c).enc d).getD (posBit hk c j) false)) := by
  obtain ⟨i, a, ⟨c₁, c₂⟩, b, t⟩ := j
  simp only at hb
  have hr : t.val * K + b.val < N * K := lt_NK t b hb
  have hin := inner_lt (N := N) (K := K) a c₁ c₂ t b hb
  simp only [Algo.psiBitsW, bitsW, rget, block]
  congr 2
  rw [getD_take_drop _ (by omega : b.val < K), getD_take_drop _ hr, sdEnc_enc]
  have hpos : posBit hk c (i, a, (c₁, c₂), b, t) = fixLen (pkEnc hk c) +
      (fixLen (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)) + (fixLen (rmEnc c) +
        (fixLen (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
          (matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Col k))) +
          (i.val * lenPsi N K k + ((a.val * (2 * k) + (c₁.val * k + c₂.val)) * (N * K) +
            (t.val * K + b.val)))))) := by
    simp only [posBit, offPsi]; omega
  rw [hpos, ← length_enc_fixLen (pkEnc hk c) d.mpk, getD_append_len,
    ← length_enc_fixLen (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)) d.c₀, getD_append_len,
    ← length_enc_fixLen (rmEnc c) d.Rm, getD_append_len,
    ← length_enc_fixLen (FixedEnc.fun (matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Col k))) d.W,
    getD_append_len, List.getD_append _ _ _ _ (by
      rw [length_enc_fixLen, fixLen_psiFun]
      have hi' := Nat.mul_le_mul_right (lenPsi N K k) (show i.val + 1 ≤ 10 from i.isLt)
      rw [Nat.add_mul, one_mul] at hi'
      omega),
    ← getD_take_drop _ hin]
  have hi : i.val < (Enum.list (α := Fin 10)).length := by simp [Enum.list]
  have hbk := FixedEnc.fun_block (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k)) d.Ψ i.val hi
  erw [hbk, Enum.getElem_fin, matEnc_cols]

/-- The bits beyond `K` are `0`. -/
theorem psiBitsW_sd_ge (d : SimData hk c) (j : Fin 10 × BI N k) (hb : K ≤ j.2.2.2.1.val) :
    Algo.psiBitsW N K k (fun i => colsW N K k 2 (d.Ψ i)) j = constW N K (bitW K false) := by
  simp only [Algo.psiBitsW, bitsW, block]
  congr 2
  rw [List.getD_eq_default]
  simp only [List.length_take]; omega

theorem constW_bitW (b : Bool) (hN : 0 < N) (hK : 0 < K) :
    constW N K (bitW K b) = b :: List.replicate (N * K - 1) false := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have h : ∀ n, concatN (n + 1) (fun t => if t = 0 then bitW (K' + 1) b else zeroW (K' + 1)) =
      bitW (K' + 1) b ++ zeroW (n * (K' + 1)) := by
    intro n
    induction n with
    | zero => simp [concatN, zeroW]
    | succ n ih =>
      rw [concatN, ih, if_neg (by omega), List.append_assoc, zeroW, zeroW, zeroW,
        ← List.replicate_add, Nat.succ_mul]
  rw [constW, h, bitW, zeroW, zeroW, List.cons_append, ← List.replicate_add]
  congr 2
  rw [Nat.succ_mul, Nat.mul_succ]; omega

/-- **The program of the bit `j`**: tape `0` the word `sdEnc d`, `1` scratch, `2` the output. -/
def psiBitP (N K k : ℕ) (pos : Fin 10 × BI N k → ℕ) (j : Fin 10 × BI N k) : Prog 3 :=
  if j.2.2.2.1.val < K then bitAtP 0 1 2 (pos j) (N * K - 1)
  else putW 2 (constW N K (bitW K false))

theorem length_sdEnc (d : SimData hk c) :
    ((sdEnc hk c).enc d).length = offPsi hk c + (10 * lenPsi N K k + 10) := by
  rw [sdEnc_enc]
  simp only [List.length_append, length_enc_fixLen, offPsi, length_encDate]
  have : fixLen (FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))) =
      10 * lenPsi N K k := by simp [fixLen, Enum.list]
  have h1 : fixLen (dateEnc) = 10 := rfl
  rw [this, h1]
  omega

theorem posBit_lt (d : SimData hk c) (j : Fin 10 × BI N k) (hb : j.2.2.2.1.val < K) :
    posBit hk c j < ((sdEnc hk c).enc d).length := by
  obtain ⟨i, a, ⟨c₁, c₂⟩, b, t⟩ := j
  have hin := inner_lt (N := N) (K := K) a c₁ c₂ t b hb
  have hi : (i.val + 1) * lenPsi N K k ≤ 10 * lenPsi N K k := Nat.mul_le_mul_right _ i.isLt
  rw [Nat.add_mul, one_mul] at hi
  rw [length_sdEnc]; simp only [posBit]; omega

theorem take_one_drop {l : List Bool} {P : ℕ} (h : P < l.length) :
    (l.drop P).take 1 = [l.getD P false] := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem _ _ h]; rfl

/-- **The law of the program of the bit `j`.** -/
theorem run_psiBitP (hN : 0 < N) (hK : 0 < K) (d : SimData hk c) (j : Fin 10 × BI N k)
    (s : Store 3) (h0 : s 0 = (sdEnc hk c).enc d) :
    run (psiBitP N K k (posBit hk c) j) s =
      Function.update (Function.update s 2 (Algo.psiBitsW N K k (fun i => colsW N K k 2 (d.Ψ i)) j))
        1 (if j.2.2.2.1.val < K then [] else s 1) := by
  unfold psiBitP
  split_ifs with hb
  · rw [run_bitAtP (by decide) (by decide), psiBitsW_sd hk c d j hb, constW_bitW _ hN hK, h0,
      take_one_drop (posBit_lt hk c d j hb)]
    rfl
  · rw [run_putW, psiBitsW_sd_ge hk c d j (by omega)]
    funext t
    simp [Function.update_apply]
    split_ifs <;> simp_all

theorem coinFree_psiBitP (pos : Fin 10 × BI N k → ℕ) (j : Fin 10 × BI N k) :
    (psiBitP N K k pos j).CoinFree := by
  unfold psiBitP; split_ifs
  · exact coinFree_bitAtP _ _ _ _ _
  · exact coinFree_putW _ _

theorem wf_psiBitP (pos : Fin 10 × BI N k → ℕ) (j : Fin 10 × BI N k) : (psiBitP N K k pos j).WF := by
  unfold psiBitP; split_ifs
  · exact wf_bitAtP _ _ _ _ _
  · exact wf_putW _ _

theorem loopFree_psiBitP (pos : Fin 10 × BI N k → ℕ) (j : Fin 10 × BI N k) :
    (psiBitP N K k pos j).LoopFree := by
  unfold psiBitP; split_ifs
  · exact loopFree_bitAtP _ _ _ _ _
  · exact loopFree_putW _ _

theorem pcount_psiBitP_le (pos : Fin 10 × BI N k → ℕ) (j : Fin 10 × BI N k) (hN : 0 < N) (hK : 0 < K) :
    pcount (psiBitP N K k pos j) ≤ pos j + N * K + 4 := by
  unfold psiBitP; split_ifs
  · rw [pcount_bitAtP]; have := Nat.mul_pos hN hK; omega
  · rw [pcount_putW, constW_bitW _ hN hK]
    simp only [List.length_cons, List.length_replicate]
    have := Nat.mul_pos hN hK
    omega

/-- **The time of the program of the bit `j`**, for tapes of at most `M` bits: quadratic, as every
primitive sweeps the word of the simulation data. -/
theorem timeBoundT_psiBitP (pos : Fin 10 × BI N k → ℕ) (j : Fin 10 × BI N k) (hN : 0 < N) (hK : 0 < K)
    (ℓ : Fin 3 → ℕ) {M : ℕ} (hM : ∀ t, ℓ t ≤ M) :
    timeBoundT (psiBitP N K k pos j) ℓ ≤
      (pos j + N * K + 4) * (2 * (M + (pos j + N * K + 4)) + 5) := by
  refine (timeBoundT_le_pcount _ (loopFree_psiBitP pos j) ℓ hM).trans ?_
  have := pcount_psiBitP_le pos j hN hK
  exact Nat.mul_le_mul this (by omega)

/-! ### The bits of the attribute -/

/-- The position of the bit `i` of the attribute in `sdEnc d`: the last field. -/
def posX (i : Fin 10) : ℕ := offPsi hk c + (10 * lenPsi N K k + i.val)

theorem getD_sd_posX (d : SimData hk c) (i : Fin 10) :
    ((sdEnc hk c).enc d).getD (posX hk c i) false = bitsOf d.x i := by
  rw [sdEnc_enc]
  have hpos : posX hk c i = fixLen (pkEnc hk c) +
      (fixLen (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)) + (fixLen (rmEnc c) +
        (fixLen (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
          (matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Col k))) +
          (fixLen (FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))) +
            i.val)))) := by
    rw [fixLen_psiFun]; simp only [posX, offPsi]; omega
  rw [hpos, ← length_enc_fixLen (pkEnc hk c) d.mpk, getD_append_len,
    ← length_enc_fixLen (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)) d.c₀, getD_append_len,
    ← length_enc_fixLen (rmEnc c) d.Rm, getD_append_len,
    ← length_enc_fixLen (FixedEnc.fun (matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Col k))) d.W,
    getD_append_len,
    ← length_enc_fixLen (FixedEnc.fun (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))) d.Ψ,
    getD_append_len]
  rfl

theorem posX_lt (d : SimData hk c) (i : Fin 10) : posX hk c i < ((sdEnc hk c).enc d).length := by
  rw [length_sdEnc]; simp only [posX]; omega

/-- **The program of the bit `i` of the attribute**: tape `0` the word `sdEnc d`, `1` scratch, `2`
the output, the ring word of the bit (an input of the Ring-GSW simulation). -/
def xBitP (N K : ℕ) (pos : Fin 10 → ℕ) (i : Fin 10) : Prog 3 := bitAtP 0 1 2 (pos i) (N * K - 1)

theorem run_xBitP (hN : 0 < N) (hK : 0 < K) (d : SimData hk c) (i : Fin 10) (s : Store 3)
    (h0 : s 0 = (sdEnc hk c).enc d) :
    run (xBitP N K (posX hk c) i) s =
      Function.update (Function.update s 2 (constW N K (bitW K (bitsOf d.x i)))) 1 [] := by
  rw [xBitP, run_bitAtP (by decide) (by decide), constW_bitW _ hN hK, h0,
    take_one_drop (posX_lt hk c d i), getD_sd_posX]
  rfl

theorem coinFree_xBitP (pos : Fin 10 → ℕ) (i : Fin 10) : (xBitP N K pos i).CoinFree :=
  coinFree_bitAtP _ _ _ _ _

theorem wf_xBitP (pos : Fin 10 → ℕ) (i : Fin 10) : (xBitP N K pos i).WF := wf_bitAtP _ _ _ _ _

theorem timeBoundT_xBitP (pos : Fin 10 → ℕ) (i : Fin 10) (ℓ : Fin 3 → ℕ) {M : ℕ}
    (hM : ∀ t, ℓ t ≤ M) :
    timeBoundT (xBitP N K pos i) ℓ ≤
      (pos i + (N * K - 1) + 5) * (2 * (M + (pos i + (N * K - 1) + 5)) + 5) := by
  have := timeBoundT_le_pcount _ (loopFree_bitAtP (0 : Fin 3) 1 2 (pos i) (N * K - 1)) ℓ hM
  rwa [pcount_bitAtP] at this

end AdvancedEncryption.DualUse.Prog
