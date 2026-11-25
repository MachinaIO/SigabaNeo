import PE.Impl.RingBTVW.Prog.SetupP
import SigabaNeo.Lib.Lattices.ProgAlgo.BinMul
import PE.Impl.RingBTVW.Algo.KeyWords

/-!
# The Ring-GSW ciphertexts of `Enc` on words

The program `binMulP` (`SigabaNeo.Lib.Lattices.ProgAlgo.BinMul`) computes products with binary
matrices given column by column, by sums of subsets, plus a gadget when a bit is set. Here its
abstract steps are evaluated on the words of the scheme's values:

* `aStepB_list`, `colB_enc`: the sums of a column are the words of `∑ₐ bitVal (f a) · B a`;
* `rowsB_enc`: the rows of `A · R` for a list of binary columns;
* `gswW`, `gswW_enc`: the word of the Ring-GSW gadget `Γ.G` (`2 × Col k`), and
  `gswW_eq`: it is `gadW ++ 0^{k N K} ++ take (k N K) gadW` (the way the program builds it);
* **`binMul_psi`**: from the words of `B₀`, `c₀ = s B₀ + e₀`, the coins `Rᵢ = rMat r i`
  (column-major, `rmTEnc`), the date bits and the gadget word, the output register receives the
  word of the ten Ring-GSW ciphertexts `Ψᵢ = [B₀; c₀] Rᵢ + xᵢ G` of `encrypt`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  Matrix AdvancedEncryption.RingBTVW.Fresh Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

variable {N K k : ℕ}

/-! ### Words of ring elements -/

theorem len_enc (v : Rg N K) : ((ringEnc N K).enc v).length = N * K := (ringEnc N K).length v

theorem takeD_enc_append (v : Rg N K) (rest : List Bool) :
    takeD (N * K) ((ringEnc N K).enc v ++ rest) = (ringEnc N K).enc v := by
  rw [takeD_eq_take (by simp [len_enc]), List.take_left' (len_enc v)]

theorem drop_enc_append (v : Rg N K) (rest : List Bool) :
    ((ringEnc N K).enc v ++ rest).drop (N * K) = rest := List.drop_left' (len_enc v)

theorem hd_enc_bitVal (hN : 0 < N) (hK : 0 < K) (b : Bool) (rest : List Bool) :
    Tape.hd ((ringEnc N K).enc (bitVal (R := Rg N K) b) ++ rest) = b := by
  rw [enc_bitVal hN hK]; rfl

theorem enc_zero_rep : (ringEnc N K).enc (0 : Rg N K) = List.replicate (N * K) false :=
  enc_zeroR N K

/-! ### The sums of a column -/

theorem aStepB_list (hN : 0 < N) (hK : 0 < K) :
    ∀ (l : List (Bool × Rg N K × Rg N K)) (x0 x1 : Rg N K) (rr rb rc : List Bool),
      (Prog.aStepB N K)^[l.length] ((ringEnc N K).enc x0, (ringEnc N K).enc x1,
        l.flatMap (fun p => (ringEnc N K).enc (bitVal p.1)) ++ rr,
        l.flatMap (fun p => (ringEnc N K).enc p.2.1) ++ rb,
        l.flatMap (fun p => (ringEnc N K).enc p.2.2) ++ rc) =
      ((ringEnc N K).enc (x0 + (l.map fun p => bitVal p.1 * p.2.1).sum),
        (ringEnc N K).enc (x1 + (l.map fun p => bitVal p.1 * p.2.2).sum), rr, rb, rc)
  | [], x0, x1, rr, rb, rc => by simp
  | p :: l, x0, x1, rr, rb, rc => by
    obtain ⟨b, u, v⟩ := p
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc]
    have hstep : Prog.aStepB N K ((ringEnc N K).enc x0, (ringEnc N K).enc x1,
        (ringEnc N K).enc (bitVal b) ++ (l.flatMap (fun p => (ringEnc N K).enc (bitVal p.1)) ++ rr),
        (ringEnc N K).enc u ++ (l.flatMap (fun p => (ringEnc N K).enc p.2.1) ++ rb),
        (ringEnc N K).enc v ++ (l.flatMap (fun p => (ringEnc N K).enc p.2.2) ++ rc)) =
        ((ringEnc N K).enc (x0 + bitVal b * u), (ringEnc N K).enc (x1 + bitVal b * v),
          l.flatMap (fun p => (ringEnc N K).enc (bitVal p.1)) ++ rr,
          l.flatMap (fun p => (ringEnc N K).enc p.2.1) ++ rb,
          l.flatMap (fun p => (ringEnc N K).enc p.2.2) ++ rc) := by
      simp only [Prog.aStepB, hd_enc_bitVal hN hK, takeD_enc_append, drop_enc_append, addRW_enc]
      cases b <;> simp [bitVal]
    rw [hstep, aStepB_list hN hK l]
    simp only [List.map_cons, List.sum_cons, add_assoc]

theorem flatMap_enc_row {d : ℕ} (B : Matrix (Fin 1) (Fin d) (Rg N K)) :
    (matEnc (N := N) (K := K) (Fin 1) (Fin d)).enc B =
      (List.finRange d).flatMap fun a => (ringEnc N K).enc (B 0 a) := by
  rw [Algo.matEnc_row1, Algo.vecW, fun_enc_eq, List.flatMap_map]
  rfl

/-- The word of a binary column. -/
def colWord (d : ℕ) (f : Fin d → Bool) : List Bool :=
  (List.finRange d).flatMap fun a => (ringEnc N K).enc (bitVal (R := Rg N K) (f a))

theorem colB_enc (hN : 0 < N) (hK : 0 < K) {d : ℕ} (f : Fin d → Bool) (B C : Fin d → Rg N K)
    (rest : List Bool) :
    Prog.colB N K d ((List.finRange d).flatMap fun a => (ringEnc N K).enc (B a))
      ((List.finRange d).flatMap fun a => (ringEnc N K).enc (C a))
      (colWord (N := N) (K := K) d f ++ rest) =
      ((ringEnc N K).enc (∑ a, bitVal (f a) * B a), (ringEnc N K).enc (∑ a, bitVal (f a) * C a),
        rest, [], []) := by
  have h := aStepB_list hN hK ((List.finRange d).map fun a => (f a, B a, C a)) 0 0 rest [] []
  simp only [List.length_map, List.length_finRange, List.flatMap_map, List.append_nil,
    zero_add, List.map_map, Function.comp_def] at h
  rw [Prog.colB, ← enc_zero_rep, colWord, h, Fin.sum_univ_def, Fin.sum_univ_def]

/-! ### Rows -/

/-- Shifting a word of `N K` bits, then `c` words, into a register. -/
theorem reg_shift {c : ℕ} (x y z : List Bool) (hy : y.length = N * K) :
    ((x ++ y).drop (N * K) ++ z).drop (c * (N * K)) =
      (x ++ (y ++ z)).drop ((c + 1) * (N * K)) := by
  rw [← List.drop_append_of_le_length (by simp [hy]), List.drop_drop, List.append_assoc]
  congr 1
  ring

theorem cStepB_list (hN : 0 < N) (hK : 0 < K) {d : ℕ} (B C : Fin d → Rg N K) :
    ∀ (cols : List (Fin d → Bool)) (r0 r1 rest : List Bool),
      (Prog.cStepB N K d ((List.finRange d).flatMap fun a => (ringEnc N K).enc (B a))
        ((List.finRange d).flatMap fun a => (ringEnc N K).enc (C a)))^[cols.length]
        (r0, r1, cols.flatMap (colWord (N := N) (K := K) d) ++ rest) =
      ((r0 ++ cols.flatMap fun f => (ringEnc N K).enc (∑ a, bitVal (f a) * B a)).drop
          (cols.length * (N * K)),
        (r1 ++ cols.flatMap fun f => (ringEnc N K).enc (∑ a, bitVal (f a) * C a)).drop
          (cols.length * (N * K)), rest)
  | [], r0, r1, rest => by simp
  | f :: cols, r0, r1, rest => by
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc]
    have hstep : Prog.cStepB N K d ((List.finRange d).flatMap fun a => (ringEnc N K).enc (B a))
        ((List.finRange d).flatMap fun a => (ringEnc N K).enc (C a))
        (r0, r1, colWord (N := N) (K := K) d f ++ (cols.flatMap (colWord (N := N) (K := K) d) ++
          rest)) =
        ((r0 ++ (ringEnc N K).enc (∑ a, bitVal (f a) * B a)).drop (N * K),
          (r1 ++ (ringEnc N K).enc (∑ a, bitVal (f a) * C a)).drop (N * K),
          cols.flatMap (colWord (N := N) (K := K) d) ++ rest) := by
      simp only [Prog.cStepB, colB_enc hN hK]
      rw [takeD_of_length' (len_enc _), takeD_of_length' (len_enc _)]
    rw [hstep, cStepB_list hN hK B C cols]
    rw [reg_shift _ _ _ (len_enc _), reg_shift _ _ _ (len_enc _)]

theorem rowsB_enc (hN : 0 < N) (hK : 0 < K) {d L : ℕ} (B C : Fin d → Rg N K)
    (cols : List (Fin d → Bool)) (hL : cols.length = L) (rest : List Bool) :
    Prog.rowsB N K d L ((List.finRange d).flatMap fun a => (ringEnc N K).enc (B a))
      ((List.finRange d).flatMap fun a => (ringEnc N K).enc (C a))
      (cols.flatMap (colWord (N := N) (K := K) d) ++ rest) =
      (cols.flatMap fun f => (ringEnc N K).enc (∑ a, bitVal (f a) * B a),
        cols.flatMap fun f => (ringEnc N K).enc (∑ a, bitVal (f a) * C a), rest) := by
  subst hL
  rw [Prog.rowsB, cStepB_list hN hK B C cols, List.drop_left' (by simp),
    List.drop_left' (by simp)]

/-- The rows of `A · R + x G` in a register. -/
theorem qB_eq {L : ℕ} (g : List Bool) (x : Bool) (r0 r1 : List Bool)
    (h0 : r0.length = L * (N * K)) (h1 : r1.length = L * (N * K)) :
    Prog.qB N K L g x r0 r1 = if x then addRW (2 * L * N) K (r0 ++ r1) g else r0 ++ r1 := by
  have e : ((List.replicate (2 * L * (N * K)) false ++ r0).drop (L * (N * K)) ++ r1).drop
      (L * (N * K)) = r0 ++ r1 := by
    rw [← List.drop_append_of_le_length (by simp; nlinarith), List.drop_drop,
      show L * (N * K) + L * (N * K) = 2 * L * (N * K) by ring, List.append_assoc,
      List.drop_left' (by simp)]
  simp only [Prog.qB, takeD_of_length' h0, takeD_of_length' h1, e]

/-! ### The Ring-GSW gadget -/

/-- The word of the Ring-GSW gadget `Γ.G`: `2^j` at the entries `(a, (a, j))`. -/
def gswW (N K k : ℕ) : List Bool :=
  concatN (2 * (2 * k)) fun p =>
    if p / (2 * k) = p % (2 * k) / k then constW N K (powW K (p % k)) else zeroW (N * K)

theorem gswW_enc (hk : 2 ^ K < 2 ^ k) :
    (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc (Sdw (N := N) hk).Γ.G = gswW N K k := by
  rw [matEnc_cols, colsW]
  symm
  apply concatN_eq_matW
  intro p hp
  rw [submatrix_apply, id, colE_apply]
  simp only [Setting.Γ, gswGadget, gadgetOf, Matrix.of_apply, Sdw, ringSetting, binaryDigits, id]
  have hmod : p % (2 * k) % k = p % k := Nat.mod_mod_of_dvd p (Dvd.intro_left 2 rfl)
  by_cases h : p / (2 * k) = p % (2 * k) / k
  · rw [if_pos h, if_pos (Fin.ext h), enc_algebraMap, enc_pow]
    simp [hmod]
  · rw [if_neg h, if_neg (fun e => h (congrArg Fin.val e))]
    exact (enc_zeroR N K).symm

theorem len_constW_pow (p : ℕ) : (constW N K (powW K p)).length = N * K := by
  rw [← enc_pow, ← enc_algebraMap]; exact len_enc _

theorem concatN_const (m : ℕ) (w : List Bool) : ∀ n, concatN n (fun _ => w) = (List.replicate n w).flatten
  | 0 => rfl
  | n + 1 => by rw [concatN, concatN_const m w n, List.replicate_succ', List.flatten_append]; simp

theorem concatN_zeroW (m : ℕ) : ∀ n, concatN n (fun _ => zeroW m) = List.replicate (n * m) false
  | 0 => by simp [concatN]
  | n + 1 => by
    rw [concatN, concatN_zeroW m n, zeroW, Nat.succ_mul, List.replicate_add]

/-- **How the program builds the gadget word**: `G̲`, then `k N K` zeros, then the first half of
`G̲`. -/
theorem gswW_eq : gswW N K k =
    gadW N K k ++ (List.replicate (k * (N * K)) false ++ (gadW N K k).take (k * (N * K))) := by
  have hg : gadW N K k = concatN k (fun p => constW N K (powW K p)) ++
      List.replicate (k * (N * K)) false := by
    rw [gadW, show 1 * (2 * k) = k + k by ring, concatN_add, ← concatN_zeroW]
    congr 1
    · refine concatN_congr fun i hi => ?_
      rw [if_pos (Nat.div_eq_of_lt hi), Nat.mod_eq_of_lt hi]
    · refine concatN_congr fun i hi => ?_
      rw [if_neg (Nat.div_pos (by omega) (by omega)).ne']
  have hlen : (concatN k (fun p => constW N K (powW K p))).length = k * (N * K) :=
    length_concatN fun i _ => len_constW_pow i
  rw [gswW, show 2 * (2 * k) = (k + k) + (k + k) by ring, concatN_add, concatN_add, concatN_add,
    hg, List.take_left' hlen]
  have dm : ∀ (q n p : ℕ), q * n ≤ p → p < (q + 1) * n → p / n = q ∧ p % n = p - q * n := by
    intro q n p h1 h2
    have hd := Nat.div_eq_of_lt_le h1 h2
    refine ⟨hd, ?_⟩
    have := Nat.div_add_mod p n
    rw [hd] at this
    rw [Nat.mul_comm] at this
    omega
  congr 1
  · congr 1
    · refine concatN_congr fun i hi => ?_
      obtain ⟨a1, b1⟩ := dm 0 (2 * k) i (by omega) (by omega)
      obtain ⟨a2, b2⟩ := dm 0 k (i % (2 * k)) (by omega) (by rw [b1]; omega)
      obtain ⟨a3, b3⟩ := dm 0 k i (by omega) (by omega)
      rw [if_pos (by rw [a1, a2]), b3]
      simp
    · rw [← concatN_zeroW]
      refine concatN_congr fun i hi => ?_
      obtain ⟨a1, b1⟩ := dm 0 (2 * k) (k + i) (by omega) (by omega)
      obtain ⟨a2, b2⟩ := dm 1 k ((k + i) % (2 * k)) (by rw [b1]; omega) (by rw [b1]; omega)
      rw [if_neg (by rw [a1, a2]; omega)]
  · congr 1
    · rw [← concatN_zeroW]
      refine concatN_congr fun i hi => ?_
      obtain ⟨a1, b1⟩ := dm 1 (2 * k) (k + k + i) (by omega) (by omega)
      obtain ⟨a2, b2⟩ := dm 0 k ((k + k + i) % (2 * k)) (by rw [b1]; omega) (by rw [b1]; omega)
      rw [if_neg (by rw [a1, a2]; omega)]
    · refine concatN_congr fun i hi => ?_
      obtain ⟨a1, b1⟩ := dm 1 (2 * k) (k + k + (k + i)) (by omega) (by omega)
      obtain ⟨a2, b2⟩ := dm 1 k ((k + k + (k + i)) % (2 * k)) (by rw [b1]; omega) (by rw [b1]; omega)
      obtain ⟨a3, b3⟩ := dm 3 k (k + k + (k + i)) (by omega) (by omega)
      rw [if_pos (by rw [a1, a2]), b3]
      congr 2
      omega

/-! ### The ciphertexts `Ψᵢ` -/

theorem length_flatMap_constE {α : Type} {n : ℕ} (l : List α) (f : α → List Bool)
    (h : ∀ x ∈ l, (f x).length = n) : (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a (by simp),
      ih (fun x hx => h x (by simp [hx])), List.length_cons]
    ring

theorem matEnc2_eq (M : Matrix (Fin 2) (RingBTVW.Fresh.Col k) (Rg N K)) :
    (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc M =
      (Enum.list (α := RingBTVW.Fresh.Col k)).flatMap (fun col => (ringEnc N K).enc (M 0 col)) ++
        (Enum.list (α := RingBTVW.Fresh.Col k)).flatMap (fun col => (ringEnc N K).enc (M 1 col)) := by
  rw [show (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc M =
      ((Enum.list (α := Fin 2)).map (fun r => M r)).flatMap
        (fun row => ((Enum.list (α := RingBTVW.Fresh.Col k)).map row).flatMap (ringEnc N K).enc) from rfl,
    show (Enum.list (α := Fin 2)) = [0, 1] from rfl]
  simp [List.flatMap_map]

theorem matEnc2_add (M M' : Matrix (Fin 2) (RingBTVW.Fresh.Col k) (Rg N K)) :
    (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc (M + M') =
      addRW (2 * (2 * k) * N) K ((matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc M)
        ((matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc M') := by
  rw [matEnc_cols, matEnc_cols, matEnc_cols, colsW, colsW, colsW, ← matAddW_eq_addRW,
    matAddW_enc]
  rfl

theorem len_matEnc2 (M : Matrix (Fin 2) (RingBTVW.Fresh.Col k) (Rg N K)) :
    ((matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc M).length = 2 * (2 * k) * (N * K) := by
  rw [matEnc_cols, colsW, length_matW]

theorem len_enum_col : (Enum.list (α := RingBTVW.Fresh.Col k)).length = 2 * k := by
  rw [Enum.length_prod]; simp [Enum.list]

variable (hk : 2 ^ K < 2 ^ k)

/-- **One Ring-GSW ciphertext**: the word `qB` of the rows of `A · Rᵢ` and the bit `xᵢ` is the
word of `Ψᵢ = A Rᵢ + xᵢ G`. -/
theorem qB_psi (hN : 0 < N) (hK : 0 < K) {d : ℕ} (B₀ c₀ : Matrix (Fin 1) (Fin d) (Rg N K))
    (rr : (Sdw (N := N) hk).Attr × RingBTVW.Fresh.Col k → (Fin d → Bool)) (i : Fin nA) (x : Bool)
    (rest : List Bool) :
    Prog.qB N K (2 * k) (gswW N K k) x
      (Prog.rowsB N K d (2 * k) ((List.finRange d).flatMap fun a => (ringEnc N K).enc (B₀ 0 a))
        ((List.finRange d).flatMap fun a => (ringEnc N K).enc (c₀ 0 a))
        (((Enum.list (α := RingBTVW.Fresh.Col k)).map fun col => rr (i, col)).flatMap
          (colWord (N := N) (K := K) d) ++ rest)).1
      (Prog.rowsB N K d (2 * k) ((List.finRange d).flatMap fun a => (ringEnc N K).enc (B₀ 0 a))
        ((List.finRange d).flatMap fun a => (ringEnc N K).enc (c₀ 0 a))
        (((Enum.list (α := RingBTVW.Fresh.Col k)).map fun col => rr (i, col)).flatMap
          (colWord (N := N) (K := K) d) ++ rest)).2.1 =
      (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc
        (gswPK B₀ c₀ * rMat (R := Rg N K) rr i + bitR (R := Rg N K) x • (Sdw (N := N) hk).Γ.G) := by
  have hL : ((Enum.list (α := RingBTVW.Fresh.Col k)).map fun col => rr (i, col)).length = 2 * k := by
    rw [List.length_map, len_enum_col]
  rw [rowsB_enc hN hK _ _ _ hL]
  have hrow : ∀ (r : Fin 2),
      (((Enum.list (α := RingBTVW.Fresh.Col k)).map fun col => rr (i, col)).flatMap fun f =>
        (ringEnc N K).enc (∑ a, bitVal (f a) * (if r = 0 then B₀ 0 a else c₀ 0 a))) =
      (Enum.list (α := RingBTVW.Fresh.Col k)).flatMap
        (fun col => (ringEnc N K).enc ((gswPK B₀ c₀ * rMat (R := Rg N K) rr i) r col)) := by
    intro r
    rw [List.flatMap_map]
    congr 1
    funext col
    congr 1
    simp only [Matrix.mul_apply, gswPK, rMat, Matrix.of_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have h0 := hrow 0
  have h1 := hrow 1
  simp only [if_true, show ((1 : Fin 2) = 0) = False from by decide, if_false] at h0 h1
  rw [qB_eq _ _ _ _ (by rw [length_flatMap_constE _ _ (fun _ _ => len_enc _), hL])
    (by rw [length_flatMap_constE _ _ (fun _ _ => len_enc _), hL]), h0, h1, ← matEnc2_eq]
  cases x
  · simp [bitR]
  · simp only [bitR, if_true, one_smul, if_true]
    rw [matEnc2_add, gswW_enc hk]

theorem reg_shiftW {W c : ℕ} (x y z : List Bool) (hy : y.length = W) :
    ((x ++ y).drop W ++ z).drop (c * W) = (x ++ (y ++ z)).drop ((c + 1) * W) := by
  rw [← List.drop_append_of_le_length (by simp [hy]), List.drop_drop, List.append_assoc]
  congr 1
  ring

/-- The word of the `Rᵢ` (column-major), matrix by matrix, column by column. -/
theorem rmTEnc_cols (c : Conf N K k) (rr : (Sdw (N := N) hk).Attr × RingBTVW.Fresh.Col k → (Fin c.d → Bool)) :
    (rmTEnc c).enc (rMat (R := Rg N K) rr) =
      (List.finRange nA).flatMap fun (i : Fin nA) =>
        ((Enum.list (α := RingBTVW.Fresh.Col k)).map fun col => rr (i, col)).flatMap
          (colWord (N := N) (K := K) c.d) := by
  show ((List.finRange nA).map (fun (i : Fin nA) => rMat (R := Rg N K) rr i)).flatMap
    (matTEnc (Fin c.d) (RingBTVW.Fresh.Col k)).enc = _
  simp only [List.flatMap_map, matTEnc_enc, colWord, rMat, Matrix.of_apply]
  rfl

/-- **The ten Ring-GSW ciphertexts**, matrix by matrix. -/
theorem iStepB_list (hN : 0 < N) (hK : 0 < K) {d : ℕ} (B₀ c₀ : Matrix (Fin 1) (Fin d) (Rg N K))
    (rr : (Sdw (N := N) hk).Attr × RingBTVW.Fresh.Col k → (Fin d → Bool)) (xb : Fin nA → Bool) :
    ∀ (l : List (Fin nA)) (out rest xr : List Bool),
      (Prog.iStepB N K d (2 * k) ((List.finRange d).flatMap fun a => (ringEnc N K).enc (B₀ 0 a))
        ((List.finRange d).flatMap fun a => (ringEnc N K).enc (c₀ 0 a)) (gswW N K k))^[l.length]
        (out, (l.flatMap fun (i : Fin nA) => ((Enum.list (α := RingBTVW.Fresh.Col k)).map
          fun col => rr (i, col)).flatMap (colWord (N := N) (K := K) d)) ++ rest, l.map xb ++ xr) =
      ((out ++ l.flatMap fun (i : Fin nA) => (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)).enc
          (gswPK B₀ c₀ * rMat (R := Rg N K) rr i + bitR (R := Rg N K) (xb i) •
            (Sdw (N := N) hk).Γ.G)).drop (l.length * (2 * (2 * k) * (N * K))), rest, xr)
  | [], out, rest, xr => by simp
  | i :: l, out, rest, xr => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep := qB_psi hk hN hK B₀ c₀ rr i (xb i)
      ((l.flatMap fun (i : Fin nA) => ((Enum.list (α := RingBTVW.Fresh.Col k)).map
        fun col => rr (i, col)).flatMap (colWord (N := N) (K := K) d)) ++ rest)
    have hrows := rowsB_enc hN hK (fun a => B₀ 0 a) (fun a => c₀ 0 a)
      ((Enum.list (α := RingBTVW.Fresh.Col k)).map fun col => rr (i, col))
      (by rw [List.length_map, len_enum_col])
      ((l.flatMap fun (i : Fin nA) => ((Enum.list (α := RingBTVW.Fresh.Col k)).map
        fun col => rr (i, col)).flatMap (colWord (N := N) (K := K) d)) ++ rest)
    simp only [Prog.iStepB, List.flatMap_cons, List.map_cons, List.cons_append, List.append_assoc,
      hd_cons, List.tail_cons]
    rw [hstep, takeD_of_length' (len_matEnc2 _), hrows, iStepB_list hN hK B₀ c₀ rr xb l,
      reg_shiftW _ _ _ (len_matEnc2 _)]

end AdvancedEncryption.RingBTVW.Prog
