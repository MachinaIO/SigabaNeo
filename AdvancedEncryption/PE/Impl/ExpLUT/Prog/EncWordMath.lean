import PE.Impl.ExpLUT.Prog.EncRow
import PE.Impl.ExpLUT.Prog.SetupP
import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.EncZRow
import SigabaNeo.Lib.Lattices.Homomorphic.BinaryDigits

/-!
# The words of the ciphertext of `Enc`: the ring identities behind the machine

The `Enc` machine writes every component of a ciphertext (ePrint 2026/2539 §5.1) as an encoding row
`rowW N K L s' A₀ A₁ Z E` (`SigabaNeo.Tape.rowW`) whose gadget stream is `zStream u y`
(`z = (u y, u)`, `SigabaNeo.Tape.Prog.zStream`). Here, at the dimensions `D`:

* `blk` of concatenations, of matrix words (`blk_matE_row0`, `blk_matE_row1`) and of the gadget
  stream (**`decRM_blk_zStream`**: entry `c` of `zStream u y` is `((u • sec y) ᵥ* G) c`);
* **`rowW_fam`**: a row whose entries decode to a family `f` is the word of `f`;
* **`decRM_autIt`**: `(σ_g)^j` on words is `σ_{g^j} = σ_{idx j}` of the setting;
* **`decRM_digit_rot`**: the digit `0` of the `i`-fold rotation of a canonical word is the gadget
  digit `i` of the setting (`binaryDigit`);
* `xInvG_pow_eq'`: `X^{−(2N − m)} = X^m` (the monomials `X^{w x_t}` by `rhoJP`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG
  SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix Cslib
open AdvancedEncryption.ExpLUT AdvancedEncryption.ExpLUT.Prog

/-! ### Blocks -/

theorem blk_append_left {n c : ℕ} {x : List Bool} (y : List Bool) (h : (c + 1) * n ≤ x.length) :
    blk n c (x ++ y) = blk n c x := by
  unfold blk
  have h1 : c * n ≤ x.length := le_trans (Nat.mul_le_mul_right n (Nat.le_succ c)) h
  rw [List.drop_append_of_le_length h1]
  have h2 : n ≤ (x.drop (c * n)).length := by rw [List.length_drop]; rw [Nat.add_mul] at h; omega
  rw [takeD_eq_take (by simp only [List.length_append]; omega), takeD_eq_take h2,
    List.take_append_of_le_length h2]

theorem blk_append_right {n c : ℕ} {x : List Bool} (y : List Bool) (h : x.length = c * n) (j : ℕ) :
    blk n (c + j) (x ++ y) = blk n j y := by
  unfold blk
  rw [Nat.add_mul, ← List.drop_drop, List.drop_append_of_le_length (le_of_eq h.symm),
    List.drop_of_length_le (le_of_eq h), List.nil_append]

theorem blk_zero_self {n : ℕ} {x : List Bool} (h : x.length = n) : blk n 0 x = x := by
  unfold blk; simp [takeD_of_length' h]

theorem blk_drop {n m c : ℕ} (x : List Bool) : blk n c (x.drop (m * n)) = blk n (m + c) x := by
  unfold blk; rw [List.drop_drop, Nat.add_mul]

theorem blk_eq_block {n c : ℕ} {x : List Bool} (h : (c + 1) * n ≤ x.length) :
    blk n c x = block n c x := by
  unfold blk block
  rw [takeD_eq_take (by rw [List.length_drop]; rw [Nat.add_mul] at h; omega)]

theorem blk_concatN {n m c : ℕ} {f : ℕ → List Bool} (hf : ∀ i < m, (f i).length = n) (hc : c < m) :
    blk n c (concatN m f) = f c := by
  rw [blk_eq_block (by rw [length_concatN hf]; exact Nat.mul_le_mul_right n hc),
    block_concatN hf, if_pos hc]

variable (D : Dims)

/-- The word of a ring element. -/
abbrev wd (a : Rg D) : List Bool := (rEnc D).enc a

theorem length_wd (a : Rg D) : (wd D a).length = D.N * D.K := (rEnc D).length a

theorem decRM_wd (a : Rg D) : decRM D.N D.K (wd D a) = a := decRM_encRM D.K_pos a

theorem length_vecE' {α : Type} [Enum α] (f : α → Rg D) :
    ((vecE D α).enc f).length = (Enum.list (α := α)).length * (D.N * D.K) := FixedEnc.length _ _

/-- Entry `c` of the word of a family, followed by anything. -/
theorem blk_vecE_append {α : Type} [Enum α] (f : α → Rg D) (rest : List Bool) {c : ℕ}
    (hc : c < (Enum.list (α := α)).length) :
    blk (D.N * D.K) c ((vecE D α).enc f ++ rest) = wd D (f (Enum.list (α := α))[c]) := by
  rw [blk_append_left _ (by rw [length_vecE']; exact Nat.mul_le_mul_right _ hc), blk_vecE D f c hc]

theorem matE_fin2 {α : Type} [Enum α] (M : Matrix (Fin 2) α (Rg D)) :
    (matE D (Fin 2) α).enc M = (vecE D α).enc (M 0) ++ (vecE D α).enc (M 1) := fun_fin2_enc _ M

/-- Entry `c` of row `0` of a matrix word (followed by anything). -/
theorem blk_matE_row0 {α : Type} [Enum α] (M : Matrix (Fin 2) α (Rg D)) (rest : List Bool) {c : ℕ}
    (hc : c < (Enum.list (α := α)).length) :
    blk (D.N * D.K) c ((matE D (Fin 2) α).enc M ++ rest) = wd D (M 0 (Enum.list (α := α))[c]) := by
  rw [matE_fin2, List.append_assoc, blk_vecE_append D _ _ hc]

/-- Entry `c` of row `1` of a matrix word: the word dropped by one row. -/
theorem blk_matE_row1 {α : Type} [Enum α] (M : Matrix (Fin 2) α (Rg D)) (rest : List Bool) {c : ℕ}
    (hc : c < (Enum.list (α := α)).length) :
    blk (D.N * D.K) c (((matE D (Fin 2) α).enc M ++ rest).drop
      ((Enum.list (α := α)).length * (D.N * D.K))) = wd D (M 1 (Enum.list (α := α))[c]) := by
  rw [matE_fin2, List.append_assoc, List.drop_append_of_le_length (le_of_eq (length_vecE' D _).symm),
    List.drop_of_length_le (le_of_eq (length_vecE' D _)), List.nil_append,
    blk_vecE_append D _ _ hc]

/-! ### Zero words -/

theorem decRM_replicate (n : ℕ) (hn : D.N * D.K ≤ n) :
    decRM D.N D.K (List.replicate n false) = 0 := by
  apply ext_coefG
  intro i hi
  rw [coefG_decRM _ hi, coefG_zero]
  have : block D.K i (List.replicate n false) = zeroW D.K := by
    unfold block zeroW
    rw [List.drop_replicate, List.take_replicate]
    congr 1
    have : (i + 1) * D.K ≤ D.N * D.K := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul] at this
    omega
  rw [this, decM_zeroW]

/-- A block past the end of a word reads `0`. -/
theorem decRM_blk_past {x : List Bool} {c : ℕ} (h : x.length ≤ c * (D.N * D.K)) :
    decRM D.N D.K (blk (D.N * D.K) c x) = 0 := by
  unfold blk
  rw [List.drop_of_length_le h, takeD_nil]
  exact decRM_replicate D _ le_rfl

/-! ### The gadget stream -/

theorem getElem_col {c : ℕ} (hc : c < (Enum.list (α := Col D.K)).length) :
    (Enum.list (α := Col D.K))[c] = (⟨c / D.K, by
      rw [Enum.length_prod, len_fin, len_fin] at hc
      exact Nat.div_lt_of_lt_mul (by linarith)⟩, ⟨c % D.K, Nat.mod_lt _ D.K_pos⟩) := by
  have hK := D.K_pos
  have hl : (Enum.list (α := Fin D.K)).length = D.K := len_fin _
  have hc' : c < 2 * D.K := by rw [Enum.length_prod, len_fin, len_fin] at hc; exact hc
  have hd : c / D.K < (Enum.list (α := Fin 2)).length := by
    rw [len_fin]; exact Nat.div_lt_of_lt_mul (by linarith)
  have hm : c % D.K < (Enum.list (α := Fin D.K)).length := by rw [hl]; exact Nat.mod_lt _ hK
  have e : c = c / D.K * (Enum.list (α := Fin D.K)).length + c % D.K := by
    rw [hl, Nat.div_add_mod']
  have h := Enum.getElem_product (Enum.list (α := Fin 2)) (Enum.list (α := Fin D.K)) (c / D.K)
    (c % D.K) hd hm (by rw [← e]; exact hc)
  simp only [← e] at h
  show ((Enum.list (α := Fin 2)).product (Enum.list (α := Fin D.K)))[c] = _
  rw [h, Enum.getElem_fin, Enum.getElem_fin]

theorem length_col : (Enum.list (α := Col D.K)).length = D.K + D.K := by
  rw [Enum.length_prod, len_fin, len_fin]; ring

/-- The gadget matrix of the setting, over `Col K`. -/
noncomputable def GD : Matrix (Fin 2) (Col D.K) (Rg D) := (setting D).G

/-- `g_i = 2^i`. -/
theorem setting_g (i : Fin D.K) : (setting D).D.g i = algebraMap (ZMod D.q) (Rg D) (2 ^ (i : ℕ)) :=
  rfl

/-- **Entry `c` of the gadget stream** of `(u y, u)` is entry `c` of `(u • sec y) G`. -/
theorem decRM_blk_zStream {u y : List Bool} (hu : u.length = D.N * D.K)
    (hy : y.length = D.N * D.K) {c : ℕ} (hc : c < (Enum.list (α := Col D.K)).length) :
    decRM D.N D.K (blk (D.N * D.K) c (zStream D.N D.K u y)) =
      ((decRM D.N D.K u • sec (decRM D.N D.K y)) ᵥ* GD D) (Enum.list (α := Col D.K))[c] := by
  have hK := D.K_pos
  have lm := length_mulRMW D.N D.K u y
  erw [GD, vecMul_G_apply, getElem_col D hc, setting_g]
  simp only
  rw [length_col] at hc
  have l1 : (gzW D.N D.K (mulRMW D.N D.K u y)).length = D.K * (D.N * D.K) := length_gzW lm
  by_cases h1 : c < D.K
  · rw [zStream, blk_append_left _ (by rw [l1]; exact Nat.mul_le_mul_right _ h1), gzW,
      blk_concatN (fun i _ => length_gIt lm i) h1, SigabaNeo.Tape.decRM_gIt hK lm, decRM_mulRMW hu hy]
    have : c / D.K = 0 := Nat.div_eq_of_lt h1
    have e2 : (⟨c / D.K, by omega⟩ : Fin 2) = 0 := Fin.ext this
    rw [e2, Nat.mod_eq_of_lt h1]
    simp only [Pi.smul_apply, sec_zero, smul_eq_mul, Algebra.smul_def, map_pow]
    ring
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp h1)
    have hj : j < D.K := by omega
    rw [zStream, blk_append_right _ l1, gzW,
      blk_concatN (fun i _ => length_gIt hu i) hj, SigabaNeo.Tape.decRM_gIt hK hu]
    have : (D.K + j) / D.K = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ hK, Nat.div_eq_of_lt hj]
    have e2 : (⟨(D.K + j) / D.K, by omega⟩ : Fin 2) = 1 := Fin.ext this
    have e3 : (D.K + j) % D.K = j := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hj]
    rw [e2, e3]
    simp only [Pi.smul_apply, sec_one, smul_eq_mul, mul_one, Algebra.smul_def, map_pow]
    exact mul_comm _ _

/-! ### Rows as families -/

/-- **A row whose entries decode to `f` is the word of `f`.** -/
theorem rowW_fam {α : Type} [Enum α] (f : α → Rg D) {s : List Bool} (hs : s.length = D.N * D.K)
    (a0 a1 z e : List Bool)
    (h : ∀ c (hc : c < (Enum.list (α := α)).length),
      decRM D.N D.K s * decRM D.N D.K (blk (D.N * D.K) c a0) + decRM D.N D.K (blk (D.N * D.K) c a1) -
        decRM D.N D.K (blk (D.N * D.K) c z) + decRM D.N D.K (blk (D.N * D.K) c e) =
          f (Enum.list (α := α))[c]) :
    rowW D.N D.K (Enum.list (α := α)).length s a0 a1 z e = (vecE D α).enc f := by
  rw [rowW_eq D.K_pos hs]
  conv_rhs => rw [vecE_concatN]
  refine concatN_congr fun c hc => ?_
  rw [dif_pos hc, h c hc]
  rfl

/-! ### Iterated automorphisms -/

/-- The template of `σ_g`: `g = 1 + 2N/W`. -/
abbrev gD : ℕ := gGen D.N (2 ^ D.b)

theorem gD_pos : 0 < gD D := by simp [gD, gGen]

theorem setting_σ : (setting D).E.σ = autσ D.N := rfl

theorem setting_idx (j : ℕ) : (setting D).idx j = gD D ^ j := rfl

theorem length_autIt {w : List Bool} (hw : w.length = D.N * D.K) (k : ℕ) :
    ∀ j : ℕ, ((autMW D.N D.K k)^[j] w).length = D.N * D.K
  | 0 => hw
  | j + 1 => by rw [Function.iterate_succ_apply']; exact length_autMW _ _ _ _ D.N_pos

/-- **`(σ_g)^j` on words is `σ_{idx j}`.** -/
theorem decRM_autIt {w : List Bool} (hw : w.length = D.N * D.K) :
    ∀ j : ℕ, decRM D.N D.K ((autMW D.N D.K (gD D))^[j] w) =
      (setting D).E.σ ((setting D).idx j) (decRM D.N D.K w)
  | 0 => by rw [setting_idx, pow_zero, (setting D).E.σ_one]; rfl
  | j + 1 => by
    have hl := length_autIt D hw (gD D) j
    have hg : Odd (gD D) := by simpa using odd_gGen_pow D.W_dvd 1
    rw [Function.iterate_succ_apply', decRM_autMW (gD_pos D) hl, decRM_autIt hw j, setting_σ,
      setting_idx, setting_idx, autσ_of_odd (odd_gGen_pow D.W_dvd j),
      autσ_of_odd (odd_gGen_pow D.W_dvd (j + 1)), aut_aut hg, pow_succ']

/-! ### Digits by rotations -/

theorem rot1_iter_eqE (u : List Bool) : ∀ j ≤ u.length, rot1^[j] u = u.drop j ++ u.take j
  | 0, _ => by simp
  | j + 1, hj => by
    rw [Function.iterate_succ_apply', rot1_iter_eqE u j (by omega)]
    obtain ⟨a, rest, hr⟩ : ∃ a rest, u.drop j = a :: rest := by
      cases h : u.drop j with
      | nil => simp at h; omega
      | cons a rest => exact ⟨a, rest, rfl⟩
    have ha : u[j]'(by omega) = a := by
      have := congrArg List.head? hr
      rw [List.head?_drop] at this
      simpa [List.getElem?_eq_getElem (show j < u.length by omega)] using this
    have hd : u.drop (j + 1) = rest := by
      rw [← List.drop_drop, hr]; rfl
    simp only [rot1, hr, List.cons_append, List.take_succ_cons, List.take_zero, List.tail_cons, hd]
    rw [List.take_succ, List.getElem?_eq_getElem (show j < u.length by omega), ha]
    simp

theorem getD_rot1_iterE {u : List Bool} {j : ℕ} (hj : j < u.length) :
    (rot1^[j] u).getD 0 false = u.getD j false := by
  rw [rot1_iter_eqE u j hj.le]
  obtain ⟨a, rest, hr⟩ : ∃ a rest, u.drop j = a :: rest := by
    cases h : u.drop j with
    | nil => simp at h; omega
    | cons a rest => exact ⟨a, rest, rfl⟩
  have := congrArg List.head? hr
  rw [List.head?_drop] at this
  rw [hr, List.cons_append, List.getD_cons_zero, List.getD_eq_getElem?_getD, this]
  rfl

theorem digitRW_zero_rotBWE {N K i : ℕ} {x : List Bool} (hx : x.length = N * K) (hi : i < K) :
    digitRW N K 0 (rotBW N K i x) = digitRW N K i x := by
  unfold digitRW
  apply concatN_congr
  intro t ht
  rw [rotBW, block_concatN (fun t' ht' => by rw [length_rot1_iter, length_block hx ht']),
    if_pos ht, getD_rot1_iterE (by rw [length_block hx ht]; exact hi)]

theorem getD_toBitsE : ∀ (K n i : ℕ), (toBits K n).getD i false = (decide (i < K) && n.testBit i)
  | 0, n, i => by simp [toBits]
  | K + 1, n, 0 => by simp [toBits, Nat.testBit_zero]
  | K + 1, n, i + 1 => by
    rw [toBits, List.getD_cons_succ, getD_toBitsE K (n / 2) i, Nat.testBit_div_two]
    simp

theorem block_encRME {N K t : ℕ} (a : Cslib.Negacyclic (ZMod (2 ^ K - 1)) N) (ht : t < N) :
    block K t (encRM N K a) = encM K (coefG a t) := by
  rw [encRM, block_concatN (fun _ _ => length_encM _ _), if_pos ht]

/-- **The digits of a canonical word are the binary digits.** -/
theorem decRM_digitRW_encRM {N K : ℕ} [NeZero (2 ^ K - 1)] (hK : 0 < K)
    (a : Cslib.Negacyclic (ZMod (2 ^ K - 1)) N) (i : ℕ) :
    decRM N K (digitRW N K i (encRM N K a)) = binaryDigit a i := by
  rw [decRM_digitRW hK]
  ext t
  rw [Cslib.Negacyclic.coeffs_ofCoeffs, coeffs_binaryDigit, block_encRME _ t.isLt, encM,
    getD_toBitsE, coefG_val]
  have hv : ((a.coeffs t).val) < 2 ^ K := by
    have := ZMod.val_lt (a.coeffs t)
    have : 2 ^ K - 1 < 2 ^ K := Nat.sub_lt (by positivity) one_pos
    omega
  by_cases hi : i < K
  · simp [hi]
  · simp only [hi, decide_false, Bool.false_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem rotBW_one_iter {N K : ℕ} {x : List Bool} (hx : x.length = N * K) :
    ∀ i, (rotBW N K 1)^[i] x = rotBW N K i x
  | 0 => by
    unfold rotBW
    simp only [Function.iterate_zero, id]
    rw [concatN_block hx]
  | i + 1 => by
    rw [Function.iterate_succ_apply', rotBW_one_iter hx i, ← rotBW_succ hx i]
    rfl

/-- **The digit `i` of a ring element, by `i` rotations and the digit `0`.** -/
theorem decRM_digit_rot (a : Rg D) (i : Fin D.K) :
    decRM D.N D.K (digitRW D.N D.K 0 ((rotBW D.N D.K 1)^[i.val] (wd D a))) = (setting D).D.d a i := by
  rw [rotBW_one_iter (length_wd D a), digitRW_zero_rotBWE (length_wd D a) i.isLt]
  exact decRM_digitRW_encRM D.K_pos a i

theorem length_digitRW (N K i : ℕ) (w : List Bool) : (digitRW N K i w).length = N * K :=
  length_concatN fun _ _ => length_bitW _ _

/-! ### Monomials -/

theorem xInvG_mul_monoXE {R : Type} [CommRing R] {N : ℕ} (hN : 2 ≤ N) :
    xInvG R N * monoX N = 1 := by
  rw [← rhoG_eq_mul]
  apply ext_coefG
  intro i hi
  rw [coefG_rhoG _ hi]
  have hX : ∀ t < N, coefG (monoX N : Cslib.Negacyclic R N) t = if t = 1 then 1 else 0 :=
    fun t ht => by
      rw [coefG_of_lt _ ht, ← pow_one (monoX N), coeffs_monoX_pow_of_lt (by omega)]
  rw [coefG_of_lt _ hi, Cslib.Negacyclic.coeffs_one]
  by_cases hi1 : i + 1 < N
  · rw [if_pos hi1, hX _ hi1]
    by_cases h0 : i = 0 <;> simp [h0]
  · rw [if_neg hi1, hX 0 (by omega)]
    have : i ≠ 0 := by omega
    simp [this]

/-- `X^{−(2N − m)} = X^m`. -/
theorem xInvG_pow_sub {R : Type} [CommRing R] {N : ℕ} (hN : 2 ≤ N) {m : ℕ} (hm : m ≤ 2 * N) :
    xInvG R N ^ (2 * N - m) = monoX N ^ m := by
  calc xInvG R N ^ (2 * N - m) = xInvG R N ^ (2 * N - m) * monoX N ^ (2 * N) := by
        rw [monoX_pow_two_n, mul_one]
    _ = (xInvG R N * monoX N) ^ (2 * N - m) * monoX N ^ m := by
        rw [mul_pow, mul_assoc, ← pow_add, show 2 * N - m + m = 2 * N by omega]
    _ = monoX N ^ m := by rw [xInvG_mul_monoXE hN, one_pow, one_mul]

theorem setting_X : (setting D).E.X = monoX D.N := rfl

/-- **`X^{−(2N − m)}` on words multiplies by `X^m`.** -/
theorem decRM_rho_sub (hN : 2 ≤ D.N) {w : List Bool} (hw : w.length = D.N * D.K) {m : ℕ}
    (hm : m ≤ 2 * D.N) :
    decRM D.N D.K ((rhoMW D.K)^[2 * D.N - m] w) = (setting D).E.X ^ m * decRM D.N D.K w := by
  rw [decRM_rhoMW_iter_mul D.N_pos hw, xInvG_pow_sub hN hm, setting_X]

theorem length_rho_iter {K : ℕ} {w : List Bool} (hK : K ≤ w.length) (j : ℕ) :
    ((rhoMW K)^[j] w).length = w.length := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', rhoMW_eq (by rw [ih]; exact hK)]
    simp [ih, notW]
    omega

/-! ### The rows of the ciphertext -/

theorem length_zStream {u y : List Bool} (hu : u.length = D.N * D.K) :
    (zStream D.N D.K u y).length = (D.K + D.K) * (D.N * D.K) := by
  rw [zStream, List.length_append, length_gzW (length_mulRMW _ _ _ _), length_gzW hu]; ring

theorem vecMul_sec (s : Rg D) {α : Type} (M : Matrix (Fin 2) α (Rg D)) (c : α) :
    (sec s ᵥ* M) c = s * M 0 c + M 1 c := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, sec]

/-- **An encoding row of a `2 × 2K` matrix stream**: `s A − (u • (y, 1)) G + e`. -/
theorem row_mat (M : Matrix (Fin 2) (Col D.K) (Rg D)) (rest : List Bool) (s : Rg D)
    {u y : List Bool} (hu : u.length = D.N * D.K) (hy : y.length = D.N * D.K)
    (e : Col D.K → Rg D) (rest' : List Bool) :
    rowW D.N D.K (D.K + D.K) (wd D s) ((matE D (Fin 2) (Col D.K)).enc M ++ rest)
      (((matE D (Fin 2) (Col D.K)).enc M ++ rest).drop ((D.K + D.K) * (D.N * D.K)))
      (zStream D.N D.K u y) ((vecE D (Col D.K)).enc e ++ rest') =
      (vecE D (Col D.K)).enc (sec s ᵥ* M -
        (decRM D.N D.K u • sec (decRM D.N D.K y)) ᵥ* GD D + e) := by
  rw [← length_col D]
  refine rowW_fam D _ (length_wd D s) _ _ _ _ fun c hc => ?_
  rw [blk_matE_row0 D M rest hc, blk_matE_row1 D M rest hc, decRM_blk_zStream D hu hy hc,
    blk_vecE_append D e rest' hc, decRM_wd, decRM_wd, decRM_wd, decRM_wd]
  simp only [Pi.add_apply, Pi.sub_apply, vecMul_sec]

/-- **The row of `b`**: `s B + e_b` (a gadget term decoding to `0`). -/
theorem row_b (B : Matrix (Fin 2) (BCol (Wb D) D.K) (Rg D)) (rest : List Bool) (s : Rg D)
    {u y : List Bool} (hu : u.length = D.N * D.K) (hy : y.length = D.N * D.K)
    (hu0 : decRM D.N D.K u = 0) (e : BCol (Wb D) D.K → Rg D) (rest' : List Bool) :
    rowW D.N D.K (Enum.list (α := BCol (Wb D) D.K)).length (wd D s)
      ((matE D (Fin 2) (BCol (Wb D) D.K)).enc B ++ rest)
      (((matE D (Fin 2) (BCol (Wb D) D.K)).enc B ++ rest).drop
        ((Enum.list (α := BCol (Wb D) D.K)).length * (D.N * D.K)))
      (zStream D.N D.K u y) ((vecE D (BCol (Wb D) D.K)).enc e ++ rest') =
      (vecE D (BCol (Wb D) D.K)).enc (sec s ᵥ* B + e) := by
  refine rowW_fam D _ (length_wd D s) _ _ _ _ fun c hc => ?_
  have hz : decRM D.N D.K (blk (D.N * D.K) c (zStream D.N D.K u y)) = 0 := by
    by_cases h2 : c < (Enum.list (α := Col D.K)).length
    · rw [decRM_blk_zStream D hu hy h2, hu0, zero_smul, Matrix.zero_vecMul]; rfl
    · rw [length_col] at h2
      exact decRM_blk_past D (by rw [length_zStream D hu]; exact Nat.mul_le_mul_right _ (by omega))
  rw [blk_matE_row0 D B rest hc, blk_matE_row1 D B rest hc, hz, blk_vecE_append D e rest' hc,
    decRM_wd, decRM_wd, decRM_wd, decRM_wd]
  simp only [Pi.add_apply, vecMul_sec, sub_zero]

theorem blk_notW {n c : ℕ} {w : List Bool} (h : (c + 1) * n ≤ w.length) :
    blk n c (notW w) = notW (blk n c w) := by
  rw [blk_eq_block h, blk_eq_block (by simpa [notW] using h), block_notW]

/-- **The bottom row of `C^in_t`**: `−s a + (X • (s, 1)) G + e`, from `A₀ = ¬a`, `A₁ = 0` and a
gadget term with `u = −X`. -/
theorem row_cb (a : Col D.K → Rg D) (s X : Rg D) {u : List Bool} (hu : u.length = D.N * D.K)
    (huX : decRM D.N D.K u = -X) (e : Col D.K → Rg D) (rest : List Bool) :
    rowW D.N D.K (D.K + D.K) (wd D s) (notW ((vecE D (Col D.K)).enc a)) []
      (zStream D.N D.K u (wd D s)) ((vecE D (Col D.K)).enc e ++ rest) =
      (vecE D (Col D.K)).enc (-(s • a) + (X • sec s) ᵥ* GD D + e) := by
  rw [← length_col D]
  refine rowW_fam D _ (length_wd D s) _ _ _ _ fun c hc => ?_
  have h0 : decRM D.N D.K (blk (D.N * D.K) c []) = 0 := decRM_blk_past D (by simp)
  rw [blk_notW (by rw [length_vecE']; exact Nat.mul_le_mul_right _ hc),
    decRM_notW (by rw [length_blk]), blk_vecE D a c hc, decRM_wd, h0,
    decRM_blk_zStream D hu (length_wd D s) hc, huX, decRM_wd, blk_vecE_append D e rest hc, decRM_wd]
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_smul, Matrix.neg_vecMul,
    decRM_wd]
  ring

/-- **The row of `c_m`**: `s d₁ + d₂ + e_m − u y`. -/
theorem row_cm (d : Fin 2 → Rg D) (rest : List Bool) (s em : Rg D) {u y : List Bool}
    (hu : u.length = D.N * D.K) (hy : y.length = D.N * D.K) (rest' : List Bool) :
    rowW D.N D.K 1 (wd D s) ((vecE D (Fin 2)).enc d ++ rest)
      (((vecE D (Fin 2)).enc d ++ rest).drop (D.N * D.K)) (zStream D.N D.K u y) (wd D em ++ rest') =
      wd D (sec s ⬝ᵥ d + em - decRM D.N D.K u * decRM D.N D.K y) := by
  have h1 : 0 < (Enum.list (α := Fin 2)).length := by rw [len_fin]; norm_num
  have h2 : 1 < (Enum.list (α := Fin 2)).length := by rw [len_fin]; norm_num
  have hc0 : 0 < (Enum.list (α := Col D.K)).length := by rw [length_col]; have := D.K_pos; omega
  rw [rowW_eq D.K_pos (length_wd D s)]
  simp only [concatN, List.nil_append]
  rw [blk_vecE_append D d rest h1,
    show ((vecE D (Fin 2)).enc d ++ rest).drop (D.N * D.K) =
      ((vecE D (Fin 2)).enc d ++ rest).drop (1 * (D.N * D.K)) by rw [one_mul],
    blk_drop, blk_vecE_append D d rest h2, decRM_blk_zStream D hu hy hc0,
    blk_append_left _ (by rw [length_wd]; omega), blk_zero_self (length_wd D em), decRM_wd, decRM_wd, decRM_wd, decRM_wd,
    Enum.getElem_fin, Enum.getElem_fin, getElem_col D hc0]
  erw [GD, vecMul_G_apply]
  simp only [setting_g, dotProduct, Fin.sum_univ_two, sec, Pi.smul_apply, smul_eq_mul]
  simp
  show encRM D.N D.K _ = encRM D.N D.K _
  congr 1
  ring

end AdvancedEncryption.ExpLUT.Prog.EncW
