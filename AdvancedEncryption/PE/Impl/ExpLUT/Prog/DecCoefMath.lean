import PE.Impl.ExpLUT.Prog.DecCoef
import PE.Impl.ExpLUT.Prog.DecAlg
import PE.Impl.ExpLUT.Prog.Words

/-!
# The coefficients computed by `coefC` are those of Lemma 8 (package F4)

At the dimensions `D` with `b = 22` (`W = 2^22`, the lookup width of the universe):

* `σ_kf`: `σ_{g_t}` is `aut N κ_t` with `κ_t = g^{2^t} mod 2N` (`κD`), the length of the template
  register `20 + t`; `autBitsR_eq_σ`: the bits of `j` give `σ_{g^j}`;
* `xInvG_pow_eq`: `X^{−u} = X^{2N − u}`; `rhoBitsR_eq`: the bits of an entry `E` give `X^{val E}`
  (template `42 + b'` of length `ρ_{b'} = 2N − 2^{b'}`, `ρD`);
* `table_eq_val`, `table_last`: the tables of `bpOf (progOf C)` are read off the predicate word;
* **`coefA_eq_alpha`**, **`coefV_eq_vcoef`**: `2^{K−b} Σ_{u<W} termA … = α_{g^j, L_i}` (`i < 15`)
  and `2^{K−b} Σ_{u<W} termV … = v_{g^j, L_15}`, for the stream of table `i` of the word `C`;
* `smul_G_apply`: the entries of `α G`.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### `X⁻¹` -/

theorem dxInvG_mul_monoX {R : Type} [CommRing R] {N : ℕ} (hN : 2 ≤ N) :
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

theorem xInvG_pow_eq {R : Type} [CommRing R] {N : ℕ} (hN : 2 ≤ N) {u : ℕ} (hu : u ≤ 2 * N) :
    xInvG R N ^ u = monoX N ^ (2 * N - u) := by
  calc xInvG R N ^ u = xInvG R N ^ u * monoX N ^ (2 * N) := by rw [monoX_pow_two_n, mul_one]
    _ = (xInvG R N * monoX N) ^ u * monoX N ^ (2 * N - u) := by
        rw [mul_pow, mul_assoc, ← pow_add, show u + (2 * N - u) = 2 * N by omega]
    _ = monoX N ^ (2 * N - u) := by rw [dxInvG_mul_monoX hN, one_pow, one_mul]

/-! ### The bits of an entry -/

/-- The template lengths of `X^{2^{b'}}`: `2N − 2^{b'}`. -/
def ρD (N : ℕ) (b' : ℕ) : ℕ := 2 * N - 2 ^ b'

theorem rhoBitsR_eq {N K : ℕ} (hN : 2 ^ 14 ≤ N) (E : List Bool) (x : RM N K) :
    ∀ n ≤ 14, rhoBitsR (ρD N) E x n =
      monoX N ^ (∑ b' ∈ Finset.range n, if E.getD b' false then 2 ^ b' else 0) * x
  | 0, _ => by simp [rhoBitsR]
  | n + 1, hn => by
    have h2 : 2 ≤ N := le_trans (by norm_num) hN
    rw [rhoBitsR, rhoBitsR_eq hN E x n (by omega), Finset.sum_range_succ]
    by_cases hb : E.getD n false = true
    · have hp : 2 ^ n ≤ 2 * N := by
        have : 2 ^ n ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [if_pos hb, if_pos hb, ρD, xInvG_pow_eq (u := 2 * N - 2 ^ n) h2 (Nat.sub_le _ _),
        Nat.sub_sub_self hp, pow_add, ← mul_assoc,
        mul_comm (monoX N ^ (2 ^ n))]
    · rw [if_neg hb, if_neg hb, add_zero]

theorem sum_getD_eq_val {E : List Bool} (hE : E.length ≤ 14) :
    (∑ b' ∈ Finset.range 14, if E.getD b' false then 2 ^ b' else 0) = val E := by
  rw [val_eq_sum_getD, ← Finset.sum_range_add_sum_Ico _ hE]
  have h0 : ∑ b' ∈ Finset.Ico E.length 14, (if E.getD b' false then 2 ^ b' else 0) = 0 :=
    Finset.sum_eq_zero fun b' hb' => by
      rw [List.getD_eq_default _ _ (by simp at hb'; omega)]; rfl
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun b' _ => ?_
  cases E.getD b' false <;> simp

/-! ### The automorphisms -/

variable (D : Dims)

/-- The template lengths of `σ_{g_t}`: `g^{2^t} mod 2N`. -/
def κD (t : ℕ) : ℕ := gGen D.N (2 ^ D.b) ^ (2 ^ t) % (2 * D.N)

theorem odd_κD (t : ℕ) : Odd (κD D t) := by
  have ho : Odd (gGen D.N (2 ^ D.b) ^ (2 ^ t)) := odd_gGen_pow D.W_dvd _
  rw [κD, Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 D.N)]
  exact Nat.odd_iff.mp ho

theorem κD_pos (t : ℕ) : 0 < κD D t := (odd_κD D t).pos

/-- `σ_{g_t}` is `aut N κ_t`. -/
theorem σ_kf (t : ℕ) (a : Rg D) : (setting D).E.σ ((setting D).kf t) a = aut D.N (κD D t) a := by
  have h : (setting D).E.σ ((setting D).kf t) = (setting D).E.σ (κD D t) := by
    rw [κD, ← ExpRing.σ_mod]; rfl
  rw [h]
  exact autσ_of_odd (odd_κD D t) a

theorem autBitsR_eq_bitAut {J : List Bool} {j : ℕ} (hJ : ∀ t < 22, J.getD t false = j.testBit t)
    (a : Rg D) : ∀ n ≤ 22, autBitsR (κD D) J a n = bitAut (setting D) j a n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [autBitsR, bitAut, hJ n (by omega), autBitsR_eq_bitAut hJ a n (by omega), σ_kf]

/-- **The bits of `j` give `σ_{g^j}`.** -/
theorem autBitsR_eq_σ (hb : D.b = 22) {J : List Bool} {j : ℕ} (hj : j < 2 ^ 22)
    (hJ : ∀ t < 22, J.getD t false = j.testBit t) (a : Rg D) :
    autBitsR (κD D) J a 22 = (setting D).E.σ ((setting D).idx j) a := by
  rw [autBitsR_eq_bitAut D hJ a 22 le_rfl,
    σ_idx_eq_bitAut (S := setting D) a 22 (by rw [setting_b, hb]) j hj]

theorem getD_toBits_22 (j t : ℕ) (ht : t < 22) : (toBits 22 j).getD t false = j.testBit t := by
  rw [getD_toBits]; simp [ht]

/-! ### The tables of the predicate word -/

theorem duOf_toSt_toSym {u : ℕ} (hu : u < 2 ^ 22) :
    (uOf (toSt (u % wSt)) (toSym (u / wSt))).val = u := by
  simp only [uOf, toSt, toSym, wSt, stateBits]
  omega

/-- **A transition table of `bpOf (progOf C)`**: the `14`-bit value at bit `14 (2^22 i + u)`. -/
theorem table_eq_val (C : List Bool) {i u : ℕ} (hi : i < 15) (hu : u < 2 ^ 22) :
    (bpOf (progOf C)).table i u = val ((C.drop (14 * (2 ^ 22 * i + u))).take 14) := by
  have hw : (bpOf (progOf C)).w = wSt := rfl
  rw [BP.table, hw]
  show bpStep (progOf C) i (u % wSt) (u / wSt) = _
  rw [bpStep, dif_pos hi]
  simp only [progOf, readSt]
  rw [duOf_toSt_toSym hu]
  have hl : val ((C.drop (14 * (2 ^ 22 * i + u))).take 14) < 2 ^ 14 :=
    lt_of_lt_of_le (val_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))
  simp only [stateBits, lutBits]
  exact Nat.mod_eq_of_lt hl

/-- **The output table of `bpOf (progOf C)`**: the bit at `210 · 2^22 + u`. -/
theorem table_last (C : List Bool) {u : ℕ} (hu : u < 2 ^ 22) :
    (bpOf (progOf C)).table 15 u = if C.getD (210 * 2 ^ 22 + u) false then 1 else 0 := by
  have hw : (bpOf (progOf C)).w = wSt := rfl
  rw [BP.table, hw]
  show bpStep (progOf C) 15 (u % wSt) (u / wSt) = _
  rw [bpStep, dif_neg (by omega)]
  simp only [progOf]
  simp only [duOf_toSt_toSym hu]

/-! ### The coefficients -/

theorem W_eq_22 (hb : D.b = 22) : (setting D).E.W = 2 ^ 22 := by rw [setting_W, hb]

theorem N_ge (hb : D.b = 22) : 2 ^ 22 < D.N := by have := D.hlt; rw [hb] at this; exact this

/-- The entry `u` of the stream of table `i`. -/
theorem entry_eq (C : List Bool) (i u : ℕ) :
    ((C.drop (14 * 2 ^ 22 * i)).drop (14 * u)).take 14 = (C.drop (14 * (2 ^ 22 * i + u))).take 14 := by
  rw [List.drop_drop]; congr 2; ring

theorem winv_smul (hb : D.b = 22) (x : Rg D) :
    (2 : ZMod (2 ^ D.K - 1)) ^ (D.K - 22) • x = (setting D).E.Winv * x := by
  rw [Algebra.smul_def]
  show _ = algebraMap _ _ ((2 : ZMod (2 ^ D.K - 1)) ^ (D.K - D.b)) * x
  rw [hb]

/-- **The coefficients `α_{g^j, L_i}` (`i < 15`).** -/
theorem coefA_eq_alpha (hb : D.b = 22) (C : List Bool) {i j : ℕ} (hi : i < 15) (hj : j < 2 ^ 22) :
    (2 : ZMod (2 ^ D.K - 1)) ^ (D.K - 22) • ∑ u ∈ Finset.range (2 ^ 22),
        termA (N := D.N) (K := D.K) (κD D) (ρD D.N) (toBits 22 j) (C.drop (14 * 2 ^ 22 * i)) u =
      alphaCoef (S := setting D) ((bpOf (progOf C)).table i) j := by
  have hN := N_ge D hb
  rw [winv_smul D hb, alphaCoef, ExpRing.alpha_def, W_eq_22 D hb]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun u hu => ?_)
  have hu' : u < 2 ^ 22 := Finset.mem_range.mp hu
  rw [termA, rhoBitsR_eq (by
      have : 2 ^ 14 ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega) _ _ 14 le_rfl,
    sum_getD_eq_val (by simp), entry_eq, ← table_eq_val C hi hu',
    autBitsR_eq_σ D hb hj (fun t ht => getD_toBits_22 j t ht),
    xInvG_pow_eq (by omega) (by omega)]
  rfl

/-- **The coefficients `v_{g^j, L_15}`.** -/
theorem coefV_eq_vcoef (hb : D.b = 22) (C : List Bool) {j : ℕ} (hj : j < 2 ^ 22) :
    (2 : ZMod (2 ^ D.K - 1)) ^ (D.K - 22) • ∑ u ∈ Finset.range (2 ^ 22),
        termV (N := D.N) (K := D.K) (κD D) (toBits 22 j) (C.drop (210 * 2 ^ 22)) u =
      vCoef (S := setting D) ((bpOf (progOf C)).table 15) j := by
  have hN := N_ge D hb
  rw [winv_smul D hb, vCoef, ExpRing.vcoef_def, W_eq_22 D hb]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun u hu => ?_)
  have hu' : u < 2 ^ 22 := Finset.mem_range.mp hu
  have hgd : (C.drop (210 * 2 ^ 22)).getD u false = C.getD (210 * 2 ^ 22 + u) false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [termV, table_last C hu', hgd,
    autBitsR_eq_σ D hb hj (fun t ht => getD_toBits_22 j t ht), xInvG_pow_eq (by omega) (by omega)]
  split_ifs <;> simp <;> rfl

/-! ### The matrix `α G` -/

/-- **The entries of `α G`**: `2^i α` on the diagonal blocks, `0` elsewhere. -/
theorem smul_G_apply (α : Rg D) (a : Fin 2) (c : Col D.K) :
    (α • (setting D).G) a c = if a = c.1 then (2 : ZMod (2 ^ D.K - 1)) ^ (c.2 : ℕ) • α else 0 := by
  have hG := G_apply (S := setting D) a c
  calc (α • (setting D).G) a c = α * (setting D).G a c := rfl
    _ = _ := by
      rw [hG]
      split_ifs
      · rw [Algebra.smul_def, mul_comm]; rfl
      · exact mul_zero α

/-! ### The block -/

theorem predLen_bound {i : ℕ} (hi : i < 15) : 14 * 2 ^ 22 * i + 14 * 2 ^ 22 ≤ predLen := by
  have : 14 * 2 ^ 22 * i + 14 * 2 ^ 22 = 14 * 2 ^ 22 * (i + 1) := by ring
  rw [this, predLen]
  calc 14 * 2 ^ 22 * (i + 1) ≤ 14 * 2 ^ 22 * 15 := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 211 * 2 ^ 22 := by norm_num

/-- **The coefficient block computes `α_{g^j, L_i}`** for a predicate word `C` of `predLen` bits,
`i < 15`, `j < W = 2^22` (register `140` holds `toBits 22 j`, register `141` the stream of
table `i`). -/
theorem exec_coefC_alpha (hb : D.b = 22) (w : St)
    (hck : CK D.N D.K (2 ^ 22) 22 (κD D) (ρD D.N) w) {C : List Bool} (hC : C.length = predLen)
    {i j : ℕ} (hi : i < 15) (hj : j < 2 ^ 22) (h140 : w 140 = toBits 22 j)
    (h141 : w 141 = C.drop (14 * 2 ^ 22 * i)) :
    ((exec D.N D.K (coefC false) w) 142).length = D.N * D.K ∧
      decRM D.N D.K ((exec D.N D.K (coefC false) w) 142) =
        alphaCoef (S := setting D) ((bpOf (progOf C)).table i) j ∧
      ∀ r : Fin 200, r.val ≤ 140 → (exec D.N D.K (coefC false) w) r = w r := by
  have hbK : 22 ≤ D.K := hb ▸ D.hb
  obtain ⟨a1, a2, a3⟩ := exec_coefA D.K_pos D.N_pos w hck (fun t _ => κD_pos D t) hbK
    (by rw [h140]; simp) (T := C.drop (14 * 2 ^ 22 * i)) (by
      rw [List.length_drop, hC]; have := predLen_bound hi; omega) h141
  refine ⟨a1, ?_, a3⟩
  rw [a2, h140]
  exact coefA_eq_alpha D hb C hi hj

/-- **The coefficient block computes `v_{g^j, L_15}`** (register `141` the stream of the output
table). -/
theorem exec_coefC_vcoef (hb : D.b = 22) (w : St)
    (hck : CK D.N D.K (2 ^ 22) 22 (κD D) (ρD D.N) w) {C : List Bool} (hC : C.length = predLen)
    {j : ℕ} (hj : j < 2 ^ 22) (h140 : w 140 = toBits 22 j)
    (h141 : w 141 = C.drop (210 * 2 ^ 22)) :
    ((exec D.N D.K (coefC true) w) 142).length = D.N * D.K ∧
      decRM D.N D.K ((exec D.N D.K (coefC true) w) 142) =
        vCoef (S := setting D) ((bpOf (progOf C)).table 15) j ∧
      ∀ r : Fin 200, r.val ≤ 140 → (exec D.N D.K (coefC true) w) r = w r := by
  have hbK : 22 ≤ D.K := hb ▸ D.hb
  obtain ⟨a1, a2, a3⟩ := exec_coefV D.K_pos D.N_pos w hck (fun t _ => κD_pos D t) hbK
    (by rw [h140]; simp) (T := C.drop (210 * 2 ^ 22)) (by
      rw [List.length_drop, hC, predLen]; omega) h141
  refine ⟨a1, ?_, a3⟩
  rw [a2, h140]
  exact coefV_eq_vcoef D hb C hj

/-- The words of `α G`, in the order of `Fin 2 × Col K` (`(a, (r, i)) ↦ 2K a + K r + i`). -/
def gadMatWords (N K : ℕ) [NeZero (2 ^ K - 1)] (x : List Bool) : List (List Bool) :=
  gadWords N K x ++ List.replicate K (List.replicate (N * K) false) ++
    List.replicate K (List.replicate (N * K) false) ++ gadWords N K x

theorem flatten_replicate_replicate (K m : ℕ) :
    (List.replicate K (List.replicate m false)).flatten = List.replicate (K * m) false := by
  induction K with
  | zero => simp
  | succ K ih => rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm,
      List.replicate_add]

theorem flatten_gadMatWords (N K : ℕ) [NeZero (2 ^ K - 1)] (x : List Bool) :
    (gadMatWords N K x).flatten = (gadWords N K x).flatten ++ List.replicate (K * (N * K)) false ++
      List.replicate (K * (N * K)) false ++ (gadWords N K x).flatten := by
  rw [gadMatWords, List.flatten_append, List.flatten_append, List.flatten_append,
    flatten_replicate_replicate]

theorem length_gadMatWords (N K : ℕ) [NeZero (2 ^ K - 1)] (x : List Bool) : (gadMatWords N K x).length = 4 * K := by
  simp [gadMatWords, gadWords]; ring

theorem mem_gadMatWords {N K : ℕ} [NeZero (2 ^ K - 1)] {x : List Bool} (hx : x.length = N * K) {y : List Bool}
    (hy : y ∈ gadMatWords N K x) : y.length = N * K := by
  simp only [gadMatWords, gadWords, List.mem_append, List.mem_map, List.mem_range,
    List.mem_replicate] at hy
  rcases hy with ((⟨k, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨k, _, rfl⟩
  · exact length_rotBW_iter hx k
  · simp
  · simp
  · exact length_rotBW_iter hx k

/-- **The entries of the word of `α G`.** -/
theorem decRM_gadMatWords {x : List Bool} (hx : x.length = D.N * D.K) (a : Fin 2) (c : Col D.K) :
    decRM D.N D.K ((gadMatWords D.N D.K x).getD (2 * D.K * a.val + D.K * c.1.val + c.2.val) []) =
      (decRM D.N D.K x • (setting D).G) a c := by
  rw [smul_G_apply]
  obtain ⟨r, i⟩ := c
  have hi := i.isLt
  have hg : ∀ k, k < D.K → decRM D.N D.K ((gadWords D.N D.K x).getD k []) =
      (2 : ZMod (2 ^ D.K - 1)) ^ k • decRM D.N D.K x := fun k hk => by
    rw [gadWords, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range,
      decRM_rotBW_iter D.K_pos hx]
  have lg : (gadWords D.N D.K x).length = D.K := by simp [gadWords]
  have lz : (List.replicate D.K (List.replicate (D.N * D.K) false)).length = D.K := by simp
  have hz : decRM D.N D.K ((List.replicate D.K (List.replicate (D.N * D.K) false)).getD i []) = 0 := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_replicate]; exact decRM_replicate _ _
  simp only [gadMatWords]
  fin_cases a <;> fin_cases r
  · show decRM D.N D.K (List.getD (_ ++ _ ++ _ ++ _ : List (List Bool)) (2 * D.K * 0 + D.K * 0 + i) []) = _
    rw [if_pos rfl, show 2 * D.K * 0 + D.K * 0 + (i : ℕ) = i by ring, List.append_assoc,
      List.append_assoc, List.getD_append _ _ _ _ (by omega), hg _ hi]
  · show decRM D.N D.K (List.getD (_ ++ _ ++ _ ++ _ : List (List Bool)) (2 * D.K * 0 + D.K * 1 + i) []) = _
    rw [if_neg (by decide), show 2 * D.K * 0 + D.K * 1 + (i : ℕ) = D.K + i by ring,
      List.append_assoc, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), lg,
      show D.K + (i : ℕ) - D.K = i by omega, List.getD_append _ _ _ _ (by omega), hz]
  · show decRM D.N D.K (List.getD (_ ++ _ ++ _ ++ _ : List (List Bool)) (2 * D.K * 1 + D.K * 0 + i) []) = _
    rw [if_neg (by decide), show 2 * D.K * 1 + D.K * 0 + (i : ℕ) = (D.K + D.K) + i by ring,
      List.getD_append _ _ _ _ (by simp only [List.length_append, lg, lz]; omega),
      List.getD_append_right _ _ _ _ (by simp only [List.length_append, lg, lz]; omega),
      List.length_append, lg, lz, show D.K + D.K + (i : ℕ) - (D.K + D.K) = i by omega, hz]
  · show decRM D.N D.K (List.getD (_ ++ _ ++ _ ++ _ : List (List Bool)) (2 * D.K * 1 + D.K * 1 + i) []) = _
    rw [if_pos rfl, show 2 * D.K * 1 + D.K * 1 + (i : ℕ) = (D.K + D.K + D.K) + i by ring,
      List.getD_append_right _ _ _ _ (by simp only [List.length_append, lg, lz]; omega),
      List.length_append, List.length_append,
      lg, lz, show D.K + D.K + D.K + (i : ℕ) - (D.K + D.K + D.K) = i by omega, hg _ hi]

/-- **The block of `α G`**: register `143` holds the words `gadMatWords` of `α` (register `142`). -/
theorem exec_gadC_words {N K : ℕ} [NeZero (2 ^ K - 1)] (hK : 0 < K) {κ ρ : ℕ → ℕ} {W bb : ℕ}
    (w : St) (hck : CK N K W bb κ ρ w) (h142 : (w 142).length = N * K) :
    (exec N K gadC w) 143 = (gadMatWords N K (w 142)).flatten ∧
      ∀ j : Fin 200, j.val < 143 → (exec N K gadC w) j = w j := by
  obtain ⟨h1, h2⟩ := exec_gadC hK w hck h142
  exact ⟨by rw [h1, flatten_gadMatWords], h2⟩

/-- **The increment of `j`**: `toBits 22 j ↦ toBits 22 (j + 1)`. -/
theorem exec_incC_toBits {N K : ℕ} [NeZero (2 ^ K - 1)] (w : St) (h1 : w 1 = [false])
    (h3 : w 3 = true :: List.replicate (N * K - 1) false) {j : ℕ} (h140 : w 140 = toBits 22 j) :
    (exec N K incC w) 140 = toBits 22 (j + 1) ∧
      ∀ r : Fin 200, r.val < 140 → (exec N K incC w) r = w r := by
  obtain ⟨a1, a2⟩ := exec_incC w h1 h3
  exact ⟨by rw [a1, h140, incW_toBits]; rfl, a2⟩

end AdvancedEncryption.ExpLUT.Prog
