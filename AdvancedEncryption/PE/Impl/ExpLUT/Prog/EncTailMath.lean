import PE.Impl.ExpLUT.Prog.EncWordMath
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncTail
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMDot
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMRing

/-! # The message row of the encryption tail agrees with the scheme -/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG
  SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

variable (D : Dims)

/-- Exponent selected by the first `j` attribute bits and their positional weights. -/
def bitExponent (m : ℕ → ℕ) (x : List Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (if hd (x.drop j) then m j else 0) + bitExponent m x j

theorem bitExponent_mul (w : ℕ) (m : ℕ → ℕ) (x : List Bool) (j : ℕ) :
    bitExponent (fun i ↦ w * m i) x j = w * bitExponent m x j := by
  induction j with
  | zero => simp [bitExponent]
  | succ j ih =>
    simp only [bitExponent]
    split_ifs <;> simp [ih, Nat.mul_add]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- The eight big-endian symbol bits select exactly the symbol's numeric value. -/
theorem bitExponent_symbol8 :
    ∀ a : PE.BranchingProgram.Symbol PE.BranchingProgram.w8,
      bitExponent (fun i ↦ 2 ^ (7 - i)) (PE.BranchingProgram.symbolBits _ a) 8 = a.val := by
  decide

/-- The actual conditional rotation loop multiplies by the selected monomial. -/
theorem decRM_rbitsW (hN : 2 ≤ D.N) (m : ℕ → ℕ) (x : List Bool)
    {u : List Bool} (hu : u.length = D.N * D.K) (j : ℕ)
    (hm : ∀ i < j, m i ≤ 2 * D.N) :
    decRM D.N D.K (rbitsW D.K (fun i ↦ 2 * D.N - m i) x j u) =
      (setting D).E.X ^ bitExponent m x j * decRM D.N D.K u := by
  induction j with
  | zero => simp [rbitsW, bitExponent]
  | succ j ih =>
    have hj := ih (fun i hi ↦ hm i (by omega))
    simp only [rbitsW, rbitW, bitExponent]
    split_ifs with hb
    · rw [decRM_rho_sub D hN (by simpa using hu) (hm j (by omega)), hj,
        pow_add, mul_assoc]
    · simpa using hj

/-- A bottom-row block produced by the actual bit-controlled rotations. -/
theorem cbRow_scheme (hN : 2 ≤ D.N) (m : ℕ → ℕ) (x : List Bool)
    (hm : ∀ i < 8, m i ≤ 2 * D.N) (a e : Col D.K → Rg D) (s : Rg D)
    (rest rest' : List Bool) :
    cbRow D.N D.K (fun i ↦ 2 * D.N - m i) (wd D s) x
      ((vecE D (Col D.K)).enc a ++ rest) ((vecE D (Col D.K)).enc e ++ rest')
      (wd D 1) =
      (vecE D (Col D.K)).enc (-(s • a) +
        ((setting D).E.X ^ bitExponent m x 8 • sec s) ᵥ* GD D + e) := by
  unfold cbRow
  rw [MVM.takeD_append_of_length rest (by rw [length_vecE', length_col])]
  apply row_cb D a s _ (by simp [length_wd])
  rw [decRM_notW (by simp [length_wd]),
    decRM_rbitsW D hN m x (length_wd D 1) 8 hm, decRM_wd, mul_one]

/-- The concrete eight-bit attribute block implements `X^(w*x)` in the scheme. -/
theorem cbRow_symbol8 (hN : 2 ≤ D.N) (w : ℕ) (hw : w * 128 ≤ 2 * D.N)
    (x : PE.BranchingProgram.Symbol PE.BranchingProgram.w8)
    (a e : Col D.K → Rg D) (s : Rg D) (rest rest' : List Bool) :
    cbRow D.N D.K (fun i ↦ 2 * D.N - w * 2 ^ (7 - i)) (wd D s)
      (PE.BranchingProgram.symbolBits _ x)
      ((vecE D (Col D.K)).enc a ++ rest) ((vecE D (Col D.K)).enc e ++ rest')
      (wd D 1) = (vecE D (Col D.K)).enc (-(s • a) +
        ((setting D).E.X ^ (w * x.val) • sec s) ᵥ* GD D + e) := by
  have hm : ∀ i < 8, w * 2 ^ (7 - i) ≤ 2 * D.N := by
    intro i _
    have hp : 2 ^ (7 - i) ≤ 128 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le 7 i)
    exact (Nat.mul_le_mul_left w hp).trans hw
  rw [cbRow_scheme D hN _ _ hm, bitExponent_mul, bitExponent_symbol8]

/-- The initial ciphertext row agrees with the scheme, including its gadget subtraction. -/
theorem hRow_c0 (A : Matrix (Fin 2) (Col D.K) (Rg D)) (e : Col D.K → Rg D)
    (s : Rg D) (rest rest' : List Bool) :
    hRow D.N D.K (wd D s) (wd D s) (wd D 1)
      ((matE D (Fin 2) (Col D.K)).enc A ++ rest)
      ((vecE D (Col D.K)).enc e ++ rest') =
      (vecE D (Col D.K)).enc (sec s ᵥ* A - sec s ᵥ* GD D + e) := by
  unfold hRow
  rw [row_mat D A rest s (length_wd D 1) (length_wd D s) e rest',
    decRM_wd, decRM_wd, one_smul]

/-- The message mask decodes to minus the half-modulus encoding of the bit. -/
theorem decRM_cmMask (S : Store 104) (μ : Bool)
    (hμ : S 15 = [μ]) (h1 : S 16 = wd D 1)
    (h0 : S 37 = List.replicate (D.N * D.K) false) :
    decRM D.N D.K (cmMask D.N D.K S) = -(half D * msgR D μ) := by
  have hK := D.K_pos
  have he : D.K - (D.K - 1) = 1 := by omega
  cases μ with
  | false => simp [cmMask, hμ, h0, hd, msgR, SigabaNeo.Tape.RingVM.decRM_replicate]
  | true =>
    simp only [cmMask, hμ, hd_cons, ite_true, h1, msgR, mul_one]
    rw [decRM_notW (length_rotBW _ _ _ (length_wd D 1))]
    have hr := decRM_rotBW (i := D.K - 1) (length_wd D 1) (Nat.sub_le D.K 1)
    rw [he, decRM_wd] at hr
    rw [hr]
    congr 1

/-- With its templates and bit set, the message row is the scheme's `c_m`. -/
theorem row_cm_message (S : Store 104) (μ : Bool) (d : Fin 2 → Rg D) (s em : Rg D)
    (rest rest' : List Bool) (hμ : S 15 = [μ]) (h1 : S 16 = wd D 1)
    (h0 : S 37 = List.replicate (D.N * D.K) false) :
    rowW D.N D.K 1 (wd D s) ((vecE D (Fin 2)).enc d ++ rest)
      (((vecE D (Fin 2)).enc d ++ rest).drop (D.N * D.K))
      (zStream D.N D.K (cmMask D.N D.K S) (S 16)) (wd D em ++ rest') =
        wd D (sec s ⬝ᵥ d + em + half D * msgR D μ) := by
  have hu : (cmMask D.N D.K S).length = D.N * D.K := by
    unfold cmMask
    split_ifs
    · rw [h1, length_notW, length_rotBW _ _ _ (length_wd D 1)]
    · simp [h0]
  rw [row_cm D d rest s em hu (by rw [h1, length_wd]) rest',
    decRM_cmMask D S μ hμ h1 h0, h1, decRM_wd, mul_one, sub_neg_eq_add]

/-- Running the initial-row program shifts the scheme's row into the output tape. -/
theorem run_c0P_scheme (S : Store 104) (h : TailOK D.K D.N S)
    (A : Matrix (Fin 2) (Col D.K) (Rg D)) (e : Col D.K → Rg D) (s : Rg D)
    (rest rest' : List Bool) (hs : S 1 = wd D s) (h1 : S 16 = wd D 1)
    (hA : S 11 = (matE D (Fin 2) (Col D.K)).enc A ++ rest)
    (he : S 12 = (vecE D (Col D.K)).enc e ++ rest') :
    (c0P.run S) 0 = (S 0 ++
      (vecE D (Col D.K)).enc (sec s ᵥ* A - sec s ᵥ* GD D + e)).drop
        ((D.K + D.K) * (D.N * D.K)) := by
  rw [run_c0P D.K_pos h]
  simp only [Function.update_of_ne (by decide : (0 : Fin 104) ≠ 12),
    Function.update_of_ne (by decide : (0 : Fin 104) ≠ 11), Function.update_self]
  rw [hs, h1, hA, he, hRow_c0]

/-- Running the message-row program shifts the correctly masked message into the output tape. -/
theorem run_cmP_scheme (S : Store 104) (h : TailOK D.K D.N S) (μ : Bool)
    (d : Fin 2 → Rg D) (s em : Rg D) (rest rest' : List Bool)
    (hs : S 1 = wd D s) (hμ : S 15 = [μ]) (h1 : S 16 = wd D 1)
    (h0 : S 37 = List.replicate (D.N * D.K) false)
    (hd : S 13 = (vecE D (Fin 2)).enc d ++ rest) (he : S 14 = wd D em ++ rest') :
    (cmP.run S) 0 = (S 0 ++ wd D (sec s ⬝ᵥ d + em + half D * msgR D μ)).drop
      (D.N * D.K) := by
  rw [run_cmP D.K_pos h]
  simp only [Function.update_of_ne (by decide : (0 : Fin 104) ≠ 14),
    Function.update_of_ne (by decide : (0 : Fin 104) ≠ 13), Function.update_self]
  rw [hs, hd, he, row_cm_message D S μ d s em rest rest' hμ h1 h0]

end AdvancedEncryption.ExpLUT.Prog.EncW
