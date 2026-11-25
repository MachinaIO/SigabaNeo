import PE.Impl.ExpLUT.Prog.EncAutPhase

/-! # The attribute ciphertext and its digit-encryption phase -/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram

variable (D : Dims)

/-- Later attribute symbols do not affect the exponent selected by a prefix. -/
theorem bitExponent_append (m : ℕ → ℕ) (x rest : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    bitExponent m (x ++ rest) j = bitExponent m x j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j < x.length := by omega
    have hh : hd ((x ++ rest).drop j) = hd (x.drop j) := by
      rw [List.drop_eq_getElem_cons (by simp; omega), List.drop_eq_getElem_cons hj']
      simp [hd, List.getElem_append_left hj', List.getElem?_eq_getElem hj']
    simp only [bitExponent, hh, ih (by omega)]

/-- The bottom row for one symbol, with all source queues allowed to have suffixes. -/
theorem cbRow_symbol8_append (hN : 2 ≤ D.N) (w : ℕ) (hw : w * 128 ≤ 2 * D.N)
    (x : Symbol w8) (a e : Col D.K → Rg D) (s : Rg D) (restX restA restE : List Bool) :
    cbRow D.N D.K (fun i ↦ 2 * D.N - w * 2 ^ (7 - i)) (wd D s)
      (symbolBits w8 x ++ restX) ((vecE D (Col D.K)).enc a ++ restA)
      ((vecE D (Col D.K)).enc e ++ restE) (wd D 1) =
      (vecE D (Col D.K)).enc (-(s • a) +
        ((setting D).E.X ^ (w * x.val) • sec s) ᵥ* GD D + e) := by
  have hm : ∀ i < 8, w * 2 ^ (7 - i) ≤ 2 * D.N := by
    intro i _
    exact (Nat.mul_le_mul_left w
      (show 2 ^ (7 - i) ≤ 128 from Nat.pow_le_pow_right (by decide) (Nat.sub_le 7 i))).trans hw
  rw [cbRow_scheme D hN _ _ hm,
    bitExponent_append _ _ _ _ (by exact (PE.BranchingProgram.length_symbolBits w8 x).ge),
    bitExponent_mul, bitExponent_symbol8]

/-- The mathematical bottom row of the current attribute ciphertext. -/
noncomputable def inputBottom (w : ℕ) (x : Symbol w8) (s : Rg D)
    (a e : Col D.K → Rg D) : Col D.K → Rg D :=
  -(s • a) + ((setting D).E.X ^ (w * x.val) • sec s) ᵥ* GD D + e

/-- The two shifted rows form the canonical codec of `cinMat`. -/
theorem assemble_cinMat (a b : Col D.K → Rg D) (z4 rest : List Bool)
    (hz4 : z4.length = (D.K + D.K + (D.K + D.K)) * (D.N * D.K)) :
    (((z4 ++ takeD ((D.K + D.K) * (D.N * D.K))
      ((vecE D (Col D.K)).enc a ++ rest)).drop ((D.K + D.K) * (D.N * D.K))) ++
        takeD ((D.K + D.K) * (D.N * D.K)) ((vecE D (Col D.K)).enc b)).drop
          ((D.K + D.K) * (D.N * D.K)) =
      (matE D (Fin 2) (Col D.K)).enc (cinMat (S := setting D) a b) := by
  have hl (v : Col D.K → Rg D) : ((vecE D (Col D.K)).enc v).length =
      (D.K + D.K) * (D.N * D.K) := by rw [length_vecE', length_col]
  rw [MVM.takeD_append_of_length rest (hl a), takeD_of_length' (hl b)]
  have hn : (D.K + D.K) * (D.N * D.K) ≤ z4.length := by simp only [Nat.add_mul] at hz4 ⊢; omega
  rw [List.drop_append_of_le_length hn, List.append_assoc, List.drop_append_of_le_length
    (by rw [List.length_drop]; simp only [Nat.add_mul] at hz4 ⊢; omega)]
  rw [List.drop_drop, ← Nat.add_mul, ← hz4, List.drop_length, List.nil_append]
  have hc : cinMat (S := setting D) a b = ![a, b] := rfl
  rw [hc]
  exact (matE_fin2 D (α := Col D.K) (show Matrix (Fin 2) (Col D.K) (Rg D) from ![a, b])).symm

/-- A complete attribute digit-encryption step consumes every source block and writes its codec. -/
theorem ciStep_encoded (hN : 2 ≤ D.N) (w : ℕ) (hw : w * 128 ≤ 2 * D.N)
    (x : Symbol w8) (s : Rg D) (a e : Col D.K → Rg D)
    (A : Dig D.K → Fin 2 → Col D.K → Rg D) (E : Dig D.K → Col D.K → Rg D)
    (z2 z4 out restX restA restE restCopy restM restD : List Bool)
    (hz2 : z2.length = (D.K + D.K) * (D.N * D.K))
    (hz4 : z4.length = (D.K + D.K + (D.K + D.K)) * (D.N * D.K))
    (hout : (D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K))) ≤ out.length) :
    ciStep D.N D.K (fun i ↦ 2 * D.N - w * 2 ^ (7 - i)) (wd D s) (wd D 1) z2 z4
      (D.K + D.K + (D.K + D.K))
      (symbolBits w8 x ++ restX, (vecE D (Col D.K)).enc a ++ restA,
        (vecE D (Col D.K)).enc e ++ restE, (vecE D (Col D.K)).enc a ++ restCopy,
        (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc A ++ restM,
        (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc E ++ restD, out) =
      (restX, restA, restE, restCopy, restM, restD,
        (out ++ (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc
          (digitRows D (wd D s) (cinMat (S := setting D) a (inputBottom D w x s a e)) A E)).drop
            ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K))))) := by
  have hl (v : Col D.K → Rg D) : ((vecE D (Col D.K)).enc v).length =
      (D.K + D.K) * (D.N * D.K) := by rw [length_vecE', length_col]
  have dropV (v : Col D.K → Rg D) (r : List Bool) :
      ((vecE D (Col D.K)).enc v ++ r).drop ((D.K + D.K) * (D.N * D.K)) = r := by
    rw [← hl v, List.drop_left]
  have hx : (symbolBits w8 x ++ restX).drop 8 = restX := by
    have hlx : (symbolBits w8 x).length = 8 := PE.BranchingProgram.length_symbolBits w8 x
    rw [← hlx, List.drop_left]
  have hb := cbRow_symbol8_append D hN w hw x a e s restX restA restE
  change _ = (vecE D (Col D.K)).enc (inputBottom D w x s a e) at hb
  have hd := deSteps_encoded D (length_wd D s)
    (cinMat (S := setting D) a (inputBottom D w x s a e)) A E out [] restM restD hout
  simp only [List.append_nil] at hd
  dsimp only [ciStep]
  rw [hb, ← hz2, List.drop_left]
  rw [hz2, assemble_cinMat D a _ z4 restCopy hz4, hd]
  simp only [hx, dropV]

/-- Only the first `j` rotation templates are read. -/
theorem rbitsW_congr_prefix (K : ℕ) (τ κ : ℕ → ℕ) (x u : List Bool) (j : ℕ)
    (h : ∀ i < j, τ i = κ i) : rbitsW K τ x j u = rbitsW K κ x j u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [rbitsW, h j (by omega), ih (fun i hi ↦ h i (by omega))]

/-- One attribute round reads precisely the eight symbol templates. -/
theorem ciStep_congr_templates (N K : ℕ) (τ κ : ℕ → ℕ) (s one z2 z4 : List Bool)
    (entries : ℕ) (h : ∀ i < 8, τ i = κ i)
    (v : List Bool × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) :
    ciStep N K τ s one z2 z4 entries v = ciStep N K κ s one z2 z4 entries v := by
  obtain ⟨x, a, e, ac, A, E, out⟩ := v
  dsimp only [ciStep, cbRow]
  rw [rbitsW_congr_prefix K τ κ x one 8 h]

/-- The actual attribute-round program consumes one symbol and writes its digit ciphertext. -/
theorem run_cinBody_encoded (S : Store 104) (h : TailOK D.K D.N S)
    (hN : 2 ≤ D.N) (w : ℕ) (hw : w * 128 ≤ 2 * D.N)
    (x : Symbol w8) (s : Rg D) (a e : Col D.K → Rg D)
    (A : Dig D.K → Fin 2 → Col D.K → Rg D) (E : Dig D.K → Col D.K → Rg D)
    (restX restA restE restCopy restM restD counter : List Bool)
    (hs : S 1 = wd D s) (h1 : S 16 = wd D 1)
    (hτ : ∀ i < 8, τT S i = 2 * D.N - w * 2 ^ (7 - i))
    (hentries : (S 34).length = D.K + D.K + (D.K + D.K))
    (hx : S 3 = symbolBits w8 x ++ restX)
    (ha : S 5 = (vecE D (Col D.K)).enc a ++ restA)
    (he : S 8 = (vecE D (Col D.K)).enc e ++ restE)
    (hcopy : S 6 = (vecE D (Col D.K)).enc a ++ restCopy)
    (hA : S 9 = (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc A ++ restM)
    (hE : S 10 = (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc E ++ restD)
    (hout : (D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K))) ≤ (S 0).length) :
    cinBody.run (Function.update S 39 counter) = Function.update (ciG S
      (restX, restA, restE, restCopy, restM, restD,
        (S 0 ++ (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc
          (digitRows D (wd D s) (cinMat (S := setting D) a (inputBottom D w x s a e)) A E)).drop
            ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K))))))
      39 counter := by
  rw [run_cinBody D.K_pos h counter,
    ciStep_congr_templates D.N D.K (τT S) _ _ _ _ _ _ hτ,
    hs, h1, hentries, hx, ha, he, hcopy, hA, hE,
    ciStep_encoded D hN w hw x s a e A E (S 30) (S 32) (S 0)
      restX restA restE restCopy restM restD h.h30 h.h32 hout]

/-- The digit rows of one attribute ciphertext. -/
noncomputable def inputDigits (w : ℕ) (s : Rg D) (x : Symbol w8)
    (a e : Col D.K → Rg D) (A : Dig D.K → Fin 2 → Col D.K → Rg D)
    (E : Dig D.K → Col D.K → Rg D) : Dig D.K → Col D.K → Rg D :=
  digitRows D (wd D s) (cinMat (S := setting D) a (inputBottom D w x s a e)) A E

/-- Each attribute block has the exact fixed length reserved by the machine. -/
theorem length_digitFamily (F : Dig D.K → Col D.K → Rg D) :
    ((FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc F).length =
      (D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K))) := by
  rw [FixedEnc.length]
  simp only [Dig, Enum.length_prod, len_fin]
  ring

/-- The outer attribute loop consumes every position and writes its complete digit-family stream. -/
theorem ciStep_stream (hN : 2 ≤ D.N) (w : ℕ) (hw : w * 128 ≤ 2 * D.N) (s : Rg D)
    (x : ℕ → Symbol w8) (a e : ℕ → Col D.K → Rg D)
    (A : ℕ → Dig D.K → Fin 2 → Col D.K → Rg D)
    (E : ℕ → Dig D.K → Col D.K → Rg D)
    (z2 z4 : List Bool) (hz2 : z2.length = (D.K + D.K) * (D.N * D.K))
    (hz4 : z4.length = (D.K + D.K + (D.K + D.K)) * (D.N * D.K))
    (j n : ℕ) (out restX restA restE restCopy restM restD : List Bool)
    (hout : n * ((D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K)))) ≤ out.length) :
    (ciStep D.N D.K (fun i ↦ 2 * D.N - w * 2 ^ (7 - i)) (wd D s) (wd D 1) z2 z4
      (D.K + D.K + (D.K + D.K)))^[n]
      (blockStream (fun t ↦ symbolBits w8 (x t)) j n ++ restX,
        blockStream (fun t ↦ (vecE D (Col D.K)).enc (a t)) j n ++ restA,
        blockStream (fun t ↦ (vecE D (Col D.K)).enc (e t)) j n ++ restE,
        blockStream (fun t ↦ (vecE D (Col D.K)).enc (a t)) j n ++ restCopy,
        blockStream (fun t ↦ (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc (A t)) j n ++ restM,
        blockStream (fun t ↦ (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc (E t)) j n ++ restD,
        out) = (restX, restA, restE, restCopy, restM, restD,
          (out ++ blockStream (fun t ↦ (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc
            (inputDigits D w s (x t) (a t) (e t) (A t) (E t))) j n).drop
              (n * ((D.K + D.K + (D.K + D.K)) *
                (D.K * ((D.K + D.K) * (D.N * D.K)))))) := by
  induction n generalizing j out with
  | zero => simp
  | succ n ih =>
    have hn : (D.K + D.K + (D.K + D.K)) *
        (D.K * ((D.K + D.K) * (D.N * D.K))) ≤ out.length := by
      rw [Nat.succ_mul] at hout; omega
    have hlen : ((out ++ (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc
        (inputDigits D w s (x j) (a j) (e j) (A j) (E j))).drop
          ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K))))).length =
          out.length := by
      rw [List.length_drop, List.length_append, length_digitFamily]; omega
    rw [Function.iterate_succ_apply]
    simp only [blockStream_succ, List.append_assoc]
    rw [ciStep_encoded D hN w hw (x j) s (a j) (e j) (A j) (E j) z2 z4 out
      _ _ _ _ _ _ hz2 hz4 hn]
    dsimp only [inputDigits] at hlen
    rw [ih (j + 1) _ (by rw [hlen]; rw [Nat.succ_mul] at hout; omega)]
    rw [List.drop_append_of_le_length hn, List.append_assoc]
    conv_rhs =>
      rw [Nat.succ_mul,
        Nat.add_comm (n * ((D.K + D.K + (D.K + D.K)) *
          (D.K * ((D.K + D.K) * (D.N * D.K)))))
          ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K)))),
        ← List.drop_drop, List.drop_append_of_le_length hn]
    rfl

/-- The complete executable attribute loop, with explicit source and output streams. -/
theorem run_cinP_stream (S : Store 104) (h : TailOK D.K D.N S)
    (hN : 2 ≤ D.N) (w : ℕ) (hw : w * 128 ≤ 2 * D.N) (s : Rg D)
    (x : ℕ → Symbol w8) (a e : ℕ → Col D.K → Rg D)
    (A : ℕ → Dig D.K → Fin 2 → Col D.K → Rg D)
    (E : ℕ → Dig D.K → Col D.K → Rg D)
    (j n : ℕ) (restX restA restE restCopy restM restD : List Bool)
    (hs : S 1 = wd D s) (h1 : S 16 = wd D 1)
    (hτ : ∀ i < 8, τT S i = 2 * D.N - w * 2 ^ (7 - i))
    (hentries : (S 34).length = D.K + D.K + (D.K + D.K)) (hcount : (S 35).length = n)
    (hx : S 3 = blockStream (fun t ↦ symbolBits w8 (x t)) j n ++ restX)
    (ha : S 5 = blockStream (fun t ↦ (vecE D (Col D.K)).enc (a t)) j n ++ restA)
    (he : S 8 = blockStream (fun t ↦ (vecE D (Col D.K)).enc (e t)) j n ++ restE)
    (hcopy : S 6 = blockStream (fun t ↦ (vecE D (Col D.K)).enc (a t)) j n ++ restCopy)
    (hA : S 9 = blockStream (fun t ↦
      (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc (A t)) j n ++ restM)
    (hE : S 10 = blockStream (fun t ↦
      (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc (E t)) j n ++ restD)
    (hout : n * ((D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K)))) ≤ (S 0).length) :
    cinP.run S = ciG S (restX, restA, restE, restCopy, restM, restD,
      (S 0 ++ blockStream (fun t ↦ (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc
        (inputDigits D w s (x t) (a t) (e t) (A t) (E t))) j n).drop
          (n * ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K)))))) := by
  have hf : ciStep D.N D.K (τT S) (S 1) (S 16) (S 30) (S 32) (S 34).length =
      ciStep D.N D.K (fun i ↦ 2 * D.N - w * 2 ^ (7 - i))
        (S 1) (S 16) (S 30) (S 32) (S 34).length :=
    funext (ciStep_congr_templates D.N D.K _ _ _ _ _ _ _ hτ)
  rw [run_cinP D.K_pos h, hf, hs, h1, hentries, hcount, hx, ha, he, hcopy, hA, hE,
    ciStep_stream D hN w hw s x a e A E (S 30) (S 32) h.h30 h.h32 j n
      (S 0) restX restA restE restCopy restM restD hout]

/-- One bottom-row round consumes the symbol, public row, and error row. -/
theorem cbStep_encoded (hN : 2 ≤ D.N) (w : ℕ) (hw : w * 128 ≤ 2 * D.N)
    (x : Symbol w8) (s : Rg D) (a e : Col D.K → Rg D)
    (out restX restA restE : List Bool) :
    cbStep D.N D.K (fun i ↦ 2 * D.N - w * 2 ^ (7 - i)) (wd D s) (wd D 1)
      (symbolBits w8 x ++ restX, (vecE D (Col D.K)).enc a ++ restA,
        (vecE D (Col D.K)).enc e ++ restE, out) =
      (restX, restA, restE, (out ++ (vecE D (Col D.K)).enc
        (inputBottom D w x s a e)).drop ((D.K + D.K) * (D.N * D.K))) := by
  have dropV (v : Col D.K → Rg D) (r : List Bool) :
      ((vecE D (Col D.K)).enc v ++ r).drop ((D.K + D.K) * (D.N * D.K)) = r := by
    have hl : ((vecE D (Col D.K)).enc v).length = (D.K + D.K) * (D.N * D.K) := by
      rw [length_vecE', length_col]
    rw [← hl, List.drop_left]
  have hx : (symbolBits w8 x ++ restX).drop 8 = restX := by
    have hl : (symbolBits w8 x).length = 8 := PE.BranchingProgram.length_symbolBits w8 x
    rw [← hl, List.drop_left]
  dsimp only [cbStep]
  rw [cbRow_symbol8_append D hN w hw x a e s restX restA restE, hx, dropV, dropV]
  rfl

/-- All attribute bottom rows, with their source queues consumed in lockstep. -/
theorem cbStep_stream (hN : 2 ≤ D.N) (w : ℕ) (hw : w * 128 ≤ 2 * D.N) (s : Rg D)
    (x : ℕ → Symbol w8) (a e : ℕ → Col D.K → Rg D) (j n : ℕ)
    (out restX restA restE : List Bool)
    (hout : n * ((D.K + D.K) * (D.N * D.K)) ≤ out.length) :
    (cbStep D.N D.K (fun i ↦ 2 * D.N - w * 2 ^ (7 - i)) (wd D s) (wd D 1))^[n]
      (blockStream (fun t ↦ symbolBits w8 (x t)) j n ++ restX,
        blockStream (fun t ↦ (vecE D (Col D.K)).enc (a t)) j n ++ restA,
        blockStream (fun t ↦ (vecE D (Col D.K)).enc (e t)) j n ++ restE, out) =
      (restX, restA, restE, (out ++ blockStream (fun t ↦
        (vecE D (Col D.K)).enc (inputBottom D w (x t) s (a t) (e t))) j n).drop
          (n * ((D.K + D.K) * (D.N * D.K)))) := by
  induction n generalizing j out with
  | zero => simp
  | succ n ih =>
    have hn : (D.K + D.K) * (D.N * D.K) ≤ out.length := by
      rw [Nat.succ_mul] at hout; omega
    have hlen : ((out ++ (vecE D (Col D.K)).enc (inputBottom D w (x j) s (a j) (e j))).drop
        ((D.K + D.K) * (D.N * D.K))).length = out.length := by
      rw [List.length_drop, List.length_append, length_vecE', length_col]; omega
    rw [Function.iterate_succ_apply]
    simp only [blockStream_succ, List.append_assoc]
    rw [cbStep_encoded D hN w hw (x j) s (a j) (e j),
      ih (j + 1) _ (by rw [hlen]; rw [Nat.succ_mul] at hout; omega)]
    rw [List.drop_append_of_le_length hn, List.append_assoc]
    conv_rhs =>
      rw [Nat.succ_mul, Nat.add_comm (n * ((D.K + D.K) * (D.N * D.K)))
        ((D.K + D.K) * (D.N * D.K)), ← List.drop_drop,
        List.drop_append_of_le_length hn]

/-- The executable bottom-row loop computes every position's scheme row. -/
theorem run_cinbotP_stream (S : Store 104) (h : TailOK D.K D.N S)
    (hN : 2 ≤ D.N) (w : ℕ) (hw : w * 128 ≤ 2 * D.N) (s : Rg D)
    (x : ℕ → Symbol w8) (a e : ℕ → Col D.K → Rg D) (j n : ℕ)
    (restX restA restE : List Bool) (hs : S 1 = wd D s) (h1 : S 16 = wd D 1)
    (hτ : ∀ i < 8, τT S i = 2 * D.N - w * 2 ^ (7 - i)) (hcount : (S 35).length = n)
    (hx : S 2 = blockStream (fun t ↦ symbolBits w8 (x t)) j n ++ restX)
    (ha : S 4 = blockStream (fun t ↦ (vecE D (Col D.K)).enc (a t)) j n ++ restA)
    (he : S 7 = blockStream (fun t ↦ (vecE D (Col D.K)).enc (e t)) j n ++ restE)
    (hout : n * ((D.K + D.K) * (D.N * D.K)) ≤ (S 0).length) :
    cinbotP.run S = cbG S (restX, restA, restE,
      (S 0 ++ blockStream (fun t ↦ (vecE D (Col D.K)).enc
        (inputBottom D w (x t) s (a t) (e t))) j n).drop
          (n * ((D.K + D.K) * (D.N * D.K)))) := by
  have hf : cbStep D.N D.K (τT S) (S 1) (S 16) =
      cbStep D.N D.K (fun i ↦ 2 * D.N - w * 2 ^ (7 - i)) (S 1) (S 16) := by
    funext ⟨xx, aa, ee, oo⟩
    dsimp only [cbStep, cbRow]
    rw [rbitsW_congr_prefix D.K _ _ xx (S 16) 8 hτ]
  rw [run_cinbotP D.K_pos h, hf, hs, h1, hcount, hx, ha, he,
    cbStep_stream D hN w hw s x a e j n (S 0) restX restA restE hout]

end AdvancedEncryption.ExpLUT.Prog.EncW
