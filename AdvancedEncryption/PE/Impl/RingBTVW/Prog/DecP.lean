import PE.Impl.RingBTVW.Prog.KeyGenP
import PE.Impl.RingBTVW.Prog.DecFin

/-!
# The machine of `Dec`, compiled from a tape program

`decFinB` ends decryption on `256` tapes: from the data word `skW ++ ctW` (tape `0`) and the word of
`c_f̂` (tape `2`) it writes `encodeTuple [[decodeBit (κ − (c₀ k₀ + c₁ k₁ + c_f̂ k₂))]]` on tape `0`
(`law_decFinB`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.RingBTVW.Fresh AdvancedEncryption.RingBTVW.Algo
  Turing Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord
open scoped SigabaNeo.Tape.Prog

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-! ### Reading a block of the data word -/

/-- `dst := take L (drop o (s 0))`. -/
def getP (o L : ℕ) (dst : Fin 256) : XProg 256 :=
  XProg.seq (XProg.prog (cp 102 0 ⨾ tailsP 102 o))
    (XProg.seq (prefP L 102 dst 103 104) (XProg.prog (clr 102)))

theorem law_getP (o L : ℕ) {dst : Fin 256} (h1 : (102 : Fin 256) ≠ dst) (h2 : (103 : Fin 256) ≠ dst)
    (h3 : dst ≠ 104) (h0 : dst ≠ 0) (s : Store 256) (hd : s dst = []) (h102 : s 102 = [])
    (h103 : s 103 = []) (h104 : s 104 = []) :
    (getP o L dst).law s = PMF.pure (Function.update s dst (((s 0).drop o).take L)) := by
  have hc : (cp 102 0 ⨾ tailsP (102 : Fin 256) o).CoinFree := by
    have := coinFree_tailsP (102 : Fin 256) o
    simp only [CoinFree] at this
    simp [CoinFree, coinFreeB, this]
  rw [getP, XProg.law_seq_pure (by rw [XProg.law_prog, law_eq_run_of_coinFree _ hc]),
    XProg.law_seq_pure (law_prefP _ h2 (by decide) h3 (by decide) _
      (by simp [run_tailsP, Function.update_apply, h103, h2.symm])
      (by simp [run_tailsP, Function.update_apply, h104, h3])), XProg.law_prim]
  congr 1
  simp only [run_seq, run_copy, run_tailsP, Prim.apply]
  funext t
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### The end of decryption -/

variable (hk) in
/-- The length of the word of the `Ψᵢ`. -/
abbrev lPsi : ℕ := fixLen (FixedEnc.fun (α := (Sdw (N := N) hk).Attr)
  (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k)))

variable (c) in
/-- The templates of the end of decryption (`counter 120`). -/
def decTmpl : List (Fin 256 × ℕ) :=
  [(6, K), (7, N), (8, N * K), (10, 1), (13, 2 * k), (14, 1), (15, 1), (16, c.d), (17, Algo.nT k),
    (29, N * K)]

variable (hk c) in
/-- **The end of decryption**: read `c₀ k₀ c₁ k₁ k₂ κ`, `decFP`, keep the constant coefficient,
the rounding test, the framed bit. -/
noncomputable def decFinB : XProg 256 :=
  XProg.seq (getP (fixLen (skEnc hk c) + lPsi (N := N) (K := K) hk) (c.d * (N * K)) 30) <|
  XProg.seq (getP (lenPK hk c) (c.d * (N * K)) 31) <|
  XProg.seq (getP (fixLen (skEnc hk c) + lPsi (N := N) (K := K) hk + c.d * (N * K)) (Algo.nT k * (N * K)) 32) <|
  XProg.seq (getP (lenPK hk c + c.d * (N * K)) (Algo.nT k * (N * K)) 33) <|
  XProg.seq (getP (lenPK hk c + c.d * (N * K) + Algo.nT k * (N * K)) (2 * k * (N * K)) 34) <|
  XProg.seq (getP (fixLen (skEnc hk c) + fixLen (ctEnc hk c) - N * K) (N * K) 35) <|
  XProg.seq (putW 4 (decRadW K)) <| XProg.seq (tmplP 120 (decTmpl c)) <|
  XProg.seq (XProg.frame eKR (XProg.prog ProgKeyR.decFP)) <|
  XProg.seq (XProg.prog (cp 28 39 ⨾ clr 39)) <| XProg.seq (prefP K 28 39 41 42) <|
  XProg.seq (XProg.prog (clr 28)) <|
  XProg.seq (XProg.frame eKR (XProg.prog (Prog.map ProgKeyR.ballR ballP))) <|
  XProg.seq (XProg.prog (clr 0)) <|
  XProg.seq (XProg.ifBit 40 (putW 0 [true, false, false]) (putW 0 [true, true, false]))
    (clearL clrAll)

theorem blkW {a b r : List Bool} {o L : ℕ} (ha : a.length = o) (hb : b.length = L) :
    ((a ++ (b ++ r)).drop o).take L = b := by
  rw [List.drop_left' ha, List.take_left' hb]

theorem dec_parts (sk : SK hk c) (ct : CT hk c) :
    let D := (skEnc hk c).enc sk ++ (ctEnc hk c).enc ct
    (D.drop (fixLen (skEnc hk c) + lPsi (N := N) (K := K) hk)).take (c.d * (N * K)) =
        vecW N K (ct.c₀ 0) ∧
      (D.drop (lenPK hk c)).take (c.d * (N * K)) = vecW N K (fun i => sk.2.k₀ i 0) ∧
      (D.drop (fixLen (skEnc hk c) + lPsi (N := N) (K := K) hk + c.d * (N * K))).take
        (Algo.nT k * (N * K)) = vecW N K (ct.c₁ 0) ∧
      (D.drop (lenPK hk c + c.d * (N * K))).take (Algo.nT k * (N * K)) =
        vecW N K (fun i => sk.2.k₁ i 0) ∧
      (D.drop (lenPK hk c + c.d * (N * K) + Algo.nT k * (N * K))).take (2 * k * (N * K)) =
        vecW N K (fun i => sk.2.k₂ i 0) ∧
      (D.drop (fixLen (skEnc hk c) + fixLen (ctEnc hk c) - N * K)).take (N * K) =
        (ringEnc N K).enc ct.κ := by
  intro D
  have esk : (skEnc hk c).enc sk = (pkEnc hk c).enc sk.1 ++ (vecW N K (fun i => sk.2.k₀ i 0) ++
      (vecW N K (fun i => sk.2.k₁ i 0) ++ vecW N K (fun i => sk.2.k₂ i 0))) := by
    rw [← keyEnc_eq c sk.2]; rfl
  set P := (FixedEnc.fun (α := (Sdw (N := N) hk).Attr)
    (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k))).enc ct.Ψ
  set J := (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
    (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k))).enc ct.cj
  have ect : (ctEnc hk c).enc ct = P ++ (vecW N K (ct.c₀ 0) ++ (vecW N K (ct.c₁ 0) ++
      (J ++ (ringEnc N K).enc ct.κ))) := by
    rw [← matEnc_row1, ← matEnc_row1]; rfl
  have lpk : ((pkEnc hk c).enc sk.1).length = lenPK hk c := length_enc_fixLen _ _
  have lsk : ((skEnc hk c).enc sk).length = fixLen (skEnc hk c) := length_enc_fixLen _ _
  have lct : ((ctEnc hk c).enc ct).length = fixLen (ctEnc hk c) := length_enc_fixLen _ _
  have lP : P.length = lPsi (N := N) (K := K) hk := length_enc_fixLen _ _
  have l0 : ∀ v : Fin c.d → Rg N K, (vecW N K v).length = c.d * (N * K) := fun v => by
    rw [length_vecW, len_fin]
  have l1 : ∀ v : TrapCol k → Rg N K, (vecW N K v).length = Algo.nT k * (N * K) := fun v => by
    rw [length_vecW, len_trapCol]
  have l2 : ∀ v : RingBTVW.Fresh.Col k → Rg N K, (vecW N K v).length = 2 * k * (N * K) := fun v => by
    rw [length_vecW, len_col]
  have lκ : ((ringEnc N K).enc ct.κ).length = N * K := (ringEnc N K).length _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : D = ((skEnc hk c).enc sk ++ P) ++ (vecW N K (ct.c₀ 0) ++
        (vecW N K (ct.c₁ 0) ++ (J ++ (ringEnc N K).enc ct.κ))) := by
      simp only [D, ect, List.append_assoc]
    rw [e, blkW (by rw [List.length_append, lsk, lP]) (l0 _)]
  · have e : D = (pkEnc hk c).enc sk.1 ++ (vecW N K (fun i => sk.2.k₀ i 0) ++
        ((vecW N K (fun i => sk.2.k₁ i 0) ++ vecW N K (fun i => sk.2.k₂ i 0)) ++
          (ctEnc hk c).enc ct)) := by
      simp only [D, esk, List.append_assoc]
    rw [e, blkW lpk (l0 _)]
  · have e : D = ((skEnc hk c).enc sk ++ P ++ vecW N K (ct.c₀ 0)) ++ (vecW N K (ct.c₁ 0) ++
        (J ++ (ringEnc N K).enc ct.κ)) := by
      simp only [D, ect, List.append_assoc]
    rw [e, blkW (by rw [List.length_append, List.length_append, lsk, lP, l0]) (l1 _)]
  · have e : D = ((pkEnc hk c).enc sk.1 ++ vecW N K (fun i => sk.2.k₀ i 0)) ++
        (vecW N K (fun i => sk.2.k₁ i 0) ++ (vecW N K (fun i => sk.2.k₂ i 0) ++
          (ctEnc hk c).enc ct)) := by
      simp only [D, esk, List.append_assoc]
    rw [e, blkW (by rw [List.length_append, lpk, l0]) (l1 _)]
  · have e : D = ((pkEnc hk c).enc sk.1 ++ vecW N K (fun i => sk.2.k₀ i 0) ++
        vecW N K (fun i => sk.2.k₁ i 0)) ++ (vecW N K (fun i => sk.2.k₂ i 0) ++
          (ctEnc hk c).enc ct) := by
      simp only [D, esk, List.append_assoc]
    rw [e, blkW (by rw [List.length_append, List.length_append, lpk, l0, l1]) (l2 _)]
  · have e : D = ((skEnc hk c).enc sk ++ P ++ vecW N K (ct.c₀ 0) ++ vecW N K (ct.c₁ 0) ++ J) ++
        ((ringEnc N K).enc ct.κ ++ []) := by
      simp only [D, ect, List.append_assoc, List.append_nil]
    have hl := lct
    rw [ect] at hl
    simp only [List.length_append, lP, l0, l1, lκ] at hl
    rw [e, blkW (by simp only [List.length_append, lsk, lP, l0, l1]; omega) lκ]

theorem ballW_one_take (K : ℕ) (sW w : List Bool) : ballW 1 K sW (w.take K) = ballW 1 K sW w := by
  simp [ballW, allN, block, List.take_take]

theorem embedF_eKR (S : Store 256) (u : Store 101) :
    embedF eKR S u = fun j => if h : j.val < 101 then u ⟨j.val, h⟩ else S j := by
  funext j
  rcases embedF_cases eKR S u j with ⟨hn, h⟩ | ⟨i, rfl, h⟩
  · rw [h, dif_neg]
    intro hj
    have := partialInv_self eKR ⟨j.val, hj⟩
    rw [show eKR ⟨j.val, hj⟩ = j from Fin.ext rfl, hn] at this
    exact absurd this (by simp)
  · rw [h, dif_pos (by rw [eKR_val]; exact i.isLt)]; rfl

/-- **The law of the end of decryption.** -/
theorem law_decFinB (hK2 : 2 ≤ K) (sk : SK hk c) (ct : CT hk c)
    (E : Matrix (Fin 1) (RingBTVW.Fresh.Col k) (Rg N K)) :
    (decFinB hk c).law (Function.update (io2 (R := 254) ((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct)
      [] []) 2 (rowW N K k E)) =
      PMF.pure (io2 (R := 254) (SigabaNeo.encodeTuple [[decodeBit c.hN
        (ct.κ - (ct.c₀ * sk.2.k₀ + ct.c₁ * sk.2.k₁ + E * sk.2.k₂) 0 0)]]) [] []) := by
  set D := (skEnc hk c).enc sk ++ (ctEnc hk c).enc ct with hD
  obtain ⟨g30, g31, g32, g33, g34, g35⟩ := dec_parts (hk := hk) (c := c) sk ct
  simp only [← hD] at g30 g31 g32 g33 g34 g35
  have b0 : ∀ t : Fin 256, t ≠ 0 → t ≠ 2 → Function.update (io2 (R := 254) D [] []) 2
      (rowW N K k E) t = [] := fun t h0 h2 => by
    have : t.val ≠ 0 := fun e => h0 (Fin.ext e)
    rw [Function.update_of_ne h2]; simp [io2, this]
  have hdecK : ∀ x ∈ decTmpl c, x.1 ≠ (120 : Fin 256) := fun x hx e => by
    simp only [decTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h <;> (subst h; simp at e)
  rw [decFinB,
    XProg.law_seq_pure (law_getP _ _ (by decide) (by decide) (by decide) (by decide) _
      (b0 _ (by decide) (by decide)) (b0 _ (by decide) (by decide)) (b0 _ (by decide) (by decide))
      (b0 _ (by decide) (by decide))),
    XProg.law_seq_pure (law_getP _ _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [b0, io2]) (by simp [b0, io2]) (by simp [b0, io2]) (by simp [b0, io2])),
    XProg.law_seq_pure (law_getP _ _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [b0, io2]) (by simp [b0, io2]) (by simp [b0, io2]) (by simp [b0, io2])),
    XProg.law_seq_pure (law_getP _ _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [b0, io2]) (by simp [b0, io2]) (by simp [b0, io2]) (by simp [b0, io2])),
    XProg.law_seq_pure (law_getP _ _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [b0, io2]) (by simp [b0, io2]) (by simp [b0, io2]) (by simp [b0, io2])),
    XProg.law_seq_pure (law_getP _ _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [b0, io2]) (by simp [b0, io2]) (by simp [b0, io2]) (by simp [b0, io2])),
    XProg.law_seq_pure (law_putW _ _ _),
    XProg.law_seq_pure (law_tmplP _ _ _ (by simp [b0, io2]) hdecK)]
  have e0 : ∀ (w : Store 256) (i : Fin 256) (v : List Bool), i ≠ 0 →
      Function.update w i v 0 = w 0 := fun w i v h => Function.update_of_ne (Ne.symm h) _ _
  simp only [e0 _ _ _ (show (30 : Fin 256) ≠ 0 by decide), e0 _ _ _ (show (31 : Fin 256) ≠ 0 by decide),
    e0 _ _ _ (show (32 : Fin 256) ≠ 0 by decide), e0 _ _ _ (show (33 : Fin 256) ≠ 0 by decide),
    e0 _ _ _ (show (34 : Fin 256) ≠ 0 by decide), e0 _ _ _ (show (2 : Fin 256) ≠ 0 by decide),
    show io2 (R := 254) D [] [] 0 = D by simp [io2], g30, g31, g32, g33, g34, g35,
    show (io2 (R := 254) D [] [] 4) = [] by simp [io2], List.nil_append]
  have e4 : ∀ (w : Store 256) (i : Fin 256) (v : List Bool), i ≠ 4 →
      Function.update w i v 4 = w 4 := fun w i v h => Function.update_of_ne (Ne.symm h) _ _
  simp only [e4 _ _ _ (show (30 : Fin 256) ≠ 4 by decide), e4 _ _ _ (show (31 : Fin 256) ≠ 4 by decide),
    e4 _ _ _ (show (32 : Fin 256) ≠ 4 by decide), e4 _ _ _ (show (33 : Fin 256) ≠ 4 by decide),
    e4 _ _ _ (show (34 : Fin 256) ≠ 4 by decide), e4 _ _ _ (show (35 : Fin 256) ≠ 4 by decide),
    e4 _ _ _ (show (2 : Fin 256) ≠ 4 by decide), show io2 (R := 254) D [] [] 4 = [] by simp [io2],
    List.nil_append]
  set S1 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (io2 (R := 254) D [] []) 2 (rowW N K k E)) 30
    (vecW N K (ct.c₀ 0))) 31 (vecW N K fun i => sk.2.k₀ i 0)) 32 (vecW N K (ct.c₁ 0))) 33
    (vecW N K fun i => sk.2.k₁ i 0)) 34 (vecW N K fun i => sk.2.k₂ i 0)) 35 ((ringEnc N K).enc ct.κ))
    4 (decRadW K) with hS1
  set S8 := tmplS (decTmpl c) S1 with hS8
  have keys : (decTmpl c).map (fun x => x.1.val) = [6, 7, 8, 10, 13, 14, 15, 16, 17, 29] := rfl
  have low : ∀ t : Fin 256, t.val ∉ [6, 7, 8, 10, 13, 14, 15, 16, 17, 29] → S8 t = S1 t :=
    fun t ht => tmplS_out' keys S1 t ht
  have blank : ∀ t : Fin 256, t.val ∉ [0, 2, 4, 6, 7, 8, 10, 13, 14, 15, 16, 17, 29, 30, 31, 32, 33,
      34, 35] → S8 t = [] := by
    intro t ht
    rw [low t (fun h => ht (by simp at h ⊢; omega))]
    have h0 : t.val ≠ 0 := fun h => ht (by simp [h])
    simp only [hS1, Function.update_apply, io2, h0, if_false]
    split_ifs with a b c' d' e f g h' <;> first | rfl | (exfalso; apply ht; subst_vars; decide)
  have tm : (S8 6).length = K ∧ (S8 7).length = N ∧ (S8 8).length = N * K ∧ (S8 10).length = 1 ∧
      (S8 13).length = 2 * k ∧ (S8 14).length = 1 ∧ (S8 15).length = 1 ∧ (S8 16).length = c.d ∧
      (S8 17).length = Algo.nT k ∧ (S8 29).length = N * K := by
    simp only [hS8, decTmpl, tmplS, List.foldl_cons, List.foldl_nil, Function.update_apply]
    simp
  obtain ⟨t6, t7, t8, t10, t13, t14, t15, t16, t17, t29⟩ := tm
  have v : ∀ t : Fin 256, t.val ∈ [0, 2, 4, 30, 31, 32, 33, 34, 35] → S8 t = S1 t := fun t ht =>
    low t (fun h => by simp at h ht; omega)
  have s0 : S8 0 = D := by rw [v 0 (by simp)]; simp [hS1, io2]
  have s2 : S8 2 = rowW N K k E := by rw [v 2 (by simp)]; simp [hS1]
  have s4 : S8 4 = decRadW K := by rw [v 4 (by simp)]; simp [hS1]
  have s30 : S8 30 = vecW N K (ct.c₀ 0) := by rw [v 30 (by simp)]; simp [hS1]
  have s31 : S8 31 = vecW N K (fun i => sk.2.k₀ i 0) := by rw [v 31 (by simp)]; simp [hS1]
  have s32 : S8 32 = vecW N K (ct.c₁ 0) := by rw [v 32 (by simp)]; simp [hS1]
  have s33 : S8 33 = vecW N K (fun i => sk.2.k₁ i 0) := by rw [v 33 (by simp)]; simp [hS1]
  have s34 : S8 34 = vecW N K (fun i => sk.2.k₂ i 0) := by rw [v 34 (by simp)]; simp [hS1]
  have s35 : S8 35 = (ringEnc N K).enc ct.κ := by rw [v 35 (by simp)]; simp [hS1]
  clear_value S8 S1
  have bl : ∀ j : Fin 101, (j.val ∉ [0, 2, 4, 6, 7, 8, 10, 13, 14, 15, 16, 17, 29, 30, 31, 32, 33,
      34, 35]) → (S8 ∘ eKR) j = [] := fun j hj => blank (eKR j) (by rw [eKR_val]; exact hj)
  have l0 : ∀ v : Fin c.d → Rg N K, (vecW N K v).length = c.d * (N * K) := fun v => by
    rw [length_vecW, len_fin]
  have l1 : ∀ v : TrapCol k → Rg N K, (vecW N K v).length = Algo.nT k * (N * K) := fun v => by
    rw [length_vecW, len_trapCol]
  have l2 : ∀ v : RingBTVW.Fresh.Col k → Rg N K, (vecW N K v).length = 2 * k * (N * K) := fun v => by
    rw [length_vecW, len_col]
  obtain ⟨u, hu, u39, uS, uA⟩ := ProgKeyR.run_decFP (N := N) (K := K) (k := k) (d := c.d)
    (by omega) (S8 ∘ eKR) (fun j h1 h2 => bl j (by simp; omega)) t6 t7 t8 t13 t14 t15 t16 t17 t29
    (by show (S8 30).length = _; rw [s30, l0]) (by show (S8 31).length = _; rw [s31, l0])
    (by show (S8 32).length = _; rw [s32, l1]) (by show (S8 33).length = _; rw [s33, l1])
    (by show (S8 2).length = _; rw [s2, Algo.length_rowW])
    (by show (S8 34).length = _; rw [s34, l2]) (by show (S8 35).length = _; rw [s35]; exact (ringEnc N K).length _)
  set V := decValW N K c.d (Algo.nT k) k (S8 30) (S8 31) (S8 32) (S8 33) (S8 2) (S8 34) (S8 35) with hV
  rw [XProg.law_seq, XProg.law_frame, XProg.law_prog, law_eq_run _ ProgKeyR.noGrow_decFP,
    show (fun j => S8 (eKR j)) = S8 ∘ eKR from rfl, hu, PMF.pure_map, PMF.pure_bind, embedF_eKR]
  set T := fun j : Fin 256 => if h : j.val < 101 then u ⟨j.val, h⟩ else S8 j with hT
  have T39 : T 39 = V := by simp [hT, u39]; rfl
  have Tlow : ∀ j : Fin 256, j.val < 26 → T j = S8 j := fun j hj => by
    simp only [hT, dif_pos (show j.val < 101 by omega)]
    rw [uA _ (Or.inl hj)]; rfl
  have Tscr : ∀ j : Fin 256, 41 ≤ j.val → j.val < 90 → T j = [] := fun j h1 h2 => by
    simp only [hT, dif_pos (show j.val < 101 by omega)]; exact uS _ h1 h2
  have hVl : V.length = N * K := by
    rw [hV, decValW, length_subRW _ _ (by rw [s35]; exact (ringEnc N K).length _)]
  have hNK : K ≤ N * K := Nat.le_mul_of_pos_left _ c.hN
  -- the constant coefficient
  have hc1 : (cp 28 39 ⨾ clr (39 : Fin 256)).CoinFree := rfl
  rw [XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ hc1, PMF.pure_bind]
  simp only [run_seq, run_copy, run_clear, T39]
  rw [XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [Tscr 41 (by decide) (by decide)]) (by simp [Tscr 42 (by decide) (by decide)])),
    XProg.law_seq_pure (XProg.law_prim _ _)]
  simp only [Prim.apply, Function.update_self, Function.update_of_ne (show (28 : Fin 256) ≠ 39 by decide),
    List.nil_append]
  set T3 := Function.update (Function.update (Function.update (Function.update T 28 V) 39 [])
    39 (V.take K)) 28 [] with hT3
  have T3scr : ProgKeyR.Scr (fun j => T3 (eKR j)) := fun j h1 h2 => by
    show T3 (eKR j) = []
    rw [hT3]
    rw [Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp [eKR_val] at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp [eKR_val] at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp [eKR_val] at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp [eKR_val] at this; omega)]
    exact Tscr _ (by rw [eKR_val]; exact h1) (by rw [eKR_val]; exact h2)
  have T3low : ∀ j : Fin 256, j.val < 26 → T3 j = S8 j := fun j hj => by
    rw [hT3, Function.update_of_ne (by intro e; rw [e] at hj; simp at hj),
      Function.update_of_ne (by intro e; rw [e] at hj; simp at hj),
      Function.update_of_ne (by intro e; rw [e] at hj; simp at hj),
      Function.update_of_ne (by intro e; rw [e] at hj; simp at hj), Tlow j hj]
  have T39' : T3 39 = V.take K := by simp [hT3]
  rw [XProg.law_seq, XProg.law_frame, XProg.law_prog,
    law_eq_run _ (NoGrow.map (u := ProgKeyR.ballR) noGrow_ballP),
    ProgKeyR.run_ballR (n := 1) (K := K) _ T3scr (by omega)
      (by show (T3 39).length = _; rw [T39', List.length_take, hVl]; simp; omega)
      (by show (T3 4).length = K; rw [T3low 4 (by decide), s4]; exact length_toBits _ _)
      (by show (T3 6).length = K; rw [T3low 6 (by decide), t6])
      (by show (T3 10).length = 1; rw [T3low 10 (by decide), t10])
      (by show (T3 14).length = 1; rw [T3low 14 (by decide), t14]),
    PMF.pure_map, PMF.pure_bind, embedF_upd, embedF_comp]
  have hb4 : T3 (eKR 4) = decRadW K := by
    show T3 4 = _; rw [T3low 4 (by decide), s4]
  have hb39 : T3 (eKR 39) = V.take K := T39'
  rw [hb4, hb39, ballW_one_take, show eKR 40 = 40 from rfl]
  have hval := decValW_eq (N := N) (K := K) (k := k) sk.2.k₀ sk.2.k₁ sk.2.k₂ ct.c₀ ct.c₁ E ct.κ
  rw [← s30, ← s31, ← s32, ← s33, ← s2, ← s34, ← s35, ← hV] at hval
  have hdec := decFinW_value (k := k) hK2 c.hN (S8 30) (S8 31) (S8 32) (S8 33) (S8 2) (S8 34)
    (S8 35) _ hval
  rw [decFinW, ← hV] at hdec
  simp only [Matrix.add_apply] at hdec
  rw [XProg.law_seq_pure (XProg.law_prim _ _), XProg.law_seq, XProg.law_ifBit]
  simp only [Prim.apply, Function.update_of_ne (show (40 : Fin 256) ≠ 0 by decide),
    Function.update_self, List.head?_cons]
  cases hbv : ballW 1 K (decRadW K) V
  · rw [if_neg (by simp), law_putW, PMF.pure_bind, law_clearL]
    congr 1
    funext t
    rw [hbv] at hdec
    by_cases t0 : t = 0
    · subst t0
      simp only [mem_clrAll, ne_eq, not_true_eq_false, if_false, Function.update_self, io2]
      simp [← hdec, encodeTuple_single, MultiTapeTM.frame]
    · have t0' : t.val ≠ 0 := fun e => t0 (Fin.ext e)
      simp only [mem_clrAll, ne_eq, t0, not_false_eq_true, if_true, io2, t0', if_false]
      split_ifs <;> rfl
  · rw [if_pos (by simp), law_putW, PMF.pure_bind, law_clearL]
    congr 1
    funext t
    rw [hbv] at hdec
    by_cases t0 : t = 0
    · subst t0
      simp only [mem_clrAll, ne_eq, not_true_eq_false, if_false, Function.update_self, io2]
      simp [← hdec, encodeTuple_single, MultiTapeTM.frame]
    · have t0' : t.val ≠ 0 := fun e => t0 (Fin.ext e)
      simp only [mem_clrAll, ne_eq, t0, not_false_eq_true, if_true, io2, t0', if_false]
      split_ifs <;> rfl

/-! ### Coin-freeness of the helpers -/

theorem coinFree_noGrowP {n : ℕ} : ∀ p : Prog n, p.NoGrow → p.CoinFree
  | .prim _, _ => rfl
  | .coin _, h => absurd h (by simp [NoGrow, noGrowB])
  | .seq p q, h | .ifBlank _ p q, h | .ifBit _ p q, h => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    have h1 := coinFree_noGrowP p h.1
    have h2 := coinFree_noGrowP q h.2
    simp only [CoinFree] at h1 h2
    simp [CoinFree, coinFreeB, h1, h2]
  | .loop _ b, h => coinFree_noGrowP b h

theorem cfX_putW {n : ℕ} (t : Fin n) : ∀ w : List Bool, (putW t w).CoinFree
  | [] => rfl
  | _ :: w => XProg.coinFree_seq rfl (cfX_putW t w)

theorem cfX_prefP {n : ℕ} (P : ℕ) (src dst a b : Fin n) : (prefP P src dst a b).CoinFree :=
  XProg.coinFree_seq rfl (XProg.coinFree_seq (coinFree_iter _ (stepF a dst b) rfl P) rfl)

theorem cfX_natP {n : ℕ} (t c' : Fin n) : ∀ m, (XProg.natP t c' m).CoinFree
  | 0 => by rw [XProg.natP]; rfl
  | m + 1 => by
    rw [XProg.natP]
    have ih := cfX_natP t c' ((m + 1) / 2)
    split_ifs
    · exact XProg.coinFree_seq ih rfl
    · exact XProg.coinFree_seq (XProg.coinFree_seq ih rfl) rfl

theorem cfX_tmplP {n : ℕ} (c' : Fin n) : ∀ l : List (Fin n × ℕ), (tmplP c' l).CoinFree
  | [] => rfl
  | x :: l => XProg.coinFree_seq (cfX_natP _ _ _) (cfX_tmplP c' l)

theorem cfX_clearL {n : ℕ} [NeZero n] : ∀ l : List (Fin n), (clearL l).CoinFree
  | [] => rfl
  | _ :: l => XProg.coinFree_seq rfl (cfX_clearL l)

theorem cfX_getP (o L : ℕ) (dst : Fin 256) : (getP o L dst).CoinFree := by
  have h := coinFree_tailsP (102 : Fin 256) o
  refine XProg.coinFree_seq ?_ (XProg.coinFree_seq (cfX_prefP _ _ _ _ _) rfl)
  simp only [XProg.CoinFree, XProg.coinFreeB]
  simp only [CoinFree] at h
  simp [coinFreeB, h]

theorem cfX_decFinB : (decFinB hk c).CoinFree := by
  unfold decFinB
  repeat' first
    | exact cfX_getP _ _ _ | exact cfX_putW _ _ | exact cfX_tmplP _ _ | exact cfX_prefP _ _ _ _ _
    | exact cfX_clearL _ | apply XProg.coinFree_seq | apply XProg.coinFree_ifBit
  all_goals first
    | exact coinFree_noGrowP _ ProgKeyR.noGrow_decFP
    | exact coinFree_noGrowP _ (NoGrow.map noGrow_ballP)
    | rfl

end AdvancedEncryption.RingBTVW.Prog
