import PE.Impl.DualUse.Prog.EncCore
import PE.Impl.DualUse.Prog.ChalI

/-!
# The output of the core of `Enc`

The words that the phases of `encCoreP` compute are those of the fields of `encrypt`:

* `c0_wordS`, `row_affine`: `c₀ = s B₀ + e₀`, `c₁ = s B₁ + e₁` (rows over any enumerated columns);
* `halfW_eq`, `kap_word`: `κ = s p + e' + M ⌊q/2⌋`;
* **`encCore_out`**: from the words of `mpk`, the date, the message bit and the coins, the output
  register of `encCoreP` is the word `ctEnc` of `encrypt mpk (bitsOf x) M r`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  Matrix AdvancedEncryption.RingBTVW Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

variable {N K k : ℕ}

/-- **A row over enumerated columns** is a row word over `Fin L`. -/
theorem rowEnc_matW {ι : Type} [Enum ι] (M : Matrix (Fin 1) ι (Rg N K)) :
    (matEnc (N := N) (K := K) (Fin 1) ι).enc M =
      matW N K 1 (Enum.list (α := ι)).length
        (Matrix.of fun _ j => M 0 ((Enum.list (α := ι)).get j)) := by
  rw [← matEnc_fin_eq_matW]
  show ((List.finRange 1).map (fun r => M r)).flatMap
      (fun row => ((Enum.list (α := ι)).map row).flatMap (ringEnc N K).enc) =
    ((List.finRange 1).map (fun r => (Matrix.of fun _ j => M 0 ((Enum.list (α := ι)).get j)) r)).flatMap
      (fun row => ((List.finRange (Enum.list (α := ι)).length).map row).flatMap (ringEnc N K).enc)
  rw [show List.finRange 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Matrix.of_apply]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem len_rowEnc {ι : Type} [Enum ι] (M : Matrix (Fin 1) ι (Rg N K)) :
    ((matEnc (N := N) (K := K) (Fin 1) ι).enc M).length =
      (Enum.list (α := ι)).length * (N * K) := by
  rw [rowEnc_matW, length_matW, Nat.one_mul]

/-- **A row `s B + e`** on words. -/
theorem row_affine {ι : Type} [Enum ι] (s : Rg N K) (B E : Matrix (Fin 1) ι (Rg N K)) :
    addRW ((Enum.list (α := ι)).length * N) K
      (matMulW N K 1 1 (Enum.list (α := ι)).length ((ringEnc N K).enc s)
        ((matEnc (N := N) (K := K) (Fin 1) ι).enc B))
      ((matEnc (N := N) (K := K) (Fin 1) ι).enc E) =
      (matEnc (N := N) (K := K) (Fin 1) ι).enc (scalar s * B + E) := by
  have hsw : (ringEnc N K).enc s = matW N K 1 1 (scalar s) := by rw [matW_one_one]; rfl
  rw [rowEnc_matW, rowEnc_matW, rowEnc_matW, hsw, matMulW_enc, ← matAddW_eq_addRW]
  have := matAddW_enc (N := N) (K := K) (m := 1) (n := (Enum.list (α := ι)).length)
    (scalar s * Matrix.of fun _ j => B 0 ((Enum.list (α := ι)).get j))
    (Matrix.of fun _ j => E 0 ((Enum.list (α := ι)).get j))
  rw [Nat.one_mul] at this
  rw [this]
  congr 1

/-- The word of `⌊q/2⌋` built by the phase of `κ`. -/
theorem halfW_eq (hk : 2 ^ K < 2 ^ k) (hN : 0 < N) (hK : 0 < K) :
    ((List.replicate (N * K) false ++ [true]).tail ++ List.replicate (N * K - K) false).drop
      (N * K - K) = (ringEnc N K).enc (Sdw (N := N) hk).half := by
  have h := ringEnc_add_half hk hN hK (0 : Rg N K)
  rw [zero_add, enc_zero_rep] at h
  rw [h]
  have hNK : K ≤ N * K := Nat.le_mul_of_pos_left K hN
  have hL : ((List.replicate (N * K) false ++ [true]).tail ++ List.replicate (N * K - K) false).drop
      (N * K - K) = List.replicate (K - 1) false ++ true :: List.replicate (N * K - K) false := by
    obtain ⟨M, hM⟩ : ∃ M, N * K = M + K := ⟨N * K - K, by omega⟩
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [hM, show M + (K' + 1) - (K' + 1) = M by omega, show K' + 1 - 1 = K' by omega,
      show M + (K' + 1) = (M + K') + 1 by omega, List.replicate_succ, List.cons_append,
      List.tail_cons, List.replicate_add, List.append_assoc, List.append_assoc,
      List.drop_left' (by simp)]
    simp
  rw [hL]
  apply List.ext_getElem
  · simp [length_flipAt]; omega
  · intro i h1 h2
    simp only [flipAt, List.getElem_mapIdx, List.getElem_replicate]
    rw [List.getElem_append]
    split_ifs with ha hb hb <;> (try simp only [List.length_replicate] at *) <;>
      (try rw [List.getElem_cons]) <;> (try split_ifs) <;>
      first | (simp; done) | omega | (simp at ha; omega)

theorem kap_word (hk : 2 ^ K < 2 ^ k) (hN : 0 < N) (hK : 0 < K) (s p e : Rg N K) (b : Bool)
    (hw : List Bool) (hhw : hw.length = N * K - K) :
    kapW N K ((ringEnc N K).enc s) ((ringEnc N K).enc p) ((ringEnc N K).enc e) [b]
      (List.replicate (N * K) false) hw =
      (ringEnc N K).enc (s * p + e + (if b then (Sdw (N := N) hk).half else 0)) := by
  simp only [kapW, mulRW_enc, addRW_enc, hhw, halfW_eq hk hN hK, hd_cons]
  cases b <;> simp

theorem upd_blank {S : Store 120} {a : ℕ} (h : ∀ i : Fin 120, a ≤ i.val → S i = []) (t : Fin 120)
    (ht : t.val < a) (v : List Bool) : ∀ i : Fin 120, a ≤ i.val → Function.update S t v i = [] := by
  intro i hi
  rw [Function.update_of_ne (fun e => by subst e; omega)]
  exact h i hi

/-- Blank tapes stay blank under updates of other tapes. -/
macro "blank120 " h:ident : tactic => `(tactic| (
  intro i hi
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> first | (simp at hi; done) | exact $h i (by omega) |
    (simp at *; omega)))

variable (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The number of columns of `B₁`. -/
abbrev nTrap (k : ℕ) : ℕ := (Enum.list (α := TrapCol k)).length

/-- The number of encodings `c_j`. -/
abbrev nJenc : ℕ := (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length

/-- The length of the word of a ciphertext, field by field as the output register is filled. -/
def ctLen : ℕ := 10 * (2 * (2 * k) * (N * K)) + 1 * c.d * (N * K) + 1 * nTrap k * (N * K) +
  nJenc (N := N) hk * (1 * (2 * k) * (N * K)) + N * K

theorem encDate_bits (x : Date) :
    encDate x = (List.finRange 10).map (Gates.DateWindow.bitsOf x) := by
  apply List.ext_getElem (by simp [Gates.DateWindow.length_encDate])
  intro i h1 h2
  simp [Gates.DateWindow.bitsOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem drop2 (X Y Z : List Bool) (a b : ℕ) (h : a ≤ (X ++ Y).length) :
    ((X ++ Y).drop a ++ Z).drop b = (X ++ Y ++ Z).drop (a + b) := by
  rw [← List.drop_append_of_le_length h, List.drop_drop, Nat.add_comm]

/-- Shifting five words into a register of their total length. -/
theorem reg5 (R A B C D E : List Bool) (hR : R.length = A.length + B.length + C.length + D.length +
    E.length) :
    ((((((R ++ A).drop A.length ++ B).drop B.length ++ C).drop C.length ++ D).drop D.length ++
      E).drop E.length) = A ++ (B ++ (C ++ (D ++ E))) := by
  rw [drop2 R A B _ _ (by simp), drop2 (R ++ A) B C _ _ (by simp),
    drop2 (R ++ A ++ B) C D _ _ (by simp; omega), drop2 (R ++ A ++ B ++ C) D E _ _ (by simp; omega)]
  simp only [List.append_assoc]
  exact List.drop_left' (by omega)

set_option maxHeartbeats 16000000 in
/-- **The core of `Enc`**: on the words of the public key, the date, the message bit and the
coins (with `Rm = rMat rr`), and templates of the right lengths, the output register holds the word
of `encrypt mpk (bitsOf x) b r`. -/
theorem encCore_out (hN : 0 < N) (hK : 0 < K) (mpk : PK hk c) (x : Date) (b : Bool)
    (r : EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k))
    (rr : (Sdw (N := N) hk).Attr × RingBTVW.Col k → (Fin c.d → Bool)) (hRm : r.Rm = rMat rr)
    (S : Store 120) (hS : ∀ i : Fin 120, 39 ≤ i.val → S i = [])
    (h0 : (S 0).length = ctLen hk c)
    (h1 : S 1 = (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc mpk.B₀)
    (h2 : S 2 = (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc mpk.B₁)
    (h3 : S 3 = (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
      (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc mpk.Bj)
    (h4 : S 4 = (ringEnc N K).enc mpk.p) (h5 : S 5 = encDate x) (h6 : S 6 = [b])
    (h7 : S 7 = (ringEnc N K).enc r.s)
    (h8 : S 8 = (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc r.e₀)
    (h9 : S 9 = (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc r.e₁)
    (h10 : S 10 = (rmTEnc c).enc (rMat (R := Rg N K) rr))
    (h11 : S 11 = (eEnc (N := N) hk).enc r.ej) (h12 : S 12 = (ringEnc N K).enc r.e')
    (t13 : (S 13).length = K) (t14 : (S 14).length = N) (t15 : S 15 = List.replicate (N * K) false)
    (t16 : (S 16).length = 1) (t17 : (S 17).length = 1) (t18 : (S 18).length = k)
    (t19 : (S 19).length = c.d) (t20 : (S 20).length = nTrap k) (t21 : (S 21).length = 2 * k)
    (t22 : (S 22).length = 10) (t23 : S 23 = List.replicate (2 * k * (N * K)) false)
    (t24 : S 24 = List.replicate (2 * (2 * k) * (N * K)) false)
    (t25 : (S 25).length = 2 * (2 * k) * N) (t26 : (S 26).length = 2 * k * N)
    (t27 : (S 27).length = 10 * (2 * (2 * k))) (t28 : (S 28).length = (k - K) * N)
    (t29 : (S 29).length = nJenc (N := N) hk) (t30 : (S 30).length = 1 * c.d * (N * K))
    (t31 : (S 31).length = c.d * N) (t32 : (S 32).length = 1 * nTrap k * (N * K))
    (t33 : (S 33).length = nTrap k * N)
    (t34 : S 34 = List.replicate (10 * (2 * (2 * k) * (N * K))) false)
    (t35 : S 35 = List.replicate (10 * (2 * (2 * k)) * (k * N)) false)
    (t36 : S 36 = List.replicate (nJenc (N := N) hk * (1 * (2 * k) * (N * K))) false)
    (t37 : (S 37).length = N * K - K) (t38 : (S 38).length = k * (N * K)) :
    (Prog.run encCoreP S) 0 = (ctEnc hk c).enc (encrypt mpk (Gates.DateWindow.bitsOf x) b r) := by
  have t15l : (S 15).length = N * K := by rw [t15, List.length_replicate]
  simp only [encCoreP, Prog.run_seq]
  rw [run_gadPh S (fun i hi => hS i (by omega)) t13 t14 t15l t18 (by rw [t23]; simp)
    (by rw [t24]; simp; ring) t38]
  have hd1 : (S 1).length = c.d * (N * K) := by rw [h1, len_rowEnc]; simp [Enum.list]
  have hd8 : (S 8).length = c.d * (N * K) := by rw [h8, len_rowEnc]; simp [Enum.list]
  rw [run_c0Ph _ (upd_blank (upd_blank (fun i hi => hS i (by omega)) _ (by decide) _) _ (by decide) _)
    (by simpa using t13) (by simpa using t14) (by simpa using t15l) (by simpa using t16)
    (by simpa using t17) (by simpa using t19) (by simpa using t30) (by simpa using t31)
    (by simp [h7, len_enc]) (by simpa using hd1) (by simpa using hd8)]
  have hT2 : (S 2).length = nTrap k * (N * K) := by rw [h2, len_rowEnc]
  have hT9 : (S 9).length = nTrap k * (N * K) := by rw [h9, len_rowEnc]
  rw [run_c1Ph _ (upd_blank (upd_blank (upd_blank (fun i hi => hS i (by omega)) _ (by decide) _) _
      (by decide) _) _ (by decide) _)
    (by simpa using t13) (by simpa using t14) (by simpa using t15l) (by simpa using t16)
    (by simpa using t17) (by simpa using t20) (by simpa using t32) (by simpa using t33)
    (by simp [h7, len_enc]) (by simpa using hT2) (by simpa using hT9)]
  rw [run_kapPh _ (upd_blank (upd_blank (upd_blank (upd_blank (fun i hi => hS i (by omega)) _
      (by decide) _) _ (by decide) _) _ (by decide) _) _ (by decide) _)
    (by simp [hS]) (by simpa using t13) (by simpa using t14) (by simpa using t15l)
    (by simp [h7, len_enc]) (by simp [h4, len_enc]) (by simp [h12, len_enc])]
  have hgl : (gswW N K k).length = 2 * (2 * k) * (N * K) := by
    rw [← gswW_enc hk, len_matEnc2]
  rw [run_psiPh (d := c.d) (L := 2 * k) _ (upd_blank (upd_blank (upd_blank (upd_blank (upd_blank
      (fun i hi => hS i (by omega)) _ (by decide) _) _ (by decide) _) _ (by decide) _) _
      (by decide) _) _ (by decide) _)
    (by simp [hS]) (by simpa using t13) (by simpa using t14) (by simpa using t15)
    (by simpa using t19) (by simpa using t21) (by simpa using t23) (by simpa using t24)
    (by simpa using t25) (by simpa using hgl)]
  rw [run_zPh (P := (k - K) * N) _ ?z1 ?z2 ?z3 ?z4 ?z5 ?z6]
  case z1 =>
    repeat (refine upd_blank ?_ _ (by decide) _)
    exact fun i hi => hS i (by omega)
  case z2 => simp [hS]
  case z3 => simpa using t13
  case z4 => simpa using t14
  case z5 => simpa using t15l
  case z6 => simpa using t28
  have hgad : (gadW N K k).length = 2 * k * N * K := by rw [length_gadW]; ring
  rw [run_cjPh (L := 2 * k) _ ?j1 ?j2 ?j3 ?j4 ?j5 ?j6 ?j7 ?j8 ?j9 ?j10 ?j11]
  case j1 =>
    repeat (refine upd_blank ?_ _ (by decide) _)
    exact fun i hi => hS i (by omega)
  case j2 => simpa using t13
  case j3 => simpa using t14
  case j4 => simpa using t15l
  case j5 => simpa using t16
  case j6 => simpa using t17
  case j7 => simpa using t21
  case j8 => simp [t23]; try ring
  case j9 => simpa using t26
  case j10 => simp [h7, len_enc]
  case j11 => simpa using hgad
  rw [run_ctPh_out _ (by simp [hS]) (by simp [hS])]
  simp (config := { decide := true }) only [Function.update_apply, ite_true, ite_false]
  have hKk : K ≤ k := ((Nat.pow_lt_pow_iff_right (by norm_num)).mp hk).le
  set Ψ := gswCts mpk (Gates.DateWindow.bitsOf x) r with hΨ
  have hc0 : addRW (c.d * N) K (matMulW N K 1 1 c.d (S 7) (S 1)) (S 8) =
      (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc (scalar r.s * mpk.B₀ + r.e₀) := by
    rw [h7, h1, h8]
    convert row_affine (ι := Fin c.d) r.s mpk.B₀ r.e₀ using 3 <;> simp [Enum.list]
  have hc1 : addRW (nTrap k * N) K (matMulW N K 1 1 (nTrap k) (S 7) (S 2)) (S 9) =
      (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (scalar r.s * mpk.B₁ + r.e₁) := by
    rw [h7, h2, h9]; exact row_affine (ι := TrapCol k) r.s mpk.B₁ r.e₁
  have hkap : kapW N K (S 7) (S 4) (S 12) (S 6) (S 15) (S 37) = (ringEnc N K).enc
      (r.s * mpk.p + r.e' + (if b then (Sdw (N := N) hk).half else 0)) := by
    rw [h7, h4, h12, h6, t15]; exact kap_word hk hN hK _ _ _ b _ t37
  have hpsi : ((Prog.iStepB N K c.d (2 * k) (S 1)
      (addRW (c.d * N) K (matMulW N K 1 1 c.d (S 7) (S 1)) (S 8)) (gswW N K k))^[(S 22).length]
      (S 34, S 10, S 5)).1 =
      (FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc Ψ := by
    rw [hc0, h1, flatMap_enc_row, flatMap_enc_row, h10, rmTEnc_cols hk c rr, h5, encDate_bits, t22,
      t34]
    have := iStepB_list hk hN hK mpk.B₀ (scalar r.s * mpk.B₀ + r.e₀) rr
      (Gates.DateWindow.bitsOf x) (List.finRange 10)
      (List.replicate (10 * (2 * (2 * k) * (N * K))) false) [] []
    simp only [List.append_nil, List.length_finRange] at this
    rw [this, List.drop_left' (by simp)]
    show _ = ((List.finRange 10).map (fun i : Fin 10 => Ψ i)).flatMap _
    rw [List.flatMap_map]
    dsimp only
    simp only [hΨ, gswCts, hRm]
  have hz : ((Prog.eStepC N K ((k - K) * N))^[(S 27).length]
      (S 35, (FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc
        (fun i : Fin 10 => Ψ i))).1 =
      (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).map
        fun j => coeffBool (Ψ j.1) j.2 := by
    have := eStepC_list (N := N) (K := K) hKk (psiEntries (fun i : Fin 10 => Ψ i)) (S 35) []
    rw [List.append_nil] at this
    rw [psiWord_eq, t27, ← len_psiEntries (fun i : Fin 10 => Ψ i), this, t35,
      List.drop_left' (by simp [len_psiEntries])]
    exact psiBits_eq hk (fun i : Fin 10 => Ψ i)
  have hcj : ((Prog.jStepE N K (2 * k) (S 7) (gadW N K k))^[(S 29).length]
      (S 36, (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).map
        (fun j => coeffBool (Ψ j.1) j.2), S 3, S 11)).1 =
      (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc
        (fun j => scalar r.s * (mpk.Bj j - bitsOf (Sdw (N := N) hk) Ψ j • (Sdw (N := N) hk).Γ₁.G) +
          r.ej j) := by
    have := jStepE_list hk r.s Ψ mpk.Bj r.ej
      (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index))
      (List.replicate (nJenc (N := N) hk * (1 * (2 * k) * (N * K))) false) [] [] []
    simp only [List.append_nil] at this
    rw [h7, h3, h11, t29, t36]
    have e3 : (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc mpk.Bj =
        (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).flatMap
          (fun j => (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (mpk.Bj j)) := by
      rw [fun_enc_eq, List.flatMap_map]
    have e11 : (eEnc (N := N) hk).enc r.ej =
        (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).flatMap
          (fun j => (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (r.ej j)) := by
      rw [eEnc, fun_enc_eq, List.flatMap_map]
    have hJ : (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length =
        nJenc (N := N) hk := rfl
    rw [e3, e11, ← hJ]
    refine (congrArg Prod.fst this).trans ?_
    dsimp only
    rw [List.drop_left' (by simp), fun_enc_eq, List.flatMap_map]
  rw [hpsi]
  erw [hz]
  rw [hcj, hc0, hc1, hkap]
  set A := (FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc Ψ
  set B := (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc (scalar r.s * mpk.B₀ + r.e₀)
  set C := (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (scalar r.s * mpk.B₁ + r.e₁)
  set D := (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
    (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc
    (fun j => scalar r.s * (mpk.Bj j - bitsOf (Sdw (N := N) hk) Ψ j • (Sdw (N := N) hk).Γ₁.G) + r.ej j)
  set E := (ringEnc N K).enc (r.s * mpk.p + r.e' + (if b then (Sdw (N := N) hk).half else 0))
  have lA := (FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).length Ψ
  have lB := (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).length (scalar r.s * mpk.B₀ + r.e₀)
  have lC := (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).length (scalar r.s * mpk.B₁ + r.e₁)
  have lD := (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
    (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).length
    (fun j => scalar r.s * (mpk.Bj j - bitsOf (Sdw (N := N) hk) Ψ j • (Sdw (N := N) hk).Γ₁.G) + r.ej j)
  have lf : ∀ n, (Enum.list (α := Fin n)).length = n := fun n => by simp [Enum.list]
  have eA : (S 34).length = A.length := by
    rw [t34, List.length_replicate, lA, lf, lf, len_enum_col]; ring
  have eB : (S 30).length = B.length := by
    rw [t30, lB, lf, lf]; ring
  have eC : (S 32).length = C.length := by
    rw [t32, lC, lf]; ring
  have eD : (S 36).length = D.length := by
    rw [t36, List.length_replicate, lD, lf, len_enum_col]; ring
  have eE : (S 15).length = E.length := by rw [t15l, len_enc]
  have hR : (S 0).length = A.length + B.length + C.length + D.length + E.length := by
    rw [← eA, ← eB, ← eC, ← eD, ← eE, h0, t34, t30, t32, t36, t15l, ctLen]
    simp
  rw [eA, eB, eC, eD, eE, takeD_of_length, takeD_of_length, takeD_of_length, takeD_of_length,
    takeD_of_length, reg5 _ _ _ _ _ _ hR]
  rfl

end AdvancedEncryption.DualUse.Prog
