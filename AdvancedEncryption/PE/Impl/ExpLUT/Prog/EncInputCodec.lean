import PE.Impl.ExpLUT.Prog.EncInputPhase

/-! # Attribute loops with the scheme's sixteen-position codecs -/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram

/-- Natural positions read in the same order as the scheme's `Pos` enumeration. -/
def posAt (t : ℕ) : Pos := (Enum.list (α := Pos)).getD t ⟨0, by decide⟩

/-- Sixteen encoded position blocks are exactly the scheme's family codec. -/
theorem posBlocks_codec {α : Type} {n : ℕ} (e : FixedEnc α n) (F : Pos → α) :
    blockStream (fun t ↦ e.enc (F (posAt t))) 0 16 = (FixedEnc.fun (α := Pos) e).enc F := by
  have h := blockStream_enum (fun p : Pos ↦ e.enc (F p)) ⟨0, by decide⟩
  simpa only [len_fin, w8_len, posAt, FixedEnc.fun, FixedEnc.encList, List.flatMap_map] using h

/-- The attribute's sixteen symbols are the actual 128-bit input encoding. -/
theorem attributeBlocks_codec (x : Attribute w8) :
    blockStream (fun t ↦ symbolBits w8 (x (posAt t))) 0 16 = encAttribute w8 x := by
  have h := blockStream_enum (fun p : Pos ↦ symbolBits w8 (x p)) ⟨0, by decide⟩
  simp only [len_fin, w8_len] at h
  rw [show blockStream (fun t ↦ symbolBits w8 (x (posAt t))) 0 16 =
    (Enum.list (α := Pos)).flatMap (fun p ↦ symbolBits w8 (x p)) from h]
  change _ = (List.ofFn x).flatMap (symbolBits w8)
  rw [List.ofFn_eq_map, List.flatMap_map]
  rfl

variable (D : Dims)

/-- Bottom rows computed by the attribute loop are the scheme's ciphertext field. -/
theorem inputBottom_encrypt (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) (t : Pos) :
    inputBottom D wSt (x t) r.s (mpk.a t) (r.ein t) =
      (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).cinBot t := rfl

/-- Digit rows computed by the attribute loop are the scheme's ciphertext field. -/
theorem inputDigits_encrypt (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) (t : Pos) :
    inputDigits D wSt r.s (x t) (mpk.a t) (r.ein t) (mpk.Ain t) (r.edin t) =
      (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).cin t := by
  funext d
  unfold inputDigits digitRows
  rw [decRM_wd]
  rfl

/-- The actual bottom-row program writes `ct.cinBot` for all sixteen attributes. -/
theorem run_cinbotP_ciphertext (S : Store 104) (h : TailOK D.K D.N S)
    (hN : 2 ≤ D.N) (hw : wSt * 128 ≤ 2 * D.N)
    (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos)
    (hs : S 1 = wd D r.s) (h1 : S 16 = wd D 1)
    (hτ : ∀ i < 8, τT S i = 2 * D.N - wSt * 2 ^ (7 - i)) (hcount : (S 35).length = 16)
    (hx : S 2 = encAttribute w8 x)
    (ha : S 4 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a)
    (he : S 7 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc r.ein)
    (hout : 16 * ((D.K + D.K) * (D.N * D.K)) ≤ (S 0).length) :
    cinbotP.run S = cbG S ([], [], [],
      (S 0 ++ (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc
        (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).cinBot).drop
          (16 * ((D.K + D.K) * (D.N * D.K)))) := by
  have hc := run_cinbotP_stream D S h hN wSt hw r.s (fun t ↦ x (posAt t))
    (fun t ↦ mpk.a (posAt t)) (fun t ↦ r.ein (posAt t)) 0 16 [] [] [] hs h1 hτ hcount
    (by rw [attributeBlocks_codec, List.append_nil]; exact hx)
    (by rw [posBlocks_codec (vecE D (Col D.K)) mpk.a, List.append_nil]; exact ha)
    (by rw [posBlocks_codec (vecE D (Col D.K)) r.ein, List.append_nil]; exact he) hout
  rw [posBlocks_codec (vecE D (Col D.K))
    (fun t ↦ inputBottom D wSt (x t) r.s (mpk.a t) (r.ein t))] at hc
  exact hc

/-- The actual attribute digit loop writes `ct.cin` for all sixteen positions. -/
theorem run_cinP_ciphertext (S : Store 104) (h : TailOK D.K D.N S)
    (hN : 2 ≤ D.N) (hw : wSt * 128 ≤ 2 * D.N)
    (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos)
    (hs : S 1 = wd D r.s) (h1 : S 16 = wd D 1)
    (hτ : ∀ i < 8, τT S i = 2 * D.N - wSt * 2 ^ (7 - i))
    (hentries : (S 34).length = D.K + D.K + (D.K + D.K)) (hcount : (S 35).length = 16)
    (hx : S 3 = encAttribute w8 x)
    (ha : S 5 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a)
    (he : S 8 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc r.ein)
    (hcopy : S 6 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a)
    (hA : S 9 = (FixedEnc.fun (α := Pos)
      (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Ain)
    (hE : S 10 = (FixedEnc.fun (α := Pos)
      (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc r.edin)
    (hout : 16 * ((D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K)))) ≤ (S 0).length) :
    cinP.run S = ciG S ([], [], [], [], [], [],
      (S 0 ++ (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
        (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).cin).drop
          (16 * ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K)))))) := by
  have hc := run_cinP_stream D S h hN wSt hw r.s (fun t ↦ x (posAt t))
    (fun t ↦ mpk.a (posAt t)) (fun t ↦ r.ein (posAt t))
    (fun t ↦ mpk.Ain (posAt t)) (fun t ↦ r.edin (posAt t))
    0 16 [] [] [] [] [] [] hs h1 hτ hentries hcount
    (by rw [attributeBlocks_codec, List.append_nil]; exact hx)
    (by rw [posBlocks_codec (vecE D (Col D.K)) mpk.a, List.append_nil]; exact ha)
    (by rw [posBlocks_codec (vecE D (Col D.K)) r.ein, List.append_nil]; exact he)
    (by rw [posBlocks_codec (vecE D (Col D.K)) mpk.a, List.append_nil]; exact hcopy)
    (by rw [posBlocks_codec (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))) mpk.Ain,
      List.append_nil]; exact hA)
    (by rw [posBlocks_codec (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))) r.edin,
      List.append_nil]; exact hE) hout
  rw [posBlocks_codec (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))
    (fun t ↦ inputDigits D wSt r.s (x t) (mpk.a t) (r.ein t) (mpk.Ain t) (r.edin t))] at hc
  have hf : (fun t ↦ inputDigits D wSt r.s (x t) (mpk.a t) (r.ein t) (mpk.Ain t) (r.edin t)) =
      (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).cin :=
    funext (inputDigits_encrypt D mpk x μ r)
  rw [hf] at hc
  exact hc

/-- The final two row programs produce the exact `c0` and `cm` ciphertext fields in order. -/
theorem run_lastRows_ciphertext (S : Store 104) (h : TailOK D.K D.N S)
    (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos)
    (hs : S 1 = wd D r.s) (h1 : S 16 = wd D 1) (hμ : S 15 = [μ])
    (hzero : S 37 = List.replicate (D.N * D.K) false)
    (hA : S 11 = (matE D (Fin 2) (Col D.K)).enc mpk.A0)
    (he : S 12 = (vecE D (Col D.K)).enc r.e0)
    (hd : S 13 = (vecE D (Fin 2)).enc mpk.d) (hem : S 14 = wd D r.em) :
    ((Prog.seq c0P cmP).run S) 0 =
      ((((S 0 ++ (vecE D (Col D.K)).enc
        (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).c0).drop
          ((D.K + D.K) * (D.N * D.K))) ++ wd D
        (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).cm).drop (D.N * D.K)) := by
  let T := c0Store D.N D.K S
  have ht : c0P.run S = T := run_c0P D.K_pos h
  have hT : TailOK D.K D.N T := by
    apply h.of_agree
    · intro i hi; fin_cases i <;> simp [T, c0Store, h.hs] at hi ⊢
    · intro i hi; fin_cases i <;> simp [T, c0Store] at hi ⊢
  have hfirst := run_c0P_scheme D S h mpk.A0 r.e0 r.s [] [] hs h1
    (by simpa using hA) (by simpa using he)
  rw [ht] at hfirst
  have hlast := run_cmP_scheme D T hT μ mpk.d r.s r.em [] []
    (by simpa [T, c0Store] using hs) (by simpa [T, c0Store] using hμ)
    (by simpa [T, c0Store] using h1) (by simpa [T, c0Store] using hzero)
    (by simpa [T, c0Store] using hd) (by simpa [T, c0Store] using hem)
  rw [Prog.run_seq, ht, hlast, hfirst]
  rfl

end AdvancedEncryption.ExpLUT.Prog.EncW
