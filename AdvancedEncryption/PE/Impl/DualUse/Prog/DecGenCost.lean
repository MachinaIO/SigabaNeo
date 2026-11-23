import PE.Impl.DualUse.Prog.DecGenP
import PE.Impl.DualUse.Prog.KeyGenCost

/-!
# The time of the compiled `Dec`

`ph_decGenP`: as `ph_keyGenP`, for `decGenP`: the guard, the parser (four frames), the front end,
the `c_f̂` block (a phase on stores with tape `0` below `16 (nDec + 2)` and tape `1` below the front
end's output bound), the end of decryption `decFinB` (uniform bounds), the dummy and long branches.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (leP unfrP frP leT unfrT frT tailsP ubp_tailsP ubp_prim0)
open AdvancedEncryption.PE.Gates.BPWord
open scoped SigabaNeo.Tape.Prog

theorem tbD_decFP : SigabaNeo.Tape.Prog.tbD ProgKeyR.decFP = 8 := by
  have h4 : SigabaNeo.Tape.Prog.matMulP.tbD = 8 := by decide +kernel
  have h5 : SigabaNeo.Tape.Prog.addRWP.tbD = 3 := by decide +kernel
  have h6 : SigabaNeo.Tape.Prog.subRWP.tbD = 3 := by decide +kernel
  simp only [ProgKeyR.decFP, SigabaNeo.Tape.Prog.tbD, SigabaNeo.Tape.Prog.tbD_map, h4, h5, h6]
  rfl

theorem tbC_decFP : SigabaNeo.Tape.Prog.tbC ProgKeyR.decFP ≤ 6000 := by
  have h4 : SigabaNeo.Tape.Prog.matMulP.tbC = 1716 := by decide +kernel
  have h5 : SigabaNeo.Tape.Prog.addRWP.tbC = 210 := by decide +kernel
  have h6 : SigabaNeo.Tape.Prog.subRWP.tbC = 210 := by decide +kernel
  simp only [ProgKeyR.decFP, SigabaNeo.Tape.Prog.tbC, SigabaNeo.Tape.Prog.tbC_map, h4, h5, h6]
  norm_num

theorem tbD_ballR : SigabaNeo.Tape.Prog.tbD (Prog.map ProgKeyR.ballR SigabaNeo.Tape.Prog.ballP) = 3 := by
  rw [SigabaNeo.Tape.Prog.tbD_map]; decide +kernel

theorem tbC_ballR : SigabaNeo.Tape.Prog.tbC (Prog.map ProgKeyR.ballR SigabaNeo.Tape.Prog.ballP) = 419 := by
  rw [SigabaNeo.Tape.Prog.tbC_map]; decide +kernel

/-! ### The end of decryption -/

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

theorem getP_eq (o L : ℕ) (dst : Fin 256) : getP o L dst = getAt o L 0 dst 102 103 104 := rfl

theorem getT_mono' {o L M o' L' M' : ℕ} (ho : o ≤ o') (hL : L ≤ L') (hM : M ≤ M') :
    getT o L M ≤ getT o' L' M' := by
  unfold getT prefT
  gcongr

theorem ub_getAt_le {n : ℕ} (o L B : ℕ) (src dst tmp a b : Fin n) (M : ℕ) (ho : o ≤ B) (hL : L ≤ B) :
    UB (getAt o L src dst tmp a b) M (getT B B M) (M + 1 + B) :=
  (ub_getAt o L src dst tmp a b M).mono (getT_mono' ho hL le_rfl) (by omega)

/-- The time of `decFinB` from tapes below `M`, offsets and lengths below `B`. -/
def decFT (K B M : ℕ) : ℕ :=
  let M1 := M + 1 + B
  let M2 := M1 + 1 + B
  let M3 := M2 + 1 + B
  let M4 := M3 + 1 + B
  let M5 := M4 + 1 + B
  let M6 := M5 + 1 + B
  let M7 := M6 + (Algo.decRadW K).length + 1
  let M8 := M7 + 1 + K
  getT B B M + (getT B B M1 + (getT B B M2 + (getT B B M3 + (getT B B M4 + (getT B B M5 +
    (putT (Algo.decRadW K).length M6 + (tmplT (decTmpl c) M7 + (6000 * (M7 + 1) ^ 8 +
    (((2 * (M7 + 1) + 3) + (2 * (M7 + 1) + 3)) + (prefT K M7 + ((2 * (M8 + 1) + 3) +
    (419 * (M8 + 1) ^ 3 + ((2 * (M8 + 1) + 3) +
    ((max (putT ([true, false, false] : List Bool).length M8)
      (putT ([true, true, false] : List Bool).length M8) + 1) +
    (256 * (2 * (max (M8 + ([true, false, false] : List Bool).length + 1)
        (M8 + ([true, true, false] : List Bool).length + 1) + 1) + 3) +
      (2 * (max (M8 + ([true, false, false] : List Bool).length + 1)
        (M8 + ([true, true, false] : List Bool).length + 1) + 1) + 3))))))))))))))))

/-- The bound after `decFinB`. -/
def decFG (K B M : ℕ) : ℕ :=
  max (M + 1 + B + 1 + B + 1 + B + 1 + B + 1 + B + 1 + B + (Algo.decRadW K).length + 1 + 1 + K +
    ([true, false, false] : List Bool).length + 1)
    (M + 1 + B + 1 + B + 1 + B + 1 + B + 1 + B + 1 + B + (Algo.decRadW K).length + 1 + 1 + K +
    ([true, true, false] : List Bool).length + 1)

variable (hk c) in
/-- The offsets and lengths read by `decFinB`. -/
def decOffs : List ℕ :=
  [fixLen (skEnc hk c) + lPsi (N := N) (K := K) hk, c.d * (N * K), lenPK hk c,
    fixLen (skEnc hk c) + lPsi (N := N) (K := K) hk + c.d * (N * K), Algo.nT k * (N * K),
    lenPK hk c + c.d * (N * K), lenPK hk c + c.d * (N * K) + Algo.nT k * (N * K),
    2 * k * (N * K), fixLen (skEnc hk c) + fixLen (ctEnc hk c) - N * K, N * K]

theorem noGrow_ballR : (Prog.map ProgKeyR.ballR SigabaNeo.Tape.Prog.ballP).NoGrow := by
  show (Prog.map _ _).noGrowB = true
  rw [Prog.noGrowB_map]; exact SigabaNeo.Tape.Prog.noGrow_ballP

set_option maxHeartbeats 2000000 in
theorem ub_decFinB (B M : ℕ) (hB : ∀ x ∈ decOffs hk c, x ≤ B) (hT : ∀ x ∈ decTmpl c, x.2 ≤ M) :
    UB (decFinB hk c) M (decFT (c := c) K B M) (decFG K B M) := by
  have hb := fun x (hx : x ∈ decOffs hk c) => hB x hx
  simp only [decOffs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hb
  have hT' : ∀ x ∈ decTmpl c, x.2 ≤ M + 6 * (1 + B) + K + 1 := fun x hx => (hT x hx).trans (by omega)
  rw [decFinB, getP_eq, getP_eq, getP_eq, getP_eq, getP_eq, getP_eq]
  refine ((ub_getAt_le _ _ B 0 30 102 103 104 M b1 b2).seq <|
    (ub_getAt_le _ _ B 0 31 102 103 104 _ b3 b2).seq <|
    (ub_getAt_le _ _ B 0 32 102 103 104 _ b4 b5).seq <|
    (ub_getAt_le _ _ B 0 33 102 103 104 _ b6 b5).seq <|
    (ub_getAt_le _ _ B 0 34 102 103 104 _ b7 b8).seq <|
    (ub_getAt_le _ _ B 0 35 102 103 104 _ b9 b10).seq <|
    (ub_putW 4 (Algo.decRadW K) _).seq <|
    (ub_tmplP 120 (decTmpl c) _ (fun x hx => (hT' x hx).trans (by
      simp only [Algo.decRadW, SigabaNeo.Lattices.Algo.length_toBits]; omega))
      (by simp [decTmpl])).seq <|
    ((ub_frame eKR ProgKeyR.decFP ProgKeyR.noGrow_decFP _).mono
      ((SigabaNeo.Tape.Prog.timeBound_le _ ProgKeyR.noGrow_decFP _).trans
        (by rw [tbD_decFP]; first | exact Nat.mul_le_mul_right _ tbC_decFP | skip)) le_rfl).seq <|
    (show UB (prog (SigabaNeo.Tape.Prog.cp 28 39 ⨾ SigabaNeo.Tape.Prog.clr 39)) _ _ _ from
      fun ℓ hℓ => ((ubp_prim0 (.copy 28 39) rfl _).seq (ubp_prim0 (.clear 39) rfl _)) ℓ hℓ).seq <|
    (ub_prefP K 28 39 41 42 _).seq <| (ub_clear 28 _).seq <|
    ((ub_frame eKR _ noGrow_ballR _).mono
      ((SigabaNeo.Tape.Prog.timeBound_le _ noGrow_ballR _).trans
        (by rw [tbD_ballR, tbC_ballR])) le_rfl).seq <|
    (ub_clear 0 _).seq <|
    (ub_ifBit (ub_putW 0 [true, false, false] _) (ub_putW 0 [true, true, false] _)).seq <|
    ((ub_clearL _ clrAll).mono (Nat.add_le_add_right (Nat.mul_le_mul_right _ length_clrAll_le) _)
      le_rfl)).mono (le_of_eq rfl) (le_of_eq rfl)

/-! ### The parser and the program -/

/-- The time of the parser of `Dec` from tapes below `M`. -/
def parse4T (M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + (unfrT M + (unfrT (2 * M) + (unfrT (2 * (2 * M)) + (unfrT (2 * (2 * (2 * M))) +
    ((2 * (2 * (2 * (2 * (2 * M))) + 1) + 3) + (2 * (2 * (2 * (2 * (2 * M))) + 1) + 3))))))

theorem ph_parse4 (M : ℕ) {β : Fin 256 → ℕ} (hβ : ∀ i, β i ≤ M) :
    Ph (prog parse4P) β (parse4T M)
      (fun i => if i ∈ [254, 253, 0, 1, 251, 252, 255] then 2 * (2 * (2 * (2 * M))) else β i) := by
  refine ph_of_ub_ws _ (fun i hi => ?_) (fun ℓ hℓ => ?_) hβ
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hi
    have hu : ∀ d : Fin 256, (d = 253 ∨ d = 0 ∨ d = 1) → (Prog.map (uU d) unfrP).Preserves i :=
      fun d hd => preserves_map _ i _ (fun j hj => by
        exfalso; fin_cases j <;> simp [uU] at hj <;> rcases hd with rfl | rfl | rfl <;> simp_all)
    exact ⟨by simp [Prog.Preserves, Prim.writes, n1], hu 253 (Or.inl rfl), hu 0 (by simp),
      hu 1 (by simp), hu 0 (by simp), by simp [Prog.Preserves, Prim.writes, n2],
      by simp [Prog.Preserves, Prim.writes, n7]⟩
  · exact ((ubp_prim0 (.clear 254) rfl M).seq ((ubp_unfrP_map _ M).seq ((ubp_unfrP_map _ _).seq
      ((ubp_unfrP_map _ _).seq ((ubp_unfrP_map _ _).seq ((ubp_prim0 (.clear 253) rfl _).seq
        (ubp_prim0 (.clear 255) rfl _))))))) ℓ hℓ

theorem ub_dumDec (M : ℕ) : UB dumDec M ((2 * (M + 1) + 3) + putT 3 M) (M + 3 + 1) :=
  (ub_clear 0 M).seq (ub_putW 0 [true, false, false] M)

variable (hk c) in
/-- The time of the branches of `Dec`. -/
def decBT (W B Tb Gb : ℕ) : ℕ :=
  let Mβ := max (16 * (nDec hk c + 2)) (frontL c.L W)
  max ((2 * (Mβ + 1) + 3) + (Tb + decFT (c := c) K B Gb))
    (max (longT Mβ) ((2 * (Mβ + 1) + 3) + putT 3 Mβ) + 1) + 1

variable (hk c) in
/-- The bound of tape `0` after the branches of `Dec`. -/
def decBL (W B Gb : ℕ) : ℕ :=
  let Mβ := max (16 * (nDec hk c + 2)) (frontL c.L W)
  max (decFG K B Gb) (max Mβ (Mβ + 3 + 1))

variable (hk c) in
/-- **The time of `Dec`'s program** from its input bound. -/
def decGT (W B Tb Gb : ℕ) : ℕ :=
  leT (nDec hk c) (nDec hk c + 1) + (max (2 * (nDec hk c + 2 + 1) + 3)
    (parse4T (nDec hk c + 2) + (frontT c.L W (16 * (nDec hk c + 2)) + (decBT hk c W B Tb Gb +
      (256 * (2 * (decBL hk c W B Gb + 1) + 3) + (2 * (decBL hk c W B Gb + 1) + 3))))) + 1)

variable (hk c) in
/-- The time of the branches of `Dec`. -/
def decBTF (LF B Tb Gb : ℕ) : ℕ :=
  let Mβ := max (16 * (nDec hk c + 2)) LF
  max ((2 * (Mβ + 1) + 3) + (Tb + decFT (c := c) K B Gb))
    (max (longT Mβ) ((2 * (Mβ + 1) + 3) + putT 3 Mβ) + 1) + 1

variable (hk c) in
/-- The bound of tape `0` after the branches of `Dec`. -/
def decBLF (LF B Gb : ℕ) : ℕ :=
  let Mβ := max (16 * (nDec hk c + 2)) LF
  max (decFG K B Gb) (max Mβ (Mβ + 3 + 1))

variable (hk c) in
/-- **The time of `Dec`'s program** from its input bound. -/
def decGTF (FT LF B Tb Gb : ℕ) : ℕ :=
  leT (nDec hk c) (nDec hk c + 1) + (max (2 * (nDec hk c + 2 + 1) + 3)
    (parse4T (nDec hk c + 2) + (FT + (decBTF hk c LF B Tb Gb +
      (256 * (2 * (decBLF hk c LF B Gb + 1) + 3) + (2 * (decBLF hk c LF B Gb + 1) + 3))))) + 1)

/-- **The time and the output bound of `Dec`'s program.** -/
theorem ph_decGenF {R : ℕ} {e : Fin (R + 2) ↪ Fin 256} (he : FrEmb e) (hR : R ≤ 166)
    {fr : XProg (R + 2)} {FT FL : ℕ → ℕ}
    (hfr : ∀ T, Ph fr (io2 (R := R) T 0 0) (FT T) (io2 (R := R) (FL T) 0 0))
    (cfX : XProg 256) (B : ℕ) {Tb Gb : ℕ}
    (hcf : ∀ β : Fin 256 → ℕ, β 0 ≤ 16 * (nDec hk c + 2) → β 1 ≤ FL (16 * (nDec hk c + 2)) →
      (∀ i, β i ≤ max (16 * (nDec hk c + 2)) (FL (16 * (nDec hk c + 2)))) →
        Ph cfX β Tb (fun _ => Gb))
    (hB : ∀ x ∈ decOffs hk c, x ≤ B) (hT : ∀ x ∈ decTmpl c, x.2 ≤ Gb) :
    timeBoundT (decGenF hk c e fr cfX) (Prog.inputBound (255 : Fin 256) (nDec hk c + 1)) ≤
        decGTF hk c (FT (16 * (nDec hk c + 2))) (FL (16 * (nDec hk c + 2))) B Tb Gb ∧
      lenBoundT (decGenF hk c e fr cfX) (Prog.inputBound (255 : Fin 256) (nDec hk c + 1)) 0 ≤
        decBLF hk c (FL (16 * (nDec hk c + 2))) B Gb := by
  set n := nDec hk c with hn
  set a := 16 * (n + 2) with ha
  set FL := FL a with hFL
  set Mβ := max a FL with hMβ
  have h0 : ∀ i, Prog.inputBound (255 : Fin 256) (n + 1) i ≤ n + 1 := fun i => by
    simp only [Prog.inputBound, Function.update_apply]; split_ifs <;> omega
  have p1 := ph_guard n (n + 1) h0
  set β1 := fun i => if i ∈ [(254 : Fin 256), 253] then n + 1 + 1
    else Prog.inputBound (255 : Fin 256) (n + 1) i with hβ1
  have hβ1M : ∀ i, β1 i ≤ n + 2 := fun i => by
    simp only [hβ1]; split_ifs
    · omega
    · have := h0 i; omega
  have pA := (ph_prim (Prim.clear (255 : Fin 256)) β1).mono le_rfl
    (show 2 * (supB β1 + 1) + 3 ≤ 2 * (n + 2 + 1) + 3 by have := supB_le_of hβ1M; omega) le_rfl
  have p3 := ph_parse4 (n + 2) hβ1M
  set β3 := fun i => if i ∈ [(254 : Fin 256), 253, 0, 1, 251, 252, 255]
    then 2 * (2 * (2 * (2 * (n + 2)))) else β1 i with hβ3
  have hβ3e : ∀ j, (fun j => β3 (e j)) j ≤ io2 (R := R) a 0 0 j := by
    intro j
    simp only [hβ3, hβ1, Prog.inputBound, Function.update_apply, io2]
    by_cases hj : j.val = 0
    · have : e j = 1 := Fin.ext (by rw [he]; simp [hj])
      simp [this, hj, ha]; omega
    · have hv : (e j).val = j.val + 82 := by rw [he]; simp [hj]
      have hne : ∀ t : Fin 256, t.val ≤ 82 ∨ t.val ≥ 250 → e j ≠ t := fun t ht e' => by
        rw [← e', hv] at ht; have := j.isLt; omega
      have h1 : e j ≠ 254 := hne 254 (by simp)
      have h2 : e j ≠ 253 := hne 253 (by simp)
      have h3 : e j ≠ 0 := hne 0 (by simp)
      have h4 : e j ≠ 1 := hne 1 (by simp)
      have h5 : e j ≠ 251 := hne 251 (by simp)
      have h6 : e j ≠ 252 := hne 252 (by simp)
      have h7 : e j ≠ 255 := hne 255 (by simp)
      simp [h1, h2, h3, h4, h5, h6, h7, hj]
  have p4 := ph_frame e (p := fr) (β := β3) (hfr a |>.mono (fun j => hβ3e j) le_rfl le_rfl)
  set β4 := embedF e β3 (io2 (R := R) FL 0 0) with hβ4
  have hb40 : β4 0 = a := by
    rw [hβ4]
    rcases embedF_cases e β3 (io2 (R := R) FL 0 0) 0 with ⟨-, h⟩ | ⟨j, hj, -⟩
    · rw [h]; simp [hβ3]; omega
    · exact absurd hj (he.ne_zero j)
  have hb41 : β4 1 ≤ FL := by
    rw [hβ4, ← he.zero, embedF_apply_self]
    simp [io2]
  have hb4M : ∀ i, β4 i ≤ Mβ := by
    intro i
    rw [hβ4]
    rcases embedF_cases e β3 (io2 (R := R) FL 0 0) i with ⟨-, h⟩ | ⟨j, -, h⟩
    · rw [h]; simp only [hβ3, hβ1, Prog.inputBound, Function.update_apply]
      split_ifs <;> omega
    · rw [h]; simp only [io2]; split_ifs <;> omega
  have pwin := ((ph_prim (Prim.tail (1 : Fin 256)) β4).seq ((hcf _ (by simp [Prim.lenT, hb40])
    (by simp only [Prim.lenT, Function.update_apply]; split_ifs <;> omega)
    (fun i => by simp only [Prim.lenT, Function.update_apply]; split_ifs <;> have := hb4M i <;> omega)).seq
    (ph_of_ub (β := fun _ => Gb) (fun _ => le_rfl) (ub_decFinB B Gb hB hT)))).mono le_rfl
    (show _ ≤ (2 * (Mβ + 1) + 3) + (Tb + decFT (c := c) K B Gb) by
      have := supB_le_of hb4M; omega) le_rfl
  have plong := ph_of_ub hb4M (ub_longB Mβ)
  have pdum := ph_of_ub hb4M (ub_dumDec Mβ)
  have p5 := ph_ifBit' (1 : Fin 256) pwin (ph_ifBlank' (1 : Fin 256) plong pdum)
  have p5' := p5.mono le_rfl (le_of_eq rfl) (show _ ≤ fun _ => decBLF hk c FL B Gb from
    fun t => le_of_eq rfl)
  have p6 := ph_clearL clrAll (fun _ => decBLF hk c FL B Gb)
  have pB := p3.seq (p4.seq (p5'.seq p6))
  have pall := p1.seq (ph_ifBlank' (254 : Fin 256) pA pB)
  have h := pall (Prog.inputBound (255 : Fin 256) (n + 1)) le_rfl
  refine ⟨h.1.trans ?_, (h.2 0).trans ?_⟩
  · have hs := supB_const_le (k := 256) (decBLF hk c FL B Gb)
    have hl := length_clrAll_le
    have e : clrAll.length * (2 * (supB (fun _ : Fin 256 => decBLF hk c FL B Gb) + 1) + 3) +
        (2 * (supB (fun _ : Fin 256 => decBLF hk c FL B Gb) + 1) + 3) ≤
        256 * (2 * (decBLF hk c FL B Gb + 1) + 3) + (2 * (decBLF hk c FL B Gb + 1) + 3) := by
      have h2 : 2 * (supB (fun _ : Fin 256 => decBLF hk c FL B Gb) + 1) + 3 ≤
          2 * (decBLF hk c FL B Gb + 1) + 3 := by omega
      exact Nat.add_le_add (Nat.mul_le_mul hl h2) h2
    show _ ≤ leT n (n + 1) + (max (2 * (n + 2 + 1) + 3) (parse4T (n + 2) + (FT a +
      (decBTF hk c FL B Tb Gb + (256 * (2 * (decBLF hk c FL B Gb + 1) + 3) +
        (2 * (decBLF hk c FL B Gb + 1) + 3))))) + 1)
    gcongr
    exact Nat.le_of_eq rfl
  · simp [mem_clrAll, Prim.lenT, hβ1, Prog.inputBound]

/-- **The time and the output bound of `Dec`'s program** (date-window front end). -/
theorem ph_decGenP (cfX : XProg 256) (W B : ℕ) {Tb Gb : ℕ}
    (hcf : ∀ β : Fin 256 → ℕ, β 0 ≤ 16 * (nDec hk c + 2) → β 1 ≤ frontL c.L W →
      (∀ i, β i ≤ max (16 * (nDec hk c + 2)) (frontL c.L W)) → Ph cfX β Tb (fun _ => Gb))
    (hB : ∀ x ∈ decOffs hk c, x ≤ B) (hT : ∀ x ∈ decTmpl c, x.2 ≤ Gb) :
    timeBoundT (decGenP hk c cfX W) (Prog.inputBound (255 : Fin 256) (nDec hk c + 1)) ≤
        decGT hk c W B Tb Gb ∧
      lenBoundT (decGenP hk c cfX W) (Prog.inputBound (255 : Fin 256) (nDec hk c + 1)) 0 ≤
        decBL hk c W B Gb :=
  ph_decGenF frEmb_eFr (by norm_num) (frontSpec_frontP c.L W).ph cfX B hcf hB hT

end AdvancedEncryption.DualUse.Prog
