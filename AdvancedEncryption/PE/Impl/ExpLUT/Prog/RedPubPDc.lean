import PE.Impl.ExpLUT.Prog.RedPubPBound
import PE.Impl.ExpLUT.AH.Conf
import SigabaNeoStd.Machines.Prog.VecBound
/-!
# The public-key component at the concrete dimensions (package G2, `pubP`)

At `Dc` (`N = 2^24`, `K = 2^16`, `b = 22`, `m̄ ≤ 2^42`), with the operation area `Mo = 2^41`,
loop counters within `Bc = 2^42` and every other register within `Mb = 2^102`:

* **`law_pubP_Dc`**, **`wf_pubP_Dc`**;
* **`len_pubP_Dc`**: from the input bound `io2 (2^101) 0 0`, the output is within `2^102` bits;
* **`time_pubP_Dc`**: at most `2^450` steps;
* **`size_pubP_Dc`**: at most `2^200` states.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.ExpLUT.Params
open scoped SigabaNeo.Tape.Prog
open SigabaNeo.Tape.RingVM.Hash

/-! ### Counts -/

theorem pnE_fin (n : ℕ) : pnE (Fin n) = n := by simp [pnE, enum_fin]

theorem pnE_prod (α β : Type) [Enum α] [Enum β] : pnE (α × β) = pnE α * pnE β :=
  Enum.length_prod

theorem pnE_bcol (D : Dims) : pnE (BCol (Wb D) D.K) = D.mb + D.K := by
  show ((Enum.list (α := Wb D)).map Sum.inl ++ (Enum.list (α := Fin D.K)).map Sum.inr).length = _
  simp [enum_fin]

theorem pencLen_mpkEnc (D : Dims) : pencLen (mpkEnc D) =
    pnE (Fin 2) * (pnE (BCol (Wb D) D.K) * (D.N * D.K)) +
      (pnE (Jh D) * (pnE (Fin 2) * (pnE (Col D.K) * (D.N * D.K))) +
      (pnE Pos * (pnE (Col D.K) * (D.N * D.K)) +
      (pnE (Fin 2) * (pnE (Col D.K) * (D.N * D.K)) +
      (pnE Pos * (pnE (Dig D.K) * (pnE (Fin 2) * (pnE (Col D.K) * (D.N * D.K)))) +
      (pnE (Fin D.b) * (pnE (Dig D.K) * (pnE (Fin 2) * (pnE (Col D.K) * (D.N * D.K)))) +
        pnE (Fin 2) * (D.N * D.K)))))) := rfl

theorem pDc_K : Dc.K = 2 ^ 16 := by show Kc = _; rw [Kc_def]
theorem pDc_N : Dc.N = 2 ^ 24 := rfl
theorem pDc_mb : Dc.mb ≤ 2 ^ 42 := by show mbar ≤ _; rw [mbar_def, Kc_def]; norm_num [en]
theorem pnE_pos16 : pnE Pos = 16 := rfl

set_option exponentiation.threshold 2000 in
/-- **The template lengths at `Dc`.** -/
theorem tmBase_Dc_le' (n : ℕ) : tmBase Dc n ≤ 2 ^ 102 := by
  have hmb := pDc_mb
  have hp := pencLen_mpkEnc Dc
  unfold tmBase
  split <;> (try rw [hp]) <;> (try simp only [pnE_bcol, pnE_prod, pnE_fin, pnE_pos16, w8_len, Col,
    Dig, Jh, Wb]) <;> (try rw [pDc_K]) <;> (try rw [pDc_N]) <;> (try rw [Dc_b]) <;>
    (try generalize Dc.mb = m at hmb) <;> norm_num <;> nlinarith

set_option exponentiation.threshold 2000 in
theorem ctr_Dc' : pnE (Jh Dc) ≤ 2 ^ 42 ∧ pnE Pos ≤ 2 ^ 42 ∧ pnE (Col Dc.K) ≤ 2 ^ 42 ∧
    pnE (Wb Dc) ≤ 2 ^ 42 := by
  have hmb := pDc_mb
  simp only [pnE_prod, pnE_fin, pnE_pos16, w8_len, Col, Jh, Wb]
  rw [pDc_K, Dc_b]
  refine ⟨by norm_num, by norm_num, by norm_num, hmb⟩

theorem tm_le_Dc (r : Fin 200) : tm Dc r ≤ pBf (2 ^ 41) (2 ^ 42) (2 ^ 102) r :=
  tm_le_pBf Dc (by rw [pDc_N]; norm_num) (by norm_num) (by rw [pDc_K]; norm_num) ctr_Dc'
    tmBase_Dc_le' r

/-! ### The component at `Dc` -/

theorem hyps_Dc : 2 ≤ Dc.N ∧ wSt * 2 ^ 7 ≤ 2 * Dc.N ∧ Dc.b ≤ 32 := by
  refine ⟨by rw [pDc_N]; norm_num, by rw [pDc_N]; norm_num [wSt, stateBits], by rw [Dc_b]; norm_num⟩

/-- **The law at `Dc`.** -/
theorem law_pubP_Dc (σ : RawSec Dc) :
    XProg.law (pubP Dc) (io2 (R := 245) ((rawEnc Dc).enc σ) [] []) =
      PMF.pure (io2 (R := 245) ((mpkEnc Dc).enc (redView Dc (rawF Dc σ)).1) [] []) :=
  law_pubP hyps_Dc.1 hyps_Dc.2.1 hyps_Dc.2.2 σ

theorem wf_pubP_Dc : (pubP Dc).WF := wf_pubP

set_option exponentiation.threshold 2000 in
/-- **The bounds at `Dc`**: from the input bound `io2 (2^101) 0 0`, the output within `2^102`
bits and at most `2^450` steps. -/
theorem bounds_pubP_Dc :
    XProg.lenBoundT (pubP Dc) (io2 (R := 245) (2 ^ 101) 0 0) ≤ io2 (R := 245) (2 ^ 102) 0 0 ∧
      XProg.timeBoundT (pubP Dc) (io2 (R := 245) (2 ^ 101) 0 0) ≤ 2 ^ 450 := by
  have hNK : Dc.N * Dc.K = 2 ^ 40 := by rw [pDc_N, pDc_K]; norm_num
  have hK : Dc.K ≤ 2 ^ 41 := by rw [pDc_K]; norm_num
  have hN : Dc.N ≤ 2 ^ 41 := by rw [pDc_N]; norm_num
  obtain ⟨hl, ht⟩ := bounds_pubP Dc (Mo := 2 ^ 41) (Bc := 2 ^ 42) (Mb := 2 ^ 102) (La := 2 ^ 101) (Lb := 0) (by rw [hNK]; norm_num)
    hK hN (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) tm_le_Dc
    (by rw [hNK]; norm_num)
  have hro : tm Dc rOut ⊔ 2 ^ 102 = 2 ^ 102 := by
    have := tm_le_Dc rOut
    have h2 : pBf (2 ^ 41) (2 ^ 42) (2 ^ 102) rOut = 2 ^ 102 := rfl
    rw [h2] at this
    exact max_eq_right this
  rw [hro] at hl
  refine ⟨hl, ht.trans ?_⟩
  rw [Dc_b]
  unfold pIB
  norm_num

theorem len_pubP_Dc :
    XProg.lenBoundT (pubP Dc) (io2 (R := 245) (2 ^ 101) 0 0) ≤ io2 (R := 245) (2 ^ 102) 0 0 :=
  bounds_pubP_Dc.1

theorem time_pubP_Dc : XProg.timeBoundT (pubP Dc) (io2 (R := 245) (2 ^ 101) 0 0) ≤ 2 ^ 450 :=
  bounds_pubP_Dc.2

/-! ### The state count -/

theorem psize_clr (t : Fin 247) : (Prog.clr t).size = 36 := rfl

theorem psize_clrL : ∀ l : List (Fin 247), (SigabaNeo.Tape.RingVM.Handler.clrL l).size = 36 * l.length + 36
  | [] => rfl
  | t :: l => by
    show (Prog.clr t).size + (SigabaNeo.Tape.RingVM.Handler.clrL l).size = _
    rw [psize_clr, psize_clrL l, List.length_cons]; ring

theorem psize_tmplsP (c : Fin 247) (m : ℕ) : ∀ l : List (Fin 247 × ℕ), (∀ p ∈ l, p.2 < 2 ^ m) →
    (tmplsP c l).size ≤ l.length * (195 * m + 36) + 36
  | [], _ => by show (Prog.prim (.copy c c)).size ≤ _; simp [Prog.size, Prim.pad]
  | p :: l, h => by
    show (XProg.natP p.1 c p.2).size + (tmplsP c l).size ≤ _
    have h1 := XProg.size_natP_le p.1 c p.2 m (h p List.mem_cons_self)
    have h2 := psize_tmplsP c m l fun q hq => h q (List.mem_cons_of_mem _ hq)
    rw [List.length_cons]
    nlinarith

theorem plength_tList (D : Dims) : (SigabaNeo.Tape.RingVM.Handler.tList D.N D.K ra rb (tm D)).length = 201 := by
  simp only [SigabaNeo.Tape.RingVM.Handler.tList, List.length_cons, List.length_map]
  rfl

set_option maxRecDepth 100000 in
theorem plength_postTapes : SigabaNeo.Tape.RingVM.Handler.postTapes.length = 246 := by
  rw [SigabaNeo.Tape.RingVM.Handler.postTapes]; rfl

set_option maxRecDepth 100000 in
/-- **The state count of the public-key component**, for template lengths below `2^m`. -/
theorem size_pubP (D : Dims) (m : ℕ) (hK : D.K < 2 ^ m) (hN : D.N < 2 ^ m)
    (hNK : D.N * D.K < 2 ^ m) (htm : ∀ r, tm D r < 2 ^ m) :
    (pubP D).size ≤ 201 * (195 * m + 36) + 20000 + 15000 * (478 + 241 * D.b) := by
  have h1 : (SigabaNeo.Tape.RingVM.Handler.inP ra rb).size = 144 := rfl
  have h2 : (SigabaNeo.Tape.RingVM.Handler.onesP ⨾ Prog.clr SigabaNeo.Tape.RingVM.Handler.cT).size ≤ 1000 := by decide
  have h3 : (SigabaNeo.Tape.RingVM.Handler.postP rOut).size = 36 + (36 * SigabaNeo.Tape.RingVM.Handler.postTapes.length + 36) := by
    show (Prog.cp _ _).size + (SigabaNeo.Tape.RingVM.Handler.clrL _).size = _
    rw [psize_clrL]; rfl
  have h4 : SigabaNeo.Tape.RingVM.Handler.postTapes.length = 246 := plength_postTapes
  have h5 := psize_tmplsP SigabaNeo.Tape.RingVM.Handler.cT m (SigabaNeo.Tape.RingVM.Handler.tList D.N D.K ra rb (tm D)) (by
    intro p hp
    rcases SigabaNeo.Tape.RingVM.Handler.mem_tList.mp hp with rfl | rfl | rfl | ⟨r, -, -, rfl⟩
    · exact hK
    · exact hN
    · exact hNK
    · exact htm r)
  rw [plength_tList] at h5
  have h6 : (compile (pubC D)).size ≤ 15000 * (478 + 241 * D.b) := by
    rw [size_compile, ← vmCount_pubC]; exact vmSize_le _
  show (SigabaNeo.Tape.RingVM.Handler.inP ra rb).size + ((tmplsP SigabaNeo.Tape.RingVM.Handler.cT (SigabaNeo.Tape.RingVM.Handler.tList D.N D.K ra rb (tm D))).size +
    (SigabaNeo.Tape.RingVM.Handler.onesP ⨾ Prog.clr SigabaNeo.Tape.RingVM.Handler.cT).size) + ((Prog.prim (.cons (tWd r1) true)).size +
    ((compile (pubC D)).size + (SigabaNeo.Tape.RingVM.Handler.postP rOut).size)) ≤ _
  have h7 : (Prog.prim (.cons (tWd r1) true) : SigabaNeo.Tape.Prog 247).size = 60 := rfl
  rw [h1, h3, h4, h7]
  omega

set_option exponentiation.threshold 2000 in
/-- **The state count at `Dc`.** -/
theorem size_pubP_Dc : (pubP Dc).size ≤ 2 ^ 200 := by
  have hle := size_pubP Dc 103 (by rw [pDc_K]; norm_num) (by rw [pDc_N]; norm_num)
    (by rw [pDc_K, pDc_N]; norm_num) (fun r => lt_of_le_of_lt
      ((tm_le_Dc r).trans (pBf_le (by norm_num) (by norm_num) r)) (by norm_num))
  rw [Dc_b] at hle
  exact hle.trans (by norm_num)

/-! ### Summary -/

/-- **The public-key component at `Dc`**: well formed, the law `law_pub` of `Generic.Comps`
(`sp.pub σ = (mpkEnc Dc).enc (redView Dc (rawF Dc σ)).1`), from the input bound
`io2 (2^101) 0 0` the output within `2^102 ≤ 2^125` bits and at most `2^450` steps, at most
`2^200` states. -/
theorem pubP_Dc_spec :
    (pubP Dc).WF ∧
      (∀ σ : RawSec Dc, XProg.law (pubP Dc) (io2 (R := 245) ((rawEnc Dc).enc σ) [] []) =
        PMF.pure (io2 (R := 245) ((mpkEnc Dc).enc (redView Dc (rawF Dc σ)).1) [] [])) ∧
      XProg.lenBoundT (pubP Dc) (io2 (R := 245) (2 ^ 101) 0 0) ≤ io2 (R := 245) (2 ^ 102) 0 0 ∧
      XProg.timeBoundT (pubP Dc) (io2 (R := 245) (2 ^ 101) 0 0) ≤ 2 ^ 450 ∧
      (pubP Dc).size ≤ 2 ^ 200 :=
  ⟨wf_pubP_Dc, law_pubP_Dc, len_pubP_Dc, time_pubP_Dc, size_pubP_Dc⟩

end AdvancedEncryption.ExpLUT.Prog.RedPubP
