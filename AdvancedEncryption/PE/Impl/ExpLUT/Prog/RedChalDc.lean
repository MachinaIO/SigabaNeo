import PE.Impl.ExpLUT.Prog.RedChalBound

/-!
# The challenge component at the concrete dimensions (package G2, `chalP`)

At `Dc` (`N = 2^24`, `K = 2^16`, `b = 22`, `m̄ ≤ 2^42`), with the operation area `Mo = N K`,
loop counters within `2^56` and every other register within `2^110`:

* **`len_chalP_Dc`**: the output is within `2^110` bits;
* **`time_chalP_Dc`**: at most `2^450` steps;
* **`size_chalP_Dc`**: at most `2^200` states.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.ExpLUT.Params AdvancedEncryption.PE.Generic
open scoped SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Prog.RedVM

theorem len_sum' (α β : Type) [Enum α] [Enum β] :
    (Enum.list (α := α ⊕ β)).length = (Enum.list (α := α)).length + (Enum.list (α := β)).length := by
  simp [enum_sum]

theorem Dc_K : Dc.K = 2 ^ 16 := by show Kc = _; rw [Kc_def]
theorem Dc_N : Dc.N = 2 ^ 24 := rfl
theorem Dc_b : Dc.b = 22 := rfl
theorem Dc_mb : Dc.mb ≤ 2 ^ 42 := by show mbar ≤ _; rw [mbar_def, Kc_def]; norm_num [en]

set_option exponentiation.threshold 2000 in
/-- **The template lengths at `Dc`.** -/
theorem tmBase_Dc_le (n : ℕ) : tmBase Dc n ≤ 2 ^ 110 := by
  have hr : (circParamsD Dc).rows ≤ 2 ^ 51 := rowsD_Dc_le
  have hmb := Dc_mb
  unfold tmBase
  split <;> (try simp only [FixedEnc.len, nE, BCol, Wb, Jh, Col, Pos, Dig, len_sum',
    length_enum_prod, len_fin, floodEnc, ctEnc, FixedEnc.comap, FixedEnc.prod]) <;>
    (try rw [Dc_K]) <;> (try rw [Dc_N]) <;> (try rw [Dc_b]) <;>
    (try generalize (circParamsD Dc).rows = r at hr) <;>
    (try generalize Dc.mb = m at hmb) <;>
    norm_num [w8, Width.len] <;> nlinarith

set_option exponentiation.threshold 2000 in
theorem ctr_Dc : Dc.K ≤ 2 ^ 56 ∧ Dc.b * 2 ≤ 2 ^ 56 ∧ nE (Dig Dc.K × Col Dc.K) ≤ 2 ^ 56 ∧
    nE (Pos × Dig Dc.K × Col Dc.K) ≤ 2 ^ 56 ∧ nE (Col Dc.K) ≤ 2 ^ 56 ∧ nE (Wb Dc) ≤ 2 ^ 56 := by
  have hmb := Dc_mb
  simp only [nE, Col, Pos, Dig, Wb, length_enum_prod, len_fin]
  rw [Dc_K, Dc_b]
  norm_num [w8, Width.len]
  omega

set_option exponentiation.threshold 2000 in
theorem rawEnc_len_Dc : (rawEnc Dc).len ≤ 2 ^ 110 := by
  simp only [FixedEnc.len, rawEnc, FixedEnc.prod, BCol, Wb, Jh, Col, Pos, Dig, PrI, len_sum',
    length_enum_prod, len_fin, instEnc, FixedEnc.comap, floodEnc, zrEnc, attrEnc, rEnc]
  have hr : (circParamsD Dc).rows ≤ 2 ^ 51 := rowsD_Dc_le
  have ht : (setting Dc).τ = Dc.K := rfl
  have hb : (setting Dc).b = Dc.b := rfl
  rw [ht, hb]
  generalize (circParamsD Dc).rows = r at hr
  rw [Dc_K, Dc_N, Dc_b]
  have hmb := Dc_mb
  generalize Dc.mb = m at hmb
  norm_num [w8, Width.len]
  nlinarith

set_option exponentiation.threshold 2000 in
theorem WR_Dc_le' : WR Dc ≤ 2 ^ 110 := by
  have hr := rowsD_Dc_le
  unfold WR
  rw [Dc_K, Dc_N]
  generalize rowsD Dc = r at hr
  nlinarith

theorem sigBound_Dc : sigBound (w8Codes (rawEnc Dc)) (WR Dc) ≤ 2 ^ 110 := by
  have h1 := rawEnc_len_Dc
  have h2 := WR_Dc_le'
  unfold sigBound stateBound
  have : (w8Codes (rawEnc Dc)).nS = (rawEnc Dc).len := rfl
  have : (w8Codes (rawEnc Dc)).nM = 1 := rfl
  have : (w8Codes (rawEnc Dc)).nA = 128 := rfl
  simp only [*]
  omega

set_option exponentiation.threshold 2000 in
/-- **The bounds of the challenge component at `Dc`**: output within `2^110` bits, at most
`2^450` steps. -/
theorem bounds_chalP_Dc :
    XProg.lenBoundT (chalP Dc) (io2 (R := 245) (sigBound (w8Codes (rawEnc Dc)) (WR Dc))
        (w8Codes (rawEnc Dc)).nM 0) ≤ io2 (R := 245) (2 ^ 110) 0 0 ∧
      XProg.timeBoundT (chalP Dc) (io2 (R := 245) (sigBound (w8Codes (rawEnc Dc)) (WR Dc))
        (w8Codes (rawEnc Dc)).nM 0) ≤ 2 ^ 450 := by
  have hNK : Dc.N * Dc.K = 2 ^ 40 := by rw [Dc_N, Dc_K]; norm_num
  have hK : Dc.K ≤ 2 ^ 40 := by rw [Dc_K]; norm_num
  have hN : Dc.N ≤ 2 ^ 40 := by rw [Dc_N]; norm_num
  obtain ⟨hl, ht⟩ := bounds_chalP Dc (Mo := 2 ^ 40) (Bc := 2 ^ 56) (Mb := 2 ^ 110) hNK.le hK hN
    (by norm_num) (by norm_num) (by norm_num) sigBound_Dc (by show 1 ≤ _; norm_num)
    (tm_le_Bf Dc (by rw [Dc_N]; norm_num) (by norm_num) ctr_Dc tmBase_Dc_le)
    (by rw [hNK]; norm_num)
  refine ⟨hl, ht.trans ?_⟩
  rw [Dc_b]
  unfold IB
  norm_num

/-! ### The state count -/

theorem size_clr (t : Fin 247) : (Prog.clr t).size = 36 := rfl

theorem size_clrL : ∀ l : List (Fin 247), (RedIO.clrL l).size = 36 * l.length + 36
  | [] => rfl
  | t :: l => by
    show (Prog.clr t).size + (RedIO.clrL l).size = _
    rw [size_clr, size_clrL l, List.length_cons]; ring

theorem size_tmplsP (c : Fin 247) (m : ℕ) : ∀ l : List (Fin 247 × ℕ), (∀ p ∈ l, p.2 < 2 ^ m) →
    (tmplsP c l).size ≤ l.length * (195 * m + 36) + 36
  | [], _ => by show (Prog.prim (.copy c c)).size ≤ _; simp [Prog.size, Prim.pad]
  | p :: l, h => by
    show (XProg.natP p.1 c p.2).size + (tmplsP c l).size ≤ _
    have h1 := XProg.size_natP_le p.1 c p.2 m (h p List.mem_cons_self)
    have h2 := size_tmplsP c m l fun q hq => h q (List.mem_cons_of_mem _ hq)
    rw [List.length_cons]
    nlinarith

theorem length_tList (D : Dims) : (RedIO.tList D.N D.K ra rb (tm D)).length = 201 := by
  simp only [RedIO.tList, List.length_cons, List.length_map]
  rfl

set_option maxRecDepth 100000 in
theorem length_postTapes : RedIO.postTapes.length = 246 := by
  rw [RedIO.postTapes]; rfl

set_option maxRecDepth 100000 in
/-- **The state count of the challenge component**, for template lengths below `2^m`. -/
theorem size_chalP (D : Dims) (m : ℕ) (hK : D.K < 2 ^ m) (hN : D.N < 2 ^ m)
    (hNK : D.N * D.K < 2 ^ m) (htm : ∀ r, tm D r < 2 ^ m) :
    (chalP D).size ≤ 201 * (195 * m + 36) + 20000 + 15000 * (1205 + 16 * D.b) := by
  have h1 : (RedIO.inP ra rb).size = 144 := rfl
  have h2 : (RedIO.onesP ⨾ Prog.clr RedIO.cT).size ≤ 1000 := by decide
  have h3 : (RedIO.postP xOut).size = 36 + (36 * RedIO.postTapes.length + 36) := by
    show (Prog.cp _ _).size + (RedIO.clrL _).size = _
    rw [size_clrL]; rfl
  have h4 : RedIO.postTapes.length = 246 := length_postTapes
  have h5 := size_tmplsP RedIO.cT m (RedIO.tList D.N D.K ra rb (tm D)) (by
    intro p hp
    rcases RedIO.mem_tList.mp hp with rfl | rfl | rfl | ⟨r, -, -, rfl⟩
    · exact hK
    · exact hN
    · exact hNK
    · exact htm r)
  rw [length_tList] at h5
  have h6 : (compile (chalC D)).size ≤ 15000 * (1205 + 16 * D.b) := by
    rw [size_compile, ← vmCount_chalC]; exact vmSize_le _
  show (RedIO.inP ra rb).size + ((tmplsP RedIO.cT (RedIO.tList D.N D.K ra rb (tm D))).size +
    (RedIO.onesP ⨾ Prog.clr RedIO.cT).size) + ((Prog.prim (.cons (tWd r1) true)).size +
    ((compile (chalC D)).size + (RedIO.postP xOut).size)) ≤ _
  have h7 : (Prog.prim (.cons (tWd r1) true) : SigabaNeo.Tape.Prog 247).size = 60 := rfl
  rw [h1, h3, h4, h7]
  omega

set_option exponentiation.threshold 2000 in
/-- **The state count at `Dc`.** -/
theorem size_chalP_Dc : (chalP Dc).size ≤ 2 ^ 200 := by
  have hb := tmBase_Dc_le
  have hle := size_chalP Dc 111 (by rw [Dc_K]; norm_num) (by rw [Dc_N]; norm_num)
    (by rw [Dc_K, Dc_N]; norm_num) (fun r => lt_of_le_of_lt
      (tm_le_Bf Dc (Mo := 2 ^ 40) (Bc := 2 ^ 56) (Mb := 2 ^ 110) (by rw [Dc_N]; norm_num)
        (by norm_num) ctr_Dc tmBase_Dc_le r |>.trans (Bf_le (by norm_num) (by norm_num) r))
      (by norm_num))
  rw [Dc_b] at hle
  exact hle.trans (by norm_num)

/-! ### Summary -/

/-- **The challenge component at `Dc`**: well formed, the law of the reduction's challenger
`spS` (the `law_chal` field of `Generic.Comps`, any `Ok`), the output within `2^110` bits at the
input bounds of `CompBoundsP.len_chal`, at most `2^450` steps there, at most `2^200` states. -/
theorem chalP_Dc_spec (kb : KeyBoxes Dc) (L : ℕ) (impl : Impl sig) (χfl : PMF (Rg Dc))
    (i₀ : CInst Dc) :
    (chalP Dc).WF ∧
      (∀ σ μ, XProg.law (chalP Dc)
        (io2 (R := 245) ((w8Codes (rawEnc Dc)).sig.enc σ) ((univ w8).encMsg μ) []) =
          ((spS Dc kb L (rawF Dc) (rawSetup Dc χfl) impl χfl i₀).chal σ μ).map
            fun ct => io2 (R := 245) ct [] []) ∧
      XProg.lenBoundT (chalP Dc) (io2 (R := 245) (sigBound (w8Codes (rawEnc Dc)) (WR Dc))
        (w8Codes (rawEnc Dc)).nM 0) ≤ io2 (R := 245) (2 ^ 110) 0 0 ∧
      XProg.timeBoundT (chalP Dc) (io2 (R := 245) (sigBound (w8Codes (rawEnc Dc)) (WR Dc))
        (w8Codes (rawEnc Dc)).nM 0) ≤ 2 ^ 450 ∧
      (chalP Dc).size ≤ 2 ^ 200 :=
  ⟨wf_chalP, fun σ μ => law_chal_spS Dc_hyps.1 Dc_hyps.2.1 Dc_hyps.2.2 kb L impl χfl i₀ σ μ,
    bounds_chalP_Dc.1, bounds_chalP_Dc.2, size_chalP_Dc⟩

end AdvancedEncryption.ExpLUT.Prog.RedChal
