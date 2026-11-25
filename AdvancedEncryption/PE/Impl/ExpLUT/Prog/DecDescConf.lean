import PE.Impl.ExpLUT.Prog.DecMachineConf
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMSize
import SigabaNeoStd.Machines.Prog.VecBound
import SigabaNeoStd.Machines.Prog.AppendWCost

/-!
# Description length of the concrete `Dec` machine (package F4)

The state count of `decProgram Dc`: the four framed unframing steps, the length test
(`size_lenEqP`), the `70` templates built by doubling (`size_natP_le`, every length below
`2^128` at `Dc`), the constants and the output, and the compiled code (`size_compile`:
`vmSize decCode = 256728820`, evaluated by the kernel). In total at most `2^28` states, so
**`descLen_decMachine : decMachine.descLen ≤ 2^465`** (the factor `3^256` of the `256` tapes
dominates).
-/

set_option autoImplicit false

namespace AdvancedEncryption.ExpLUT.Prog.DecConf

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM AdvancedEncryption.ExpLUT.Params
open DecM

/-! ### Sizes of the enumerations -/

theorem dmBC_eq (D : Dims) : dmBC D = D.mb + D.K := by
  simp [dmBC, BCol, Wb, enum_sum, enum_fin]

theorem dmJ_eq (D : Dims) : dmJ D = D.b * 2 := by
  simp [dmJ, Jh, length_enum_prod, enum_fin]

theorem dmJC_eq (D : Dims) : dmJC D = D.b * 2 * (2 * D.K) := by
  rw [dmJC, length_enum_prod, length_col]; simp [Jh, length_enum_prod, enum_fin]

theorem dmDig_eq (D : Dims) : dmDig D = 2 * (2 * D.K) * D.K := dlen_dig D.K

theorem dmPos_eq : dmPos = 16 := rfl

theorem dmB_eq (D : Dims) : dmB D = D.b := by simp [dmB, enum_fin]

theorem Dc_K : Dc.K = 2 ^ 16 := Kc_def
theorem Dc_N : Dc.N = 2 ^ 24 := rfl
theorem Dc_mb : Dc.mb = 3 * (2 ^ 24 * 2 ^ 16) + 408 := by
  show mbar = _; rw [mbar_def, Kc_def]

set_option maxRecDepth 10000 in
/-- Every template length is below `2^128` at `Dc`. -/
theorem tmpl_lt : ∀ p ∈ tmplList Dc, p.2 < 2 ^ 128 := by
  have hκ : ∀ t, κD Dc t < 2 ^ 128 := fun t =>
    (Nat.mod_lt _ (by positivity)).trans_le (by rw [Dc_N]; norm_num)
  have hρ : ∀ b, ρD Dc.N b < 2 ^ 128 := fun b =>
    (Nat.sub_le _ _).trans_lt (by rw [Dc_N]; norm_num)
  simp only [tmplList, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨⟨?_, fun t _ => hκ t⟩, fun b _ => hρ b⟩
  simp only [dmBC_eq, dmJ_eq, dmJC_eq, dmlen_col, dmDig_eq, dmPos_eq, dmB_eq, len_fin2, famMLen,
    Dc_K, Dc_N, Dc_mb, Dc_b]
  norm_num

theorem size_tmplsP (c : Fin 256) (m : ℕ) : ∀ l : List (Fin 256 × ℕ), (∀ p ∈ l, p.2 < 2 ^ m) →
    (tmplsP c l).size ≤ l.length * (195 * m + 36) + 36
  | [], _ => by simp [tmplsP, XProg.size, Prog.size, Prim.pad]
  | p :: l, h => by
    have h1 := XProg.size_natP_le p.1 c p.2 m (h p (by simp))
    have h2 := size_tmplsP c m l fun q hq => h q (by simp [hq])
    simp only [tmplsP, XProg.size_seq, List.length_cons]
    nlinarith

theorem length_tmplList (D : Dims) : (tmplList D).length = 70 := by simp [tmplList]

set_option maxRecDepth 100000 in
theorem vmSize_decCode : vmSize decCode = 256728820 := by decide +kernel

theorem log2_predLen : Nat.log2 predLen = 29 := by
  rw [Nat.log2_eq_iff (by simp [predLen])]; norm_num [predLen]

theorem size_decProgram_eq (D : Dims) : (decProgram D).size =
    (4 * Prog.unfrP.size + (Prog.clr (253 : Fin 256)).size) + ((Prog.lenEqP predLen).size +
      (((tmplsP 250 (tmplList D)).size + (DecM.constP.size + ((compile decCode).size +
        DecM.outP.size))) + DecM.invP.size + 1)) := by
  simp only [decProgram, validP, parseX, unfrX, lenX, XProg.size_seq, XProg.size_frame,
    XProg.size_prog, XProg.size_ifBit]
  ring

theorem size_unfrP : Prog.unfrP.size ≤ 10000 := by decide
theorem size_constP : DecM.constP.size ≤ 10000 := by decide
theorem size_outP : DecM.outP.size ≤ 10000 := by decide
theorem size_invP : DecM.invP.size ≤ 10000 := by decide
theorem size_clr253 : (Prog.clr (253 : Fin 256)).size ≤ 10000 := by decide

/-- **The state count of the `Dec` program.** -/
theorem size_decProgram : (decProgram Dc).size + 4 ≤ 2 ^ 28 := by
  have ht := size_tmplsP 250 128 (tmplList Dc) tmpl_lt
  rw [length_tmplList] at ht
  have hl := Prog.size_lenEqP predLen
  rw [log2_predLen] at hl
  have hc : (compile decCode).size = 256728820 := by rw [size_compile, vmSize_decCode]
  rw [size_decProgram_eq, hc]
  have := size_unfrP; have := size_constP; have := size_outP; have := size_invP
  have := size_clr253
  omega

theorem descLen_decMP_eq (D : Dims) (L : ℕ) : (decMP D L).descLen =
    6 * ((decProgram D).size + 4) * 3 ^ 256 * 3 ^ 0 *
      Machine.entryBits 256 ((decProgram D).size + 4) 0 := by
  rw [Machine.descLen, decMP, XProg.states_toMachineT, XProg.card_state]
  rfl

theorem descLen_arith {k S B : ℕ} (h : S ≤ B) :
    6 * S * 3 ^ k * 3 ^ 0 * Machine.entryBits k S 0 ≤ 6 * B * 3 ^ k * (4 + 4 * k + B) := by
  have hs : Nat.size S ≤ S := Nat.size_le.mpr Nat.lt_two_pow_self
  unfold Machine.entryBits
  simp only [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero, Nat.size_zero]
  gcongr
  omega

set_option exponentiation.threshold 2000 in
/-- **The description length of the concrete `Dec` machine.** -/
theorem descLen_decMachine : decMachine.descLen ≤ 2 ^ 465 := by
  rw [decMachine, descLen_decMP_eq]
  exact (descLen_arith size_decProgram).trans (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.DecConf
