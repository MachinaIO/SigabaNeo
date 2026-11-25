import PE.Impl.ExpLUT.Prog.KeyTimeBoxFamily
/-! Runtime of actual acceptance, including rejection, and the full deterministic try. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

def boxScratch : List (Fin 64) := [rTx, rFa, rDi, rDc, rTa, rTnb, rTd, rDq, rQb, 19]

def boxBase (M : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) : ℕ :=
  if r ∈ boxScratch then M else b r

theorem boxBase_inside (M : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) (hr : r ∈ boxScratch) :
    boxBase M b r = M := ite_eq_left hr

theorem boxBase_outside (M : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) (hr : r ∉ boxScratch) :
    boxBase M b r = b r := ite_eq_right hr

theorem boxBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (boxBase M b)) := by
  apply layout_inputs
  · intro r; unfold boxBase; split_ifs
    · exact le_rfl
    · simpa using h.top (tR r)
  · exact h.ring
  · exact h.dimension
  · exact h.width

theorem le_boxBase (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) : b ≤ boxBase M b := by
  intro r; unfold boxBase; split_ifs
  · simpa using h.top (tR r)
  · exact le_rfl

theorem boxBase_caps (N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) N K (layout (2 ^ 120) N K b))
    (hs : b rTBk + b rTKB ≤ 2 ^ 120) (hr : b rTKB ≤ 2 ^ 16) :
    BoxCaps N K (boxBase (2 ^ 120) b) := by
  have hi (r : Fin 64) (hr : r ∈ boxScratch) := boxBase_inside (2 ^ 120) b r hr
  have ho (r : Fin 64) (hr : r ∉ boxScratch) := boxBase_outside (2 ^ 120) b r hr
  have hz : b rZ ≤ 2 ^ 120 := by simpa using h.top (tR rZ)
  have hb : b rB1 ≤ 2 ^ 120 := by simpa using h.top (tR rB1)
  have hc : b rTKB ≤ 2 ^ 120 := by simpa using h.top (tR rTKB)
  constructor
  · rw [hi _ (by decide)]; exact h.ring
  · rw [hi _ (by decide)]; exact h.ring
  · rw [hi _ (by decide)]; exact h.ring
  · rw [hi _ (by decide)]; exact h.ring
  · rw [ho _ (by decide), ho _ (by decide), hi _ (by decide)]; exact hs
  · rw [ho _ (by decide), hi _ (by decide)]; exact hc
  · rw [ho _ (by decide)]; exact hr
  · rw [ho _ (by decide), hi _ (by decide)]; exact hz
  · rw [ho _ (by decide), hi _ (by decide)]; exact hz
  · rw [hi _ (by decide)]; norm_num
  · rw [ho _ (by decide), hi _ (by decide)]; exact hb

noncomputable def acceptResult (B : ℕ) (b : Fin 64 → ℕ) :=
  boxBase (2 ^ 120) (acceptInitResult Dc B b)

theorem acceptResult_inputs (B : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b)) (hB : B ≤ Dc.K) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (acceptResult B b)) :=
  boxBase_inputs _ _ _ _ (acceptInitResult_inputs Dc _ B b h (by norm_num) hB
    (correction_counts_Dc.2.2.trans (by norm_num)))

theorem acceptResult_fields (B : ℕ) (b : Fin 64 → ℕ) :
    acceptResult B b rB1 = b rB1 ∧ acceptResult B b rZ = b rZ ∧
    acceptResult B b rQc = (Enum.list (α := PIdxD Dc)).length ∧
    acceptResult B b 19 = 2 ^ 120 := by
  have hf := acceptInitResult_fields Dc B b
  exact ⟨(boxBase_outside _ _ rB1 (by decide)).trans hf.2.2.2.2.2.1,
    (boxBase_outside _ _ rZ (by decide)).trans hf.2.2.2.2.2.2.1,
    (boxBase_outside _ _ rQc (by decide)).trans hf.2.2.2.2.1,
    boxBase_inside _ _ 19 (by decide)⟩

theorem compile_rejectWord (n : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hk : b 19 = 2 ^ 120) (hn : n ≤ 2 ^ 120) :
    Cert (MVM.compile (natC 19 rB1 n)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 250) := by
  apply (layout_nat_update (2 ^ 120) Dc.N Dc.K b h 19 rB1 (by decide) n hb hn).mono
    le_rfl (layout_mono _ _ _ (cap_update_le b 19 n (hn.trans hk.ge)))
  calc
    _ ≤ (32 * 2 ^ 120 + 4) * (2 * 2 ^ 120 + 5) := by gcongr
    _ ≤ 2 ^ 250 := by norm_num

theorem compile_acceptC_of_parts (D : Dims) (B r : ℕ) (a c : Fin 105 → ℕ)
    (T0 T1 T2 T3 : ℕ)
    (p0 : Cert (MVM.compile (acceptInitC D B r)) a c T0)
    (p1 : Cert (MVM.compile boxFamilyC) c c T1)
    (pn : Cert (MVM.compile Code.nop) c c T2)
    (pr : Cert (MVM.compile (natC 19 rB1 (codecSize (keyEnc D)))) c c T3) :
    Cert (MVM.compile (acceptC D B r)) a c (T0 + (T1 + (max T2 T3 + 1))) :=
  p0.seq (p1.seq (Cert.ifBit (tR rTx) pn pr))

theorem compile_acceptC_Dc (B r : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hB : B ≤ Dc.K) :
    Cert (MVM.compile (acceptC Dc B r)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (acceptResult B b)) (2 ^ 434) := by
  let d := acceptInitResult Dc B b
  let c := acceptResult B b
  have hd := acceptInitResult_inputs Dc (2 ^ 120) B b h (by norm_num) hB
    (correction_counts_Dc.2.2.trans (by norm_num))
  have hc := acceptResult_inputs B b h hB
  have hf := acceptInitResult_fields Dc B b
  have cf := acceptResult_fields B b
  have hs : d rTBk + d rTKB ≤ 2 ^ 120 := by
    calc
      _ = B + (Dc.K - B) := congrArg₂ (· + ·) hf.2.1 hf.2.2.1
      _ = Dc.K := Nat.add_sub_of_le hB
      _ ≤ 2 ^ 120 := h.width
  have hr : d rTKB ≤ 2 ^ 16 := by
    calc
      _ = Dc.K - B := hf.2.2.1
      _ ≤ Dc.K := Nat.sub_le _ _
      _ ≤ 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have caps := boxBase_caps Dc.N Dc.K d hd hs hr
  have p0 := (compile_acceptInitC_Dc B r b h hb hB).mono le_rfl
    (layout_mono _ _ _ (le_boxBase _ _ _ d hd)) le_rfl
  have p1 := (compile_boxFamilyC_Dc c hc (cf.1.trans hb) caps
    (cf.2.2.1.le.trans correction_counts_Dc.2.2)).mono le_rfl
      (layout_mono _ _ _ (cap_update_le c rTx 1 caps.flag)) le_rfl
  have pn := (compile_nop _ (2 ^ 120) hc.top).mono le_rfl le_rfl
    (show 2 * (2 ^ 120 + 1) + 3 ≤ 2 * 2 ^ 120 + 5 by omega)
  have pk := keyCodec_bounds_Dc.2.2
  have pr := compile_rejectWord (codecSize (keyEnc Dc)) c hc (cf.1.trans hb) cf.2.2.2 pk
  exact (compile_acceptC_of_parts Dc B r _ _ _ _ _ _ p0 p1 pn pr).mono
    le_rfl le_rfl (by norm_num)

noncomputable def tryKeyResult (B : ℕ) (b : Fin 64 → ℕ) := acceptResult B (proposalKeyResult b)

theorem compile_tryKeyC_Dc (B r : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) (hB : B ≤ Dc.K) :
    Cert (MVM.compile (tryKeyC Dc B r)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (tryKeyResult B b)) (2 ^ 500) := by
  have hf := proposalKeyResult_fields b
  have p0 := compile_proposalKeyC_Dc b h hb hz
  have p1 := compile_acceptC_Dc B r (proposalKeyResult b) (proposalKeyResult_inputs b h)
    (hf.2.2.1.trans hb) hB
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
