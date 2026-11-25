import PE.Impl.ExpLUT.Prog.RedKeyTK

/-!
# Module 9: the acceptance test at a large tape cap (tight)

F3's `compile_acceptC_Dc` charges every digit/addition of the box test with the tape cap as
counter (`2^434` at `M = 2^120`, `≈ 2^474` at `2^150`). Here the digit position (`rDi ≤ K`) and the
ring words (`N K`) are the counters (`rktTstBody` … `rktBoxFamilyC`), and the key register `19`
is tracked: **`rktAcceptC`** ends with `19 ≤ max (b 19) (codecSize keyEnc)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

/-- One digit pair of the box test (tight): counters `rDi ≤ Ci` and one ring word. -/
def tstBT (M N K Ci : ℕ) : ℕ :=
  2 * operationBound M N K Ci + 2 * operationBound M N K (N * K) + 10 * (2 * M + 5)

theorem rktTstBody (M N K Ci : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hb : b rB1 = 1) (hd : N * K ≤ b rTd) (hf : N * K ≤ b rFa) (hi : b rDi ≤ Ci)
    (hs : b rDi + 1 ≤ M) :
    Cert (MVM.compile tstBody) (layout M N K b)
      (layout M N K (Function.update b rDi (b rDi + 1))) (tstBT M N K Ci) := by
  let b1 := Function.update b rTd (N * K)
  have h1 : RingInputs M N K (layout M N K b1) := h.update_layout _ _ h.ring
  have p0 := rktOpU M N K Ci b h .dig rTd rTa rDi hi
  have p1 := rktOp M N K (N * K) b1 h1 .add rFa rFa rTd (by simpa [b1] using hf) (by simp [b1])
  have p2 := rktOpU M N K Ci b1 h1 .dig rTd rTnb rDi (by simpa [b1] using hi)
  have e2 : Function.update b1 rTd (N * K) = b1 := by simp [b1]
  rw [e2] at p2
  have p3 := layout_append M N K b1 h1.top rDi rB1 (by simpa [b1, hb] using hs)
  have e3 : b1 rB1 = 1 := by simpa [b1] using hb
  have e4 : b1 rDi = b rDi := by simp [b1]
  rw [e3, e4] at p3
  rw [tstBody]
  apply (p0.seq (p1.seq (p2.seq (p1.seq p3)))).mono le_rfl _ (by unfold tstBT; omega)
  apply layout_mono
  intro r
  by_cases he : r = rDi
  · subst r; simp
  · by_cases ht : r = rTd
    · subst r; simpa [b1, Function.update_of_ne he] using hd
    · simp [b1, Function.update_of_ne he, Function.update_of_ne ht]

def tstLT (M N K Ci R : ℕ) : ℕ := R * (2 * M + tstBT M N K Ci + 4) + 2

theorem rktTstLoop (M N K Ci R : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hb : b rB1 = 1) (hd : N * K ≤ b rTd) (hf : N * K ≤ b rFa)
    (hr : b rDc ≤ R) (hi : b rDi + R ≤ Ci) (hs : b rDi + R ≤ M) :
    Cert (MVM.compile (.rep rDc tstBody)) (layout M N K b)
      (layout M N K (Function.update b rDi (b rDi + R))) (tstLT M N K Ci R) := by
  let γ := fun j ↦ layout M N K (Function.update b rDi (b rDi + j))
  have hγ (j : ℕ) (hj : j ≤ R) : RingInputs M N K (γ j) :=
    h.update_layout rDi _ (by omega)
  apply rep_family rDc tstBody γ R (tstBT M N K Ci) _
    (by simp [γ]) (by simpa using hr)
  · intro j hj
    have hp := rktTstBody M N K Ci (Function.update b rDi (b rDi + j))
      (hγ j (by omega)) (by simpa using hb) (by simpa using hd) (by simpa using hf)
      (by simp only [Function.update_self]; omega) (by simp only [Function.update_self]; omega)
    simp only [Function.update_self, cap_reset] at hp
    have he : b rDi + j + 1 = b rDi + (j + 1) := by omega
    rw [he] at hp
    exact hp.mono (tailB_le (tR rDc) _) le_rfl le_rfl
  · intro j hj; exact supB_le_of (hγ j (by omega)).top
  · intro j hj
    apply layout_mono
    intro r
    by_cases he : r = rDi
    · subst r; simp only [Function.update_self]; omega
    · simp [Function.update_of_ne he]

def tstT (M N K Ci R : ℕ) : ℕ :=
  2 * operationBound M N K (N * K) + 2 * (2 * M + 5) + tstLT M N K Ci R

/-- The digit test of `rTx` (tight); `rRR` and `rTx` are single ring words. -/
theorem rktTstC (M N K Ci : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hb : b rB1 = 1) (hd : N * K ≤ b rTd) (hf : N * K ≤ b rFa)
    (ha : N * K ≤ b rTa) (hn : N * K ≤ b rTnb) (hR : b rRR ≤ N * K) (hx : b rTx ≤ N * K)
    (hs : b rTBk + b rTKB ≤ b rDi) (hc : b rTKB ≤ b rDc) (hci : b rTBk + b rTKB ≤ Ci) :
    Cert (MVM.compile tstC) (layout M N K b) (layout M N K b)
      (tstT M N K Ci (b rTKB)) := by
  let c := Function.update b rDi (b rTBk)
  let d := Function.update c rDc (b rTKB)
  have hi := h.update_layout rDi (b rTBk) (by simpa using h.top (tR rTBk))
  have hj := hi.update_layout rDc (b rTKB) (by simpa using h.top (tR rTKB))
  have p0 := rktOp M N K (N * K) b h .add rTa rTx rRR ha hR
  have p1 := rktOp M N K (N * K) b h .sub rTnb rRR rTx hn hx
  have p2 := layout_copy_update M N K b h.top rDi rTBk
  have p3 := layout_copy_update M N K c hi.top rDc rTKB
  have he : c rTKB = b rTKB := by simp [c]
  rw [he] at p3
  have hdi : b rDi ≤ M := by simpa using h.top (tR rDi)
  have hsum : b rTBk + b rTKB ≤ M := hs.trans hdi
  have dk (r : Fin 64) (h1 : r ≠ rDc) (h2 : r ≠ rDi) : d r = b r := by
    simp only [d, c, Function.update_of_ne h1, Function.update_of_ne h2]
  have ddi : d rDi = b rTBk := by simp only [d, c, Function.update_of_ne (by decide : rDi ≠ rDc),
    Function.update_self]
  have p4 := rktTstLoop M N K Ci (b rTKB) d hj
    (by rw [dk _ (by decide) (by decide)]; exact hb) (by rw [dk _ (by decide) (by decide)]; exact hd)
    (by rw [dk _ (by decide) (by decide)]; exact hf)
    (by simp [d]) (by rw [ddi]; exact hci) (by rw [ddi]; exact hsum)
  have ho : Function.update d rDi (d rDi + b rTKB) ≤ b := by
    intro r
    by_cases hdi : r = rDi
    · subst r; simpa [d, c] using hs
    · by_cases hdc : r = rDc
      · subst r; simpa [d, c] using hc
      · simp [Function.update_of_ne hdi, Function.update_of_ne hdc, d, c]
  exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl (layout_mono _ _ _ ho)
    (by unfold tstT; omega)

/-- The box-test envelope: the scratch of the test widened to `M` (the key register `19` is
not part of it, unlike F3's `boxScratch`). -/
def bxScratch : List (Fin 64) := [rTx, rFa, rDi, rDc, rTa, rTnb, rTd, rDq, rQb]

def bxBase (M : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) : ℕ := if r ∈ bxScratch then M else b r

theorem bxBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (bxBase M b)) := by
  apply layout_inputs
  · intro r; unfold bxBase; split_ifs
    · exact le_rfl
    · simpa using h.top (tR r)
  · exact h.ring
  · exact h.dimension
  · exact h.width

theorem le_bxBase (M N K : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b)) :
    b ≤ bxBase M b := by
  intro r; unfold bxBase; split_ifs
  · simpa using h.top (tR r)
  · exact le_rfl

theorem bxBase_in (M : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) (hr : r ∈ bxScratch) :
    bxBase M b r = M := if_pos hr

theorem bxBase_out (M : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) (hr : r ∉ bxScratch) :
    bxBase M b r = b r := if_neg hr

def boxBT (M N K Ci R : ℕ) : ℕ :=
  3 * (2 * M + 5) + mvT M N K + (tstT M N K Ci R + (2 * M + 5)) + (2 * M + 5) + 1

/-- One coordinate of the streaming box test (tight). The envelope `e` has the test scratch at
`M ≥ N K`. -/
theorem rktBoxBodyC (M N K Ci : ℕ) (e : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K e))
    (hb : e rB1 = 1) (hz : e rZ ≤ N * K) (hNK : N * K ≤ M) (hm : 1 ≤ M)
    (hd : e rTd = M) (hf : e rFa = M) (ha : e rTa = M) (hn : e rTnb = M) (hx : e rTx = M)
    (hdi : e rDi = M) (hdc : e rDc = M) (hq : e rDq = M) (hR : e rRR ≤ N * K)
    (hBK : e rTBk + e rTKB ≤ M) (hci : e rTBk + e rTKB ≤ Ci) :
    Cert (MVM.compile boxBodyC) (layout M N K e) (layout M N K e)
      (boxBT M N K Ci (e rTKB)) := by
  let e1 := Function.update e rTx (e rZ)
  have h1 : RingInputs M N K (layout M N K e1) := h.update_layout _ _ (by simpa using h.top (tR rZ))
  have k (r : Fin 64) (hr : r ≠ rTx) : e1 r = e r := Function.update_of_ne hr _ _
  have k1 : e1 rTx = e rZ := Function.update_self _ _ _
  have p0 := layout_copy_update M N K e h.top rTx rZ
  have p1 := rktMvR M N K e1 h1 rTx rQa (by decide)
  have p2 := layout_copy M N K e1 h1.top rFa rZ
    (by rw [k _ (by decide), k _ (by decide), hf]; exact hz.trans hNK)
  have p3 := (rktTstC M N K Ci e1 h1 (by rw [k _ (by decide)]; exact hb)
    (by rw [k _ (by decide), hd]; exact hNK)
    (by rw [k _ (by decide), hf]; exact hNK) (by rw [k _ (by decide), ha]; exact hNK)
    (by rw [k _ (by decide), hn]; exact hNK)
    (by rw [k _ (by decide)]; exact hR) (by rw [k1]; exact hz)
    (by rw [k _ (by decide), k _ (by decide), k _ (by decide), hdi]; exact hBK)
    (by rw [k _ (by decide), k _ (by decide), hdc]; exact hBK.trans' (Nat.le_add_left _ _))
    (by rw [k _ (by decide), k _ (by decide)]; exact hci)).seq
    (layout_eqb_update M N K e1 h1 rTx rFa rZ (by decide))
  have e1k : e1 rTKB = e rTKB := by simp [e1]
  rw [e1k] at p3
  have ee : Function.update e1 rTx 1 = Function.update e rTx 1 := by simp [e1]
  rw [ee] at p3
  have hu : RingInputs M N K (layout M N K (Function.update e rTx 1)) :=
    h.update_layout _ _ (by omega)
  have pn := (compile_nop _ M hu.top).mono le_rfl le_rfl
    (show 2 * (M + 1) + 3 ≤ 2 * M + 5 by omega)
  have pc := layout_copy M N K _ hu.top rDq rB1
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hq, hb]; omega)
  have p4 := Cert.ifBit (tR rTx) pn pc
  have hle : Function.update e rTx 1 ≤ e := cap_update_le e rTx 1 (by rw [hx]; omega)
  exact ((p0.seq (p1.seq p2)).seq (p3.seq p4)).mono le_rfl (layout_mono _ _ _ hle)
    (by unfold boxBT; omega)

def boxFT (M N K Ci R L : ℕ) : ℕ :=
  (2 * M + 5) + (L * (2 * M + boxBT M N K Ci R + 4) + 2) + (2 * M + 5) + (2 * M + 5)

/-- The streaming family test and the latch (tight). -/
theorem rktBoxFamilyC (M N K Ci L : ℕ) (e : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K e))
    (hb : e rB1 = 1) (hz : e rZ ≤ N * K) (hNK : N * K ≤ M) (hm : 1 ≤ M)
    (hd : e rTd = M) (hf : e rFa = M) (ha : e rTa = M) (hn : e rTnb = M) (hx : e rTx = M)
    (hdi : e rDi = M) (hdc : e rDc = M) (hq : e rDq = M) (hR : e rRR ≤ N * K)
    (hBK : e rTBk + e rTKB ≤ M) (hci : e rTBk + e rTKB ≤ Ci) (hL : e rQc ≤ L) :
    Cert (MVM.compile boxFamilyC) (layout M N K e)
      (layout M N K (Function.update e rTx 1)) (boxFT M N K Ci (e rTKB) L) := by
  have p0 := (layout_clear_update M N K e h.top rDq).mono le_rfl
    (layout_mono _ _ _ (cap_update_le e rDq 0 (Nat.zero_le _))) le_rfl
  have p1 := rep_fixed rQc boxBodyC (layout M N K e) M L (boxBT M N K Ci (e rTKB)) h.top
    (by simpa using hL) (rktBoxBodyC M N K Ci e h hb hz hNK hm hd hf ha hn hx hdi hdc hq hR hBK hci)
  have p2 := (layout_clear_update M N K e h.top rQb).mono le_rfl
    (layout_mono _ _ _ (cap_update_le e rQb 0 (Nat.zero_le _))) le_rfl
  have p3 := layout_eqb_update M N K e h rTx rDq rQb (by decide)
  rw [boxFamilyC, boxQueueC]
  exact ((p0.seq p1).seq (p2.seq p3)).mono le_rfl le_rfl (by unfold boxFT; omega)

/-- The output envelope of the acceptance step. -/
noncomputable def accOut (D : Dims) (M B : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (bxBase M (acceptInitResult D B b)) rTx 1) 19
    (max (b 19) (codecSize (keyEnc D)))

noncomputable def accT (D : Dims) (M B L : ℕ) : ℕ :=
  acceptInitTime D M B + (boxFT M D.N D.K D.K (D.K - B) L +
    (max (2 * (M + 1) + 3) ((32 * codecSize (keyEnc D) + 4) * (2 * M + 5)) + 1))

/-- **The acceptance step** (tight), generic in the cap `M`. -/
theorem rktAcceptC (D : Dims) (M B r L : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b)) (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K)
    (hm : 1 ≤ M) (hB : B ≤ D.K) (hc : (Enum.list (α := PIdxD D)).length ≤ L) (hLM : L ≤ M)
    (hkey : codecSize (keyEnc D) ≤ M) :
    Cert (MVM.compile (acceptC D B r)) (layout M D.N D.K b)
      (layout M D.N D.K (accOut D M B b)) (accT D M B L) := by
  have hci := acceptInitResult_inputs D M B b h hm hB (hc.trans hLM)
  have hf := acceptInitResult_fields D B b
  set c := acceptInitResult D B b with hcdef
  set e := bxBase M c with hedef
  have he := bxBase_inputs M D.N D.K c hci
  have p0 := (compile_acceptInitC D M B r b h hb hm hB (hc.trans hLM)).mono le_rfl
    (layout_mono _ _ _ (le_bxBase M D.N D.K c hci)) le_rfl
  have out (r : Fin 64) (hr : r ∉ bxScratch) : e r = c r := bxBase_out M c r hr
  have inn (r : Fin 64) (hr : r ∈ bxScratch) : e r = M := bxBase_in M c r hr
  have eB : e rTBk + e rTKB = D.K := by
    rw [out _ (by decide), out _ (by decide), hf.2.1, hf.2.2.1]; omega
  have p1 := rktBoxFamilyC M D.N D.K D.K L e he
    (by rw [out _ (by decide), hf.2.2.2.2.2.1]; exact hb)
    (by rw [out _ (by decide), hf.2.2.2.2.2.2.1]; exact hz) h.ring hm
    (inn _ (by decide)) (inn _ (by decide)) (inn _ (by decide)) (inn _ (by decide))
    (inn _ (by decide)) (inn _ (by decide)) (inn _ (by decide)) (inn _ (by decide))
    (by rw [out _ (by decide), hf.1])
    (by rw [eB]; exact h.width) (by rw [eB])
    (by rw [out _ (by decide), hf.2.2.2.2.1]; exact hc)
  have ekb : e rTKB = D.K - B := by rw [out _ (by decide), hf.2.2.1]
  rw [ekb] at p1
  let f := Function.update e rTx 1
  have hfi : RingInputs M D.N D.K (layout M D.N D.K f) := he.update_layout _ _ hm
  have hle : f ≤ accOut D M B b := by
    intro q
    by_cases hq : q = 19
    · subst hq
      show Function.update e rTx 1 19 ≤ accOut D M B b 19
      rw [accOut, Function.update_self, Function.update_of_ne (by decide), out _ (by decide),
        hf.2.2.2.2.2.2.2]
      exact le_max_left _ _
    · rw [accOut, Function.update_of_ne hq]
  have hle2 : Function.update f 19 (codecSize (keyEnc D)) ≤ accOut D M B b := by
    intro q
    by_cases hq : q = 19
    · subst hq
      rw [accOut, Function.update_self, Function.update_self]
      exact le_max_right _ _
    · rw [accOut, Function.update_of_ne hq, Function.update_of_ne hq]
  have pn := (compile_nop _ M hfi.top).mono le_rfl (layout_mono _ _ _ hle) le_rfl
  have pr := (layout_nat_update M D.N D.K f hfi 19 rB1 (by decide) _
    (by show Function.update e rTx 1 rB1 = 1
        rw [Function.update_of_ne (by decide), out _ (by decide), hf.2.2.2.2.2.1]; exact hb)
    hkey).mono le_rfl (layout_mono _ _ _ hle2) le_rfl
  rw [acceptC]
  exact (p0.seq (p1.seq (Cert.ifBit (tR rTx) pn pr))).mono le_rfl le_rfl
    (by unfold accT; exact le_rfl)

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
