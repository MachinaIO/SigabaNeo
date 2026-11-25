import PE.Impl.ExpLUT.Prog.RedKeyTIn
import PE.Impl.ExpLUT.Prog.RedKeyMTail

/-!
# Module 9: tight per-instruction certificates (the back end at a `2^150` tape cap)

F3's ring-instruction certificate `layout_op` charges `operationBound M N K M`, i.e. the counter
register is bounded by the tape cap `M`. At `M = 2^150` that is `≈ 2^390` per instruction, too
much for the `≈ 2^64 … 2^102` instructions of the back end. Here the counter is charged with its
actual layout bound (`rktOp`, `rktOpU`: `operationBound M N K C` for `b c ≤ C`), and register
moves with their exact cost `(2 M + 3) (20 + 10 N K)` (`rktMvR`). The kernels on the hot paths are
re-proved with these (all generic in `M N K`):

* `rktIpBody`, `rktIpC`, `rktSignedDotC` (inner products);
* `rktAutQBody`, `rktAutQC`, `rktAutGatheredC`, `rktGatherAutC` (queue automorphisms).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

/-! ### Instructions -/

/-- A ring instruction, charging the counter register `c` with its layout bound. -/
theorem rktOp (M N K C : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (o : Op) (d s c : Fin 64) (hd : N * K ≤ b d) (hc : b c ≤ C) :
    Cert (MVM.compile (.op o d s c)) (layout M N K b) (layout M N K b)
      (operationBound M N K C) := by
  obtain ⟨hp, hr⟩ := compile_op_scratch_ready M N K o d s c _ h
  apply hp.mono le_rfl
  · apply le_layout M N K b _ hr.top hr.templateK hr.templateN hr.zeros.le hr.ones
    intro r
    by_cases he : r = d
    · subst r; rw [operationResult_destination]; exact hd
    · rw [operationResult_other _ _ _ _ _ _ _ he, cleanWork_register, layout_register]
  · exact operationBound_mono le_rfl le_rfl le_rfl (by simpa using hc)

/-- A ring instruction with the destination reset to one ring word. -/
theorem rktOpU (M N K C : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (o : Op) (d s c : Fin 64) (hc : b c ≤ C) :
    Cert (MVM.compile (.op o d s c)) (layout M N K b)
      (layout M N K (Function.update b d (N * K))) (operationBound M N K C) := by
  obtain ⟨hp, hr⟩ := compile_op_scratch_ready M N K o d s c _ h
  apply hp.mono le_rfl
  · apply le_layout M N K _ _ hr.top hr.templateK hr.templateN hr.zeros.le hr.ones
    intro r
    by_cases he : r = d
    · subst r; simp [operationResult_destination]
    · rw [operationResult_other _ _ _ _ _ _ _ he, cleanWork_register, layout_register,
        Function.update_of_ne he]
  · exact operationBound_mono le_rfl le_rfl le_rfl (by simpa using hc)

/-- The exact cost of a register move. -/
def mvT (M N K : ℕ) : ℕ := (2 * M + 3) * (20 + 10 * (N * K))

theorem rktMvR (M N K : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (d s : Fin 64) (hd : d ≠ s) :
    Cert (MVM.compile (.mvR d s)) (layout M N K b) (layout M N K b) (mvT M N K) := by
  have hc := compile_mvR_scratch d s hd (layout M N K b) M h.top
  have h37 : layout M N K b 37 = N * K := by simp [layout]
  rw [h37] at hc
  exact hc

/-! ### Inner products -/

/-- The tight cost of one inner-product step. -/
def ipBT (M N K : ℕ) : ℕ := 2 * (2 * M + 5) + 2 * mvT M N K + 2 * operationBound M N K (N * K)

theorem rktIpBody (M N K : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hc : QueueArithmeticCaps N K b) (hz : b rZ ≤ N * K) :
    Cert (MVM.compile ipBody) (layout M N K b) (layout M N K b) (ipBT M N K) := by
  let b1 := Function.update b rQx (b rZ)
  let b2 := Function.update b1 rQy (b rZ)
  let b3 := Function.update b2 rQx (N * K)
  have h1 : RingInputs M N K (layout M N K b1) := h.update_layout _ _ (by simpa using h.top (tR rZ))
  have h2 : RingInputs M N K (layout M N K b2) := h1.update_layout _ _ (by simpa using h.top (tR rZ))
  have h3 : RingInputs M N K (layout M N K b3) := h2.update_layout _ _ h.ring
  have p0 := layout_copy_update M N K b h.top rQx rZ
  have p1 := rktMvR M N K b1 h1 rQx rQa (by decide)
  have p2 := layout_copy_update M N K b1 h1.top rQy rZ
  have e1 : b1 rZ = b rZ := by simp [b1]
  rw [e1] at p2
  have p3 := rktMvR M N K b2 h2 rQy rQb (by decide)
  have p4 := rktOpU M N K (N * K) b2 h2 .mul rQx rQx rQy (by simpa [b2] using hz)
  have p5 := rktOpU M N K (N * K) b3 h3 .add rIa rIa rQx (by simp [b3])
  rw [ipBody]
  apply (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq p5))))).mono le_rfl _
    (by unfold ipBT; omega)
  apply layout_mono
  intro r
  by_cases ha : r = rIa
  · subst r; simpa using hc.acc
  by_cases hx : r = rQx
  · subst r; simpa [b3, b2, b1, Function.update_of_ne ha] using hc.x
  by_cases hy : r = rQy
  · subst r; simpa [b3, b2, b1, Function.update_of_ne ha] using hc.zeroY
  simp [b3, b2, b1, Function.update_of_ne ha, Function.update_of_ne hx, Function.update_of_ne hy]

def ipT (M N K R : ℕ) : ℕ := R * (2 * M + ipBT M N K + 4) + 2

theorem rktIpC (M N K R : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hc : QueueArithmeticCaps N K b) (hz : b rZ ≤ N * K) (hr : b rQc ≤ R) :
    Cert (MVM.compile ipC) (layout M N K b) (layout M N K b) (ipT M N K R) :=
  rep_fixed rQc ipBody (layout M N K b) M R (ipBT M N K) h.top (by simpa using hr)
    (rktIpBody M N K b h hc hz)

def sdT (M N K R : ℕ) : ℕ := 6 * (2 * M + 5) + 2 * ipT M N K R + operationBound M N K (N * K)

/-- Both signed dot products and the final subtraction (tight). The accumulator is reset to the
zero word first, so only `rZ = N K` is needed of it. -/
theorem rktSignedDotC (M N K R : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hc : QueueArithmeticCaps N K b) (hz0 : b rZ = N * K)
    (hr : b rQc ≤ R) (hs : N * K ≤ b 13)
    (ha : b 10 ≤ b rQa) (hb : b 11 ≤ b rQb) (hn : b 12 ≤ b rQc) :
    Cert (MVM.compile signedDotC) (layout M N K b)
      (layout M N K (Function.update b rIa (N * K))) (sdT M N K R) := by
  let b1 := Function.update b rIa (N * K)
  have h1 : RingInputs M N K (layout M N K b1) := h.update_layout _ _ h.ring
  have k (r : Fin 64) (hr : r ≠ rIa) : b1 r = b r := Function.update_of_ne hr _ _
  have k1 : b1 rIa = N * K := Function.update_self _ _ _
  have hc1 : QueueArithmeticCaps N K b1 :=
    ⟨by rw [k _ (by decide)]; exact hc.x, by rw [k _ (by decide)]; exact hc.y, k1.ge,
      by rw [k _ (by decide), k _ (by decide)]; exact hc.zeroX,
      by rw [k _ (by decide), k _ (by decide)]; exact hc.zeroY⟩
  have p0 := layout_copy_update M N K b h.top rIa rZ
  rw [hz0] at p0
  have pi := rktIpC M N K R b1 h1 hc1 (by rw [k _ (by decide)]; exact hz0.le)
    (by rw [k _ (by decide)]; exact hr)
  have p2 := layout_copy M N K b1 h1.top 13 rIa (by rw [k1, k _ (by decide)]; exact hs)
  have p3 := layout_copy M N K b1 h1.top rQa 10 (by rw [k _ (by decide), k _ (by decide)]; exact ha)
  have p4 := layout_copy M N K b1 h1.top rQb 11 (by rw [k _ (by decide), k _ (by decide)]; exact hb)
  have p5 := layout_copy M N K b1 h1.top rQc 12 (by rw [k _ (by decide), k _ (by decide)]; exact hn)
  have p6 := layout_copy M N K b1 h1.top rIa rZ (by rw [k1, k _ (by decide)]; exact hz0.le)
  have p8 := rktOpU M N K (N * K) b1 h1 .sub rIa 13 rIa k1.le
  have e8 : Function.update b1 rIa (N * K) = b1 := by simp [b1]
  rw [e8] at p8
  rw [signedDotC]
  exact (p0.seq (pi.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (pi.seq p8)))))))).mono
    le_rfl le_rfl (by unfold sdT; omega)

/-! ### Queue automorphisms -/

/-- The tight cost of one automorphism step (`k` the exponent bound). -/
def autBT (M N K k : ℕ) : ℕ :=
  (2 * M + 5) + mvT M N K + operationBound M N K k + appendAllowance M

theorem rktAutQBody (M N K k : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hz : b rZ ≤ b rQx) (hy : N * K ≤ b rQy) (hk : b rQk ≤ k) (hs : b rQa + N * K ≤ M) :
    Cert (MVM.compile autQBody) (layout M N K b)
      (layout M N K (Function.update b rQa (b rQa + N * K))) (autBT M N K k) := by
  have p0 := layout_copy M N K b h.top rQx rZ hz
  have p1 := rktMvR M N K b h rQx rQa (by decide)
  have p2 := rktOpU M N K k b h .aut rQy rQx rQk hk
  have hi := h.update_layout rQy (N * K) h.ring
  have p3 := layout_append_uniform M N K (Function.update b rQy (N * K)) hi.top
    rQa rQy (by simpa using hs)
  rw [autQBody]
  apply (p0.seq (p1.seq (p2.seq p3))).mono le_rfl _ (by unfold autBT; omega)
  apply layout_mono
  intro r
  by_cases ha : r = rQa
  · subst r; simp
  · by_cases hy' : r = rQy
    · subst r; simpa using hy
    · simp [Function.update_of_ne ha, Function.update_of_ne hy']

def autQT (M N K k R : ℕ) : ℕ := R * (2 * M + autBT M N K k + 4) + 2

theorem rktAutQC (M N K k R : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hz : b rZ ≤ b rQx) (hy : N * K ≤ b rQy) (hk : b rQk ≤ k)
    (hr : b rQc ≤ R) (hs : b rQa + R * (N * K) ≤ M) :
    Cert (MVM.compile autQC) (layout M N K b)
      (layout M N K (Function.update b rQa (b rQa + R * (N * K)))) (autQT M N K k R) := by
  let γ := fun j ↦ layout M N K (Function.update b rQa (b rQa + j * (N * K)))
  have hi (j : ℕ) (hj : j ≤ R) : RingInputs M N K (γ j) :=
    h.update_layout rQa _ (by
      have := Nat.mul_le_mul_right (N * K) hj
      omega)
  have hp : Cert (MVM.compile (.rep rQc autQBody)) (γ 0) (γ R)
      (R * (2 * M + autBT M N K k + 4) + 2) := by
    apply rep_family rQc autQBody γ R (autBT M N K k) _
      (by simp [γ]) (by simpa [γ] using hr)
    · intro j hj
      have hj' : j + 1 ≤ R := by omega
      have hsize : b rQa + (j + 1) * (N * K) ≤ M := by
        have := Nat.mul_le_mul_right (N * K) hj'; omega
      have hb := rktAutQBody M N K k (Function.update b rQa (b rQa + j * (N * K)))
        (hi j (by omega)) (by simpa using hz) (by simpa using hy) (by simpa using hk)
        (by simpa only [Function.update_self, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hsize)
      simp only [Function.update_self, cap_reset] at hb
      rw [show b rQa + j * (N * K) + N * K = b rQa + (j + 1) * (N * K) by ring] at hb
      exact hb.mono (tailB_le (tR rQc) _) le_rfl le_rfl
    · intro j hj; exact supB_le_of (hi j (by omega)).top
    · intro j hj
      apply layout_mono
      intro r
      by_cases he : r = rQa
      · subst r; simp only [Function.update_self]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right (N * K) hj) _
      · simp [Function.update_of_ne he]
  simpa [γ, autQC, autQT] using hp

def autGT (M N K n k : ℕ) : ℕ := (32 * n + 32 * k + 10) * (2 * M + 5) + autQT M N K k n

theorem rktAutGatheredC (M N K n k : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ b rQx) (hy : N * K ≤ b rQy)
    (hn : n ≤ M) (hk : k ≤ M) (hs : b 4 + n * (N * K) ≤ M) :
    Cert (MVM.compile (autGatheredC n k)) (layout M N K b)
      (layout M N K (autGatheredResult N K n k b)) (autGT M N K n k) := by
  let c := Function.update b rQa (b 4)
  let d := Function.update c rQc n
  let e := Function.update d rQk k
  let f := Function.update e rQa (b 4 + n * (N * K))
  have hc := h.update_layout rQa _ (by simpa using h.top (tR 4))
  have hd := hc.update_layout rQc n hn
  have he := hd.update_layout rQk k hk
  have hf := he.update_layout rQa _ hs
  have p0 := layout_copy_update M N K b h.top rQa 4
  have p1 := layout_nat_update M N K c hc rQc rB1 (by decide) n (by simpa [c] using hb) hn
  have p2 := layout_nat_update M N K d hd rQk rB1 (by decide) k (by simpa [d, c] using hb) hk
  have p3 := rktAutQC M N K k n e he (by simpa [e, d, c] using hz)
    (by simpa [e, d, c] using hy) (by simp [e]) (by simp [e, d]) (by simpa [e, d, c] using hs)
  have p4 := layout_copy_update M N K f hf.top 4 rQa
  have heq : Function.update f 4 (f rQa) = autGatheredResult N K n k b := by
    funext r
    by_cases h0 : r = 4 <;> by_cases h1 : r = rQa <;>
      by_cases h2 : r = rQc <;> by_cases h3 : r = rQk <;>
        simp_all [f, e, d, c, autGatheredResult]
  rw [heq] at p4
  have ha : e rQa = b 4 := by simp [e, d, c]
  rw [ha] at p3
  rw [autGatheredC]
  exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl le_rfl
    (by unfold autGT; ring_nf; omega)

theorem rktGatherAutC (M N K I k : ℕ) (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ N * K) (hx : b rZ ≤ b rQx) (hy : N * K ≤ b rQy)
    (hi : I * (N * K) ≤ M) (hj : ∀ j ∈ js, j ≤ I)
    (hn : js.length ≤ M) (hk : k ≤ M) (hs : 2 * (js.length * (N * K)) ≤ M) :
    Cert (MVM.compile (gatherAutC N K k js)) (layout M N K b)
      (layout M N K (gatherAutResult M N K k js b))
      (gatherTime M N K I js.length + autGT M N K js.length k) := by
  let c := Function.update (gatherBase M b) 4 (js.length * (N * K))
  have hc := (gatherBase_inputs M N K b h).update_layout 4 _ (by omega : js.length * (N * K) ≤ M)
  have p0 := compile_gatherC M N K I js b h hb hz hi hj (by omega)
  have p1 := rktAutGatheredC M N K js.length k c hc
    (by simpa [c, gatherBase] using hb) (by simpa [c, gatherBase] using hx)
    (by simpa [c, gatherBase] using hy) hn hk (by simpa [c, two_mul] using hs)
  exact p0.seq p1

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
