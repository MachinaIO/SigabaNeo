import PE.Impl.ExpLUT.Prog.KeyTimePrefix

/-! Actual coefficient gathering with counter setup and queue automorphisms. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def autGatheredResult (N K n k : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update (Function.update b rQa (b 4 + n * (N * K)))
    rQc n) rQk k) 4 (b 4 + n * (N * K))

def autGatheredTime (M N K n k : ℕ) :=
  (32 * n + 32 * k + 10) * (2 * M + 5) + autQueueTime M N K n

theorem compile_autGatheredC (M N K n k : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ b rQx) (hy : N * K ≤ b rQy)
    (hn : n ≤ M) (hk : k ≤ M) (hs : b 4 + n * (N * K) ≤ M) :
    Cert (MVM.compile (autGatheredC n k)) (layout M N K b)
      (layout M N K (autGatheredResult N K n k b)) (autGatheredTime M N K n k) := by
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
  have p3 := compile_autQC M N K n e he (by simpa [e, d, c] using hz)
    (by simpa [e, d, c] using hy) (by simp [e, d]) (by simpa [e, d, c] using hs)
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
    (by unfold autGatheredTime; ring_nf; omega)

theorem autGatheredResult_inputs (M N K n k : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hn : n ≤ M) (hk : k ≤ M) (hs : b 4 + n * (N * K) ≤ M) :
    RingInputs M N K (layout M N K (autGatheredResult N K n k b)) :=
  (((h.update_layout rQa _ hs).update_layout rQc n hn).update_layout rQk k hk).update_layout 4 _ hs

def gatherAutResult (M N K k : ℕ) (js : List ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  autGatheredResult N K js.length k
    (Function.update (gatherBase M b) 4 (js.length * (N * K)))

theorem compile_gatherAutC (M N K I k : ℕ) (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ N * K) (hx : b rZ ≤ b rQx) (hy : N * K ≤ b rQy)
    (hi : I * (N * K) ≤ M) (hj : ∀ j ∈ js, j ≤ I)
    (hn : js.length ≤ M) (hk : k ≤ M) (hs : 2 * (js.length * (N * K)) ≤ M) :
    Cert (MVM.compile (gatherAutC N K k js)) (layout M N K b)
      (layout M N K (gatherAutResult M N K k js b))
      (gatherTime M N K I js.length + autGatheredTime M N K js.length k) := by
  let c := Function.update (gatherBase M b) 4 (js.length * (N * K))
  have hc := (gatherBase_inputs M N K b h).update_layout 4 _ (by omega : js.length * (N * K) ≤ M)
  have p0 := compile_gatherC M N K I js b h hb hz hi hj (by omega)
  have p1 := compile_autGatheredC M N K js.length k c hc
    (by simpa [c, gatherBase] using hb) (by simpa [c, gatherBase] using hx)
    (by simpa [c, gatherBase] using hy) hn hk (by simpa [c, two_mul] using hs)
  exact p0.seq p1

theorem gatherAutResult_length (M N K k : ℕ) (js : List ℕ) (b : Fin 64 → ℕ) :
    gatherAutResult M N K k js b 4 = 2 * (js.length * (N * K)) := by
  simp [gatherAutResult, autGatheredResult, two_mul]

theorem gatherAutResult_inputs (M N K k : ℕ) (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hn : js.length ≤ M) (hk : k ≤ M)
    (hs : 2 * (js.length * (N * K)) ≤ M) :
    RingInputs M N K (layout M N K (gatherAutResult M N K k js b)) := by
  apply autGatheredResult_inputs
  · exact (gatherBase_inputs M N K b h).update_layout 4 _ (by omega)
  · exact hn
  · exact hk
  · simpa [two_mul] using hs

theorem gatherAutResult_other (M N K k : ℕ) (js : List ℕ) (b : Fin 64 → ℕ) (r : Fin 64)
    (hr : r ∉ [1, 2, 3, 4, rQa, rQc, rQk]) : gatherAutResult M N K k js b r = b r := by
  have hn (s : Fin 64) (hs : s ∈ [1, 2, 3, 4, rQa, rQc, rQk]) : r ≠ s :=
    fun he ↦ hr (he.symm ▸ hs)
  simp [gatherAutResult, autGatheredResult, gatherBase,
    Function.update_of_ne (hn 1 (by simp)), Function.update_of_ne (hn 2 (by simp)),
    Function.update_of_ne (hn 3 (by simp)), Function.update_of_ne (hn 4 (by simp)),
    Function.update_of_ne (hn rQa (by simp)), Function.update_of_ne (hn rQc (by simp)),
    Function.update_of_ne (hn rQk (by simp))]

set_option exponentiation.threshold 1000 in
theorem autGatheredTime_concrete :
    autGatheredTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) (2 ^ 25) ≤ 2 ^ 412 := by
  have ho := operationBound_concrete (M := 2 ^ 120) (count := 2 ^ 120) le_rfl le_rfl
  unfold autGatheredTime autQueueTime autQueueBodyTime
  calc
    _ ≤ (32 * 2 ^ 66 + 32 * 2 ^ 25 + 10) * (2 * 2 ^ 120 + 5) +
      (2 ^ 66 * (2 * 2 ^ 120 + ((2 * 2 ^ 120 + 5) + moveAllowance (2 ^ 120) +
        2 ^ 340 + appendAllowance (2 ^ 120)) + 4) + 2) := by gcongr
    _ ≤ 2 ^ 412 := by norm_num [moveAllowance, appendAllowance]

set_option exponentiation.threshold 1000 in
theorem gatherAutTime_concrete (n k : ℕ) (hn : n ≤ 2 ^ 66) (hk : k ≤ 2 ^ 25) :
    gatherTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) n +
      autGatheredTime (2 ^ 120) (2 ^ 24) (2 ^ 16) n k ≤ 2 ^ 414 := by
  have hg : gatherTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) (2 ^ 66) ≤ 2 ^ 316 := by
    have := gatherTime_concrete; omega
  have ha := autGatheredTime_concrete
  have hg' : gatherTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) n ≤ 2 ^ 316 := by
    apply le_trans _ hg
    unfold gatherTime; gcongr
  have ha' : autGatheredTime (2 ^ 120) (2 ^ 24) (2 ^ 16) n k ≤ 2 ^ 412 := by
    apply le_trans _ ha
    unfold autGatheredTime autQueueTime; gcongr
  exact (Nat.add_le_add hg' ha').trans (by norm_num)

theorem compile_gatherAutC_concrete (k : ℕ) (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hb : b rB1 = 1) (hz : b rZ ≤ 2 ^ 24 * 2 ^ 16)
    (hx : b rZ ≤ b rQx) (hy : 2 ^ 24 * 2 ^ 16 ≤ b rQy)
    (hj : ∀ j ∈ js, j ≤ 2 ^ 66) (hn : js.length ≤ 2 ^ 66) (hk : k ≤ 2 ^ 25) :
    Cert (MVM.compile (gatherAutC (2 ^ 24) (2 ^ 16) k js))
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (gatherAutResult (2 ^ 120) (2 ^ 24) (2 ^ 16) k js b))
      (2 ^ 414) := by
  have hs : 2 * (js.length * (2 ^ 24 * 2 ^ 16)) ≤ 2 ^ 120 := by
    calc
      _ ≤ 2 * (2 ^ 66 * (2 ^ 24 * 2 ^ 16)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hn)
      _ ≤ 2 ^ 120 := by norm_num
  exact (compile_gatherAutC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) k js b h hb hz hx hy
    (by norm_num) hj (hn.trans (by norm_num)) (hk.trans (by norm_num)) hs).mono
      le_rfl le_rfl (gatherAutTime_concrete js.length k hn hk)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
