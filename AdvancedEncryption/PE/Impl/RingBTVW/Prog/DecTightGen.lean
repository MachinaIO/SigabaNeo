import PE.Impl.RingBTVW.Prog.DecTightCf
import PE.Impl.RingBTVW.Prog.DecGenCost

/-!
# The clock of `Dec`, per tape

`ph_decGenF` with the `c_f̂` block per tape (`cfOut`) and the end of decryption per tape
(`ph_decFinB'`): **`ph_decGenF'`** (any front end with a phase bound).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (leP unfrP frP leT unfrT frT tailsP ubp_tailsP ubp_prim0)
open AdvancedEncryption.PE.Gates.BPWord
open scoped SigabaNeo.Tape.Prog

/-- The bound after `decFinB'`. -/
def decG' (K B U0 : ℕ) : ℕ :=
  max (U0 + 6 * (1 + B) + K + 1 + K + ([true, false, false] : List Bool).length + 1)
    (U0 + 6 * (1 + B) + K + 1 + K + ([true, true, false] : List Bool).length + 1)

/-- The bound of tape `0` after the branches. -/
def decBL' (Mβ G : ℕ) : ℕ := max G (max Mβ (Mβ + 3 + 1))

/-- The time of the branches. -/
def decBT' (Mβ Tb Tf : ℕ) : ℕ :=
  max ((2 * (Mβ + 1) + 3) + (Tb + Tf)) (max (longT Mβ) ((2 * (Mβ + 1) + 3) + putT 3 Mβ) + 1) + 1

/-- **The time of `Dec`'s program**, per tape. -/
def decGT' (n Fr Mβ Tb Tf G : ℕ) : ℕ :=
  leT n (n + 1) + (max (2 * (n + 2 + 1) + 3)
    (parse4T (n + 2) + (Fr + (decBT' Mβ Tb Tf +
      (256 * (2 * (decBL' Mβ G + 1) + 3) + (2 * (decBL' Mβ G + 1) + 3))))) + 1)

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

set_option maxHeartbeats 4000000 in
/-- **The time and the output bound of `Dec`'s program, per tape**, for any front end. -/
theorem ph_decGenF' {R : ℕ} {e : Fin (R + 2) ↪ Fin 256} (he : FrEmb e) (hR : R ≤ 166)
    {fr : XProg (R + 2)} {FT FL : ℕ → ℕ}
    (hfr : ∀ T, Ph fr (io2 (R := R) T 0 0) (FT T) (io2 (R := R) (FL T) 0 0))
    (cfX : XProg 256) (B U0 T F0 F2 : ℕ) {Tb : ℕ}
    (hcf : ∀ β : Fin 256 → ℕ, β 0 ≤ 16 * (nDec hk c + 2) → β 1 ≤ FL (16 * (nDec hk c + 2)) →
      (∀ i, β i ≤ max (16 * (nDec hk c + 2)) (FL (16 * (nDec hk c + 2)))) →
        Ph cfX β Tb (cfOut F0 F2))
    (hB : ∀ x ∈ decOffs hk c, x ≤ B) (hF0 : F0 ≤ U0)
    (hF2 : F2 ≤ 2 * k * (N * K)) (hTU : T ≤ U0)
    (t1 : K ≤ T) (t2 : N ≤ T) (t3 : N * K ≤ T) (t4 : 1 ≤ T) (t5 : 2 * k ≤ T) (t6 : c.d ≤ T)
    (t7 : Algo.nT k ≤ T) (t8 : 2 * k * (N * K) ≤ U0) :
    timeBoundT (decGenF hk c e fr cfX) (Prog.inputBound (255 : Fin 256) (nDec hk c + 1)) ≤
        decGT' (nDec hk c) (FT (16 * (nDec hk c + 2)))
          (max (16 * (nDec hk c + 2)) (FL (16 * (nDec hk c + 2)))) Tb
          (decFT' N K k c.d (Algo.nT k) B U0 T) (decG' K B U0) ∧
      lenBoundT (decGenF hk c e fr cfX) (Prog.inputBound (255 : Fin 256) (nDec hk c + 1)) 0 ≤
        decBL' (max (16 * (nDec hk c + 2)) (FL (16 * (nDec hk c + 2)))) (decG' K B U0) := by
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
    (ph_decFinB' B U0 T F0 F2 hB hF0 hF2 hTU t1 t2 t3 t4 t5 t6 t7 t8))).mono le_rfl
    (show _ ≤ (2 * (Mβ + 1) + 3) + (Tb + decFT' N K k c.d (Algo.nT k) B U0 T) by
      have := supB_le_of hb4M; omega) le_rfl
  have plong := ph_of_ub hb4M (ub_longB Mβ)
  have pdum := ph_of_ub hb4M (ub_dumDec Mβ)
  have p5 := ph_ifBit' (1 : Fin 256) pwin (ph_ifBlank' (1 : Fin 256) plong pdum)
  have p5' := p5.mono le_rfl (le_of_eq rfl) (show _ ≤ fun _ => decBL' Mβ (decG' K B U0) from
    fun t => by simp only [decBL', decG']; omega)
  have p6 := ph_clearL clrAll (fun _ => decBL' Mβ (decG' K B U0))
  have pB := p3.seq (p4.seq (p5'.seq p6))
  have pall := p1.seq (ph_ifBlank' (254 : Fin 256) pA pB)
  have h := pall (Prog.inputBound (255 : Fin 256) (n + 1)) le_rfl
  refine ⟨h.1.trans ?_, (h.2 0).trans ?_⟩
  · have hs := supB_const_le (k := 256) (decBL' Mβ (decG' K B U0))
    have hl := length_clrAll_le
    have e : clrAll.length * (2 * (supB (fun _ : Fin 256 => decBL' Mβ (decG' K B U0)) + 1) + 3) +
        (2 * (supB (fun _ : Fin 256 => decBL' Mβ (decG' K B U0)) + 1) + 3) ≤
        256 * (2 * (decBL' Mβ (decG' K B U0) + 1) + 3) + (2 * (decBL' Mβ (decG' K B U0) + 1) + 3) := by
      have h2 : 2 * (supB (fun _ : Fin 256 => decBL' Mβ (decG' K B U0)) + 1) + 3 ≤
          2 * (decBL' Mβ (decG' K B U0) + 1) + 3 := by omega
      exact Nat.add_le_add (Nat.mul_le_mul hl h2) h2
    show _ ≤ leT n (n + 1) + (max (2 * (n + 2 + 1) + 3) (parse4T (n + 2) + (FT a +
      (decBT' Mβ Tb (decFT' N K k c.d (Algo.nT k) B U0 T) + (256 * (2 * (decBL' Mβ (decG' K B U0) + 1) + 3) +
        (2 * (decBL' Mβ (decG' K B U0) + 1) + 3))))) + 1)
    gcongr
    exact Nat.le_of_eq rfl
  · simp [mem_clrAll, Prim.lenT, hβ1, Prog.inputBound]

end AdvancedEncryption.RingBTVW.Prog
