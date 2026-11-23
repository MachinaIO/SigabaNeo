import PE.Impl.DualUse.Prog.KeyTightWin

/-!
# The time of the compiled `KeyGen`, per tape

`ph_keyGenP` (`PE.Impl.DualUse.Prog.KeyGenCost`) with the window branch charged per tape: the
key-row block leaves only tapes `0`, `2` nonblank (`v02 Gb`), and its tail (`ph_winTail_v`) charges
the key try its own loop counters. **`ph_keyGenP_v`**: `keyGenP` takes at most `keyGTv' …` steps
and leaves at most `keyBLv' …` bits on tape `0`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (leP unfrP frP leT unfrT frT tailsP ubp_tailsP ubp_prim0)
open AdvancedEncryption.PE.Gates.BPWord
open SigabaNeo.Lattices.Algo
open scoped SigabaNeo.Tape.Prog

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

variable (hk c) in
/-- The time of the branches of `KeyGen`, the window branch per tape. -/
def keyBTv' (W : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) : ℕ :=
  let Mβ := max (8 * (nKG hk c + 2)) (frontL c.L W)
  max ((2 * (Mβ + 1) + 3) + (Tb + winTV hk c Gb cf))
    (max (longT Mβ) (dumT hk c Mβ + frT (dumD hk c Mβ + 1)) + 1) + 1

variable (hk c) in
/-- The bound of tape `0` after the branches of `KeyGen`. -/
def keyBLv' (W : ℕ) (_cf : KeyCfg) (Gb : ℕ) : ℕ :=
  let Mβ := max (8 * (nKG hk c + 2)) (frontL c.L W)
  max (3 * winTop hk c Gb + 1) (max Mβ (3 * (dumD hk c Mβ + 1) + 1))

variable (hk c) in
/-- **The time of `KeyGen`'s program**, the window branch per tape. -/
def keyGTv' (W : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) : ℕ :=
  leT (nKG hk c) (nKG hk c + 1) + (max (2 * (nKG hk c + 2 + 1) + 3)
    (parseT (nKG hk c + 2) + (frontT c.L W (8 * (nKG hk c + 2)) + (keyBTv' hk c W cf Tb Gb +
      (256 * (2 * (keyBLv' hk c W cf Gb + 1) + 3) + (2 * (keyBLv' hk c W cf Gb + 1) + 3))))) + 1)

theorem ph_keyGenP_v (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) {Tb Gb : ℕ}
    (hbf : ∀ β : Fin 256 → ℕ, β 0 ≤ 8 * (nKG hk c + 2) → β 1 ≤ frontL c.L W →
      (∀ i, β i ≤ max (8 * (nKG hk c + 2)) (frontL c.L W)) → Ph bfX β Tb (v02 Gb))
    (hsW : cf.sW.length ≤ K) (hpw : (powW K (cf.B - 1)).length ≤ K) (hKT : K ≤ winTop hk c Gb)
    (hTm : ∀ x ∈ keyTmplR hk c cf, x.2 ≤ winTop hk c Gb) :
    timeBoundT (keyGenP hk c bfX W cf) (Prog.inputBound (255 : Fin 256) (nKG hk c + 1)) ≤ keyGTv' hk c W cf Tb Gb ∧
      lenBoundT (keyGenP hk c bfX W cf) (Prog.inputBound (255 : Fin 256) (nKG hk c + 1)) 0 ≤ keyBLv' hk c W cf Gb := by
  set n := nKG hk c with hn
  set a := 8 * (n + 2) with ha
  set FL := frontL c.L W with hFL
  set Mβ := max a FL with hMβ
  have h0 : ∀ i, Prog.inputBound (255 : Fin 256) (n + 1) i ≤ n + 1 := fun i => by
    simp only [Prog.inputBound, Function.update_apply]; split_ifs <;> omega
  have p1 := ph_guard n (n + 1) h0
  set β1 := fun i => if i ∈ [(254 : Fin 256), 253] then n + 1 + 1 else Prog.inputBound (255 : Fin 256) (n + 1) i
    with hβ1
  have hβ1M : ∀ i, β1 i ≤ n + 2 := fun i => by
    simp only [hβ1]; split_ifs
    · omega
    · have := h0 i; omega
  -- the short branch
  have pA := (ph_prim (Prim.clear (255 : Fin 256)) β1).mono le_rfl
    (show 2 * (supB β1 + 1) + 3 ≤ 2 * (n + 2 + 1) + 3 by have := supB_le_of hβ1M; omega) le_rfl
  -- parsing
  have p3 := ph_parse (n + 2) hβ1M
  set β3 := fun i => if i ∈ [(254 : Fin 256), 253, 0, 1, 251, 252, 255] then 2 * (2 * (2 * (n + 2)))
    else β1 i with hβ3
  have hβ3e : ∀ j, (fun j => β3 (eFr j)) j ≤ io2 (R := 6) a 0 0 j := by
    intro j
    simp only [hβ3, hβ1, Prog.inputBound, Function.update_apply, io2]
    by_cases hj : j.val = 0
    · have : eFr j = 1 := Fin.ext (by rw [eFr_val]; simp [hj])
      simp [this, hj, ha]; omega
    · have hv : (eFr j).val = j.val + 82 := by rw [eFr_val]; simp [hj]
      have hne : ∀ t : Fin 256, t.val ≤ 82 ∨ t.val ≥ 90 → eFr j ≠ t := fun t ht e => by
        rw [← e, hv] at ht; have := j.isLt; omega
      have h1 : eFr j ≠ 254 := hne 254 (by simp)
      have h2 : eFr j ≠ 253 := hne 253 (by simp)
      have h3 : eFr j ≠ 0 := hne 0 (by simp)
      have h4 : eFr j ≠ 1 := hne 1 (by simp)
      have h5 : eFr j ≠ 251 := hne 251 (by simp)
      have h6 : eFr j ≠ 252 := hne 252 (by simp)
      have h7 : eFr j ≠ 255 := hne 255 (by simp)
      simp [h1, h2, h3, h4, h5, h6, h7, hj]
  have p4 := ph_front c.L W a (β := β3) (fun j => hβ3e j)
  set β4 := embedF eFr β3 (io2 (R := 6) FL 0 0) with hβ4
  have hb40 : β4 0 = a := by
    rw [hβ4]
    rcases embedF_cases eFr β3 (io2 (R := 6) FL 0 0) 0 with ⟨-, h⟩ | ⟨j, hj, -⟩
    · rw [h]; simp [hβ3]; omega
    · exact absurd hj (eFr_ne_zero j)
  have hb41 : β4 1 ≤ FL := by
    rw [hβ4, show (1 : Fin 256) = eFr 0 from Fin.ext (by rw [eFr_val]; simp), embedF_apply_self]
    simp [io2]
  have hb4M : ∀ i, β4 i ≤ Mβ := by
    intro i
    rw [hβ4]
    rcases embedF_cases eFr β3 (io2 (R := 6) FL 0 0) i with ⟨-, h⟩ | ⟨j, -, h⟩
    · rw [h]; simp only [hβ3, hβ1, Prog.inputBound, Function.update_apply]
      split_ifs <;> omega
    · rw [h]; simp only [io2]; split_ifs <;> omega
  -- the branches
  have pwin := ((ph_prim (Prim.tail (1 : Fin 256)) β4).seq ((hbf _ (by simp [Prim.lenT, hb40])
    (by simp only [Prim.lenT, Function.update_apply]; split_ifs <;> omega)
    (fun i => by simp only [Prim.lenT, Function.update_apply]; split_ifs <;> have := hb4M i <;> omega)).seq
    (ph_winTail_v hk c Gb cf hsW hpw hKT hTm))).mono le_rfl
    (show _ ≤ (2 * (Mβ + 1) + 3) + (Tb + winTV hk c Gb cf) by
      have := supB_le_of hb4M; omega) le_rfl
  have plong := ph_of_ub hb4M (ub_longB Mβ)
  have pdum := ph_of_ub hb4M ((ub_dumB hk c Mβ).seq (show UB (prog (Prog.map uF frP)) _ _ _ from
    fun ℓ hℓ => ubp_frP_map uF _ ℓ hℓ))
  have p5 := ph_ifBit' (1 : Fin 256) pwin (ph_ifBlank' (1 : Fin 256) plong pdum)
  have p5' := p5.mono le_rfl (le_of_eq rfl) (show _ ≤ fun _ => keyBLv' hk c W cf Gb from
    fun t => le_of_eq rfl)
  have p6 := ph_clearL clrAll (fun _ => keyBLv' hk c W cf Gb)
  have pB := p3.seq (p4.seq (p5'.seq p6))
  have pall := p1.seq (ph_ifBlank' (254 : Fin 256) pA pB)
  have h := pall (Prog.inputBound (255 : Fin 256) (n + 1)) le_rfl
  refine ⟨h.1.trans ?_, (h.2 0).trans ?_⟩
  · have hs := supB_const_le (k := 256) (keyBLv' hk c W cf Gb)
    have hl := length_clrAll_le
    have := Nat.mul_le_mul_right (2 * (supB (fun _ : Fin 256 => keyBLv' hk c W cf Gb) + 1) + 3) hl
    have e : clrAll.length * (2 * (supB (fun _ : Fin 256 => keyBLv' hk c W cf Gb) + 1) + 3) +
        (2 * (supB (fun _ : Fin 256 => keyBLv' hk c W cf Gb) + 1) + 3) ≤
        256 * (2 * (keyBLv' hk c W cf Gb + 1) + 3) + (2 * (keyBLv' hk c W cf Gb + 1) + 3) := by
      have h2 : 2 * (supB (fun _ : Fin 256 => keyBLv' hk c W cf Gb) + 1) + 3 ≤
          2 * (keyBLv' hk c W cf Gb + 1) + 3 := by omega
      exact Nat.add_le_add (Nat.mul_le_mul hl h2) h2
    show _ ≤ leT n (n + 1) + (max (2 * (n + 2 + 1) + 3) (parseT (n + 2) + (frontT c.L W a +
      (keyBTv' hk c W cf Tb Gb + (256 * (2 * (keyBLv' hk c W cf Gb + 1) + 3) +
        (2 * (keyBLv' hk c W cf Gb + 1) + 3))))) + 1)
    gcongr
    exact Nat.le_of_eq rfl
  · simp [mem_clrAll, Prim.lenT, hβ1, Prog.inputBound]


end AdvancedEncryption.DualUse.Prog
