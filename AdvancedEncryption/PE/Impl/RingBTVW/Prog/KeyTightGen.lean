import PE.Impl.RingBTVW.Prog.KeyTightWin

/-!
# The time of the compiled `KeyGen`, per tape

`ph_keyGenF` (`PE.Impl.RingBTVW.Prog.KeyGenCost`) with the window branch charged per tape: the
key-row block leaves only tapes `0`, `2` nonblank (`v02 Gb`), and its tail (`ph_winTail_v`) charges
the key try its own loop counters. **`ph_keyGenF_v`**: for any front end meeting a phase bound
(`FT`, `FL`), `keyGenF` takes at most `keyGTFv …` steps and leaves at most `keyBLFv …` bits on tape
`0`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (leP unfrP frP leT unfrT frT tailsP ubp_tailsP ubp_prim0)
open AdvancedEncryption.PE.Gates.BPWord
open SigabaNeo.Lattices.Algo
open scoped SigabaNeo.Tape.Prog

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

variable (hk c) in
/-- The time of the branches of `KeyGen`, the window branch per tape. -/
def keyBTFv (LF : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) : ℕ :=
  let Mβ := max (8 * (nKG hk c + 2)) LF
  max ((2 * (Mβ + 1) + 3) + (Tb + winTV hk c Gb cf))
    (max (longT Mβ) (dumT hk c Mβ + frT (dumD hk c Mβ + 1)) + 1) + 1

variable (hk c) in
/-- The bound of tape `0` after the branches of `KeyGen`. -/
def keyBLFv (LF : ℕ) (_cf : KeyCfg) (Gb : ℕ) : ℕ :=
  let Mβ := max (8 * (nKG hk c + 2)) LF
  max (3 * winTop hk c Gb + 1) (max Mβ (3 * (dumD hk c Mβ + 1) + 1))

variable (hk c) in
/-- **The time of `KeyGen`'s program**, the window branch per tape. -/
def keyGTFv (FT LF : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) : ℕ :=
  leT (nKG hk c) (nKG hk c + 1) + (max (2 * (nKG hk c + 2 + 1) + 3)
    (parseT (nKG hk c + 2) + (FT + (keyBTFv hk c LF cf Tb Gb +
      (256 * (2 * (keyBLFv hk c LF cf Gb + 1) + 3) + (2 * (keyBLFv hk c LF cf Gb + 1) + 3))))) + 1)

/-- **The time and the output bound of `KeyGen`'s program**, the window branch per tape. -/
theorem ph_keyGenF_v {R : ℕ} {e : Fin (R + 2) ↪ Fin 256} (he : FrEmb e) (hR : R ≤ 166)
    {fr : XProg (R + 2)} {FT FL : ℕ → ℕ}
    (hfr : ∀ T, Ph fr (io2 (R := R) T 0 0) (FT T) (io2 (R := R) (FL T) 0 0))
    (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) {Tb Gb : ℕ}
    (hbf : ∀ β : Fin 256 → ℕ, β 0 ≤ 8 * (nKG hk c + 2) → β 1 ≤ FL (8 * (nKG hk c + 2)) →
      (∀ i, β i ≤ max (8 * (nKG hk c + 2)) (FL (8 * (nKG hk c + 2)))) → Ph bfX β Tb (v02 Gb))
    (hsW : cf.sW.length ≤ K) (hpw : (powW K (cf.B - 1)).length ≤ K) (hKT : K ≤ winTop hk c Gb)
    (hTm : ∀ x ∈ keyTmplR hk c cf, x.2 ≤ winTop hk c Gb) :
    timeBoundT (keyGenF hk c e fr bfX W cf) (Prog.inputBound (255 : Fin 256) (nKG hk c + 1)) ≤
        keyGTFv hk c (FT (8 * (nKG hk c + 2))) (FL (8 * (nKG hk c + 2))) cf Tb Gb ∧
      lenBoundT (keyGenF hk c e fr bfX W cf) (Prog.inputBound (255 : Fin 256) (nKG hk c + 1)) 0 ≤
        keyBLFv hk c (FL (8 * (nKG hk c + 2))) cf Gb := by
  set n := nKG hk c with hn
  set a := 8 * (n + 2) with ha
  set FL := FL a with hFL
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
  have p5' := p5.mono le_rfl (le_of_eq rfl) (show _ ≤ fun _ => keyBLFv hk c FL cf Gb from
    fun t => le_of_eq rfl)
  have p6 := ph_clearL clrAll (fun _ => keyBLFv hk c FL cf Gb)
  have pB := p3.seq (p4.seq (p5'.seq p6))
  have pall := p1.seq (ph_ifBlank' (254 : Fin 256) pA pB)
  have h := pall (Prog.inputBound (255 : Fin 256) (n + 1)) le_rfl
  refine ⟨h.1.trans ?_, (h.2 0).trans ?_⟩
  · have hs := supB_const_le (k := 256) (keyBLFv hk c FL cf Gb)
    have hl := length_clrAll_le
    have := Nat.mul_le_mul_right (2 * (supB (fun _ : Fin 256 => keyBLFv hk c FL cf Gb) + 1) + 3) hl
    have e : clrAll.length * (2 * (supB (fun _ : Fin 256 => keyBLFv hk c FL cf Gb) + 1) + 3) +
        (2 * (supB (fun _ : Fin 256 => keyBLFv hk c FL cf Gb) + 1) + 3) ≤
        256 * (2 * (keyBLFv hk c FL cf Gb + 1) + 3) + (2 * (keyBLFv hk c FL cf Gb + 1) + 3) := by
      have h2 : 2 * (supB (fun _ : Fin 256 => keyBLFv hk c FL cf Gb) + 1) + 3 ≤
          2 * (keyBLFv hk c FL cf Gb + 1) + 3 := by omega
      exact Nat.add_le_add (Nat.mul_le_mul hl h2) h2
    show _ ≤ leT n (n + 1) + (max (2 * (n + 2 + 1) + 3) (parseT (n + 2) + (FT a +
      (keyBTFv hk c FL cf Tb Gb + (256 * (2 * (keyBLFv hk c FL cf Gb + 1) + 3) +
        (2 * (keyBLFv hk c FL cf Gb + 1) + 3))))) + 1)
    gcongr
    exact Nat.le_of_eq rfl
  · simp [mem_clrAll, Prim.lenT, hβ1, Prog.inputBound]

end AdvancedEncryption.RingBTVW.Prog
