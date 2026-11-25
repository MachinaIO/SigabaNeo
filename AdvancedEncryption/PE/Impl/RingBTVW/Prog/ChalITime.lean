import PE.Impl.RingBTVW.Prog.Lift

/-!
# The time of the challenge component of the ideal side

`chalIP` (`PE.Impl.RingBTVW.Prog.ChalI`) drops a prefix of `D` bits, then (for `μ = true`) moves
`P` bits to a scratch tape, flips one bit and moves the prefix back. Its tapes only shrink or are
shuffled, so it is bounded in the shape `shp 6 0 S` (every tape at most `S`, the unused tape `6`
blank): the moves grow the scratch by `P + 1`, and moving the scratch back
(`appendTapeP 2 0 3 4`, `app20_bounds`) at most doubles it.

**`time_chalIP`**: `timeBoundT (chalIP hk c) (io2 a b 0) ≤ timeChalI hk c a b`, and the same for
the lift `chalIL` (`time_chalIL`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg Matrix
  AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

/-! ### Primitives in the shape `shp 6 0 S` -/

theorem atb6_prim (p : Prim 7) {s : ℕ}
    (h : ∀ x S, p.lenT (shp (6 : Fin 7) x S) ≤ shp 6 x (S + s)) :
    ATB (prog (.prim p)) (6 : Fin 7) 0 0 s tBit :=
  ATB.prim p fun x S _ => by simpa using h x S

theorem atb6_tail (j : Fin 7) : ATB (prog (.prim (.tail j))) (6 : Fin 7) 0 0 0 tBit :=
  atb6_prim _ fun x S i => by
    simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> omega

theorem atb6_clear (j : Fin 7) : ATB (prog (.prim (.clear j))) (6 : Fin 7) 0 0 0 tBit :=
  atb6_prim _ fun x S i => by
    simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> omega

theorem atb6_cons (j : Fin 7) (hj : j ≠ 6) (b : Bool) :
    ATB (prog (.prim (.cons j b))) (6 : Fin 7) 0 0 1 tBit :=
  atb6_prim _ fun x S i => by
    simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> simp_all

theorem atb6_snocHead (j j' : Fin 7) (hj : j ≠ 6) :
    ATB (prog (.prim (.snocHead j j'))) (6 : Fin 7) 0 0 1 tBit :=
  atb6_prim _ fun x S i => by
    simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> simp_all

theorem atb6_copy (j j' : Fin 7) (hj : j ≠ 6) (hj' : j' ≠ 6) :
    ATB (prog (.prim (.copy j j'))) (6 : Fin 7) 0 0 0 tBit :=
  atb6_prim _ fun x S i => by
    simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> simp_all

/-! ### Moving the scratch back -/

theorem app20_bounds {ℓ : Fin 7 → ℕ} {S : ℕ} (hℓ : ℓ ≤ shp (6 : Fin 7) 0 S) :
    timeBoundT (appendTapeP 2 0 3 4) ℓ ≤ tApp S S S ∧
      lenBoundT (appendTapeP 2 0 3 4) ℓ ≤ shp (6 : Fin 7) 0 (S + S) := by
  have hℓ' : ℓ ≤ shp (2 : Fin 7) S S := fun i => by
    have := hℓ i; simp only [shp] at this ⊢; split_ifs at this ⊢ <;> omega
  have hb2 : ATB (prog (.prim (.snocHead 2 3))) (2 : Fin 7) 0 1 0 tBit :=
    ATB.prim _ fun x S _ i => by
      simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> omega
  have hb3 : ATB (prog (.prim (.tail 3))) (2 : Fin 7) 0 0 0 tBit :=
    ATB.prim _ fun x S _ i => by
      simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> omega
  have hb := hb2.seq hb3
  set ℓ1 := (Prim.copy 3 0).lenT ℓ
  have h0 : ℓ 0 ≤ S := by have := hℓ' 0; simpa [shp] using this
  have hℓ1 : ℓ1 ≤ shp (2 : Fin 7) S S := fun i => by
    simp only [ℓ1, Prim.lenT, Function.update_apply]
    split_ifs with h
    · subst h; simp only [shp]; simp; omega
    · exact hℓ' i
  have hf := forN_bounds (r := (2 : Fin 7)) (t := 0) (c := 4) (by decide) hb
    ⟨preserves_prim (by simp [Prim.writes]), preserves_prim (by simp [Prim.writes])⟩
    (mono2_seq 1 0 mono_tBit mono_tBit) (Nat.zero_le S) le_rfl hℓ1
    (by simp only [ℓ1, Prim.lenT, Function.update_apply]; simpa using h0)
  have hs0 := supB_shp (2 : Fin 7) S S
  have hs1 := supB_mono hℓ'
  set ℓ2 := lenBoundT (forN 4 0 (XProg.seq (prog (.prim (.snocHead 2 3))) (prog (.prim (.tail 3))))) ℓ1
  have hℓ2 : ℓ2 ≤ shp (2 : Fin 7) (S + S) S := hf.2.trans (shp_mono (by simp) (by simp))
  have hs2 := supB_mono hℓ2
  have hs3 := supB_shp (2 : Fin 7) (S + S) S
  have hℓ3 : (Prim.clear 3).lenT ℓ2 ≤ shp (2 : Fin 7) (S + S) S := fun i => by
    simp only [Prim.lenT, Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact hℓ2 i
  have hs4 := supB_mono hℓ3
  refine ⟨?_, ?_⟩
  · show timeBoundT (prog (.prim (.copy 3 0))) ℓ + (timeBoundT _ ℓ1 +
      (timeBoundT (prog (.prim (.clear 3))) ℓ2 +
        timeBoundT (prog (.prim (.clear 0))) ((Prim.clear 3).lenT ℓ2))) ≤ _
    rw [timeBoundT_prim, timeBoundT_prim, timeBoundT_prim]
    have := hf.1
    rw [show S + S * (1 + 0) = S + S by ring, show S + S * (0 + 0) = S by ring,
      show S + S + 1 = S + S + 1 by rfl] at this
    simp only [Nat.add_zero] at this
    simp only [Prim.pad, tApp]
    omega
  · intro i
    by_cases h6 : i = 6
    · subst h6
      rw [lenBoundT_of_preserves _ 6 (by
        simp [appendTapeP, forN, XProg.Preserves, Prog.Preserves, Prim.writes]) ℓ]
      exact hℓ 6
    show Function.update ((Prim.clear 3).lenT ℓ2) 0 0 i ≤ _
    rw [Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · refine (hℓ3 i).trans ?_
      simp only [shp, if_neg h6]; split_ifs <;> omega

/-! ### The pieces of the challenge -/

/-- The time of one transfer step (`snocHead 2 0`, `tail 0`). -/
def tMv (x S : ℕ) : ℕ := tBit x S + tBit (x + 0) (S + 1)

theorem mono_tMv : Mono2 tMv := mono2_seq 0 1 mono_tBit mono_tBit

theorem atb6_dropF (D : ℕ) :
    ATB (dropF D) (6 : Fin 7) (max 0 D) (D * 0) (D * 0) (countT D 0 0 tBit) :=
  ATB.count (t := (3 : Fin 7)) (c := 4) (by decide) (by decide) (by decide) (atb6_tail 0)
    (preserves_prim (by simp [Prim.writes])) mono_tBit D

theorem atb6_mvLoop (P : ℕ) :
    ATB (withCount 3 4 P (forN 4 3 (seq (prog (.prim (.snocHead 2 0))) (prog (.prim (.tail 0))))))
      (6 : Fin 7) (max 0 P) (P * (0 + 0)) (P * (1 + 0)) (countT P (0 + 0) (1 + 0) tMv) :=
  ATB.count (t := (3 : Fin 7)) (c := 4) (by decide) (by decide) (by decide) ((atb6_snocHead 2 0 (by decide)).seq (atb6_tail 0))
    ⟨preserves_prim (by simp [Prim.writes]), preserves_prim (by simp [Prim.writes])⟩ mono_tMv P

/-- The time of flipping the head. -/
def tFH (x S : ℕ) : ℕ := max (tBit x S + tBit (x + 0) (S + 0)) (tBit x S + tBit (x + 0) (S + 0)) + 1

theorem atb6_flipHead : ATB flipHead (6 : Fin 7) 0 (0 + 0) (0 + 1) tFH :=
  ATB.ifBit 0 ((atb6_tail 0).seq (atb6_cons 0 (by decide) false))
    ((atb6_tail 0).seq (atb6_cons 0 (by decide) true))

/-- **The time of `flipP P`** from the shape `shp 6 0 S`. -/
def tFlip (P S : ℕ) : ℕ :=
  countT P (0 + 0) (1 + 0) tMv 0 S + (tFH 0 (S + P) + (tApp (S + P + 1) (S + P + 1) (S + P + 1) +
    (tBit 0 (2 * (S + P + 1)) + tBit 0 (2 * (S + P + 1)))))

theorem flipP_bounds (P : ℕ) {ℓ : Fin 7 → ℕ} {S : ℕ} (hP : P ≤ S) (hℓ : ℓ ≤ shp (6 : Fin 7) 0 S) :
    timeBoundT (flipP P) ℓ ≤ tFlip P S ∧
      lenBoundT (flipP P) ℓ ≤ shp (6 : Fin 7) 0 (2 * (S + P + 1)) := by
  have hL := atb6_mvLoop P 0 S (by omega)
  set mv : XProg 7 := withCount 3 4 P (forN 4 3 (seq (prog (.prim (.snocHead 2 0))) (prog (.prim (.tail 0)))))
  have hℓ1 : lenBoundT mv ℓ ≤ shp (6 : Fin 7) 0 (S + P) :=
    ((lenBoundT_mono mv hℓ).trans hL.2).trans (shp_mono (by simp) (by simp))
  have hFH := atb6_flipHead 0 (S + P) (Nat.zero_le _)
  have hℓ2 : lenBoundT flipHead (lenBoundT mv ℓ) ≤ shp (6 : Fin 7) 0 (S + P + 1) :=
    ((lenBoundT_mono flipHead hℓ1).trans hFH.2).trans (shp_mono (by simp) (by simp))
  have hA := app20_bounds hℓ2
  set ℓ3 := lenBoundT (appendTapeP 2 0 3 4) (lenBoundT flipHead (lenBoundT mv ℓ))
  have hℓ3 : ℓ3 ≤ shp (6 : Fin 7) 0 (2 * (S + P + 1)) :=
    hA.2.trans (shp_mono le_rfl (by omega))
  have hC := atb6_copy 0 2 (by decide) (by decide) 0 (2 * (S + P + 1)) (Nat.zero_le _)
  have hℓ4 : lenBoundT (prog (.prim (.copy 0 2))) ℓ3 ≤ shp (6 : Fin 7) 0 (2 * (S + P + 1)) :=
    ((lenBoundT_mono _ hℓ3).trans hC.2).trans (shp_mono (by simp) (by simp))
  have hK := atb6_clear 2 0 (2 * (S + P + 1)) (Nat.zero_le _)
  refine ⟨?_, ?_⟩
  · show timeBoundT mv ℓ + (timeBoundT flipHead (lenBoundT mv ℓ) +
      (timeBoundT (appendTapeP 2 0 3 4) (lenBoundT flipHead (lenBoundT mv ℓ)) +
        (timeBoundT (prog (.prim (.copy 0 2))) ℓ3 +
          timeBoundT (prog (.prim (.clear 2))) (lenBoundT (prog (.prim (.copy 0 2))) ℓ3)))) ≤ _
    have t1 := (timeBoundT_mono mv hℓ).trans hL.1
    have t2 := (timeBoundT_mono flipHead hℓ1).trans hFH.1
    have t4 := (timeBoundT_mono _ hℓ3).trans hC.1
    have t5 := (timeBoundT_mono _ hℓ4).trans hK.1
    unfold tFlip
    omega
  · show lenBoundT (prog (.prim (.clear 2))) (lenBoundT (prog (.prim (.copy 0 2))) ℓ3) ≤ _
    exact ((lenBoundT_mono _ hℓ4).trans hK.2).trans (shp_mono (by simp) (by simp))

/-- Clearing the scratch tapes. -/
theorem clrS_bounds {ℓ : Fin 7 → ℕ} {S : ℕ} (hℓ : ℓ ≤ shp (6 : Fin 7) 0 S) :
    timeBoundT clrS ℓ ≤ 6 * tBit 0 S ∧ lenBoundT clrS ℓ = fun t => if t = 0 then ℓ 0 else 0 := by
  have h := (atb6_clear 1).seq ((atb6_clear 2).seq ((atb6_clear 3).seq ((atb6_clear 4).seq
    ((atb6_clear 5).seq (atb6_clear 6)))))
  refine ⟨((timeBoundT_mono _ hℓ).trans (h 0 S (Nat.zero_le _)).1).trans
    (le_of_eq (by simp only [Nat.add_zero]; ring)), ?_⟩
  funext t
  fin_cases t <;> rfl

/-- **The time of the challenge body** from the shape `shp 6 0 S`. -/
def tChal (D P S : ℕ) : ℕ :=
  countT D 0 0 tBit 0 S + (max (tFlip P S) (tBit 0 S) + 1 + 6 * tBit 0 (2 * (S + P + 1)))

theorem time_chalBodyP (D P : ℕ) {ℓ : Fin 7 → ℕ} {S : ℕ} (hD : D ≤ S) (hP : P ≤ S)
    (hℓ : ℓ ≤ shp (6 : Fin 7) 0 S) : timeBoundT (chalBodyP D P) ℓ ≤ tChal D P S := by
  have hd := atb6_dropF D 0 S (by omega)
  have hℓ1 : lenBoundT (dropF D) ℓ ≤ shp (6 : Fin 7) 0 S :=
    ((lenBoundT_mono _ hℓ).trans hd.2).trans (shp_mono (by simp) (by simp))
  have hF := flipP_bounds P hP hℓ1
  have hN := atb6_copy 2 2 (by decide) (by decide) 0 S (Nat.zero_le _)
  have hNl : lenBoundT nopX (lenBoundT (dropF D) ℓ) ≤ shp (6 : Fin 7) 0 (2 * (S + P + 1)) :=
    ((lenBoundT_mono _ hℓ1).trans hN.2).trans (shp_mono (by simp) (by omega))
  have hℓ2 : lenBoundT (ifBit 1 (flipP P) nopX) (lenBoundT (dropF D) ℓ) ≤
      shp (6 : Fin 7) 0 (2 * (S + P + 1)) := fun t => max_le (hF.2 t) (hNl t)
  show timeBoundT (dropF D) ℓ + ((max (timeBoundT (flipP P) (lenBoundT (dropF D) ℓ))
    (timeBoundT nopX (lenBoundT (dropF D) ℓ)) + 1) +
      timeBoundT clrS (lenBoundT (ifBit 1 (flipP P) nopX) (lenBoundT (dropF D) ℓ))) ≤ _
  have t1 := (timeBoundT_mono _ hℓ).trans hd.1
  have t2 := (timeBoundT_mono nopX hℓ1).trans hN.1
  have t3 := (clrS_bounds hℓ2).1
  have hm := max_le_max hF.1 t2
  unfold tChal
  omega

/-- **The length bound of the challenge body**: the output alone on tape `0`. -/
theorem len_chalBodyP (D P : ℕ) {ℓ : Fin 7 → ℕ} {S : ℕ} (hD : D ≤ S) (hP : P ≤ S)
    (hℓ : ℓ ≤ shp (6 : Fin 7) 0 S) :
    lenBoundT (chalBodyP D P) ℓ ≤ io2 (R := 5) (2 * (S + P + 1)) 0 0 := by
  have hd := atb6_dropF D 0 S (by omega)
  have hℓ1 : lenBoundT (dropF D) ℓ ≤ shp (6 : Fin 7) 0 S :=
    ((lenBoundT_mono _ hℓ).trans hd.2).trans (shp_mono (by simp) (by simp))
  have hF := flipP_bounds P hP hℓ1
  have hN := atb6_copy 2 2 (by decide) (by decide) 0 S (Nat.zero_le _)
  have hNl : lenBoundT nopX (lenBoundT (dropF D) ℓ) ≤ shp (6 : Fin 7) 0 (2 * (S + P + 1)) :=
    ((lenBoundT_mono _ hℓ1).trans hN.2).trans (shp_mono (by simp) (by omega))
  have hℓ2 : lenBoundT (ifBit 1 (flipP P) nopX) (lenBoundT (dropF D) ℓ) ≤
      shp (6 : Fin 7) 0 (2 * (S + P + 1)) := fun t => max_le (hF.2 t) (hNl t)
  show lenBoundT clrS (lenBoundT (ifBit 1 (flipP P) nopX) (lenBoundT (dropF D) ℓ)) ≤ _
  rw [(clrS_bounds hℓ2).2]
  intro t
  have h0 := hℓ2 0
  simp only [shp] at h0
  simp only [io2]
  split_ifs <;> simp_all

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The scale of the challenge component for inputs of at most `a`, `b` bits. -/
def sChalI (a b : ℕ) : ℕ := max (max a b) (max (preI hk c) (offK hk c + (K - 1)))

/-- **The time of the challenge component of the ideal side.** -/
def timeChalI (a b : ℕ) : ℕ := tChal (preI hk c) (offK hk c + (K - 1)) (sChalI hk c a b)

theorem time_chalIP (a b : ℕ) :
    timeBoundT (chalIP hk c) (io2 (R := 5) a b 0) ≤ timeChalI hk c a b := by
  refine time_chalBodyP _ _ (by unfold sChalI; omega) (by unfold sChalI; omega) fun i => ?_
  simp only [io2, shp, sChalI]
  split_ifs <;> omega

/-- **The length bound of the challenge component of the ideal side.** -/
theorem len_chalIP (a b : ℕ) :
    lenBoundT (chalIP hk c) (io2 (R := 5) a b 0) ≤
      io2 (2 * (sChalI hk c a b + (offK hk c + (K - 1)) + 1)) 0 0 := by
  refine len_chalBodyP _ _ (by unfold sChalI; omega) (by unfold sChalI; omega) fun i => ?_
  simp only [io2, shp, sChalI]
  split_ifs <;> omega

/-- **The time of the lifted challenge component of the ideal side.** -/
theorem time_chalIL (a b : ℕ) :
    timeBoundT (chalIL hk c) (io2 (R := 80) a b 0) ≤ timeChalI hk c a b := by
  rw [chalIL, time_lift82]; exact time_chalIP hk c a b

theorem len_chalIL (a b : ℕ) :
    lenBoundT (chalIL hk c) (io2 (R := 80) a b 0) ≤
      io2 (2 * (sChalI hk c a b + (offK hk c + (K - 1)) + 1)) 0 0 :=
  lenBoundT_liftP_le _ _ (len_chalIP hk c a b)

end AdvancedEncryption.RingBTVW.Prog
