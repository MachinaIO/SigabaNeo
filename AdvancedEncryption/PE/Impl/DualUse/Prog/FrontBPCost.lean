import PE.Impl.DualUse.Prog.FrontBP
import PE.Impl.DualUse.Prog.WfB2Time
import PE.Impl.DualUse.Prog.CostTools

/-!
# The cost of the front end for branching programs (Stage II, not wired)

From a query of at most `T` bits (`io2 T 0 0`), with `S = max (T + 1) bpLen` (`allG`, `S0` of the
compiler's certificate, `BpCompCost`):

* every piece is bounded uniformly (`UB`); the compiler is entered after the tapes `1 … 63` are
  cleared, so its own bounds `bounds_bpCompP` on `inB S` apply;
* **`ph_frontBP`**: at most `frontBT n T` steps, at most `frontBA = bpLen + allG + S0 + 1` bits on
  tape `0` (whatever `T`: the word is cut to `bpLen` bits before the compiler), every other tape
  blank (the final clearing);
* **`size_frontBP_le`**: at most `36 n + 2^56` states (the guard `leP n` is linear in `n`, the cut's
  template `60 · bpLen ≈ 2^54.8`, the length test logarithmic, the compiler `≤ 2^27`);
* **`frontSpecG_frontBP`**: the interface `FrontSpecG` with these three bounds.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Lattices
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord
open AdvancedEncryption.DualUse.BpComp (bpCompC allN allG S0 Uc inB)

theorem bpLen_le : bpLen ≤ 2 ^ 49 := by unfold bpLen; norm_num

theorem bpLen_eq : bpLen = BpComp.bpLenA := rfl

/-! ### Uniform bounds of the pieces -/

theorem UB.lower {k : ℕ} {p : XProg k} {M M₀ T M' : ℕ} (h : UB p M T M') (hM : M₀ ≤ M) :
    UB p M₀ T M' := fun ℓ hℓ => h ℓ fun i => (hℓ i).trans hM

theorem ub_frame_ubp {k m : ℕ} (e : Fin m ↪ Fin k) {p : Prog m} {M T M' : ℕ} (h : Prog.UBP p M T M') :
    UB (frame e (prog p)) M T (max M M') := by
  intro ℓ hℓ
  have h' := h (fun j => ℓ (e j)) (fun j => hℓ (e j))
  refine ⟨by rw [timeBoundT_frame, timeBoundT_prog]; exact h'.1, fun i => ?_⟩
  show embedF e ℓ (Prog.lenBoundT p fun j => ℓ (e j)) i ≤ _
  rcases embedF_cases e ℓ (Prog.lenBoundT p fun j => ℓ (e j)) i with ⟨-, h⟩ | ⟨j, rfl, h⟩
  · rw [h]; exact (hℓ i).trans (le_max_left _ _)
  · rw [h]; exact (h'.2 j).trans (le_max_right _ _)

/-- The time of a clearing of at most `72` tapes from tapes below `M`. -/
def clr72T (M : ℕ) : ℕ := 72 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3)

theorem length_clr63 : clr63.length ≤ 72 :=
  (List.length_filter_le _ _).trans (by rw [List.length_finRange])

theorem length_clr71 : clr71.length ≤ 72 :=
  (List.length_filter_le _ _).trans (by rw [List.length_finRange])

theorem ub_clearL72 {l : List (Fin 72)} (hl : l.length ≤ 72) (M : ℕ) :
    UB (clearL l) M (clr72T M) M :=
  (ub_clearL M l).mono (by unfold clr72T; have := Nat.mul_le_mul_right (2 * (M + 1) + 3) hl; omega)
    le_rfl

/-- The output bound of the front end: the compiler's bound at `m`, plus the bit `f(0)` and the
consed `true` (and one bit of slack). -/
def frontBA (m : ℕ) : ℕ := m + allG + S0 + 3

theorem frontBA_pos (m : ℕ) : 1 ≤ frontBA m := by unfold frontBA; omega

/-- The bound of the other tapes in the branches (`2^49`: the tapes of the authorization program). -/
def BB (m S : ℕ) : ℕ := max S (frontBA m) + 2 ^ 49

/-- The per-tape bound after the branches: `frontBA m` on tape `0`, `BB m S` elsewhere. -/
def βo (m S : ℕ) : Fin 72 → ℕ := fun t => if t = 0 then frontBA m else BB m S

/-- The per-tape bound after the compiler: tape `0` below `m + allG + S0 + 1`. -/
def βc (m S : ℕ) : Fin 72 → ℕ := fun t => if t = 0 then m + allG + S0 + 1 else max S (frontBA m)

theorem pcount_cutPn (m : ℕ) : Prog.pcount (cutPn m) = m + 5 := by
  simp only [cutPn, Prog.pcount, SigabaNeo.Tape.Prog.pcount_putW, List.length_replicate]

/-- The time of the cut from tapes below `S`. -/
def cutBT (m S : ℕ) : ℕ := (m + 5) * (2 * (max S m + (m + 5)) + 5)

theorem lenBoundT_cutPn (m : ℕ) (ℓ : Fin 72 → ℕ) :
    Prog.lenBoundT (cutPn m) ℓ = Function.update (Function.update (Function.update (Function.update
      (Function.update ℓ 69 m) 0 0) 0 m) 69 0) 69 0 := by
  simp only [cutPn, Prog.lenBoundT, SigabaNeo.Tape.Prog.lenBoundT_putW, Prim.lenT,
    List.length_replicate]
  funext t
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem loopFree_cutPn (m : ℕ) : (cutPn m).LoopFree :=
  ⟨SigabaNeo.Tape.Prog.loopFree_putW _ _, trivial, trivial, trivial, trivial⟩

/-- The time of the valid branch after its first clearing. -/
def compBT (m S : ℕ) : ℕ :=
  cutBT m S + (clr72T (max S m) + (allN * Uc allG m + (2 * (max S (frontBA m) + 1) + 3)))

/-- **The cut, the compiler and the consed bit**, from tapes below `S`: tape `0` below
`frontBA m`. -/
theorem ph_comp (m S : ℕ) :
    Ph (seq (prog (cutPn m)) (seq (clearL clr63) (seq (frame e64 (prog bpCompC))
      (prog (.prim (.cons 0 true)))))) (fun _ => S) (compBT m S) (βc m S) := by
  intro ℓ hℓ
  set ℓ1 := Prog.lenBoundT (cutPn m) ℓ with hℓ1
  have c0 : ℓ1 0 ≤ m := by rw [hℓ1, lenBoundT_cutPn]; simp [Function.update_apply]
  have cM : ∀ t, ℓ1 t ≤ max S m := fun t => by
    rw [hℓ1, lenBoundT_cutPn]
    simp only [Function.update_apply]
    have : ℓ t ≤ S := hℓ t
    split_ifs <;> omega
  have tc : Prog.timeBoundT (cutPn m) ℓ ≤ cutBT m S := by
    have := Prog.timeBoundT_le_pcount (cutPn m) (loopFree_cutPn m) ℓ
      (M := max S m) (fun t => (hℓ t).trans (le_max_left _ _))
    rwa [pcount_cutPn] at this
  have hc := ub_clearL72 length_clr63 (max S m) ℓ1 cM
  set ℓ2 := lenBoundT (clearL clr63) ℓ1 with hℓ2
  have c2 : ∀ t, ℓ2 t ≤ if t ∈ clr63 then 0 else ℓ1 t := lenBoundT_clearL_le clr63 ℓ1
  have hv : (fun j => ℓ2 (e64 j)) ≤ inB m := by
    intro j
    have h := c2 (e64 j)
    simp only [inB, Function.update_apply]
    by_cases hj : j = BpComp.tIN
    · subst hj
      have hn : e64 BpComp.tIN ∉ clr63 := by rw [mem_clr63]; simp [e64]
      rw [if_pos rfl]; rw [if_neg hn] at h; exact h.trans c0
    · rw [if_neg hj]
      have hm : e64 j ∈ clr63 := by
        rw [mem_clr63]
        refine ⟨fun e => hj (Fin.ext ?_), by simp [e64]⟩
        have := congrArg Fin.val e; simpa [e64] using this
      rw [if_pos hm] at h; exact h
  obtain ⟨b1, b2⟩ := BpComp.bounds_bpCompP BpComp.Rbp BpComp.Rbp_ok BpComp.Rbp_fits m
  set ℓ3 := embedF e64 ℓ2 (Prog.lenBoundT bpCompC fun j => ℓ2 (e64 j)) with hℓ3
  have c3 : ∀ t, ℓ3 t ≤ max (max S m) (m + allG + S0) := fun t => by
    rcases embedF_cases e64 ℓ2 (Prog.lenBoundT bpCompC fun j => ℓ2 (e64 j)) t with
      ⟨-, h⟩ | ⟨j, rfl, h⟩
    · rw [hℓ3, h]; exact (hc.2 t).trans (le_max_left _ _)
    · rw [hℓ3, h]; exact (((Prog.lenBoundT_mono bpCompC hv) j).trans (b2 j)).trans
        (le_max_right _ _)
  have c30 : ℓ3 0 ≤ m + allG + S0 := by
    rw [hℓ3, show (0 : Fin 72) = e64 0 from rfl, embedF_apply_self]
    exact ((Prog.lenBoundT_mono bpCompC hv) 0).trans (b2 0)
  have c3' : ∀ t, ℓ3 t ≤ max S (frontBA m) := fun t => by
    have := c3 t
    have h1 : max S m ≤ max S (frontBA m) := max_le_max le_rfl (by unfold frontBA; omega)
    have h2 : m + allG + S0 ≤ max S (frontBA m) :=
      le_trans (by unfold frontBA; omega) (le_max_right _ _)
    exact this.trans (max_le h1 h2)
  refine ⟨?_, fun t => ?_⟩
  · show Prog.timeBoundT (cutPn m) ℓ + (timeBoundT (clearL clr63) ℓ1 +
      (Prog.timeBoundT bpCompC (fun j => ℓ2 (e64 j)) + Prog.timeBoundT (.prim (.cons 0 true)) ℓ3))
      ≤ _
    have t3 := (Prog.timeBoundT_mono bpCompC hv).trans b1
    have t4 : Prog.timeBoundT (.prim (.cons 0 true)) ℓ3 ≤ 2 * (max S (frontBA m) + 1) + 3 := by
      have h := (ph_prim (Prim.cons (0 : Fin 72) true) (fun _ => max S (frontBA m)) ℓ3 c3').1
      have := supB_const_le (k := 72) (max S (frontBA m))
      exact h.trans (by omega)
    unfold compBT
    exact Nat.add_le_add tc (Nat.add_le_add hc.1 (Nat.add_le_add t3 t4))
  · show (Prim.cons (0 : Fin 72) true).lenT ℓ3 t ≤ _
    simp only [Prim.lenT, Function.update_apply, βc]
    split_ifs with h
    · subst h; omega
    · exact c3' t

/-- The two-level bound: `a` on tape `0`, `b` elsewhere. -/
def γ (a b : ℕ) : Fin 72 → ℕ := fun t => if t = 0 then a else b

theorem supB_γ (a b : ℕ) : supB (γ a b) ≤ max a b :=
  supB_le_of fun t => by simp only [γ]; split_ifs <;> omega

/-- The time of the authorization program on words of at most `B` bits. -/
def authBT (B : ℕ) : ℕ := BpComp.authN B * (2 * B + 5)

theorem ph_bit0P {a B0 B : ℕ} (hB : B0 + 2 ^ 49 ≤ B) :
    Ph bit0P (fun t => if t ∈ clr63 then 0 else γ a B0 t)
      (129 * (2 * (max a B0 + 129) + 3) + authBT B) (γ a B) := by
  have hβ : supB (fun t => if t ∈ clr63 then 0 else γ a B0 t) ≤ max a B0 :=
    supB_le_of fun t => by simp only [γ]; split_ifs <;> omega
  have h1 := ph_putW (71 : Fin 72) (List.replicate 128 false)
    (fun t => if t ∈ clr63 then 0 else γ a B0 t)
  simp only [List.length_replicate] at h1
  have hin : (fun j => Function.update (fun t => if t ∈ clr63 then 0 else γ a B0 t) 71
      ((if (71 : Fin 72) ∈ clr63 then 0 else γ a B0 71) + 128) (eA j)) ≤ BpComp.βA B := by
    intro j
    fin_cases j <;> simp (config := { decide := true }) [eA, γ, mem_clr63, BpComp.βA] <;> omega
  have h2 : Ph (prog BpComp.authBPC) (fun j => Function.update (fun t => if t ∈ clr63 then 0 else
      γ a B0 t) 71 ((if (71 : Fin 72) ∈ clr63 then 0 else γ a B0 71) + 128) (eA j))
      (authBT B) (BpComp.βA B) := fun ℓ hℓ => by
    have := BpComp.ta_authBP (S := B) (by omega) ℓ (hℓ.trans hin)
    exact ⟨by rw [timeBoundT_prog]; exact this.1, this.2⟩
  refine (h1.mono le_rfl (Nat.mul_le_mul_left _ (by omega)) le_rfl).seq
    ((ph_frame eA h2).mono le_rfl le_rfl ?_)
  intro t
  rcases embedF_cases eA _ (BpComp.βA B) t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h]
    simp only [Function.update_apply, γ]
    split_ifs <;> omega
  · rw [h]
    have h0 : eA j ≠ 0 := by fin_cases j <;> decide
    simp only [γ, h0, if_false]
    exact (BpComp.βA_le (by omega) j).trans le_rfl

theorem ph_fixP (a B : ℕ) :
    Ph fixP (γ a B) (4 * (2 * (max (a + 2) B + 1) + 3) + 1) (γ (a + 2) B) := by
  have hs : ∀ c, supB (γ c B) ≤ max (a + 2) B → 2 * (supB (γ c B) + 1) + 3 ≤
      2 * (max (a + 2) B + 1) + 3 := fun c h => by omega
  have p1 := ph_prim (Prim.tail (0 : Fin 72)) (γ a B)
  have p2 := ph_prim (Prim.cons (0 : Fin 72) false) (γ a B)
  have p3 := ph_prim (Prim.cons (0 : Fin 72) true) (γ a B)
  have p4 := ph_prim (Prim.cons (0 : Fin 72) true) (γ (a + 1) B)
  have p5 := ph_prim (Prim.clear (70 : Fin 72)) (γ (a + 2) B)
  have e1 : (Prim.tail (0 : Fin 72)).lenT (γ a B) ≤ γ a B := fun t => by
    simp only [Prim.lenT, Function.update_apply, γ]; split_ifs <;> omega
  have e2 : ∀ b, (Prim.cons (0 : Fin 72) b).lenT (γ a B) ≤ γ (a + 1) B := fun b t => by
    simp only [Prim.lenT, Function.update_apply, γ]; split_ifs <;> omega
  have e3 : (Prim.cons (0 : Fin 72) true).lenT (γ (a + 1) B) ≤ γ (a + 2) B := fun t => by
    simp only [Prim.lenT, Function.update_apply, γ]; split_ifs <;> omega
  have e4 : (Prim.clear (70 : Fin 72)).lenT (γ (a + 2) B) ≤ γ (a + 2) B := fun t => by
    simp only [Prim.lenT, Function.update_apply, γ]; split_ifs <;> omega
  have q1 := p1.mono le_rfl le_rfl e1
  have q2 := ph_ifBit' (70 : Fin 72) (p2.mono le_rfl le_rfl (e2 false))
    (p3.mono le_rfl le_rfl (e2 true))
  have q3 := p4.mono le_rfl le_rfl e3
  have q4 := p5.mono le_rfl le_rfl e4
  have s1 := supB_γ a B
  have s2 := supB_γ (a + 1) B
  have s3 := supB_γ (a + 2) B
  refine (q1.seq ((q2.mono le_rfl le_rfl (fun t => by simp)).seq (q3.seq q4))).mono le_rfl ?_ le_rfl
  have := hs a (s1.trans (by omega))
  have := hs (a + 1) (s2.trans (by omega))
  have := hs (a + 2) (s3.trans (by omega))
  simp only [max_self]
  omega

/-- The time of the branch of a word of `m` bits. -/
def validBT (m S : ℕ) : ℕ :=
  (2 * (S + 1) + 3) + ((2 * (S + 1) + 3) + (compBT m S + (clr72T (max S (frontBA m)) +
    ((129 * (2 * (max S (frontBA m) + 129) + 3) + authBT (BB m S)) +
      (4 * (2 * (BB m S + 1) + 3) + 1)))))

theorem ph_validB (m S : ℕ) : Ph (validB m) (fun _ => S) (validBT m S) (βo m S) := by
  set a := m + allG + S0 + 1
  set B0 := max S (frontBA m)
  have haB : a + 2 ≤ B0 := le_trans (by unfold frontBA; omega) (le_max_right _ _)
  have hS1 : supB (fun _ : Fin 72 => S) ≤ S := supB_const_le S
  have h1 : Ph (prog (.prim (.clear (64 : Fin 72)))) (fun _ => S) (2 * (S + 1) + 3)
      (fun _ => S) := (ph_prim _ _).mono le_rfl (by omega) (fun t => by
        simp only [Prim.lenT, Function.update_apply]; split_ifs <;> omega)
  have h2 : Ph (prog (.prim (.copy (70 : Fin 72) 0))) (fun _ => S) (2 * (S + 1) + 3)
      (fun _ => S) := (ph_prim _ _).mono le_rfl (by omega) (fun t => by
        simp only [Prim.lenT, Function.update_apply]; split_ifs <;> omega)
  have h3 := ph_comp m S
  have hcl := (ph_clearL clr63 (γ a B0)).mono (fun t => le_rfl) (show _ ≤ clr72T B0 by
    have hsup : supB (γ a B0) ≤ B0 := (supB_γ a B0).trans (max_le (by omega) le_rfl)
    have := Nat.mul_le_mul length_clr63 (show 2 * (supB (γ a B0) + 1) + 3 ≤ 2 * (B0 + 1) + 3 by
      omega)
    unfold clr72T; omega) le_rfl
  have h4 := ph_bit0P (a := a) (B0 := B0) (B := BB m S) (by unfold BB; omega)
  have h5 := ph_fixP a (BB m S)
  have hmax1 : max a B0 = B0 := max_eq_right (by omega)
  have hmax2 : max (a + 2) (BB m S) = BB m S := max_eq_right (by unfold BB; omega)
  rw [hmax1] at h4
  rw [hmax2] at h5
  have hc : Ph (compBlk m) (fun _ => S) (compBT m S) (γ a B0) := h3.mono le_rfl le_rfl
    (fun t => le_rfl)
  refine (h1.seq (h2.seq (hc.seq (hcl.seq (h4.seq h5))))).mono le_rfl (le_of_eq rfl) ?_
  intro t
  simp only [γ, βo]
  split_ifs <;> simp only [frontBA, a, BB] <;> omega

/-- The time of the dummy branch. -/
def dumBT (S : ℕ) : ℕ := (2 * (S + 1) + 3) + ((2 * (S + 1) + 3) + (2 * (S + 1) + 3))

theorem ph_dumBP (m S : ℕ) : Ph dumBP (fun _ => S) (dumBT S) (βo m S) := by
  have h1 := ph_prim (Prim.clear (64 : Fin 72)) (fun _ => S)
  have h2 := ph_prim (Prim.clear (0 : Fin 72)) ((Prim.clear (64 : Fin 72)).lenT fun _ => S)
  have h3 := ph_prim (Prim.snoc (0 : Fin 72) false)
    ((Prim.clear (0 : Fin 72)).lenT ((Prim.clear (64 : Fin 72)).lenT fun _ => S))
  have hs : ∀ β : Fin 72 → ℕ, (∀ t, β t ≤ S) → 2 * (supB β + 1) + 3 ≤ 2 * (S + 1) + 3 :=
    fun β hβ => by have := supB_le_of hβ; omega
  refine (h1.seq (h2.seq h3)).mono le_rfl ?_ ?_
  · unfold dumBT
    have a1 := hs (fun _ => S) (fun _ => le_rfl)
    have a2 := hs ((Prim.clear (64 : Fin 72)).lenT fun _ => S) (fun t => by
      simp only [Prim.lenT, Function.update_apply]; split_ifs <;> omega)
    have a3 := hs ((Prim.clear (0 : Fin 72)).lenT ((Prim.clear (64 : Fin 72)).lenT fun _ => S))
      (fun t => by simp only [Prim.lenT, Function.update_apply]; split_ifs <;> omega)
    omega
  · intro t
    simp only [Prim.lenT, Function.update_apply, βo, BB]
    have := frontBA_pos m
    split_ifs <;> omega

/-- The time of the length test from tapes below `S`. -/
def lenEqBT (m S : ℕ) : ℕ := (12 * m + 6 * S + 120) * (2 * S + 5)

/-- The time of the short branch. -/
def shortBT (m S : ℕ) : ℕ :=
  (2 * (S + 1) + 3) + (lenEqBT m S + (max (validBT m S) (dumBT S) + 1))

theorem ph_shortB {m S : ℕ} (hS : m ≤ S) (h1S : 1 ≤ S) :
    Ph (shortB m) (fun _ => S) (shortBT m S) (βo m S) := by
  have hl : Prog.UBP (Prog.lenEqP m) S (lenEqBT m S) S := fun ℓ hℓ =>
    Prog.lenEqP_bounds m hS h1S ℓ hℓ
  have h1 := ph_of_ub (β := fun _ : Fin 72 => S) (fun _ => le_rfl) (ub_clear 64 S)
  have h2 := ph_of_ub (β := fun _ : Fin 72 => S) (fun _ => le_rfl)
    ((ub_frame_ubp eEq hl).mono le_rfl (max_self S).le)
  have h3 := ph_ifBit' (64 : Fin 72) (ph_validB m S) (ph_dumBP m S)
  exact h1.seq (h2.seq (h3.mono le_rfl le_rfl (fun t => by simp)))

/-- `S`: the bound in the short branch. -/
def SB (m T : ℕ) : ℕ := max (T + 1) m

/-- **The time of the front end** on queries of at most `T` bits. -/
def frontBTn (n m T : ℕ) : ℕ :=
  Prog.leT n T + (max (2 * (T + 1 + 1) + 3) (shortBT m (SB m T)) + 1) +
    clr72T (BB m (SB m T))

/-- **The cost of the front end**: the output bound `frontBA m` does not depend on the input
bound `T`. -/
theorem ph_frontBPn (n m T : ℕ) :
    Ph (frontBPn n m) (io2 (R := 70) T 0 0) (frontBTn n m T) (io2 (R := 70) (frontBA m) 0 0) := by
  have hTS : T + 1 ≤ SB m T := le_max_left _ _
  have hSb : m ≤ SB m T := le_max_right _ _
  have h1 := ph_of_ub (β := io2 (R := 70) T 0 0) (fun i => by simp only [io2]; split_ifs <;> omega)
    ((ub_frame_ubp eLe (Prog.ubp_leP n T)).mono le_rfl (show max T (T + 1) ≤ T + 1 by omega))
  have hlong := ph_prim (Prim.clear (0 : Fin 72)) (fun _ => T + 1)
  have hshort := (ph_shortB hSb (by omega)).mono (fun _ => hTS) le_rfl le_rfl
  have h2 := ph_ifBlank' (64 : Fin 72) hlong hshort
  have h2' := h2.mono le_rfl le_rfl (show _ ≤ βo m (SB m T) from fun t => by
    simp only [Prim.lenT, Function.update_apply, βo, BB]
    split_ifs with h0 <;> omega)
  have hc := ph_clearL clr71 (βo m (SB m T))
  have h := h1.seq (h2'.seq hc)
  have hsup : supB (βo m (SB m T)) ≤ BB m (SB m T) :=
    supB_le_of fun t => by simp only [βo, BB]; split_ifs <;> omega
  refine h.mono le_rfl ?_ ?_
  · have hsup1 : supB (fun _ : Fin 72 => T + 1) ≤ T + 1 := supB_const_le _
    have := Nat.mul_le_mul length_clr71 (show 2 * (supB (βo m (SB m T)) + 1) + 3 ≤
      2 * (BB m (SB m T) + 1) + 3 by omega)
    have hl : 2 * (supB (fun _ : Fin 72 => T + 1) + 1) + 3 ≤ 2 * (T + 1 + 1) + 3 := by omega
    have e1 : max (2 * (supB (fun _ : Fin 72 => T + 1) + 1) + 3) (shortBT m (SB m T)) ≤
        max (2 * (T + 1 + 1) + 3) (shortBT m (SB m T)) := max_le_max hl le_rfl
    have e3 : 2 * (supB (βo m (SB m T)) + 1) + 3 ≤ 2 * (BB m (SB m T) + 1) + 3 := by
      omega
    unfold frontBTn clr72T
    linarith
  · intro t
    simp only [mem_clr71, io2, βo]
    by_cases h0 : t = 0
    · subst h0; simp
    · have : t.val ≠ 0 := fun e => h0 (Fin.ext e)
      simp [h0, this]

/-! ### The size -/

theorem size_clearL72 : ∀ l : List (Fin 72), (clearL l).size ≤ 60 * l.length + 60
  | [] => Prog.size_prim_le' _
  | t :: l => by
    have := size_clearL72 l
    have := Prog.size_prim_le' (Prim.clear t)
    show Prog.size _ + (clearL l).size ≤ _
    simp only [List.length_cons]; omega

theorem size_putW72 (o : Fin 72) : ∀ w : List Bool,
    Prog.size (SigabaNeo.Tape.Prog.putW o w) ≤ 60 * (w.length + 1)
  | [] => Prog.size_prim_le' _
  | b :: w => by
    have := size_putW72 o w
    have := Prog.size_prim_le' (Prim.cons o b)
    show Prog.size _ + Prog.size _ ≤ _
    simp only [List.length_cons]; omega

theorem size_cutPn (m : ℕ) : Prog.size (cutPn m) ≤ 60 * (m + 5) := by
  have := size_putW72 69 (List.replicate m false)
  rw [List.length_replicate] at this
  have := Prog.size_prim_le' (Prim.carry Prog.takeOp (69 : Fin 72) 0)
  have := Prog.size_prim_le' (Prim.clear (0 : Fin 72))
  have := Prog.size_prim_le' (Prim.copy (0 : Fin 72) 69)
  have := Prog.size_prim_le' (Prim.clear (69 : Fin 72))
  show Prog.size _ + (Prog.size _ + (Prog.size _ + (Prog.size _ + Prog.size _))) ≤ _
  omega

theorem size_tailsP' {k : ℕ} (i : Fin k) : ∀ n, (SigabaNeo.Tape.Prog.tailsP i n).size = 36 * (n + 1)
  | 0 => by simp [SigabaNeo.Tape.Prog.tailsP, Prog.size, Prim.pad]
  | n + 1 => by
    rw [SigabaNeo.Tape.Prog.tailsP, Prog.size, size_tailsP' i n]
    simp [Prog.size, Prim.pad]; ring

theorem size_leP' (n : ℕ) : (SigabaNeo.Tape.Prog.leP n).size ≤ 36 * n + 400 := by
  simp only [SigabaNeo.Tape.Prog.leP, Prog.size, Prim.pad, size_tailsP']; omega

/-- **The states of the front end**: `36 n + 60 m + 500 log₂ m + 2^27 + 2^19` at most. -/
theorem size_frontBPn_le (n m : ℕ) :
    (frontBPn n m).size ≤ 36 * n + 60 * m + 500 * Nat.log2 m + 2 ^ 27 + 2 ^ 20 := by
  have h1 := size_leP' n
  have h2 := Prog.size_lenEqP m
  have h3 := BpComp.size_bpCompC
  have h0 := size_cutPn m
  have h4 := size_clearL72 clr63
  have h5 := size_clearL72 clr71
  have l4 := length_clr63
  have l5 := length_clr71
  have hp : ∀ q : Prim 72, (Prog.prim q).size ≤ 60 := fun q => Prog.size_prim_le' q
  have := hp (.clear 0); have := hp (.clear 64); have := hp (.cons 0 true)
  have := hp (.snoc 0 false); have := hp (.copy 70 0); have := hp (.tail 0)
  have := hp (.cons 0 false); have := hp (.clear 70)
  have h6 := BpComp.size_authBPC
  have h7 : (putW (71 : Fin 72) (List.replicate 128 false)).size ≤ 60 * 129 := by
    have : ∀ w : List Bool, (putW (71 : Fin 72) w).size ≤ 60 * (w.length + 1) := by
      intro w; induction w with
      | nil => exact Prog.size_prim_le' _
      | cons b w ih =>
        have := Prog.size_prim_le' (Prim.snoc (71 : Fin 72) b)
        show Prog.size _ + (putW 71 w).size ≤ _
        simp only [List.length_cons]; omega
    simpa using this (List.replicate 128 false)
  simp only [frontBPn, shortB, validB, compBlk, bit0P, fixP, dumBP, size_seq, size_frame,
    size_prog, size_ifBlank, size_ifBit] at *
  omega

theorem size_frontBP_le (n : ℕ) : (frontBP n).size ≤ 36 * n + 2 ^ 56 := by
  have h := size_frontBPn_le n bpLen
  have hb := bpLen_le
  have hl : Nat.log2 bpLen < 50 := (Nat.log2_lt (by unfold bpLen; norm_num)).mpr
    (lt_of_le_of_lt hb (by norm_num))
  have : 60 * 2 ^ 49 + 500 * 50 + 2 ^ 27 + 2 ^ 20 ≤ (2 : ℕ) ^ 56 := by norm_num
  exact h.trans (by omega)

/-! ### The interface -/

/-- **The front end meets the interface** for any guard `n` and word length `m`. -/
theorem frontSpecG_frontBPn (n m : ℕ) :
    FrontSpecG (frontBPn n m) n (fun C => C.length = m) bwBP0 (frontBTn n m) (fun _ => frontBA m)
      (36 * n + 60 * m + 500 * Nat.log2 m + 2 ^ 27 + 2 ^ 20) where
  wf := wf_frontBPn n m
  coinFree := coinFree_frontBPn n m
  law := law_frontBPn n m
  ph := ph_frontBPn n m
  size := size_frontBPn_le n m

/-- **The front end for branching programs meets the interface** (`ValidC C := C.length = bpLen`,
`blockWord 512 := bwBP` at the switch). -/
theorem frontSpecG_frontBP (n : ℕ) :
    FrontSpecG (frontBP n) n (fun C => C.length = bpLen) bwBP0 (frontBTn n bpLen)
      (fun _ => frontBA bpLen) (36 * n + 2 ^ 56) :=
  { frontSpecG_frontBPn n bpLen with size := size_frontBP_le n }

/-! ### Closed forms -/

theorem frontBA_le {m : ℕ} (hm : m ≤ 2 ^ 49) : frontBA m ≤ 2 ^ 63 := by
  have h := BpComp.allG_le
  unfold frontBA; omega

theorem allN_Uc_mono {m : ℕ} (hm : m ≤ BpComp.bpLenA) :
    allN * Uc allG m ≤ 2 ^ 126 :=
  (Nat.mul_le_mul_left _ (by unfold Uc; omega)).trans BpComp.allN_Uc_le

theorem authN_lin (B : ℕ) : BpComp.authN B = BpComp.authN 0 + 6 * B := by
  unfold BpComp.authN; ring

theorem authN_zero_le : BpComp.authN 0 ≤ 2 ^ 57 := by
  unfold BpComp.authN; decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- **The time of the front end in one number**: for a guard `n`, a word length `m ≤ bpLenA`
and queries of `T` bits, all below `X ≥ 2^64`, at most `2^8 · X^2` steps (the length test and the
authorization program at `attr0` are quadratic in their tapes; the compiler costs
`2^126 ≤ X^2`). -/
theorem frontBTn_le {n m T X : ℕ} (hm : m ≤ BpComp.bpLenA) (hm49 : m ≤ 2 ^ 49) (hn : n ≤ X)
    (hT : T + 1 ≤ X) (hX : 2 ^ 64 ≤ X) : frontBTn n m T ≤ 2 ^ 8 * X ^ 2 := by
  have hA := frontBA_le hm49
  have hc := allN_Uc_mono hm
  have h49 : (2 : ℕ) ^ 49 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h57 : (2 : ℕ) ^ 57 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h63 : (2 : ℕ) ^ 63 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hX2 : (2 : ℕ) ^ 126 ≤ X ^ 2 := by
    calc (2 : ℕ) ^ 126 ≤ (2 ^ 64) ^ 2 := by norm_num
      _ ≤ X ^ 2 := Nat.pow_le_pow_left hX 2
  have hmX : m ≤ X := by omega
  have hS : SB m T ≤ X := max_le hT hmX
  set S := SB m T
  have hB0 : max S (frontBA m) ≤ X := max_le hS (by omega)
  have hBB : BB m S ≤ 2 * X := by unfold BB; omega
  have hSb : max S m ≤ X := max_le hS hmX
  have hX1 : 1 ≤ X := le_trans (by norm_num) hX
  have hXX : X ≤ X ^ 2 := by nlinarith
  unfold frontBTn
  have p1 : Prog.leT n T ≤ 3 * X ^ 2 := by
    unfold Prog.leT
    have : (n + 5) * (2 * (T + 2) + 3) ≤ (X + 5) * (2 * X + 5) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have pc : ∀ M, M ≤ 2 * X → clr72T M ≤ 2 * X ^ 2 := fun M hM => by
    unfold clr72T; nlinarith
  have p2 : cutBT m S ≤ 2 * X ^ 2 := by
    unfold cutBT
    have : (m + 5) * (2 * (max S m + (m + 5)) + 5) ≤ (X + 5) * (2 * (X + (X + 5)) + 5) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have p3 : lenEqBT m S ≤ 18 * X ^ 2 := by
    unfold lenEqBT
    have : (12 * m + 6 * S + 120) * (2 * S + 5) ≤ (18 * X + 120) * (2 * X + 5) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have pa : authBT (BB m S) ≤ 65 * X ^ 2 := by
    unfold authBT
    rw [authN_lin]
    have h1 : BpComp.authN 0 + 6 * BB m S ≤ 13 * X := by have := authN_zero_le; omega
    have h2 : 2 * BB m S + 5 ≤ 5 * X := by omega
    calc (BpComp.authN 0 + 6 * BB m S) * (2 * BB m S + 5) ≤ (13 * X) * (5 * X) :=
          Nat.mul_le_mul h1 h2
      _ = 65 * X ^ 2 := by ring
  have p4 : validBT m S ≤ 75 * X ^ 2 := by
    unfold validBT compBT
    have c1 := pc _ (le_trans hSb (by omega))
    have c2 := pc _ (le_trans hB0 (by omega))
    have c3 : 129 * (2 * (max S (frontBA m) + 129) + 3) ≤ 300 * X := by omega
    have c4 : 4 * (2 * (BB m S + 1) + 3) + 1 ≤ 30 * X := by omega
    have c5 : 2 * (S + 1) + 3 ≤ 3 * X := by omega
    have c6 : 2 * (max S (frontBA m) + 1) + 3 ≤ 3 * X := by omega
    have c7 : 400 * X ≤ X ^ 2 := by nlinarith
    linarith
  have p5 : dumBT S ≤ X ^ 2 := by unfold dumBT; nlinarith
  have p6 : shortBT m S ≤ 95 * X ^ 2 := by
    unfold shortBT
    have : max (validBT m S) (dumBT S) ≤ 75 * X ^ 2 := max_le p4 (by omega)
    nlinarith
  have q1 := pc _ hBB
  have q2 : max (2 * (T + 1 + 1) + 3) (shortBT m S) ≤ 95 * X ^ 2 := max_le (by nlinarith) p6
  have : (2 : ℕ) ^ 8 * X ^ 2 = 256 * X ^ 2 := by norm_num
  linarith

end AdvancedEncryption.DualUse.Prog
