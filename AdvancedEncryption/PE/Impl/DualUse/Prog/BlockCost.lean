import PE.Impl.DualUse.Prog.BfXCost
import PE.Impl.DualUse.Prog.PostCost
import PE.Impl.DualUse.Prog.KeyPTimeT

/-!
# The time of the blocks `bfX` and `cfX`

From a store with at most `a` bits on tape `0` and at most `LF` bits on tape `1` (any bounds
elsewhere: the blocks clear them first), with a `W_f` block bounded at `wfIn Lw LF` by `Tw` steps
and `Gw` bits, and the crafted data below `Lw`:

* `ph_bfX`: `bfX` takes at most `clear + preTX X + Tw + postBT …` steps, every tape below `Gw + …`;
* `ph_cfX`: the same for `cfX`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

theorem io2_eLo_nat {m : ℕ} [NeZero m] {hm : m + 1 ≤ 256} (a b : ℕ) :
    (fun j => io2 (R := 254) a b 0 (eLo m hm j)) = Function.update (fun _ => 0) 0 a := by
  funext j
  simp only [io2, eLo_val, Function.update_apply]
  by_cases h : j.val = 0
  · have : j = 0 := Fin.ext (by simp [h])
    simp [h, this]
  · have : j ≠ 0 := fun e => h (by rw [e]; simp)
    simp [h, this]

theorem embedF_eLo_nat {m : ℕ} [NeZero m] {hm : m + 1 ≤ 256} (a b a' : ℕ) :
    embedF (eLo m hm) (io2 (R := 254) a b 0) (Function.update (fun _ => 0) 0 a') =
      io2 (R := 254) a' b 0 := by
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · simp only [io2, eLo_val, Function.update_apply]
    by_cases h : j.val = 0
    · have : j = 0 := Fin.ext (by simp [h])
      simp [h, this]
    · have : j ≠ 0 := fun e => h (by rw [e]; simp)
      simp [h, this]
  · have h0 : t.val ≠ 0 := fun h => ht 0 (Fin.ext (by rw [eLo_val]; simp [h]))
    simp only [io2, h0, if_false]

theorem vec18_eq (a : ℕ) : (![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 18 → ℕ) =
    Function.update (fun _ => 0) 0 a := by
  funext j; fin_cases j <;> simp

theorem vec21_eq (a : ℕ) :
    (![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 21 → ℕ) =
      Function.update (fun _ => 0) 0 a := by
  funext j; fin_cases j <;> simp

theorem length_clr01_le : clr01.length ≤ 256 :=
  (List.length_filter_le _ _).trans (by rw [List.length_finRange])

/-- The clearing phase of the blocks. -/
theorem ph_clr01 {β : Fin 256 → ℕ} {a LF Mβ : ℕ} (h0 : β 0 ≤ a) (h1 : β 1 ≤ LF)
    (hβ : ∀ i, β i ≤ Mβ) :
    Ph (clearL clr01) β (256 * (2 * (Mβ + 1) + 3) + (2 * (Mβ + 1) + 3)) (io2 (R := 254) a LF 0) := by
  refine (ph_clearL clr01 β).mono le_rfl ?_ ?_
  · have hs := supB_le_of hβ
    have := Nat.mul_le_mul length_clr01_le (show 2 * (supB β + 1) + 3 ≤ 2 * (Mβ + 1) + 3 by omega)
    omega
  · intro t
    by_cases ht0 : t = 0
    · subst ht0; simp [mem_clr01, io2, h0]
    · by_cases ht1 : t = 1
      · subst ht1; simp [mem_clr01, io2, h1]
      · have h0' : t.val ≠ 0 := fun e => ht0 (Fin.ext e)
        have h1' : t.val ≠ 1 := fun e => ht1 (Fin.ext e)
        simp [mem_clr01, ht0, ht1, io2, h0', h1']

/-- A `W_f` block bounded at its input. -/
theorem ph_wf {wfB : XProg 256} {Lw LF Tw Gw L' : ℕ} (hwT : timeBoundT wfB (wfIn Lw LF) ≤ Tw)
    (hwL : ∀ i, lenBoundT wfB (wfIn Lw LF) i ≤ Gw) (hL : L' ≤ Lw) :
    Ph wfB (io2 (R := 254) L' LF 0) Tw (fun _ => Gw) := fun ℓ hℓ => by
  have hin : ℓ ≤ wfIn Lw LF := fun i => (hℓ i).trans (io2_mono hL le_rfl i)
  exact ⟨(timeBoundT_mono wfB hin).trans hwT, fun i => (lenBoundT_mono wfB hin i).trans (hwL i)⟩

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- **The time of `bfX`.** -/
theorem ph_bfX {wfB : XProg 256} {Lw LF Tw Gw a Mβ X : ℕ}
    (hwT : timeBoundT wfB (wfIn Lw LF) ≤ Tw) (hwL : ∀ i, lenBoundT wfB (wfIn Lw LF) i ≤ Gw)
    (hX : a + 3 + lenPK hk c + lenT N K k + nJ (N := N) hk * DualUse.rowL N K k +
      c.d * (N * K) + 10 * (c.d * DualUse.rowL N K k) +
      nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) + 10 * (2 * DualUse.rowL N K k) + 10 +
      lenZ c + DualUse.rowL N K k + (lenZ c - lenT N K k) + 10 ≤ X)
    (hoB : offBk c ≤ X) (hRM : 10 * (c.d * DualUse.rowL N K k) ≤ X)
    (hPS : 10 * (2 * DualUse.rowL N K k) ≤ X) (hnT : nJ (N := N) hk ≤ X)
    (hLw : a + 1 + lenPK hk c + c.d * (N * K) + 10 * (c.d * DualUse.rowL N K k) +
      nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) + 10 * (2 * DualUse.rowL N K k) + 10 ≤ Lw)
    (hG : ∀ x ∈ postTmpl N K k, x.2 ≤ Gw)
    {β : Fin 256 → ℕ} (h0 : β 0 ≤ a) (h1 : β 1 ≤ LF) (hβ : ∀ i, β i ≤ Mβ) :
    Ph (bfX hk c wfB) β (256 * (2 * (Mβ + 1) + 3) + (2 * (Mβ + 1) + 3) + (preTX X + (Tw +
      postBT (lenPK hk c) (lenT N K k) (offWk hk c) (lenZ c) N K k Gw)))
      (fun _ => Gw + 1 + lenPK hk c + 1 + lenT N K k + 1 + lenPK hk c + 1 + lenT N K k) := by
  have p1 := ph_clr01 h0 h1 hβ
  have p2 : Ph (preB hk c) (io2 (R := 254) a LF 0) (preTX X) (io2 (R := 254)
      (a + 1 + lenPK hk c + c.d * (N * K) + 10 * (c.d * DualUse.rowL N K k) +
        nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) + 10 * (2 * DualUse.rowL N K k) + 10) LF 0) := by
    have h := ph_frame (eLo 18 eLo18) (β := io2 (R := 254) a LF 0) (T := preTX X)
      (p := preCoreB (lenPK hk c) (lenT N K k) (offBk c) (nJ (N := N) hk * DualUse.rowL N K k)
        (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk) (c.d * (N * K))
        (10 * (c.d * DualUse.rowL N K k)) (10 * (2 * DualUse.rowL N K k)) (lenZ c - lenT N K k))
      (by
        rw [io2_eLo_nat, ← vec18_eq]
        exact (ph_preCoreB _ _ _ _ _ _ _ _ _ _ _ a X hX hoB hRM hPS hnT).mono le_rfl le_rfl
          (le_of_eq (vec18_eq _)))
    rw [embedF_eLo_nat] at h
    exact h
  have p3 := ph_wf hwT hwL hLw
  have p4 : Ph (postB hk c) (fun _ => Gw)
      (postBT (lenPK hk c) (lenT N K k) (offWk hk c) (lenZ c) N K k Gw)
      (fun _ => Gw + 1 + lenPK hk c + 1 + lenT N K k + 1 + lenPK hk c + 1 + lenT N K k) :=
    ph_of_ub (fun _ => le_rfl) (ub_frameLe _ (ub_postCoreB _ _ _ _ _ _ _ _ hG) (by omega))
  exact p1.seq (p2.seq (p3.seq p4))

/-- **The time of `cfX`.** -/
theorem ph_cfX {wfB : XProg 256} {Lw LF Tw Gw a Mβ X : ℕ}
    (hwT : timeBoundT wfB (wfIn Lw LF) ≤ Tw) (hwL : ∀ i, lenBoundT wfB (wfIn Lw LF) i ≤ Gw)
    (hX : 2 * (a + 6 + lenPK hk c + lenKA hk c + N * K + 2 * lPsi (N := N) (K := K) hk +
      c.d * (N * K) + 10 * ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) +
      (lenZ c - (lenKA hk c + N * K)) + lenZ c + DualUse.rowL N K k +
      (c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k + lPsi (N := N) (K := K) hk + 10 +
      c.d * (N * K) + (lenZ c - (lenKA hk c + N * K)) + nJ (N := N) hk + 10) +
      lenCj (N := N) hk + nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) +
      lPsi (N := N) (K := K) hk + 10 ≤ X)
    (hoK : lenPK hk c + lenKA hk c + lenCj (N := N) hk ≤ X)
    (hoP : lenPK hk c + fixLen (keyEnc (N := N) (K := K) c) ≤ X)
    (hoJ : lenPK hk c + lenKA hk c ≤ X)
    (hLw : a + 1 + lenPK hk c + c.d * (N * K) +
      10 * ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) +
      nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) + lPsi (N := N) (K := K) hk + 10 ≤ Lw)
    (hG : ∀ x ∈ postTmplC N K k (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk), x.2 ≤ Gw)
    {β : Fin 256 → ℕ} (h0 : β 0 ≤ a) (h1 : β 1 ≤ LF) (hβ : ∀ i, β i ≤ Mβ) :
    Ph (cfX hk c wfB) β (256 * (2 * (Mβ + 1) + 3) + (2 * (Mβ + 1) + 3) + (preTCX X + (Tw +
      postCT (lenPK hk c) (lenKA hk c) (N * K) (offWk hk c)
        (nJ (N := N) hk * (lenZ c + DualUse.rowL N K k)) (lenZ c) N K k (lenZ c)
        (DualUse.rowL N K k) (nJ (N := N) hk) Gw)))
      (fun _ => postCG (lenPK hk c) (lenKA hk c) (N * K)
        (nJ (N := N) hk * (lenZ c + DualUse.rowL N K k)) N K k (nJ (N := N) hk)
        (DualUse.rowL N K k) Gw) := by
  have p1 := ph_clr01 h0 h1 hβ
  have p2 : Ph (preC hk c) (io2 (R := 254) a LF 0) (preTCX X) (io2 (R := 254)
      (a + 1 + lenPK hk c + c.d * (N * K) +
        10 * ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) +
        nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) + lPsi (N := N) (K := K) hk + 10) LF 0) := by
    have h := ph_frame (eLo 21 eLo21) (β := io2 (R := 254) a LF 0) (T := preTCX X)
      (p := preCoreC (lenPK hk c) (lenKA hk c) (lenPK hk c + lenKA hk c + lenCj (N := N) hk) (N * K)
        (lenPK hk c + fixLen (keyEnc (N := N) (K := K) c)) (lPsi (N := N) (K := K) hk)
        (lenPK hk c + lenKA hk c) (lenCj (N := N) hk) (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk)
        (c.d * (N * K)) ((c.d - 2) * DualUse.rowL N K k) (2 * DualUse.rowL N K k)
        (lenZ c - (lenKA hk c + N * K)))
      (by
        rw [io2_eLo_nat, ← vec21_eq]
        exact (ph_preCoreC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a X hX hoK hoP hoJ).mono le_rfl le_rfl
          (le_of_eq (vec21_eq _)))
    rw [embedF_eLo_nat] at h
    exact h
  have p3 := ph_wf hwT hwL hLw
  have p4 := ph_of_ub (β := fun _ => Gw) (fun _ => le_rfl)
    (ub_frameLe (eLo 64 eLo64) (ub_postCoreC (lenPK hk c) (lenKA hk c) (N * K) (offWk hk c)
      (nJ (N := N) hk * (lenZ c + DualUse.rowL N K k)) (lenZ c) N K k (lenZ c)
      (DualUse.rowL N K k) (nJ (N := N) hk) Gw hG) (by simp only [postCG]; omega))
  exact p1.seq (p2.seq (p3.seq p4))

end AdvancedEncryption.DualUse.Prog
