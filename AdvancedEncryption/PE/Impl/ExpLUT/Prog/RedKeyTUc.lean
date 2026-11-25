import PE.Impl.ExpLUT.Prog.RedKeyTPub
/-!
# Module 9: the clock of the `u` routine `uC` (cap `M`, generic)

`uC = ringOneC ; bRowC ; 11 := 17 ; clr 12 ; clr 13 ; uRowsC ; … ; decRowsC ; 20 := rDq`.
The rows (`rktURowC`, `rktURowsC`) use F3's generic recomposition/automorphism/inner-product
certificates (counter cap `M`): `2^22` rows of `≈ 2^408` steps at `M = 2^150`, affordable.
The accumulators `rIa` are reset to the zero word before each use, so the appended words are
single ring words.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

/-- The registers one row of `uC` uses as scratch (widened to the cap). -/
def uScr : List (Fin 64) := [rQa, rQb, rQc, rQk, rIa, rQx, rQy, rUz]

def uRowT (M N K k : ℕ) : ℕ :=
  8 * (2 * M + 5) + (32 * K + 4) * (2 * M + 5) * 3 + (32 * k + 4) * (2 * M + 5) +
    recomposeTime M N K K + autQueueTime M N K K + innerProductTime M N K K + 2 * appendAllowance M

/-- **One row of `uC`**: `13 += N K`, `12 += N K`. -/
theorem rktURowC (M N K k : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hb : b rB1 = 1) (hz : b rZ = N * K) (hs : ∀ r ∈ uScr, b r = M)
    (hk : k ≤ M) (hKM : K ≤ M) (hub : b rUb + K * (N * K) ≤ M)
    (hg : b rUg + N * K ≤ M) (hp : b rUp + N * K ≤ M) :
    Cert (MVM.compile (uRowC K k)) (layout M N K b)
      (layout M N K (Function.update (Function.update b rUg (b rUg + N * K)) rUp
        (b rUp + N * K))) (uRowT M N K k) := by
  have sQa := hs rQa (by decide)
  have sQb := hs rQb (by decide)
  have sQc := hs rQc (by decide)
  have sQk := hs rQk (by decide)
  have sIa := hs rIa (by decide)
  have sQx := hs rQx (by decide)
  have sQy := hs rQy (by decide)
  have sUz := hs rUz (by decide)
  have hNK : N * K ≤ M := h.ring
  have tUz : b rUz ≤ M := by simpa using h.top (tR rUz)
  have tUb : b rUb ≤ M := by simpa using h.top (tR rUb)
  have t7 : b 7 ≤ M := by simpa using h.top (tR 7)
  -- gadget part
  have s1 := layout_copy M N K b h.top rQb rUz (by rw [sQb]; exact tUz)
  have s2 := layout_copy M N K b h.top rQa rUz (by rw [sQa]; exact tUz)
  let b1 := Function.update b rQc K
  have h1 : RingInputs M N K (layout M N K b1) := h.update_layout _ _ hKM
  have s3 := layout_nat_update M N K b h rQc rB1 (by decide) K hb hKM
  let b2 := Function.update b1 rIa (N * K)
  have h2 : RingInputs M N K (layout M N K b2) := h1.update_layout _ _ hNK
  have s4 := layout_copy_update M N K b1 h1.top rIa rZ
  have e4 : b1 rZ = N * K := by simp [b1, hz]
  rw [e4] at s4
  have k2 (r : Fin 64) (h1 : r ≠ rIa) (h2 : r ≠ rQc) : b2 r = b r := by
    simp only [b2, b1, Function.update_of_ne h1, Function.update_of_ne h2]
  have qa2 : QueueArithmeticCaps N K b2 :=
    ⟨by rw [k2 _ (by decide) (by decide), sQx]; exact hNK,
      by rw [k2 _ (by decide) (by decide), sQy]; exact hNK, by simp [b2],
      by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), sQx, hz]; exact hNK,
      by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), sQy, hz]; exact hNK⟩
  have s5 := compile_gadRecC M N K K b2 rUo h2 qa2 (by simp [b2, b1])
    (by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), sQy]; exact t7)
  have s6 := layout_copy M N K b2 h2.top rUz rQa
    (by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), sQa, sUz])
  have s7 := layout_append_uniform M N K b2 h2.top rUg rIa
    (by rw [k2 _ (by decide) (by decide)]; simpa [b2] using hg)
  let b3 := Function.update b2 rUg (b rUg + N * K)
  have e7 : Function.update b2 rUg (b2 rUg + b2 rIa) = b3 := by simp [b3, b2, b1]
  rw [e7] at s7
  have h3 : RingInputs M N K (layout M N K b3) := h2.update_layout _ _ hg
  -- public part
  let b4 := Function.update b3 rQa (b rUb)
  have h4 : RingInputs M N K (layout M N K b4) := h3.update_layout _ _ tUb
  have t1 := layout_copy_update M N K b3 h3.top rQa rUb
  have e1 : b3 rUb = b rUb := by simp [b3, b2, b1]
  rw [e1] at t1
  have t2 := layout_nat_update M N K b4 h4 rQc rB1 (by decide) K (by simp [b4, b3, b2, b1, hb]) hKM
  have e2 : Function.update b4 rQc K = b4 := by simp [b4, b3, b2, b1]
  rw [e2] at t2
  let b5 := Function.update b4 rQk k
  have h5 : RingInputs M N K (layout M N K b5) := h4.update_layout _ _ hk
  have t3 := layout_nat_update M N K b4 h4 rQk rB1 (by decide) k (by simp [b4, b3, b2, b1, hb]) hk
  have k5 (r : Fin 64) (h1 : r ≠ rQk) (h2 : r ≠ rQa) (h3 : r ≠ rUg) (h4 : r ≠ rIa)
      (h5 : r ≠ rQc) : b5 r = b r := by
    simp only [b5, b4, b3, b2, b1, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5]
  have t4 := compile_autQC M N K K b5 h5
    (by rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), sQx, hz]; exact hNK)
    (by rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), sQy]; exact hNK)
    (by simp [b5, b4, b3, b2, b1]) (by simpa [b5, b4] using hub)
  let b6 := Function.update b5 rQa (b rUb + K * (N * K))
  have e4' : Function.update b5 rQa (b5 rQa + K * (N * K)) = b6 := by simp [b6, b5, b4]
  rw [e4'] at t4
  have h6 : RingInputs M N K (layout M N K b6) := h5.update_layout _ _ hub
  have t5 := layout_nat_update M N K b6 h6 rQc rB1 (by decide) K
    (by simp [b6, b5, b4, b3, b2, b1, hb]) hKM
  have e5 : Function.update b6 rQc K = b6 := by simp [b6, b5, b4, b3, b2, b1]
  rw [e5] at t5
  have k6 (r : Fin 64) (h1 : r ≠ rQk) (h2 : r ≠ rQa) (h3 : r ≠ rUg) (h4 : r ≠ rIa)
      (h5 : r ≠ rQc) : b6 r = b r := by
    rw [← k5 r h1 h2 h3 h4 h5]; simp only [b6, Function.update_of_ne h2]
  have e6a : b6 rIa = N * K := by simp [b6, b5, b4, b3, b2]
  have t6 := layout_copy M N K b6 h6.top rIa rZ
    (by rw [e6a, k6 _ (by decide) (by decide) (by decide) (by decide) (by decide), hz])
  have qa6 : QueueArithmeticCaps N K b6 :=
    ⟨by rw [k6 _ (by decide) (by decide) (by decide) (by decide) (by decide), sQx]; exact hNK,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide) (by decide), sQy]; exact hNK,
      e6a.ge,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        k6 _ (by decide) (by decide) (by decide) (by decide) (by decide), sQx, hz]; exact hNK,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        k6 _ (by decide) (by decide) (by decide) (by decide) (by decide), sQy, hz]; exact hNK⟩
  have t7 := compile_ipC M N K K b6 h6 qa6 (by simp [b6, b5, b4, b3, b2, b1])
  have t8 := layout_append_uniform M N K b6 h6.top rUp rIa
    (by rw [e6a, k6 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hp)
  rw [e6a, k6 _ (by decide) (by decide) (by decide) (by decide) (by decide)] at t8
  rw [uRowC, uGadC, uPubC, gadRecC]
  rw [gadRecC] at s5
  refine ((s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))).seq
    (t1.seq (t2.seq (t3.seq (t4.seq (t5.seq (t6.seq (t7.seq t8)))))))).mono le_rfl ?_
    (by unfold uRowT; nlinarith)
  apply layout_mono
  intro r
  by_cases hrp : r = rUp
  · subst hrp; simp
  rw [Function.update_of_ne hrp, Function.update_of_ne hrp]
  by_cases hrg : r = rUg
  · subst hrg; simp [b6, b5, b4, b3]
  rw [Function.update_of_ne hrg]
  by_cases hra : r = rQa
  · subst hra; simp [b6, sQa]; exact hub
  by_cases hrk : r = rQk
  · subst hrk; simp [b6, b5, sQk]; exact hk
  by_cases hri : r = rIa
  · subst hri; simp [b6, b5, b4, b3, b2, sIa]; exact hNK
  by_cases hrc : r = rQc
  · subst hrc; simp [b6, b5, b4, b3, b2, b1, sQc]; exact hKM
  exact (k6 r hrk hra hrg hri hrc).le

/-- **The rows of `uC`**. -/
theorem rktURowsC (M N K E : ℕ) (e : ℕ → ℕ) : ∀ (is : List ℕ) (b : Fin 64 → ℕ),
    RingInputs M N K (layout M N K b) → b rB1 = 1 → b rZ = N * K → (∀ r ∈ uScr, b r = M) →
    (∀ i ∈ is, e i ≤ E) → E ≤ M → K ≤ M → b rUb + K * (N * K) ≤ M →
    b rUg + is.length * (N * K) ≤ M → b rUp + is.length * (N * K) ≤ M →
    Cert (MVM.compile (uRowsC K e is)) (layout M N K b)
      (layout M N K (Function.update (Function.update b rUg (b rUg + is.length * (N * K))) rUp
        (b rUp + is.length * (N * K)))) (is.length * uRowT M N K E + (2 * M + 5))
  | [], b, h, _, _, _, _, _, _, _, _, _ => by
    simpa [uRowsC] using (compile_nop (layout M N K b) M h.top).mono le_rfl le_rfl
      (show 2 * (M + 1) + 3 ≤ 2 * M + 5 by omega)
  | i :: is, b, h, hb, hz, hs, he, hE, hKM, hub, hg, hp => by
    have hNK := h.ring
    have hg' : b rUg + N * K + is.length * (N * K) ≤ M := by
      have := hg; simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at this; omega
    have hp' : b rUp + N * K + is.length * (N * K) ≤ M := by
      have := hp; simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at this; omega
    have p0 := rktURowC M N K (e i) b h hb hz hs ((he i (by simp)).trans hE) hKM hub
      (by omega) (by omega)
    let c := Function.update (Function.update b rUg (b rUg + N * K)) rUp (b rUp + N * K)
    have hc : RingInputs M N K (layout M N K c) :=
      (h.update_layout _ _ (by omega)).update_layout _ _ (by omega)
    have k (r : Fin 64) (h1 : r ≠ rUp) (h2 : r ≠ rUg) : c r = b r := by
      simp only [c, Function.update_of_ne h1, Function.update_of_ne h2]
    have cg : c rUg = b rUg + N * K := by
      simp only [c]; rw [Function.update_of_ne (by decide), Function.update_self]
    have cp' : c rUp = b rUp + N * K := by simp only [c, Function.update_self]
    have p1 := rktURowsC M N K E e is c hc (by rw [k _ (by decide) (by decide)]; exact hb)
      (by rw [k _ (by decide) (by decide)]; exact hz)
      (fun r hr => by
        rw [k r (by intro h; subst h; simp [uScr] at hr) (by intro h; subst h; simp [uScr] at hr)]
        exact hs r hr)
      (fun j hj => he j (by simp [hj])) hE hKM (by rw [k _ (by decide) (by decide)]; exact hub)
      (by rw [cg]; exact hg') (by rw [cp']; exact hp')
    have hout : Function.update (Function.update c rUg (c rUg + is.length * (N * K))) rUp
        (c rUp + is.length * (N * K)) = Function.update (Function.update b rUg
          (b rUg + (i :: is).length * (N * K))) rUp (b rUp + (i :: is).length * (N * K)) := by
      rw [cg, cp']
      have e1 : b rUg + N * K + is.length * (N * K) = b rUg + (i :: is).length * (N * K) := by
        simp only [List.length_cons]; ring
      have e2 : b rUp + N * K + is.length * (N * K) = b rUp + (i :: is).length * (N * K) := by
        simp only [List.length_cons]; ring
      rw [e1, e2]
      funext r
      by_cases h1 : r = rUp
      · subst h1; simp only [Function.update_self]
      by_cases h2 : r = rUg
      · subst h2; simp only [Function.update_of_ne h1, Function.update_self]
      simp only [c, Function.update_of_ne h1, Function.update_of_ne h2]
    rw [hout] at p1
    have hu : uRowT M N K (e i) ≤ uRowT M N K E := by
      have := he i (by simp)
      unfold uRowT; gcongr
    rw [uRowsC]
    exact (p0.seq p1).mono le_rfl le_rfl (by simp only [List.length_cons]; nlinarith)

/-! ### The standard envelope of the back end -/

/-- All registers at the cap `Mx`, except the templates `rB1`, `rZ`, the public key `14`, the
digits `17`, the corrected short part `18` and the key `19`. -/
def stdX (v14 v17 v18 v19 : ℕ) (r : Fin 64) : ℕ :=
  if r = rB1 then 1 else if r = rZ then Dc.N * Dc.K else if r = 14 then v14 else
    if r = 17 then v17 else if r = 18 then v18 else if r = 19 then v19 else Mx

section
variable (v14 v17 v18 v19 : ℕ)
theorem stdX_rB1 : stdX v14 v17 v18 v19 rB1 = 1 := by simp [stdX]
theorem stdX_rZ : stdX v14 v17 v18 v19 rZ = Dc.N * Dc.K := by simp [stdX]
theorem stdX_14 : stdX v14 v17 v18 v19 14 = v14 := by simp [stdX]
theorem stdX_17 : stdX v14 v17 v18 v19 17 = v17 := by simp [stdX]
theorem stdX_18 : stdX v14 v17 v18 v19 18 = v18 := by simp [stdX]
theorem stdX_19 : stdX v14 v17 v18 v19 19 = v19 := by simp [stdX]
theorem stdX_other (r : Fin 64) (h1 : r ≠ rB1) (h2 : r ≠ rZ) (h3 : r ≠ 14) (h5 : r ≠ 17)
    (h6 : r ≠ 18) (h4 : r ≠ 19) : stdX v14 v17 v18 v19 r = Mx := by
  simp [stdX, h1, h2, h3, h4, h5, h6]
end

theorem stdX_inputs (v14 v17 v18 v19 : ℕ) (h14 : v14 ≤ Mx) (h17 : v17 ≤ Mx) (h18 : v18 ≤ Mx)
    (h19 : v19 ≤ Mx) : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K (stdX v14 v17 v18 v19)) := by
  have hNK : Dc.N * Dc.K ≤ Mx := by rw [rkNK]; norm_num
  apply layout_inputs
  · intro r; unfold stdX; split_ifs
    · norm_num
    · exact hNK
    · exact h14
    · exact h17
    · exact h18
    · exact h19
    · exact le_rfl
  · exact hNK
  · rw [rkN]; norm_num
  · rw [rkK]; norm_num

theorem le_stdX (v14 v17 v18 v19 : ℕ) (c : Fin 64 → ℕ) (hc : ∀ r, c r ≤ Mx) (h1 : c rB1 ≤ 1)
    (hz : c rZ ≤ Dc.N * Dc.K) (h14 : c 14 ≤ v14) (h17 : c 17 ≤ v17) (h18 : c 18 ≤ v18)
    (h19 : c 19 ≤ v19) : c ≤ stdX v14 v17 v18 v19 := by
  intro r
  unfold stdX
  split_ifs with a1 a2 a3 a5 a6 a4
  · subst a1; exact h1
  · subst a2; exact hz
  · subst a3; exact h14
  · subst a5; exact h17
  · subst a6; exact h18
  · subst a4; exact h19
  · exact hc r

theorem top_of_inputs {M N K : ℕ} {c : Fin 64 → ℕ} (h : RingInputs M N K (layout M N K c))
    (r : Fin 64) : c r ≤ M := by simpa using h.top (tR r)

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
