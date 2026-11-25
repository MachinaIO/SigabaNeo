import PE.Impl.RingBTVW.Prog.TightB1
import PE.Impl.RingBTVW.Prog.SetupCostP

/-!
# Steps of `Setup` on symbolic stores

The per-tape bounds of `setupP : XProg 96` are tracked as symbolic stores `bnd ρ σ` (one polynomial
per tape, `SigabaNeo.Lib.Machines.Prog.AbsBound`); the side conditions of every step are closed
checks (`allLe`, `pLe`, `aLe`, `xcheck`) decided by the kernel.

* `vb_copyS`, `vb_appCS`, `vb_frS`: a copy, an append (`appC`), a framed append (`frameApP 91 0`);
* `vb_smpS`: a framed sampler with a shape bound (`ATBb`);
* `vb_xcheck`: a framed block summarised by a certificate of the framed interpreter (`fcall`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym TightP

theorem bnd_le_of_allLe {n : ℕ} {σ : Asg} {T : Poly} (h : allLe σ T n = true) (ρ : List ℕ) :
    ∀ t : Fin n, bnd ρ σ t ≤ pEval ρ T := fun t => allLe_spec h ρ t

/-- **A copy.** -/
theorem vb_copyS (i j : Fin 96) (ρ : List ℕ) (σ : Asg) (Mp : Poly) (hall : allLe σ Mp 96 = true) :
    VB (prog (.prim (.copy i j))) (bnd ρ σ) (2 * (pEval ρ Mp + 1) + 3)
      (bnd ρ (aSet σ i.val (aGet σ j.val))) := by
  refine (VB.prim (.copy i j) (bnd_le_of_allLe hall ρ)).mono le_rfl le_rfl (le_of_eq ?_)
  rw [bnd_aSet]; rfl

/-- The store after `appC 0 s`. -/
def appA (σ : Asg) (s : ℕ) : Asg :=
  aSet (aSet (aSet (aSet σ 0 (pAdd (aGet σ 0) (aGet σ s))) 89 []) 88 []) 90 (aGet σ s)

/-- **An append to tape `0`.** -/
theorem vb_appCS (s : Fin 96) (ρ : List ℕ) (σ : Asg) (Mp : Poly) (hall : allLe σ Mp 96 = true)
    (hr : pLe (pAdd (aGet σ 0) (aGet σ s.val)) Mp = true) :
    VB (appC 0 s) (bnd ρ σ) ((2 * pEval ρ Mp + 3) + appT' (pEval ρ Mp) (bnd ρ σ s))
      (bnd ρ (appA σ s.val)) := by
  have h := vb_appC (r := 0) (a := s) (by decide) (by decide) (by decide) (bnd ρ σ)
    (bnd_le_of_allLe hall ρ) (by
      have := pEval_le_of_pLe ρ hr
      simp only [pEval_pAdd] at this
      exact this)
  refine h.mono le_rfl le_rfl (le_of_eq ?_)
  have e : appA σ s.val = aSet (aSet (aSet (aSet σ (0 : Fin 96).val
      (pAdd (aGet σ (0 : Fin 96).val) (aGet σ s.val))) (89 : Fin 96).val [])
      (88 : Fin 96).val []) (90 : Fin 96).val (aGet σ s.val) := rfl
  rw [e, bnd_aSet, bnd_aSet, bnd_aSet, bnd_aSet]
  funext t
  simp only [appOut, Function.update_apply, pEval_pAdd, pEval_nil]
  by_cases h90 : t = 90
  · simp [h90]; rfl
  · by_cases h88 : t = 88
    · simp [h88]
    · by_cases h89 : t = 89
      · simp [h89]
      · by_cases h0 : t = 0
        · subst h0; simp; rfl
        · simp [h90, h88, h89, h0]

/-- The store after `frameApP 91 0 89 90`. -/
def frA (σ : Asg) : Asg :=
  aSet (aSet (aSet σ 91 (pAdd (aGet σ 91) (pAdd (pMul (pC 2) (aGet σ 0)) (pC 1)))) 89 []) 90
    (aGet σ 0)

/-- **The framed append of tape `0` to the output tape `91`.** -/
theorem vb_frS (ρ : List ℕ) (σ : Asg) (Mp : Poly) (hall : allLe σ Mp 96 = true)
    (hr : pLe (pAdd (aGet σ 91) (pAdd (pMul (pC 2) (aGet σ 0)) (pC 1))) Mp = true) :
    VB (frameApP (91 : Fin 96) 0 89 90) (bnd ρ σ) (frT' (pEval ρ Mp) (bnd ρ σ (0 : Fin 96))) (bnd ρ (frA σ)) := by
  have h := vb_frameApP (k := 96) (r := 91) (a := 0) (S := 89) (c := 90) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (bnd ρ σ) (bnd_le_of_allLe hall ρ) (by
      have := pEval_le_of_pLe ρ hr
      simp only [pEval_pAdd, pEval_pMul, pEval_pC] at this
      exact this)
  refine h.mono le_rfl le_rfl (le_of_eq ?_)
  have e : frA σ = aSet (aSet (aSet σ (91 : Fin 96).val (pAdd (aGet σ (91 : Fin 96).val)
      (pAdd (pMul (pC 2) (aGet σ (0 : Fin 96).val)) (pC 1)))) (89 : Fin 96).val [])
      (90 : Fin 96).val (aGet σ (0 : Fin 96).val) := rfl
  rw [e, bnd_aSet, bnd_aSet, bnd_aSet]
  simp only [frOut, pEval_pAdd, pEval_pMul, pEval_pC, pEval_nil]
  rfl

/-- **A framed sampler**, the side conditions as closed checks: the scratch below `Sp`, the
output below `σ' (e 0)`, the scratch afterwards below `σ'`, the rest unchanged. -/
theorem vb_smpS (e : Fin 7 ↪ Fin 96) {p : XProg 7} {B : Bnd} (h : ATBb p B) (ρ : List ℕ)
    (σ σ' : Asg) (Sp pa ps : Poly)
    (chk : ((List.finRange 7).all fun j => j == 0 ||
      (pLe (aGet σ (e j).val) Sp && pLe (pAdd Sp ps) (aGet σ' (e j).val))) &&
      pLe (pAdd (aGet σ (e 0).val) pa) (aGet σ' (e 0).val) && aLe σ σ' = true)
    (hS₀ : B.S₀ ≤ pEval ρ Sp) (ha : B.a ≤ pEval ρ pa) (hs : B.s ≤ pEval ρ ps) :
    VB (frame e p) (bnd ρ σ) (B.T (bnd ρ σ (e 0)) (pEval ρ Sp)) (bnd ρ σ') := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq] at chk
  obtain ⟨⟨hj, h0⟩, hall⟩ := chk
  refine vb_smp e h le_rfl (fun j hj0 => ?_) hS₀ ?_ (fun j hj0 => ?_)
    (fun t => aLe_spec ρ hall t.val)
  · rcases hj j with h' | h'
    · exact absurd h' hj0
    · exact pEval_le_of_pLe ρ h'.1
  · have := pEval_le_of_pLe ρ h0
    simp only [pEval_pAdd] at this
    show _ ≤ pEval ρ (aGet σ' (e 0).val)
    unfold bnd at *
    omega
  · rcases hj j with h' | h'
    · exact absurd h' hj0
    · have := pEval_le_of_pLe ρ h'.2
      simp only [pEval_pAdd] at this
      show _ ≤ pEval ρ (aGet σ' (e j).val)
      omega

/-- **A block summarised by a certificate of the framed interpreter.** -/
theorem vb_xcheck {H : List ℕ → Prop} {n : ℕ} (a : XAst H n) {σ σ' : Asg} {c : Poly}
    (h : xcheck 8 a σ σ' c = true) (hlen : σ'.length = n) (ρ : List ℕ) (hH : H ρ) :
    VB a.toX (bnd ρ σ) (pEval ρ c) (bnd ρ σ') := fun ℓ hℓ => by
  have h' := bounds_of_xcheck h ρ hH hℓ
  exact ⟨h'.2, fun t => h'.1 t (by rw [hlen]; exact t.isLt)⟩

/-! ### The counter scratch of a coin sampler -/

/-- A loop leaves its counter at its entry bound when the body never writes it. -/
theorem lenBoundT_loop_self {k : ℕ} {i : Fin k} {body : XProg k} (hb : body.Preserves i)
    (ℓ : Fin k → ℕ) : lenBoundT (loop i body) ℓ i = ℓ i := by
  have hit : ∀ m, ((loopStepT i body)^[m] ℓ) i = ℓ i - m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', loopStepT, lenBoundT_of_preserves body i hb, tailB,
        Function.update_self, ih]
      omega
  show (Finset.range (ℓ i + 1)).sup (fun m => ((loopStepT i body)^[m] ℓ) i) = ℓ i
  simp only [hit]
  refine le_antisymm (Finset.sup_le fun m _ => Nat.sub_le _ _) ?_
  exact le_of_eq_of_le (by simp) (Finset.le_sup (f := fun m => ℓ i - m) (Finset.mem_range.mpr
    (Nat.succ_pos _)))

/-- **After `n` fair bits the counter scratch `4` is below `n`.** -/
theorem len_coinsF_4 (n : ℕ) (ℓ : Fin 7 → ℕ) : lenBoundT (coinsF n) ℓ 4 ≤ n := by
  have hpres : (coinAp (0 : Fin 7) 2).Preserves 4 := preserves_coinAp (by decide) (by decide)
  set L1 := lenBoundT (natP (3 : Fin 7) 4 n) ℓ with hL1
  have h3 : L1 3 ≤ n := by
    have := (natP_bounds (t := (3 : Fin 7)) (c := 4) (by decide) n ℓ (supB ℓ + n)
      (fun i => (le_supB ℓ i).trans (Nat.le_add_right _ _)) (Nat.le_add_left _ _)).1 3
    simpa [natB] using this
  show lenBoundT (prog (.prim (.clear 3))) (lenBoundT (loop 4 (coinAp 0 2))
    (Function.update L1 4 (L1 3))) 4 ≤ n
  rw [lenBoundT_prim]
  simp only [Prim.lenT]
  rw [Function.update_of_ne (by decide), lenBoundT_loop_self hpres, Function.update_self]
  exact h3

theorem embedF_le' {k m : ℕ} {e : Fin m ↪ Fin k} {a c : Fin k → ℕ} {b : Fin m → ℕ}
    (hb : ∀ j, b j ≤ c (e j)) (ha : ∀ t, (∀ j, e j ≠ t) → a t ≤ c t) : embedF e a b ≤ c := by
  intro t
  rcases embedF_cases e a b t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h]
    refine ha t fun j hj => ?_
    subst hj
    rw [partialInv_self] at hn
    exact Option.some_ne_none _ hn
  · rw [h]; exact hb j

/-- **A framed coin sampler**: as `vb_smpS`, and its counter scratch `e 4` below `n`. -/
theorem vb_smpS4 (e : Fin 7 ↪ Fin 96) (n : ℕ) (ρ : List ℕ) (σ σ' : Asg) (Sp pa ps p4 : Poly)
    (chk : ((List.finRange 7).all fun j => j == 0 ||
      (pLe (aGet σ (e j).val) Sp && (j == 4 || pLe (pAdd Sp ps) (aGet σ' (e j).val)))) &&
      pLe (pAdd (aGet σ (e 0).val) pa) (aGet σ' (e 0).val) && pLe p4 (aGet σ' (e 4).val) &&
      (List.finRange 96).all (fun t => t == e 4 || pLe (aGet σ t.val) (aGet σ' t.val)) = true)
    (hS₀ : (bCoins n).S₀ ≤ pEval ρ Sp) (ha : (bCoins n).a ≤ pEval ρ pa)
    (hs : (bCoins n).s ≤ pEval ρ ps) (h4 : n ≤ pEval ρ p4) :
    VB (frame e (coinsF n)) (bnd ρ σ) ((bCoins n).T (bnd ρ σ (e 0)) (pEval ρ Sp)) (bnd ρ σ') := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq] at chk
  obtain ⟨⟨⟨hj, h0⟩, hc4⟩, hall⟩ := chk
  have hB := atbb_coinsF n
  intro ℓ' hℓ'
  have hsh : (fun j => ℓ' (e j)) ≤ shp (0 : Fin 7) (bnd ρ σ (e 0)) (pEval ρ Sp) := fun j => by
    simp only [shp]
    split_ifs with hj0
    · subst hj0; exact hℓ' _
    · rcases hj j with h' | h'
      · exact absurd h' hj0
      · exact (hℓ' _).trans (pEval_le_of_pLe ρ h'.1)
  refine ⟨ATB.time hB hS₀ hsh, embedF_le' (fun j => ?_) (fun t ht => ?_)⟩
  · by_cases hj4 : j = 4
    · subst hj4
      exact (len_coinsF_4 n _).trans (h4.trans (pEval_le_of_pLe ρ hc4))
    · have := ((lenBoundT_mono _ hsh).trans
        ((show ATB (coinsF n) 0 (bCoins n).S₀ (bCoins n).a (bCoins n).s (bCoins n).T from hB)
          _ _ hS₀).2) j
      simp only [shp] at this
      split_ifs at this with hj0
      · subst hj0
        have := pEval_le_of_pLe ρ h0
        simp only [pEval_pAdd] at this
        show _ ≤ pEval ρ (aGet σ' (e 0).val)
        unfold bnd at *
        omega
      · rcases hj j with h' | h'
        · exact absurd h' hj0
        · rcases h'.2 with h'' | h''
          · exact absurd h'' hj4
          · have := pEval_le_of_pLe ρ h''
            simp only [pEval_pAdd] at this
            show _ ≤ pEval ρ (aGet σ' (e j).val)
            omega
  · rcases (of_decide_eq_true hall) t with h' | h'
    · exact absurd h'.symm (ht 4)
    · exact (hℓ' t).trans (pEval_le_of_pLe ρ h')

end AdvancedEncryption.RingBTVW.Prog
