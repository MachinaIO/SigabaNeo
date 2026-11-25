import PE.Impl.ExpLUT.Prog.RedKeySimEC

/-!
# `KGsim` on the VM (module 6b, part 3): the paired table loop (generic VM)

The `j` loop of F3's table (`KeyLut.jBodyK`) with the slab twin of `slabLut_eq_chain`: for each
`j < n` the chain is run from `(B, pu, L_c)` (`seChainC`, the public part is F3's `chainM`:
**`bitChain_seStep_fst`**), and besides `rAccL += A_j G⁻¹(α_j G)` the slab accumulator gets
`seAcc += [v G⁻¹(α_j G) | v ∈ slab_j]` (`seMapC`, `seSumC`).

* `seJRest`, **`exec_seJRest`**: one `j` after the coefficient routine;
* `seJBody cf`, **`exec_seJLoop`**: the loop, `rAccL = accM …` (F3's table) and
  `seAcc = seTab …`.

The payload `pu` (the table's input payload `μ`) is the head word of the step stream `rAinS = 0`
(read, not consumed); the chain's start slab is `seSc = 16`.
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- The current slab of the evaluation (the chain's start in the table). -/
@[simp, vmreg] abbrev seSc : Fin 64 := 16

variable {N K : ℕ}

/-! ### The public part of the paired chain is F3's chain -/

theorem seStep_fst (g t : ℕ) (D : SeBits N K)
    (st : (Fin 2 → Fin 2 × Fin K → Rq N K) × Rq N K × List (Fin 2 × Fin K → Rq N K)) :
    (seStep g D t st).1 = autVM g (2 ^ t) (D.Hf t) (D.Aa t) st.1 := rfl

theorem bitChain_seStep_fst (g : ℕ) (D : SeBits N K)
    (st : (Fin 2 → Fin 2 × Fin K → Rq N K) × Rq N K × List (Fin 2 × Fin K → Rq N K)) :
    ∀ t j, (bitChain (seStep g D) t j st).1 = chainM g D.Hf D.Aa t j st.1
  | 0, _ => rfl
  | t + 1, j => by
    rw [chainM_succ, ← bitChain_seStep_fst g D st t j]
    simp only [bitChain]
    split_ifs
    · rw [seStep_fst]
    · rfl

/-! ### One `j` after the coefficient -/

/-- One `j` (the coefficient `α_j` in `rAl`): the paired chain, `α G`, the slab and public
accumulations, `μ := σ_g(μ)`, `j := j + 1`. -/
def seJRest : Code :=
  .seq (.cp seA rB) <| .seq (.cp seSl seSc) <| .seq (.op .add seMu rAinS rZ) <| .seq seChainC <|
  .seq agC <| .seq (.cp seY rMA) <| .seq (.cp seQ seSl) <| .seq seMapC <| .seq (.cp seQ seAcc) <|
  .seq seSumC <| .seq (.cp rMA seY) <| .seq (.cp rGX seA) <| .seq ginvMulC <| .seq matAddC <|
  .seq (.op .aut rMu rMu rKc) (.op .add rJ rJ rOne)

/-- The registers the `j` loop only reads. -/
def seRoJ (r : Fin 64) : Bool :=
  (decide (r.val < 29) && !([2, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15, 17] : List ℕ).contains r.val) ||
    r == rKc || decide (57 ≤ r.val)

theorem seJRest_roJ : ∀ r : Fin 64, seRoJ r = true → seJRest.writes r = false := by decide

theorem seRoJ_keep : ∀ r : Fin 64, seRoJ r = true → seKeep r = true ∧ r ≠ rPw2 ∧ r ≠ rCt := by
  decide

theorem SeChainIn.of_roJ {w w' : St} {g b n : ℕ} {D : SeBits N K} (h : SeChainIn w g b n D)
    (hw : ∀ r : Fin 64, seRoJ r = true → w' r = w r) : SeChainIn w' g b n D :=
  ⟨by rw [hw _ (by decide)]; exact h.sw, by rw [hw _ (by decide)]; exact h.tb,
   by rw [hw _ (by decide)]; exact h.bit1, by rw [hw _ (by decide)]; exact h.trec,
   by rw [hw _ (by decide)]; exact h.tw, by rw [hw _ (by decide)]; exact h.kc,
   h.tm.of_writes fun q hq => hw q (by revert q; decide)⟩

/-- **One `j`**. -/
theorem exec_seJRest (hN : 0 < N) (hK : 0 < K) (w : St) (g b j : ℕ) (hg : 0 < g)
    (hj : j < 2 ^ K - 1) (D : SeBits N K) (α pu μj : Rq N K) (B acc : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Lc accS : List (Fin 2 × Fin K → Rq N K)) (restS : List Bool)
    (hin : SeChainIn w g b Lc.length D) (hbL : 2 ^ b ≤ Lc.length) (hAl : w rAl = encRM N K α)
    (hB : w rB = encL N K (matL B)) (hSc : w seSc = encL N K (seRows Lc))
    (hS : w rAinS = encRM N K pu ++ restS) (hJ : w rJ = encRM N K (j : Rq N K))
    (hMu : w rMu = encRM N K μj) (hAcc : w rAccL = encL N K (matL acc))
    (hSA : w seAcc = encL N K (seRows accS)) (haccl : accS.length = Lc.length)
    (hO : w rOne = encRM N K 1) (h4K : w rT4K = List.replicate (4 * K) false) :
    exec N K seJRest w rAccL = encL N K (matL fun a c =>
      acc a c + ginvMulm (chainM g D.Hf D.Aa b j B) (gM α) a c) ∧
    exec N K seJRest w seAcc = encL N K (seRows (List.zipWith seRowAdd accS
      ((bitChain (seStep g D) b j (B, pu, Lc)).2.2.map fun v => seGRow v (gM α)))) ∧
    exec N K seJRest w rJ = encRM N K ((j + 1 : ℕ) : Rq N K) ∧
    exec N K seJRest w rMu = encRM N K (aut N g μj) ∧
    (∀ r : Fin 64, seRoJ r = true → exec N K seJRest w r = w r) := by
  have hT := hin.tm
  refine ⟨?_, ?_, ?_, ?_, fun r hr => exec_writes _ _ _ (seJRest_roJ r hr)⟩ <;>
    unfold seJRest <;> simp only [exec_seq]
  all_goals
    generalize hW1 : exec N K (.op .add seMu rAinS rZ) (exec N K (.cp seSl seSc)
      (exec N K (.cp seA rB) w)) = W1
    have f1 : ∀ r : Fin 64, r ≠ seA → r ≠ seSl → r ≠ seMu → W1 r = w r := fun r h1 h2 h3 => by
      rw [← hW1]; vm_simp; simp [Function.update_apply, h1, h2, h3]
    have a1 : W1 seA = encL N K (matL B) ∧ W1 seSl = encL N K (seRows Lc) ∧
        W1 seMu = encRM N K pu := by
      rw [← hW1]; vm_simp
      simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hB, hSc, hS, hT.z,
        takeD_encRM_append, takeD_encRM, canonW_add hK, add_zero, and_self]
    have hin1 : SeChainIn W1 g b Lc.length D := hin.of_keep fun r hr _ _ =>
      f1 r (by intro e; subst e; simp [seKeep] at hr) (by intro e; subst e; simp [seKeep] at hr)
        (by intro e; subst e; simp [seKeep] at hr)
    obtain ⟨c1, c2, c3, T2⟩ := exec_seChainC hN hK W1 g b j hg hj D B pu Lc hbL hin1
      (by rw [f1 _ (by decide) (by decide) (by decide), hJ]) a1.1 a1.2.2 a1.2.1
    generalize hW2 : exec N K seChainC W1 = W2
    rw [hW2] at c1 c2 c3 T2
    rw [bitChain_seStep_fst] at c1
    have f2 : ∀ r : Fin 64, seRoJ r = true → W2 r = w r := fun r hr => by
      obtain ⟨k1, k2, k3⟩ := seRoJ_keep r hr
      rw [← hW2, exec_writes _ _ _ (seChainC_keep r k1 k2 k3), f1 r
        (by intro e; subst e; simp [seRoJ] at hr) (by intro e; subst e; simp [seRoJ] at hr)
        (by intro e; subst e; simp [seRoJ] at hr)]
    have g2 : ∀ r : Fin 64, (r = rAl ∨ r = rAccL ∨ r = rJ ∨ r = rMu ∨ r = seAcc) → W2 r = w r := by
      intro r hr
      rw [← hW2, exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
        f1 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
          (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
          (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    have ma3 := exec_agC hK W2 α (by rw [g2 _ (Or.inl rfl), hAl]) T2
    generalize hW3 : exec N K agC W2 = W3
    rw [hW3] at ma3
    have T3 : MulTmpl N K W3 := T2.of_writes fun q hq => by
      rw [← hW3]; exact exec_writes _ _ _ (by revert q; decide)
    generalize hW4 : exec N K (.cp seQ seSl) (exec N K (.cp seY rMA) W3) = W4
    have a4 : W4 seQ = encL N K (seRows (bitChain (seStep g D) b j (B, pu, Lc)).2.2) ∧
        W4 seY = encL N K (matL (gM α)) ∧ (W4 rTW).length = Lc.length := by
      rw [← hW4]; vm_simp
      simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, ma3]
      refine ⟨by rw [← hW3, exec_writes _ _ _ (by decide), c3], trivial, ?_⟩
      rw [← hW3, exec_writes _ _ _ (by decide), f2 _ (by decide), hin.tw]
    have T4 : MulTmpl N K W4 := T3.of_writes fun q hq => by
      rw [← hW4]; vm_simp
      have h1 : q ≠ seQ := by intro e; subst e; simp at hq
      have h2 : q ≠ seY := by intro e; subst e; simp at hq
      simp [Function.update_apply, h1, h2]
    have hlen := length_bitChain_seStep g D (B, pu, Lc) b j
    obtain ⟨m5, T5⟩ := exec_seMapC hK W4 _ (gM α) (by rw [a4.2.2, hlen]) a4.1 a4.2.1 T4
    generalize hW5 : exec N K seMapC W4 = W5
    rw [hW5] at m5 T5
    have s7 := exec_seSumC hK (exec N K (.cp seQ seAcc) W5) accS
      ((bitChain (seStep g D) b j (B, pu, Lc)).2.2.map fun v => seGRow v (gM α))
      (by rw [exec_cp, Function.update_of_ne (by decide), ← hW5, exec_writes _ _ _ (by decide),
        a4.2.2, haccl])
      (by rw [List.length_map, hlen, haccl])
      (by rw [exec_cp, Function.update_self, ← hW5, exec_writes _ _ _ (by decide), ← hW4,
        exec_writes _ _ _ (by decide), ← hW3, exec_writes _ _ _ (by decide), exec_writes _ _ _ (by decide),
        g2 _ (by simp), hSA])
      (by rw [exec_cp, Function.update_of_ne (by decide), m5])
      (T5.of_writes fun q hq => by rw [exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq)])
    generalize hW7 : exec N K seSumC (exec N K (.cp seQ seAcc) W5) = W7
    rw [hW7] at s7
    have T7 : MulTmpl N K W7 := T5.of_writes fun q hq => by
      rw [← hW7, exec_writes _ _ _ (by revert q; decide), exec_cp,
        Function.update_of_ne (by intro e; subst e; simp at hq)]
    have back7 : ∀ r : Fin 64, (r = rAccL ∨ r = rJ ∨ r = rMu ∨ r = seA ∨ r = rOne ∨ r = rT4K ∨
        r = rKc) → W7 r = W2 r := by
      intro r hr
      rw [← hW7, exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        exec_cp, Function.update_of_ne (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        ← hW5, exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        ← hW4, exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        ← hW3, exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    generalize hW8 : exec N K (.cp rGX seA) (exec N K (.cp rMA seY) W7) = W8
    have a8 : W8 rGX = encL N K (matL (chainM g D.Hf D.Aa b j B)) ∧ W8 rMA = encL N K (matL (gM α)) := by
      rw [← hW8]; vm_simp
      simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, back7 seA (by simp), c1, true_and]
      rw [← hW7, exec_writes _ _ _ (by decide), exec_cp, Function.update_of_ne (by decide), ← hW5,
        exec_writes _ _ _ (by decide), a4.2.1]
    have T8 : MulTmpl N K W8 := T7.of_writes fun q hq => by
      rw [← hW8]; vm_simp
      have h1 : q ≠ rGX := by intro e; subst e; simp at hq
      have h2 : q ≠ rMA := by intro e; subst e; simp at hq
      simp [Function.update_apply, h1, h2]
    have g9 := exec_ginvMulC hK W8 _ _ a8.1 a8.2 T8
    generalize hW9 : exec N K ginvMulC W8 = W9
    rw [hW9] at g9
    have back9 : ∀ r : Fin 64, (r = rAccL ∨ r = rJ ∨ r = rMu ∨ r = rOne ∨ r = rT4K ∨ r = rKc) →
        W9 r = W2 r := by
      intro r hr
      rw [← hW9, exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        ← hW8, exec_cp, Function.update_of_ne (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        exec_cp, Function.update_of_ne (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        back7 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    have T9 : MulTmpl N K W9 := T8.of_writes fun q hq => by
      rw [← hW9]; exact exec_writes _ _ _ (ginvMulC_writes_ge q hq)
    have c10 := exec_matAddC hK W9 (matL acc) (matL (ginvMulm (chainM g D.Hf D.Aa b j B) (gM α)))
      (4 * K) (by simp) (by simp) (by rw [back9 _ (by simp), g2 _ (by simp), hAcc]) g9
      (by rw [back9 _ (by simp), f2 _ (by decide), h4K]) T9.z
    generalize hW10 : exec N K matAddC W9 = W10
    rw [hW10] at c10
    have back10 : ∀ r : Fin 64, (r = rJ ∨ r = rMu ∨ r = rOne ∨ r = rKc) → W10 r = W2 r := by
      intro r hr
      rw [← hW10, exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
        back9 r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)]
  · rw [exec_add, Function.update_of_ne (by decide), exec_aut, Function.update_of_ne (by decide),
      c10, ← matL_add hK]
  · rw [exec_add, Function.update_of_ne (by decide), exec_aut, Function.update_of_ne (by decide),
      ← hW10, exec_writes _ _ _ (by decide), ← hW9, exec_writes _ _ _ (by decide), ← hW8,
      exec_writes _ _ _ (by decide), exec_writes _ _ _ (by decide), s7]
  · rw [exec_add, Function.update_self, exec_aut, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), back10 rJ (by simp), back10 rOne (by simp), g2 rJ (by simp), f2 rOne (by decide), hJ, hO,
      takeD_encRM, takeD_encRM, canonW_add hK, Nat.cast_succ]
  · rw [exec_add, Function.update_of_ne (by decide), exec_aut, Function.update_self,
      back10 rMu (by simp), back10 rKc (by simp), g2 rMu (by simp), hMu, takeD_encRM,
      f2 rKc (by decide), hin.kc, canonW_aut hK hN hg]

/-! ### The loop over `j` -/

/-- One `j`: the coefficient routine, then `seJRest`. -/
def seJBody (cf : Code) : Code := .seq cf seJRest

/-- **The slab table** after `j` values: `Σ_{j' < j} [v G⁻¹(α_{j'} G) | v ∈ chain_{j'}]`. -/
def seTab (cv : Rq N K → Rq N K) (g : ℕ) (D : SeBits N K) (b : ℕ)
    (B : Fin 2 → Fin 2 × Fin K → Rq N K) (pu μ0 : Rq N K) (Lc : List (Fin 2 × Fin K → Rq N K)) :
    ℕ → List (Fin 2 × Fin K → Rq N K)
  | 0 => List.replicate Lc.length fun _ => 0
  | j + 1 => List.zipWith seRowAdd (seTab cv g D b B pu μ0 Lc j)
      ((bitChain (seStep g D) b j (B, pu, Lc)).2.2.map fun v => seGRow v (gM (cv ((aut N g)^[j] μ0))))

theorem length_seTab (cv : Rq N K → Rq N K) (g : ℕ) (D : SeBits N K) (b : ℕ)
    (B : Fin 2 → Fin 2 × Fin K → Rq N K) (pu μ0 : Rq N K) (Lc : List (Fin 2 × Fin K → Rq N K)) :
    ∀ j, (seTab cv g D b B pu μ0 Lc j).length = Lc.length
  | 0 => by simp [seTab]
  | j + 1 => by
    simp only [seTab, List.length_zipWith, List.length_map, length_bitChain_seStep,
      length_seTab cv g D b B pu μ0 Lc j, min_self]

theorem seJBody_writes_rCj2 (cf : Code) (hcf : CoefW cf) : (seJBody cf).writes rCj2 = false := by
  have h1 : cf.writes rCj2 = false := by
    cases hw : cf.writes rCj2
    · rfl
    · rcases hcf _ hw with e | ⟨a, b⟩
      · exact absurd e (by decide)
      · simp at a
  simp only [seJBody, Code.writes, h1, Bool.false_or]
  decide

theorem seRoJ_roJ : ∀ r : Fin 64, seRoJ r = true → roJ r = true := by decide

theorem roC_seRoJ : ∀ r : Fin 64, roC r = true → seRoJ r = true := by decide

theorem seJBody_roJ (cf : Code) (hcf : CoefW cf) : ∀ r : Fin 64, seRoJ r = true →
    (seJBody cf).writes r = false := by
  intro r hr
  simp only [seJBody, Code.writes, hcf.ro r (seRoJ_roJ r hr), seJRest_roJ r hr, Bool.or_self]

/-- **The paired loop over `j`**: `rAccL = accM …` (F3's table), `seAcc = seTab …`. -/
theorem exec_seJLoop (hN : 0 < N) (hK : 0 < K) (cf : Code) (hcfw : CoefW cf)
    (cv : Rq N K → Rq N K) (w : St)
    (hcf : ∀ w' : St, (∀ r : Fin 64, roC r = true → w' r = w r) → ∀ μ : Rq N K,
      w' rMu = encRM N K μ → exec N K cf w' rAl = encRM N K (cv μ))
    (g b n : ℕ) (hg : 0 < g) (hn : n ≤ 2 ^ K - 1) (D : SeBits N K)
    (B : Fin 2 → Fin 2 × Fin K → Rq N K) (pu μ0 : Rq N K) (Lc : List (Fin 2 × Fin K → Rq N K))
    (restS : List Bool) (hin : SeChainIn w g b Lc.length D) (hbL : 2 ^ b ≤ Lc.length)
    (hB : w rB = encL N K (matL B)) (hSc : w seSc = encL N K (seRows Lc))
    (hS : w rAinS = encRM N K pu ++ restS) (hO : w rOne = encRM N K 1)
    (h4K : w rT4K = List.replicate (4 * K) false)
    (hAcc : w rAccL = encL N K (matL (fun _ _ => 0)))
    (hSA : w seAcc = encL N K (seRows (List.replicate Lc.length fun _ => 0)))
    (hJ : w rJ = encRM N K 0) (hMu : w rMu = encRM N K μ0) (hC : (w rCj2).length = n) :
    exec N K (.rep rCj2 (seJBody cf)) w rAccL =
      encL N K (matL (accM cv g D.Hf D.Aa b B μ0 n)) ∧
    exec N K (.rep rCj2 (seJBody cf)) w seAcc =
      encL N K (seRows (seTab cv g D b B pu μ0 Lc n)) ∧
    (∀ r : Fin 64, seRoJ r = true → exec N K (.rep rCj2 (seJBody cf)) w r = w r) := by
  have key := exec_rep_inv2 (N := N) (K := K) rCj2 (seJBody cf) (seJBody_writes_rCj2 cf hcfw)
    (fun j w' => w' rAccL = encL N K (matL (accM cv g D.Hf D.Aa b B μ0 j)) ∧
      w' seAcc = encL N K (seRows (seTab cv g D b B pu μ0 Lc j)) ∧
      w' rJ = encRM N K (j : Rq N K) ∧ w' rMu = encRM N K ((aut N g)^[j] μ0)) w
    ⟨by simp only [accM, Finset.sum_range_zero]; exact hAcc, hSA, by simpa using hJ,
      by simpa using hMu⟩ ?_
  · rw [hC] at key
    refine ⟨key.1, key.2.1, fun r hr => ?_⟩
    have hr' : r ≠ rCj2 := by intro e; subst e; simp [seRoJ] at hr
    exact exec_writes _ _ _ (by simp [Code.writes, seJBody_roJ cf hcfw r hr, Ne.symm hr'])
  · intro j w' hj hP _ hfr
    rw [hC] at hj
    obtain ⟨p1, p2, p3, p4⟩ := hP
    generalize hW0 : Function.update w' rCj2 (w' rCj2).tail = W0
    have f0 : ∀ r : Fin 64, seRoJ r = true → W0 r = w r := fun r hr => by
      have hr' : r ≠ rCj2 := by intro e; subst e; simp [seRoJ] at hr
      rw [← hW0, Function.update_of_ne hr', hfr r (seJBody_roJ cf hcfw r hr) hr']
    have q : ∀ r : Fin 64, (r = rAccL ∨ r = seAcc ∨ r = rJ ∨ r = rMu) → W0 r = w' r := by
      intro r hr
      rw [← hW0, Function.update_of_ne (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
    unfold seJBody
    rw [exec_seq]
    generalize hW1 : exec N K cf W0 = W1
    have c1 : W1 rAl = encRM N K (cv ((aut N g)^[j] μ0)) := hW1 ▸
      hcf W0 (fun r hr => f0 r (roC_seRoJ r hr)) _ (by rw [q _ (by simp), p4])
    have g1 : ∀ r : Fin 64, seRoJ r = true → W1 r = w r := fun r hr => by
      rw [← hW1, exec_writes _ _ _ (hcfw.ro r (seRoJ_roJ r hr)), f0 r hr]
    have k1 : ∀ r : Fin 64, (r = rAccL ∨ r = seAcc ∨ r = rJ ∨ r = rMu) → W1 r = w' r := by
      intro r hr
      rw [← hW1, hcfw.frame _ _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl <;> decide), q r hr]
    obtain ⟨r1, r2, r3, r4, -⟩ := exec_seJRest hN hK W1 g b j hg (by omega) D _ pu _ B _ Lc _ restS
      (hin.of_roJ g1) hbL c1 (by rw [g1 _ (by decide), hB]) (by rw [g1 _ (by decide), hSc])
      (by rw [g1 _ (by decide), hS]) (by rw [k1 _ (by simp), p3])
      (by rw [k1 _ (by simp), p4]) (by rw [k1 _ (by simp), p1]) (by rw [k1 _ (by simp), p2])
      (length_seTab cv g D b B pu μ0 Lc j) (by rw [g1 _ (by decide), hO])
      (by rw [g1 _ (by decide), h4K])
    refine ⟨?_, ?_, r3, ?_⟩
    · have e : (fun a c => accM cv g D.Hf D.Aa b B μ0 j a c +
          ginvMulm (chainM g D.Hf D.Aa b j B) (gM (cv ((aut N g)^[j] μ0))) a c) =
          accM cv g D.Hf D.Aa b B μ0 (j + 1) := by
        funext a c
        simp [accM, Finset.sum_range_succ]
      rw [r1, e]
    · rw [r2, seTab]
    · rw [r4, Function.iterate_succ_apply']

end AdvancedEncryption.ExpLUT.Prog
