import PE.Impl.ExpLUT.Prog.RedKeySimEMath

/-!
# `KGsim` on the VM (module 6b, part 6): the paired chain and table on full states (at `D`)

For the helper slabs of the supported forms (`SeForms`: `R_{H_{g_t}}` on the row `0`, `R_{C_{g_t}}`
and `R^aut_t` on the row `2^t`), the paired step `slabChainStep` of `RedKeySimSlab` is the VM's
`seStep` under the state map `(k, A, s) ↦ (A, σ_g^k μ, seSlabL s)` (**`seStep_slabChainStep`**),
hence the chains (**`bitChain_seStep_slab`**) and the tables (**`seSlabL_slabLut`**: `slabLut` is
`seTab … (2^b)`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib Matrix
open SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

variable (D : Dims)

/-- A slab supported on the row `i₀`. -/
noncomputable def seRowSl (i₀ : Fin (setting D).E.W) (v : Col (setting D).τ → Rg D) : Slab (setting D) :=
  fun i c => if i = i₀ then v c else 0

/-- **The supported forms of the helper slabs** (for the bits `t < b`). -/
structure SeForms (Q : SlabAut (setting D)) (hr cr : ℕ → Col (setting D).τ → Rg D)
    (ρ : ℕ → Dig (setting D).τ → Col (setting D).τ → Rg D) : Prop where
  hf : ∀ t < D.b, Q.hf t = seRowSl D (setting D).row0 (hr t)
  C : ∀ t < D.b, Q.C t = seRowSl D ((setting D).rowT t) (cr t)
  aut : ∀ t < D.b, ∀ d, Q.aut t d = seRowSl D ((setting D).rowT t) (ρ t d)

/-- **The per-bit data of a slab** for `seStep`. -/
noncomputable def seBitsOf (P : AutPub (setting D)) (h : AutData (setting D))
    (hr cr : ℕ → Col (setting D).τ → Rg D) (ρ : ℕ → Dig (setting D).τ → Col (setting D).τ → Rg D) :
    SeBits D.N D.K where
  gc t := fun a c => gcAut (setting D) ((setting D).idx (2 ^ t)) (P.Hi t) (h.hi t) a c
  ad t := fun d _ c => ρ t d c
  crow t := fun c => cr t c
  Aa t := fun d a c => P.Aaut t d a c
  hrow t := fun c => hr t c
  Hf t := fun a c => P.Hf t a c

/-- The state map of the paired chain. -/
noncomputable def seStOf (μ : Rg D)
    (st : ℕ × Matrix (Fin 2) (Col (setting D).τ) (Rg D) × Slab (setting D)) :
    (Fin 2 → Fin 2 × Fin D.K → Rq D.N D.K) × Rq D.N D.K × List (Fin 2 × Fin D.K → Rq D.N D.K) :=
  (fun a c => st.2.1 a c, (aut D.N (gD D))^[st.1] μ, seSlabL D st.2.2)

theorem idx_two_pow_eq_kf (t : ℕ) : (setting D).idx (2 ^ t) = (setting D).kf t := rfl

/-- **One paired step is `seStep`.** -/
theorem seStep_slabChainStep (P : AutPub (setting D)) (h : AutData (setting D))
    (Q : SlabAut (setting D)) (hr cr : ℕ → Col (setting D).τ → Rg D)
    (ρ : ℕ → Dig (setting D).τ → Col (setting D).τ → Rg D) (hQ : SeForms D Q hr cr ρ) (μ : Rg D)
    {t : ℕ} (ht : t < D.b) (st : ℕ × Matrix (Fin 2) (Col (setting D).τ) (Rg D) × Slab (setting D)) :
    seStep (gD D) (seBitsOf D P h hr cr ρ) t (seStOf D μ st) =
      seStOf D μ (slabChainStep P h Q μ t st) := by
  obtain ⟨k, A, s⟩ := st
  simp only [seStOf, slabChainStep]
  rw [seStep_eq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show _ = fun a c => autPK (setting D) ((setting D).kf t) (P.Hf t) (P.Aaut t) A a c
    rw [autPK_eq D (by rw [kf_setting]; exact (odd_gD D).pow)]
    show ginvMulm _ (mulPKm _ _) = ginvMulm _ (mulPKm (fun a c => aut D.N _ _) _)
    congr 2
    funext a' c'
    rw [seMatAut, aut_iterate D (odd_gD D), kf_setting]
  · show (aut D.N (gD D))^[2 ^ t] ((aut D.N (gD D))^[k] μ) = (aut D.N (gD D))^[k + 2 ^ t] μ
    rw [← Function.iterate_add_apply, add_comm]
  · show _ = seSlabL D (slabAut (2 ^ t) (P.Hi t) (P.Aaut t) A (h.hi t)
      ((setting D).E.σ ((setting D).idx k) μ) (Q.hf t) (Q.C t) (Q.aut t) s)
    rw [hQ.hf t ht, hQ.C t ht, show Q.aut t = fun d => seRowSl D ((setting D).rowT t) (ρ t d) from
      funext fun d => hQ.aut t ht d]
    unfold seRowSl
    rw [seSlabL_slabAut D ht, seSigIdx, length_seSlabL]
    rfl

/-- **The paired chains agree.** -/
theorem bitChain_seStep_slab (P : AutPub (setting D)) (h : AutData (setting D))
    (Q : SlabAut (setting D)) (hr cr : ℕ → Col (setting D).τ → Rg D)
    (ρ : ℕ → Dig (setting D).τ → Col (setting D).τ → Rg D) (hQ : SeForms D Q hr cr ρ) (μ : Rg D)
    (st : ℕ × Matrix (Fin 2) (Col (setting D).τ) (Rg D) × Slab (setting D)) :
    ∀ t, t ≤ D.b → ∀ j, bitChain (seStep (gD D) (seBitsOf D P h hr cr ρ)) t j (seStOf D μ st) =
      seStOf D μ (bitChain (slabChainStep P h Q μ) t j st)
  | 0, _, _ => rfl
  | t + 1, ht, j => by
    simp only [bitChain]
    rw [bitChain_seStep_slab P h Q hr cr ρ hQ μ st t (by omega) j]
    split_ifs
    · exact seStep_slabChainStep D P h Q hr cr ρ hQ μ (by omega) _
    · rfl

theorem seSlabL_zero : seSlabL D (0 : Slab (setting D)) =
    List.replicate (setting D).E.W fun _ => 0 := by
  apply List.ext_getElem (by simp [seSlabL])
  intro i h1 h2
  simp only [seSlabL, List.getElem_map, List.getElem_replicate]
  rfl

/-- **The table on a slab is `seTab`** (coefficients `coef j = cv (σ_g^j μ₀)`). -/
theorem seSlabL_slabLut (P : AutPub (setting D)) (h : AutData (setting D))
    (Q : SlabAut (setting D)) (hr cr : ℕ → Col (setting D).τ → Rg D)
    (ρ : ℕ → Dig (setting D).τ → Col (setting D).τ → Rg D) (hQ : SeForms D Q hr cr ρ)
    (coef : ℕ → Rg D) (cv : Rq D.N D.K → Rq D.N D.K) (μ0 : Rq D.N D.K)
    (hco : ∀ j < 2 ^ D.b, coef j = cv ((aut D.N (gD D))^[j] μ0))
    (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (μ : Rg D) (sc : Slab (setting D)) :
    seSlabL D (slabLut P coef A h Q μ sc) =
      seTab cv (gD D) (seBitsOf D P h hr cr ρ) D.b (fun a c => A a c) μ μ0 (seSlabL D sc)
        (2 ^ D.b) := by
  rw [slabLut_eq_chain]
  have hW := seW_eq D
  have key : ∀ m ≤ (setting D).E.W, seSlabL D (∑ j ∈ Finset.range m,
      fun i => (slabChain P A h Q μ sc (setting D).b j).2.2 i ᵥ* (setting D).ginv (coef j • (setting D).G)) =
      seTab cv (gD D) (seBitsOf D P h hr cr ρ) D.b (fun a c => A a c) μ μ0 (seSlabL D sc) m := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Finset.sum_range_zero, seSlabL_zero, seTab, length_seSlabL]
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ, seSlabL_add, ih (by omega), seTab, seSlabL_ginv]
      congr 1
      have e0 : seStOf D μ (0, A, sc) = ((fun a c => A a c), μ, seSlabL D sc) := rfl
      have hc := bitChain_seStep_slab D P h Q hr cr ρ hQ μ (0, A, sc) D.b le_rfl m
      rw [e0] at hc
      erw [hc]
      show _ = List.map _ (seSlabL D (slabChain P A h Q μ sc (setting D).b m).2.2)
      congr 1
      funext v
      rw [hco m (by omega), smul_G_eq_gM]
  exact key _ le_rfl

/-! ### The evaluation -/

/-- The supported forms of the fresh slabs of `Mul` (`Z^in_t`, `R^in_{t,d}` on the row `0`). -/
structure SeFormsIn (Q : SlabFresh Pos (setting D)) (zv : Pos → Col (setting D).τ → Rg D)
    (rv : Pos → Dig (setting D).τ → Col (setting D).τ → Rg D) : Prop where
  Z : ∀ t, Q.Zin t = seRowSl D (setting D).row0 (zv t)
  R : ∀ t d, Q.Rin t d = seRowSl D (setting D).row0 (rv t d)

/-- **The slab evaluation is `seEvalVM`** (at `F = bpOf (progOf C)`, `W = 2^{22}`), with
`Cin i = C^in_{read i}`, `pz i = X^{z_i}`, `pu i = X^{z_i + w x_{read i}}`, `z i`/`rd i` the rows of
`Z^in`/`R^in` at `read i`. -/
theorem seSlabL_slabEvalAt (hb : D.b = 22) (mpk : MPKt D) (C : List Bool)
    (ctd : EvalCTData (setting D) Pos) (x : Pos → ℕ) (Q : SlabFresh Pos (setting D))
    (hr cr : ℕ → Col (setting D).τ → Rg D) (ρ : ℕ → Dig (setting D).τ → Col (setting D).τ → Rg D)
    (hQ : SeForms D Q.aut hr cr ρ) (zv : Pos → Col (setting D).τ → Rg D)
    (rv : Pos → Dig (setting D).τ → Col (setting D).τ → Rg D) (hQi : SeFormsIn D Q zv rv) :
    ∀ i ≤ 16, seSlabL D (slabEvalAt (bpOf (progOf C)) (evalPub (helperMap D) mpk) ctd x Q i) =
      seEvalVM (cvsK D C) (gD D) (seBitsOf D (evalPub (helperMap D) mpk).aut ctd.aut hr cr ρ) D.b
        (xInvG (ZMod (2 ^ D.K - 1)) D.N) (2 ^ D.b) (AinK D mpk) (fun a c => mpk.A0 a c)
        (fun i a c => ctd.Cin ((bpOf (progOf C)).read i) a c)
        (fun i => (setting D).E.X ^ (bpOf (progOf C)).state x i)
        (fun i => (setting D).E.X ^ ((bpOf (progOf C)).state x i +
          (bpOf (progOf C)).w * x ((bpOf (progOf C)).read i)))
        (fun i c => zv ((bpOf (progOf C)).read i) c)
        (fun i d _ c => rv ((bpOf (progOf C)).read i) d c) (seSlabL D Q.R0) i
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := seSlabL_slabEvalAt hb mpk C ctd x Q hr cr ρ hQ zv rv hQi i (by omega)
    have hpk := evalPKAt_eq D hb mpk C i (by omega)
    simp only [slabEvalAt]
    rw [seSlabL_slabLut D _ _ _ hr cr ρ hQ _ (cvsK D C i) (xInvG (ZMod (2 ^ D.K - 1)) D.N)
      (fun j _ => coefs_eq D hb C (by omega) j),
      show Q.Rin ((bpOf (progOf C)).read i) = fun d => seRowSl D (setting D).row0
        (rv ((bpOf (progOf C)).read i) d) from funext fun d => hQi.R _ d, hQi.Z]
    unfold seRowSl
    rw [seSlabL_slabMul, ih, seEvalVM]
    erw [← hpk]
    rw [mulPK_eq_mulPKm]
    rfl

/-! ### The fresh slabs of `slabFreshOf` are of the supported forms -/

theorem seRowSl_of_supp (s : Slab (setting D)) (i₀ : Fin (setting D).E.W)
    (h : ∀ i, i ≠ i₀ → s i = 0) : s = seRowSl D i₀ (s i₀) := by
  funext i c
  unfold seRowSl
  split_ifs with hi
  · rw [hi]
  · rw [h i hi]; rfl

theorem slabβ_supp (i₀ : Fin (setting D).E.W) (Z : Matrix (Wb D) (Col (setting D).τ) (Rg D))
    (r : Rest (Wb D) (Jh D) (setting D).τ) :
    ∀ i, i ≠ i₀ → slabβ (J := Jh D) i₀ Z r i = 0 := by
  intro i hi
  rcases r with w | ⟨k, c'⟩
  · funext c; exact if_neg hi
  · rfl

theorem slabη_supp (i₀ : Fin (setting D).E.W) (k : Jh D) (r : Rest (Wb D) (Jh D) (setting D).τ) :
    ∀ i, i ≠ i₀ → slabη (Wb := Wb D) (S := setting D) i₀ k r i = 0 := by
  intro i hi
  rcases r with w | ⟨k', c'⟩
  · rfl
  · funext c; exact if_neg fun h => hi h.1

theorem finExt_supp {f : Fin (setting D).b → Slab (setting D)} {i₀ : ℕ → Fin (setting D).E.W}
    (hf : ∀ t : Fin (setting D).b, ∀ i, i ≠ i₀ t → f t i = 0) (t : ℕ) :
    ∀ i, i ≠ i₀ t → finExt (S := setting D) f t i = 0 := by
  intro i hi
  unfold finExt
  split_ifs with h
  · exact hf ⟨t, h⟩ i hi
  · rfl

variable (P : Prog (setting D) (Wb D) (Jh D) Pos) (r : Rest (Wb D) (Jh D) (setting D).τ)

/-- The row of `R_{H_{g_t}}` of the slab `r` (row `0`). -/
noncomputable def seHrOf (t : ℕ) : Col (setting D).τ → Rg D :=
  (slabFreshOf (helperMap D) P r).aut.hf t (setting D).row0
/-- The row of `R_{C_{g_t}}` of the slab `r` (row `2^t`). -/
noncomputable def seCrOf (t : ℕ) : Col (setting D).τ → Rg D :=
  (slabFreshOf (helperMap D) P r).aut.C t ((setting D).rowT t)
/-- The rows of `R^aut_{t,d}` of the slab `r` (row `2^t`). -/
noncomputable def seRhoOf (t : ℕ) (d : Dig (setting D).τ) : Col (setting D).τ → Rg D :=
  (slabFreshOf (helperMap D) P r).aut.aut t d ((setting D).rowT t)
/-- The row of `Z^in_t` of the slab `r` (row `0`). -/
noncomputable def seZvOf (t : Pos) : Col (setting D).τ → Rg D :=
  (slabFreshOf (helperMap D) P r).Zin t (setting D).row0
/-- The rows of `R^in_{t,d}` of the slab `r` (row `0`). -/
noncomputable def seRvOf (t : Pos) (d : Dig (setting D).τ) : Col (setting D).τ → Rg D :=
  (slabFreshOf (helperMap D) P r).Rin t d (setting D).row0

theorem seForms_slabFreshOf :
    SeForms D (slabFreshOf (helperMap D) P r).aut (seHrOf D P r) (seCrOf D P r) (seRhoOf D P r) :=
  ⟨fun t _ => seRowSl_of_supp D _ _ (finExt_supp D (i₀ := fun _ => (setting D).row0)
     (f := fun t' => slabη (setting D).row0 ((helperMap D).fwd t') r)
     (fun t' => slabη_supp D _ _ r) t),
   fun t _ => seRowSl_of_supp D _ _ (finExt_supp D (i₀ := fun t => (setting D).rowT t)
     (f := fun t' => slabη ((setting D).rowT t') ((helperMap D).inv t') r)
     (fun t' => slabη_supp D _ _ r) t),
   fun t _ d => by
     refine seRowSl_of_supp D _ _ ?_
     intro i hi
     show finExt (S := setting D) (fun t d => slabβ ((setting D).rowT t) (P.Raut t d) r) t d i = 0
     unfold finExt
     split_ifs with h
     · exact slabβ_supp D _ _ r i hi
     · rfl⟩

theorem seFormsIn_slabFreshOf :
    SeFormsIn D (slabFreshOf (helperMap D) P r) (seZvOf D P r) (seRvOf D P r) :=
  ⟨fun _ => seRowSl_of_supp D _ _ (slabβ_supp D _ _ r),
   fun _ _ => seRowSl_of_supp D _ _ (slabβ_supp D _ _ r)⟩

/-- **The slab `r` of `R̂_F = simKey …` is `seEvalVM … 16`** with the per-slab data
`seBitsOf … (seHrOf P r) (seCrOf P r) (seRhoOf P r)`, `z = seZvOf P r`, `rd = seRvOf P r` and the
start slab `slabβ row0 R₀ r` (`F = bpOf (progOf C)`, `W = 2^{22}`). -/
theorem seSlabL_simKey (hb : D.b = 22) (mpk : MPKt D) (C : List Bool) (ct : CTt D) (x : Pos → ℕ) :
    seSlabL D (slab (simKey (helperMap D) mpk (bpOf (progOf C)) ct x P) r) =
      seEvalVM (cvsK D C) (gD D) (seBitsOf D (evalPub (helperMap D) mpk).aut
          (evalData (helperMap D) mpk ct).aut (seHrOf D P r) (seCrOf D P r) (seRhoOf D P r)) D.b
        (xInvG (ZMod (2 ^ D.K - 1)) D.N) (2 ^ D.b) (AinK D mpk) (fun a c => mpk.A0 a c)
        (fun i a c => (evalData (helperMap D) mpk ct).Cin ((bpOf (progOf C)).read i) a c)
        (fun i => (setting D).E.X ^ (bpOf (progOf C)).state x i)
        (fun i => (setting D).E.X ^ ((bpOf (progOf C)).state x i +
          (bpOf (progOf C)).w * x ((bpOf (progOf C)).read i)))
        (fun i c => seZvOf D P r ((bpOf (progOf C)).read i) c)
        (fun i d _ c => seRvOf D P r ((bpOf (progOf C)).read i) d c)
        (seSlabL D (slabβ (setting D).row0 P.R0 r)) 16 := by
  rw [slab_simKey]
  exact seSlabL_slabEvalAt D hb mpk C _ x _ _ _ _ (seForms_slabFreshOf D P r) _ _
    (seFormsIn_slabFreshOf D P r) 16 le_rfl

end AdvancedEncryption.ExpLUT.Prog
