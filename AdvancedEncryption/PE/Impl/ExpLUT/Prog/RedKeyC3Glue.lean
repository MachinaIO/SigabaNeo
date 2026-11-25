import PE.Impl.ExpLUT.Prog.RedKeyC1
import PE.Impl.ExpLUT.Prog.RedKeyC2
import PE.Impl.ExpLUT.Prog.RedKeyMidM
/-!
# Cost certificate of `mid`: the glue steps and phases M1–M2 on the `247` tapes

Bounds on the `247` tapes are written **`c3S a g`** (`a` on the MVM tapes `0 … 104` via
`RedKeyM.rkE`, `g` on the others — the bound version of `RedKeyMid.mS`).

* `c3_onM`: an MVM certificate `Cert (compile c) a b T` lifts to `onM c` on `c3S a g`;
* `c3_enter`: `midEnter` from `c3S a g` (every tape `≤ 2^150`) to `c3S (preResult N K a) g`;
* the `prog` steps `midLdM2`, `midStA`, `midLdPk` (exact bound transformers, `c3_ld`, `c3_st`,
  `c3_cons`);
* **`c3_cert_head`**: the head of `mid pk` — `m1P ; midEnter ; midLdM2 ; onM m2C ; midStA ;
  midEnter ; midLdPk` — from `rkIn` to **`c3S c3In c3G`** in `≤ 2^438` steps, where
  `c3In` is the MVM envelope at the start of M3 (`0 ≤ 2^101` raw secret, `1 ≤ 2^110` `ctW`,
  `2 ≤ 2^102` `mpkW`, `rCs ≤ predLen`, templates `35 … 38` exact, every other tape blank but the
  op-area tapes `41`/`42`… see `c3In`), and `c3G` the storage bounds (`tAF ≤ 2^104`,
  `tCt ≤ 2^110`, `tMpk ≤ 2^102`, `tSig ≤ 2^101`, `tC ≤ predLen`, others `0`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 2000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.RedKeyM
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid
open AdvancedEncryption.ExpLUT.Prog.KeyTime

/-! ### Bounds with storage tapes -/

/-- `a` on the MVM tapes, `g` on the others. -/
def c3S (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) : Fin 247 → ℕ := embedF rkE g a

theorem c3S_lo (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) (j : Fin 105) : c3S a g (rkE j) = a j := by
  simp [c3S]

theorem c3S_hi (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) (t : Fin 247) (ht : 105 ≤ t.val) :
    c3S a g t = g t := by
  rcases embedF_cases rkE g a t with ⟨-, h⟩ | ⟨j, hj, -⟩
  · exact h
  · have := j.isLt; rw [← hj, rkE_val] at ht; omega

theorem c3S_restrict (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) : (fun j => c3S a g (rkE j)) = a := by
  funext j; exact c3S_lo a g j

theorem c3_embedF (a a' : Fin 105 → ℕ) (g : Fin 247 → ℕ) :
    embedF rkE (c3S a g) a' = c3S a' g := by
  funext t
  by_cases hlo : t.val < 105
  · have e : t = rkE ⟨t.val, hlo⟩ := Fin.ext rfl
    rw [e, embedF_apply_self, c3S_lo]
  · rcases embedF_cases rkE (c3S a g) a' t with ⟨-, h⟩ | ⟨j, hj, -⟩
    · rw [h, c3S_hi _ _ _ (by omega), c3S_hi _ _ _ (by omega)]
    · have := j.isLt; rw [← hj, rkE_val] at hlo; omega

theorem c3S_update_lo (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) (j : Fin 105) (v : ℕ) :
    Function.update (c3S a g) (rkE j) v = c3S (Function.update a j v) g := by
  funext t
  by_cases ht : t = rkE j
  · subst ht; simp [c3S_lo]
  rw [Function.update_of_ne ht]
  by_cases hlo : t.val < 105
  · have e : t = rkE ⟨t.val, hlo⟩ := Fin.ext rfl
    have hne : (⟨t.val, hlo⟩ : Fin 105) ≠ j := fun h => ht (by rw [e, h])
    rw [e, c3S_lo, c3S_lo, Function.update_of_ne hne]
  · rw [c3S_hi _ _ _ (by omega), c3S_hi _ _ _ (by omega)]

theorem c3S_update_hi (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) (t : Fin 247) (ht : 105 ≤ t.val)
    (v : ℕ) : Function.update (c3S a g) t v = c3S a (Function.update g t v) := by
  funext l
  by_cases hl : l = t
  · subst hl; rw [Function.update_self, c3S_hi _ _ _ ht, Function.update_self]
  rw [Function.update_of_ne hl]
  by_cases hlo : l.val < 105
  · have e : l = rkE ⟨l.val, hlo⟩ := Fin.ext rfl
    rw [e, c3S_lo, c3S_lo]
  · rw [c3S_hi _ _ _ (by omega), c3S_hi _ _ _ (by omega), Function.update_of_ne hl]

theorem c3S_top {a : Fin 105 → ℕ} {g : Fin 247 → ℕ} {M : ℕ} (ha : ∀ t, a t ≤ M)
    (hg : ∀ t, g t ≤ M) : ∀ t, c3S a g t ≤ M := by
  intro t
  by_cases hlo : t.val < 105
  · have e : t = rkE ⟨t.val, hlo⟩ := Fin.ext rfl
    rw [e, c3S_lo]; exact ha _
  · rw [c3S_hi _ _ _ (by omega)]; exact hg _

theorem c3S_mono {a a' : Fin 105 → ℕ} {g g' : Fin 247 → ℕ} (ha : a ≤ a') (hg : g ≤ g') :
    c3S a g ≤ c3S a' g' := embedF_mono rkE hg ha

theorem c3N : Dc.N = 2 ^ 24 := RedPubP.pDc_N
theorem c3K : Dc.K = 2 ^ 16 := RedPubP.pDc_K
theorem c3NK : Dc.N * Dc.K = 2 ^ 40 := by rw [c3N, c3K]; norm_num

/-! ### The steps -/

theorem c3_onM (c : MVM.Code) {a b : Fin 105 → ℕ} {T : ℕ} (h : Cert (MVM.compile c) a b T)
    (g : Fin 247 → ℕ) : Cert (onM c) (c3S a g) (c3S b g) T := by
  have hf := Cert.frame rkE (a := c3S a g) (b := b) (p := MVM.compile c)
    (by rw [show (c3S a g ∘ rkE) = a from c3S_restrict a g]; exact h)
  rw [c3_embedF] at hf
  exact hf

theorem c3_enter (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) (ha : ∀ t, a t ≤ 2 ^ 150) :
    Cert midEnter (c3S a g) (c3S (preResult Dc.N Dc.K a) g) (2 ^ 310) := by
  have hn : Dc.N ≤ 2 ^ 150 := by rw [c3N]; norm_num
  have hk : Dc.K ≤ 2 ^ 150 := by rw [c3K]; norm_num
  have hr : Dc.N * Dc.K ≤ 2 ^ 150 := by rw [c3NK]; norm_num
  have h := cert_vmPre (2 ^ 150) Dc.N Dc.K a ha hn hk hr
  have hf := Cert.frame rkE (a := c3S a g) (b := preResult Dc.N Dc.K a)
    (p := .prog (MVM.IO.pre Dc.N Dc.K (fun _ ↦ 0)))
    (by rw [show (c3S a g ∘ rkE) = a from c3S_restrict a g]; exact h)
  rw [c3_embedF] at hf
  exact hf.mono le_rfl le_rfl (by norm_num)

theorem c3_tRg (r : Fin 64) : tRg r = rkE (tR r) := rfl

theorem c3_ld (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) (r : Fin 64) (t : Fin 247) (ht : 105 ≤ t.val) :
    Prim.lenT (.copy (tRg r) t) (c3S a g) = c3S (Function.update a (tR r) (g t)) g := by
  show Function.update _ _ _ = _
  rw [c3S_hi _ _ _ ht, c3_tRg, c3S_update_lo]

theorem c3_st (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) (r : Fin 64) (t : Fin 247) (ht : 105 ≤ t.val) :
    Prim.lenT (.copy t (tRg r)) (c3S a g) = c3S a (Function.update g t (a (tR r))) := by
  show Function.update _ _ _ = _
  rw [c3_tRg, c3S_lo, c3S_update_hi _ _ _ ht]

theorem c3_cons (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) (r : Fin 64) (b : Bool) :
    Prim.lenT (.cons (tRg r) b) (c3S a g) = c3S (Function.update a (tR r) (a (tR r) + 1)) g := by
  show Function.update _ _ _ = _
  rw [c3_tRg, c3S_lo, c3S_update_lo]

theorem c3_clr (a : Fin 105 → ℕ) (g : Fin 247 → ℕ) (t : Fin 247) (ht : 105 ≤ t.val) :
    Prim.lenT (.clear t) (c3S a g) = c3S a (Function.update g t 0) := by
  show Function.update _ _ _ = _
  rw [c3S_update_hi _ _ _ ht]

/-! ### The storage bounds -/

/-- The storage after M1 (`RedKeyC1.c1Out`) as `247`-bounds: blank MVM tapes. -/
theorem c1Out_eq : c1Out = c3S (fun _ => 0) c1Out := by
  funext t
  by_cases hlo : t.val < 105
  · have e : t = rkE ⟨t.val, hlo⟩ := Fin.ext rfl
    rw [e, c3S_lo]
    have h1 : rkE ⟨t.val, hlo⟩ ≠ tCt := fun h => by
      have := congrArg Fin.val h; simp [rkE_val, tCt] at this; omega
    have h2 : rkE ⟨t.val, hlo⟩ ≠ tMpk := fun h => by
      have := congrArg Fin.val h; simp [rkE_val, tMpk] at this; omega
    have h3 : rkE ⟨t.val, hlo⟩ ≠ tSig := fun h => by
      have := congrArg Fin.val h; simp [rkE_val, tSig] at this; omega
    have h4 : rkE ⟨t.val, hlo⟩ ≠ tC := fun h => by
      have := congrArg Fin.val h; simp [rkE_val, tC] at this; omega
    simp [c1Out, h1, h2, h3, h4]
  · rw [c3S_hi _ _ _ (by omega)]

/-- **The storage bounds from the second entry on** (`tAF` holds `matL A_F`). -/
def c3G : Fin 247 → ℕ := Function.update c1Out tAF (2 ^ 104)

/-! ### The head of `mid` -/

/-- The MVM bounds after the first entry. -/
def c3E1 : Fin 105 → ℕ := preResult Dc.N Dc.K (fun _ => 0)

theorem c3_blank_le (a : Fin 105 → ℕ) (ha : ∀ t, a t ≤ 2 ^ 104) (t : Fin 105)
    (h0 : t ≠ 41) (h1 : t ≠ 42) (hr : 41 ≤ t.val) : preResult Dc.N Dc.K a t = 0 := by
  have hreg : ∃ r : Fin 64, t = tR r :=
    ⟨⟨t.val - 41, by have := t.isLt; omega⟩, Fin.ext (by simp [tR]; omega)⟩
  obtain ⟨r, rfl⟩ := hreg
  simp only [preResult, h0, h1, if_false, KeyTime.blankVM]
  rw [show MVM.enc Dc.N Dc.K (fun _ => []) (tR r) = [] from MVM.encX_tR r]; rfl

theorem c3_pre_le (a : Fin 105 → ℕ) (ha : ∀ t, a t ≤ 2 ^ 104) (b : Fin 64 → ℕ)
    (hb0 : a 0 ≤ b 0) (hb1 : a 1 ≤ b 1) :
    preResult Dc.N Dc.K a ≤ layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b := by
  have hn : Dc.N ≤ 2 ^ 104 := by rw [c3N]; norm_num
  have hk : Dc.K ≤ 2 ^ 104 := by rw [c3K]; norm_num
  have hr : Dc.N * Dc.K ≤ 2 ^ 104 := by rw [c3NK]; norm_num
  have hi := preResult_inputs (2 ^ 104) Dc.N Dc.K a ha hn hk hr
  apply le_layout _ _ _ b _ hi.top (by simpa [c3K] using hi.templateK)
    (by simpa [c3N] using hi.templateN) (by simpa [c3NK] using hi.zeros.le)
    (by simpa [c3NK] using hi.ones)
  intro r
  by_cases h0 : r = 0
  · subst h0; simpa [preResult, tR] using hb0
  by_cases h1 : r = 1
  · subst h1; simpa [preResult, tR] using hb1
  rw [c3_blank_le a ha (tR r) (fun h => h0 (tR_inj (h.trans rfl)))
    (fun h => h1 (tR_inj (h.trans rfl))) (by simp [tR])]
  exact Nat.zero_le _


theorem c3_tC_ne : tC ≠ tAF := by decide
theorem c3G_vals : c3G tCt = 2 ^ 110 ∧ c3G tMpk = 2 ^ 102 ∧ c3G tSig = 2 ^ 101 ∧
    c3G tC = predLen ∧ c3G tAF = 2 ^ 104 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [c3G, c1Out, tCt, tMpk, tSig, tC, tAF]

theorem c1Out_vals : c1Out tMpk = 2 ^ 102 ∧ c1Out tC = predLen := by
  refine ⟨?_, ?_⟩ <;> simp [c1Out, tCt, tMpk, tSig, tC]

theorem c3_top150 {a : Fin 105 → ℕ} {g : Fin 247 → ℕ} (ha : ∀ t, a t ≤ 2 ^ 104)
    (hg : ∀ t, g t ≤ 2 ^ 110) : ∀ t, c3S a g t ≤ 2 ^ 150 :=
  c3S_top (fun t => (ha t).trans (by norm_num)) (fun t => (hg t).trans (by norm_num))

theorem c1Out_top : ∀ t, c1Out t ≤ 2 ^ 110 := by
  intro t; have := c1_predLen; unfold c1Out; split_ifs <;> omega

theorem c3G_top : ∀ t, c3G t ≤ 2 ^ 110 := by
  intro t; unfold c3G; rw [Function.update_apply]; split_ifs
  · norm_num
  · exact c1Out_top t

theorem c3E1_top : ∀ t, c3E1 t ≤ 2 ^ 104 := by
  have hi := preResult_inputs (2 ^ 104) Dc.N Dc.K (fun _ => 0) (fun _ => Nat.zero_le _)
    (by rw [c3N]; norm_num) (by rw [c3K]; norm_num) (by rw [c3NK]; norm_num)
  exact hi.top

theorem c3_cert_ldM2 :
    Cert (.prog midLdM2) (c3S c3E1 c1Out) (c3S c2In c1Out) (3 * (2 * (2 ^ 150 + 3) + 5)) := by
  refine ⟨?_, (c1CX_bounds midLdM2 (by simp [midLdM2, c1CX]) _ _
    (c3_top150 c3E1_top c1Out_top)).2⟩
  show Prog.lenBoundT midLdM2 _ ≤ _
  simp only [midLdM2, Prog.lenBoundT]
  rw [c3_ld _ _ _ _ (by decide), c3_ld _ _ _ _ (by decide), c3_cons]
  refine c3S_mono (fun t => ?_) le_rfl
  have hpre := c3_pre_le (fun _ => 0) (fun _ => Nat.zero_le _) c2InB (Nat.zero_le _)
    (Nat.zero_le _)
  obtain ⟨hM, hC⟩ := c1Out_vals
  have e : c3E1 (tR rB1) = 0 := c3_blank_le _ (fun _ => Nat.zero_le _) _ (by decide)
    (by decide) (by simp [tR, rB1])
  by_cases h1 : t = tR rB1
  · subst h1
    rw [Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide), e]
    simp [c2In, c2InB]
  by_cases h2 : t = tR rCs
  · subst h2
    rw [Function.update_of_ne (by decide), Function.update_self, hC]
    have := c1_predLen
    simp only [c2In, c2InB, layout_register]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    omega
  by_cases h3 : t = tR 2
  · subst h3
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self, hM]
    simp only [c2In, c2InB, layout_register]
    rw [Function.update_of_ne (by decide), Function.update_self]
  · rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    exact hpre t

theorem c3_cert_stA :
    Cert (.prog midStA) (c3S c2L c1Out) (c3S c2L c3G) (1 * (2 * (2 ^ 150 + 1) + 5)) := by
  refine ⟨?_, (c1CX_bounds midStA (by simp [midStA, c1CX]) _ _
    (c3_top150 c2L_inputs.top c1Out_top)).2⟩
  · show Prim.lenT (.copy tAF (tRg 8)) _ ≤ _
    rw [c3_st _ _ _ _ (by decide)]
    simp [c3G, c2L]

/-- **The MVM envelope at the start of M3** (after the second entry and `midLdPk`). -/
def c3In : Fin 105 → ℕ :=
  Function.update (Function.update (Function.update (Function.update
    (preResult Dc.N Dc.K c2L) (tR 0) (2 ^ 101)) (tR 1) (2 ^ 110)) (tR 2) (2 ^ 102)) (tR rCs) predLen

theorem c3_cert_ldPk :
    Cert (.prog midLdPk) (c3S (preResult Dc.N Dc.K c2L) c3G) (c3S c3In c3G)
      (4 * (2 * (2 ^ 150 + 4) + 5)) := by
  have hpt : ∀ t, preResult Dc.N Dc.K c2L t ≤ 2 ^ 104 :=
    (preResult_inputs (2 ^ 104) Dc.N Dc.K c2L c2L_inputs.top (by rw [c3N]; norm_num)
      (by rw [c3K]; norm_num) (by rw [c3NK]; norm_num)).top
  refine ⟨?_, (c1CX_bounds midLdPk (by simp [midLdPk, c1CX]) _ _ (c3_top150 hpt c3G_top)).2⟩
  show Prog.lenBoundT midLdPk _ ≤ _
  obtain ⟨g1, g2, g3, g4, -⟩ := c3G_vals
  simp only [midLdPk, Prog.lenBoundT]
  rw [c3_ld _ _ _ _ (by decide), c3_ld _ _ _ _ (by decide), c3_ld _ _ _ _ (by decide),
    c3_ld _ _ _ _ (by decide), g1, g2, g3, g4]
  exact le_rfl

/-! ### The head of `mid` -/

/-- The tail of `mid pk` from M3 on. -/
noncomputable def c3Rest (pk : MVM.Code) : XProg 247 :=
  .seq (onM pk) <| .seq (onM (simKeyC Dc)) <| .seq (.prog midLd14) <| .seq (onM (setXC Dc)) <|
    .seq (onM simXC) <| .prog midFin

theorem c3_mid_eq (pk : MVM.Code) : mid pk =
    (.seq m1P <| .seq midEnter <| .seq (.prog midLdM2) <| .seq (onM m2C) <| .seq (.prog midStA) <|
      .seq midEnter <| .seq (.prog midLdPk) (c3Rest pk)) := rfl

/-- **The head of `mid`** (phases M1, M2 and the glue up to M3). -/
theorem c3_cert_head (X : XProg 247) (out : Fin 247 → ℕ) (T : ℕ)
    (h : Cert X (c3S c3In c3G) out T) :
    Cert (.seq m1P <| .seq midEnter <| .seq (.prog midLdM2) <| .seq (onM m2C) <|
      .seq (.prog midStA) <| .seq midEnter <| .seq (.prog midLdPk) X) RedKeyT.rkIn out
      (2 ^ 438 + T) := by
  have p1 : Cert m1P RedKeyT.rkIn (c3S (fun _ => 0) c1Out) (2 ^ 437) := by
    rw [← c1Out_eq]; exact c1_cert_m1P
  have p2 := c3_enter (fun _ => 0) c1Out (fun _ => Nat.zero_le _)
  have p3 := c3_cert_ldM2
  have p4 := c3_onM _ c2_cert_m2C c1Out
  have p5 := c3_cert_stA
  have p6 := c3_enter c2L c3G (fun t => (c2L_inputs.top t).trans (by norm_num))
  have p7 := c3_cert_ldPk
  have all := p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (p7.seq h))))))
  refine all.mono le_rfl le_rfl ?_
  have hn : (2 : ℕ) ^ 437 + (2 ^ 310 + (3 * (2 * (2 ^ 150 + 3) + 5) + (2 ^ 391 +
      (1 * (2 * (2 ^ 150 + 1) + 5) + (2 ^ 310 + 4 * (2 * (2 ^ 150 + 4) + 5)))))) ≤ 2 ^ 438 := by norm_num
  calc _ = ((2 : ℕ) ^ 437 + (2 ^ 310 + (3 * (2 * (2 ^ 150 + 3) + 5) + (2 ^ 391 +
      (1 * (2 * (2 ^ 150 + 1) + 5) + (2 ^ 310 + 4 * (2 * (2 ^ 150 + 4) + 5))))))) + T := by ring
    _ ≤ 2 ^ 438 + T := Nat.add_le_add_right hn _

/-- **`RkMidBound` from a certificate of the tail** (phases M3, M4 and the exit): the tail must
take the envelope `c3S c3In c3G` to `rkLiftB a` in at most `2^439` steps. -/
theorem c3_midBound (pk : MVM.Code) (a : Fin 105 → ℕ) (T : ℕ)
    (h : Cert (c3Rest pk) (c3S c3In c3G) (RedKeyT.rkLiftB a) T) (hT : T ≤ 2 ^ 439) :
    RedKeyT.RkMidBound (mid pk) a := by
  have hc := c3_cert_head _ _ _ h
  rw [← c3_mid_eq] at hc
  exact ⟨hc.time.trans (by
    calc _ ≤ 2 ^ 438 + 2 ^ 439 := Nat.add_le_add_left hT _
      _ ≤ 2 ^ 440 := by norm_num), hc.len⟩

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
