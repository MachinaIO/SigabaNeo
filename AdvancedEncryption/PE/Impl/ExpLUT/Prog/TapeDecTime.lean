import PE.Impl.ExpLUT.Prog.TapeDecVM

/-!
# The clock of the packed decryption machine

`decProgram Dc` packed with a workspace of `37` tapes, every logical tape at most `TD = 2^110`:

* parsing and the length test: narrow frames, each its old clock (`DecTight.fu_unfrX`, `fu_clr`,
  `fu_lenX`) plus one leaf overhead (`fxa_vbFrame`);
* the templates (`tmplsP`): wide doubling loops (`natP`), `≤ (4n + 4) · Cn` for a template of `n`
  bits (`fxa_natP`);
* the constants and the output: narrow plain leaves (`fu_constP`, `fu_outP`, `fu_invP`);
* the code: `dtP_decCode`, at most `fD · dtTvm` (`fD = 1 + 4 · ovT 37 256 TD ≈ 2^131`);
* the branch on the length test: `FXa.ifBit`.

**`time_decMachineP : decMachineP.time ≤ 2 ^ 356`**.
-/

namespace AdvancedEncryption.ExpLUT.Prog.TapeDec

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Pack SigabaNeo.Tape.RingVM Function
open AdvancedEncryption.ExpLUT.Params
open AdvancedEncryption.ExpLUT.Prog.DecT (toB)
open AdvancedEncryption.ExpLUT.Prog.DecTight

/-- The identity placement. -/
abbrev ιD : Fin 256 ↪ Fin 256 := Embedding.refl _

/-- The leaf overhead. -/
abbrev ovD' : ℕ := ovT wD 256 TD

theorem hk256 : ¬ 256 ≤ wD := by decide

theorem FXa.postL {k : ℕ} {σ : Fin k ↪ Fin 256} {p : XProg k} {Pre Post Post' : (Fin 256 → ℕ) → Prop}
    {t : ℕ} (h : FXa wD TD σ p Pre Post t)
    (h' : ∀ L, Pre L → Post (Lafter σ p L) → Post' (Lafter σ p L)) :
    FXa wD TD σ p Pre Post' t := fun L hL =>
  have h1 := h L hL
  ⟨h1.1, h1.2.1, h' L hL h1.2.2.1, h1.2.2.2⟩

/-! ### Leaves from the old per-tape bounds -/

/-- A box below the cap. -/
abbrev Bx (a : Fin 256 → ℕ) (L : Fin 256 → ℕ) : Prop := L ≤ a

/-- **A narrow frame** from its old per-tape bounds. -/
theorem fxa_vbFrame {m : ℕ} (hm : m ≤ wD) {e : Fin m ↪ Fin 256} {q : XProg m}
    {a b : Fin 256 → ℕ} {T : ℕ} (h : XProg.VB (.frame e q) a T b) (ha : ∀ t, a t ≤ TD)
    (hb : ∀ t, b t ≤ TD) : FXa wD TD ιD (.frame e q) (Bx a) (Bx b) (T + ovD') := by
  have hA : ∀ L, Bx a L → Lafter (e.trans ιD) q L ≤ b := fun L hL => by
    rw [← Lafter_frame, Lafter_refl]; exact (h L hL).2
  refine (FXa.of_FX (FX.frame (FX.leaf hm (e.trans ιD) q fun L hL =>
      ⟨fun t => (hL t).trans (ha t), fun t => (hA L hL t).trans (hb t), ?_⟩))
    (fun L hL => (h L hL).1)).mono (fun _ h => h) (fun _ h => h) (by rw [Nat.one_mul])
  rw [← Lafter_frame, Lafter_refl]
  exact (h L hL).2

/-- **A narrow plain leaf** from its old per-tape bounds. -/
theorem fxa_vbProg {q : SigabaNeo.Tape.Prog 256} (hq : NarrowP wD q) {a b : Fin 256 → ℕ} {T : ℕ}
    (h : XProg.VB (.prog q) a T b) (ha : ∀ t, a t ≤ TD) (hb : ∀ t, b t ≤ TD) :
    FXa wD TD ιD (.prog q) (Bx a) (Bx b) (T + ovD') :=
  FXa.narrowProg ιD hq (fun L hL => by
    rw [Lafter_refl]
    exact ⟨fun t => (hL t).trans (ha t), fun t => ((h L hL).2 t).trans (hb t), (h L hL).2⟩)
    (fun L hL => (h L hL).1)

/-! ### The templates -/

/-- The time of a primitive leaf. -/
abbrev tPD : ℕ := 2 * (TD + 1) + 3 + ovD'

/-- The constant of the doubling loops. -/
irreducible_def Cn : ℕ := loopOv (256 * (2 * TD + 1)) TD + tPD + 6 * (256 * (2 * TD + 1)) + 18 + 2 * tPD

theorem tPD_le_Cn : tPD ≤ Cn := by rw [Cn_def]; omega
theorem loop_le_Cn : loopOv (256 * (2 * TD + 1)) TD + tPD ≤ Cn := by rw [Cn_def]; omega
theorem dbl_le_Cn : tPD + ((6 * (256 * (2 * TD + 1)) + 16) + 2) + tPD ≤ Cn := by
  rw [Cn_def]; omega

theorem Lafter_primD (a : Prim 256) (L : Fin 256 → ℕ) : Lafter ιD (.prog (.prim a)) L = a.lenT L := by
  rw [Lafter_refl]; rfl

/-- One primitive between two caps. -/
theorem fxaD_prim (a : Prim 256) {Pre Post : (Fin 256 → ℕ) → Prop}
    (h : ∀ L, Pre L → Le TD L ∧ Le TD (a.lenT L) ∧ Post (a.lenT L)) :
    FXa wD TD ιD (.prog (.prim a)) Pre Post tPD :=
  FXa.prim (by decide) ιD a fun L hL => by rw [Lafter_primD]; exact h L hL

/-- **A doubling loop** `t := t ++ t` (counter `c`), from `t` at most `m`. -/
theorem fxa_dblP {B m : ℕ} (hB : B + 1 ≤ TD) (hm : 2 * m ≤ B) (t c : Fin 256) (htc : t ≠ c) :
    FXa wD TD ιD (XProg.dblP t c) (fun L => Le B L ∧ L t ≤ m) (fun L => Le B L ∧ L t ≤ 2 * m)
      (tPD + ((6 * (256 * (2 * TD + 1)) + 16) +
        (m * (loopOv (256 * (2 * TD + 1)) TD + tPD) + 2))) := by
  set body : XProg 256 := .prog (.prim (.snoc t false))
  set g : (Fin 256 → ℕ) → (Fin 256 → ℕ) := fun ℓ' => body.lenBoundT (tailB c ℓ') with hgdef
  have step : ∀ ℓ : Fin 256 → ℕ, g ℓ t ≤ ℓ t + 1 ∧ ∀ x, x ≠ t → g ℓ x ≤ ℓ x := by
    intro ℓ
    refine ⟨?_, fun x hx => ?_⟩
    · simp only [hgdef, body, XProg.lenBoundT, SigabaNeo.Tape.Prog.lenBoundT, Prim.lenT,
        Function.update_self, tailB, Function.update_of_ne htc]
      exact le_rfl
    · simp only [hgdef, body, XProg.lenBoundT, SigabaNeo.Tape.Prog.lenBoundT, Prim.lenT,
        Function.update_of_ne hx, tailB, Function.update_apply]
      split_ifs with h
      · subst h; omega
      · exact le_rfl
  have hg : ∀ (ℓ : Fin 256 → ℕ) (j : ℕ), (g^[j] ℓ) t ≤ ℓ t + j ∧
      ∀ x, x ≠ t → (g^[j] ℓ) x ≤ ℓ x := by
    intro ℓ j
    induction j with
    | zero => exact ⟨le_rfl, fun _ _ => le_rfl⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨(step _).1.trans (by have := ih.1; omega),
        fun x hx => ((step _).2 x hx).trans (ih.2 x hx)⟩
  have hloop : ∀ L, (Le B L ∧ L t ≤ m ∧ L c ≤ m) →
      Le B (Lafter ιD (.loop c body) L) ∧ Lafter ιD (.loop c body) L t ≤ 2 * m := fun L hL => by
    rw [Lafter_refl]
    show (∀ x, iterSupT g (L c) L x ≤ B) ∧ iterSupT g (L c) L t ≤ 2 * m
    have ht : iterSupT g (L c) L t ≤ 2 * m :=
      Finset.sup_le fun j hj => by
        have := (hg L j).1
        have : j ≤ L c := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        omega
    refine ⟨fun x => ?_, ht⟩
    by_cases hx : x = t
    · subst hx; omega
    · exact Finset.sup_le fun j _ => ((hg L j).2 x hx).trans (hL.1 x)
  show FXa wD TD ιD (.seq (.prog (.prim (.copy c t))) (.loop c body)) _ _ _
  refine FXa.seq hk256 (Mid := fun L => Le B L ∧ L t ≤ m ∧ L c ≤ m)
    (fxaD_prim _ fun L hL => ⟨fun x => (hL.1 x).trans (by omega), fun x => ?_, ?_⟩) ?_
  · simp only [Prim.lenT, Function.update_apply]
    split_ifs
    · exact (hL.2).trans (by omega)
    · exact (hL.1 x).trans (by omega)
  · refine ⟨fun x => ?_, ?_, ?_⟩
    · simp only [Prim.lenT, Function.update_apply]
      split_ifs
      · exact (hL.2).trans (by omega)
      · exact hL.1 x
    · simp only [Prim.lenT, Function.update_of_ne htc]; exact hL.2
    · simp only [Prim.lenT, Function.update_self]; exact hL.2
  · refine (FXa.loop (Q := Le B) (Q' := fun _ => True) hk256 (fun L hL => hL.2.2)
      (fun L hL => ⟨fun x => (hL.1 x).trans (by omega),
        fun x => ((hloop L hL).1 x).trans (by omega), hloop L hL, (hloop L hL).1⟩)
      (fxaD_prim _ fun L hL => ⟨fun x => (hL x).trans (by omega),
        fun x => (lenT_le_succ _ hL x).trans hB, trivial⟩)).mono (fun _ h => h) (fun _ h => h) ?_
    omega

set_option maxRecDepth 100000 in
/-- **The template `t := replicate n false`**, at most `(4n + 4) · Cn` steps. -/
theorem fxa_natP {B : ℕ} (hB : B + 1 ≤ TD) (t c : Fin 256) (htc : t ≠ c) :
    ∀ n, n ≤ B → FXa wD TD ιD (XProg.natP t c n) (Le B) (fun L => Le B L ∧ L t ≤ n)
      ((4 * n + 4) * Cn) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | n
    · rw [XProg.natP]
      refine (fxaD_prim (.clear t) (Pre := Le B) (Post := fun L => Le B L ∧ L t ≤ 0)
        fun L hL => ⟨fun x => (hL x).trans (by omega), fun x => ?_,
        fun x => ?_, ?_⟩).mono (fun _ h => h) (fun _ h => h)
          (by have := tPD_le_Cn; omega)
      · simp only [Prim.lenT, Function.update_apply]; split_ifs <;> [omega; exact (hL x).trans (by omega)]
      · simp only [Prim.lenT, Function.update_apply]; split_ifs <;> [omega; exact hL x]
      · simp [Prim.lenT]
    · set m := (n + 1) / 2 with hm
      have hIH := ih m (by omega) (by omega)
      have hd := fxa_dblP hB (by omega : 2 * m ≤ B) t c htc
      have hdT : tPD + ((6 * (256 * (2 * TD + 1)) + 16) +
          (m * (loopOv (256 * (2 * TD + 1)) TD + tPD) + 2)) + tPD ≤ (m + 1) * Cn := by
        have : m * (loopOv (256 * (2 * TD + 1)) TD + tPD) ≤ m * Cn :=
          Nat.mul_le_mul_left _ loop_le_Cn
        have := dbl_le_Cn
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hsum : (4 * m + 4) * Cn + (m + 1) * Cn ≤ (4 * (n + 1) + 4) * Cn := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      rw [XProg.natP]
      split_ifs with h2
      · refine (FXa.seq hk256 (hIH.mono (fun _ h => h) (fun L h => ⟨h.1, h.2⟩) le_rfl)
          hd).mono (fun _ h => h) (fun L h => ⟨h.1, h.2.trans (by omega)⟩) (by omega)
      · refine (FXa.seq hk256 (FXa.seq hk256 hIH hd) (fxaD_prim (.snoc t false)
          (Pre := fun L => Le B L ∧ L t ≤ 2 * m) (Post := fun L => Le B L ∧ L t ≤ n + 1)
          fun L hL => ⟨fun x => (hL.1 x).trans (by omega), fun x => ?_, fun x => ?_, ?_⟩)).mono
          (fun _ h => h) (fun _ h => h) (by omega)
        · simp only [Prim.lenT, Function.update_apply]
          split_ifs with hx
          · subst hx; have := hL.2; omega
          · exact (hL.1 x).trans (by omega)
        · simp only [Prim.lenT, Function.update_apply]
          split_ifs with hx
          · subst hx; have := hL.2; omega
          · exact hL.1 x
        · simp only [Prim.lenT, Function.update_self]; have := hL.2; omega

/-- The time of the templates. -/
irreducible_def tTm (l : List (Fin 256 × ℕ)) : ℕ := (l.map fun p => (4 * p.2 + 4) * Cn).sum + tPD

theorem fxa_tmplsP {B : ℕ} (hB : B + 1 ≤ TD) (c : Fin 256) :
    ∀ l : List (Fin 256 × ℕ), (∀ p ∈ l, p.2 ≤ B ∧ p.1 ≠ c) →
      FXa wD TD ιD (tmplsP c l) (Le B) (Le B) (tTm l)
  | [], _ => (fxaD_prim (.copy c c) fun L hL => ⟨fun x => (hL x).trans (by omega),
      fun x => (lenT_le_succ _ hL x).trans hB, fun x => by
        simp only [Prim.lenT, Function.update_apply]; split_ifs <;> exact hL _⟩).mono
      (fun _ h => h) (fun _ h => h) (by rw [tTm_def]; simp)
  | p :: l, h => by
    have h1 := fxa_natP hB p.1 c (h p (by simp)).2 p.2 (h p (by simp)).1
    have h2 := fxa_tmplsP hB c l (fun q hq => h q (by simp [hq]))
    refine (FXa.seq hk256 (h1.mono (fun _ h => h) (fun _ h => h.1) le_rfl) h2).mono
      (fun _ h => h) (fun _ h => h) (le_of_eq ?_)
    rw [tTm_def, tTm_def]
    simp only [List.map_cons, List.sum_cons]
    ring

/-! ### The program -/

set_option maxRecDepth 100000 in
theorem dtL4_le : ∀ t, dtL4 t ≤ TD := by
  intro t
  refine dtFv_le (Nat.zero_le _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun x => ?_) t
  have : ∀ x : Fin 200, toB dtB0 x ≤ 2 ^ 110 := by decide +kernel
  exact this x

set_option maxRecDepth 100000 in
theorem dtL5_le : ∀ t, dtL5 t ≤ TD := by
  intro t
  refine dtFv_le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun x => ?_) t
  have : ∀ x : Fin 200, toB dtBend x ≤ 2 ^ 110 := by decide +kernel
  exact this x

theorem dtLfin_le : ∀ t, dtLfin t ≤ TD := fun t => by
  unfold dtLfin; split_ifs <;> norm_num

theorem dtL2_leT : ∀ t, dtL2 t ≤ TD := fun t => (dtL2_le t).trans (by norm_num)

theorem dtPsh_leT {M : ℕ} (hM : M ≤ TD) : ∀ t, dtPsh M t ≤ TD := fun t => (dtPsh_le M t).trans hM

/-- **The code, framed on its tapes.** -/
theorem fxa_vm : FXa wD TD ιD (.frame vmE (compile decCode)) (Bx dtL4) (Bx dtL5) (fD * dtTvm) := by
  refine FXa.frame hk256 (FXa.postL (dtP_decCode.mono (fun L hL => ⟨fun t => (hL t).trans
    (dtL4_le t), fun j => (hL (vmE j)).trans (dtFv_vmE_le _ _ _ _ _ _ _ _ _ _ (Nat.zero_le _)
      le_rfl le_rfl le_rfl le_rfl j)⟩) (fun _ h => h) le_rfl) fun L hL hP t => ?_)
  by_cases ht : t.val < 247
  · have e : t = vmE ⟨t.val, ht⟩ := Fin.ext rfl
    rw [e]
    exact (hP.2 ⟨t.val, ht⟩).trans
      (encB_le_fv _ _ _ _ _ _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl le_rfl _)
  · rw [← Lafter_frame, Lafter_refl]
    show embedF vmE L _ t ≤ _
    rcases embedF_cases vmE L (XProg.lenBoundT (compile decCode) fun j => L (vmE j)) t with
      ⟨-, h1⟩ | ⟨i, hi, -⟩
    · rw [h1]; refine (hL t).trans (le_of_eq ?_)
      unfold dtL4 dtL5; rw [dtFv_high t (by omega), dtFv_high t (by omega)]
    · exact absurd (show t.val < 247 by rw [← hi]; exact i.isLt) ht

set_option maxRecDepth 100000 in
theorem narrow_constP : NarrowP wD DecM.constP := by decide +kernel
set_option maxRecDepth 100000 in
theorem narrow_outP : NarrowP wD DecM.outP := by decide +kernel
set_option maxRecDepth 100000 in
theorem narrow_invP : NarrowP wD DecM.invP := by decide +kernel

/-- The time of the valid branch. -/
irreducible_def tValid : ℕ :=
  tTm (DecM.tmplList Dc) + ((fuConstT + ovD') + (fD * dtTvm + (fuOutT + ovD')))

set_option maxRecDepth 100000 in
theorem fxa_validP : FXa wD TD ιD (DecM.validP Dc) (Bx (dtPsh (2 ^ 109))) (fun _ => True) tValid := by
  have ht : FXa wD TD ιD (tmplsP 250 (DecM.tmplList Dc)) (Bx (dtPsh (2 ^ 109))) (Bx dtL2)
      (tTm (DecM.tmplList Dc)) :=
    FXa.postL ((fxa_tmplsP (B := 2 ^ 109) (by norm_num) 250 (DecM.tmplList Dc) fun p hp =>
      ⟨(tmpl_le_L2 p hp).trans (dtL2_le _), (tmpl_ok p hp).1⟩).mono
        (fun L hL t => (hL t).trans (dtPsh_le _ t)) (fun _ h => h) le_rfl) fun L hL _ => by
      rw [Lafter_refl]; exact (fu_tmplsDc L hL).2
  rw [tValid_def]
  exact FXa.seq hk256 ht (FXa.seq hk256 (fxa_vbProg narrow_constP fu_constP dtL2_leT dtL4_le)
    (FXa.seq hk256 fxa_vm ((fxa_vbProg narrow_outP fu_outP dtL5_le dtLfin_le).mono
      (fun _ h => h) (fun _ _ => trivial) le_rfl)))

/-- The time of the program. -/
irreducible_def tProg : ℕ :=
  ((Prog.unfrT (2 ^ 105) + ovD') + ((Prog.unfrT (2 * 2 ^ 105) + ovD') +
    ((Prog.unfrT (2 * (2 * 2 ^ 105)) + ovD') + ((Prog.unfrT (2 * (2 * (2 * 2 ^ 105))) + ovD') +
      ((2 * (2 * (2 * (2 * (2 * 2 ^ 105))) + 1) + 3) + ovD'))))) +
  ((fuLenT + ovD') + ((6 * (256 * (2 * TD + 1)) + 16) +
    ((2 * (256 * (2 * TD + 1)) + 3 + max tValid (fuInvT + ovD')) + 1)))

theorem fxa_parseX : FXa wD TD ιD DecM.parseX (Bx (dtPsh (2 ^ 105)))
    (Bx (dtPsh (2 * (2 * (2 * (2 * 2 ^ 105)))))) ((Prog.unfrT (2 ^ 105) + ovD') +
      ((Prog.unfrT (2 * 2 ^ 105) + ovD') + ((Prog.unfrT (2 * (2 * 2 ^ 105)) + ovD') +
        ((Prog.unfrT (2 * (2 * (2 * 2 ^ 105))) + ovD') +
          ((2 * (2 * (2 * (2 * (2 * 2 ^ 105))) + 1) + 3) + ovD'))))) := by
  have hc : ∀ M, M ≤ 2 ^ 109 → ∀ t, dtPsh M t ≤ TD := fun M hM => dtPsh_leT (hM.trans (by norm_num))
  exact FXa.seq hk256 (fxa_vbFrame (by decide) (fu_unfrX 253 _ (by decide) (2 ^ 105)) (hc _ (by norm_num))
    (hc _ (by norm_num))) (FXa.seq hk256 (fxa_vbFrame (by decide) (fu_unfrX 123 _ (by decide) (2 * 2 ^ 105))
      (hc _ (by norm_num)) (hc _ (by norm_num))) (FXa.seq hk256 (fxa_vbFrame (by decide)
        (fu_unfrX 120 _ (by decide) (2 * (2 * 2 ^ 105))) (hc _ (by norm_num)) (hc _ (by norm_num)))
      (FXa.seq hk256 (fxa_vbFrame (by decide) (fu_unfrX 124 _ (by decide) (2 * (2 * (2 * 2 ^ 105)))) (hc _ (by norm_num))
        (hc _ (by norm_num))) (fxa_vbProg (by decide +kernel) (fu_clr (2 * (2 * (2 * (2 * 2 ^ 105))))) (hc _ (by norm_num))
          (hc _ (by norm_num))))))

set_option maxRecDepth 100000 in
theorem fxa_decProgram (n : ℕ) (hn : n ≤ 2 ^ 105) :
    FXa wD TD ιD (DecM.decProgram Dc) (fun L => L = SigabaNeo.Tape.Prog.inputBound 255 n)
      (fun _ => True) tProg := by
  have e109 : dtPsh (2 * (2 * (2 * (2 * 2 ^ 105)))) = dtPsh (2 ^ 109) := congrArg dtPsh (by norm_num)
  have hlen := fxa_vbFrame (by decide) fu_lenX (dtPsh_leT (by norm_num)) (dtPsh_leT (by norm_num))
  have hif : FXa wD TD ιD (.ifBit 249 (DecM.validP Dc) (.prog DecM.invP))
      (Bx (dtPsh (2 ^ 109))) (fun _ => True)
      ((6 * (256 * (2 * TD + 1)) + 16) +
        ((2 * (256 * (2 * TD + 1)) + 3 + max tValid (fuInvT + ovD')) + 1)) := by
    refine FXa.ifBit hk256 (fun L hL => ⟨fun t => ?_, trivial⟩) fxa_validP
      ((fxa_vbProg narrow_invP fu_invP (dtPsh_leT (by norm_num)) dtLfin_le).mono (fun _ h => h)
        (fun _ _ => trivial) le_rfl)
    rw [Lafter_ifBit]
    exact max_le ((fxa_validP L hL).2.1 t)
      ((fxa_vbProg narrow_invP fu_invP (dtPsh_leT (by norm_num)) dtLfin_le L hL).2.1 t)
  show FXa wD TD ιD (.seq DecM.parseX (.seq DecM.lenX (.ifBit 249 (DecM.validP Dc) (.prog DecM.invP)))) _ _ _
  rw [tProg_def]
  exact (FXa.seq hk256 (fxa_parseX.mono (fun _ h => h) (fun L h => e109 ▸ h) le_rfl)
    (FXa.seq hk256 hlen hif)).mono
    (fun L hL => by subst hL; exact inputBound_le_Psh n hn) (fun _ h => h) le_rfl

/-! ### The clock -/


theorem tTm_le_gen (l : List (Fin 256 × ℕ))
    (h4 : (l.map fun p => 2 * dtL2 p.1 + 1).sum ≤ 2 ^ 99) (h5 : l.length = 70)
    (hle : ∀ p ∈ l, p.2 ≤ dtL2 p.1) : tTm l ≤ (2 ^ 100 + 280) * Cn + tPD := by
  have hs : (l.map fun p => 4 * p.2 + 4).sum ≤ 2 ^ 100 + 280 := by
    have h1 : ∀ p ∈ l, 4 * p.2 + 4 ≤ 2 * (2 * dtL2 p.1 + 1) + 2 := fun p hp => by
      have := hle p hp; omega
    have h2 := List.sum_le_sum h1
    have h3 : (l.map fun p => 2 * (2 * dtL2 p.1 + 1) + 2).sum =
        2 * (l.map fun p => 2 * dtL2 p.1 + 1).sum + 2 * l.length := by
      rw [List.sum_map_add, List.sum_map_mul_left, List.map_const', List.sum_replicate]
      ring
    omega
  rw [tTm_def]
  have : (l.map fun p => (4 * p.2 + 4) * Cn).sum = (l.map fun p => 4 * p.2 + 4).sum * Cn := by
    rw [List.sum_map_mul_right]
  rw [this]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hs) _

theorem tTm_le : tTm (DecM.tmplList Dc) ≤ (2 ^ 100 + 280) * Cn + tPD := by
  have h4 := tmpl_sum_le
  rw [← tmpl_sum_eq] at h4
  exact tTm_le_gen _ h4 (DecConf.length_tmplList Dc) tmpl_le_L2

set_option exponentiation.threshold 2000 in
theorem arith_val {tm co ov fv ou : ℕ} (htm : tm ≤ (2 ^ 100 + 280) * 2 ^ 131 + 2 ^ 131)
    (hco : co ≤ 2 ^ 152) (hov : ov ≤ 2 ^ 130) (hfv : fv ≤ (2 ^ 131 + 2 ^ 125) * 2 ^ 224)
    (hou : ou ≤ 2 ^ 112) : tm + ((co + ov) + (fv + (ou + ov))) ≤
      (2 ^ 100 + 280) * 2 ^ 131 + 2 ^ 131 + ((2 ^ 152 + 2 ^ 130) +
        ((2 ^ 131 + 2 ^ 125) * 2 ^ 224 + (2 ^ 112 + 2 ^ 130))) := by
  omega

set_option exponentiation.threshold 2000 in
theorem arith_tProg {u1 u2 u3 u4 c ov lt V I : ℕ} (hu : u1 + (u2 + (u3 + (u4 + c))) ≤ 2 ^ 221)
    (hov : ov ≤ 2 ^ 130) (hlt : lt ≤ 2 ^ 222)
    (hV : V ≤ (2 ^ 100 + 280) * 2 ^ 131 + 2 ^ 131 + ((2 ^ 152 + 2 ^ 130) +
      ((2 ^ 131 + 2 ^ 125) * 2 ^ 224 + (2 ^ 112 + 2 ^ 130)))) (hI : I ≤ 2 ^ 112) :
    ((u1 + ov) + ((u2 + ov) + ((u3 + ov) + ((u4 + ov) + (c + ov))))) +
      ((lt + ov) + ((6 * (256 * (2 * 2 ^ 110 + 1)) + 16) +
        ((2 * (256 * (2 * 2 ^ 110 + 1)) + 3 + max V (I + ov)) + 1))) ≤ 2 ^ 356 - 2 ^ 354 := by
  have : max V (I + ov) ≤ (2 ^ 100 + 280) * 2 ^ 131 + 2 ^ 131 + ((2 ^ 152 + 2 ^ 130) +
      ((2 ^ 131 + 2 ^ 125) * 2 ^ 224 + (2 ^ 112 + 2 ^ 130))) := max_le hV (by omega)
  omega

set_option exponentiation.threshold 2000 in
theorem arith_dec2 {n a p t c o : ℕ} (hn : n ≤ 2 ^ 105)
    (ha : a ≤ 327 * (2 * (2 ^ 105 + 256) + 5)) (hp : p ≤ 2 ^ 120) (ht : t ≤ 2 ^ 356 - 2 ^ 354)
    (hc : c ≤ 2 ^ 122) (ho : o ≤ 3) : (2 * n + 2) + a + p + t + c + (2 * o + 2) ≤ 2 ^ 356 := by
  omega

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem tProg_le : tProg ≤ 2 ^ 356 - 2 ^ 354 := by
  have hT := tTm_le
  have hv := dtTvm_le
  have hov : ovD' ≤ 2 ^ 130 := by unfold ovD' ovT putTime; norm_num
  have hC : Cn ≤ 2 ^ 131 := by rw [Cn_def]; unfold tPD loopOv putTime; norm_num [ovD', ovT, putTime]
  have hfD : fD ≤ 2 ^ 131 + 2 ^ 125 := by unfold fD ovT putTime; norm_num
  have hvm : fD * dtTvm ≤ (2 ^ 131 + 2 ^ 125) * 2 ^ 224 := Nat.mul_le_mul hfD hv
  have htP : tPD ≤ 2 ^ 131 := by
    show 2 * (2 ^ 110 + 1) + 3 + ovD' ≤ 2 ^ 131
    omega
  have hTm : tTm (DecM.tmplList Dc) ≤ (2 ^ 100 + 280) * 2 ^ 131 + 2 ^ 131 :=
    hT.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hC) htP)
  have hP := fuParseT_le
  have hL := fuLenT_le
  have hc : fuConstT ≤ 2 ^ 152 := by unfold fuConstT; norm_num
  have ho : fuOutT ≤ 2 ^ 112 := by unfold fuOutT; norm_num
  have hi : fuInvT ≤ 2 ^ 112 := by unfold fuInvT; norm_num
  have hu : Prog.unfrT (2 ^ 105) + (Prog.unfrT (2 * 2 ^ 105) + (Prog.unfrT (2 * (2 * 2 ^ 105)) +
      (Prog.unfrT (2 * (2 * (2 * 2 ^ 105))) + (2 * (2 * (2 * (2 * (2 * 2 ^ 105))) + 1) + 3)))) ≤
      2 ^ 221 := hP
  have hval : tValid ≤ (2 ^ 100 + 280) * 2 ^ 131 + 2 ^ 131 + ((2 ^ 152 + 2 ^ 130) +
      ((2 ^ 131 + 2 ^ 125) * 2 ^ 224 + (2 ^ 112 + 2 ^ 130))) := by
    rw [tValid_def]; exact arith_val hTm hc hov hvm ho
  rw [tProg_def]
  exact arith_tProg hu hov hL hval hi

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
/-- **The clock of the packed decryption machine**: at most `2^356` steps. -/
theorem time_decMachineP : decMachineP.time ≤ 2 ^ 356 := by
  have hn := DecConf.dtInput_le
  have h := time_packMachineT_le' (D := dD) (DecM.decProgram Dc) 255 0 (DecM.decInputLength Dc predLen)
    (fxa_decProgram _ hn)
  have ho : XProg.lenBoundT (DecM.decProgram Dc)
      (SigabaNeo.Tape.Prog.inputBound 255 (DecM.decInputLength Dc predLen)) 0 ≤ 3 := by
    have hb := fu_decProgram _ (inputBound_le_Psh _ hn)
    exact (hb.2 0).trans (by simp [dtLfin])
  have hp : putTime 256 (DecM.decInputLength Dc predLen) ≤ 2 ^ 120 :=
    (putTime_mono le_rfl hn).trans (by unfold putTime; norm_num)
  have h8 : (256 + 1) * (2 * (DecM.decInputLength Dc predLen + 256) + 5) ≤
      327 * (2 * (2 ^ 105 + 256) + 5) := Nat.mul_le_mul (by norm_num) (by omega)
  have h9 : 6 * (256 * (2 * TD + 1)) + 16 ≤ 2 ^ 122 := by norm_num
  have ht := tProg_le
  exact h.trans (arith_dec2 hn h8 hp ht h9 ho)

end AdvancedEncryption.ExpLUT.Prog.TapeDec
