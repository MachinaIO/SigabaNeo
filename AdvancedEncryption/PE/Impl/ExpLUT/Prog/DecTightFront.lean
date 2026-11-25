import PE.Impl.ExpLUT.Prog.DecTimeConf
import PE.Impl.ExpLUT.Prog.DecTightVM

/-!
# Tight clock of the `Dec` machine: the program around the code (part 5)

The per-tape shape `dtFv Z M a b c d R`: the operation area `0 … 39` at most `Z`, the template tapes
`40 … 43` at most `a, b, c, d`, the blank scratch `44 … 46` empty, the register `x` (tape `47 + x`)
at most `R x`, the other tapes at most `M`. Unlike the uniform shape of `DecTimeConf` it keeps
the operation area empty and the registers apart, so the compiled code is entered below
`encB (2^40) N K (toB dtB0)` (`DecTight.dt_decCode`):

* parsing (`fu_parseX`, every word below `2^109`) and the length test (`fu_lenX`);
* the templates, each charged its own length (`vb_tmplsT`, `fu_tmplsDc`);
* the constants (`vb_forN43T`, `fu_constP`);
* the code (`fu_vm`), the output (`fu_outP`) and the invalid branch (`fu_invP`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.DecTight

set_option autoImplicit false
set_option linter.deprecated false

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM AdvancedEncryption.ExpLUT.Params
open DecM
open SigabaNeo.Tape.XProg
open AdvancedEncryption.ExpLUT.Prog.DecT (toB)

/-! ### The shape -/

/-- A pointwise order, stated tape by tape. -/
theorem dtPile {n : ℕ} {L L' : Fin n → ℕ} (h : ∀ t, L t ≤ L' t) : L ≤ L' := h

/-- The per-tape shape. -/
def dtFv (Z M a b c d : ℕ) (R : Fin 200 → ℕ) : Fin 256 → ℕ := fun t =>
  if t.val < 40 then Z else if t.val = 40 then a else if t.val = 41 then b
  else if t.val = 42 then c else if t.val = 43 then d else if t.val < 47 then 0
  else if h : t.val < 247 then R ⟨t.val - 47, by omega⟩ else M

theorem dtFv_mono {Z M a b c d Z' M' a' b' c' d' : ℕ} {R R' : Fin 200 → ℕ} (hZ : Z ≤ Z') (hM : M ≤ M')
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d') (hR : R ≤ R') :
    dtFv Z M a b c d R ≤ dtFv Z' M' a' b' c' d' R' := dtPile fun t => by
  have hR' : ∀ x, R x ≤ R' x := hR
  unfold dtFv; split_ifs <;> first | exact hR' _ | omega

theorem dtFv_le {Z M a b c d U : ℕ} {R : Fin 200 → ℕ} (hZ : Z ≤ U) (hM : M ≤ U) (ha : a ≤ U)
    (hb : b ≤ U) (hc : c ≤ U) (hd : d ≤ U) (hR : ∀ x, R x ≤ U) (t : Fin 256) :
    dtFv Z M a b c d R t ≤ U := by
  unfold dtFv; split_ifs <;> first | omega | exact hR _

theorem dtFv_high {Z M a b c d : ℕ} {R : Fin 200 → ℕ} (t : Fin 256) (ht : 247 ≤ t.val) :
    dtFv Z M a b c d R t = M := by
  unfold dtFv
  split_ifs <;> first | rfl | omega

theorem dtFv_reg {Z M a b c d : ℕ} {R : Fin 200 → ℕ} (x : Fin 200) : dtFv Z M a b c d R (tR x) = R x := by
  have hx := x.isLt
  have e : (tR x).val = 47 + x.val := rfl
  unfold dtFv
  split_ifs <;> first | omega | (congr 1; ext; simp [e])

theorem dtFv_low {Z M a b c d : ℕ} {R : Fin 200 → ℕ} (t : Fin 256) (ht : t.val < 40) :
    dtFv Z M a b c d R t = Z := by
  unfold dtFv; rw [if_pos ht]

/-! ### Generic blocks -/

/-- **A block framed on a few tapes**, from a uniform bound of the block. -/
theorem vbU_frame {m : ℕ} (e : Fin m ↪ Fin 256) {p : XProg m} {M T M' : ℕ}
    (h : ∀ ℓ : Fin m → ℕ, (∀ i, ℓ i ≤ M) →
      XProg.timeBoundT p ℓ ≤ T ∧ ∀ i, XProg.lenBoundT p ℓ i ≤ M')
    {L L' : Fin 256 → ℕ} (hin : ∀ j, L (e j) ≤ M) (hout : ∀ j, M' ≤ L' (e j)) (hrest : L ≤ L') :
    VB (.frame e p) L T L' := by
  have h' : VB p (fun j => L (e j)) T (fun _ => M') := fun ℓ hℓ => by
    have := h ℓ (fun i => (hℓ i).trans (hin i))
    exact ⟨this.1, fun i => this.2 i⟩
  refine (VB.frame e h').mono le_rfl le_rfl fun t => ?_
  rcases embedF_cases e L (fun _ => M') t with ⟨-, h1⟩ | ⟨i, rfl, h1⟩
  · rw [h1]; exact hrest t
  · rw [h1]; exact hout i

/-- **A primitive**, its bound vector `p.lenT L`, from a uniform bound `U`. -/
theorem vbU_prim (p : Prim 256) {L : Fin 256 → ℕ} {U : ℕ} (hU : ∀ t, L t ≤ U) {L' : Fin 256 → ℕ}
    (h : p.lenT L ≤ L') : VB (.prog (.prim p)) L (2 * (U + 1) + 3) L' :=
  (VB.prim p hU).mono le_rfl le_rfl h

theorem vb_progSeqT {p q : Tape.Prog 256} {a b c : Fin 256 → ℕ} {T U : ℕ}
    (hp : VB (.prog p) a T b) (hq : VB (.prog q) b U c) :
    VB (.prog (Tape.Prog.seq p q)) a (T + U) c := fun ℓ hℓ => VB.seq hp hq ℓ hℓ

/-- **The templates**, each charged its own length (counter `250`, uniform bound `M`). -/
theorem vb_tmplsT (M : ℕ) {L' : Fin 256 → ℕ} (hM : ∀ t, L' t ≤ M) (h250 : L' 250 = M) :
    ∀ (l : List (Fin 256 × ℕ)) (L : Fin 256 → ℕ), L ≤ L' → (∀ p ∈ l, p.1 ≠ 250 ∧ p.2 ≤ L' p.1) →
    VB (tmplsP 250 l) L ((l.map fun p => 2 * L' p.1 + 1).sum * (4 * M + 12) + (2 * (M + 1) + 3)) L'
  | [], L, hL, _ => by
    refine (vbU_prim (.copy 250 250) (fun t => (hL t).trans (hM t)) fun t => ?_).mono le_rfl
      (by simp) le_rfl
    simp only [Prim.lenT, Function.update_eq_self]
    exact hL t
  | p :: l, L, hL, h => by
    have hp := h p (by simp)
    have h1 := VB.natP (t := p.1) (c := (250 : Fin 256)) (Ne.symm hp.1) p.2
      (fun i => (hL i).trans (hM i)) (hp.2.trans (hM _))
    have h2 : natB p.1 250 p.2 L ≤ L' := fun i => by
      simp only [natB]
      split_ifs with e1 e2
      · subst e1; exact hp.2
      · subst e2; rw [h250]; exact max_le ((hL 250).trans (hM _)) (hp.2.trans (hM _))
      · exact hL i
    have ih := vb_tmplsT M hM h250 l L' le_rfl (fun q hq => h q (by simp [hq]))
    refine ((h1.mono le_rfl le_rfl h2).seq ih).mono le_rfl ?_ le_rfl
    simp only [List.map_cons, List.sum_cons]
    set s := (l.map fun p => 2 * L' p.1 + 1).sum
    have : (2 * p.2 + 1) * (4 * M + 12) ≤ (2 * L' p.1 + 1) * (4 * M + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    have e := Nat.add_mul (2 * L' p.1 + 1) s (4 * M + 12)
    omega

theorem dt_iter_snocT {k : ℕ} (c r : Fin k) (hcr : c ≠ r) (b : Bool) (L : Fin k → ℕ) :
    ∀ j, (Tape.Prog.loopStepT c (.prim (.snoc r b)))^[j] L ≤ Function.update L r (L r + j)
  | 0 => fun i => by simp
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    refine (Tape.Prog.loopStepT_mono c _ (dt_iter_snocT c r hcr b L j)).trans fun i => ?_
    simp only [Tape.Prog.loopStepT, Tape.Prog.lenBoundT, Prim.lenT, Tape.tailB,
      Function.update_apply]
    split_ifs <;> simp_all

/-- **`c` ones on `43`** (counter `250` copied from `42`), on any bound vector. -/
theorem vb_forN43T (L L' : Fin 256 → ℕ) (M c : ℕ) (hM : ∀ i, L i ≤ M) (h42 : L 42 ≤ c)
    (h43 : L 43 = 0) (hcM : c ≤ M) (hL' : ∀ i, i ≠ 43 → i ≠ 250 → L i ≤ L' i) (h43' : c ≤ L' 43)
    (h250' : c ≤ L' 250) :
    VB (.prog (Tape.Prog.forN 250 42 (.prim (.snoc 43 true)))) L
      ((2 * (M + 1) + 3) + (c * (4 * M + 9) + 2)) L' := by
  intro ℓ hℓ
  have hu : ∀ i, ℓ i ≤ M := fun i => (hℓ i).trans (hM i)
  set ℓ1 := Prim.lenT (.copy (250 : Fin 256) 42) ℓ with hℓ1
  have e1 : ℓ1 = Function.update ℓ 250 (ℓ 42) := rfl
  have hl42 : ℓ 42 ≤ c := (hℓ 42).trans h42
  have hl43 : ℓ 43 = 0 := by have h' : ℓ 43 ≤ L 43 := hℓ 43; omega
  have hit := dt_iter_snocT (k := 256) 250 43 (by decide) true ℓ1
  have hbnd : ∀ j, j ≤ ℓ1 250 → ∀ i,
      ((Tape.Prog.loopStepT 250 (.prim (.snoc 43 true)))^[j] ℓ1) i ≤ M := by
    intro j hj i
    refine (hit j i).trans ?_
    have hj' : j ≤ c := by rw [e1, Function.update_self] at hj; omega
    simp only [e1, Function.update_apply]
    split_ifs <;> simp_all; omega
  refine ⟨?_, ?_⟩
  · show Tape.Prog.timeBoundT (.prim (.copy 250 42)) ℓ +
      Tape.Prog.timeBoundT (.loop 250 (.prim (.snoc 43 true))) ℓ1 ≤ _
    refine Nat.add_le_add ?_ ?_
    · show 2 * (supB ℓ + 0) + 3 ≤ _
      have := XProg.supB_le_of hu; omega
    · refine (Tape.Prog.timeBoundT_loop_le 250 _ ℓ1 (R := 4 * M + 8) fun j hj => ?_).trans ?_
      · show 2 * supB _ + 3 + (2 * (supB _ + 1) + 3) ≤ _
        have s1 := XProg.supB_le_of (hbnd j hj.le)
        have s2 : supB (Tape.tailB 250 ((Tape.Prog.loopStepT 250
            (.prim (.snoc 43 true)))^[j] ℓ1)) ≤ M :=
          XProg.supB_le_of fun i => (Tape.tailB_le 250 _ i).trans (hbnd j hj.le i)
        omega
      · have : ℓ1 250 ≤ c := by rw [e1, Function.update_self]; exact hl42
        have : ℓ1 250 * (4 * M + 8 + 1) ≤ c * (4 * M + 9) := Nat.mul_le_mul this (by omega)
        omega
  · show Tape.Prog.lenBoundT (.loop 250 (.prim (.snoc 43 true))) ℓ1 ≤ _
    refine Tape.iterSupT_le fun j hj i => (hit j i).trans ?_
    have hj' : j ≤ c := by rw [e1, Function.update_self] at hj; omega
    by_cases h1 : i = 43
    · subst h1
      rw [Function.update_self, e1, Function.update_of_ne (by decide), hl43]
      exact (show 0 + j ≤ L' 43 by omega)
    · rw [Function.update_of_ne h1, e1]
      by_cases h2 : i = 250
      · subst h2; rw [Function.update_self]; exact (show ℓ 42 ≤ L' 250 by omega)
      · rw [Function.update_of_ne h2]
        exact (show ℓ i ≤ L i from hℓ i).trans (hL' i h1 h2)

/-! ### Parsing and the length test -/

/-- The registers of the parsed words: `C`, `sk`, `ct` on `73`, `76`, `77`. -/
def dtRp (M : ℕ) : Fin 200 → ℕ := fun x => if x.val = 73 ∨ x.val = 76 ∨ x.val = 77 then M else 0

/-- The shape while parsing. -/
def dtPsh (M : ℕ) : Fin 256 → ℕ := dtFv 0 M 0 0 0 0 (dtRp M)

theorem dtRp_mono {M M' : ℕ} (h : M ≤ M') (x : Fin 200) : dtRp M x ≤ dtRp M' x := by
  unfold dtRp; split_ifs <;> omega

theorem dtPsh_mono {M M' : ℕ} (h : M ≤ M') : dtPsh M ≤ dtPsh M' :=
  dtFv_mono le_rfl h le_rfl le_rfl le_rfl le_rfl (dtPile (dtRp_mono h))

theorem dtPsh_le (M : ℕ) (t : Fin 256) : dtPsh M t ≤ M :=
  dtFv_le (Nat.zero_le _) le_rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (fun x => by unfold dtRp; split_ifs <;> omega) t

theorem dtPsh_tape (M : ℕ) (t : Fin 256)
    (ht : t.val = 120 ∨ t.val = 123 ∨ t.val = 124 ∨ 247 ≤ t.val) : dtPsh M t = M := by
  rcases ht with h | h | h | h
  · obtain rfl : t = tR 73 := Fin.ext h
    rw [dtPsh, dtFv_reg]; simp [dtRp]
  · obtain rfl : t = tR 76 := Fin.ext h
    rw [dtPsh, dtFv_reg]; simp [dtRp]
  · obtain rfl : t = tR 77 := Fin.ext h
    rw [dtPsh, dtFv_reg]; simp [dtRp]
  · exact dtFv_high t h

theorem uI_tapes (d : Fin 256) (hd : d.val = 120 ∨ d.val = 123 ∨ d.val = 124 ∨ 247 ≤ d.val)
    (j : Fin 4) : (uI d j).val = 120 ∨ (uI d j).val = 123 ∨ (uI d j).val = 124 ∨
      247 ≤ (uI d j).val := by
  fin_cases j <;> simp [uI]
  omega

theorem fu_unfrX (d : Fin 256) (h : Function.Injective (uI d))
    (hd : d.val = 120 ∨ d.val = 123 ∨ d.val = 124 ∨ 247 ≤ d.val) (M : ℕ) :
    VB (unfrX d h) (dtPsh M) (Prog.unfrT M) (dtPsh (2 * M)) :=
  vbU_frame _ (fun ℓ hℓ => Prog.ubp_unfrP M ℓ hℓ)
    (fun j => (dtPsh_tape M _ (uI_tapes d hd j)).le)
    (fun j => (dtPsh_tape (2 * M) _ (uI_tapes d hd j)).ge) (dtPsh_mono (by omega))

theorem fu_clr (M : ℕ) : VB (.prog (Prog.clr 253)) (dtPsh M) (2 * (M + 1) + 3) (dtPsh M) :=
  vbU_prim (.clear 253) (dtPsh_le M) fun t => by
    simp only [Prim.lenT, Function.update_apply]
    split_ifs
    · exact Nat.zero_le _
    · exact le_rfl

/-- The clock of parsing. -/
def fuParseT : ℕ :=
  Prog.unfrT (2 ^ 105) + (Prog.unfrT (2 * 2 ^ 105) + (Prog.unfrT (2 * (2 * 2 ^ 105)) +
    (Prog.unfrT (2 * (2 * (2 * 2 ^ 105))) + (2 * (2 * (2 * (2 * (2 * 2 ^ 105))) + 1) + 3))))

/-- **Parsing.** -/
theorem fu_parseX : VB parseX (dtPsh (2 ^ 105)) fuParseT (dtPsh (2 ^ 109)) := by
  have e : (2 : ℕ) ^ 109 = 2 * (2 * (2 * (2 * 2 ^ 105))) := by norm_num
  rw [e]
  exact (fu_unfrX 253 _ (by decide) _).seq ((fu_unfrX 123 _ (by decide) _).seq
    ((fu_unfrX 120 _ (by decide) _).seq ((fu_unfrX 124 _ (by decide) _).seq (fu_clr _))))

/-- The clock of the length test. -/
def fuLenT : ℕ := (12 * predLen + 6 * 2 ^ 109 + 120) * (2 * 2 ^ 109 + 5)

/-- **The length test.** -/
theorem fu_lenX : VB lenX (dtPsh (2 ^ 109)) fuLenT (dtPsh (2 ^ 109)) :=
  vbU_frame _ (fun ℓ hℓ => Prog.lenEqP_bounds predLen (by norm_num [predLen]) (by norm_num) ℓ hℓ)
    (fun j => (dtPsh_le _ _).trans le_rfl)
    (fun j => by
      refine (dtPsh_tape _ _ ?_).ge
      fin_cases j <;> simp [lenMap])
    le_rfl

/-! ### The templates -/

/-- The register bounds after the templates (`3` holds `N K - 1` bits, `75` is empty). -/
def dtR2 : Fin 200 → ℕ := Function.update (Function.update (toB dtB0) 3 (2 ^ 40 - 1)) 75 0

/-- The shape after the templates. -/
def dtL2 : Fin 256 → ℕ := dtFv 0 (2 ^ 109) (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) 0 dtR2

set_option maxRecDepth 100000 in
theorem dtB0_le : ∀ x, toB dtB0 x ≤ 2 ^ 109 := by decide +kernel

theorem dtR2_le (x : Fin 200) : dtR2 x ≤ 2 ^ 109 := by
  unfold dtR2
  simp only [Function.update_apply]
  split_ifs
  · exact Nat.zero_le _
  · norm_num
  · exact dtB0_le x

theorem dtL2_le (t : Fin 256) : dtL2 t ≤ 2 ^ 109 :=
  dtFv_le (Nat.zero_le _) le_rfl (by norm_num) (by norm_num) (by norm_num) (Nat.zero_le _) dtR2_le t

theorem dtL2_250 : dtL2 250 = 2 ^ 109 := dtFv_high 250 (by decide)

set_option maxRecDepth 100000 in
theorem dtPsh_le_L2 : ∀ t, dtPsh (2 ^ 109) t ≤ dtL2 t := by decide +kernel

set_option maxRecDepth 100000 in
theorem dtL2_kReg : ∀ t < 22, dtL2 (tR (kReg t)) = 2 * 2 ^ 24 := by decide +kernel

set_option maxRecDepth 100000 in
theorem dtL2_rReg : ∀ b < 14, dtL2 (tR (rReg b)) = 2 * 2 ^ 24 := by decide +kernel

set_option maxRecDepth 100000 in
theorem tmplTapes_ne250 : ∀ u ∈ tmplTapes, u ≠ 250 := by decide +kernel

set_option maxRecDepth 10000 in
/-- **Every template fits its bound.** -/
theorem tmpl_le_L2 : ∀ p ∈ tmplList Dc, p.2 ≤ dtL2 p.1 := by
  have hκ : ∀ t, t < 22 → κD Dc t ≤ dtL2 (tR (kReg t)) := fun t ht => by
    rw [dtL2_kReg t ht]
    exact (Nat.mod_lt _ (by rw [DecConf.Dc_N]; positivity)).le.trans (by rw [DecConf.Dc_N])
  have hρ : ∀ b, b < 14 → ρD Dc.N b ≤ dtL2 (tR (rReg b)) := fun b hb => by
    rw [dtL2_rReg b hb]
    exact (Nat.sub_le _ _).trans (by rw [DecConf.Dc_N])
  simp only [tmplList, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨⟨?_, fun t ht => hκ t ht⟩, fun b hb => hρ b hb⟩
  simp only [DecConf.dmBC_eq, DecConf.dmJ_eq, DecConf.dmJC_eq, dmlen_col, DecConf.dmDig_eq,
    DecConf.dmPos_eq, DecConf.dmB_eq, len_fin2, famMLen, DecConf.Dc_K, DecConf.Dc_N,
    DecConf.Dc_mb, Dc_b]
  decide +kernel

theorem tmpl_ok : ∀ p ∈ tmplList Dc, p.1 ≠ 250 ∧ p.2 ≤ dtL2 p.1 := fun p hp =>
  ⟨tmplTapes_ne250 _ (by rw [← tmplList_fst Dc]; exact List.mem_map_of_mem hp), tmpl_le_L2 p hp⟩

theorem tmpl_sum_eq : ((tmplList Dc).map fun p => 2 * dtL2 p.1 + 1).sum =
    (tmplTapes.map fun u => 2 * dtL2 u + 1).sum := by
  rw [← tmplList_fst Dc, List.map_map]; rfl

set_option maxRecDepth 100000 in
theorem tmpl_sum_le : (tmplTapes.map fun u => 2 * dtL2 u + 1).sum ≤ 2 ^ 99 := by decide +kernel

/-- The clock of the templates. -/
def fuTmplT : ℕ := 2 ^ 99 * (4 * 2 ^ 109 + 12) + (2 * (2 ^ 109 + 1) + 3)

/-- **The templates.** -/
theorem fu_tmplsDc : VB (tmplsP 250 (tmplList Dc)) (dtPsh (2 ^ 109)) fuTmplT dtL2 := by
  refine (vb_tmplsT (2 ^ 109) dtL2_le dtL2_250 _ _ dtPsh_le_L2 tmpl_ok).mono le_rfl ?_ le_rfl
  rw [tmpl_sum_eq]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ tmpl_sum_le) _

/-! ### The constants -/

/-- The shape after the all-ones word on `43`. -/
def dtL3 : Fin 256 → ℕ := dtFv 0 (2 ^ 109) (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16) dtR2

/-- The shape before the code. -/
def dtL4 : Fin 256 → ℕ :=
  dtFv 0 (2 ^ 109) (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16) (toB dtB0)

set_option maxRecDepth 100000 in
theorem dtB0_3 : toB dtB0 3 = 2 ^ 40 := by decide +kernel

set_option maxRecDepth 100000 in
theorem dtB0_75 : toB dtB0 75 = 1 := by decide +kernel

theorem dtL3_le (t : Fin 256) : dtL3 t ≤ 2 ^ 109 :=
  dtFv_le (Nat.zero_le _) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) dtR2_le t

theorem dtR2_le_B0 (x : Fin 200) : dtR2 x ≤ toB dtB0 x := by
  unfold dtR2
  simp only [Function.update_apply]
  split_ifs with h1 h2
  · exact Nat.zero_le _
  · subst h2; rw [dtB0_3]; omega
  · exact le_rfl

theorem dtL3_le_L4 (t : Fin 256) : dtL3 t ≤ dtL4 t :=
  dtFv_mono le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (dtPile dtR2_le_B0) t

/-- The clock of the constants. -/
def fuConstT : ℕ := ((2 * (2 ^ 109 + 1) + 3) + (2 ^ 24 * 2 ^ 16 * (4 * 2 ^ 109 + 9) + 2)) +
  ((2 * (2 ^ 109 + 1) + 3) + (2 * (2 ^ 109 + 1) + 3))

theorem dtFv43 {Z M a b c d : ℕ} {R : Fin 200 → ℕ} : dtFv Z M a b c d R 43 = d := by
  unfold dtFv; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos (by decide)]

theorem dtFv42 {Z M a b c d : ℕ} {R : Fin 200 → ℕ} : dtFv Z M a b c d R 42 = c := by
  unfold dtFv; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]

/-- **The constants.** -/
theorem fu_constP : VB (.prog DecM.constP) dtL2 fuConstT dtL4 := by
  have h1 : VB (.prog (Tape.Prog.forN 250 42 (.prim (.snoc 43 true)))) dtL2
      ((2 * (2 ^ 109 + 1) + 3) + (2 ^ 24 * 2 ^ 16 * (4 * 2 ^ 109 + 9) + 2)) dtL3 :=
    vb_forN43T dtL2 dtL3 (2 ^ 109) (2 ^ 24 * 2 ^ 16) dtL2_le (by unfold dtL2; rw [dtFv42])
      (by unfold dtL2; rw [dtFv43]) (by norm_num)
      (fun i h43 _ => by
        have h43' : i.val ≠ 43 := fun e => h43 (Fin.ext e)
        unfold dtL2 dtL3 dtFv
        split_ifs <;> exact le_rfl)
      (by unfold dtL3; rw [dtFv43]) (by unfold dtL3; rw [dtFv_high 250 (by decide)]; norm_num)
  have h2 : VB (.prog (.prim (.cons (tR 3) true))) dtL3 (2 * (2 ^ 109 + 1) + 3)
      (Function.update dtL3 (tR 3) (2 ^ 40)) :=
    vbU_prim _ dtL3_le fun t => by
      simp only [Prim.lenT, Function.update_apply]
      split_ifs with h
      · subst h; unfold dtL3; rw [dtFv_reg]; simp [dtR2]
      · exact le_rfl
  have h3 : VB (.prog (.prim (.snoc (tR 75) true))) (Function.update dtL3 (tR 3) (2 ^ 40))
      (2 * (2 ^ 109 + 1) + 3) dtL4 :=
    vbU_prim _ (fun t => by
      rw [Function.update_apply]; split_ifs
      · norm_num
      · exact dtL3_le t) fun t => by
      simp only [Prim.lenT, Function.update_apply]
      by_cases h75 : t = tR 75
      · subst h75; rw [if_pos rfl, if_neg (by decide)]
        unfold dtL3 dtL4; rw [dtFv_reg, dtFv_reg, dtB0_75]; simp [dtR2]
      · rw [if_neg h75]
        by_cases h3 : t = tR 3
        · subst h3; rw [if_pos rfl]; unfold dtL4; rw [dtFv_reg, dtB0_3]
        · rw [if_neg h3]
          exact dtL3_le_L4 t
  exact vb_progSeqT h1 (vb_progSeqT h2 h3)

/-! ### The code -/



theorem dtFv_vmE_le (Z M a b c d Mo N K : ℕ) (R : Fin 200 → ℕ) (hZ : Z ≤ Mo) (ha : a ≤ K) (hb : b ≤ N)
    (hc : c ≤ N * K) (hd : d ≤ N * K) (j : Fin 247) :
    dtFv Z M a b c d R (vmE j) ≤ encB Mo N K R j := by
  have := j.isLt
  have hv : (vmE j).val = j.val := rfl
  unfold dtFv encB
  generalize vmE j = u at hv ⊢
  rcases (show j.val < 40 ∨ j.val = 40 ∨ j.val = 41 ∨ j.val = 42 ∨ j.val = 43 ∨
    (44 ≤ j.val ∧ j.val ≤ 46) ∨ 47 ≤ j.val by omega) with h | h | h | h | h | h | h <;>
  simp (disch := omega) only [_root_.if_pos, _root_.if_neg, _root_.dif_pos, _root_.dif_neg] <;>
  first | exact le_rfl | omega | (apply le_of_eq; congr 1; exact Fin.ext (by simp only; omega))

theorem encB_le_fv (Z M a b c d Mo N K : ℕ) (R : Fin 200 → ℕ) (hZ : Mo ≤ Z) (ha : K ≤ a)
    (hb : N ≤ b) (hc : N * K ≤ c) (hd : N * K ≤ d) (j : Fin 247) :
    encB Mo N K R j ≤ dtFv Z M a b c d R (vmE j) := by
  have := j.isLt
  have hv : (vmE j).val = j.val := rfl
  unfold dtFv encB
  generalize vmE j = u at hv ⊢
  rcases (show j.val < 40 ∨ j.val = 40 ∨ j.val = 41 ∨ j.val = 42 ∨ j.val = 43 ∨
    (44 ≤ j.val ∧ j.val ≤ 46) ∨ 47 ≤ j.val by omega) with h | h | h | h | h | h | h <;>
  simp (disch := omega) only [_root_.if_pos, _root_.if_neg, _root_.dif_pos, _root_.dif_neg] <;>
  first | exact le_rfl | omega | (apply le_of_eq; congr 1; exact Fin.ext (by simp only; omega))

/-- The shape after the code. -/
def dtL5 : Fin 256 → ℕ :=
  dtFv (2 ^ 40) (2 ^ 109) (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16) (toB dtBend)

/-- **The compiled code**, framed on the tapes `0 … 246`. -/
theorem fu_vm : VB (.frame vmE (compile decCode)) dtL4 dtTvm dtL5 := by
  have hv : VB (compile decCode) (fun j => dtL4 (vmE j)) dtTvm
      (encB (2 ^ 40) (2 ^ 24) (2 ^ 16) (toB dtBend)) := fun ℓ hℓ =>
    dt_decCode ℓ fun j => (hℓ j).trans (dtFv_vmE_le _ _ _ _ _ _ _ _ _ _ (Nat.zero_le _) le_rfl
      le_rfl le_rfl le_rfl j)
  refine (VB.frame vmE hv).mono le_rfl le_rfl fun t => ?_
  by_cases ht : t.val < 247
  · have e : t = vmE ⟨t.val, ht⟩ := Fin.ext rfl
    rw [e, embedF_apply_self]
    exact encB_le_fv _ _ _ _ _ _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl le_rfl _
  · rcases embedF_cases vmE dtL4 (encB (2 ^ 40) (2 ^ 24) (2 ^ 16) (toB dtBend)) t with
      ⟨-, h1⟩ | ⟨i, hi, -⟩
    · rw [h1]; unfold dtL4 dtL5; rw [dtFv_high t (by omega), dtFv_high t (by omega)]
    · exact absurd (show t.val < 247 by rw [← hi]; exact i.isLt) ht

/-! ### The output and the invalid branch -/

/-- The final shape: the output tape `0` at most `3` bits, every tape below `2^110`. -/
def dtLfin : Fin 256 → ℕ := fun t => if t = 0 then 3 else 2 ^ 110

set_option maxRecDepth 100000 in
theorem dtBend_le : ∀ x, toB dtBend x ≤ 2 ^ 109 := by decide +kernel

set_option maxRecDepth 100000 in
theorem dtBend_179 : toB dtBend 179 = 1 := by decide +kernel

theorem dtL5_le (t : Fin 256) : dtL5 t ≤ 2 ^ 109 :=
  dtFv_le (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) dtBend_le t

/-- The clock of the output. -/
def fuOutT : ℕ := (2 * (2 ^ 109 + 1) + 3) + ((2 * (2 ^ 109 + 1 + 1) + 3) + (2 * (2 ^ 109 + 2 + 1) + 3))

theorem dtUpd_le {L : Fin 256 → ℕ} {U v : ℕ} (hL : ∀ t, L t ≤ U) (hv : v ≤ U) (s : Fin 256)
    (t : Fin 256) : Function.update L s v t ≤ U := by
  rw [Function.update_apply]; split_ifs
  · exact hv
  · exact hL t

/-- **The output** `[true, b, false]` on tape `0`. -/
theorem fu_outP : VB (.prog DecM.outP) dtL5 fuOutT dtLfin := by
  have hc : (Prim.copy (0 : Fin 256) (tR 179)).lenT dtL5 = Function.update dtL5 0 1 := by
    simp only [Prim.lenT]; unfold dtL5; rw [dtFv_reg, dtBend_179]
  have h1 : VB (.prog (.prim (.copy 0 (tR 179)))) dtL5 (2 * (2 ^ 109 + 1) + 3)
      (Function.update dtL5 0 1) := vbU_prim _ dtL5_le hc.le
  have hb1 : ∀ t, Function.update dtL5 0 1 t ≤ 2 ^ 109 + 1 :=
    dtUpd_le (fun t => (dtL5_le t).trans (by omega)) (by norm_num) 0
  have h2 : VB (.prog (.prim (.cons 0 true))) (Function.update dtL5 0 1) (2 * (2 ^ 109 + 1 + 1) + 3)
      (Function.update dtL5 0 2) := vbU_prim _ hb1 fun t => by
    simp only [Prim.lenT, Function.update_apply]; split_ifs <;> simp_all
  have hb2 : ∀ t, Function.update dtL5 0 2 t ≤ 2 ^ 109 + 2 :=
    dtUpd_le (fun t => (dtL5_le t).trans (by omega)) (by norm_num) 0
  have h3 : VB (.prog (.prim (.snoc 0 false))) (Function.update dtL5 0 2) (2 * (2 ^ 109 + 2 + 1) + 3)
      dtLfin := vbU_prim _ hb2 fun t => by
    simp only [Prim.lenT, Function.update_apply, dtLfin]
    split_ifs with h
    · simp
    · exact (dtL5_le t).trans (by norm_num)
  exact vb_progSeqT h1 (vb_progSeqT h2 h3)

/-- The clock of the invalid branch. -/
def fuInvT : ℕ := (2 * (2 ^ 109 + 1) + 3) + ((2 * (2 ^ 109 + 1 + 1) + 3) + (2 * (2 ^ 109 + 2 + 1) + 3))

/-- **The invalid branch** `[false]` on tape `0`. -/
theorem fu_invP : VB (.prog DecM.invP) (dtPsh (2 ^ 109)) fuInvT dtLfin := by
  have h0 : dtPsh (2 ^ 109) 0 = 0 := dtFv_low 0 (by decide)
  have h1 : VB (.prog (.prim (.snoc 0 true))) (dtPsh (2 ^ 109)) (2 * (2 ^ 109 + 1) + 3)
      (Function.update (dtPsh (2 ^ 109)) 0 1) := vbU_prim _ (dtPsh_le _) fun t => by
    simp only [Prim.lenT, Function.update_apply]; split_ifs with h
    · subst h; rw [h0]
    · exact le_rfl
  have hb1 : ∀ t, Function.update (dtPsh (2 ^ 109)) 0 1 t ≤ 2 ^ 109 + 1 :=
    dtUpd_le (fun t => (dtPsh_le _ t).trans (by omega)) (by norm_num) 0
  have h2 : VB (.prog (.prim (.snoc 0 false))) (Function.update (dtPsh (2 ^ 109)) 0 1)
      (2 * (2 ^ 109 + 1 + 1) + 3) (Function.update (dtPsh (2 ^ 109)) 0 2) := vbU_prim _ hb1 fun t => by
    simp only [Prim.lenT, Function.update_apply]; split_ifs <;> simp_all
  have hb2 : ∀ t, Function.update (dtPsh (2 ^ 109)) 0 2 t ≤ 2 ^ 109 + 2 :=
    dtUpd_le (fun t => (dtPsh_le _ t).trans (by omega)) (by norm_num) 0
  have h3 : VB (.prog (.prim (.snoc 0 false))) (Function.update (dtPsh (2 ^ 109)) 0 2)
      (2 * (2 ^ 109 + 2 + 1) + 3) dtLfin := vbU_prim _ hb2 fun t => by
    simp only [Prim.lenT, Function.update_apply, dtLfin]
    split_ifs with h
    · simp
    · exact (dtPsh_le _ t).trans (by norm_num)
  exact vb_progSeqT h1 (vb_progSeqT h2 h3)

end AdvancedEncryption.ExpLUT.Prog.DecTight
