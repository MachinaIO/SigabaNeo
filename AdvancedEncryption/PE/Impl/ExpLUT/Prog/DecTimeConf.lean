import PE.Impl.ExpLUT.Prog.DecDescConf
import PE.Impl.ExpLUT.Prog.DecTimeUni
/-!
# The clock of the concrete `Dec` machine (package F4)

The per-tape bounds of `decProgram Dc` are tracked by the shape `dtv M a b c d`: the template
tapes `40 … 43` of the ring-word machine at most `a, b, c, d`, its blank scratch `44 … 46` empty,
every other tape at most `M`.

* parsing (four framed unframings, `Prog.ubp_unfrP`) and the length test (`lenEqP_bounds`) are
  framed away from `40 … 46` (`dtv_frame`);
* the templates (`natP` by doubling, `VB.natP`): `K, N, N K` on `40 … 42`, the register
  templates elsewhere (`dtv_tmpls`);
* the constants: `N K` ones on `43` (`dtv_forN43`);
* the compiled code under the uniform cap `2^110` (`DecT.duVM_decCode`, at most `2^726` steps);
* the output and the invalid branch (`dtv_prog`).

**`time_decMachine : decMachine.time ≤ 2 ^ 727`**.
-/

set_option autoImplicit false

namespace AdvancedEncryption.ExpLUT.Prog.DecConf

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM AdvancedEncryption.ExpLUT.Params
open DecM
open SigabaNeo.Tape.XProg

/-! ### The shape of the bounds -/

/-- `a, b, c, d` on the template tapes `40 … 43`, `0` on `44 … 46`, `M` elsewhere. -/
def dtv (M a b c d : ℕ) : Fin 256 → ℕ := fun t =>
  if t.val = 40 then a else if t.val = 41 then b else if t.val = 42 then c
  else if t.val = 43 then d else if 44 ≤ t.val ∧ t.val ≤ 46 then 0 else M

theorem dtv_mono {M a b c d M' a' b' c' d' : ℕ} (hM : M ≤ M') (ha : a ≤ a') (hb : b ≤ b')
    (hc : c ≤ c') (hd : d ≤ d') : dtv M a b c d ≤ dtv M' a' b' c' d' := fun t => by
  simp only [dtv]; split_ifs <;> omega

theorem dtv_le {M a b c d : ℕ} (ha : a ≤ M) (hb : b ≤ M) (hc : c ≤ M) (hd : d ≤ M) (t : Fin 256) :
    dtv M a b c d t ≤ M := by
  simp only [dtv]; split_ifs <;> omega

/-- **A block framed away from `40 … 46`**, from a uniform bound. -/
theorem dtv_frame {m : ℕ} (e : Fin m ↪ Fin 256) (he : ∀ j, (e j).val < 40 ∨ 46 < (e j).val)
    {p : XProg m} {M T M' a b c d : ℕ}
    (h : ∀ ℓ : Fin m → ℕ, (∀ i, ℓ i ≤ M) →
      XProg.timeBoundT p ℓ ≤ T ∧ ∀ i, XProg.lenBoundT p ℓ i ≤ M')
    (hM : M ≤ M') : VB (.frame e p) (dtv M a b c d) T (dtv M' a b c d) := by
  have hv : ∀ j, dtv M a b c d (e j) = M := fun j => by
    have := he j; simp only [dtv]; split_ifs <;> omega
  have h' : VB p (fun j => dtv M a b c d (e j)) T (fun _ => M') := fun ℓ hℓ => by
    have := h ℓ (fun i => (hℓ i).trans (hv i).le)
    exact ⟨this.1, fun i => this.2 i⟩
  refine (VB.frame e h').mono le_rfl le_rfl fun t => ?_
  rcases embedF_cases e (dtv M a b c d) (fun _ => M') t with ⟨-, h1⟩ | ⟨i, rfl, h1⟩
  · rw [h1]; exact dtv_mono hM le_rfl le_rfl le_rfl le_rfl t
  · rw [h1]; have := he i; simp only [dtv]; split_ifs <;> omega

/-- **A program keeping `40 … 46`**, from a uniform bound. -/
theorem dtv_prog (p : Tape.Prog 256) (hp : ∀ t : Fin 256, 40 ≤ t.val → t.val ≤ 46 → p.Preserves t)
    {M T M' a b c d : ℕ} (h : Prog.UBP p M T M') (hM : M ≤ M') (ha : a ≤ M) (hb : b ≤ M)
    (hc : c ≤ M) (hd : d ≤ M) : VB (.prog p) (dtv M a b c d) T (dtv M' a b c d) := by
  intro ℓ hℓ
  have hu : ∀ i, ℓ i ≤ M := fun i => (hℓ i).trans (dtv_le ha hb hc hd i)
  refine ⟨(h ℓ hu).1, fun t => ?_⟩
  show Prog.lenBoundT p ℓ t ≤ _
  by_cases ht : 40 ≤ t.val ∧ t.val ≤ 46
  · rw [Prog.lenBoundT_of_preserves t p (hp t ht.1 ht.2) ℓ]
    exact (hℓ t).trans (dtv_mono hM le_rfl le_rfl le_rfl le_rfl t)
  · refine ((h ℓ hu).2 t).trans ?_
    simp only [dtv]; split_ifs <;> omega

theorem vb_ifBitD {k : ℕ} {i : Fin k} {p q : XProg k} {a b : Fin k → ℕ} {T U : ℕ}
    (hp : VB p a T b) (hq : VB q a U b) : VB (.ifBit i p q) a (max T U + 1) b := fun ℓ hℓ =>
  ⟨by show max _ _ + 1 ≤ _; have := (hp ℓ hℓ).1; have := (hq ℓ hℓ).1; omega,
    fun t => max_le ((hp ℓ hℓ).2 t) ((hq ℓ hℓ).2 t)⟩

theorem vb_progSeqD {k : ℕ} {p q : Tape.Prog k} {a b c : Fin k → ℕ} {T U : ℕ}
    (hp : VB (.prog p) a T b) (hq : VB (.prog q) b U c) :
    VB (.prog (Tape.Prog.seq p q)) a (T + U) c := fun ℓ hℓ => VB.seq hp hq ℓ hℓ

/-! ### Parsing and the length test -/

theorem uI_out (d : Fin 256) (hd : d.val < 40 ∨ 46 < d.val) (j : Fin 4) :
    (uI d j).val < 40 ∨ 46 < (uI d j).val := by
  fin_cases j <;> simp [uI] <;> omega

theorem dtv_unfrX (d : Fin 256) (h : Function.Injective (uI d)) (hd : d.val < 40 ∨ 46 < d.val)
    (M : ℕ) : VB (unfrX d h) (dtv M 0 0 0 0) (Prog.unfrT M) (dtv (2 * M) 0 0 0 0) :=
  dtv_frame _ (uI_out d hd) (fun ℓ hℓ => Prog.ubp_unfrP M ℓ hℓ) (by omega)

theorem dtv_parseX (M : ℕ) : VB parseX (dtv M 0 0 0 0)
    (Prog.unfrT M + (Prog.unfrT (2 * M) + (Prog.unfrT (2 * (2 * M)) +
      (Prog.unfrT (2 * (2 * (2 * M))) + (2 * (2 * (2 * (2 * (2 * M))) + 1) + 3)))))
    (dtv (2 * (2 * (2 * (2 * M)))) 0 0 0 0) :=
  (dtv_unfrX 253 _ (by decide) M).seq ((dtv_unfrX 123 _ (by decide) _).seq
    ((dtv_unfrX 120 _ (by decide) _).seq ((dtv_unfrX 124 _ (by decide) _).seq
      (dtv_prog _ (fun t h1 h2 => by
          simp only [Tape.Prog.Preserves, Prim.writes, List.mem_singleton]
          intro e; subst e; simp at h2)
        (Prog.ubp_prim0 (.clear 253) rfl _) le_rfl (Nat.zero_le _) (Nat.zero_le _)
        (Nat.zero_le _) (Nat.zero_le _)))))

theorem dtv_lenX (S : ℕ) (hS : predLen ≤ S) (h1 : 1 ≤ S) :
    VB lenX (dtv S 0 0 0 0) ((12 * predLen + 6 * S + 120) * (2 * S + 5)) (dtv S 0 0 0 0) :=
  dtv_frame _ (fun j => by fin_cases j <;> simp [lenMap])
    (fun ℓ hℓ => Prog.lenEqP_bounds predLen hS h1 ℓ hℓ) le_rfl

/-! ### The templates -/

/-- **The templates of the register tapes** keep the shape. -/
theorem dtv_tmpls {M a b c d : ℕ} (ha : a ≤ M) (hb : b ≤ M) (hc : c ≤ M) (hd : d ≤ M) :
    ∀ l : List (Fin 256 × ℕ), (∀ p ∈ l, 47 ≤ p.1.val ∧ p.1 ≠ 250 ∧ p.2 ≤ M) →
    VB (tmplsP 250 l) (dtv M a b c d)
      (l.length * ((2 * M + 1) * (4 * M + 12)) + (2 * (M + 1) + 3)) (dtv M a b c d)
  | [], _ => by
    refine (VB.prim (.copy 250 250) (dtv_le ha hb hc hd)).mono le_rfl (by simp) fun t => ?_
    simp [Prim.lenT]
  | p :: l, h => by
    have hp := h p (by simp)
    have h1 := VB.natP (t := p.1) (c := (250 : Fin 256)) (Ne.symm hp.2.1) p.2
      (dtv_le ha hb hc hd) hp.2.2
    have h1' : VB (natP p.1 250 p.2) (dtv M a b c d) ((2 * M + 1) * (4 * M + 12))
        (dtv M a b c d) := by
      refine h1.mono le_rfl (Nat.mul_le_mul_right _ (by omega)) fun t => ?_
      simp only [natB]
      split_ifs with e1 e2
      · subst e1; have := hp.1; simp only [dtv]; split_ifs <;> omega
      · subst e2; refine max_le le_rfl ?_; simp only [dtv]; split_ifs <;> simp_all
      · exact le_rfl
    have ih := dtv_tmpls ha hb hc hd l fun q hq => h q (by simp [hq])
    refine (h1'.seq ih).mono le_rfl ?_ le_rfl
    simp only [List.length_cons, Nat.succ_mul]
    omega

/-- The register templates of `tmplList`, after the three tapes `40 … 42`. -/
theorem tmplList_eq (D : Dims) : tmplList D =
    (40, D.K) :: (41, D.N) :: (42, D.N * D.K) :: (tmplList D).drop 3 := rfl

theorem tmplTapes_drop : ∀ u ∈ tmplTapes.drop 3, 47 ≤ u.val ∧ u ≠ 250 := by decide +kernel

set_option maxRecDepth 10000 in
/-- Every template length is below `2^100` at `Dc`. -/
theorem tmpl_lt100 : ∀ p ∈ tmplList Dc, p.2 < 2 ^ 100 := by
  have hκ : ∀ t, κD Dc t < 2 ^ 100 := fun t =>
    (Nat.mod_lt _ (by positivity)).trans_le (by rw [Dc_N]; norm_num)
  have hρ : ∀ b, ρD Dc.N b < 2 ^ 100 := fun b =>
    (Nat.sub_le _ _).trans_lt (by rw [Dc_N]; norm_num)
  simp only [tmplList, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨⟨?_, fun t _ => hκ t⟩, fun b _ => hρ b⟩
  simp only [dmBC_eq, dmJ_eq, dmJC_eq, dmlen_col, dmDig_eq, dmPos_eq, dmB_eq, len_fin2, famMLen,
    Dc_K, Dc_N, Dc_mb, Dc_b]
  norm_num

theorem tmpl_rest (M : ℕ) (hM : 2 ^ 100 ≤ M) :
    ∀ p ∈ (tmplList Dc).drop 3, 47 ≤ p.1.val ∧ p.1 ≠ 250 ∧ p.2 ≤ M := by
  intro p hp
  have h1 : p.1 ∈ tmplTapes.drop 3 := by
    rw [← tmplList_fst Dc, ← List.map_drop]; exact List.mem_map_of_mem hp
  have h2 := tmpl_lt100 p (List.mem_of_mem_drop hp)
  exact ⟨(tmplTapes_drop _ h1).1, (tmplTapes_drop _ h1).2, by omega⟩

theorem natB_dtv (t : Fin 256) (n M a b c d a' b' c' d' : ℕ) (hn : n ≤ M)
    (h : ∀ i : Fin 256, i ≠ t → i ≠ 250 → dtv M a b c d i ≤ dtv M a' b' c' d' i)
    (ht : n ≤ dtv M a' b' c' d' t) (h250 : dtv M a b c d 250 ≤ M) (ht250 : t ≠ 250) :
    natB t 250 n (dtv M a b c d) ≤ dtv M a' b' c' d' := fun i => by
  simp only [natB]
  split_ifs with e1 e2
  · subst e1; exact ht
  · subst e2; refine max_le ?_ ?_ <;> simp only [dtv] <;> simp at h250 ⊢ <;> omega
  · exact h i e1 e2

/-- **The templates.** -/
theorem dtv_tmplsDc (M : ℕ) (hM : 2 ^ 100 ≤ M) :
    VB (tmplsP 250 (tmplList Dc)) (dtv M 0 0 0 0) (70 * ((2 * M + 1) * (4 * M + 12)) + 2 * M + 5)
      (dtv M (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) 0) := by
  have hK : Dc.K = 2 ^ 16 := Dc_K
  have hN : Dc.N = 2 ^ 24 := Dc_N
  have hM16 : 2 ^ 16 ≤ M := le_trans (by norm_num) hM
  have hM24 : 2 ^ 24 ≤ M := le_trans (by norm_num) hM
  have hM40 : 2 ^ 24 * 2 ^ 16 ≤ M := le_trans (by norm_num) hM
  rw [tmplList_eq, hK, hN]
  have hlen : ((tmplList Dc).drop 3).length = 67 := by
    rw [List.length_drop, length_tmplList]
  have hr := dtv_tmpls hM16 hM24 hM40 (Nat.zero_le M) _ (tmpl_rest M hM)
  rw [hlen] at hr
  have n40 := (VB.natP (t := (40 : Fin 256)) (c := (250 : Fin 256)) (by decide) (2 ^ 16)
    (dtv_le (M := M) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)) hM16).mono
    le_rfl le_rfl (natB_dtv 40 (2 ^ 16) M 0 0 0 0 (2 ^ 16) 0 0 0 hM16
      (fun i h1 _ => by simp only [dtv]; split_ifs <;> simp_all [Fin.ext_iff])
      (by simp [dtv]) (by simp [dtv]) (by decide))
  have n41 := (VB.natP (t := (41 : Fin 256)) (c := (250 : Fin 256)) (by decide) (2 ^ 24)
    (dtv_le (M := M) hM16 (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)) hM24).mono
    le_rfl le_rfl (natB_dtv 41 (2 ^ 24) M (2 ^ 16) 0 0 0 (2 ^ 16) (2 ^ 24) 0 0 hM24
      (fun i h1 _ => by simp only [dtv]; split_ifs <;> simp_all [Fin.ext_iff])
      (by simp [dtv]) (by simp [dtv]) (by decide))
  have n42 := (VB.natP (t := (42 : Fin 256)) (c := (250 : Fin 256)) (by decide) (2 ^ 24 * 2 ^ 16)
    (dtv_le (M := M) hM16 hM24 (Nat.zero_le _) (Nat.zero_le _)) hM40).mono
    le_rfl le_rfl (natB_dtv 42 (2 ^ 24 * 2 ^ 16) M (2 ^ 16) (2 ^ 24) 0 0 (2 ^ 16) (2 ^ 24)
      (2 ^ 24 * 2 ^ 16) 0 hM40
      (fun i h1 _ => by simp only [dtv]; split_ifs <;> simp_all [Fin.ext_iff])
      (by simp [dtv]) (by simp [dtv]) (by decide))
  refine (n40.seq (n41.seq (n42.seq hr))).mono le_rfl ?_ le_rfl
  have a1 : (2 * 2 ^ 16 + 1) * (4 * M + 12) ≤ (2 * M + 1) * (4 * M + 12) :=
    Nat.mul_le_mul_right _ (by omega)
  have a2 : (2 * 2 ^ 24 + 1) * (4 * M + 12) ≤ (2 * M + 1) * (4 * M + 12) :=
    Nat.mul_le_mul_right _ (by omega)
  have a3 : (2 * (2 ^ 24 * 2 ^ 16) + 1) * (4 * M + 12) ≤ (2 * M + 1) * (4 * M + 12) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ### The constants -/

theorem dt_iter_snoc {k : ℕ} (c r : Fin k) (hcr : c ≠ r) (b : Bool) (L : Fin k → ℕ) :
    ∀ j, (Tape.Prog.loopStepT c (.prim (.snoc r b)))^[j] L ≤ Function.update L r (L r + j)
  | 0 => fun i => by simp
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    refine (Tape.Prog.loopStepT_mono c _ (dt_iter_snoc c r hcr b L j)).trans fun i => ?_
    simp only [Tape.Prog.loopStepT, Tape.Prog.lenBoundT, Prim.lenT, Tape.tailB,
      Function.update_apply]
    split_ifs <;> simp_all <;> omega

/-- **`N K` ones on `43`.** -/
theorem dtv_forN43 (M a b c : ℕ) (hc : c ≤ M) (ha : a ≤ M) (hb : b ≤ M) :
    VB (.prog (Tape.Prog.forN 250 42 (.prim (.snoc 43 true)))) (dtv M a b c 0)
      ((2 * (M + 1) + 3) + (c * (4 * M + 9) + 2)) (dtv M a b c c) := by
  intro ℓ hℓ
  have hu : ∀ i, ℓ i ≤ M := fun i => (hℓ i).trans (dtv_le ha hb hc (Nat.zero_le _) i)
  set ℓ1 := Prim.lenT (.copy (250 : Fin 256) 42) ℓ with hℓ1
  have e1 : ℓ1 = Function.update ℓ 250 (ℓ 42) := rfl
  have h42 : ℓ 42 ≤ c := by have := hℓ 42; simpa [dtv] using this
  have h43 : ℓ 43 = 0 := by have := hℓ 43; simp [dtv] at this; omega
  have hit := dt_iter_snoc (k := 256) 250 43 (by decide) true ℓ1
  have hbnd : ∀ j, j ≤ ℓ1 250 → ∀ i,
      ((Tape.Prog.loopStepT 250 (.prim (.snoc 43 true)))^[j] ℓ1) i ≤ M := by
    intro j hj i
    refine (hit j i).trans ?_
    have hj' : j ≤ c := by rw [e1, Function.update_self] at hj; omega
    simp only [e1, Function.update_apply]
    split_ifs <;> simp_all <;> omega
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
      · have : ℓ1 250 ≤ c := by rw [e1, Function.update_self]; exact h42
        have : ℓ1 250 * (4 * M + 8 + 1) ≤ c * (4 * M + 9) := Nat.mul_le_mul this (by omega)
        omega
  · show Tape.Prog.lenBoundT (.loop 250 (.prim (.snoc 43 true))) ℓ1 ≤ _
    refine Tape.iterSupT_le fun j hj i => (hit j i).trans ?_
    have hj' : j ≤ c := by rw [e1, Function.update_self] at hj; omega
    have hi := hℓ i
    by_cases h1 : i = 43
    · subst h1
      rw [Function.update_self, e1, Function.update_of_ne (by decide), h43]
      simp [dtv]; omega
    · rw [Function.update_of_ne h1, e1]
      by_cases h2 : i = 250
      · subst h2; rw [Function.update_self]; simp [dtv]; omega
      · rw [Function.update_of_ne h2]
        exact hi.trans (dtv_mono le_rfl le_rfl le_rfl le_rfl (Nat.zero_le c) i)

theorem pres_tR (x : Fin 200) (t : Fin 256) (h : t.val ≤ 46) : tR x ≠ t := fun e => by
  have := congrArg Fin.val e; simp [tR] at this; omega

/-- **The constants.** -/
theorem dtv_constP (M a b c : ℕ) (hc : c ≤ M) (ha : a ≤ M) (hb : b ≤ M) :
    VB (.prog constP) (dtv M a b c 0)
      ((2 * (M + 1) + 3) + (c * (4 * M + 9) + 2) + ((2 * (M + 1) + 3) + (2 * (M + 1 + 1) + 3)))
      (dtv (M + 2) a b c c) := by
  have h1 := dtv_forN43 M a b c hc ha hb
  have h2 : VB (.prog (.prim (.cons (tR 3) true))) (dtv M a b c c) (2 * (M + 1) + 3)
      (dtv (M + 1) a b c c) := dtv_prog (.prim (.cons (tR 3) true)) (fun t _ h => by
      simp only [Tape.Prog.Preserves, Prim.writes, List.mem_singleton]
      exact fun e => pres_tR 3 t h e.symm)
    (Prog.ubp_prim (.cons (tR 3) true) M) (by omega) ha hb hc hc
  have h3 : VB (.prog (.prim (.snoc (tR 75) true))) (dtv (M + 1) a b c c)
      (2 * (M + 1 + 1) + 3) (dtv (M + 2) a b c c) := dtv_prog (.prim (.snoc (tR 75) true)) (fun t _ h => by
      simp only [Tape.Prog.Preserves, Prim.writes, List.mem_singleton]
      exact fun e => pres_tR 75 t h e.symm)
    (Prog.ubp_prim (.snoc (tR 75) true) (M + 1)) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact vb_progSeqD h1 (vb_progSeqD h2 h3)

/-! ### The compiled code -/

set_option linter.deprecated false in
theorem dtv_vmE (M : ℕ) (j : Fin 247) :
    dtv M (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16) (vmE j) =
      encB M (2 ^ 24) (2 ^ 16) (fun _ => M) j := by
  have := j.isLt
  unfold dtv encB
  rw [show (vmE j).val = j.val from rfl]
  rcases (show j.val < 40 ∨ j.val = 40 ∨ j.val = 41 ∨ j.val = 42 ∨ j.val = 43 ∨
    (44 ≤ j.val ∧ j.val ≤ 46) ∨ 47 ≤ j.val by omega) with h | h | h | h | h | h | h <;>
  simp (disch := omega) only [_root_.if_pos, _root_.if_neg, _root_.dif_pos, _root_.dif_neg]

theorem dtv_vm : VB (.frame vmE (compile decCode))
    (dtv DecT.duM (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16)) (2 ^ 726)
    (dtv DecT.duM (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16)) := by
  have hE : (fun j => dtv DecT.duM (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16) (vmE j)) ≤
      encB DecT.duM (2 ^ 24) (2 ^ 16) (fun _ => DecT.duM) := fun j => (dtv_vmE _ j).le
  have hv : VB (compile decCode) (encB DecT.duM (2 ^ 24) (2 ^ 16) (fun _ => DecT.duM)) (2 ^ 726)
      (encB DecT.duM (2 ^ 24) (2 ^ 16) (fun _ => DecT.duM)) := fun ℓ hℓ =>
    ⟨((XProg.timeBoundT_mono _) hℓ).trans DecT.duVM_decCode.1,
      ((XProg.lenBoundT_mono _) hℓ).trans DecT.duVM_decCode.2⟩
  refine (VB.frame vmE (hv.mono hE le_rfl le_rfl)).mono le_rfl le_rfl fun t => ?_
  rcases embedF_cases vmE (dtv DecT.duM (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16))
    (encB DecT.duM (2 ^ 24) (2 ^ 16) (fun _ => DecT.duM)) t with ⟨-, h1⟩ | ⟨i, rfl, h1⟩
  · rw [h1]
  · rw [h1]; exact (dtv_vmE _ i).ge

/-! ### The output -/

theorem dtv_outP (M a b c d : ℕ) (ha : a ≤ M) (hb : b ≤ M) (hc : c ≤ M) (hd : d ≤ M) :
    VB (.prog DecM.outP) (dtv M a b c d)
      ((2 * (M + 1) + 3) + ((2 * (M + 1) + 3) + (2 * (M + 1 + 1) + 3))) (dtv (M + 2) a b c d) :=
  dtv_prog _ (fun t h0 _ => by
      simp only [DecM.outP, Prog.cp, Tape.Prog.Preserves, Prim.writes, List.mem_singleton]
      refine ⟨?_, ?_, ?_⟩ <;> intro e <;> subst e <;> simp at h0)
    ((Prog.ubp_prim0 (.copy 0 (tR 179)) rfl M).seq ((Prog.ubp_prim (.cons 0 true) M).seq
      (Prog.ubp_prim (.snoc 0 true) (M + 1))) |>.mono le_rfl le_rfl) (by omega) ha hb hc hd

theorem dtv_invP (M : ℕ) :
    VB (.prog invP) (dtv M 0 0 0 0)
      ((2 * (M + 1) + 3) + ((2 * (M + 1 + 1) + 3) + (2 * (M + 1 + 1 + 1) + 3)))
      (dtv (M + 1 + 1 + 1) 0 0 0 0) :=
  dtv_prog _ (fun t h0 _ => by
      simp only [invP, Tape.Prog.Preserves, Prim.writes, List.mem_singleton]
      refine ⟨?_, ?_, ?_⟩ <;> intro e <;> subst e <;> simp at h0)
    ((Prog.ubp_prim (.snoc 0 true) M).seq ((Prog.ubp_prim (.snoc 0 false) (M + 1)).seq
      (Prog.ubp_prim (.snoc 0 false) (M + 1 + 1)))) (by omega) (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) (Nat.zero_le _)

/-! ### The input length -/

theorem dtKcol_len (D : Dims) : (Enum.list (α := KColt D)).length =
    2 ^ D.b * (D.mb + D.K) + (2 ^ D.b * (D.b * 2 * (2 * D.K)) + 2 * D.K) := by
  simp only [KColt, KCol, enum_sum, List.length_append, List.length_map, length_enum_prod,
    enum_fin, List.length_finRange]

theorem dtSk_len (D : Dims) : dfixLen (skEnc D) =
    (dm2 * (dmBC D * (D.N * D.K)) + (dmJ D * (dm2 * (dmCol D * (D.N * D.K))) +
      (dmPos * (dmCol D * (D.N * D.K)) + (dm2 * (dmCol D * (D.N * D.K)) +
      (dmPos * (dmDig D * (dm2 * (dmCol D * (D.N * D.K)))) +
      (dmB D * (dmDig D * (dm2 * (dmCol D * (D.N * D.K)))) + dm2 * (D.N * D.K))))))) +
    (Enum.list (α := KColt D)).length * (D.N * D.K) := rfl

theorem dtCt_len (D : Dims) : dfixLen (ctEnc D) =
    dmBC D * (D.N * D.K) + (dmJ D * (dmCol D * (D.N * D.K)) +
      (dmB D * (dmDig D * (dmCol D * (D.N * D.K))) + (dmPos * (dmCol D * (D.N * D.K)) +
      (dmPos * (dmDig D * (dmCol D * (D.N * D.K))) + (dmCol D * (D.N * D.K) + D.N * D.K))))) := rfl

set_option maxRecDepth 10000 in
theorem dtPw_len : pwW.length ≤ 2 ^ 11 := by decide +kernel

theorem dtSk_le : dfixLen (skEnc Dc) ≤ 7 * 2 ^ 101 := by
  rw [dtSk_len, dtKcol_len, dmBC_eq, dmJ_eq, dmlen_col, dmDig_eq, dmPos_eq, dmB_eq, len_fin2, Dc_K,
    Dc_N, Dc_mb, Dc_b]
  norm_num

theorem dtCt_le : dfixLen (ctEnc Dc) ≤ 2 ^ 100 := by
  rw [dtCt_len, dmBC_eq, dmJ_eq, dmlen_col, dmDig_eq, dmPos_eq, dmB_eq, Dc_K, Dc_N, Dc_mb, Dc_b]
  norm_num

theorem dtInput_arith (a b c d : ℕ) (ha : a ≤ 2 ^ 11) (hb : b ≤ 7 * 2 ^ 101) (hc : c ≤ 2 ^ 31)
    (hd : d ≤ 2 ^ 100) : (2 * a + 1) + (2 * b + 1) + (2 * c + 1) + (2 * d + 1) ≤ 2 ^ 105 := by
  have : (2 * 2 ^ 11 + 1) + (2 * (7 * 2 ^ 101) + 1) + (2 * 2 ^ 31 + 1) + (2 * 2 ^ 100 + 1) ≤
    (2 : ℕ) ^ 105 := by norm_num
  omega

theorem dtInput_gen (D : Dims) (L : ℕ) (ha : pwW.length ≤ 2 ^ 11)
    (hb : dfixLen (skEnc D) ≤ 7 * 2 ^ 101) (hc : L ≤ 2 ^ 31)
    (hd : dfixLen (ctEnc D) ≤ 2 ^ 100) : decInputLength D L ≤ 2 ^ 105 := by
  unfold decInputLength
  exact dtInput_arith _ _ _ _ ha hb hc hd

/-- **The input is at most `2^105` bits long.** -/
theorem dtInput_le : decInputLength Dc predLen ≤ 2 ^ 105 :=
  dtInput_gen Dc predLen dtPw_len dtSk_le (by norm_num [predLen]) dtCt_le

/-! ### The whole program -/

/-- The clock of the valid branch. -/
def dtValidT : ℕ :=
  (70 * ((2 * 2 ^ 109 + 1) * (4 * 2 ^ 109 + 12)) + 2 * 2 ^ 109 + 5) +
    (((2 * (2 ^ 109 + 1) + 3) + ((2 ^ 24 * 2 ^ 16) * (4 * 2 ^ 109 + 9) + 2) +
      ((2 * (2 ^ 109 + 1) + 3) + (2 * (2 ^ 109 + 1 + 1) + 3))) +
    (2 ^ 726 + ((2 * (DecT.duM + 1) + 3) + ((2 * (DecT.duM + 1) + 3) +
      (2 * (DecT.duM + 1 + 1) + 3)))))

/-- The clock of the program. -/
def dtProgT : ℕ :=
  (Prog.unfrT (2 ^ 105) + (Prog.unfrT (2 * 2 ^ 105) + (Prog.unfrT (2 * (2 * 2 ^ 105)) +
      (Prog.unfrT (2 * (2 * (2 * 2 ^ 105))) + (2 * (2 * (2 * (2 * (2 * 2 ^ 105))) + 1) + 3))))) +
    (((12 * predLen + 6 * 2 ^ 109 + 120) * (2 * 2 ^ 109 + 5)) +
      (max dtValidT ((2 * (2 ^ 109 + 1) + 3) + ((2 * (2 ^ 109 + 1 + 1) + 3) +
        (2 * (2 ^ 109 + 1 + 1 + 1) + 3))) + 1))

/-- **The per-tape bounds of the `Dec` program.** -/
theorem dtv_decProgram : VB (decProgram Dc) (dtv (2 ^ 105) 0 0 0 0) dtProgT
    (dtv (DecT.duM + 2) (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16)) := by
  have hp := (dtv_parseX (2 ^ 105)).mono le_rfl le_rfl
    (dtv_mono (M' := 2 ^ 109) (by norm_num) le_rfl le_rfl le_rfl le_rfl)
  have hl := dtv_lenX (2 ^ 109) (by norm_num [predLen]) (by norm_num)
  have ht := dtv_tmplsDc (2 ^ 109) (by norm_num)
  have hc := (dtv_constP (2 ^ 109) (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (by norm_num) (by norm_num)
    (by norm_num)).mono le_rfl le_rfl (dtv_mono (M' := DecT.duM) (by norm_num) le_rfl le_rfl le_rfl
      le_rfl)
  have ho := dtv_outP DecT.duM (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hv : VB (validP Dc) (dtv (2 ^ 109) 0 0 0 0) dtValidT
      (dtv (DecT.duM + 2) (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16)) :=
    ht.seq (hc.seq (dtv_vm.seq ho))
  have hi := (dtv_invP (2 ^ 109)).mono le_rfl le_rfl
    (dtv_mono (M' := DecT.duM + 2) (a' := 2 ^ 16) (b' := 2 ^ 24) (c' := 2 ^ 24 * 2 ^ 16)
      (d' := 2 ^ 24 * 2 ^ 16) (by norm_num) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      (Nat.zero_le _))
  exact hp.seq (hl.seq (vb_ifBitD hv hi))

set_option exponentiation.threshold 2000 in
theorem dtValidT_le : dtValidT ≤ 2 ^ 726 + 2 ^ 230 := by
  unfold dtValidT DecT.duM; norm_num

set_option exponentiation.threshold 2000 in
theorem dt_unfrT_le (M : ℕ) (hM : M ≤ 2 ^ 109) : Prog.unfrT M ≤ 2 ^ 225 := by
  unfold Prog.unfrT
  have h : M * (2 * (M + 1 * M) + 3 + (4 * (2 * (M + 1 * M + 2) + 3) + 2) + 1) ≤
      2 ^ 109 * (2 * (2 ^ 109 + 1 * 2 ^ 109) + 3 + (4 * (2 * (2 ^ 109 + 1 * 2 ^ 109 + 2) + 3) + 2)
        + 1) := by gcongr
  have : 2 ^ 109 * (2 * (2 ^ 109 + 1 * 2 ^ 109) + 3 + (4 * (2 * (2 ^ 109 + 1 * 2 ^ 109 + 2) + 3) + 2)
        + 1) + 2 ^ 112 ≤ (2 : ℕ) ^ 225 := by norm_num
  have : M ≤ 2 ^ 112 := hM.trans (by norm_num)
  omega

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem dtProgT_le : dtProgT ≤ 2 ^ 726 + 2 ^ 240 := by
  have h1 := dt_unfrT_le (2 ^ 105) (by norm_num)
  have h2 := dt_unfrT_le (2 * 2 ^ 105) (by norm_num)
  have h3 := dt_unfrT_le (2 * (2 * 2 ^ 105)) (by norm_num)
  have h4 := dt_unfrT_le (2 * (2 * (2 * 2 ^ 105))) (by norm_num)
  have hv := dtValidT_le
  have hp : predLen ≤ 2 ^ 31 := by norm_num [predLen]
  have hl : (12 * predLen + 6 * 2 ^ 109 + 120) * (2 * 2 ^ 109 + 5) ≤ (2 : ℕ) ^ 225 :=
    (Nat.mul_le_mul_right _ (show 12 * predLen + 6 * 2 ^ 109 + 120 ≤ 2 ^ 113 by
      norm_num [predLen])).trans
      (by norm_num)
  have hm : max dtValidT ((2 * (2 ^ 109 + 1) + 3) + ((2 * (2 ^ 109 + 1 + 1) + 3) +
      (2 * (2 ^ 109 + 1 + 1 + 1) + 3))) ≤ 2 ^ 726 + 2 ^ 230 := max_le hv (by norm_num)
  have h5 : (2 * (2 * (2 * (2 * (2 * 2 ^ 105))) + 1) + 3) ≤ (2 : ℕ) ^ 225 := by norm_num
  unfold dtProgT
  have : (2 : ℕ) ^ 225 * 6 + 2 ^ 230 + 1 ≤ 2 ^ 240 := by norm_num
  linarith

theorem inputBound_le_dtv (n : ℕ) (hn : n ≤ 2 ^ 105) :
    Prog.inputBound (255 : Fin 256) n ≤ dtv (2 ^ 105) 0 0 0 0 := fun t => by
  simp only [Prog.inputBound, Function.update_apply]
  split_ifs with h
  · subst h; simpa [dtv] using hn
  · exact Nat.zero_le _

/-- The clock of a program from the shape bounds (the input length abstract). -/
theorem dt_total {p : XProg 256} {n T : ℕ} (hn : n ≤ 2 ^ 105)
    (h : VB p (dtv (2 ^ 105) 0 0 0 0) T
      (dtv (DecT.duM + 2) (2 ^ 16) (2 ^ 24) (2 ^ 24 * 2 ^ 16) (2 ^ 24 * 2 ^ 16))) :
    XProg.totalTimeT p 255 0 n ≤ (2 * 2 ^ 105 + 2) + T + (2 * (DecT.duM + 2) + 2) := by
  have hb := h _ (inputBound_le_dtv n hn)
  have h0 : XProg.lenBoundT p (Prog.inputBound 255 n) 0 ≤ DecT.duM + 2 :=
    (hb.2 0).trans (by simp [dtv])
  unfold XProg.totalTimeT
  have := hb.1
  omega

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
/-- **The clock of the concrete `Dec` machine.** -/
theorem time_decMachine : decMachine.time ≤ 2 ^ 727 := by
  rw [decMachine, time_decMP]
  refine (dt_total dtInput_le dtv_decProgram).trans ?_
  have hT := dtProgT_le
  have : (2 * 2 ^ 105 + 2) + (2 ^ 726 + 2 ^ 240) + (2 * (DecT.duM + 2) + 2) ≤ (2 : ℕ) ^ 727 := by
    norm_num
  linarith

end AdvancedEncryption.ExpLUT.Prog.DecConf
