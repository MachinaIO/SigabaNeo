import PE.Impl.DualUse.Prog.WfTime
import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenTape

/-!
# The `f̂` gate generator (WS-L1)

**`fhatGen hk W : XProg 136`**: the constants of the register machine (`constsP`, with growing
words), then the deterministic `mainP` (gate count, the machine code of `f̂` and of the output
positions, the tapes `1 2 3`).

* `fhatGen_spec`: `GenSpec hk (fhatGen hk W) W (fhatOk hk W)`, with
  `fhatOk hk W gs := WOk N hk W gs ∧ gs ≠ [] ∧ 0 < N`;
* `ub_fhatGen`: `∀ M, UB (fhatGen hk W) M (fhatTg hk W M) (fhatLg hk W M)`, with explicit
  polynomial bounds.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  AdvancedEncryption.DualUse.Algo SigabaNeo.Lattices.FhatGen SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open scoped SigabaNeo.Tape.Prog

/-! ### The input positions of `f̂` -/

section Enum

theorem length_enum_prod {α β : Type} [Enum α] [Enum β] :
    (Enum.list (α := α × β)).length = (Enum.list (α := α)).length * (Enum.list (α := β)).length :=
  List.length_product _ _

theorem enumIx_prod {α β : Type} [Enum α] [DecidableEq α] [Enum β] [DecidableEq β]
    [DecidableEq (α × β)] (a : α) (b : β) :
    enumIx (α := α × β) (a, b) = enumIx a * (Enum.list (α := β)).length + enumIx b := by
  have ha : enumIx a < (Enum.list (α := α)).length := enumIx_lt a
  have hb : enumIx b < (Enum.list (α := β)).length := enumIx_lt b
  have hg := getElem?_product (Enum.list (α := β)) (Enum.list (α := α)) (enumIx a) (enumIx b) ha hb
  have e1 : (Enum.list (α := α))[enumIx a] = a := List.getElem_idxOf ha
  have e2 : (Enum.list (α := β))[enumIx b] = b := List.getElem_idxOf hb
  rw [e1, e2] at hg
  have hnd : (Enum.list (α := α × β)).Nodup := Enum.nodup
  have hg' : (Enum.list (α := α × β))[enumIx a * (Enum.list (α := β)).length + enumIx b]? =
      some (a, b) := hg
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hg'
  unfold enumIx
  have := hnd.idxOf_getElem (enumIx a * (Enum.list (α := β)).length + enumIx b) hlt
  rw [hget] at this
  convert this using 2
  · exact lawful_beq_subsingleton _ _
  all_goals rfl

theorem enumIx_fin {n : ℕ} (i : Fin n) : enumIx i = i.val := List.idxOf_finRange i

end Enum

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k)

theorem length_enum_fin (n : ℕ) : (Enum.list (α := Fin n)).length = n := List.length_finRange

theorem length_enum_BI : (Enum.list (α := (Sdw (N := N) hk).ctBits.Index)).length =
    4 * k * N * k := by
  show (Enum.list (α := Fin 2 × (Fin 2 × Fin k) × Fin k × Fin N)).length = _
  simp only [length_enum_prod]
  repeat erw [length_enum_fin]
  ring

theorem nT_eq : nT N K k hk = 10 * (4 * k * N * k) := by
  show (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length = _
  rw [length_enum_prod, length_enum_BI]; rfl

theorem enumIx_BI (b : BI N k) :
    enumIx (α := Fin 2 × (Fin 2 × Fin k) × Fin k × Fin N) b = codec b := by
  obtain ⟨a, ⟨c1, c2⟩, i', j⟩ := b
  rw [enumIx_prod, enumIx_prod, enumIx_prod, enumIx_prod, enumIx_fin, enumIx_fin, enumIx_fin,
    enumIx_fin, enumIx_fin]
  simp only [length_enum_prod]
  repeat erw [length_enum_fin]
  simp only [codec]
  ring

theorem ixT_eq (i : Fin 10) (b : BI N k) : ixT N K k hk (i, b) = i.val * (4 * k * N * k) + codec b := by
  unfold ixT
  refine (enumIx_prod (α := (Sdw (N := N) hk).Attr) (β := (Sdw (N := N) hk).ctBits.Index) i b).trans ?_
  rw [length_enum_BI]
  congr 1
  · show enumIx (α := Fin 10) i * _ = _
    rw [enumIx_fin]
  · exact enumIx_BI b

theorem ixT_lt (j : Fin 10 × BI N k) : ixT N K k hk j < nT N K k hk := enumIx_lt _

/-! ### The generator -/

variable (N) in
/-- **The `f̂` gate generator.** -/
noncomputable def fhatGen (W : ℕ) : XProg 136 :=
  XProg.seq (constsP N k K W (nT N K k hk)) (XProg.prog mainP)

variable (N) in
/-- The gate lists the generator handles. -/
def fhatOk (W : ℕ) (gs : GateList) : Prop := WOk N hk W gs ∧ gs ≠ [] ∧ 0 < N

theorem wf_itemsPF (f : Fin 136 → ℕ × Bool) : ∀ ts : List (Fin 136), tCnt ∉ ts → (FhatGen.itemsP f ts).WF
  | [], _ => trivial
  | t :: ts, h => by
    have ht : t ≠ tCnt := fun e => h (by simp [e])
    refine ⟨⟨wf_natP (Ne.symm ht) _, ?_⟩, wf_itemsPF f ts (fun e => h (by simp [e]))⟩
    cases (f t).2 <;> trivial

theorem noGrow_seq {p q : Prog 136} (hp : p.NoGrow) (hq : q.NoGrow) : (p ⨾ q).NoGrow := by
  simp only [Prog.NoGrow, Prog.noGrowB, Bool.and_eq_true] at *; exact ⟨hp, hq⟩

theorem noGrow_mainP : mainP.NoGrow := by
  unfold mainP
  refine noGrow_seq ?_ (noGrow_seq ?_ (noGrow_seq ?_ (noGrow_seq ?_ (noGrow_seq ?_
    (noGrow_seq ?_ ?_)))))
  · decide
  · exact Prog.NoGrow.map uV (RegVM.noGrow_compile _ _)
  · decide
  · decide
  · exact Prog.NoGrow.map uV (RegVM.noGrow_compile _ _)
  · decide
  · decide

theorem wf_mainP : mainP.WF :=
  ⟨Prog.wf_of_wfB (by decide), Prog.WF.map uV_inj (RegVM.wf_compile _ _ (by decide)),
    Prog.wf_of_wfB (by decide), Prog.wf_of_wfB (by decide),
    Prog.WF.map uV_inj (RegVM.wf_compile _ _ (by decide)), Prog.wf_of_wfB (by decide),
    Prog.wf_of_wfB (by decide)⟩

theorem posW_fhatPos (W : ℕ) (gs : GateList) :
    Prog.posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) gs (ixT N K k hk) (nT N K k hk)) =
      Prog.posW W N k (fun c i j => pfix (nT N K k hk) (nT N K k hk + 1 + (fhF N k K gs).1.length)
        N k (repList (envG N k W (nT N K k hk)) (ixT N K k hk) (fhF N k K gs).2) c i j) := by
  unfold Prog.posW
  refine concatN_congr fun c hc => concatN_congr fun i hi => concatN_congr fun j hj => ?_
  congr 1
  unfold fhatPos
  rw [dif_pos ⟨hc, hi, hj⟩]
  exact (pfix_repList (E := envG N k W (nT N K k hk)) (ixT N K k hk) (ixT_lt hk) _ _ hc hi hj).symm

/-- **The generator meets the specification.** -/
theorem fhatGen_spec (W : ℕ) : GenSpec N hk (fhatGen N hk W) W (fhatOk N hk W) where
  wf := ⟨wf_itemsPF _ tsC (by decide), wf_mainP⟩
  law gs hok := by
    obtain ⟨hw, hgs, hN⟩ := hok
    have hKk : K < k := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hk
    have hin : genIn W gs = inS W gs := rfl
    rw [fhatGen, XProg.law_seq, hin, law_constsP _ _ _ _ _ _ (fun i hi => by
        simp [inS, show i.val ≠ 0 by omega]),
      PMF.pure_bind, XProg.law_prog_run _ noGrow_mainP,
      run_mainP (by omega) hN (by omega) (ixT N K k hk) (ixT_eq hk) (ixT_lt hk) gs hgs hw.bnd
        hw.hG hw.hT]
    congr 1
    funext j
    simp only [outS, genOut]
    rw [posW_fhatPos]
    rfl

/-! ### The uniform bound -/

variable (N) in
/-- A bound on the words the constants write. -/
def fhatVb (W : ℕ) : ℕ :=
  Pv N k W + Cv N k W * (Mv N k W + 1) + Mv N k W + W + nT N K k hk +
    (nT N K k hk + 1 + K + N + 4 * k * N * k + treeHeight N k + 2 * k * k * N + 4 * k * N +
      2 * k * N + k + 14)

theorem le_ite_fst {c : Prop} [Decidable c] {a b : ℕ × Bool} {V : ℕ} (ha : a.1 ≤ V) (hb : b.1 ≤ V) :
    (if c then a else b).1 ≤ V := by split <;> assumption

theorem valsT_le (W : ℕ) (i : Fin 136) :
    (valsT N k K W (nT N K k hk) i).1 ≤ fhatVb N hk W := by
  have := cst0_le N k K (nT N K k hk) (i.val - 4 - 31)
  unfold valsT valsV fhatVb
  repeat' apply le_ite_fst
  all_goals (try simp only); omega

theorem UB.of_le {p : XProg 136} {M L T M' : ℕ} (h : UB p L T M') (hML : M ≤ L) : UB p M T M' :=
  fun ℓ hℓ => h ℓ (fun i => (hℓ i).trans hML)

theorem ub_itemsPF (f : Fin 136 → ℕ × Bool) (V L : ℕ) (hV : ∀ t, (f t).1 ≤ V) (hVL : V ≤ L) :
    ∀ ts : List (Fin 136), tCnt ∉ ts →
      UB (FhatGen.itemsP f ts) L (ts.length * ((2 * V + 1) * (4 * L + 12) + 3 * (L + 1)) + 3 * (L + 1)) L
  | [], _ => by
    refine ((ub_prog (Prog.nop 0) L).mono ?_ ?_)
    · simp [Prog.nop, Prog.timeBound, Prim.pad]; omega
    · rw [Prog.lenBound_eq (Prog.nop 0) rfl]
  | t :: ts, h => by
    have ht : t ≠ tCnt := fun e => h (by simp [e])
    have h1 := ub_natP (Ne.symm ht) ((hV t).trans hVL)
    have h2 : UB (XProg.prog (if (f t).2 then Prog.prim (.carry oneOp t t) else Prog.nop t)) L
        (3 * (L + 1)) L := by
      cases (f t).2
      · refine ((ub_prog (Prog.nop t) L).mono ?_ ?_)
        · simp [Prog.nop, Prog.timeBound, Prim.pad]; omega
        · rw [Prog.lenBound_eq (Prog.nop t) rfl]
      · refine ((ub_prog (Prog.prim (.carry oneOp t t)) L).mono ?_ ?_)
        · simp [Prog.timeBound, Prim.pad]; omega
        · rw [Prog.lenBound_eq (Prog.prim (.carry oneOp t t)) rfl]
    have h3 := ub_itemsPF f V L hV hVL ts (fun e => h (by simp [e]))
    refine ((h1.seq h2).seq h3).mono ?_ le_rfl
    have : (2 * (f t).1 + 1) * (4 * L + 12) ≤ (2 * V + 1) * (4 * L + 12) :=
      Nat.mul_le_mul_right _ (by have := hV t; omega)
    simp only [List.length_cons]
    nlinarith

variable (N) in
/-- The length bound of the generator from tapes below `M`. -/
def fhatLg (W M : ℕ) : ℕ := max M (fhatVb N hk W)

variable (N) in
/-- The time bound of the generator from tapes below `M`. -/
noncomputable def fhatTg (W M : ℕ) : ℕ :=
  (tsC.length * ((2 * fhatVb N hk W + 1) * (4 * fhatLg N hk W M + 12) + 3 * (fhatLg N hk W M + 1)) +
    3 * (fhatLg N hk W M + 1)) + Prog.tbC mainP * (fhatLg N hk W M + 1) ^ Prog.tbD mainP

/-- **The uniform bound of the generator.** -/
theorem ub_fhatGen (W : ℕ) : ∀ M, UB (fhatGen N hk W) M (fhatTg N hk W M) (fhatLg N hk W M) := by
  intro M
  have hc := ub_itemsPF (valsT N k K W (nT N K k hk)) (fhatVb N hk W) (fhatLg N hk W M)
    (valsT_le hk W) (le_max_right _ _) tsC (by decide)
  have hm : UB (XProg.prog mainP) (fhatLg N hk W M)
      (Prog.tbC mainP * (fhatLg N hk W M + 1) ^ Prog.tbD mainP) (fhatLg N hk W M) :=
    (ub_prog mainP _).mono (Prog.timeBound_le mainP noGrow_mainP _)
      (by rw [Prog.lenBound_eq mainP noGrow_mainP])
  exact UB.of_le (hc.seq hm) (le_max_left _ _)

end AdvancedEncryption.DualUse.Prog
