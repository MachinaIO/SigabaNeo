import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenRepOf

/-!
# Generating gate tapes: the whole compiler

`compileStepC`: read the two wire indices of a source gate (`rdsrc`), their representations into
the lists `10`, `11` (`repOfC`), the NAND block (`blockC`), its output appended to the list `22`
of all block outputs (a copy of the last one kept in `23`). `fhatC`: the gate `0` (`NAND(1, 1)`),
then one step per source gate (`|63|` of them). `exec_fhatC`: the program is `fhatSLPL` of
`predOf 10 gs`, the list `23` the representation list of its output.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {E : Env}

/-- One source gate. -/
def compileStepC : Code :=
  .seq (.seq (.rdsrc 60) (repOfC 10)) (.seq (.seq (.rdsrc 60) (repOfC 11)) (.seq blockC
    (.seq (.lmov 23 21) (.seq (takeC 10 21 22) (.inc 59)))))

/-- All the constant registers: `CstK`, `10 = B`, `13 = 1`, `14 = 11`. -/
def AllC (N k K : ℕ) (σ : St) : Prop :=
  CstK (E := E) N k K σ ∧ σ.sc 10 = 4 * k * N * k ∧ σ.sc 13 = 1 ∧ σ.sc 14 = 11

theorem allC_of {N k K : ℕ} {σ τ : St} (h : AllC (E := E) N k K σ)
    (hf : ∀ r : SR, r.val < 16 → τ.sc r = σ.sc r) : AllC (E := E) N k K τ := by
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2, h3, h4⟩, h5, h6, h7⟩, h8, h9, h11⟩, h12⟩, h10, h13, h14⟩ := h
  exact ⟨⟨⟨⟨⟨⟨by rw [hf 0 (by decide), h0], by rw [hf 1 (by decide), h1]⟩,
    by rw [hf 2 (by decide), h2], by rw [hf 3 (by decide), h3], by rw [hf 4 (by decide), h4]⟩,
    by rw [hf 5 (by decide), h5], by rw [hf 6 (by decide), h6], by rw [hf 7 (by decide), h7]⟩,
    by rw [hf 8 (by decide), h8], by rw [hf 9 (by decide), h9], by rw [hf 11 (by decide), h11]⟩,
    by rw [hf 12 (by decide), h12]⟩, by rw [hf 10 (by decide), h10], by rw [hf 13 (by decide), h13],
    by rw [hf 14 (by decide), h14]⟩

theorem AllC.rq {N k K : ℕ} {σ : St} (h : AllC (E := E) N k K σ) : RQ (E := E) k K N σ :=
  ⟨⟨h.1.1.1.1, h.1.1.1.2⟩, h.2.1, h.1.2, h.2.2.1, h.2.2.2⟩

/-- Codes that never read the source. -/
def NoRd : Code → Prop
  | .rdsrc _ => False
  | .seq p q | .ifLt _ _ p q => NoRd p ∧ NoRd q
  | .rep _ body => NoRd body
  | _ => True

theorem src_exec : ∀ (c : Code), NoRd c → ∀ σ : St, (exec E c σ).src = σ.src
  | .rdsrc _, h, _ => h.elim
  | .nand _ _ _, _, _ | .one _, _, _ | .zero _, _, _ | .mov _ _, _, _ | .inc _, _, _
  | .add _ _, _, _ | .sub _ _, _, _ | .lnil _, _, _ | .lpush _ _, _, _ | .lpop _ _, _, _
  | .lmov _ _, _, _ | .skip, _, _ => rfl
  | .seq p q, h, σ => by rw [exec_seq, src_exec q h.2, src_exec p h.1]
  | .ifLt a b p q, h, σ => by
    simp only [exec]; split_ifs
    · exact src_exec p h.1 σ
    · exact src_exec q h.2 σ
  | .rep a body, h, σ => by
    simp only [exec]
    generalize σ.sc a = m
    induction m generalizing σ with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply, ih, src_exec body h]

theorem noRd_repOfC (tgt : LR) : NoRd (repOfC tgt) := by
  simp [NoRd, repOfC, inRepC, constRepC, oLoop, inBody, valC, cBody, maddC, sliceC, dropC,
    takeC, constC, gvBody, odoO]

theorem noNand_repOfC (tgt : LR) : NoNand (repOfC tgt) := by
  simp [NoNand, repOfC, inRepC, constRepC, oLoop, inBody, valC, cBody, maddC, sliceC, dropC,
    takeC, constC, gvBody, odoO]

/-- `σ` with new registers, lists and source. -/
def setSLS (σ : St) (sc : SR → ℕ) (ls : LR → List ℕ) (src : List ℕ) : St :=
  { σ with sc := sc, ls := ls, src := src }

/-- The bounds a source gate needs. -/
structure StepB (E : Env) (N k : ℕ) (g : ℕ) : Prop where
  hk : 0 < k
  hN : 0 < N
  hbig : 4 * k * N * k + 2 * N + k + 2 ≤ E.M
  hrep : (g + 11) * (4 * k * N * k) + 4 * k * N + 2 ≤ E.M
  hcap : (2 * k * N + 1) * k ≤ E.C
  hcap' : k + 3 ≤ E.C
  hcapB : 4 * k * N * k ≤ E.C
  hcapR : g * (4 * k * N * k) ≤ E.C
  hgM : g + 1 ≤ E.M

set_option maxHeartbeats 4000000 in
theorem exec_compileStepC (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) {N k K : ℕ} (hK : K ≤ k + 1)
    (ix' : Fin 10 × BI N k → ℕ) (hix : ∀ i b, ix' (i, b) = i.val * (4 * k * N * k) + codec b)
    (hixn : ∀ j, ix' j < E.n) {g : ℕ} (hb : StepB E N k g)
    (reps : List (BI N k → Wire (Fin 10 × BI N k))) (hreps : reps.length < g)
    (P : SLP (Fin 10 × BI N k)) (a b : ℕ) (rest : List ℕ) (σ : St)
    (hc : AllC (E := E) N k K σ) (hI : Inv E σ) (hS : ScOK E σ) (hsrc : σ.src = a :: b :: rest)
    (h59 : σ.sc 59 = reps.length) (h22 : σ.ls 22 = (reps.map (repList E ix')).flatten)
    (hM : E.n + (exec E compileStepC (mk E ix' P σ)).t ≤ E.M) :
    ∃ sc' ls', exec E compileStepC (mk E ix' P σ) =
        mk E ix' (compileStepL (ordT₀ N k) (ordO₀ N k) (gvExp (2 ^ K)) (.gate 0) (2 ^ K) (P, reps)
          ⟨ofIdx 10 a, ofIdx 10 b⟩).1 (setSLS σ sc' ls' rest) ∧
      ls' 22 = ((compileStepL (ordT₀ N k) (ordO₀ N k) (gvExp (2 ^ K)) (.gate 0) (2 ^ K) (P, reps)
          ⟨ofIdx 10 a, ofIdx 10 b⟩).2.map (repList E ix')).flatten ∧
      ls' 23 = repList E ix' ((compileStepL (ordT₀ N k) (ordO₀ N k) (gvExp (2 ^ K)) (.gate 0)
          (2 ^ K) (P, reps) ⟨ofIdx 10 a, ofIdx 10 b⟩).2.getLast?.getD fun _ => .one) ∧
      sc' 59 = reps.length + 1 ∧
      (∀ r : SR, r.val < 16 ∨ r.val = 63 → sc' r = σ.sc r) := by
  have hnM' : E.n ≤ E.M := by omega
  have nv : ∀ (r : SR) (c : ℕ), r.val ≠ c → ∀ d : SR, d.val = c → r ≠ d :=
    fun r c h d hd e => h (by rw [e, hd])
  have hrep' : (reps.length + 11) * (4 * k * N * k) + 4 * k * N + 2 ≤ E.M := by
    have := Nat.mul_le_mul_right (4 * k * N * k) (show reps.length + 11 ≤ g + 11 by omega)
    have := hb.hrep; omega
  -- read `a`, its representation into `10`
  set σ1 : St := setSLS σ (Function.update σ.sc 60 a) σ.ls (b :: rest)
  have e1 : exec E (.rdsrc 60) σ = σ1 := by simp [exec, σ1, setSLS, hsrc]
  have hI1 : Inv E σ1 := by have := inv_exec E (.rdsrc 60) σ hI; rwa [e1] at this
  have hs1 : ∀ r : SR, r ≠ 60 → σ1.sc r = σ.sc r := fun r h => by
    simp [σ1, setSLS, Function.update_of_ne h]
  have hc1 : AllC (E := E) N k K σ1 := allC_of hc (fun r hr => hs1 r (nv r 60 (by omega) 60 rfl))
  obtain ⟨d2, q2, hI2, f2, g2⟩ := exec_repOfC (E := E) hnM hb.hk hb.hN ix' hix 10 (by decide) reps a
    σ1 hc1.rq hI1 (by simp [σ1, setSLS]) (by rw [hs1 59 (by decide), h59])
    (by simp [σ1, setSLS, h22]) hrep' hb.hcapB
  set σ2 := exec E (repOfC 10) σ1
  -- read `b`, its representation into `11`
  have hsrc2 : σ2.src = b :: rest := by rw [src_exec _ (noRd_repOfC 10)]; rfl
  set σ3 : St := setSLS σ2 (Function.update σ2.sc 60 b) σ2.ls rest
  have e3 : exec E (.rdsrc 60) σ2 = σ3 := by simp [exec, σ3, setSLS, hsrc2]
  have hI3 : Inv E σ3 := by have := inv_exec E (.rdsrc 60) σ2 hI2; rwa [e3] at this
  have hs3 : ∀ r : SR, r ≠ 60 → σ3.sc r = σ2.sc r := fun r h => by
    simp [σ3, setSLS, Function.update_of_ne h]
  have hc3 : AllC (E := E) N k K σ3 := allC_of hc (fun r hr => by
    rw [hs3 r (nv r 60 (by omega) 60 rfl), f2 r (by omega), hs1 r (nv r 60 (by omega) 60 rfl)])
  obtain ⟨d4, q4, hI4, f4, g4⟩ := exec_repOfC (E := E) hnM hb.hk hb.hN ix' hix 11 (by decide) reps b
    σ3 hc3.rq hI3 (by simp [σ3, setSLS])
    (by rw [hs3 59 (by decide), f2 59 (by decide), hs1 59 (by decide), h59])
    (by simp only [σ3, setSLS]; rw [g2 22 (by decide) (by decide) (by decide)]; simp [σ1, setSLS, h22])
    hrep' hb.hcapB
  set σ4 := exec E (repOfC 11) σ3
  set repA := repOfL (.gate 0) (gvExp (2 ^ K)) reps (ofIdx 10 a)
  set repB := repOfL (.gate 0) (gvExp (2 ^ K)) reps (ofIdx 10 b)
  have h4_10 : σ4.ls 10 = repList E ix' repA := by
    rw [g4 10 (by decide) (by decide) (by decide)]; exact d2
  have h4_22 : σ4.ls 22 = (reps.map (repList E ix')).flatten := by
    rw [g4 22 (by decide) (by decide) (by decide)]; show σ2.ls 22 = _
    rw [g2 22 (by decide) (by decide) (by decide)]; simp [σ1, setSLS, h22]
  have hs4 : ∀ r : SR, r.val < 16 ∨ r.val = 59 ∨ r.val = 63 → σ4.sc r = σ.sc r := fun r hr => by
    rw [f4 r (by omega), hs3 r (nv r 60 (by omega) 60 rfl), f2 r (by omega),
      hs1 r (nv r 60 (by omega) 60 rfl)]
  have hpre : exec E (.seq (.seq (.rdsrc 60) (repOfC 10)) (.seq (.rdsrc 60) (repOfC 11))) σ = σ4 := by
    simp only [exec_seq]; rw [e1, e3]
  have hS4 : ScOK E σ4 := by
    have := scOK_exec E hnM' hWM (.seq (.seq (.rdsrc 60) (repOfC 10)) (.seq (.rdsrc 60) (repOfC 11)))
      σ hI hS
    rwa [hpre] at this
  have ea : exec E (.seq (.rdsrc 60) (repOfC 10)) σ = σ2 := by rw [exec_seq, e1]
  have eb : exec E (.seq (.rdsrc 60) (repOfC 11)) σ2 = σ4 := by rw [exec_seq, e3]
  unfold compileStepC at hM ⊢
  rw [exec_seq, exec_mk_noNand (.seq (.rdsrc 60) (repOfC 10)) ⟨trivial, noNand_repOfC 10⟩, ea,
    exec_seq, exec_mk_noNand (.seq (.rdsrc 60) (repOfC 11)) ⟨trivial, noNand_repOfC 11⟩, eb] at hM ⊢
  -- the block
  rw [exec_seq] at hM ⊢
  obtain ⟨sc5, ls5, h5, d5, f5, g5⟩ := exec_blockC hnM hWM hixn hb.hk hb.hN hK repA repB P σ4
    (allC_of hc (fun r hr => hs4 r (by omega))).1 hI4 hS4 h4_10 d4 hb.hcap hb.hcap' hb.hcapB hb.hbig
    (le_trans (Nat.add_le_add_left (by t_chain) _) hM)
  set r := nandBlockL (ordT₀ N k) (ordO₀ N k) (gvExp (2 ^ K)) (.gate 0) (2 ^ K) repA repB P
  rw [h5]
  have hS5 := (is_exec hnM' hWM h5 ⟨hI4, hS4⟩)
  -- copy into `23`, append to `22`, count
  set τ5 := setSL σ4 sc5 (Function.update ls5 23 (repList E ix' r.2))
  have e6 : exec E (.lmov 23 21) (setSL σ4 sc5 ls5) = τ5 := by
    simp [exec, τ5, setSL, d5]
  have hI6 : Inv E τ5 := by
    have := inv_exec E (.lmov 23 21) (setSL σ4 sc5 ls5) hS5.1; rwa [e6] at this
  have hsrc4 : σ4.src = rest := by rw [src_exec _ (noRd_repOfC 11)]; rfl
  obtain ⟨sc7, h7, f7⟩ := exec_takeC (E := E) (n := 10) (lA := 21) (lR := 22) (by decide)
    (repList E ix' r.2) [] ((reps.map (repList E ix')).flatten) τ5 hI6
    (by simp [τ5, setSL, d5]) (by simp [τ5, setSL]; rw [g5 22 (by decide), h4_22])
    (by simp [τ5, setSL]; rw [f5 10 (by decide), hs4 10 (by decide), hc.2.1, length_repList])
    (by
      rw [length_flatten_of' (V := 4 * k * N * k) _ (fun w hw => by
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw; exact length_repList E ix' x), length_repList]
      simp only [List.length_map]
      have := Nat.mul_le_mul_right (4 * k * N * k) (show reps.length + 1 ≤ g by omega)
      have := hb.hcapR; nlinarith)
  rw [exec_mk_noNand (.seq (.lmov 23 21) (.seq (takeC 10 21 22) (.inc 59)))
    (by simp [NoNand, takeC]), exec_seq, e6, exec_seq, h7]
  have h59' : sc7 59 = reps.length := by
    rw [f7 59 (by decide)]; show sc5 59 = _; rw [f5 59 (by decide), hs4 59 (by decide), h59]
  refine ⟨Function.update sc7 59 (reps.length + 1), Function.update (Function.update
    (Function.update ls5 23 (repList E ix' r.2)) 21 []) 22
      ((reps.map (repList E ix')).flatten ++ repList E ix' r.2), ?_, ?_, ?_, ?_, fun x hx => ?_⟩
  · simp only [exec, setSL, setSLS, h59', min_eq_left (show reps.length + 1 ≤ E.M by
      have := hb.hgM; omega)]
    simp only [compileStepL, mk, τ5, setSL, hsrc4]; rfl
  · simp [compileStepL, List.map_append]; rfl
  · simp [compileStepL]; rfl
  · simp
  · rw [Function.update_of_ne (nv x 59 (by omega) 59 rfl), f7 x (by
      simp only [List.mem_singleton]; exact nv x 41 (by omega) 41 rfl)]
    show sc5 x = _
    rw [f5 x (by omega), hs4 x (by omega)]

end FhatGen

end SigabaNeo.Lattices
