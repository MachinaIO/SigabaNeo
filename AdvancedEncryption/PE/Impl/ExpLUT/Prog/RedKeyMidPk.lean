import PE.Impl.ExpLUT.Prog.RedKeyMidM
import PE.Impl.ExpLUT.Prog.KeyEvalInit

/-!
# `mid`, phase M3 (part): constants, the coefficient word, the slab counter

`pkOf pkt = pkConstC ; pkCfC ; pkt` splits the packet code of phase M3 (`PkOk`, `RedKeyMidCode`):

* **`pkConstC`**: `simKeyC`'s constants `SeConst` (F3's `templateOpsC`: unary templates by
  doubling, the ring constants `1`, `X⁻¹`, `X^{2^{14}−1}` as literal words) —
  **`seConst_pkConstC`**;
* **`pkCfC`**: `4 := C`, then `rCs := Cf = (C ++ 0^{16 tlK − |C|})^{|seRestL|} ++ 0^{m̄}` and the
  slab counter `seLoopC := 0^{|seRestL|}` — **`exec_pkCfC`** (the `blocks`/`tail` fields of
  `SimKeyIn`);
* **`pkt`** (**the remaining obligation**, contract **`PktOk pkt`**): from registers `0` =
  `rawEnc σ`, `1` = `ctW σ`, `2` = `mpkW σ`, `4` = `C` (and the constants), write the packet stream
  `seRestL.flatMap (sePkOf …)` into `rAinS = 0`, never writing the constants, `rCs`, `seLoopC`.

**`pkOk_pkOf`**: `PktOk pkt → PkOk (pkOf pkt)`, hence `RkMidOk (mid (pkOf pkt))`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyMid

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Constants -/

/-- The constants of `simKeyC` (`SeConst`). -/
noncomputable def pkConstOps (D : Dims) : List (Fin 64 × TemplateWord) :=
  [(rKc, .zeros (gD D)), (rBit1, .zeros 1), (rTb, .zeros D.b),
   (seTRec, .zeros ((32 * D.K ^ 3 + 12 * D.K) * (D.N * D.K))),
   (rTK, .zeros D.K), (rTK1, .zeros (D.K - 1)), (rZ, .zeros (D.N * D.K)),
   (rT2K, .zeros (2 * D.K)), (rTKNK, .zeros (D.K * (D.N * D.K))),
   (rT2KNK, .zeros (2 * D.K * (D.N * D.K))),
   (rT4KNK, .zeros (2 * (2 * D.K) * (D.N * D.K))),
   (rOne, .bits (encRM D.N D.K 1)),
   (rMu0, .bits (encRM D.N D.K (xInvG (ZMod (2 ^ D.K - 1)) D.N))),
   (rT4K, .zeros (4 * D.K)), (rTW, .zeros (2 ^ D.b)), (rTtab, .zeros tlK),
   (rXc, .bits (encRM D.N D.K (xcK D))), (rTe, .zeros 14)]

/-- **The constants**, from any state (`5 := [true]`, `rB1 := [false]` first). -/
noncomputable def pkConstC (D : Dims) : Code :=
  .seq (.clr 6) <| .seq (bitsC 5 rB1 6) (templateOpsC (pkConstOps D))

theorem wf_pkConstC (D : Dims) : (pkConstC D).WFc :=
  ⟨trivial, by repeat constructor, wf_templateOpsC _⟩

theorem exec_pkConstC (D : Dims) (w : St) :
    exec D.N D.K (pkConstC D) w = templateOpsState (pkConstOps D)
      (Function.update (Function.update (Function.update w 6 []) 5 [true]) rB1 [false]) := by
  rw [pkConstC, exec_seq, exec_seq,
    exec_bitsC _ _ _ (by decide) (by decide) (by decide) _ (by simp)]
  apply exec_templateOpsC
  · simp [pkConstOps]
  · simp
  · simp

/-- **`pkConstC` establishes `SeConst`.** -/
theorem seConst_pkConstC (D : Dims) (w : St) :
    SeConst (exec D.N D.K (pkConstC D) w) (gD D) D.b (2 ^ D.b) tlK
      (xInvG (ZMod (2 ^ D.K - 1)) D.N) (xcK D) := by
  rw [exec_pkConstC]
  constructor
  all_goals try constructor
  all_goals simp [templateOpsState, pkConstOps, TemplateWord.value, encRM_zero,
    encL_replicate_zero]

theorem pkConstC_rB1 (D : Dims) (w : St) : exec D.N D.K (pkConstC D) w rB1 = [false] := by
  rw [exec_pkConstC]; simp [templateOpsState, pkConstOps, TemplateWord.value]

/-- `pkConstC` keeps the input registers `0 … 4`. -/
theorem pkConstC_keeps (D : Dims) (r : Fin 64) (hr : r.val < 5) : (pkConstC D).writes r = false := by
  have hf : (templateOpsC (pkConstOps D)).writes r = false := by
    apply templateOpsC_frame
    intro op hop
    simp only [pkConstOps, List.mem_cons, List.mem_nil_iff, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
    · intro h; subst h; simp at hr
  have h6 : r ≠ 6 := by intro h; subst h; simp at hr
  have h5 : r ≠ 5 := by intro h; subst h; simp at hr
  have h38 : r ≠ rB1 := by intro h; subst h; simp at hr
  simp [pkConstC, Code.writes, bitsC, hf, Ne.symm h6, Ne.symm h5, Ne.symm h38]

/-! ### The coefficient word and the slab counter -/

/-- The number of slabs. -/
noncomputable abbrev nSl (D : Dims) : ℕ := (seRestL D).length

/-- `|C|` padded to the bits of `16` tables. -/
abbrev cpLen : ℕ := tlK * 16

/-- **`Cf`** and the slab counter: `4 := C`; `rCs := (C ++ 0^{16 tlK − |C|})^{nSl} ++ 0^{m̄}`;
`seLoopC := 0^{nSl}` (scratch `29`, `30`, `32`). -/
noncomputable def pkCfC (D : Dims) : Code :=
  .seq (.cp 4 rCs) <| .seq (natC 29 rB1 (cpLen - predLen)) <| .seq (.app rCs 29) <|
  .seq (.cp 30 rCs) <| .seq (.clr rCs) <| .seq (natC seLoopC rB1 (nSl D)) <|
  .seq (.cp 32 seLoopC) <| .seq (.rep 32 (.app rCs 30)) <| .seq (natC 29 rB1 D.mb) (.app rCs 29)

theorem wf_pkCfC (D : Dims) : (pkCfC D).WFc :=
  ⟨trivial, natC_wfc _ _ _, trivial, trivial, trivial, natC_wfc _ _ _, trivial,
    ⟨by decide, trivial⟩, natC_wfc _ _ _, trivial⟩

/-- The rounds of `rep 32 (app rCs 30)`. -/
theorem iter_app (N K : ℕ) : ∀ (n : ℕ) (w : St),
    (fun w' => exec N K (.app rCs 30) (Function.update w' 32 (w' 32).tail))^[n] w =
      Function.update (Function.update w rCs (w rCs ++ (List.replicate n (w 30)).flatten)) 32
        ((w 32).drop n)
  | 0, w => by simp
  | n + 1, w => by
    rw [Function.iterate_succ_apply, iter_app N K n]
    funext r
    simp only [exec_app, Function.update_apply]
    by_cases h32 : r = 32
    · subst h32; simp [List.drop_tail]
    by_cases h3 : r = rCs
    · subst h3
      simp [List.replicate_succ, List.flatten_cons, List.append_assoc]
    · simp [h32, h3]

theorem exec_rep_app (N K : ℕ) (w : St) :
    exec N K (.rep 32 (.app rCs 30)) w =
      Function.update (Function.update w rCs (w rCs ++ (List.replicate (w 32).length (w 30)).flatten))
        32 [] := by
  show (fun w' => exec N K (.app rCs 30) (Function.update w' 32 (w' 32).tail))^[(w 32).length] w = _
  rw [iter_app]
  simp

/-- The padded predicate. -/
def cPad (C : List Bool) : List Bool := C ++ List.replicate (cpLen - predLen) false

/-- **The coefficient word.** -/
noncomputable def cfOf (D : Dims) (C : List Bool) : List Bool :=
  (List.replicate (nSl D) (cPad C)).flatten ++ List.replicate D.mb false

theorem exec_pkCfC (D : Dims) (w : St) (C : List Bool) (hC : w rCs = C)
    (hb : w rB1 = [false]) :
    exec D.N D.K (pkCfC D) w rCs = cfOf D C ∧
    exec D.N D.K (pkCfC D) w seLoopC = List.replicate (nSl D) false ∧
    exec D.N D.K (pkCfC D) w 4 = C ∧
    (∀ r : Fin 64, r ≠ 4 → r ≠ 29 → r ≠ rCs → r ≠ 30 → r ≠ seLoopC → r ≠ 32 →
      exec D.N D.K (pkCfC D) w r = w r) := by
  rw [pkCfC]
  simp only [exec_seq]
  -- the steps, one by one
  set w1 := exec D.N D.K (.cp 4 rCs) w with hw1
  have e1 : w1 = Function.update w 4 C := by rw [hw1, exec_cp, hC]
  set w2 := exec D.N D.K (natC 29 rB1 (cpLen - predLen)) w1
  have e2 : w2 = Function.update w1 29 (List.replicate (cpLen - predLen) false) :=
    exec_natC 29 rB1 (by decide) _ _ (by rw [e1, Function.update_of_ne (by decide)]; exact hb)
  set w3 := exec D.N D.K (.app rCs 29) w2
  have e3 : w3 rCs = cPad C := by
    simp only [w3, exec_app, Function.update_self, e2, e1]
    simp [Function.update_apply, hC, cPad]
  set w4 := exec D.N D.K (.cp 30 rCs) w3
  set w5 := exec D.N D.K (.clr rCs) w4
  set w6 := exec D.N D.K (natC seLoopC rB1 (nSl D)) w5
  have hb5 : w5 rB1 = [false] := by
    simp only [w5, w4, w3, exec_clr, exec_cp, exec_app, Function.update_apply, e2, e1]
    simp [hb]
  have e6 : w6 = Function.update w5 seLoopC (List.replicate (nSl D) false) :=
    exec_natC seLoopC rB1 (by decide) _ _ hb5
  set w7 := exec D.N D.K (.cp 32 seLoopC) w6
  set w8 := exec D.N D.K (.rep 32 (.app rCs 30)) w7
  have e8 : w8 = Function.update (Function.update w7 rCs
      (w7 rCs ++ (List.replicate (w7 32).length (w7 30)).flatten)) 32 [] := exec_rep_app _ _ w7
  have w7C : w7 rCs = [] := by simp [w7, e6, w5, Function.update_apply]
  have w732 : (w7 32).length = nSl D := by simp [w7, e6]
  have w730 : w7 30 = cPad C := by
    simp only [w7, w6, e6, w5, w4, exec_cp, exec_clr, Function.update_apply]
    simp [e3]
  set w9 := exec D.N D.K (natC 29 rB1 D.mb) w8
  have hb8 : w8 rB1 = [false] := by
    rw [e8]; simp [Function.update_apply, w7, e6, hb5]
  have e9 : w9 = Function.update w8 29 (List.replicate D.mb false) :=
    exec_natC 29 rB1 (by decide) _ _ hb8
  have hfin : exec D.N D.K (.app rCs 29) w9 =
      Function.update w9 rCs (w9 rCs ++ w9 29) := exec_app _ _ _ _ _
  rw [hfin]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Function.update_self, e9, Function.update_self, Function.update_of_ne (by decide), e8,
      Function.update_of_ne (by decide), Function.update_self, w7C, w732, w730]
    rfl
  · rw [Function.update_of_ne (by decide), e9, Function.update_of_ne (by decide), e8,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    simp [w7, e6]
  · rw [Function.update_of_ne (by decide), e9, Function.update_of_ne (by decide), e8,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    simp [w7, e6, w5, w4, w3, e2, e1, Function.update_apply]
  · intro r h4 h29 hCs h30 hL h32
    rw [Function.update_of_ne hCs, e9, Function.update_of_ne h29, e8, Function.update_of_ne h32,
      Function.update_of_ne hCs]
    simp [w7, e6, w5, w4, w3, e2, e1, Function.update_apply, h4, h29, hCs, h30, hL, h32]

theorem length_cPad (C : List Bool) (hC : ValidC C) : (cPad C).length = cpLen := by
  rw [cPad, List.length_append, List.length_replicate, hC]
  have : predLen ≤ cpLen := by rw [predLen, cpLen, tlK]; norm_num
  omega

theorem drop_flatten_rep (x : List Bool) (m : ℕ) (hx : x.length = m) :
    ∀ (k L : ℕ) (u : List Bool), k ≤ L →
      ((List.replicate L x).flatten ++ u).drop (m * k) = (List.replicate (L - k) x).flatten ++ u
  | 0, L, u, _ => by simp
  | k + 1, L, u, h => by
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc, Nat.mul_succ,
      show m * k + m = m + m * k from Nat.add_comm _ _, ← List.drop_drop, ← hx, List.drop_left,
      hx, drop_flatten_rep x m hx k L' u (by omega)]
    congr 3
    omega

theorem cfOf_blocks (D : Dims) (C : List Bool) (hC : ValidC C) :
    ∀ k < nSl D, ∃ u, (cfOf D C).drop (tlK * 16 * k) = C ++ u := by
  intro k hk
  rw [cfOf, drop_flatten_rep (cPad C) cpLen (length_cPad C hC) k (nSl D) _ hk.le]
  obtain ⟨L', hL'⟩ : ∃ L', nSl D - k = L' + 1 := ⟨nSl D - k - 1, by omega⟩
  rw [hL', List.replicate_succ, List.flatten_cons, cPad]
  exact ⟨List.replicate (cpLen - predLen) false ++ ((List.replicate L' (cPad C)).flatten ++
    List.replicate D.mb false), by simp [cPad, List.append_assoc]⟩

theorem cfOf_tail (D : Dims) (C : List Bool) (hC : ValidC C) :
    ((cfOf D C).drop (tlK * 16 * nSl D)).length = D.mb := by
  rw [cfOf, drop_flatten_rep (cPad C) cpLen (length_cPad C hC) (nSl D) (nSl D) _ le_rfl]
  simp

/-! ### The packet stream: the remaining contract -/

/-- The registers the packet code must keep: the constants, `rCs`, the slab counter. -/
def pktKeepR (r : Fin 64) : Bool := seConstR r || r == rCs || r == seLoopC

/-- **The contract of the packet-stream code** (rest of phase M3): from registers `0` =
`rawEnc σ`, `1` = `ctW σ`, `2` = `mpkW σ`, `4` = `C` (any other contents), it writes the packets
of all slabs into `rAinS` and never writes a register of `pktKeepR`. -/
def PktOk (pkt : Code) : Prop :=
  (∀ r : Fin 64, pktKeepR r = true → pkt.writes r = false) ∧
  ∀ (σ : RawSec Dc) (C : List Bool), ValidC C → ∀ w : St,
    w 0 = (rawEnc Dc).enc σ → w 1 = ctW σ → w 2 = mpkW σ → w 4 = C →
    exec Dc.N Dc.K pkt w rAinS = encL Dc.N Dc.K ((seRestL Dc).flatMap
      (sePkOf Dc (redView Dc (rawF Dc σ)).1 C (redView Dc (rawF Dc σ)).2 (rawF Dc σ).1
        (ExpLUT.progOf (rawF Dc σ).2.2.1)))

/-- **The packet code of phase M3.** -/
noncomputable def pkOf (pkt : Code) : Code := .seq (pkConstC Dc) (.seq (pkCfC Dc) pkt)

theorem wf_pkOf {pkt : Code} (h : pkt.WFc) : (pkOf pkt).WFc := ⟨wf_pkConstC Dc, wf_pkCfC Dc, h⟩

/-- **`PktOk pkt → PkOk (pkOf pkt)`.** -/
theorem pkOk_pkOf {pkt : Code} (hpkt : PktOk pkt) : PkOk (pkOf pkt) := by
  intro σ C hC
  set w0 := pkInit σ C
  set w1 := exec Dc.N Dc.K (pkConstC Dc) w0
  have k1 : ∀ r : Fin 64, r.val < 5 → w1 r = w0 r := fun r hr =>
    exec_writes _ _ _ (pkConstC_keeps Dc r hr)
  have hst := seConst_pkConstC Dc w0
  obtain ⟨hCf, hL, h4, hk⟩ := exec_pkCfC Dc w1 C
    ((k1 rCs (by decide)).trans (by simp [w0, pkInit])) (pkConstC_rB1 Dc w0)
  set w2 := exec Dc.N Dc.K (pkCfC Dc) w1
  have k2 : ∀ r : Fin 64, seConstR r = true → w2 r = w1 r := by
    intro r hr
    apply hk <;> intro h <;> subst h <;> simp [seConstR] at hr
  have k3 : ∀ r : Fin 64, pktKeepR r = true → exec Dc.N Dc.K pkt w2 r = w2 r :=
    fun r hr => exec_writes _ _ _ (hpkt.1 r hr)
  have hS := hpkt.2 σ C hC w2
    ((hk 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((k1 0 (by decide)).trans (by simp [w0, pkInit])))
    ((hk 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((k1 1 (by decide)).trans (by simp [w0, pkInit])))
    ((hk 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((k1 2 (by decide)).trans (by simp [w0, pkInit])))
    h4
  refine ⟨cfOf Dc C, ?_⟩
  have e : exec Dc.N Dc.K (pkOf pkt) (pkInit σ C) = exec Dc.N Dc.K pkt w2 := by
    simp only [pkOf, exec_seq]; rfl
  rw [e]
  refine ⟨?_, hS, ?_, cfOf_blocks Dc C hC, cfOf_tail Dc C hC, ?_, hC⟩
  · refine hst.of_frame fun r hr => ?_
    rw [k3 r (by simp [pktKeepR, hr]), k2 r hr]
  · rw [k3 rCs (by decide), hCf]
  · rw [k3 seLoopC (by decide), hL, List.length_replicate]

/-- **The middle phases from a packet-stream code.** -/
theorem rkMidOk_pkOf {pkt : Code} (hpkt : PktOk pkt) : RedKeyM.RkMidOk (mid (pkOf pkt)) :=
  rkMidOk_mid (pkOk_pkOf hpkt)

end AdvancedEncryption.ExpLUT.Prog.RedKeyMid
