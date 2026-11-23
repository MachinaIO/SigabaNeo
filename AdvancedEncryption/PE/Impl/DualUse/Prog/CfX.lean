import PE.Impl.DualUse.Prog.BfX
import PE.Impl.DualUse.Prog.DecGenP

/-!
# The `c_f̂` block `cfX` of `Dec`

`cfX hk c wfB W`: from the data word `sk ++ ct` (tape `0`) and the gate list of a window predicate
(tape `1`), the word of `c_f̂` on tape `2` (`CfSpec`), through a coin-free `W_f` block `wfB`:

1. `preC` (framed off tape `1`): the word of the crafted data `sdC mpk ct (S ++ 0…0)`
   (`RowSimData`): the last two rows of every `Rᵢ` are `Ψᵢ`, the last row of every `W_j` is `c_j`,
   and the stash `S` (the key, `Ψ`, `c₀`, `c₁`, `κ`) rides in the first `W_j`;
2. `wfB`: the word of `W_f = simW sd C` on tape `2`;
3. `postC` (framed off tape `1`): tape `0` back to `sk ++ ct` (the `c_j` read back from the
   `W_j` by `skipLoopP`), tape `2` to its last row plus the second row of `G`:
   `c_f̂ = row_{d-1} W_f + G₁` (`evalCiphertext_sdC`).

**`cfSpec_cfX`**: `CfSpec hk c (cfX hk c wfB W) W` from `WfSpec hk c wfB W` and coin-freeness.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Lattices Matrix
  AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord
open SigabaNeo.Tape.Prog (tailsP run_tailsP coinFree_tailsP wf_tailsP)

/-! ### The word of the crafted data -/

/-- The templates of `preCoreC`. -/
def preTmplC (Z R nJ C0 Z2 R2 PAD LΨ : ℕ) : List (Fin 21 × ℕ) :=
  [(7, Z), (8, R), (9, nJ), (10, C0), (11, Z2), (12, R2), (13, 10), (14, PAD), (20, LΨ)]

/-- **The crafted data of `Dec` as a program on 21 tapes.** -/
def preCoreC (L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD : ℕ) : XProg 21 :=
  XProg.seq (getAt 0 L 0 1 4 5 6) <|
  XProg.seq (getAt L A 0 3 4 5 6) <|
  XProg.seq (getAt oK NK 0 3 4 5 6) <|
  XProg.seq (getAt oP LΨ 0 2 4 5 6) <|
  XProg.seq (getAt oP LΨ 0 18 4 5 6) <|
  XProg.seq (tmplP 17 (preTmplC Z R nJ C0 Z2 R2 PAD LΨ)) <|
  XProg.seq (XProg.zerosP 1 16 10) <|
  XProg.seq (XProg.zerosP 3 16 14) <|
  XProg.seq (XProg.zerosP 19 16 11) <|
  XProg.seq (wLoopP 1 2 19 15 16 13 11 12) <|
  XProg.seq (getAt oJ Lcj 0 2 4 5 6) <|
  XProg.seq (wLoopP 1 2 3 15 16 9 7 8) <|
  XProg.seq (XProg.moveP 1 18 16 20) <|
  XProg.seq (XProg.zerosP 1 16 13) <|
  XProg.seq (XProg.prog (.prim (.copy 0 1))) <|
  clearL [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

theorem law_preCoreC (L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD : ℕ) (w : List Bool)
    (prows : List (List Bool)) (hP : (w.drop oP).take LΨ = prows.flatten)
    (hpr : ∀ r ∈ prows, r.length = R2) (hpn : prows.length = 10)
    (rows : List (List Bool)) (hF : (w.drop oJ).take Lcj = rows.flatten)
    (hr : ∀ r ∈ rows, r.length = R) (hn : rows.length = nJ)
    (hX : ((w.drop L).take A ++ (w.drop oK).take NK).length + PAD = Z)
    (hPl : prows.flatten.length ≤ LΨ) :
    (preCoreC L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD).law (io1 w) =
      PMF.pure (io1 (w.take L ++ List.replicate C0 false ++
        wPart (List.replicate Z2 false) (List.replicate Z2 false) prows ++
        wPart ((w.drop L).take A ++ (w.drop oK).take NK ++ List.replicate PAD false)
          (List.replicate Z false) rows ++ prows.flatten ++ List.replicate 10 false)) := by
  rw [io1_sto, io1_sto, preCoreC]
  rw [XProg.law_seq_pure (law_getAt 0 L (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt L A (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt oK NK (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt oP LΨ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt oP LΨ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_tmplP 17 _ _ (by simp) (by simp [preTmplC])), preTmplC]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_zerosP (by decide) (by decide) _ (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_zerosP (by decide) (by decide) _ (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_zerosP (by decide) (by decide) _ (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_wLoopP (by decide) _ (by simp) (by simp))]
  norm_sto
  obtain ⟨h1, h2⟩ := iterate_wStep Z2 R2 prows hpr
    (List.take L w ++ List.replicate C0 false) (List.replicate Z2 false) [] (by simp)
  rw [List.append_nil, hpn] at h1 h2
  rw [hP, h1, h2]
  generalize ((wStep Z2 R2)^[10] _).2.2 = X'
  rw [XProg.law_seq_pure (law_getAt oJ Lcj (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_wLoopP (by decide) _ (by simp) (by simp))]
  norm_sto
  obtain ⟨h3, h4⟩ := iterate_wStep Z R rows hr
    (List.take L w ++ List.replicate C0 false ++
      wPart (List.replicate Z2 false) (List.replicate Z2 false) prows)
    ((w.drop L).take A ++ (w.drop oK).take NK ++ List.replicate PAD false) []
    (by rw [List.length_append, List.length_replicate]; exact hX)
  rw [List.append_nil, hn] at h3 h4
  rw [hF, h3, h4]
  generalize ((wStep Z R)^[nJ] _).2.2 = X''
  rw [XProg.law_seq_pure (XProg.law_moveP (by decide) (by decide) (by decide) (by decide) _
    (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_zerosP (by decide) (by decide) _ (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_prim _ _), Prim.apply, update_sto, law_clearL, clear_sto]
  refine congrArg PMF.pure ?_
  funext t
  fin_cases t <;> simp [List.append_assoc, List.take_of_length_le hPl]

/-! ### Reading `sk ++ ct` and `c_f̂` back -/

/-- The tapes of `gadP` in `postCoreC`. -/
def uGc : Fin 21 → Fin 64 := ![7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
  25, 26, 27]

/-- The tapes of `addRWP` in `postCoreC`: output `28`, inputs `1`, `60`, templates `8`, `29`,
scratch `30 … 52`. -/
def uAc : Fin 28 → Fin 64 := ![28, 1, 60, 8, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
  42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]

theorem uGc_inj : Function.Injective uGc := by decide
theorem uAc_inj : Function.Injective uAc := by decide

/-- The templates of `postCoreC`. -/
def postTmplC (N K k Z R nJ : ℕ) : List (Fin 64 × ℕ) :=
  [(8, K), (9, N), (10, N * K), (11, k), (12, 2 * k * (N * K)), (29, 1 * (2 * k) * N), (57, Z),
    (58, R), (59, nJ), (61, k * (N * K))]

/-- **Reading back, on 64 tapes**: tape `0` to the prefix of `L` bits, the `A` bits at `oW`, the
rows read back from the `LW` bits at `oW` (`skipLoopP`), and the `NK` bits at `oW + A`; tape `1`
to its bits after `Zr`, plus the second row of the gadget (`k N K` zeros, then the first half of
`gadW`). -/
def postCoreC (L A NK oW LW Zr N K k Z R nJ : ℕ) : XProg 64 :=
  XProg.seq (getAt 0 L 0 2 4 5 6) <|
  XProg.seq (getAt oW A 0 3 4 5 6) <|
  XProg.seq (getAt (oW + A) NK 0 54 4 5 6) <|
  XProg.seq (getAt oW LW 0 55 4 5 6) <|
  XProg.seq (tmplP 53 (postTmplC N K k Z R nJ)) <|
  XProg.seq (skipLoopP 56 55 62 63 59 57 58) <|
  XProg.seq (XProg.prog (.prim (.clear 0))) <|
  XProg.seq (prefP L 2 0 4 5) <|
  XProg.seq (prefP A 3 0 4 5) <|
  XProg.seq (prefP (nJ * R) 56 0 4 5) <|
  XProg.seq (prefP NK 54 0 4 5) <|
  XProg.seq (XProg.prog (tailsP 1 Zr)) <|
  XProg.seq (XProg.prog (Prog.map uGc Prog.gadP)) <|
  XProg.seq (XProg.zerosP 60 63 61) <|
  XProg.seq (prefP (k * (N * K)) 7 60 4 5) <|
  XProg.seq (XProg.prog (Prog.map uAc Prog.addRWP)) <|
  XProg.seq (XProg.prog (.prim (.copy 1 28))) <|
  clearL [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

theorem length_botG (N K k : ℕ) :
    (List.replicate (k * (N * K)) false ++ (Algo.gadW N K k).take (k * (N * K))).length =
      1 * (2 * k) * N * K := by
  have : k * (N * K) ≤ 2 * k * (N * K) := Nat.mul_le_mul_right _ (by omega)
  rw [List.length_append, List.length_replicate, List.length_take, length_gadW, min_eq_left this]
  ring

theorem law_postCoreC (L A NK oW LW Zr N K k Z R nJ : ℕ) (sd wf : List Bool)
    (hwf : (wf.drop Zr).length = 1 * (2 * k) * N * K) :
    (postCoreC L A NK oW LW Zr N K k Z R nJ).law (sto [(1, wf), (0, sd)]) =
      PMF.pure (sto [(1, Algo.matAddW N K (1 * (2 * k)) (wf.drop Zr)
          (List.replicate (k * (N * K)) false ++ (Algo.gadW N K k).take (k * (N * K)))),
        (0, sd.take L ++ (sd.drop oW).take A ++
          ((skStep Z R)^[nJ] ([], (sd.drop oW).take LW)).1.take (nJ * R) ++
          (sd.drop (oW + A)).take NK)]) := by
  rw [postCoreC]
  rw [XProg.law_seq_pure (law_getAt 0 L (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt oW A (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt (oW + A) NK (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt oW LW (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_tmplP 53 _ _ (by simp) (by simp [postTmplC])), postTmplC]
  norm_sto
  rw [XProg.law_seq_pure (law_skipLoopP (by decide) _ (by simp) (by simp))]
  norm_sto
  generalize ((skStep Z R)^[nJ] _).2 = Y'
  rw [XProg.law_seq_pure (XProg.law_prim _ _), Prim.apply, update_sto]
  rw [XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _ (by simp)
    (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _ (by simp)
    (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _ (by simp)
    (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _ (by simp)
    (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (by rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _
    (coinFree_tailsP _ _)]), run_tailsP, update_sto]
  norm_sto
  rw [XProg.law_seq_pure (by rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _
    (Prog.coinFree_mapP uGc (coinFree_noGrowP _ Prog.noGrow_gadP))])]
  rw [Prog.run_gadP_map (K := K) (N := N) (k' := k) uGc_inj _
    (fun i hi => by fin_cases i <;> (try simp at hi) <;> simp [uGc])
    (by simp [uGc]) (by simp [uGc]) (by simp [uGc]) (by simp [uGc]) (by simp [uGc]),
    show uGc 0 = (7 : Fin 64) from rfl, update_sto]
  rw [XProg.law_seq_pure (XProg.law_zerosP (by decide) (by decide) _ (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _ (by simp)
    (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (by rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _
    (Prog.coinFree_mapP uAc (coinFree_noGrowP _ Prog.noGrow_addRWP))])]
  rw [Prog.run_map_eq_update uAc_inj _ _ 0 _ (Prog.run_addRWP_mat (K := K) (N := N)
    (L := 1 * (2 * k)) _
    (fun i hi => by fin_cases i <;> (try simp at hi) <;> simp [uAc]) (by simp [uAc]) (by simp [uAc])
    (by simpa [uAc] using hwf) (by simpa [uAc] using length_botG N K k)),
    show uAc 0 = (28 : Fin 64) from rfl, update_sto]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_prim _ _), Prim.apply, update_sto, law_clearL, clear_sto]
  refine congrArg PMF.pure ?_
  funext t
  fin_cases t <;> simp [uAc, uGc, List.take_take]

/-! ### The block -/

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

variable (hk c) in
/-- The length of the key, `Ψ`, `c₀`, `c₁` in `sk ++ ct`. -/
def lenKA : ℕ :=
  fixLen (keyEnc (N := N) (K := K) c) + (lPsi (N := N) (K := K) hk +
    ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)) +
      (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K))))

variable (hk) in
/-- The length of the `c_j`. -/
abbrev lenCj : ℕ := nJ (N := N) hk * DualUse.rowL N K k

theorem eLo21 : 21 + 1 ≤ 256 := by norm_num
theorem eLo64 : 64 + 1 ≤ 256 := by norm_num

variable (hk c) in
/-- **The crafted data of `Dec`**, framed off tape `1`. -/
def preC : XProg 256 :=
  XProg.frame (eLo 21 eLo21) (preCoreC (lenPK hk c) (lenKA hk c)
    (lenPK hk c + lenKA hk c + lenCj (N := N) hk) (N * K)
    (lenPK hk c + fixLen (keyEnc (N := N) (K := K) c)) (lPsi (N := N) (K := K) hk)
    (lenPK hk c + lenKA hk c) (lenCj (N := N) hk) (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk)
    (c.d * (N * K)) ((c.d - 2) * DualUse.rowL N K k) (2 * DualUse.rowL N K k)
    (lenZ c - (lenKA hk c + N * K)))

variable (hk c) in
/-- **Reading `sk ++ ct` and `c_f̂` back**, framed off tape `1`. -/
def postC : XProg 256 :=
  XProg.frame (eLo 64 eLo64) (postCoreC (lenPK hk c) (lenKA hk c) (N * K) (offWk hk c)
    (nJ (N := N) hk * (lenZ c + DualUse.rowL N K k)) (lenZ c) N K k (lenZ c) (DualUse.rowL N K k)
    (nJ (N := N) hk))

variable (hk c) in
/-- **The `c_f̂` block of `Dec`** around a `W_f` block `wfB`. -/
def cfX (wfB : XProg 256) : XProg 256 :=
  XProg.seq (clearL clr01) (XProg.seq (preC hk c) (XProg.seq wfB (postC hk c)))

/-! ### The words -/

/-- The key, `Ψ`, `c₀`, `c₁`. -/
def wKA (sk : SK hk c) (ct : CT hk c) : List Bool :=
  (keyEnc (N := N) (K := K) c).enc sk.2 ++
    ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr) (matEnc (N := N) (K := K) (Fin 2)
      (RingBTVW.Col k))).enc ct.Ψ ++
    ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc ct.c₀ ++
      (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc ct.c₁))

/-- The rows `c_j`. -/
def cjRowsC (ct : CT hk c) : List (List Bool) :=
  (Enum.list (α := JIx (N := N) hk)).map
    fun j => (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (ct.cj j)

/-- The rows `Ψᵢ`. -/
def psiRowsC (ct : CT hk c) : List (List Bool) :=
  (List.finRange 10).map fun i => (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k)).enc (ct.Ψ i)

theorem length_wKA (sk : SK hk c) (ct : CT hk c) : (wKA sk ct).length = lenKA hk c := by
  rw [wKA, List.length_append, List.length_append, List.length_append, length_enc_fixLen,
    length_enc_fixLen, FixedEnc.length, FixedEnc.length]
  rfl

theorem length_cjRows (ct : CT hk c) : ∀ r ∈ cjRowsC ct, r.length = DualUse.rowL N K k := by
  intro r hr
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hr
  exact length_row1 _

theorem length_psiRows (ct : CT hk c) : ∀ r ∈ psiRowsC ct, r.length = 2 * DualUse.rowL N K k := by
  intro r hr
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
  rw [FixedEnc.length, len_matEnc_col]

theorem flatten_cjRows (ct : CT hk c) :
    (cjRowsC ct).flatten =
      (FixedEnc.fun (α := JIx (N := N) hk) (matEnc (N := N) (K := K) (Fin 1)
        (RingBTVW.Col k))).enc ct.cj := by
  rw [fun_enc_eq, flatMap_eq_flatten, cjRowsC, List.map_map]; rfl

theorem flatten_psiRows10 (ct : CT hk c) :
    (psiRowsC ct).flatten =
      (FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc ct.Ψ := by
  show _ = ((Enum.list (α := Fin 10)).map ct.Ψ).flatMap
    (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k)).enc
  rw [flatMap_eq_flatten]
  exact congrArg List.flatten (List.map_map (g := (matEnc (N := N) (K := K) (Fin 2)
    (RingBTVW.Col k)).enc) (f := ct.Ψ) (l := List.finRange 10)).symm

theorem flatten_psiRows (ct : CT hk c) :
    (psiRowsC ct).flatten =
      (FixedEnc.fun (α := (Sdw (N := N) hk).Attr) (matEnc (N := N) (K := K) (Fin 2)
        (RingBTVW.Col k))).enc ct.Ψ :=
  flatten_psiRows10 ct

theorem length_flatten {rows : List (List Bool)} {R : ℕ} (hr : ∀ r ∈ rows, r.length = R) :
    rows.flatten.length = rows.length * R := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    rw [List.flatten_cons, List.length_append, hr r (by simp),
      ih (fun r' h => hr r' (by simp [h])), List.length_cons]
    ring

/-- **The data word of `Dec`**: `pk`, the key, `Ψ`, `c₀`, `c₁`, the `c_j`, `κ`. -/
theorem data_split (sk : SK hk c) (ct : CT hk c) :
    (skEnc hk c).enc sk ++ (ctEnc hk c).enc ct =
      (pkEnc hk c).enc sk.1 ++ (wKA sk ct ++ ((cjRowsC ct).flatten ++ (ringEnc N K).enc ct.κ)) := by
  rw [flatten_cjRows]
  show (pkEnc hk c).enc sk.1 ++ (keyEnc (N := N) (K := K) c).enc sk.2 ++ _ = _
  simp only [wKA, List.append_assoc]
  rfl

theorem length_cj (ct : CT hk c) : (cjRowsC ct).flatten.length = lenCj (N := N) hk := by
  rw [length_flatten (length_cjRows ct)]
  simp [cjRowsC, lenCj, nJ]

theorem wPart_same (Y : List Bool) : ∀ rows : List (List Bool),
    wPart Y Y rows = rows.flatMap (fun r => Y ++ r)
  | [] => rfl
  | r :: rs => by rw [wPart, wPart_same Y rs, List.flatMap_cons, List.append_assoc]

theorem length_wPart {X Y : List Bool} {Z R : ℕ} (hX : X.length = Z) (hY : Y.length = Z) :
    ∀ rows : List (List Bool), (∀ r ∈ rows, r.length = R) →
      (wPart X Y rows).length = rows.length * (Z + R)
  | [], _ => by simp [wPart]
  | r :: rs, hr => by
    rw [wPart, List.length_append, List.length_append, hX, hr r (by simp),
      wPart_same, ← wPart_same]
    rw [length_wPart hY hY rs (fun r' h => hr r' (by simp [h])), List.length_cons]
    ring

variable (hk c) in
/-- The stash of `Dec`: the key, `Ψ`, `c₀`, `c₁`, `κ`, padded to `d - 1` rows. -/
def stashC (sk : SK hk c) (ct : CT hk c) : List Bool :=
  wKA sk ct ++ (ringEnc N K).enc ct.κ ++ List.replicate (lenZ c - (lenKA hk c + N * K)) false

theorem length_stashC (hS : lenKA hk c + N * K ≤ lenZ c) (sk : SK hk c) (ct : CT hk c) :
    (stashC hk c sk ct).length = lenZ c := by
  rw [stashC, List.length_append, List.length_append, length_wKA, (ringEnc N K).length,
    List.length_replicate]
  omega

/-- **The word written by `preC`**. -/
theorem sdEnc_sdC (hd : 3 ≤ c.d) (hS : lenKA hk c + N * K ≤ lenZ c) (sk : SK hk c) (ct : CT hk c) :
    (sdEnc hk c).enc (sdC hk c sk.1 ct (stashC hk c sk ct)) =
      (pkEnc hk c).enc sk.1 ++ List.replicate (c.d * (N * K)) false ++
        wPart (List.replicate ((c.d - 2) * DualUse.rowL N K k) false)
          (List.replicate ((c.d - 2) * DualUse.rowL N K k) false) (psiRowsC ct) ++
        wPart (wKA sk ct ++ (ringEnc N K).enc ct.κ ++
            List.replicate (lenZ c - (lenKA hk c + N * K)) false)
          (List.replicate (lenZ c) false) (cjRowsC ct) ++
        (psiRowsC ct).flatten ++ List.replicate 10 false := by
  have h := sdEnc_sdOf (hk := hk) (c := c) sk.1 (rmW := fun i =>
      List.replicate ((c.d - 2) * DualUse.rowL N K k) false ++
        (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k)).enc (ct.Ψ i)) (fun i => by
      rw [List.length_append, List.length_replicate, FixedEnc.length, len_matEnc_col, ← Nat.add_mul]
      congr 1; omega) ct.Ψ (length_stashC hS sk ct) (by omega) ct.cj
  rw [sdC, h, ← flatten_psiRows10, wPart_same]
  simp only [stashC, List.append_assoc]
  rfl

/-! ### Blocks of the data word -/

section Data

variable (sk : SK hk c) (ct : CT hk c)

theorem lenPK_eq_pk : ((pkEnc hk c).enc sk.1).length = lenPK hk c := length_enc_fixLen _ _

theorem length_kappa : ((ringEnc N K).enc ct.κ).length = N * K := (ringEnc N K).length _

theorem D_pk : ((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct).take (lenPK hk c) =
    (pkEnc hk c).enc sk.1 := by
  rw [data_split, List.take_left' (lenPK_eq_pk sk)]

theorem D_KA : (((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct).drop (lenPK hk c)).take (lenKA hk c) =
    wKA sk ct := by
  rw [data_split, List.drop_left' (lenPK_eq_pk sk), List.take_left' (length_wKA sk ct)]

theorem D_kappa : (((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct).drop
    (lenPK hk c + lenKA hk c + lenCj (N := N) hk)).take (N * K) = (ringEnc N K).enc ct.κ := by
  rw [data_split, ← List.drop_drop, ← List.drop_drop, List.drop_left' (lenPK_eq_pk sk),
    List.drop_left' (length_wKA sk ct), List.drop_left' (length_cj ct),
    List.take_of_length_le (le_of_eq (length_kappa ct))]

theorem D_cj : (((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct).drop
    (lenPK hk c + lenKA hk c)).take (lenCj (N := N) hk) = (cjRowsC ct).flatten := by
  rw [data_split, ← List.drop_drop, List.drop_left' (lenPK_eq_pk sk),
    List.drop_left' (length_wKA sk ct), List.take_left' (length_cj ct)]

theorem D_psi : (((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct).drop
    (lenPK hk c + fixLen (keyEnc (N := N) (K := K) c))).take (lPsi (N := N) (K := K) hk) =
      (psiRowsC ct).flatten := by
  rw [data_split, ← List.drop_drop, List.drop_left' (lenPK_eq_pk sk), wKA, List.append_assoc,
    List.drop_left' (length_enc_fixLen _ _), flatten_psiRows, List.append_assoc,
    List.take_left' (length_enc_fixLen _ _)]

theorem length_psi : (psiRowsC ct).flatten.length = lPsi (N := N) (K := K) hk := by
  rw [flatten_psiRows, length_enc_fixLen]

end Data

/-! ### The laws of the block -/

theorem law_preC (hd : 3 ≤ c.d) (hS : lenKA hk c + N * K ≤ lenZ c) (sk : SK hk c) (ct : CT hk c)
    (g : List Bool) :
    (preC hk c).law (io2 (R := 254) ((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct) g []) =
      PMF.pure (io2 (R := 254) ((sdEnc hk c).enc (sdC hk c sk.1 ct (stashC hk c sk ct))) g []) := by
  rw [preC, XProg.law_frame, io2_eLo, ← io1_sto,
    law_preCoreC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (psiRowsC ct) (D_psi sk ct) (length_psiRows ct)
      (by unfold psiRowsC; exact (List.length_map _).trans (List.length_finRange))
      (cjRowsC ct) (D_cj sk ct) (length_cjRows ct) (by simp [cjRowsC, nJ])
      (by rw [D_KA, D_kappa, List.length_append, length_wKA, length_kappa]; omega)
      (le_of_eq (length_psi ct)),
    PMF.pure_map, io1_sto, embedF_eLo, sdEnc_sdC hd hS, D_pk, D_KA, D_kappa]

theorem botG_eq : List.replicate (k * (N * K)) false ++ (Algo.gadW N K k).take (k * (N * K)) =
    Algo.rowW N K k (rowAt (Sdw (N := N) hk).Γ.G 1) := by
  have h := colsW_last (by norm_num : 0 < 2) (Algo.gswB N K k hk.le).G
  rw [← Algo.gswGadW_enc hk.le, gswGadW_eq, show (2 - 1) * DualUse.rowL N K k = (Algo.gadW N K k).length by
    rw [length_gadW]; simp [DualUse.rowL], List.drop_left] at h
  exact h

theorem law_postC (hd : 3 ≤ c.d) (hS : lenKA hk c + N * K ≤ lenZ c) (sk : SK hk c) (ct : CT hk c)
    (wf : List Bool) (hwf : (wf.drop (lenZ c)).length = 1 * (2 * k) * N * K) :
    (postC hk c).law (Function.update (io2 (R := 254)
        ((sdEnc hk c).enc (sdC hk c sk.1 ct (stashC hk c sk ct))) [] []) 2 wf) =
      PMF.pure (Function.update (io2 (R := 254) ((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct) [] [])
        2 (Algo.matAddW N K (1 * (2 * k)) (wf.drop (lenZ c))
          (List.replicate (k * (N * K)) false ++ (Algo.gadW N K k).take (k * (N * K))))) := by
  rw [postC, XProg.law_frame, upd_eLo (by norm_num), show (⟨1, by norm_num⟩ : Fin 64) = 1 from rfl,
    law_postCoreC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hwf, PMF.pure_map]
  refine congrArg PMF.pure ((embedF_eLo_upd (hm := eLo64) (by norm_num : 1 < 64) _ _ _ _).trans ?_)
  congr 2
  have hS' := length_stashC hS sk ct
  have hZ2 : (wPart (List.replicate ((c.d - 2) * DualUse.rowL N K k) false)
      (List.replicate ((c.d - 2) * DualUse.rowL N K k) false) (psiRowsC ct)).length =
        10 * (c.d * DualUse.rowL N K k) := by
    rw [length_wPart (Z := (c.d - 2) * DualUse.rowL N K k) (by simp) (by simp) _ (length_psiRows ct)]
    simp only [psiRowsC, List.length_map, List.length_finRange]
    congr 1
    rw [← Nat.add_mul]
    congr 1
    omega
  have hW : (wPart (stashC hk c sk ct) (List.replicate (lenZ c) false) (cjRowsC ct)).length =
      nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) := by
    rw [length_wPart (Z := lenZ c) hS' (by simp) _ (length_cjRows ct)]
    simp [cjRowsC, nJ]
  have hne : cjRowsC ct ≠ [] := by
    simpa [cjRowsC] using enum_JIx_ne_nil hk c.hN
  obtain ⟨r0, rs, hrs⟩ := List.exists_cons_of_ne_nil hne
  have hsd : ((sdEnc hk c).enc (sdC hk c sk.1 ct (stashC hk c sk ct))).drop (offWk hk c) =
      wPart (stashC hk c sk ct) (List.replicate (lenZ c) false) (cjRowsC ct) ++
        ((psiRowsC ct).flatten ++ List.replicate 10 false) := by
    rw [sdEnc_sdC hd hS, offWk]
    simp only [List.append_assoc]
    rw [← List.drop_drop, ← List.drop_drop, List.drop_left' (lenPK_eq_pk sk),
      List.drop_left' (by simp), List.drop_left' hZ2]
    simp only [stashC, List.append_assoc]
  have hpk : ((sdEnc hk c).enc (sdC hk c sk.1 ct (stashC hk c sk ct))).take (lenPK hk c) =
      (pkEnc hk c).enc sk.1 := by
    rw [sdEnc_sdC hd hS]; simp only [List.append_assoc]; rw [List.take_left' (lenPK_eq_pk sk)]
  have hit := iterate_skStep (lenZ c) (DualUse.rowL N K k) (cjRowsC ct) (length_cjRows ct) []
    (stashC hk c sk ct) [] hS'
  have hlen : (cjRowsC ct).length = nJ (N := N) hk := by simp [cjRowsC, nJ]
  rw [List.append_nil, hlen] at hit
  rw [← List.drop_drop, hsd, hpk, List.take_left' hW, hlen] at *
  rw [hit, List.nil_append, List.take_of_length_le (le_of_eq (length_cj ct))]
  have e1 : (wPart (stashC hk c sk ct) (List.replicate (lenZ c) false) (cjRowsC ct) ++
      ((psiRowsC ct).flatten ++ List.replicate 10 false)).take (lenKA hk c) = wKA sk ct := by
    rw [hrs, wPart, stashC]; simp only [List.append_assoc]; rw [List.take_left' (length_wKA sk ct)]
  have e2 : ((wPart (stashC hk c sk ct) (List.replicate (lenZ c) false) (cjRowsC ct) ++
      ((psiRowsC ct).flatten ++ List.replicate 10 false)).drop (lenKA hk c)).take (N * K) =
        (ringEnc N K).enc ct.κ := by
    rw [hrs, wPart, stashC]; simp only [List.append_assoc]
    rw [List.drop_left' (length_wKA sk ct), List.take_left' (length_kappa ct)]
  rw [e1, e2, data_split]
  simp only [List.append_assoc]

/-! ### Coin-freeness, well-formedness, the specification -/

theorem cf_getAt {n : ℕ} (o L : ℕ) (src dst tmp a b : Fin n) : (getAt o L src dst tmp a b).CoinFree :=
  XProg.coinFree_seq (coinFree_cpTails _ _ _) (XProg.coinFree_seq (cfX_prefP _ _ _ _ _) rfl)

theorem cf_preCoreC (L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD : ℕ) :
    (preCoreC L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD).CoinFree :=
  (XProg.coinFree_seq (cf_getAt _ _ _ _ _ _ _) (XProg.coinFree_seq (cf_getAt _ _ _ _ _ _ _) (XProg.coinFree_seq (cf_getAt _ _ _ _ _ _ _) (XProg.coinFree_seq (cf_getAt _ _ _ _ _ _ _) (XProg.coinFree_seq (cf_getAt _ _ _ _ _ _ _) (XProg.coinFree_seq (cfX_tmplP _ _) (XProg.coinFree_seq rfl (XProg.coinFree_seq rfl (XProg.coinFree_seq rfl (XProg.coinFree_seq rfl (XProg.coinFree_seq (cf_getAt _ _ _ _ _ _ _) (XProg.coinFree_seq rfl (XProg.coinFree_seq rfl (XProg.coinFree_seq rfl (XProg.coinFree_seq rfl (cfX_clearL _))))))))))))))))

theorem cf_postCoreC (L A NK oW LW Zr N K k Z R nJ : ℕ) :
    (postCoreC L A NK oW LW Zr N K k Z R nJ).CoinFree :=
  (XProg.coinFree_seq (cf_getAt _ _ _ _ _ _ _) (XProg.coinFree_seq (cf_getAt _ _ _ _ _ _ _) (XProg.coinFree_seq (cf_getAt _ _ _ _ _ _ _) (XProg.coinFree_seq (cf_getAt _ _ _ _ _ _ _) (XProg.coinFree_seq (cfX_tmplP _ _) (XProg.coinFree_seq rfl (XProg.coinFree_seq rfl (XProg.coinFree_seq (cfX_prefP _ _ _ _ _) (XProg.coinFree_seq (cfX_prefP _ _ _ _ _) (XProg.coinFree_seq (cfX_prefP _ _ _ _ _) (XProg.coinFree_seq (cfX_prefP _ _ _ _ _) (XProg.coinFree_seq (coinFree_tailsP _ _) (XProg.coinFree_seq (Prog.coinFree_mapP uGc (coinFree_noGrowP _ Prog.noGrow_gadP)) (XProg.coinFree_seq rfl (XProg.coinFree_seq (cfX_prefP _ _ _ _ _) (XProg.coinFree_seq (Prog.coinFree_mapP uAc (coinFree_noGrowP _ Prog.noGrow_addRWP)) (XProg.coinFree_seq rfl (cfX_clearL _))))))))))))))))))

theorem wf_preCoreC (L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD : ℕ) :
    (preCoreC L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD).WF :=
  ⟨wf_getAt _ _ _ _ _ _ _, wf_getAt _ _ _ _ _ _ _, wf_getAt _ _ _ _ _ _ _, wf_getAt _ _ _ _ _ _ _,
    wf_getAt _ _ _ _ _ _ _, wf_tmplP _ _ (by simp [preTmplC]), XProg.wf_zerosP (by decide),
    XProg.wf_zerosP (by decide), XProg.wf_zerosP (by decide),
    wf_wLoopP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    wf_getAt _ _ _ _ _ _ _,
    wf_wLoopP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    XProg.wf_moveP (by decide) (by decide), XProg.wf_zerosP (by decide), trivial, wf_clearL _⟩

theorem wf_postCoreC (L A NK oW LW Zr N K k Z R nJ : ℕ) :
    (postCoreC L A NK oW LW Zr N K k Z R nJ).WF :=
  ⟨wf_getAt _ _ _ _ _ _ _, wf_getAt _ _ _ _ _ _ _, wf_getAt _ _ _ _ _ _ _, wf_getAt _ _ _ _ _ _ _,
    wf_tmplP _ _ (by simp [postTmplC]),
    wf_skipLoopP (by decide) (by decide) (by decide) (by decide) (by decide), trivial,
    wf_prefP _ _ _ _ _, wf_prefP _ _ _ _ _, wf_prefP _ _ _ _ _, wf_prefP _ _ _ _ _, wf_tailsP _ _,
    Prog.WF.map uGc_inj Prog.wf_gadP, XProg.wf_zerosP (by decide), wf_prefP _ _ _ _ _,
    Prog.WF.map uAc_inj Prog.wf_addRWP, trivial, wf_clearL _⟩

/-- **The `c_f̂` block meets its specification**, for a coin-free `W_f` block meeting `WfSpec`. -/
theorem cfSpec_cfX (hd : 3 ≤ c.d) (hS : lenKA hk c + N * K ≤ lenZ c) {wfB : XProg 256} {W : ℕ}
    (hwf : WfSpec hk c wfB W) (hcf : wfB.CoinFree) : CfSpec hk c (cfX hk c wfB) W where
  wf := ⟨wf_clearL _, wf_preCoreC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, hwf.wf,
    wf_postCoreC _ _ _ _ _ _ _ _ _ _ _ _⟩
  coinFree := XProg.coinFree_seq (cfX_clearL _) (XProg.coinFree_seq
    (cf_preCoreC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (XProg.coinFree_seq hcf (cf_postCoreC _ _ _ _ _ _ _ _ _ _ _ _)))
  law sk C ct hL hC := by
    have hd0 : 0 < c.d := by omega
    have hcl := colsW_last hd0 (simW (sdC hk c sk.1 ct (stashC hk c sk ct)) C)
    rw [cfX, XProg.law_seq_pure (law_clr01 _ _), XProg.law_seq_pure (law_preC hd hS sk ct _), XProg.law_seq_pure (hwf.law _ C hL hC),
      law_postC hd hS sk ct _ (by rw [hcl, Algo.length_rowW]; ring)]
    congr 2
    obtain ⟨w, rfl⟩ := hC
    rw [hcl, botG_eq, matAdd_rowW,
      evalCiphertext_sdC (by omega) sk.1 ct (length_stashC hS sk ct) w]
    rfl

end AdvancedEncryption.DualUse.Prog
