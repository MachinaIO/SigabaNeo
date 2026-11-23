import PE.Impl.DualUse.Prog.RowSimP
import PE.Impl.DualUse.Prog.KeyGenP
import PE.Impl.DualUse.Prog.DecP
import SigabaNeo.Lib.Lattices.ProgAlgo.MatAdd
import SigabaNeo.Lib.Lattices.ProgAlgo.Nand
import SigabaNeo.Lib.Machines.Prog.CoinFreeX

/-!
# The key-row block `bfX` of `KeyGen`

`bfX hk c wfB W`: from the word of a master secret key (tape `0`) and the gate list of a window
predicate (tape `1`), the key row `B_f̂` on tape `2` (`BfSpec`), through the `W_f` block `wfB` of
the key component (any block meeting `WfSpec`):

1. `preB` (framed off tape `1`): the word of the crafted simulation data
   `sdB mpk (T ++ 0…0)` (`RowSimData`), `T` the trapdoor part of the master key, carried in the
   first `W_j`;
2. `wfB`: the word of `W_f = simW sd C` on tape `2`;
3. `postB` (framed off tape `1`): tape `0` back to the master key (`pk` prefix and `T`), tape
   `2` to its last row plus `G̲` (`gadP`, `addRWP`): `B_f̂ = row_{d-1} W_f + G̲`
   (`keyMatrix_sdB`).

**`bfSpec_bfX`**: `BfSpec hk c (bfX hk c wfB W) W` from `WfSpec hk c wfB W`, for `3 ≤ c.d`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Lattices Matrix
  AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord
open SigabaNeo.Tape.Prog (tailsP run_tailsP coinFree_tailsP wf_tailsP)

/-! ### The word of the crafted data, as a tape program -/

/-- The templates of `preCoreB`. -/
def preTmpl (Z R nT C0 RM0 PS0 PAD : ℕ) : List (Fin 18 × ℕ) :=
  [(7, Z), (8, R), (9, nT), (10, C0), (11, RM0), (12, PS0), (13, nA), (14, PAD)]

/-- **The crafted data of `KeyGen` as a program on 18 tapes**: the `pk` prefix (`L` bits) to the
output `1`, the trapdoor `T` (`LT` bits after it) to the stash `3`, the rows `F` (`nTR` bits at
`oB`) to `2`; zeros for `c₀` and the `Rᵢ`, the `W`-part loop, zeros for `Ψ` and the date; the output
back to tape `0`. -/
def preCoreB (L LT oB nTR Z R nT C0 RM0 PS0 PAD : ℕ) : XProg 18 :=
  XProg.seq (getAt 0 L 0 1 4 5 6) <|
  XProg.seq (getAt L LT 0 3 4 5 6) <|
  XProg.seq (getAt oB nTR 0 2 4 5 6) <|
  XProg.seq (tmplP 17 (preTmpl Z R nT C0 RM0 PS0 PAD)) <|
  XProg.seq (XProg.zerosP 1 16 10) <|
  XProg.seq (XProg.zerosP 1 16 11) <|
  XProg.seq (XProg.zerosP 3 16 14) <|
  XProg.seq (wLoopP 1 2 3 15 16 9 7 8) <|
  XProg.seq (XProg.zerosP 1 16 12) <|
  XProg.seq (XProg.zerosP 1 16 13) <|
  XProg.seq (XProg.prog (.prim (.copy 0 1))) <|
  clearL [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

theorem law_preCoreB (L LT oB nTR Z R nT C0 RM0 PS0 PAD : ℕ) (w : List Bool)
    (rows : List (List Bool)) (hF : (w.drop oB).take nTR = rows.flatten)
    (hr : ∀ r ∈ rows, r.length = R) (hn : rows.length = nT)
    (hT : ((w.drop L).take LT).length + PAD = Z) :
    (preCoreB L LT oB nTR Z R nT C0 RM0 PS0 PAD).law (io1 w) =
      PMF.pure (io1 (w.take L ++ List.replicate C0 false ++ List.replicate RM0 false ++
        wPart ((w.drop L).take LT ++ List.replicate PAD false) (List.replicate Z false) rows ++
        List.replicate PS0 false ++ List.replicate nA false)) := by
  rw [io1_sto, io1_sto, preCoreB,
    XProg.law_seq_pure (law_getAt 0 L (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt L LT (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt oB nTR (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_tmplP 17 _ _ (by simp) (by simp [preTmpl])), preTmpl]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_zerosP (by decide) (by decide) _ (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_zerosP (by decide) (by decide) _ (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_zerosP (by decide) (by decide) _ (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_wLoopP (by decide) _ (by simp) (by simp))]
  norm_sto
  obtain ⟨h1, h2⟩ := iterate_wStep Z R rows hr
    (List.take L w ++ List.replicate C0 false ++ List.replicate RM0 false)
    (List.take LT (List.drop L w) ++ List.replicate PAD false) []
    (by rw [List.length_append, List.length_replicate]; exact hT)
  rw [List.append_nil, hn] at h1 h2
  rw [hF, h1, h2]
  generalize ((wStep Z R)^[nT] _).2.2 = X'
  rw [XProg.law_seq_pure (XProg.law_zerosP (by decide) (by decide) _ (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_zerosP (by decide) (by decide) _ (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (XProg.law_prim _ _), Prim.apply, update_sto, law_clearL, clear_sto]
  congr 1
  funext t
  fin_cases t <;> simp [List.append_assoc]

/-! ### Reading the key row back -/

/-- The tapes of `gadP` in `postCoreB`: output `7`, templates `8 … 12`, scratch `13 … 27`. -/
def uG : Fin 21 → Fin 55 := ![7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
  25, 26, 27]

/-- The tapes of `addRWP` in `postCoreB`: output `28`, inputs `1`, `7`, templates `8`, `29`,
scratch `30 … 52`. -/
def uA : Fin 28 → Fin 55 := ![28, 1, 7, 8, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42,
  43, 44, 45, 46, 47, 48, 49, 50, 51, 52]

theorem uG_inj : Function.Injective uG := by decide
theorem uA_inj : Function.Injective uA := by decide

/-- The templates of `postCoreB`. -/
def postTmpl (N K k : ℕ) : List (Fin 55 × ℕ) :=
  [(8, K), (9, N), (10, N * K), (11, k), (12, 2 * k * (N * K)), (29, 1 * (2 * k) * N)]

/-- The gadget row added to the row of `W_f` (tape `1`), the sum copied back to `1`. -/
def gadAddP : Prog 55 :=
  Prog.seq (Prog.map uG Prog.gadP) (Prog.seq (Prog.map uA Prog.addRWP) (.prim (.copy 1 28)))

/-- **Reading the key row back, on 55 tapes**: tape `0` (the crafted data) back to its prefix of
`L` bits and the `LT` bits at `oW`; the bit after them (`f(0)`) to the flag tape `54`; tape `1`
(the word of `W_f`) to its bits after `Zr`, plus the gadget row (`gadP`, `addRWP`) if the flag is
set. -/
def postCoreB (L LT oW Zr N K k : ℕ) : XProg 55 :=
  XProg.seq (getAt 0 L 0 2 4 5 6) <|
  XProg.seq (getAt oW LT 0 3 4 5 6) <|
  XProg.seq (getAt (oW + LT) 1 0 54 4 5 6) <|
  XProg.seq (XProg.prog (.prim (.clear 0))) <|
  XProg.seq (prefP L 2 0 4 5) <|
  XProg.seq (prefP LT 3 0 4 5) <|
  XProg.seq (XProg.prog (tailsP 1 Zr)) <|
  XProg.seq (tmplP 53 (postTmpl N K k)) <|
  XProg.seq (XProg.prog (.ifBit 54 gadAddP (.prim (.clear 54)))) <|
  clearL [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54]

theorem coinFree_gadAddP : gadAddP.CoinFree := by
  have h1 := Prog.coinFree_mapP uG (coinFree_noGrowP _ Prog.noGrow_gadP)
  have h2 := Prog.coinFree_mapP uA (coinFree_noGrowP _ Prog.noGrow_addRWP)
  simp only [Prog.CoinFree] at h1 h2
  simp [Prog.CoinFree, gadAddP, Prog.coinFreeB, h1, h2]

theorem law_postCoreB (L LT oW Zr N K k : ℕ) (sd wf : List Bool) (b : Bool)
    (hb : (sd.drop (oW + LT)).take 1 = [b])
    (hwf : (wf.drop Zr).length = 1 * (2 * k) * N * K) :
    (postCoreB L LT oW Zr N K k).law (sto [(1, wf), (0, sd)]) =
      PMF.pure (sto [(1, if b then Algo.matAddW N K (1 * (2 * k)) (wf.drop Zr) (Algo.gadW N K k)
          else wf.drop Zr),
        (0, sd.take L ++ (sd.drop oW).take LT)]) := by
  rw [postCoreB,
    XProg.law_seq_pure (law_getAt 0 L (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt oW LT (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_getAt (oW + LT) 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp) (by simp) (by simp))]
  norm_sto
  rw [hb]
  rw [XProg.law_seq_pure (XProg.law_prim _ _), Prim.apply, update_sto]
  rw [XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _ (by simp)
    (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _ (by simp)
    (by simp))]
  norm_sto
  rw [XProg.law_seq_pure (by rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _
    (coinFree_tailsP _ _)]), run_tailsP, update_sto]
  norm_sto
  rw [XProg.law_seq_pure (law_tmplP 53 _ _ (by simp) (by simp [postTmpl])), postTmpl]
  norm_sto
  have hcf : (Prog.ifBit (54 : Fin 55) gadAddP (.prim (.clear 54))).CoinFree := by
    have := coinFree_gadAddP
    simp only [Prog.CoinFree] at this
    simp [Prog.CoinFree, Prog.coinFreeB, this]
  rw [XProg.law_seq_pure (by rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _ hcf])]
  cases b
  · rw [Prog.run_ifBit, if_neg (by simp [sto]), Prog.run_prim, Prim.apply, update_sto]
    norm_sto
    rw [law_clearL, clear_sto]
    congr 1
    funext t
    fin_cases t <;> simp [List.take_take]
  · rw [Prog.run_ifBit, if_pos (by simp [sto]), gadAddP, Prog.run_seq]
    rw [Prog.run_gadP_map (K := K) (N := N) (k' := k) uG_inj _
      (fun i hi => by fin_cases i <;> (try simp at hi) <;> simp [uG])
      (by simp [uG]) (by simp [uG]) (by simp [uG]) (by simp [uG]) (by simp [uG]),
      show uG 0 = (7 : Fin 55) from rfl, update_sto]
    norm_sto
    rw [Prog.run_seq]
    rw [Prog.run_map_eq_update uA_inj _ _ 0 _ (Prog.run_addRWP_mat (K := K) (N := N) (L := 1 * (2 * k)) _
      (fun i hi => by fin_cases i <;> (try simp at hi) <;> simp [uA]) (by simp [uA]) (by simp [uA])
      (by simpa [uA] using hwf) (by simp [uA, length_gadW]; ring)),
      show uA 0 = (28 : Fin 55) from rfl, update_sto]
    norm_sto
    rw [Prog.run_prim, Prim.apply, update_sto, law_clearL, clear_sto]
    congr 1
    funext t
    fin_cases t <;> simp [uA, uG, List.take_take]

/-! ### The block -/

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The length of the trapdoor part `T = (e, t)` of the master key. -/
abbrev lenT (N K k : ℕ) : ℕ := DualUse.rowL N K k + N * K

/-- The offset of the rows `B_j` in the word of a public key. -/
def offBk (c : Conf N K k) : ℕ :=
  (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)) +
    (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K))

variable (hk) in
/-- The number of rows `B_j`. -/
abbrev nJ : ℕ := (Enum.list (α := JIx (N := N) hk)).length

/-- The free part of a `W_j`: its first `d - 1` rows. -/
abbrev lenZ (c : Conf N K k) : ℕ := (c.d - 1) * DualUse.rowL N K k

variable (hk c) in
/-- The offset of the `W_j` in the word of the simulation data. -/
def offWk : ℕ := lenPK hk c + c.d * (N * K) + nA * (c.d * DualUse.rowL N K k)

theorem eLo18 : 18 + 1 ≤ 256 := by norm_num
theorem eLo55 : 55 + 1 ≤ 256 := by norm_num

variable (hk c) in
/-- **The crafted data of `KeyGen`**, framed off tape `1`: the trapdoor and the bit `f(0)` (the
last bit of tape `0`) stashed in the free rows of the first `W_j`. -/
def preB : XProg 256 :=
  XProg.frame (eLo 18 eLo18) (preCoreB (lenPK hk c) (lenT N K k + 1) (offBk c)
    (nJ (N := N) hk * DualUse.rowL N K k)
    (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk) (c.d * (N * K)) (nA * (c.d * DualUse.rowL N K k))
    (nA * (2 * DualUse.rowL N K k)) (lenZ c - (lenT N K k + 1)))

variable (hk c) in
/-- **Reading the key row back**, framed off tape `1`. -/
def postB : XProg 256 :=
  XProg.frame (eLo 55 eLo55) (postCoreB (lenPK hk c) (lenT N K k) (offWk hk c) (lenZ c) N K k)

/-- Every tape but `0` and `1`. -/
def clr01 : List (Fin 256) := (List.finRange 256).filter fun t => t ≠ 0 ∧ t ≠ 1

theorem mem_clr01 (t : Fin 256) : t ∈ clr01 ↔ t ≠ 0 ∧ t ≠ 1 := by simp [clr01]

/-- Clearing the scratch tapes of a store with words on `0` and `1` only. -/
theorem law_clr01 (a g : List Bool) :
    (clearL clr01).law (io2 (R := 254) a g []) = PMF.pure (io2 (R := 254) a g []) := by
  rw [law_clearL]
  congr 1
  funext t
  by_cases h0 : t = 0
  · subst h0; simp [mem_clr01]
  · by_cases h1 : t = 1
    · subst h1; simp [mem_clr01]
    · have h0' : t.val ≠ 0 := fun e => h0 (Fin.ext e)
      have h1' : t.val ≠ 1 := fun e => h1 (Fin.ext e)
      simp [mem_clr01, h0, h1, io2, h0', h1']

/-- The bit `f(0)` (the head of tape `1`) moved to the end of tape `0`. -/
def mvBit : Prog 256 := .seq (.prim (.snocHead 0 1)) (.prim (.tail 1))

theorem law_mvBit (a : List Bool) (b : Bool) (g : List Bool) :
    (XProg.prog mvBit).law (io2 (R := 254) a (b :: g) []) =
      PMF.pure (io2 (R := 254) (a ++ [b]) g []) := by
  rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _ (by simp [Prog.CoinFree, Prog.coinFreeB, mvBit])]
  congr 1
  funext t
  simp only [mvBit, Prog.run_seq, Prog.run_prim, Prim.apply, Function.update_apply, io2]
  by_cases h0 : t = 0
  · subst h0; simp
  · by_cases h1 : t = 1
    · subst h1; simp
    · have h0' : t.val ≠ 0 := fun e => h0 (Fin.ext e)
      have h1' : t.val ≠ 1 := fun e => h1 (Fin.ext e)
      simp [h0, h1, h0', h1']

variable (hk c) in
/-- **The key-row block of `KeyGen`** around a `W_f` block `wfB` on the stream: the scratch tapes
cleared (for the per-tape bounds), the bit `f(0)` moved behind the master key, the crafted data,
the `W_f` block, the key row (plus `G̲` if the bit is set). -/
def bfX (wfB : XProg 256) : XProg 256 :=
  XProg.seq (clearL clr01) (XProg.seq (XProg.prog mvBit)
    (XProg.seq (preB hk c) (XProg.seq wfB (postB hk c))))

/-! ### The words -/

theorem flatMap_eq_flatten {α : Type*} (l : List α) (f : α → List Bool) :
    l.flatMap f = (l.map f).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The word of the rows `B_j`, in the master key's word. -/
theorem msk_rows (msk : SKey hk c) :
    ((((mskEnc hk c).enc msk).drop (offBk c)).take (nJ (N := N) hk * DualUse.rowL N K k)) =
      ((Enum.list (α := JIx (N := N) hk)).map
        fun j => (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (msk.1.Bj j)).flatten := by
  have hfam : ((FixedEnc.fun (α := JIx (N := N) hk) (matEnc (N := N) (K := K) (Fin 1)
      (RingBTVW.Col k))).enc msk.1.Bj).length = nJ (N := N) hk * DualUse.rowL N K k := by
    rw [FixedEnc.length, len_row1]
  have e : (mskEnc hk c).enc msk = (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc msk.1.B₀ ++
      ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc msk.1.B₁ ++
      ((FixedEnc.fun (α := JIx (N := N) hk) (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc msk.1.Bj ++
      ((ringEnc N K).enc msk.1.p ++ (Algo.rowW N K k msk.2.1 ++ (ringEnc N K).enc msk.2.2)))) := by
    rw [Algo.mskEnc_eq]
    have : (pkEnc hk c).enc msk.1 = (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc msk.1.B₀ ++
        ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc msk.1.B₁ ++
        ((FixedEnc.fun (α := JIx (N := N) hk) (matEnc (N := N) (K := K) (Fin 1)
          (RingBTVW.Col k))).enc msk.1.Bj ++ (ringEnc N K).enc msk.1.p)) := rfl
    rw [this]; simp only [List.append_assoc]
  have hl : ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc msk.1.B₀ ++
      (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc msk.1.B₁).length = offBk c := by
    rw [List.length_append, FixedEnc.length, FixedEnc.length]; rfl
  rw [e, ← List.append_assoc, List.drop_left' hl, List.take_left' hfam, fun_enc_eq,
    flatMap_eq_flatten]
  rw [List.map_map]; rfl

theorem length_rows (mpk : PK hk c) :
    ∀ r ∈ (Enum.list (α := JIx (N := N) hk)).map
      (fun j => (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (mpk.Bj j)), r.length = DualUse.rowL N K k := by
  intro r hr
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hr
  exact length_row1 _

/-- The trapdoor part of the master key. -/
def mskT (msk : SKey hk c) : List Bool := Algo.rowW N K k msk.2.1 ++ (ringEnc N K).enc msk.2.2

theorem length_mskT (msk : SKey hk c) : (mskT msk).length = lenT N K k := by
  rw [mskT, List.length_append, ← Algo.matEnc_row, length_row1, (ringEnc N K).length]

theorem msk_split (msk : SKey hk c) :
    (mskEnc hk c).enc msk = (pkEnc hk c).enc msk.1 ++ mskT msk := Algo.mskEnc_eq hk c msk

theorem lenT_le (hk : 2 ^ K < 2 ^ k) (hd : 3 ≤ c.d) : lenT N K k ≤ lenZ c := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  simp only [lenT, lenZ, DualUse.rowL]
  generalize hQ : N * K = Q
  have h2 : 2 ≤ c.d - 1 := by omega
  have e1 : 2 * (2 * k * Q) ≤ (c.d - 1) * (2 * k * Q) := Nat.mul_le_mul_right _ h2
  have e2 : Q ≤ 2 * k * Q := by
    have := Nat.mul_le_mul_right Q (show 1 ≤ 2 * k by omega); simpa using this
  omega

variable (hk c) in
/-- The stash of `KeyGen`: the trapdoor part and the bit `f(0)`, padded to `d - 1` rows. -/
def stashB (b : Bool) (msk : SKey hk c) : List Bool :=
  mskT msk ++ b :: List.replicate (lenZ c - (lenT N K k + 1)) false

theorem length_stashB (hS : lenT N K k + 1 ≤ lenZ c) (b : Bool) (msk : SKey hk c) :
    (stashB hk c b msk).length = lenZ c := by
  rw [stashB, List.length_append, length_mskT, List.length_cons, List.length_replicate]
  omega

theorem psi0_word :
    (FixedEnc.fun (α := Fin nA) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc
      (fun _ => (0 : Matrix (Fin 2) (RingBTVW.Col k) (Rg N K))) = List.replicate (nA * (2 * DualUse.rowL N K k)) false := by
  rw [fun_enc_const _ _ (matEnc_zero _ _), Algo.len_fin, len_matEnc_col]

/-- **The word written by `preB`** is that of the crafted data `sdB`. -/
theorem sdEnc_sdB (hd : 3 ≤ c.d) (hS : lenT N K k + 1 ≤ lenZ c) (b : Bool) (msk : SKey hk c) :
    (sdEnc hk c).enc (sdB hk c msk.1 (stashB hk c b msk)) =
      ((mskEnc hk c).enc msk ++ [b]).take (lenPK hk c) ++ List.replicate (c.d * (N * K)) false ++
        List.replicate (nA * (c.d * DualUse.rowL N K k)) false ++
        wPart (((((mskEnc hk c).enc msk ++ [b])).drop (lenPK hk c)).take (lenT N K k + 1) ++
            List.replicate (lenZ c - (lenT N K k + 1)) false) (List.replicate (lenZ c) false)
          ((Enum.list (α := JIx (N := N) hk)).map
            fun j => (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (msk.1.Bj j)) ++
        List.replicate (nA * (2 * DualUse.rowL N K k)) false ++ List.replicate nA false := by
  have hp : ((pkEnc hk c).enc msk.1).length = lenPK hk c := length_enc_fixLen _ _
  rw [sdB, sdEnc_sdOf msk.1 (fun _ => by simp) _ (length_stashB hS b msk) (by omega), psi0_word,
    msk_split, show (pkEnc hk c).enc msk.1 ++ mskT msk ++ [b] = (pkEnc hk c).enc msk.1 ++
      (mskT msk ++ [b]) from List.append_assoc _ _ _, List.take_left' hp, List.drop_left' hp,
    List.take_of_length_le (by rw [List.length_append, length_mskT]; simp), flatMap_const_replicate,
      List.length_finRange]
  simp only [stashB, List.append_assoc, List.singleton_append]

/-! ### The laws of the block -/

theorem enum_JIx_ne_nil (hk : 2 ^ K < 2 ^ k) (hN : 0 < N) : (Enum.list (α := JIx (N := N) hk)) ≠ [] := by
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  intro h
  have := Enum.complete (α := JIx (N := N) hk)
    ((⟨0, by norm_num⟩ : Fin nA), ((0 : Fin 2), ((0 : Fin 2), (⟨0, hk0⟩ : Fin k)), (⟨0, hk0⟩ : Fin k), (⟨0, hN⟩ : Fin N)))
  rw [h] at this
  simp at this

theorem take_drop_append_of_len (l r : List Bool) {o n : ℕ}
    (h : ((l.drop o).take n).length = n) : ((l ++ r).drop o).take n = (l.drop o).take n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : o + n ≤ l.length := by
    rw [List.length_take, List.length_drop] at h
    have := min_eq_left_iff.mp h
    omega
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem msk_rows_len (msk : SKey hk c) :
    ((((mskEnc hk c).enc msk).drop (offBk c)).take (nJ (N := N) hk * DualUse.rowL N K k)).length =
      nJ (N := N) hk * DualUse.rowL N K k := by
  rw [msk_rows msk, List.length_flatten, List.map_map]
  simp only [Function.comp_def, FixedEnc.length, len_row1, List.map_const', List.sum_replicate,
    List.length_map, smul_eq_mul]

theorem law_preB (hd : 3 ≤ c.d) (hS : lenT N K k + 1 ≤ lenZ c) (msk : SKey hk c) (b : Bool)
    (g : List Bool) :
    (preB hk c).law (io2 (R := 254) ((mskEnc hk c).enc msk ++ [b]) g []) =
      PMF.pure (io2 (R := 254) ((sdEnc hk c).enc (sdB hk c msk.1 (stashB hk c b msk))) g []) := by
  rw [preB, XProg.law_frame, io2_eLo, ← io1_sto,
    law_preCoreB _ _ _ _ _ _ _ _ _ _ _ _ _
      ((take_drop_append_of_len _ _ (msk_rows_len msk)).trans (msk_rows msk))
      (length_rows msk.1) (by simp)
      (by rw [msk_split, show (pkEnc hk c).enc msk.1 ++ mskT msk ++ [b] = (pkEnc hk c).enc msk.1 ++
          (mskT msk ++ [b]) from List.append_assoc _ _ _, List.drop_left' (length_enc_fixLen _ _),
        List.take_of_length_le (by rw [List.length_append, length_mskT]; simp),
        List.length_append, length_mskT]
          simp; omega),
    PMF.pure_map, io1_sto, embedF_eLo, sdEnc_sdB hd hS]

theorem sdB_split (hd : 3 ≤ c.d) (hS : lenT N K k + 1 ≤ lenZ c) (b : Bool) (msk : SKey hk c) :
    ∃ rest, (sdEnc hk c).enc (sdB hk c msk.1 (stashB hk c b msk)) =
      (pkEnc hk c).enc msk.1 ++ (List.replicate (c.d * (N * K) + nA * (c.d * DualUse.rowL N K k)) false ++
        (mskT msk ++ b :: rest)) := by
  have hne : ((Enum.list (α := JIx (N := N) hk)).map
      fun j => (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (msk.1.Bj j)) ≠ [] := by
    simpa using enum_JIx_ne_nil hk c.hN
  obtain ⟨r0, rs, hrs⟩ := List.exists_cons_of_ne_nil hne
  rw [sdB, sdEnc_sdOf msk.1 (fun _ => by simp) _ (length_stashB hS b msk) (by omega), psi0_word,
    flatMap_const_replicate, List.length_finRange, hrs, wPart, stashB]
  refine ⟨List.replicate (lenZ c - (lenT N K k + 1)) false ++ r0 ++
    wPart (List.replicate ((c.d - 1) * DualUse.rowL N K k) false)
      (List.replicate ((c.d - 1) * DualUse.rowL N K k) false) rs ++
    (List.replicate (nA * (2 * DualUse.rowL N K k)) false ++ List.replicate nA false), ?_⟩
  simp only [List.append_assoc, List.replicate_add, List.cons_append]

theorem law_postB (hd : 3 ≤ c.d) (hS : lenT N K k + 1 ≤ lenZ c) (msk : SKey hk c) (b : Bool)
    (wf : List Bool) (hwf : (wf.drop (lenZ c)).length = 1 * (2 * k) * N * K) :
    (postB hk c).law (Function.update (io2 (R := 254)
        ((sdEnc hk c).enc (sdB hk c msk.1 (stashB hk c b msk))) [] []) 2 wf) =
      PMF.pure (Function.update (io2 (R := 254) ((mskEnc hk c).enc msk) [] []) 2
        (if b then Algo.matAddW N K (1 * (2 * k)) (wf.drop (lenZ c)) (Algo.gadW N K k)
          else wf.drop (lenZ c))) := by
  obtain ⟨rest, hsd⟩ := sdB_split hd hS b msk
  have hp : ((pkEnc hk c).enc msk.1).length = lenPK hk c := length_enc_fixLen _ _
  have hz : (List.replicate (c.d * (N * K) + nA * (c.d * DualUse.rowL N K k)) false).length +
      lenPK hk c = offWk hk c := by rw [List.length_replicate, offWk]; ring
  have hdrop : ((sdEnc hk c).enc (sdB hk c msk.1 (stashB hk c b msk))).drop (offWk hk c) =
      mskT msk ++ b :: rest := by
    rw [hsd, ← hz, Nat.add_comm, ← List.drop_drop, List.drop_left' hp, List.drop_left' rfl]
  have hb : (((sdEnc hk c).enc (sdB hk c msk.1 (stashB hk c b msk))).drop
      (offWk hk c + lenT N K k)).take 1 = [b] := by
    rw [← List.drop_drop, hdrop, List.drop_left' (length_mskT msk)]; rfl
  rw [postB, XProg.law_frame, upd_eLo (by norm_num), show (⟨1, by norm_num⟩ : Fin 55) = 1 from rfl,
    law_postCoreB _ _ _ _ _ _ _ _ _ b hb hwf, PMF.pure_map]
  refine congrArg PMF.pure ((embedF_eLo_upd (hm := eLo55) (by norm_num : 1 < 55) _ _ _ _).trans ?_)
  congr 2
  rw [hdrop, List.take_left' (length_mskT msk), msk_split, hsd, List.take_left' hp]

/-! ### Well-formedness and the specification -/

theorem wf_preCoreB (L LT oB nTR Z R nT C0 RM0 PS0 PAD : ℕ) :
    (preCoreB L LT oB nTR Z R nT C0 RM0 PS0 PAD).WF :=
  ⟨wf_getAt _ _ _ _ _ _ _, wf_getAt _ _ _ _ _ _ _, wf_getAt _ _ _ _ _ _ _,
    wf_tmplP _ _ (by simp [preTmpl]), XProg.wf_zerosP (by decide), XProg.wf_zerosP (by decide),
    XProg.wf_zerosP (by decide), wf_wLoopP (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), XProg.wf_zerosP (by decide), XProg.wf_zerosP (by decide),
    trivial, wf_clearL _⟩

theorem wf_postCoreB (L LT oW Zr N K k : ℕ) : (postCoreB L LT oW Zr N K k).WF :=
  ⟨wf_getAt _ _ _ _ _ _ _, wf_getAt _ _ _ _ _ _ _, wf_getAt _ _ _ _ _ _ _, trivial,
    wf_prefP _ _ _ _ _, wf_prefP _ _ _ _ _, wf_tailsP _ _, wf_tmplP _ _ (by simp [postTmpl]),
    ⟨⟨Prog.WF.map uG_inj Prog.wf_gadP, Prog.WF.map uA_inj Prog.wf_addRWP, trivial⟩, trivial⟩,
    wf_clearL _⟩

theorem matAdd_rowW (A B : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) :
    Algo.matAddW N K (1 * (2 * k)) (Algo.rowW N K k A) (Algo.rowW N K k B) =
      Algo.rowW N K k (A + B) := by
  simp only [Algo.rowW]
  rw [Algo.matAddW_enc]
  rfl

/-- **The key-row block meets its specification**, for any `W_f` block meeting `WfSpecS` (the law
on the instruction stream, the tail of the block word). -/
theorem bfSpec_bfX (hd : 3 ≤ c.d) (hS : lenT N K k + 1 ≤ lenZ c) {wfB : XProg 256} {W : ℕ}
    (hwf : WfSpecS hk c wfB W) : BfSpec hk c (bfX hk c wfB) W where
  wf := ⟨wf_clearL _, ⟨trivial, trivial⟩, wf_preCoreB _ _ _ _ _ _ _ _ _ _ _, hwf.wf,
    wf_postCoreB _ _ _ _ _ _ _⟩
  law msk C hL hC := by
    have hd0 : 0 < c.d := by omega
    have hcl := colsW_last hd0 (simW (sdB hk c msk.1 (stashB hk c (bit0 C) msk)) C)
    rw [bfX, XProg.law_seq_pure (law_clr01 _ _), blockWord_eq,
      XProg.law_seq_pure (law_mvBit _ _ _), XProg.law_seq_pure (law_preB hd hS msk _ _),
      XProg.law_seq_pure (by
        have := hwf.law (sdB hk c msk.1 (stashB hk c (bit0 C) msk)) C hL hC
        rwa [blockWord_eq, List.tail_cons] at this),
      law_postB hd hS msk _ _ (by rw [hcl, Algo.length_rowW]; ring)]
    congr 2
    rw [hcl, keyMatrix_sdB hd0 msk.1 (length_stashB hS (bit0 C) msk) C]
    cases bit0 C
    · simp only [bitR, Bool.false_eq_true, if_false, zero_smul, add_zero]; rfl
    · rw [if_pos rfl, Algo.gadW_enc hk.le, matAdd_rowW]
      simp [bitR]
      rfl

end AdvancedEncryption.DualUse.Prog
