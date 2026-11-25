import PE.Impl.ExpLUT.Prog.RedKeyURow
import PE.Impl.ExpLUT.Prog.RedKeyTry
import PE.Impl.ExpLUT.Prog.KeyBHCodec
/-!
# `KGsim` on the VM (package G2, item 5): the vector `u` of the simulated correction

The routine `uC D` (`RedKeyPLAN.md`, module 3): from `mpk` (register `14`) and the digits `z`
(register `17`) it leaves `u = gadDec (M_F (0, z) − (I_W ⊗ g) z)` in register `20`:

1. the ring one in register `7` (F3's `ringOneC`); the gadget row `b = (B⁽¹⁾_c)_c` of the public
   key in register `10` (prefix of the public-key word, F3's `gatherC`);
2. for every row `i < W`, `uRowC K (rowExponent D i)` (`RedKeyURow`): the rows
   `Σ_c σ_i(b_c) z(i,c)` of `M_F (0, z)` (register `12`) and `Σ_c 2^c z(i,c)` of `(I_W ⊗ g) z`
   (register `13`);
3. F3's `decRowsC` on the two row queues: the digits of the differences, row-major.

* generic: `uRowsC`, **`exec_uRowsC`**; `bRowC`, **`exec_bRowC`**;
* **`uOk_uC : UOk D (uC D)`** (for `2 ≤ K`): the contract of `RedKeyTry`, so
  `simTryKeyC D (uC D) B r` is a complete single try with the simulated trapdoor once the rows of
  `X` are in register `16`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape
  SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)
open Cslib.Probability Cslib.BitString

variable {N K : ℕ}

/-- The rows `is` (their exponents `e i`). -/
def uRowsC (K : ℕ) (e : ℕ → ℕ) : List ℕ → Code
  | [] => .nop
  | i :: is => .seq (uRowC K (e i)) (uRowsC K e is)

theorem wf_uRowsC (K : ℕ) (e : ℕ → ℕ) : ∀ is, (uRowsC K e is).WFc
  | [] => trivial
  | _ :: is => ⟨wf_uRowC _ _, wf_uRowsC K e is⟩

theorem uRowsC_frame (K : ℕ) (e : ℕ → ℕ) : ∀ (is : List ℕ) (r : Fin 64),
    (uRowsC K e is).writes r = true → r ∈ [rQa, rQb, rQc, rQk, rIa, rQx, rQy, rUz, rUp, rUg]
  | [], r, h => by simp [uRowsC, Code.writes] at h
  | i :: is, r, h => by
    simp only [uRowsC, Code.writes, Bool.or_eq_true] at h
    rcases h with h | h
    · exact uRowC_frame K (e i) r h
    · exact uRowsC_frame K e is r h

/-- **All rows**: for rows `rs` (index, digits), register `12` gets the public rows, `13` the
gadget rows. -/
theorem exec_uRowsC (hN : 0 < N) (hK : 0 < K) (e : ℕ → ℕ) (he : ∀ i, 0 < e i) (b : List (Rq N K))
    (hb : b.length = K) :
    ∀ (rs : List (ℕ × List (Rq N K))) (w : St) (rest P G : List (Rq N K)),
    (∀ r ∈ rs, r.2.length = K) →
    w rUb = encL N K b → w rUz = encL N K ((rs.map Prod.snd).flatten ++ rest) →
    w rUp = encL N K P → w rUg = encL N K G →
    w rB1 = [false] → w rZ = encRM N K 0 → w rUo = encRM N K 1 →
    exec N K (uRowsC K e (rs.map Prod.fst)) w rUp = encL N K (P ++ rs.map fun r =>
      (List.zipWith (· * ·) (b.map (aut N (e r.1))) r.2).sum) ∧
    exec N K (uRowsC K e (rs.map Prod.fst)) w rUg = encL N K (G ++ rs.map fun r =>
      ∑ j ∈ Finset.range K, 2 ^ j * r.2.getD j 0)
  | [], w, rest, P, G, _, _, _, hp, hg, _, _, _ => by simp [uRowsC, hp, hg]
  | r :: rs, w, rest, P, G, hl, h10, h11, h12, h13, h1, hZ, hO => by
    have hr : r.2.length = K := hl r (List.mem_cons_self ..)
    obtain ⟨g11, g12, g13⟩ := exec_uRowC hN hK w b r.2 ((rs.map Prod.snd).flatten ++ rest) P G
      (e r.1) (he _) hb hr h10 (by simpa [List.append_assoc] using h11) h12 h13 h1 hZ hO
    set v := exec N K (uRowC K (e r.1)) w
    have keep : ∀ q : Fin 64, q ∉ [rQa, rQb, rQc, rQk, rIa, rQx, rQy, rUz, rUp, rUg] → v q = w q :=
      fun q hq => exec_writes _ _ _ (writes_false_of_frame (uRowC_frame K (e r.1)) hq)
    have ih := exec_uRowsC hN hK e he b hb rs v rest _ _ (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      ((keep rUb (by decide)).trans h10) g11 g12 g13 ((keep rB1 (by decide)).trans h1)
      ((keep rZ (by decide)).trans hZ) ((keep rUo (by decide)).trans hO)
    simp only [List.map_cons, uRowsC, exec_seq]
    simpa only [List.append_assoc, List.singleton_append] using ih

/-! ### The gadget row of `B⁽¹⁾` -/

variable (D : Dims)

/-- The positions of `B⁽¹⁾_c` in the B/H prefix of the public key. -/
noncomputable def bRowIdx : List ℕ :=
  (List.ofFn fun c : Fin D.K => (Sum.inl ((0 : Fin 2), Sum.inr c) : BHSource D)).map Enum.index

/-- `10 := (B⁽¹⁾_c)_c` from the public key in register `14`. -/
noncomputable def bRowC : Code :=
  .seq (.cp 0 14) <| .seq (prefixC (bhPrefixLength D)) (saveQueueC (gatherC D.N D.K (bRowIdx D)) rUb)

theorem wf_bRowC : (bRowC D).WFc := ⟨trivial, wf_prefixC _, wf_gatherC _ _ _, trivial⟩

theorem bRowC_frame (r : Fin 64) (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4)
    (h10 : r ≠ rUb) : (bRowC D).writes r = false := by
  simp only [bRowC, Code.writes, prefixC_preserves _ r h0 h2 h3,
    saveQueueC_frame _ _ _ (gatherC_preserves D.N D.K _ r h1 h2 h3 h4) h10, Bool.or_false,
    beq_eq_false_iff_ne]
  exact Ne.symm h0

variable {D}

/-- **The gadget row of `B⁽¹⁾`.** -/
theorem exec_bRowC (mpk : MPKt D) (w : St) (hM : w 14 = (mpkEnc D).enc mpk)
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (bRowC D) w rUb =
      encL D.N D.K (List.ofFn fun c : Fin D.K => mpk.B 0 (Sum.inr c)) := by
  obtain ⟨tail, ht⟩ := mpkEnc_bhPrefix D mpk
  have hl : (encL D.N D.K (Enum.list.map (bhSource D mpk))).length = bhPrefixLength D := by
    simp [length_encL, bhPrefixLength]
  rw [bRowC, exec_seq, exec_seq, exec_saveQueueC]
  have hS : exec D.N D.K (prefixC (bhPrefixLength D)) (exec D.N D.K (.cp 0 14) w) 0 =
      encL D.N D.K (Enum.list.map (bhSource D mpk)) := by
    rw [← hl]
    exact exec_prefixC _ tail _ (by simp [hM, ht]) (by simp [h1])
  have h := exec_gatherC_family (bhSource D mpk)
    (List.ofFn fun c : Fin D.K => (Sum.inl ((0 : Fin 2), Sum.inr c) : BHSource D)) _ hS
    (by rw [exec_writes _ _ _ (prefixC_preserves _ rB1 (by decide) (by decide) (by decide))]
        simp [h1])
    (by rw [exec_writes _ _ _ (prefixC_preserves _ rZ (by decide) (by decide) (by decide))]
        simp [hZ])
  rw [bRowIdx, h, List.map_ofFn]
  rfl

/-! ### The routine -/

variable (D)

/-- **The `u` routine.** -/
noncomputable def uC : Code :=
  .seq (ringOneC D.N D.K) <| .seq (bRowC D) <| .seq (.cp rUz 17) <| .seq (.clr rUp) <|
  .seq (.clr rUg) <| .seq (uRowsC D.K (rowExponent D) (List.ofFn fun i : Fin (setting D).E.W => i.val)) <|
  .seq (.cp rQa rUp) <| .seq (.cp rQb rUg) <| .seq (natC rQc rB1 (setting D).E.W) <|
  .seq (natC rQk rB1 D.K) <| .seq decRowsC (.cp rVu rDq)

theorem wf_uC : (uC D).WFc :=
  ⟨wf_ringOneC _ _, wf_bRowC D, trivial, trivial, trivial, wf_uRowsC _ _ _, trivial, trivial,
    natC_wfc _ _ _, natC_wfc _ _ _, wf_decRowsC, trivial⟩

theorem uC_frame (r : Fin 64) (hr : r = 9 ∨ r = 16 ∨ r = 17 ∨ r = rB1 ∨ r = rZ) :
    (uC D).writes r = false := by
  have hb := bRowC_frame D r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have hu := writes_false_of_frame (uRowsC_frame D.K (rowExponent D)
    (List.ofFn fun i : Fin (setting D).E.W => i.val)) (r := r)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have hd := writes_false_of_frame (c := decRowsC) (r := r)
    (l := [rDq, rQa, rQb, rQc, rQx, rIa, rY, rZq, rU, rCK, rTd])
    (by simp only [decRowsC, decRowBodyC, decRowLoadC, decomposeC, digQC, digQBody, Code.writes]
        decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have ho := writes_false_of_frame (c := ringOneC D.N D.K) (r := r) (l := [5, 6, 7])
    (by simp only [ringOneC, bitsC, Code.writes, natC_writes_eq]; decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  simp only [uC, Code.writes, hb, hu, hd, ho, natC_writes_eq, Bool.or_false, Bool.false_or]
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ### The rows are the rows of `M_F (0, z)` and of `(I_W ⊗ g) z` -/

variable {D}

theorem pubRow_eq (mpk : MPKt D) (F : BP Pos) (z : ZIdxS D → Rg D) (i : Fin (setting D).E.W) :
    (List.zipWith (· * ·) ((List.ofFn fun c : Fin D.K => mpk.B 0 (Sum.inr c)).map
      (aut D.N (rowExponent D i.val))) (List.ofFn fun c : Fin D.K => z (i, c))).sum =
      pubZ (helperMap D) mpk F z i := by
  rw [zip_aut_ofFn, pubZ_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [aut_rowExponent]

theorem gadRow_eq (z : ZIdxS D → Rg D) (i : Fin (setting D).E.W) :
    ∑ j ∈ Finset.range D.K, (2 : Rg D) ^ j * (List.ofFn fun c : Fin D.K => z (i, c)).getD j 0 =
      gadZ z i := by
  rw [Finset.sum_range, gadZ]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hg : (setting D).D.g c = algebraMap (ZMod D.q) (Rg D) (2 ^ (c : ℕ)) := rfl
  rw [hg, map_pow, map_ofNat]

/-- **The `u` routine meets the contract of the simulated try.** -/
theorem uOk_uC (hK : 2 ≤ D.K) : UOk D (uC D) where
  wf := wf_uC D
  frame := uC_frame D
  exec mpk F z w hM hz h1 hZ := by
    have hK0 : 0 < D.K := by omega
    -- the rows
    let rs : List (ℕ × List (Rg D)) := List.ofFn fun i : Fin (setting D).E.W =>
      (i.val, List.ofFn fun c : Fin D.K => z (i, c))
    have hfst : (List.ofFn fun i : Fin (setting D).E.W => i.val) = rs.map Prod.fst := by
      simp [rs, List.map_ofFn, Function.comp_def]
    have hsnd : Enum.list.map z = (rs.map Prod.snd).flatten ++ [] := by
      rw [List.append_nil, enum_gadget_order]
      simp [rs, List.map_ofFn, Function.comp_def]
    -- ring one, gadget row, queues
    have o7 := exec_ringOneC D.N_pos hK w h1
    set s1 := exec D.N D.K (ringOneC D.N D.K) w with hs1
    have f1 : ∀ r : Fin 64, r ∉ [5, 6, 7] → s1 r = w r := fun r hr =>
      exec_writes _ _ _ (writes_false_of_frame (c := ringOneC D.N D.K) (l := [5, 6, 7])
        (by simp only [ringOneC, bitsC, Code.writes, natC_writes_eq]; decide) hr)
    have b10 := exec_bRowC mpk s1 ((f1 14 (by decide)).trans hM) ((f1 rB1 (by decide)).trans h1)
      ((f1 rZ (by decide)).trans hZ)
    set s2 := exec D.N D.K (bRowC D) s1 with hs2
    have f2 : ∀ r : Fin 64, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ rUb → s2 r = s1 r :=
      fun r a b c d e g => exec_writes _ _ _ (bRowC_frame D r a b c d e g)
    have q : ∀ r : Fin 64, r ∉ [0, 1, 2, 3, 4, 5, 6, 7, rUb] → s2 r = w r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [f2 r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.2.2.2, f1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1⟩)]
    set s3 := exec D.N D.K (.clr rUg) (exec D.N D.K (.clr rUp) (exec D.N D.K (.cp rUz 17) s2))
      with hs3
    have f3 : ∀ r : Fin 64, r ≠ rUz → r ≠ rUp → r ≠ rUg → s3 r = s2 r := by
      intro r a b c; simp [hs3, Function.update_of_ne a, Function.update_of_ne b,
        Function.update_of_ne c]
    have h3z : s3 rUz = encL D.N D.K ((rs.map Prod.snd).flatten ++ []) := by
      rw [← hsnd]; simp [hs3, q 17 (by decide), hz]
    obtain ⟨r12, r13⟩ := exec_uRowsC D.N_pos hK0 (rowExponent D) (rowExponent_pos D)
      (List.ofFn fun c : Fin D.K => mpk.B 0 (Sum.inr c)) (by simp) rs s3 [] [] []
      (by intro r hr; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr; simp)
      (by rw [f3 _ (by decide) (by decide) (by decide), b10]) h3z (by simp [hs3]) (by simp [hs3])
      (by rw [f3 _ (by decide) (by decide) (by decide), q _ (by decide), h1])
      (by rw [f3 _ (by decide) (by decide) (by decide), q _ (by decide), hZ])
      (by rw [f3 _ (by decide) (by decide) (by decide), f2 _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), o7])
    -- the decomposition
    let rows : List (Rg D × Rg D) := List.ofFn fun i : Fin (setting D).E.W =>
      (pubZ (helperMap D) mpk F z i, gadZ z i)
    have e12 : [] ++ rs.map (fun r => (List.zipWith (· * ·) ((List.ofFn fun c : Fin D.K =>
        mpk.B 0 (Sum.inr c)).map (aut D.N (rowExponent D r.1))) r.2).sum) = rows.map Prod.fst := by
      simp only [List.nil_append, rs, rows, List.map_ofFn, Function.comp_def]
      exact congrArg List.ofFn (funext fun i => by rw [← pubRow_eq mpk F z i, List.map_ofFn]; rfl)
    have e13 : [] ++ rs.map (fun r => ∑ j ∈ Finset.range D.K, (2 : Rg D) ^ j * r.2.getD j 0) =
        rows.map Prod.snd := by
      simp only [List.nil_append, rs, rows, List.map_ofFn, Function.comp_def]
      exact congrArg List.ofFn (funext fun i => gadRow_eq z i)
    rw [← hfst] at r12 r13
    rw [e12] at r12
    rw [e13] at r13
    set s4 := exec D.N D.K (uRowsC D.K (rowExponent D)
      (List.ofFn fun i : Fin (setting D).E.W => i.val)) s3 with hs4
    have f4 : ∀ r : Fin 64, r ∉ [rQa, rQb, rQc, rQk, rIa, rQx, rQy, rUz, rUp, rUg] → s4 r = s3 r :=
      fun r hr => exec_writes _ _ _ (writes_false_of_frame (uRowsC_frame _ _ _) hr)
    have hB4 : s4 rB1 = [false] := by
      rw [f4 _ (by decide), f3 _ (by decide) (by decide) (by decide), q _ (by decide), h1]
    have hZ4 : s4 rZ = encRM D.N D.K 0 := by
      rw [f4 _ (by decide), f3 _ (by decide) (by decide) (by decide), q _ (by decide), hZ]
    set s5 := exec D.N D.K (.cp rQb rUg) (exec D.N D.K (.cp rQa rUp) s4) with hs5
    have e6 := exec_natC (N := D.N) (K := D.K) rQc rB1 (by decide) (setting D).E.W s5
      (by simp [hs5, hB4])
    set s6 := Function.update s5 rQc (List.replicate (setting D).E.W false) with hs6
    have e7 := exec_natC (N := D.N) (K := D.K) rQk rB1 (by decide) D.K s6
      (by simp [hs6, hs5, hB4])
    set s7 := Function.update s6 rQk (List.replicate D.K false) with hs7
    obtain ⟨-, -, d⟩ := exec_decRowsC hK0 s7 rows (by simp [hs7, hs6, hs5, r12])
      (by simp [hs7, hs6, hs5, r13]) (by simp [hs7, hs6, rows]) (by simp [hs7])
      (by simp [hs7, hs6, hs5, hB4]) (by simp [hs7, hs6, hs5, hZ4])
    simp only [uC, exec_seq]
    rw [← hs1, ← hs2, ← hs3, ← hs4, ← hs5, e6, e7, exec_cp, Function.update_self, d]
    rw [rows_digits_gadDec D (pubZ (helperMap D) mpk F z) (gadZ z), uVec, enum_gadget_order]
    rfl

open Params in
/-- **The simulated try at the concrete parameters, with the `u` routine**: fair coins, the
decoder and `simTryKeyC Dc (uC Dc) Bk rSmall` give the encoded key law of `T_sim` (box `kbDc`),
for ready states whose register `16` holds the rows of `X = simX M (h1Of mpk) A_F R̂`. -/
theorem map_coins_exec_simTryKeyC_uC_Dc (mpk : MPKt Dc) (F : BP Pos)
    (Rh : SimMat (Wb Dc) (Jh Dc) (setting Dc)) (states : (PIdxS Dc → Rg Dc) → St)
    (ready : ∀ p, SimTryReady mpk F
      (fun q ic => simX (helperMap Dc) (h1Of mpk) (keyPK (helperMap Dc) mpk F) Rh q ic) p
        (states p)) :
    (uniformList (nPI Dc * Dc.N * Bk)).map
      (fun cs ↦ exec Dc.N Dc.K (simTryKeyC Dc (uC Dc) Bk rSmall) (states (coinDec Dc Bk cs)) 19) =
    ((keyLaw (S := setting Dc) kbDc.Big kbDc.Small kbDc.hBig gadDec (helperMap Dc) mpk F
      (simTrap (helperMap Dc) mpk F Rh)).map keyOfOutput).map (keyEnc Dc).enc :=
  map_coins_exec_simTryKeyC_Dc (uOk_uC (by change 2 ≤ Kc; rw [Kc_def]; norm_num)) mpk F Rh
    states ready

end AdvancedEncryption.ExpLUT.Prog
