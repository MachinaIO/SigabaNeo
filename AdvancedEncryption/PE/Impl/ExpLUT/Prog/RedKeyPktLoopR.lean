import PE.Impl.ExpLUT.Prog.RedKeyPktLoop
/-!
# The packet stream, part 7: the loop over the `η` slabs (generic `N K`)

For `t₀ < b` (`ptT0` holds `2 t₀` bits), `s ∈ {0, 1}` (unrolled), `j < nC` (`ptCj` holds `j` zero
words): the selector `ptSelVM t₀ s` (bits `[k = (t, 1), k = (t, 0)]_t` of `k = (t₀, s)`), the unit
row `ptUnitVM j`, one packet (`ptSlabInrC`). **`exec_ptInrLoopC`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Selectors and unit rows -/

/-- The selector of `(t₀, s)` as built: `0^{2t₀} ++ [s = 1, s = 0] ++ 0^{2b − 2t₀ − 2}`. -/
def ptSelVM (b t0 : ℕ) (s : Bool) : List Bool :=
  List.replicate (2 * t0) false ++ ([s, !s] ++ (List.replicate (2 * b) false).drop (2 * t0 + 2))

/-- The unit row `j` as built (zero words `Z`, the word `O`). -/
def ptUnitVM (O Z : List Bool) (nC j : ℕ) : List Bool :=
  (List.replicate j Z).flatten ++ (O ++ ((List.replicate nC Z).flatten.drop (j * Z.length + Z.length)))

/-- The selector of `s` (`true`: `[true, false]`, i.e. `k = (t₀, 1)`). -/
def ptSelSetC (s : Bool) : Code :=
  .seq (.cp ptSel ptT0) <|
  .seq (if s then .app ptSel ptBT else .app ptSel ptB1) <|
  .seq (if s then .app ptSel ptB1 else .app ptSel ptBT) <|
  .seq (.cp ptR ptZS) <| .seq (.drop ptR ptT0) <| .seq (.drop ptR ptB1) <| .seq (.drop ptR ptB1)
    (.app ptSel ptR)

/-- The unit row of `ptCj`. -/
def ptUnitC : Code :=
  .seq (.cp ptU ptCj) <| .seq (.app ptU ptOne) <| .seq (.cp ptR ptZ2) <| .seq (.drop ptR ptCj) <|
  .seq (.drop ptR ptZero) (.app ptU ptR)

/-- One `η` slab. -/
def ptJBody (s : Bool) : Code := .seq (ptSelSetC s) (.seq ptUnitC (.seq ptSlabInrC (.app ptCj ptZero)))

/-- The `nC` slabs of `(t₀, s)`. -/
def ptJLoopC (s : Bool) : Code := .seq (.clr ptCj) (.seq (.cp ptLB ptTC) (.rep ptLB (ptJBody s)))

/-- The slabs of `t₀`. -/
def ptT0Body : Code :=
  .seq (ptJLoopC false) <| .seq (ptJLoopC true) <| .seq (.app ptT0 ptB1) (.app ptT0 ptB1)

/-- **The `η` slabs.** -/
def ptInrLoopC : Code := .seq (.clr ptT0) (.seq (.cp ptLA ptTB) (.rep ptLA ptT0Body))

/-- The registers the `η` loop reads and never writes. -/
def ptInrKeep (r : Fin 64) : Bool :=
  ptRowConstR r || ptSkR r || r == ptBT || r == ptB1 || r == ptZS

theorem ptJBody_writes (s : Bool) : ∀ r : Fin 64, ptInrKeep r = true ∨ r = ptLB ∨ r = ptLA ∨
    r = ptT0 → (ptJBody s).writes r = false := by
  cases s <;> decide

theorem ptT0Body_writes : ∀ r : Fin 64, ptInrKeep r = true ∨ r = ptLA →
    ptT0Body.writes r = false := by
  decide

theorem exec_ptSelSetC {N K : ℕ} (s : Bool) (w : St) (b t0 : ℕ) (hT0 : w ptT0 = List.replicate (2 * t0) false)
    (hBT : w ptBT = [true]) (hB1 : w ptB1 = [false]) (hZS : w ptZS = List.replicate (2 * b) false) :
    exec N K (ptSelSetC s) w ptSel = ptSelVM b t0 s ∧
      ∀ r, r ≠ ptSel → r ≠ ptR → exec N K (ptSelSetC s) w r = w r := by
  cases s <;>
  · simp only [ptSelSetC, exec_seq, exec_cp, exec_app, exec_drop, if_false, if_true,
      Bool.false_eq_true, show (ptR : Fin 64) ≠ ptT0 by decide, show (ptR : Fin 64) ≠ ptB1 by decide]
    refine ⟨?_, fun r h1 h2 => by simp [Function.update_apply, h1, h2]⟩
    simp only [Function.update_apply, show (ptSel : Fin 64) ≠ ptR by decide,
      show (ptT0 : Fin 64) ≠ ptR by decide, show (ptT0 : Fin 64) ≠ ptSel by decide,
      show (ptB1 : Fin 64) ≠ ptR by decide, show (ptB1 : Fin 64) ≠ ptSel by decide,
      show (ptBT : Fin 64) ≠ ptSel by decide, show (ptZS : Fin 64) ≠ ptR by decide,
      show (ptZS : Fin 64) ≠ ptSel by decide, show (ptR : Fin 64) ≠ ptSel by decide, if_true,
      if_false, hT0, hBT, hB1, hZS, List.length_replicate, List.length_singleton, List.drop_drop]
    simp [ptSelVM, List.append_assoc, Nat.add_comm, Nat.add_left_comm]
    all_goals omega

theorem exec_ptUnitC {N K : ℕ} (w : St) (O Z : List Bool) (nC j : ℕ)
    (hCj : w ptCj = (List.replicate j Z).flatten) (hO : w ptOne = O) (hZ : w ptZero = Z)
    (hZ2 : w ptZ2 = (List.replicate nC Z).flatten) :
    exec N K ptUnitC w ptU = ptUnitVM O Z nC j ∧
      ∀ r, r ≠ ptU → r ≠ ptR → exec N K ptUnitC w r = w r := by
  simp only [ptUnitC, exec_seq, exec_cp, exec_app, exec_drop,
    show (ptR : Fin 64) ≠ ptCj by decide, show (ptR : Fin 64) ≠ ptZero by decide, if_false]
  refine ⟨?_, fun r h1 h2 => by simp [Function.update_apply, h1, h2]⟩
  simp only [Function.update_apply, show (ptU : Fin 64) ≠ ptR by decide,
    show (ptCj : Fin 64) ≠ ptR by decide, show (ptCj : Fin 64) ≠ ptU by decide,
    show (ptOne : Fin 64) ≠ ptU by decide, show (ptZero : Fin 64) ≠ ptR by decide,
    show (ptZ2 : Fin 64) ≠ ptR by decide, show (ptR : Fin 64) ≠ ptU by decide, if_true, if_false,
    hCj, hO, hZ, hZ2, List.drop_drop]
  simp only [ptUnitVM, List.append_assoc]
  congr 3
  rw [List.length_flatten]
  simp [List.map_replicate, List.sum_replicate, Nat.add_comm]

/-- The packet of an `η` slab with selector `sel` and unit row `U`. -/
def ptInrPk (b nD : ℕ) (Z2 ZL : List Bool) (G Aa Hf SP PU : ℕ → List Bool) (A0 : List Bool)
    (sel U : List Bool) : List Bool :=
  ptPacket b G (fun _ => ptAdRW nD Z2) (ptCrRW Z2 sel U) Aa (ptHrRW Z2 sel U) Hf (Z2 ++ ZL) A0 SP
    (fun _ => Z2) (fun _ => ptAdRW nD Z2) PU

/-- The `nC` packets of `(t₀, s)`. -/
def ptJPk (b nC nD : ℕ) (O Z Z2 ZL : List Bool) (G Aa Hf SP PU : ℕ → List Bool) (A0 : List Bool)
    (t0 : ℕ) (s : Bool) : List Bool :=
  (List.range nC).flatMap fun j => ptInrPk b nD Z2 ZL G Aa Hf SP PU A0 (ptSelVM b t0 s) (ptUnitVM O Z nC j)

/-- The inputs of the `η` loop. -/
structure PtInrIn (m nC nD b : ℕ) (O Z Z2 ZL : List Bool) (G Aa Hf SP PU : ℕ → List Bool)
    (A0 : List Bool) (w : St) : Prop where
  sk : PtSkIn b G Aa Hf SP PU A0 w
  rc : PtRowConst m nC nD O Z Z2 ZL w
  bt : w ptBT = [true]
  b1 : w ptB1 = [false]
  zs : w ptZS = List.replicate (2 * b) false
  z2 : Z2 = (List.replicate nC Z).flatten

theorem PtInrIn.of_frame {m nC nD b : ℕ} {O Z Z2 ZL : List Bool} {G Aa Hf SP PU : ℕ → List Bool}
    {A0 : List Bool} {w w' : St} (h : PtInrIn m nC nD b O Z Z2 ZL G Aa Hf SP PU A0 w)
    (hw : ∀ r, ptInrKeep r = true → w' r = w r) : PtInrIn m nC nD b O Z Z2 ZL G Aa Hf SP PU A0 w' :=
  ⟨h.sk.of_frame fun r hr => hw r (by simp [ptInrKeep, hr]),
   h.rc.of_frame fun r hr => hw r (by simp [ptInrKeep, hr]),
   by rw [hw _ rfl]; exact h.bt, by rw [hw _ rfl]; exact h.b1, by rw [hw _ rfl]; exact h.zs, h.z2⟩

/-- **The `nC` slabs of `(t₀, s)`.** -/
theorem exec_ptJLoopC {N K : ℕ} (m nC nD b : ℕ) (O Z Z2 ZL : List Bool)
    {G Aa Hf SP PU : ℕ → List Bool} {A0 : List Bool} (s : Bool) (t0 : ℕ) (w : St)
    (hin : PtInrIn m nC nD b O Z Z2 ZL G Aa Hf SP PU A0 w)
    (hT0 : w ptT0 = List.replicate (2 * t0) false) :
    exec N K (ptJLoopC s) w rAinS = w rAinS ++ ptJPk b nC nD O Z Z2 ZL G Aa Hf SP PU A0 t0 s ∧
      ∀ r, ptInrKeep r = true ∨ r = ptLA ∨ r = ptT0 → exec N K (ptJLoopC s) w r = w r := by
  set w1 := exec N K (.cp ptLB ptTC) (exec N K (.clr ptCj) w) with hw1
  have hfr1 : ∀ r, r ≠ ptLB → r ≠ ptCj → w1 r = w r := fun r h1 h2 => by
    simp [hw1, Function.update_apply, h1, h2]
  have hcnt : (w1 ptLB).length = nC := by simp [hw1, hin.rc.tc]
  have key := exec_rep_inv2 (N := N) (K := K) ptLB (ptJBody s) (ptJBody_writes s _ (by simp))
    (fun j v => v rAinS = w rAinS ++ (List.range j).flatMap (fun j =>
      ptInrPk b nD Z2 ZL G Aa Hf SP PU A0 (ptSelVM b t0 s) (ptUnitVM O Z nC j)) ∧
      v ptCj = (List.replicate j Z).flatten) w1
    ⟨by rw [hfr1 _ (by decide) (by decide)]; simp, by simp [hw1, Function.update_apply]⟩
    (by
      intro j v hj hP _ hfr
      rw [hcnt] at hj
      obtain ⟨h1, h2⟩ := hP
      set v1 := Function.update v ptLB (v ptLB).tail with hv1
      have fr : ∀ r, ptInrKeep r = true ∨ r = ptLA ∨ r = ptT0 → v1 r = w r := by
        intro r hr
        have hrB : r ≠ ptLB := by rintro rfl; revert hr; decide
        have hrJ : r ≠ ptCj := by rintro rfl; revert hr; decide
        rw [hv1, Function.update_of_ne hrB, hfr r (ptJBody_writes s r (by tauto)) hrB, hfr1 r hrB hrJ]
      have hin1 := hin.of_frame fun r hr => fr r (Or.inl hr)
      obtain ⟨a1, a2⟩ := exec_ptSelSetC (N := N) (K := K) s v1 b t0
        (by rw [fr _ (by simp)]; exact hT0) hin1.bt hin1.b1 hin1.zs
      set v2 := exec N K (ptSelSetC s) v1 with hv2
      have hin2 := hin1.of_frame fun r hr => a2 r (by rintro rfl; revert hr; decide)
        (by rintro rfl; revert hr; decide)
      obtain ⟨u1, u2⟩ := exec_ptUnitC (N := N) (K := K) v2 O Z nC j
        (by rw [a2 _ (by decide) (by decide), hv1, Function.update_of_ne (by decide)]; exact h2)
        hin2.rc.one hin2.rc.zero (by rw [hin2.rc.z2, hin2.z2])
      set v3 := exec N K ptUnitC v2 with hv3
      have hin3 := hin2.of_frame fun r hr => u2 r (by rintro rfl; revert hr; decide)
        (by rintro rfl; revert hr; decide)
      obtain ⟨s1, s2⟩ := exec_ptSlabInrC (N := N) (K := K) m nC nD b O Z Z2 ZL (ptSelVM b t0 s)
        (ptUnitVM O Z nC j) v3 hin3.sk hin3.rc
        (by rw [u2 _ (by decide) (by decide)]; exact a1) u1
      have hE : exec N K (ptJBody s) v1 = exec N K (.app ptCj ptZero) (exec N K ptSlabInrC v3) := rfl
      rw [hE]
      refine ⟨?_, ?_⟩
      · rw [exec_app, Function.update_of_ne (by decide), s1]
        have e0 : v3 rAinS = v rAinS := by
          rw [u2 _ (by decide) (by decide), a2 _ (by decide) (by decide), hv1,
            Function.update_of_ne (by decide)]
        rw [e0, h1, List.range_succ, List.flatMap_append]
        simp [List.append_assoc, ptInrPk]
      · rw [exec_app, Function.update_self, exec_writes _ _ ptCj (by decide),
          exec_writes _ _ ptZero (by decide), u2 _ (by decide) (by decide),
          u2 _ (by decide) (by decide), a2 _ (by decide) (by decide), a2 _ (by decide) (by decide),
          hv1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h2,
          hfr _ (ptJBody_writes s _ (Or.inl (by decide))) (by decide), hfr1 _ (by decide) (by decide),
          hin.rc.zero, List.replicate_succ', List.flatten_append, List.flatten_singleton])
  rw [hcnt] at key
  refine ⟨key.1, fun r hr => ?_⟩
  have hrB : r ≠ ptLB := by rintro rfl; revert hr; decide
  have hrJ : r ≠ ptCj := by rintro rfl; revert hr; decide
  have hw : (Code.rep ptLB (ptJBody s)).writes r = false := by
    simp only [Code.writes, ptJBody_writes s r (by tauto), Bool.or_false, beq_eq_false_iff_ne]
    exact fun h => hrB h.symm
  show exec N K (.rep ptLB (ptJBody s)) w1 r = w r
  rw [exec_writes _ _ r hw, hfr1 r hrB hrJ]

/-- **The `η` slabs.** -/
theorem exec_ptInrLoopC {N K : ℕ} (m nC nD b : ℕ) (O Z Z2 ZL : List Bool)
    {G Aa Hf SP PU : ℕ → List Bool} {A0 : List Bool} (w : St)
    (hin : PtInrIn m nC nD b O Z Z2 ZL G Aa Hf SP PU A0 w) :
    exec N K ptInrLoopC w rAinS = w rAinS ++ (List.range b).flatMap (fun t0 =>
        ptJPk b nC nD O Z Z2 ZL G Aa Hf SP PU A0 t0 false ++
          ptJPk b nC nD O Z Z2 ZL G Aa Hf SP PU A0 t0 true) ∧
      ∀ r, ptInrKeep r = true → exec N K ptInrLoopC w r = w r := by
  set w1 := exec N K (.cp ptLA ptTB) (exec N K (.clr ptT0) w) with hw1
  have hfr1 : ∀ r, r ≠ ptLA → r ≠ ptT0 → w1 r = w r := fun r h1 h2 => by
    simp [hw1, Function.update_apply, h1, h2]
  have hcnt : (w1 ptLA).length = b := by
    simp only [hw1, exec_cp, exec_clr, Function.update_self]
    rw [Function.update_of_ne (by decide), hin.sk.tb]
  have key := exec_rep_inv2 (N := N) (K := K) ptLA ptT0Body (ptT0Body_writes _ (by simp))
    (fun t v => v rAinS = w rAinS ++ (List.range t).flatMap (fun t0 =>
        ptJPk b nC nD O Z Z2 ZL G Aa Hf SP PU A0 t0 false ++
          ptJPk b nC nD O Z Z2 ZL G Aa Hf SP PU A0 t0 true) ∧
      v ptT0 = List.replicate (2 * t) false) w1
    ⟨by rw [hfr1 _ (by decide) (by decide)]; simp, by simp [hw1, Function.update_apply]⟩
    (by
      intro t v ht hP _ hfr
      obtain ⟨h1, h2⟩ := hP
      set v1 := Function.update v ptLA (v ptLA).tail with hv1
      have fr : ∀ r, ptInrKeep r = true → v1 r = w r := by
        intro r hr
        have hrA : r ≠ ptLA := by rintro rfl; revert hr; decide
        have hrT : r ≠ ptT0 := by rintro rfl; revert hr; decide
        rw [hv1, Function.update_of_ne hrA, hfr r (ptT0Body_writes r (Or.inl hr)) hrA,
          hfr1 r hrA hrT]
      have hin1 := hin.of_frame fr
      have hT1 : v1 ptT0 = List.replicate (2 * t) false := by
        rw [hv1, Function.update_of_ne (by decide)]; exact h2
      obtain ⟨j1, j2⟩ := exec_ptJLoopC (N := N) (K := K) m nC nD b O Z Z2 ZL false t v1 hin1 hT1
      set v2 := exec N K (ptJLoopC false) v1 with hv2
      have hin2 := hin1.of_frame fun r hr => j2 r (Or.inl hr)
      obtain ⟨k1, k2⟩ := exec_ptJLoopC (N := N) (K := K) m nC nD b O Z Z2 ZL true t v2 hin2
        (by rw [j2 _ (Or.inr (Or.inr rfl))]; exact hT1)
      set v3 := exec N K (ptJLoopC true) v2 with hv3
      have hE : exec N K ptT0Body v1 = exec N K (.app ptT0 ptB1) (exec N K (.app ptT0 ptB1) v3) := rfl
      rw [hE]
      refine ⟨?_, ?_⟩
      · simp only [exec_app, Function.update_of_ne (show (rAinS : Fin 64) ≠ ptT0 by decide)]
        rw [k1, j1, hv1, Function.update_of_ne (by decide), h1, List.range_succ,
          List.flatMap_append]
        simp [List.append_assoc]
      · simp only [exec_app, Function.update_self, Function.update_of_ne (show (ptB1 : Fin 64) ≠ ptT0 by decide)]
        rw [k2 _ (Or.inr (Or.inr rfl)), j2 _ (Or.inr (Or.inr rfl)), hT1, k2 _ (Or.inl rfl),
          j2 _ (Or.inl rfl), hin1.b1]
        rw [List.append_assoc, show 2 * (t + 1) = 2 * t + 2 by ring, List.replicate_add]
        rfl)
  rw [hcnt] at key
  refine ⟨key.1, fun r hr => ?_⟩
  have hrA : r ≠ ptLA := by rintro rfl; revert hr; decide
  have hrT : r ≠ ptT0 := by rintro rfl; revert hr; decide
  have hw : (Code.rep ptLA ptT0Body).writes r = false := by
    simp only [Code.writes, ptT0Body_writes r (Or.inl hr), Bool.or_false, beq_eq_false_iff_ne]
    exact fun h => hrA h.symm
  show exec N K (.rep ptLA ptT0Body) w1 r = w r
  rw [exec_writes _ _ r hw, hfr1 r hrA hrT]

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
