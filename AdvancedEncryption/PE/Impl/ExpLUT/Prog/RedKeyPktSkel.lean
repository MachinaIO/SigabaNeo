import PE.Impl.ExpLUT.Prog.RedKeyMidPk
/-!
# The packet stream (phase M3, `PktOk`), part 1: the skeleton of one packet

A packet of `simKeyC`'s stream (`sePacket`) interleaves **public** segments (the same for every
slab) with **slab** segments:

  `∏_{t<b} [G_t | ad_t | cr_t | Aa_t | hr_t | Hf_t] ++ l0 ++ A₀ ++ ∏_{i<16} [SP_i | z_i | rd_i | PU_i]`

(`ptPacket`; `G_t = matL gc_t`, `Aa_t = adL A^aut_t`, `Hf_t = matL H_{g_t}`, `SP_i = adL A^in_i ++
matL C^in_i ++ [X^{z_i}]`, `PU_i = [X^{z_i + w x_i}]` public; `ad`, `cr`, `hr`, `l0`, `z`, `rd` of the
slab). **`sePacket_eq_ptPacket`** is the bridge.

`ptSkelC ad cr hr l0 z rd` appends one packet to `rAinS`: the public segments are popped from copies
of the queues `ptPB = ∏_t (G_t ++ Aa_t ++ Hf_t)` and `ptPS = ∏_i (SP_i ++ PU_i)` (`ptPopAppC`, the
widths from templates), `A₀` from `ptA0`; the six slab segments are written by the parameter codes.
**`exec_ptSkelC`**: if the parameter codes advance five phase invariants (`Iad`, `Icr`, `Ihr`
indexed by the bit `t`, `Iz`, `Ird` by the step `i`; `PtSubOk`) and never touch the skeleton's
registers, the code appends `ptPacket` of the words (as bits) and ends in `Iz 16`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### The interleaved packet -/

/-- **The packet** from its segments (any element type). -/
def ptPacket {α : Type*} (b : ℕ) (G ad cr Aa hr Hf : ℕ → List α) (l0 A0 : List α)
    (SP z rd PU : ℕ → List α) : List α :=
  (List.range b).flatMap (fun t => G t ++ (ad t ++ (cr t ++ (Aa t ++ (hr t ++ Hf t))))) ++
    (l0 ++ (A0 ++ (List.range 16).flatMap fun i => SP i ++ (z i ++ (rd i ++ PU i))))

theorem sePacket_eq_ptPacket {N K : ℕ} (Dd : SeBits N K) (b : ℕ) (L0 : List (Fin 2 × Fin K → Rq N K))
    (A0 : Fin 2 → Fin 2 × Fin K → Rq N K) (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Cin : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu : ℕ → Rq N K)
    (z : ℕ → Fin 2 × Fin K → Rq N K) (rd : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) :
    sePacket Dd b L0 A0 Ain Cin pz pu z rd =
      ptPacket b (fun t => matL (Dd.gc t)) (fun t => adL (Dd.ad t)) (fun t => vecL (Dd.crow t))
        (fun t => adL (Dd.Aa t)) (fun t => vecL (Dd.hrow t)) (fun t => matL (Dd.Hf t)) (seRows L0)
        (matL A0) (fun i => adL (Ain i) ++ (matL (Cin i) ++ [pz i])) (fun i => vecL (z i))
        (fun i => adL (rd i)) (fun i => [pu i]) := by
  simp only [sePacket, ptPacket, seStream, seStepsL, seStepRec, List.append_assoc,
    List.cons_append, List.singleton_append, List.nil_append]
  rfl

theorem flatMap_map_flatMap {α β : Type*} (f : α → List β) (g : ℕ → List α) (l : List ℕ) :
    (l.flatMap g).flatMap f = l.flatMap fun i => (g i).flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.flatMap_append, ih]

/-- The packet of words is the word of the packet. -/
theorem flatMap_ptPacket {α β : Type*} (f : α → List β) (b : ℕ) (G ad cr Aa hr Hf : ℕ → List α)
    (l0 A0 : List α) (SP z rd PU : ℕ → List α) :
    (ptPacket b G ad cr Aa hr Hf l0 A0 SP z rd PU).flatMap f =
      ptPacket b (fun t => (G t).flatMap f) (fun t => (ad t).flatMap f) (fun t => (cr t).flatMap f)
        (fun t => (Aa t).flatMap f) (fun t => (hr t).flatMap f) (fun t => (Hf t).flatMap f)
        (l0.flatMap f) (A0.flatMap f) (fun i => (SP i).flatMap f) (fun i => (z i).flatMap f)
        (fun i => (rd i).flatMap f) (fun i => (PU i).flatMap f) := by
  simp only [ptPacket, List.flatMap_append, flatMap_map_flatMap]

/-! ### Registers of the skeleton -/

/-- The bit queue (a copy of `ptPB`). -/
@[simp, vmreg] abbrev ptQB : Fin 64 := 5
/-- The step queue (a copy of `ptPS`). -/
@[simp, vmreg] abbrev ptQS : Fin 64 := 6
/-- The popped segment. -/
@[simp, vmreg] abbrev ptTmp : Fin 64 := 7
/-- The bit counter. -/
@[simp, vmreg] abbrev ptCT : Fin 64 := 8
/-- The step counter. -/
@[simp, vmreg] abbrev ptCI : Fin 64 := 9
/-- `∏_t (G_t ++ Aa_t ++ Hf_t)`. -/
@[simp, vmreg] abbrev ptPB : Fin 64 := 10
/-- `∏_i (SP_i ++ PU_i)`. -/
@[simp, vmreg] abbrev ptPS : Fin 64 := 11
/-- `A₀`. -/
@[simp, vmreg] abbrev ptA0 : Fin 64 := 12
/-- Unary `b`. -/
@[simp, vmreg] abbrev ptTB : Fin 64 := 13
/-- Unary `16`. -/
@[simp, vmreg] abbrev ptT16 : Fin 64 := 14
/-- The width of a matrix (`G_t`, `Hf_t`). -/
@[simp, vmreg] abbrev ptTM : Fin 64 := 15
/-- The width of `Aa_t`. -/
@[simp, vmreg] abbrev ptTAa : Fin 64 := 16
/-- The width of `SP_i`. -/
@[simp, vmreg] abbrev ptTSP : Fin 64 := 17
/-- The width of `PU_i`. -/
@[simp, vmreg] abbrev ptTPU : Fin 64 := 29

/-- The registers the skeleton writes besides `rAinS`. -/
def ptSkW (r : Fin 64) : Bool := r == ptQB || r == ptQS || r == ptTmp || r == ptCT || r == ptCI

/-- The registers the skeleton reads and never writes. -/
def ptSkR (r : Fin 64) : Bool :=
  r == ptPB || r == ptPS || r == ptA0 || r == ptTB || r == ptT16 || r == ptTM || r == ptTAa ||
    r == ptTSP || r == ptTPU

/-! ### Popping a segment onto the output -/

/-- **`rAinS ++= ` the first `|T|` bits of `q`** (which loses them). -/
def ptPopAppC (q T : Fin 64) : Code := .seq (.cp ptTmp T) (.seq (.mv ptTmp q T) (.app rAinS ptTmp))

theorem exec_ptPopAppC {N K : ℕ} (q T : Fin 64) (hqt : q ≠ ptTmp) (hTt : T ≠ ptTmp) (hqT : q ≠ T)
    (hq0 : q ≠ rAinS) (w : St) (u v : List Bool) (hq : w q = u ++ v) (hu : u.length = (w T).length) :
    exec N K (ptPopAppC q T) w =
      Function.update (Function.update (Function.update w ptTmp u) q v) rAinS (w rAinS ++ u) := by
  have hne : ¬(ptTmp = q ∨ ptTmp = T ∨ q = T) := by
    rintro (h | h | h)
    · exact hqt h.symm
    · exact hTt h.symm
    · exact hqT h
  simp only [ptPopAppC, exec_seq, exec_cp, exec_mv, if_neg hne, exec_app]
  have hsh : ValVM.shiftIn (w T).length (w T) (u ++ v) = u := by
    unfold ValVM.shiftIn
    rw [takeD_eq_take (by simp; omega), ← hu, List.take_left' rfl, hu, List.drop_left' rfl]
  simp only [Function.update_self, Function.update_of_ne (Ne.symm hTt),
    Function.update_of_ne hqt, hq, hu, hsh]
  funext r
  simp only [Function.update_apply]
  by_cases h0 : r = rAinS
  · subst h0; simp [hq0.symm, show (rAinS : Fin 64) ≠ ptTmp by decide, hsh]
  · by_cases h1 : r = q
    · subst h1; simp [h0, hqt, hsh, ← hu]
    · by_cases h2 : r = ptTmp
      · subst h2; simp [h0, h1, hsh]
      · simp [h0, h1, h2]

theorem ptPopAppC_writes (q T r : Fin 64) (h1 : r ≠ ptTmp) (h2 : r ≠ q) (h3 : r ≠ rAinS) :
    (ptPopAppC q T).writes r = false := by
  simp [ptPopAppC, Code.writes, Ne.symm h1, Ne.symm h2, Ne.symm h3]

/-! ### The skeleton -/

/-- The body of the bit loop. -/
def ptTBody (ad cr hr : Code) : Code :=
  .seq (ptPopAppC ptQB ptTM) <| .seq ad <| .seq cr <| .seq (ptPopAppC ptQB ptTAa) <| .seq hr
    (ptPopAppC ptQB ptTM)

/-- The body of the step loop. -/
def ptIBody (z rd : Code) : Code :=
  .seq (ptPopAppC ptQS ptTSP) <| .seq z <| .seq rd (ptPopAppC ptQS ptTPU)

/-- **One packet**, appended to `rAinS`. -/
def ptSkelC (ad cr hr l0 z rd : Code) : Code :=
  .seq (.cp ptQB ptPB) <| .seq (.cp ptCT ptTB) <| .seq (.rep ptCT (ptTBody ad cr hr)) <|
  .seq l0 <| .seq (.app rAinS ptA0) <| .seq (.cp ptQS ptPS) <| .seq (.cp ptCI ptT16)
    (.rep ptCI (ptIBody z rd))

/-- A parameter code never touches the skeleton's registers (other than appending to `rAinS`). -/
def PtFree (c : Code) : Prop := ∀ r : Fin 64, ptSkW r = true ∨ ptSkR r = true → c.writes r = false

/-- An invariant is insensitive to the skeleton's writes. -/
def PtStable (I : St → Prop) : Prop :=
  ∀ (w : St) (r : Fin 64) (v : List Bool), (ptSkW r = true ∨ r = rAinS) → I w →
    I (Function.update w r v)

/-- A code appends `u` to `rAinS` from `P` and ends in `Q`. -/
def PtApp (N K : ℕ) (c : Code) (P Q : St → Prop) (u : List Bool) : Prop :=
  ∀ w, P w → exec N K c w rAinS = w rAinS ++ u ∧ Q (exec N K c w)

/-- **The contract of the six slab codes** (words `ad t`, …, `rd i`; phase invariants). -/
structure PtSubOk (N K b : ℕ) (adC crC hrC l0C zC rdC : Code)
    (Iad Icr Ihr Iz Ird : ℕ → St → Prop) (ad cr hr : ℕ → List Bool) (l0 : List Bool)
    (z rd : ℕ → List Bool) : Prop where
  fad : PtFree adC
  fcr : PtFree crC
  fhr : PtFree hrC
  fl0 : PtFree l0C
  fz : PtFree zC
  frd : PtFree rdC
  sad : ∀ t, PtStable (Iad t)
  scr : ∀ t, PtStable (Icr t)
  shr : ∀ t, PtStable (Ihr t)
  sz : ∀ i, PtStable (Iz i)
  srd : ∀ i, PtStable (Ird i)
  had : ∀ t < b, PtApp N K adC (Iad t) (Icr t) (ad t)
  hcr : ∀ t < b, PtApp N K crC (Icr t) (Ihr t) (cr t)
  hhr : ∀ t < b, PtApp N K hrC (Ihr t) (Iad (t + 1)) (hr t)
  hl0 : PtApp N K l0C (Iad b) (Iz 0) l0
  hz : ∀ i < 16, PtApp N K zC (Iz i) (Ird i) (z i)
  hrd : ∀ i < 16, PtApp N K rdC (Ird i) (Iz (i + 1)) (rd i)

/-- The skeleton's inputs: the public queues and the templates. -/
structure PtSkIn (b : ℕ) (G Aa Hf SP PU : ℕ → List Bool) (A0 : List Bool) (w : St) : Prop where
  pb : w ptPB = (List.range b).flatMap fun t => G t ++ (Aa t ++ Hf t)
  ps : w ptPS = (List.range 16).flatMap fun i => SP i ++ PU i
  a0 : w ptA0 = A0
  tb : (w ptTB).length = b
  t16 : (w ptT16).length = 16
  lG : ∀ t, (G t).length = (w ptTM).length
  lHf : ∀ t, (Hf t).length = (w ptTM).length
  lAa : ∀ t, (Aa t).length = (w ptTAa).length
  lSP : ∀ i, (SP i).length = (w ptTSP).length
  lPU : ∀ i, (PU i).length = (w ptTPU).length

theorem PtSkIn.of_frame {b : ℕ} {G Aa Hf SP PU : ℕ → List Bool} {A0 : List Bool} {w w' : St}
    (h : PtSkIn b G Aa Hf SP PU A0 w) (hw : ∀ r, ptSkR r = true → w' r = w r) :
    PtSkIn b G Aa Hf SP PU A0 w' :=
  ⟨by rw [hw _ rfl]; exact h.pb, by rw [hw _ rfl]; exact h.ps, by rw [hw _ rfl]; exact h.a0,
   by rw [hw _ rfl]; exact h.tb, by rw [hw _ rfl]; exact h.t16,
   fun t => by rw [hw _ rfl]; exact h.lG t, fun t => by rw [hw _ rfl]; exact h.lHf t,
   fun t => by rw [hw _ rfl]; exact h.lAa t, fun i => by rw [hw _ rfl]; exact h.lSP i,
   fun i => by rw [hw _ rfl]; exact h.lPU i⟩

theorem PtStable.update2 {I : St → Prop} (hI : PtStable I) {w : St} (h : I w) (r₁ r₂ : Fin 64)
    (v₁ v₂ : List Bool) (h₁ : ptSkW r₁ = true ∨ r₁ = rAinS) (h₂ : ptSkW r₂ = true ∨ r₂ = rAinS) :
    I (Function.update (Function.update w r₁ v₁) r₂ v₂) :=
  hI _ _ _ h₂ (hI _ _ _ h₁ h)

/-- A pop keeps a stable invariant. -/
theorem PtStable.pop {I : St → Prop} (hI : PtStable I) {w : St} (h : I w) (q : Fin 64)
    (hq : ptSkW q = true) (u v o : List Bool) :
    I (Function.update (Function.update (Function.update w ptTmp u) q v) rAinS o) :=
  hI _ _ _ (Or.inr rfl) (hI _ _ _ (Or.inl hq) (hI _ _ _ (Or.inl rfl) h))

theorem ptFree_frame {c : Code} (hc : PtFree c) (N K : ℕ) (w : St) (r : Fin 64)
    (hr : ptSkW r = true ∨ ptSkR r = true) : exec N K c w r = w r :=
  exec_writes c w r (hc r hr)

/-- One round of the bit loop. -/
theorem exec_ptTBody {N K b : ℕ} {adC crC hrC l0C zC rdC : Code} {Iad Icr Ihr Iz Ird : ℕ → St → Prop}
    {ad cr hr : ℕ → List Bool} {l0 : List Bool} {z rd : ℕ → List Bool}
    (hs : PtSubOk N K b adC crC hrC l0C zC rdC Iad Icr Ihr Iz Ird ad cr hr l0 z rd)
    {G Aa Hf SP PU : ℕ → List Bool} {A0 : List Bool} (t : ℕ) (ht : t < b) (w : St)
    (hin : PtSkIn b G Aa Hf SP PU A0 w) (hI : Iad t w) (rest : List Bool)
    (hq : w ptQB = G t ++ (Aa t ++ (Hf t ++ rest))) :
    let w' := exec N K (ptTBody adC crC hrC) w
    w' rAinS = w rAinS ++ (G t ++ (ad t ++ (cr t ++ (Aa t ++ (hr t ++ Hf t))))) ∧
      w' ptQB = rest ∧ Iad (t + 1) w' ∧ (∀ r, ptSkR r = true → w' r = w r) ∧
      w' ptCT = w ptCT ∧ w' ptCI = w ptCI ∧ w' ptQS = w ptQS := by
  intro w'
  -- step 1: pop G
  set w1 := exec N K (ptPopAppC ptQB ptTM) w with hw1
  have e1 := exec_ptPopAppC (N := N) (K := K) ptQB ptTM (by decide) (by decide) (by decide) (by decide) w
    (G t) _ hq (hin.lG t)
  have I1 : Iad t w1 := by rw [hw1, e1]; exact (hs.sad t).pop hI ptQB rfl _ _ _
  have sk1 : ∀ r, ptSkR r = true → w1 r = w r := by
    intro r hr; rw [hw1, e1]
    have : r ≠ rAinS ∧ r ≠ ptQB ∧ r ≠ ptTmp := by
      revert hr; revert r; decide
    simp [Function.update_apply, this.1, this.2.1, this.2.2]
  -- step 2: ad
  set w2 := exec N K adC w1 with hw2
  obtain ⟨o2, I2⟩ := hs.had t ht w1 I1
  have f2 : ∀ r, ptSkW r = true ∨ ptSkR r = true → w2 r = w1 r := ptFree_frame hs.fad N K w1
  -- step 3: cr
  set w3 := exec N K crC w2 with hw3
  obtain ⟨o3, I3⟩ := hs.hcr t ht w2 I2
  have f3 : ∀ r, ptSkW r = true ∨ ptSkR r = true → w3 r = w2 r := ptFree_frame hs.fcr N K w2
  -- step 4: pop Aa
  have hq3 : w3 ptQB = Aa t ++ (Hf t ++ rest) := by
    rw [f3 _ (Or.inl rfl), f2 _ (Or.inl rfl), hw1, e1]; simp
  have hT3 : ∀ r, ptSkR r = true → w3 r = w r := fun r hr => by
    rw [f3 _ (Or.inr hr), f2 _ (Or.inr hr), sk1 r hr]
  set w4 := exec N K (ptPopAppC ptQB ptTAa) w3 with hw4
  have e4 := exec_ptPopAppC (N := N) (K := K) ptQB ptTAa (by decide) (by decide) (by decide) (by decide) w3
    (Aa t) _ hq3 (by rw [hT3 _ rfl]; exact hin.lAa t)
  have I4 : Ihr t w4 := by rw [hw4, e4]; exact (hs.shr t).pop I3 ptQB rfl _ _ _
  -- step 5: hr
  set w5 := exec N K hrC w4 with hw5
  obtain ⟨o5, I5⟩ := hs.hhr t ht w4 I4
  have f5 : ∀ r, ptSkW r = true ∨ ptSkR r = true → w5 r = w4 r := ptFree_frame hs.fhr N K w4
  -- step 6: pop Hf
  have hq5 : w5 ptQB = Hf t ++ rest := by rw [f5 _ (Or.inl rfl), hw4, e4]; simp
  have hT4 : ∀ r, ptSkR r = true → w4 r = w r := fun r hr => by
    rw [hw4, e4, ← hT3 r hr]
    have : r ≠ rAinS ∧ r ≠ ptQB ∧ r ≠ ptTmp := by
      revert hr; revert r; decide
    simp [Function.update_apply, this.1, this.2.1, this.2.2]
  have hT5 : ∀ r, ptSkR r = true → w5 r = w r := fun r hr => by rw [f5 _ (Or.inr hr), hT4 r hr]
  have e6 := exec_ptPopAppC (N := N) (K := K) ptQB ptTM (by decide) (by decide) (by decide) (by decide) w5
    (Hf t) _ hq5 (by rw [hT5 _ rfl]; exact hin.lHf t)
  have hw' : w' = exec N K (ptPopAppC ptQB ptTM) w5 := rfl
  have sk' : ∀ r, ptSkW r = false → r ≠ rAinS → w' r = w5 r := by
    intro r h1 h2
    rw [hw', e6]
    have : r ≠ ptQB ∧ r ≠ ptTmp := by
      constructor <;> (intro h; subst h; simp [ptSkW] at h1)
    simp [Function.update_apply, h2, this.1, this.2]
  have oth : ∀ r, ptSkW r = true → r ≠ ptQB → r ≠ ptTmp → w' r = w r := by
    intro r hr h1 h2
    have hr0 : r ≠ rAinS := by intro h; subst h; simp [ptSkW] at hr
    rw [hw', e6]
    simp only [Function.update_apply, if_neg hr0, if_neg h1, if_neg h2]
    rw [f5 _ (Or.inl hr), hw4, e4]
    simp only [Function.update_apply, if_neg hr0, if_neg h1, if_neg h2]
    rw [f3 _ (Or.inl hr), f2 _ (Or.inl hr), hw1, e1]
    simp only [Function.update_apply, if_neg hr0, if_neg h1, if_neg h2]
  refine ⟨?_, ?_, ?_, ?_, oth _ rfl (by decide) (by decide), oth _ rfl (by decide) (by decide),
    oth _ rfl (by decide) (by decide)⟩
  · rw [hw', e6]
    simp only [Function.update_self]
    rw [hw5, o5, hw4, e4]
    simp only [Function.update_self]
    rw [hw3, o3, hw2, o2, hw1, e1]
    simp [List.append_assoc]
  · rw [hw', e6]; simp
  · rw [hw', e6]; exact (hs.sad (t + 1)).pop I5 ptQB rfl _ _ _
  · intro r hr
    rw [hw', e6, ← hT5 r hr]
    have : r ≠ rAinS ∧ r ≠ ptQB ∧ r ≠ ptTmp := by
      revert hr; revert r; decide
    simp [Function.update_apply, this.1, this.2.1, this.2.2]

/-- One round of the step loop. -/
theorem exec_ptIBody {N K b : ℕ} {adC crC hrC l0C zC rdC : Code} {Iad Icr Ihr Iz Ird : ℕ → St → Prop}
    {ad cr hr : ℕ → List Bool} {l0 : List Bool} {z rd : ℕ → List Bool}
    (hs : PtSubOk N K b adC crC hrC l0C zC rdC Iad Icr Ihr Iz Ird ad cr hr l0 z rd)
    {G Aa Hf SP PU : ℕ → List Bool} {A0 : List Bool} (i : ℕ) (hi : i < 16) (w : St)
    (hin : PtSkIn b G Aa Hf SP PU A0 w) (hI : Iz i w) (rest : List Bool)
    (hq : w ptQS = SP i ++ (PU i ++ rest)) :
    let w' := exec N K (ptIBody zC rdC) w
    w' rAinS = w rAinS ++ (SP i ++ (z i ++ (rd i ++ PU i))) ∧
      w' ptQS = rest ∧ Iz (i + 1) w' ∧ (∀ r, ptSkR r = true → w' r = w r) ∧
      w' ptCI = w ptCI := by
  intro w'
  set w1 := exec N K (ptPopAppC ptQS ptTSP) w with hw1
  have e1 := exec_ptPopAppC (N := N) (K := K) ptQS ptTSP (by decide) (by decide) (by decide) (by decide) w
    (SP i) _ hq (hin.lSP i)
  have I1 : Iz i w1 := by rw [hw1, e1]; exact (hs.sz i).pop hI ptQS rfl _ _ _
  set w2 := exec N K zC w1 with hw2
  obtain ⟨o2, I2⟩ := hs.hz i hi w1 I1
  have f2 : ∀ r, ptSkW r = true ∨ ptSkR r = true → w2 r = w1 r := ptFree_frame hs.fz N K w1
  set w3 := exec N K rdC w2 with hw3
  obtain ⟨o3, I3⟩ := hs.hrd i hi w2 I2
  have f3 : ∀ r, ptSkW r = true ∨ ptSkR r = true → w3 r = w2 r := ptFree_frame hs.frd N K w2
  have hq3 : w3 ptQS = PU i ++ rest := by
    rw [f3 _ (Or.inl rfl), f2 _ (Or.inl rfl), hw1, e1]; simp
  have hT3 : ∀ r, ptSkR r = true → w3 r = w r := fun r hr => by
    rw [f3 _ (Or.inr hr), f2 _ (Or.inr hr), hw1, e1]
    have : r ≠ rAinS ∧ r ≠ ptQS ∧ r ≠ ptTmp := by
      revert hr; revert r; decide
    simp [Function.update_apply, this.1, this.2.1, this.2.2]
  have e4 := exec_ptPopAppC (N := N) (K := K) ptQS ptTPU (by decide) (by decide) (by decide) (by decide) w3
    (PU i) _ hq3 (by rw [hT3 _ rfl]; exact hin.lPU i)
  have hw' : w' = exec N K (ptPopAppC ptQS ptTPU) w3 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hw', e4]
    simp only [Function.update_self]
    rw [hw3, o3, hw2, o2, hw1, e1]
    simp [List.append_assoc]
  · rw [hw', e4]; simp
  · rw [hw', e4]; exact (hs.sz (i + 1)).pop I3 ptQS rfl _ _ _
  · intro r hr
    rw [hw', e4, ← hT3 r hr]
    have : r ≠ rAinS ∧ r ≠ ptQS ∧ r ≠ ptTmp := by
      revert hr; revert r; decide
    simp [Function.update_apply, this.1, this.2.1, this.2.2]
  · rw [hw', e4]
    simp only [Function.update_apply, show (ptCI : Fin 64) ≠ rAinS by decide,
      show (ptCI : Fin 64) ≠ ptQS by decide, show (ptCI : Fin 64) ≠ ptTmp by decide, if_false]
    rw [f3 _ (Or.inl rfl), f2 _ (Or.inl rfl), hw1, e1]
    simp [Function.update_apply]

theorem ptTBody_writes_CT {adC crC hrC : Code} (h1 : PtFree adC) (h2 : PtFree crC)
    (h3 : PtFree hrC) : (ptTBody adC crC hrC).writes ptCT = false := by
  simp [ptTBody, Code.writes, h1 ptCT (Or.inl rfl), h2 ptCT (Or.inl rfl), h3 ptCT (Or.inl rfl),
    ptPopAppC_writes]

theorem ptIBody_writes_CI {zC rdC : Code} (h1 : PtFree zC) (h2 : PtFree rdC) :
    (ptIBody zC rdC).writes ptCI = false := by
  simp [ptIBody, Code.writes, h1 ptCI (Or.inl rfl), h2 ptCI (Or.inl rfl), ptPopAppC_writes]

theorem drop_flatMap_range {α : Type*} (f : ℕ → List α) :
    ∀ (n m : ℕ), m ≤ n → ((List.range n).flatMap f).drop ((List.range m).flatMap f).length =
      (List.range' m (n - m)).flatMap f
  | n, 0, _ => by simp [List.range_eq_range']
  | n, m + 1, h => by
    have ih := drop_flatMap_range f n m (by omega)
    rw [List.range_succ, List.flatMap_append, List.length_append, ← List.drop_drop, ih]
    obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
    rw [hk, List.range'_succ, List.flatMap_cons]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.drop_left']
    congr 2; omega

theorem range'_flatMap_cons {α : Type*} (f : ℕ → List α) (m k : ℕ) :
    (List.range' m (k + 1)).flatMap f = f m ++ (List.range' (m + 1) k).flatMap f := by
  rw [List.range'_succ, List.flatMap_cons]

/-- **One packet.** -/
theorem exec_ptSkelC {N K b : ℕ} {adC crC hrC l0C zC rdC : Code}
    {Iad Icr Ihr Iz Ird : ℕ → St → Prop} {ad cr hr : ℕ → List Bool} {l0 : List Bool}
    {z rd : ℕ → List Bool}
    (hs : PtSubOk N K b adC crC hrC l0C zC rdC Iad Icr Ihr Iz Ird ad cr hr l0 z rd)
    {G Aa Hf SP PU : ℕ → List Bool} {A0 : List Bool} (w : St)
    (hin : PtSkIn b G Aa Hf SP PU A0 w) (hI : Iad 0 w) :
    let w' := exec N K (ptSkelC adC crC hrC l0C zC rdC) w
    w' rAinS = w rAinS ++ ptPacket b G ad cr Aa hr Hf l0 A0 SP z rd PU ∧ Iz 16 w' ∧
      ∀ r, ptSkR r = true → w' r = w r := by
  intro w'
  -- the bit loop
  set v0 := exec N K (.cp ptCT ptTB) (exec N K (.cp ptQB ptPB) w) with hv0
  have hv0s : ∀ r, ptSkR r = true → v0 r = w r := by
    intro r hr
    have : r ≠ ptCT ∧ r ≠ ptQB := by revert hr; revert r; decide
    simp [hv0, Function.update_apply, this.1, this.2]
  have hv0I : Iad 0 v0 := by
    rw [hv0]; simp only [exec_cp]
    exact (hs.sad 0).update2 hI _ _ _ _ (Or.inl rfl) (Or.inl rfl)
  have hv0c : (v0 ptCT).length = b := by simp [hv0, hin.tb]
  let PT : ℕ → St → Prop := fun t v => t ≤ b ∧
    v rAinS = w rAinS ++ (List.range t).flatMap
      (fun t => G t ++ (ad t ++ (cr t ++ (Aa t ++ (hr t ++ Hf t))))) ∧
    v ptQB = (List.range' t (b - t)).flatMap (fun t => G t ++ (Aa t ++ Hf t)) ∧
    Iad t v ∧ ∀ r, ptSkR r = true → v r = w r
  have hloop := exec_rep_inv (N := N) (K := K) ptCT (ptTBody adC crC hrC)
    (ptTBody_writes_CT hs.fad hs.fcr hs.fhr) PT v0
    ⟨Nat.zero_le _, by simp [hv0], by simp [hv0, hin.pb, List.range_eq_range'], hv0I, hv0s⟩
    (by
      intro t v ht hP _
      obtain ⟨-, h1, h2, h3, h4⟩ := hP
      rw [hv0c] at ht
      have hin' := hin.of_frame h4
      set vv := Function.update v ptCT (v ptCT).tail
      have hvvI : Iad t vv := (hs.sad t) _ _ _ (Or.inl rfl) h3
      obtain ⟨k, hk⟩ : ∃ k, b - t = k + 1 := ⟨b - t - 1, by omega⟩
      have hq : vv ptQB = G t ++ (Aa t ++ (Hf t ++
          (List.range' (t + 1) (b - (t + 1))).flatMap (fun t => G t ++ (Aa t ++ Hf t)))) := by
        have e : b - (t + 1) = k := by omega
        simp only [vv, Function.update_apply, show (ptQB : Fin 64) ≠ ptCT by decide, if_false, h2,
          hk, range'_flatMap_cons, List.append_assoc, e]
      have hvvs : ∀ r, ptSkR r = true → vv r = w r := by
        intro r hr
        have : r ≠ ptCT := by revert hr; revert r; decide
        simp only [vv, Function.update_apply, if_neg this]; exact h4 r hr
      obtain ⟨o1, o2, o3, o4, -, -, -⟩ := exec_ptTBody hs t ht vv (hin.of_frame hvvs) hvvI _ hq
      refine ⟨by omega, ?_, o2, o3, fun r hr => by rw [o4 r hr, hvvs r hr]⟩
      rw [o1]
      simp only [vv, Function.update_apply, show (rAinS : Fin 64) ≠ ptCT by decide, if_false, h1,
        List.range_succ, List.flatMap_append, List.append_assoc]
      simp)
  rw [hv0c] at hloop
  obtain ⟨-, l1, -, l3, l4⟩ := hloop
  set v1 := exec N K (.rep ptCT (ptTBody adC crC hrC)) v0 with hv1
  -- l0, A₀
  set v2 := exec N K l0C v1 with hv2
  obtain ⟨o2, I2⟩ := hs.hl0 v1 l3
  have f2 : ∀ r, ptSkW r = true ∨ ptSkR r = true → v2 r = v1 r := ptFree_frame hs.fl0 N K v1
  set v3 := exec N K (.cp ptCI ptT16) (exec N K (.cp ptQS ptPS) (exec N K (.app rAinS ptA0) v2))
    with hv3
  have hv3s : ∀ r, ptSkR r = true → v3 r = w r := by
    intro r hr
    have : r ≠ ptCI ∧ r ≠ ptQS ∧ r ≠ rAinS := by revert hr; revert r; decide
    simp only [hv3, exec_cp, exec_app, Function.update_apply, if_neg this.1, if_neg this.2.1,
      if_neg this.2.2]
    rw [f2 _ (Or.inr hr), l4 r hr]
  have hv3I : Iz 0 v3 := by
    simp only [hv3, exec_cp, exec_app]
    exact (hs.sz 0) _ _ _ (Or.inl rfl) ((hs.sz 0) _ _ _ (Or.inl rfl)
      ((hs.sz 0) _ _ _ (Or.inr rfl) I2))
  have hv3c : (v3 ptCI).length = 16 := by
    have e : v3 ptCI = v2 ptT16 := by simp [hv3, Function.update_apply]
    rw [e, f2 _ (Or.inr rfl), l4 _ rfl, hin.t16]
  have hv3o : v3 rAinS = w rAinS ++ ((List.range b).flatMap
      (fun t => G t ++ (ad t ++ (cr t ++ (Aa t ++ (hr t ++ Hf t))))) ++ (l0 ++ A0)) := by
    simp only [hv3, exec_cp, exec_app, Function.update_apply, show (rAinS : Fin 64) ≠ ptCI by decide,
      show (rAinS : Fin 64) ≠ ptQS by decide, if_false, if_true]
    rw [hv2, o2, ← hv2, l1, f2 _ (Or.inr rfl), l4 _ rfl, hin.a0]
    simp [List.append_assoc]
  have hv3q : v3 ptQS = (List.range 16).flatMap fun i => SP i ++ PU i := by
    have e : v3 ptQS = v2 ptPS := by simp [hv3, Function.update_apply]
    rw [e, f2 _ (Or.inr rfl), l4 _ rfl, hin.ps]
  -- the step loop
  let PI : ℕ → St → Prop := fun i v => i ≤ 16 ∧
    v rAinS = v3 rAinS ++ (List.range i).flatMap (fun i => SP i ++ (z i ++ (rd i ++ PU i))) ∧
    v ptQS = (List.range' i (16 - i)).flatMap (fun i => SP i ++ PU i) ∧
    Iz i v ∧ ∀ r, ptSkR r = true → v r = w r
  have hloop2 := exec_rep_inv (N := N) (K := K) ptCI (ptIBody zC rdC)
    (ptIBody_writes_CI hs.fz hs.frd) PI v3
    ⟨Nat.zero_le _, by simp, by simp [hv3q, List.range_eq_range'], hv3I, hv3s⟩
    (by
      intro i v hi hP _
      obtain ⟨-, h1, h2, h3, h4⟩ := hP
      rw [hv3c] at hi
      set vv := Function.update v ptCI (v ptCI).tail
      have hvvI : Iz i vv := (hs.sz i) _ _ _ (Or.inl rfl) h3
      obtain ⟨k, hk⟩ : ∃ k, 16 - i = k + 1 := ⟨16 - i - 1, by omega⟩
      have hq : vv ptQS = SP i ++ (PU i ++
          (List.range' (i + 1) (16 - (i + 1))).flatMap (fun i => SP i ++ PU i)) := by
        have e : 16 - (i + 1) = k := by omega
        simp only [vv, Function.update_apply, show (ptQS : Fin 64) ≠ ptCI by decide, if_false, h2,
          hk, range'_flatMap_cons, List.append_assoc, e]
      have hvvs : ∀ r, ptSkR r = true → vv r = w r := by
        intro r hr
        have : r ≠ ptCI := by revert hr; revert r; decide
        simp only [vv, Function.update_apply, if_neg this]; exact h4 r hr
      obtain ⟨o1, o2, o3, o4, -⟩ := exec_ptIBody hs i hi vv (hin.of_frame hvvs) hvvI _ hq
      refine ⟨by omega, ?_, o2, o3, fun r hr => by rw [o4 r hr, hvvs r hr]⟩
      rw [o1]
      simp only [vv, Function.update_apply, show (rAinS : Fin 64) ≠ ptCI by decide, if_false, h1,
        List.range_succ, List.flatMap_append, List.append_assoc]
      simp)
  rw [hv3c] at hloop2
  obtain ⟨-, m1, -, m3, m4⟩ := hloop2
  have hw' : w' = exec N K (.rep ptCI (ptIBody zC rdC)) v3 := rfl
  refine ⟨?_, by rw [hw']; exact m3, fun r hr => by rw [hw']; exact m4 r hr⟩
  rw [hw', m1, hv3o]
  simp [ptPacket, List.append_assoc]

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
