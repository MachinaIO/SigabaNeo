import SigabaNeoStd.Lattices.Algo.FhatLoop
import SigabaNeoStd.Lattices.Homomorphic.SLPShadow

/-!
# The values of the output wires of `f̂`, block by block

`f̂ = fhatSLPL ordT ordO gv q p w` is built from the predicate's program `p` by one NAND block per
gate, each block one coefficient circuit per output coefficient (`leaves`, `rounds`, `foldSum` of
`modAdd`/`modSub` gadgets). By the relocation lemmas of `SigabaNeoStd.Lattices.Homomorphic.SLPShadow`,
under **any** semantics `valueOf inp one step`, the values of the wires of a block are a fixed
function of the values of the two bundles of wires it reads:

* `termV`, `leavesV`, `pairRoundV`, `roundsV`, `foldSumV`, `coefV`: the shadows of the coefficient
  circuit (lists of values of `k`-bit numbers);
* `nandV ordT ordO gv zv q A B : BI N k → α`: the bundle of values of a NAND block from the bundles
  `A`, `B` of its two operands;
* `fhatV`: the bundle of the output wires of `f̂`, by one `nandV` per gate of `p`, with the input
  bundles `fun i b => inp (i, b)`, the constant bundle (`constRepVV`) and `zv = step one one` (the
  value of the gate `0` of `f̂`).

**`valueOf_fhatSLPL`**: `valueOf inp one step f̂.1 (f̂.2 b) = fhatV … b`. So the values of the output
wires of `f̂` (the simulation `slpSim` of its output wires, the key matrix, …) are computed by
evaluating the shadows, block by block, without the program `f̂`.
-/

namespace SigabaNeo.Lattices.Algo

open SLP

variable {N k : ℕ} {ι α : Type*} (inp : ι → α) (one : α) (step : α → α → α)

/-! ### Lists of numbers -/

/-- The numbers `L` (lists of wires) are valid in `P` and have the values `Ls`. -/
def LSh (P : SLP ι) (L : List (List (Wire ι))) (Ls : List (List α)) : Prop :=
  (∀ ws ∈ L, AllValid P ws) ∧ L.map (fun ws => ws.map (valueOf inp one step P)) = Ls

theorem LSh.ext {P P' : SLP ι} (h : Ext P P') {L : List (List (Wire ι))} {Ls : List (List α)}
    (hL : LSh inp one step P L Ls) : LSh inp one step P' L Ls := by
  refine ⟨fun ws hws => (hL.1 ws hws).ext h, ?_⟩
  rw [← hL.2]
  exact List.map_congr_left fun ws hws => map_valueOf_ext inp one step h (hL.1 ws hws)

theorem lsh_nil (P : SLP ι) : LSh inp one step P ([] : List (List (Wire ι))) [] :=
  ⟨fun _ h => by simp at h, rfl⟩

theorem LSh.cons {P : SLP ι} {ws : List (Wire ι)} {L : List (List (Wire ι))} {Ls : List (List α)}
    (hw : AllValid P ws) (hL : LSh inp one step P L Ls) :
    LSh inp one step P (ws :: L) (ws.map (valueOf inp one step P) :: Ls) := by
  refine ⟨fun v hv => ?_, by rw [List.map_cons, hL.2]⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hw
  · exact hL.1 v hv

/-! ### The terms of a coefficient -/

/-- The values of a coefficient of a bundle. -/
def coefWV (A : BI N k → α) (a : Fin 2) (c : Fin 2 × Fin k) (j : Fin N) : List α :=
  List.ofFn fun i : Fin k => A (a, c, i, j)

theorem map_coefW (P : SLP ι) (rep : BI N k → Wire ι) (a : Fin 2) (c : Fin 2 × Fin k) (j : Fin N) :
    (coefW rep a c j).map (valueOf inp one step P) =
      coefWV (fun b => valueOf inp one step P (rep b)) a c j := by
  simp only [coefW, bitsL, coefWV, List.map_ofFn]
  rfl

theorem allValid_coefW {P : SLP ι} {rep : BI N k → Wire ι} (h : ∀ b, Valid P (rep b)) (a : Fin 2)
    (c : Fin 2 × Fin k) (j : Fin N) : AllValid P (coefW rep a c j) := by
  intro w hw
  simp only [coefW, bitsL, List.mem_ofFn] at hw
  obtain ⟨i, rfl⟩ := hw
  exact h _

/-- The shadow of `termStep`: one term added to the running sum `acc`. -/
def termV (zv : α) (q k : ℕ) (A B : BI N k → α) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N)
    (acc : List α) (e : (Fin 2 × Fin k) × Fin N) : List α :=
  if h : e.2.val ≤ t.val then
    modSubV one step zv q k acc
      (andLV one step (B (e.1.1, col, e.1.2, e.2)) (coefWV A a e.1 ⟨t.val - e.2.val, by omega⟩))
  else
    modAddV one step zv q k acc
      (andLV one step (B (e.1.1, col, e.1.2, e.2)) (coefWV A a e.1 ⟨N + t.val - e.2.val, by omega⟩))

/-- The operands of a block are valid in `P` with the values `A`, `B`, and `z` has the value `zv`. -/
structure Opnd (P : SLP ι) (z : Wire ι) (zv : α) (repA repB : BI N k → Wire ι)
    (A B : BI N k → α) : Prop where
  hz : Valid P z
  vz : valueOf inp one step P z = zv
  ha : ∀ b, Valid P (repA b)
  va : ∀ b, valueOf inp one step P (repA b) = A b
  hb : ∀ b, Valid P (repB b)
  vb : ∀ b, valueOf inp one step P (repB b) = B b

theorem Opnd.ext {P P' : SLP ι} (h : Ext P P') {z : Wire ι} {zv : α} {repA repB : BI N k → Wire ι}
    {A B : BI N k → α} (o : Opnd inp one step P z zv repA repB A B) :
    Opnd inp one step P' z zv repA repB A B :=
  ⟨o.hz.ext h, by rw [valueOf_ext inp one step h o.hz, o.vz], fun b => (o.ha b).ext h,
    fun b => by rw [valueOf_ext inp one step h (o.ha b), o.va], fun b => (o.hb b).ext h,
    fun b => by rw [valueOf_ext inp one step h (o.hb b), o.vb]⟩

theorem sh_termStep {z : Wire ι} {zv : α} (q k : ℕ) {repA repB : BI N k → Wire ι}
    {A B : BI N k → α} (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N)
    (st : SLP ι × List (Wire ι)) (o : Opnd inp one step st.1 z zv repA repB A B)
    (hst : AllValid st.1 st.2) (e : (Fin 2 × Fin k) × Fin N) :
    ShN inp one step st.1 (termStep z q k repA repB a col t st e)
      (termV one step zv q k A B a col t (st.2.map (valueOf inp one step st.1)) e) := by
  unfold termStep termV
  split_ifs with h
  · set r := andL (repB (e.1.1, col, e.1.2, e.2)) st.1 (coefW repA a e.1 ⟨t.val - e.2.val, by omega⟩)
    have h1 := sh_andL inp one step (repB (e.1.1, col, e.1.2, e.2)) st.1 (coefW repA a e.1 ⟨t.val - e.2.val, by omega⟩)
      (o.hb _) (allValid_coefW o.ha _ _ _)
    have h2 := sh_modSub inp one step z q k r.1 st.2 r.2 (o.hz.ext h1.ext) (hst.ext h1.ext) h1.valid
    refine ⟨h1.ext.trans h2.ext, h2.valid, ?_⟩
    rw [h2.value, h1.value, valueOf_ext inp one step h1.ext o.hz, o.vz,
      map_valueOf_ext inp one step h1.ext hst, o.vb, map_coefW]
    congr 3
    funext b; exact o.va b
  · set r := andL (repB (e.1.1, col, e.1.2, e.2)) st.1
      (coefW repA a e.1 ⟨N + t.val - e.2.val, by omega⟩)
    have h1 := sh_andL inp one step (repB (e.1.1, col, e.1.2, e.2)) st.1 (coefW repA a e.1 ⟨N + t.val - e.2.val, by omega⟩)
      (o.hb _) (allValid_coefW o.ha _ _ _)
    have h2 := sh_modAdd inp one step z q k r.1 st.2 r.2 (o.hz.ext h1.ext) (hst.ext h1.ext) h1.valid
    refine ⟨h1.ext.trans h2.ext, h2.valid, ?_⟩
    rw [h2.value, h1.value, valueOf_ext inp one step h1.ext o.hz, o.vz,
      map_valueOf_ext inp one step h1.ext hst, o.vb, map_coefW]
    congr 3
    funext b; exact o.va b

/-- The shadow of `leaves`: each term from `0`. -/
def leavesV (zv : α) (q k : ℕ) (A B : BI N k → α) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N) :
    List ((Fin 2 × Fin k) × Fin N) → List (List α)
  | [] => []
  | e :: es => termV one step zv q k A B a col t (constV one zv k 0) e ::
      leavesV zv q k A B a col t es

theorem sh_leaves {z : Wire ι} {zv : α} (q k : ℕ) {repA repB : BI N k → Wire ι}
    {A B : BI N k → α} (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N) :
    ∀ (es : List ((Fin 2 × Fin k) × Fin N)) (P : SLP ι), Opnd inp one step P z zv repA repB A B →
      Ext P (leaves z q k repA repB a col t P es).1 ∧
        LSh inp one step (leaves z q k repA repB a col t P es).1
          (leaves z q k repA repB a col t P es).2 (leavesV one step zv q k A B a col t es)
  | [], P, _ => ⟨Ext.refl P, lsh_nil inp one step P⟩
  | e :: es, P, o => by
    have h1 := sh_termStep inp one step q k a col t (P, constL z k 0) o (allValid_constL o.hz k 0) e
    have ih := sh_leaves q k a col t es _ (o.ext inp one step h1.ext)
    refine ⟨h1.ext.trans ih.1, ?_⟩
    have hl := LSh.cons inp one step (h1.valid.ext ih.1) ih.2
    rw [map_valueOf_ext inp one step ih.1 h1.valid, h1.value] at hl
    simp only [map_constL, o.vz] at hl
    exact hl

/-! ### The tree of additions -/

/-- The shadow of `pairRound`. -/
def pairRoundV (zv : α) (q k : ℕ) : List (List α) → List (List α)
  | a :: b :: rest => modAddV one step zv q k a b :: pairRoundV zv q k rest
  | l => l

theorem sh_pairRound {z : Wire ι} {zv : α} (q k : ℕ) :
    ∀ (P : SLP ι) (L : List (List (Wire ι))) (Ls : List (List α)), Valid P z →
      valueOf inp one step P z = zv → LSh inp one step P L Ls →
      Ext P (pairRound z q k P L).1 ∧
        LSh inp one step (pairRound z q k P L).1 (pairRound z q k P L).2
          (pairRoundV one step zv q k Ls)
  | P, [], Ls, _, _, hL => by
    obtain ⟨-, rfl⟩ := hL; exact ⟨Ext.refl P, lsh_nil inp one step P⟩
  | P, [a], Ls, _, _, hL => by
    obtain ⟨h1, rfl⟩ := hL; exact ⟨Ext.refl P, h1, rfl⟩
  | P, a :: b :: rest, Ls, hz, vz, hL => by
    obtain ⟨hv, rfl⟩ := hL
    have ha : AllValid P a := hv a (by simp)
    have hb : AllValid P b := hv b (by simp)
    have h1 := sh_modAdd inp one step z q k P a b hz ha hb
    have ih := sh_pairRound q k (modAdd z q k P a b).1 rest
      (rest.map fun ws => ws.map (valueOf inp one step P)) (hz.ext h1.ext)
      (by rw [valueOf_ext inp one step h1.ext hz, vz])
      (LSh.ext inp one step h1.ext (Ls := rest.map fun ws => ws.map (valueOf inp one step P))
        ⟨fun ws hws => hv ws (by simp [hws]), rfl⟩)
    refine ⟨h1.ext.trans ih.1, ?_⟩
    have hl := LSh.cons inp one step (h1.valid.ext ih.1) ih.2
    rw [map_valueOf_ext inp one step ih.1 h1.valid, h1.value, vz] at hl
    exact hl

/-- The shadow of `rounds`. -/
def roundsV (zv : α) (q k : ℕ) : ℕ → List (List α) → List (List α)
  | 0, L => L
  | h + 1, L => roundsV zv q k h (pairRoundV one step zv q k L)

theorem sh_rounds {z : Wire ι} {zv : α} (q k : ℕ) :
    ∀ (h : ℕ) (P : SLP ι) (L : List (List (Wire ι))) (Ls : List (List α)), Valid P z →
      valueOf inp one step P z = zv → LSh inp one step P L Ls →
      Ext P (rounds z q k h P L).1 ∧
        LSh inp one step (rounds z q k h P L).1 (rounds z q k h P L).2
          (roundsV one step zv q k h Ls)
  | 0, P, _, _, _, _, hL => ⟨Ext.refl P, hL⟩
  | h + 1, P, L, Ls, hz, vz, hL => by
    obtain ⟨e1, g1⟩ := sh_pairRound inp one step q k P L Ls hz vz hL
    obtain ⟨e2, g2⟩ := sh_rounds q k h _ _ _ (hz.ext e1)
      (by rw [valueOf_ext inp one step e1 hz, vz]) g1
    exact ⟨e1.trans e2, g2⟩

/-- The shadow of `foldSum`. -/
def foldSumV (zv : α) (q k : ℕ) : List (List α) → List α
  | [] => constV one zv k 0
  | a :: rest => rest.foldl (fun acc b => modAddV one step zv q k acc b) a

theorem sh_foldl_modAdd {z : Wire ι} {zv : α} (q k : ℕ) :
    ∀ (L : List (List (Wire ι))) (st : SLP ι × List (Wire ι)), Valid st.1 z →
      valueOf inp one step st.1 z = zv → AllValid st.1 st.2 → (∀ ws ∈ L, AllValid st.1 ws) →
      ShN inp one step st.1 (L.foldl (fun st b => modAdd z q k st.1 st.2 b) st)
        ((L.map fun ws => ws.map (valueOf inp one step st.1)).foldl
          (fun acc b => modAddV one step zv q k acc b) (st.2.map (valueOf inp one step st.1)))
  | [], st, _, _, hs, _ => ⟨Ext.refl _, hs, rfl⟩
  | b :: rest, st, hz, vz, hs, hL => by
    have hb : AllValid st.1 b := hL b (by simp)
    have h1 := sh_modAdd inp one step z q k st.1 st.2 b hz hs hb
    have ih := sh_foldl_modAdd q k rest (modAdd z q k st.1 st.2 b) (hz.ext h1.ext)
      (by rw [valueOf_ext inp one step h1.ext hz, vz]) h1.valid
      (fun ws hws => (hL ws (by simp [hws])).ext h1.ext)
    refine ⟨h1.ext.trans ih.ext, ih.valid, ?_⟩
    rw [List.foldl_cons, ih.value, h1.value, vz, List.map_cons, List.foldl_cons]
    congr 1
    exact List.map_congr_left fun ws hws =>
      map_valueOf_ext inp one step h1.ext (hL ws (by simp [hws]))

theorem sh_foldSum {z : Wire ι} {zv : α} (q k : ℕ) (P : SLP ι) (L : List (List (Wire ι)))
    (Ls : List (List α)) (hz : Valid P z) (vz : valueOf inp one step P z = zv)
    (hL : LSh inp one step P L Ls) :
    ShN inp one step P (foldSum z q k P L) (foldSumV one step zv q k Ls) := by
  obtain ⟨hv, rfl⟩ := hL
  cases L with
  | nil =>
    refine ⟨Ext.refl P, allValid_constL hz k 0, ?_⟩
    show (constL z k 0).map (valueOf inp one step P) = _
    rw [map_constL, vz]; rfl
  | cons a rest =>
    have h := sh_foldl_modAdd inp one step q k rest (P, a) hz vz (hv a (by simp))
      (fun ws hws => hv ws (by simp [hws]))
    exact ⟨h.ext, h.valid, h.value⟩

/-- **The shadow of a coefficient circuit**: the values of the `k` wires of the output
coefficient `(a, col, t)` of a NAND block. -/
def coefV (ordT : List ((Fin 2 × Fin k) × Fin N)) (zv : α) (q : ℕ) (A B : BI N k → α) (Gv : ℕ)
    (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N) : List α :=
  foldSumV one step zv q k (roundsV one step zv q k (treeHeight N k)
    (constV one zv k Gv :: leavesV one step zv q k A B a col t ordT))

theorem sh_coefCircuitL (ordT : List ((Fin 2 × Fin k) × Fin N)) {z : Wire ι} {zv : α} (q : ℕ)
    {repA repB : BI N k → Wire ι} {A B : BI N k → α} (Gv : ℕ) (a : Fin 2) (col : Fin 2 × Fin k)
    (t : Fin N) (P : SLP ι) (o : Opnd inp one step P z zv repA repB A B) :
    ShN inp one step P (coefCircuitL ordT z q repA repB Gv a col t P)
      (coefV one step ordT zv q A B Gv a col t) := by
  obtain ⟨e1, g1⟩ := sh_leaves inp one step q k a col t ordT P o
  have o1 := o.ext inp one step e1
  have g1' := LSh.cons inp one step (allValid_constL o1.hz k Gv) g1
  rw [map_constL, o1.vz] at g1'
  obtain ⟨e2, g2⟩ := sh_rounds inp one step q k (treeHeight N k) _ _ _ o1.hz o1.vz g1'
  have h3 := sh_foldSum inp one step q k _ _ _ (o1.hz.ext e2)
    (by rw [valueOf_ext inp one step e2 o1.hz, o1.vz]) g2
  exact ⟨e1.trans (e2.trans h3.ext), h3.valid, h3.value⟩

/-! ### A NAND block -/

/-- **The shadow of a NAND block**: the bundle of values of its output wires, from the bundles
`A`, `B` of its operands. -/
def nandV (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k)) (gv : OI N k → ℕ)
    (zv : α) (q : ℕ) (A B : BI N k → α) : BI N k → α := fun b =>
  if (b.1, b.2.1, b.2.2.2) ∈ ordO then
    (coefV one step ordT zv q A B (gv (b.1, b.2.1, b.2.2.2)) b.1 b.2.1 b.2.2.2).getD b.2.2.1 one
  else one

theorem sh_foldl_blockStep (ordT : List ((Fin 2 × Fin k) × Fin N)) (gv : OI N k → ℕ)
    {z : Wire ι} {zv : α} (q : ℕ) {repA repB : BI N k → Wire ι} {A B : BI N k → α} :
    ∀ (os : List (OI N k)) (done : List (OI N k)) (st : SLP ι × (OI N k → List (Wire ι))),
      Opnd inp one step st.1 z zv repA repB A B → (∀ o, AllValid st.1 (st.2 o)) →
      (∀ o, (st.2 o).map (valueOf inp one step st.1) =
        if o ∈ done then coefV one step ordT zv q A B (gv o) o.1 o.2.1 o.2.2 else []) →
      let r := os.foldl (blockStepL ordT gv z q repA repB) st
      Ext st.1 r.1 ∧ (∀ o, AllValid r.1 (r.2 o)) ∧
        ∀ o, (r.2 o).map (valueOf inp one step r.1) =
          if o ∈ done ∨ o ∈ os then coefV one step ordT zv q A B (gv o) o.1 o.2.1 o.2.2 else []
  | [], done, st, _, hv, hval => ⟨Ext.refl _, hv, fun o => by simpa using hval o⟩
  | o₀ :: os, done, st, op, hv, hval => by
    have h1 := sh_coefCircuitL inp one step ordT q (gv o₀) o₀.1 o₀.2.1 o₀.2.2 st.1 op
    set c := coefCircuitL ordT z q repA repB (gv o₀) o₀.1 o₀.2.1 o₀.2.2 st.1
    have ih := sh_foldl_blockStep ordT gv q os (o₀ :: done)
      (c.1, Function.update st.2 o₀ c.2) (op.ext inp one step h1.ext)
      (fun o => by
        by_cases ho : o = o₀
        · subst ho; simpa using h1.valid
        · simpa [Function.update_of_ne ho] using (hv o).ext h1.ext)
      (fun o => by
        by_cases ho : o = o₀
        · subst ho; simpa using h1.value
        · simp only [Function.update_of_ne ho]
          rw [map_valueOf_ext inp one step h1.ext (hv o), hval o]
          simp [ho])
    refine ⟨h1.ext.trans ih.1, ih.2.1, fun o => ?_⟩
    show ((os.foldl (blockStepL ordT gv z q repA repB) (c.1, Function.update st.2 o₀ c.2)).2 o).map
      (valueOf inp one step (os.foldl (blockStepL ordT gv z q repA repB)
        (c.1, Function.update st.2 o₀ c.2)).1) = _
    rw [ih.2.2 o]
    simp only [List.mem_cons]
    congr 1
    apply propext
    tauto

theorem sh_nandBlockL (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gv : OI N k → ℕ) {z : Wire ι} {zv : α} (q : ℕ) {repA repB : BI N k → Wire ι}
    {A B : BI N k → α} (P : SLP ι) (o : Opnd inp one step P z zv repA repB A B) :
    Ext P (nandBlockL ordT ordO gv z q repA repB P).1 ∧
      (∀ b, Valid (nandBlockL ordT ordO gv z q repA repB P).1
        ((nandBlockL ordT ordO gv z q repA repB P).2 b)) ∧
      ∀ b, valueOf inp one step (nandBlockL ordT ordO gv z q repA repB P).1
        ((nandBlockL ordT ordO gv z q repA repB P).2 b) = nandV one step ordT ordO gv zv q A B b := by
  obtain ⟨e, hv, hval⟩ := sh_foldl_blockStep inp one step ordT gv q ordO [] (P, fun _ => []) o
    (fun _ => allValid_nil P) (fun _ => by simp)
  refine ⟨e, fun b => valid_getD (hv _) _, fun b => ?_⟩
  show valueOf inp one step (ordO.foldl (blockStepL ordT gv z q repA repB) (P, fun _ => [])).1
    (((ordO.foldl (blockStepL ordT gv z q repA repB) (P, fun _ => [])).2
      (b.1, b.2.1, b.2.2.2)).getD b.2.2.1 .one) = _
  rw [valueOf_getD, hval]
  simp only [List.not_mem_nil, false_or, nandV]
  split_ifs <;> rfl

/-! ### The compiler -/

/-- The constant bundle (`constRepV`): `one` at the set bits of the gadget's coefficients, `zv`
elsewhere. -/
def constRepVV (zv : α) (gv : OI N k → ℕ) : BI N k → α :=
  fun b => (constV one zv k (gv (b.1, b.2.1, b.2.2.2))).getD b.2.2.1 one

/-- The shadow of `repOfL`: the bundle of a wire of the predicate's program, from the input bundles
`inB` and the bundles of the blocks so far. -/
def repV {A : Type*} (inB : A → BI N k → α) (zv : α) (gv : OI N k → ℕ)
    (bs : List (BI N k → α)) : Wire A → BI N k → α
  | .input i => inB i
  | .one => constRepVV one zv gv
  | .gate m => bs.getD m (constRepVV one zv gv)

/-- The shadow of `compileStepL`: one more block. -/
def compileStepV {A : Type*} (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gv : OI N k → ℕ) (inB : A → BI N k → α) (zv : α) (q : ℕ) (bs : List (BI N k → α))
    (g : Gate A) : List (BI N k → α) :=
  bs ++ [nandV one step ordT ordO gv zv q (repV one inB zv gv bs g.a) (repV one inB zv gv bs g.b)]

/-- **The shadow of `f̂`**: the bundle of values of the output wires of
`fhatSLPL ordT ordO gv q p w`. -/
def fhatV {A : Type*} (inB : A → BI N k → α) (ordT : List ((Fin 2 × Fin k) × Fin N))
    (ordO : List (OI N k)) (gv : OI N k → ℕ) (q : ℕ) (p : SLP A) (w : Wire A) : BI N k → α :=
  repV one inB (step one one) gv
    (p.foldl (compileStepV one step ordT ordO gv inB (step one one) q) []) w

section Compile

variable {A : Type*} (inp : A × BI N k → α)

/-- The bundles `reps` are valid in `P` and have the values `bs`. -/
def BSh (P : SLP (A × BI N k)) (reps : List (BI N k → Wire (A × BI N k)))
    (bs : List (BI N k → α)) : Prop :=
  (∀ r ∈ reps, ∀ b, Valid P (r b)) ∧ reps.map (fun r b => valueOf inp one step P (r b)) = bs

theorem sh_repOfL {z : Wire (A × BI N k)} {zv : α} (gv : OI N k → ℕ) {P : SLP (A × BI N k)}
    (hz : Valid P z) (vz : valueOf inp one step P z = zv)
    {reps : List (BI N k → Wire (A × BI N k))} {bs : List (BI N k → α)}
    (hr : BSh one step inp P reps bs) (w : Wire A) :
    (∀ b, Valid P (repOfL z gv reps w b)) ∧
      ∀ b, valueOf inp one step P (repOfL z gv reps w b) =
        repV one (fun i b => inp (i, b)) zv gv bs w b := by
  have hc : ∀ b, Valid P (constRepV z gv b) := fun b => valid_getD (allValid_constL hz k _) _
  have vc : ∀ b, valueOf inp one step P (constRepV z gv b) = constRepVV one zv gv b := by
    intro b
    simp only [constRepV, constRepVV]
    rw [valueOf_getD, map_constL, vz]
  cases w with
  | input i => exact ⟨fun b => trivial, fun b => rfl⟩
  | one => exact ⟨hc, vc⟩
  | gate m =>
    obtain ⟨hv, rfl⟩ := hr
    simp only [repOfL, repV]
    by_cases hm : m < reps.length
    · rw [List.getD_eq_getElem _ _ hm, List.getD_eq_getElem _ _ (by simpa using hm),
        List.getElem_map]
      exact ⟨hv _ (List.getElem_mem hm), fun b => rfl⟩
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨hc, vc⟩

theorem BSh.ext {P P' : SLP (A × BI N k)} (h : Ext P P') {reps : List (BI N k → Wire (A × BI N k))}
    {bs : List (BI N k → α)} (hr : BSh one step inp P reps bs) : BSh one step inp P' reps bs := by
  refine ⟨fun r hr' b => (hr.1 r hr' b).ext h, ?_⟩
  rw [← hr.2]
  exact List.map_congr_left fun r hr' => funext fun b => valueOf_ext inp one step h (hr.1 r hr' b)

theorem sh_foldl_compileStep (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gv : OI N k → ℕ) {z : Wire (A × BI N k)} {zv : α} (q : ℕ) :
    ∀ (p : SLP A) (st : SLP (A × BI N k) × List (BI N k → Wire (A × BI N k)))
      (bs : List (BI N k → α)), Valid st.1 z → valueOf inp one step st.1 z = zv →
      BSh one step inp st.1 st.2 bs →
      let r := p.foldl (compileStepL ordT ordO gv z q) st
      Ext st.1 r.1 ∧ BSh one step inp r.1 r.2
        (p.foldl (compileStepV one step ordT ordO gv (fun i b => inp (i, b)) zv q) bs)
  | [], st, bs, _, _, hr => ⟨Ext.refl _, hr⟩
  | g :: p, st, bs, hz, vz, hr => by
    obtain ⟨ha, va⟩ := sh_repOfL one step inp gv hz vz hr g.a
    obtain ⟨hb, vb⟩ := sh_repOfL one step inp gv hz vz hr g.b
    obtain ⟨e1, hv1, vv1⟩ := sh_nandBlockL inp one step ordT ordO gv q st.1
      ⟨hz, vz, ha, va, hb, vb⟩
    set r := nandBlockL ordT ordO gv z q (repOfL z gv st.2 g.a) (repOfL z gv st.2 g.b) st.1
    have hr' : BSh one step inp r.1 (st.2 ++ [r.2])
        (compileStepV one step ordT ordO gv (fun i b => inp (i, b)) zv q bs g) := by
      have hr1 := hr.ext one step inp e1
      refine ⟨fun r' hr' b => ?_, ?_⟩
      · rcases List.mem_append.mp hr' with hr' | hr'
        · exact hr1.1 r' hr' b
        · rw [List.mem_singleton] at hr'; subst hr'; exact hv1 b
      · rw [List.map_append, hr1.2, compileStepV, List.map_singleton]
        congr 2
        funext b
        exact vv1 b
    have ih := sh_foldl_compileStep ordT ordO gv q p (r.1, st.2 ++ [r.2]) _ (hz.ext e1)
      (by rw [valueOf_ext inp one step e1 hz, vz]) hr'
    exact ⟨e1.trans ih.1, ih.2⟩

/-- **The values of the output wires of `f̂`** are its shadow `fhatV`, under any semantics. -/
theorem valueOf_fhatSLPL (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gv : OI N k → ℕ) (q : ℕ) (p : SLP A) (w : Wire A) (b : BI N k) :
    valueOf inp one step (fhatSLPL ordT ordO gv q p w).1 ((fhatSLPL ordT ordO gv q p w).2 b) =
      fhatV one step (fun i b => inp (i, b)) ordT ordO gv q p w b := by
  have hz : Valid ([⟨.one, .one⟩] : SLP (A × BI N k)) (.gate 0) := by simp [Valid]
  have vz : valueOf inp one step ([⟨.one, .one⟩] : SLP (A × BI N k)) (.gate 0) = step one one :=
    valueOf_addNand inp one step [] .one .one
  obtain ⟨e, hr⟩ := sh_foldl_compileStep one step inp ordT ordO gv q p ([⟨.one, .one⟩], []) []
    hz vz ⟨fun _ h => by simp at h, rfl⟩
  exact (sh_repOfL one step inp gv (hz.ext e) (by rw [valueOf_ext inp one step e hz, vz]) hr w).2 b

end Compile

end SigabaNeo.Lattices.Algo
