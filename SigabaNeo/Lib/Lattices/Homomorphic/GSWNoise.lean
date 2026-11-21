import SigabaNeo.Lib.Lattices.Homomorphic.GSWCircuit
import SigabaNeo.Lib.Lattices.Homomorphic.NoiseGadgets

/-!
# The noise of evaluating `f̂` homomorphically

The noise bound (`slpBound WN E`) through the Boolean program of the Ring-GSW evaluation: with
`M = modFactor WN k` and `h = treeHeight N k`, one term is within `M · (WN + 1) · A`, one round of
the tree multiplies by `M`, so a NAND block multiplies by `gswFactor WN N k = M^(h+1) · (WN + 1)`
(`nb_nandBlock`), and the program of `f̂` for a straight-line program of `n` gates is within
`gswFactor^n · E` (`nb_fhatSLP`).
-/

namespace SigabaNeo.Lattices

open Cslib SLP
open scoped Matrix

variable {N q k : ℕ} [NeZero q] {ι : Type*} (WN E : ℕ) (x : ι → Bool)

/-- All wires of a representation are within `A`. -/
def RepNB (p : SLP ι) (rep : BI N k → Wire ι) (A : ℕ) : Prop := ∀ b, nb WN E p (rep b) ≤ A

theorem RepNB.mono {p : SLP ι} {rep : BI N k → Wire ι} {A B : ℕ} (hA : RepNB WN E p rep A)
    (h : A ≤ B) : RepNB WN E p rep B := fun b => (hA b).trans h

theorem RepNB.ext {p p' : SLP ι} (h : Ext p p') {rep : BI N k → Wire ι} (hv : ∀ b, Valid p (rep b))
    {A : ℕ} (hA : RepNB WN E p rep A) : RepNB WN E p' rep A := fun b => by
  rw [nb_ext WN E h (hv b)]; exact hA b

theorem nb_coefW {p : SLP ι} {rep : BI N k → Wire ι} {A : ℕ} (hA : RepNB WN E p rep A)
    (a : Fin 2) (c : Fin 2 × Fin k) (j : Fin N) : NBL WN E p (coefW rep a c j) A := by
  intro w hw
  simp only [coefW, bitsL, List.mem_ofFn] at hw
  obtain ⟨i, rfl⟩ := hw
  exact hA _

/-- **One term** of a coefficient. -/
theorem nb_termStep (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N)
    {st : SLP ι × List (Wire ι)} {v : ZMod q} (hst : AccSpec (k := k) x p z st v)
    (e : (Fin 2 × Fin k) × Fin N) {A : ℕ} (hzA : nb WN E p z ≤ A) (hAa : RepNB WN E p repA A)
    (hAb : RepNB WN E p repB A) (hstA : NBL WN E st.1 st.2 A) :
    NBL WN E (termStep z q k repA repB a col t st e).1 (termStep z q k repA repB a col t st e).2
      (modFactor WN k * ((WN + 1) * A)) := by
  have ha' := ha.ext x hst.ext
  have hb' := hb.ext x hst.ext
  have hz' := hz.ext hst.ext
  have hAa' := hAa.ext WN E hst.ext ha.1
  have hAb' := hAb.ext WN E hst.ext hb.1
  have hzA' : nb WN E st.1 z ≤ A := by rw [nb_ext WN E hst.ext hz]; exact hzA
  have hW : A ≤ (WN + 1) * A := Nat.le_mul_of_pos_left _ (by omega)
  unfold termStep
  split_ifs with h
  · obtain ⟨hcv, hcl, -⟩ := coefW_spec x hk ha' a e.1 ⟨t.val - e.2.val, by omega⟩
    have hr := andL_spec x (repB (e.1.1, col, e.1.2, e.2)) st.1
      (coefW repA a e.1 ⟨t.val - e.2.val, by omega⟩) (hb'.1 _) hcv
    have nr := nb_andL WN E (repB (e.1.1, col, e.1.2, e.2)) st.1
      (coefW repA a e.1 ⟨t.val - e.2.val, by omega⟩) (hb'.1 _) hcv (hAb' _)
      (nb_coefW WN E hAa' _ _ _)
    rw [hcl] at hr
    have h' : WN * A + A = (WN + 1) * A := by ring
    rw [h'] at nr
    exact nb_modSub WN E z q k _ st.2 _ (hz'.ext hr.ext) (hst.valid.ext hr.ext) hr.valid
      hst.length hr.length (by rw [nb_ext WN E hr.ext hz']; exact hzA'.trans hW)
      ((NBL.ext WN E hr.ext hst.valid hstA).mono WN E hW) nr
  · obtain ⟨hcv, hcl, -⟩ := coefW_spec x hk ha' a e.1 ⟨N + t.val - e.2.val, by omega⟩
    have hr := andL_spec x (repB (e.1.1, col, e.1.2, e.2)) st.1
      (coefW repA a e.1 ⟨N + t.val - e.2.val, by omega⟩) (hb'.1 _) hcv
    have nr := nb_andL WN E (repB (e.1.1, col, e.1.2, e.2)) st.1
      (coefW repA a e.1 ⟨N + t.val - e.2.val, by omega⟩) (hb'.1 _) hcv (hAb' _)
      (nb_coefW WN E hAa' _ _ _)
    rw [hcl] at hr
    have h' : WN * A + A = (WN + 1) * A := by ring
    rw [h'] at nr
    exact nb_modAdd WN E z q k _ st.2 _ (hz'.ext hr.ext) (hst.valid.ext hr.ext) hr.valid
      hst.length hr.length (by rw [nb_ext WN E hr.ext hz']; exact hzA'.trans hW)
      ((NBL.ext WN E hr.ext hst.valid hstA).mono WN E hW) nr

/-- All numbers of a list are within `X`. -/
def NBLL (p : SLP ι) (L : List (List (Wire ι))) (X : ℕ) : Prop := ∀ ws ∈ L, NBL WN E p ws X

theorem modFactor_pos (w : ℕ) : 0 < modFactor WN w := by unfold modFactor; positivity

theorem nb_leaves (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N)
    {A : ℕ} (hzA : nb WN E p z ≤ A) (hAa : RepNB WN E p repA A) (hAb : RepNB WN E p repB A) :
    ∀ (es : List ((Fin 2 × Fin k) × Fin N)) (p' : SLP ι), Ext p p' →
      NBLL WN E (leaves z q k repA repB a col t p' es).1 (leaves z q k repA repB a col t p' es).2
        (modFactor WN k * ((WN + 1) * A))
  | [], p', _ => by simp [NBLL, leaves]
  | e :: es, p', he => by
    have hz' := hz.ext he
    have hz0' : bv x p' z = false := by rw [bv_ext x he hz]; exact hz0
    obtain ⟨hcv, hcl, hcn⟩ := constL_spec x p' z hz' hz0' k 0
    have h0 : AccSpec (k := k) x p' z (p', constL z k 0) (0 : ZMod q) :=
      ⟨Ext.refl p', hcv, hcl, by simp [hcn]⟩
    have ht := termStep_spec x hk hz' hz0' (ha.ext x he) (hb.ext x he) a col t h0 e
    have hzA' : nb WN E p' z ≤ A := by rw [nb_ext WN E he hz]; exact hzA
    have nt := nb_termStep WN E x hk hz' hz0' (ha.ext x he) (hb.ext x he) a col t h0 e hzA'
      (hAa.ext WN E he ha.1) (hAb.ext WN E he hb.1)
      ((nb_constL WN E p' z k 0).mono WN E hzA')
    have ih := nb_leaves hk hz hz0 ha hb a col t hzA hAa hAb es _ (he.trans ht.ext)
    have hl := leaves_spec x hk hz hz0 ha hb a col t es _ (he.trans ht.ext)
    intro ws hws
    simp only [leaves, List.mem_cons] at hws
    rcases hws with rfl | hws
    · exact NBL.ext WN E hl.1 ht.valid nt
    · exact ih ws hws

theorem length_pairRound (z : Wire ι) (q k : ℕ) : ∀ (p : SLP ι) (L : List (List (Wire ι))),
    (pairRound z q k p L).2.length = (L.length + 1) / 2
  | p, [] => by simp [pairRound]
  | p, [_] => by simp [pairRound]
  | p, a :: b :: rest => by
    simp only [pairRound, List.length_cons, length_pairRound z q k _ rest]; omega

theorem length_rounds (z : Wire ι) (q k : ℕ) : ∀ (h : ℕ) (p : SLP ι) (L : List (List (Wire ι))),
    L.length ≤ 2 ^ h → (rounds z q k h p L).2.length ≤ 1
  | 0, p, L, hL => by simpa [rounds] using hL
  | h + 1, p, L, hL => by
    simp only [rounds]
    refine length_rounds z q k h _ _ ?_
    rw [length_pairRound, pow_succ] at *
    omega

theorem nb_pairRound (hk : q < 2 ^ k) {z : Wire ι} :
    ∀ (p : SLP ι) (L : List (List (Wire ι))) (vs : List (ZMod q)), Valid p z → bv x p z = false →
      LGood (k := k) x p L vs → ∀ {X : ℕ}, nb WN E p z ≤ X → NBLL WN E p L X →
      NBLL WN E (pairRound z q k p L).1 (pairRound z q k p L).2 (modFactor WN k * X)
  | p, [], _, _, _, _, _, _, _ => by simp [NBLL, pairRound]
  | p, [a], _, _, _, _, X, _, hL => by
    intro ws hws
    simp only [pairRound, List.mem_singleton] at hws
    subst hws
    exact (hL ws (List.mem_singleton_self _)).mono WN E
      (Nat.le_mul_of_pos_left _ (modFactor_pos WN k))
  | p, a :: b :: rest, vs, hz, hz0, h, X, hzX, hL => by
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    cases h with
    | @cons _ va _ vs₁ ha h' =>
      cases h' with
      | @cons _ vb _ vs'' hb hr =>
        have hm := modAdd_spec x z q k p a b hz hz0 ha.1 hb.1 ha.2.1 hb.2.1 hq hk.le
          (by rw [ha.2.2]; exact ZMod.val_lt _) (by rw [hb.2.2]; exact ZMod.val_lt _)
        have nm := nb_modAdd WN E z q k p a b hz ha.1 hb.1 ha.2.1 hb.2.1 hzX
          (hL a (by simp)) (hL b (by simp))
        have hz' := hz.ext hm.ext
        have hrest : NBLL WN E (modAdd z q k p a b).1 rest X := fun ws hws => by
          have hv : AllValid p ws := by
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hws
            exact (List.forall₂_iff_get.mp hr).2 i hi (by
              rw [← (List.forall₂_iff_get.mp hr).1]; exact hi) |>.1
          exact NBL.ext WN E hm.ext hv (hL ws (by simp [hws]))
        have ih := nb_pairRound hk (modAdd z q k p a b).1 rest vs'' hz'
          (by rw [bv_ext x hm.ext hz]; exact hz0) (LGood.ext (k := k) x hm.ext hr)
          (X := X) (by rw [nb_ext WN E hm.ext hz]; exact hzX) hrest
        have hpr := pairRound_spec x hk (modAdd z q k p a b).1 rest vs'' hz'
          (by rw [bv_ext x hm.ext hz]; exact hz0) (LGood.ext (k := k) x hm.ext hr)
        intro ws hws
        simp only [pairRound, List.mem_cons] at hws
        rcases hws with rfl | hws
        · exact NBL.ext WN E hpr.1 hm.valid nm
        · exact ih ws hws

theorem nb_rounds (hk : q < 2 ^ k) {z : Wire ι} :
    ∀ (h : ℕ) (p : SLP ι) (L : List (List (Wire ι))) (vs : List (ZMod q)), Valid p z →
      bv x p z = false → LGood (k := k) x p L vs → ∀ {X : ℕ}, nb WN E p z ≤ X →
      NBLL WN E p L X →
      NBLL WN E (rounds z q k h p L).1 (rounds z q k h p L).2 (modFactor WN k ^ h * X)
  | 0, p, L, vs, _, _, _, X, _, hL => by simpa [rounds] using hL
  | h + 1, p, L, vs, hz, hz0, hg, X, hzX, hL => by
    obtain ⟨e₁, g₁⟩ := pairRound_spec x hk p L vs hz hz0 hg
    have n₁ := nb_pairRound WN E x hk p L vs hz hz0 hg hzX hL
    have hM : X ≤ modFactor WN k * X := Nat.le_mul_of_pos_left _ (modFactor_pos WN k)
    have ih := nb_rounds hk h _ _ _ (hz.ext e₁) (by rw [bv_ext x e₁ hz]; exact hz0) g₁
      (X := modFactor WN k * X) (by rw [nb_ext WN E e₁ hz]; exact hzX.trans hM) n₁
    simp only [rounds]
    rw [pow_succ, mul_assoc]
    exact ih

theorem nb_foldSum {z : Wire ι} (p : SLP ι) (L : List (List (Wire ι))) (hL1 : L.length ≤ 1)
    {X : ℕ} (hzX : nb WN E p z ≤ X) (hL : NBLL WN E p L X) :
    NBL WN E (foldSum z q k p L).1 (foldSum z q k p L).2 X := by
  match L, hL1 with
  | [], _ => exact (nb_constL WN E p z k 0).mono WN E hzX
  | [a], _ => simpa [foldSum] using hL a (List.mem_singleton_self _)

/-- The factor of one NAND block: `M^(h+1) · (WN + 1)`. -/
def gswFactor (WN N k : ℕ) : ℕ := modFactor WN k ^ (treeHeight N k + 1) * (WN + 1)

/-- **The noise of one output coefficient.** -/
theorem nb_coefCircuit (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N)
    {A : ℕ} (hzA : nb WN E p z ≤ A) (hAa : RepNB WN E p repA A) (hAb : RepNB WN E p repB A) :
    NBL WN E (coefCircuit z q k repA repB (((gswBin hk).G a col).coeffs t).val a col t p).1
      (coefCircuit z q k repA repB (((gswBin hk).G a col).coeffs t).val a col t p).2
      (gswFactor WN N k * A) := by
  set es := (Finset.univ : Finset ((Fin 2 × Fin k) × Fin N)).toList
  set Gv := (((gswBin hk).G a col).coeffs t).val
  obtain ⟨e₁, g₁⟩ := leaves_spec x hk hz hz0 ha hb a col t es p (Ext.refl p)
  have n₁ := nb_leaves WN E x hk hz hz0 ha hb a col t hzA hAa hAb es p (Ext.refl p)
  set r := leaves z q k repA repB a col t p es
  set X := modFactor WN k * ((WN + 1) * A) with hX
  have hAX : A ≤ X := by
    rw [hX]
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans
      (Nat.le_mul_of_pos_left _ (modFactor_pos WN k))
  have hz₁ := hz.ext e₁
  have hz0₁ : bv x r.1 z = false := by rw [bv_ext x e₁ hz]; exact hz0
  have hzX : nb WN E r.1 z ≤ X := by rw [nb_ext WN E e₁ hz]; exact hzA.trans hAX
  obtain ⟨hcv, hcl, hcn⟩ := constL_spec x r.1 z hz₁ hz0₁ k Gv
  have g₁' : LGood (k := k) x r.1 (constL z k Gv :: r.2)
      ((((gswBin hk).G a col).coeffs t) :: es.map (termZ Ψa Ψb a col t)) :=
    List.Forall₂.cons ⟨hcv, hcl, by rw [hcn, Nat.mod_eq_of_lt ((ZMod.val_lt _).trans hk)]⟩ g₁
  have n₁' : NBLL WN E r.1 (constL z k Gv :: r.2) X := by
    intro ws hws
    rcases List.mem_cons.mp hws with rfl | hws
    · exact (nb_constL WN E r.1 z k Gv).mono WN E hzX
    · exact n₁ ws hws
  obtain ⟨e₂, -⟩ := rounds_spec x hk (treeHeight N k) r.1 _ _ hz₁ hz0₁ g₁'
  have n₂ := nb_rounds WN E x hk (treeHeight N k) r.1 _ _ hz₁ hz0₁ g₁' hzX n₁'
  have hlen : (constL z k Gv :: r.2).length ≤ 2 ^ treeHeight N k := by
    have hl : r.2.length = es.length := by rw [g₁.length_eq, List.length_map]
    rw [List.length_cons, hl, Finset.length_toList, Finset.card_univ]
    exact Nat.le_pow_clog (by norm_num) _
  have hX2 : nb WN E (rounds z q k (treeHeight N k) r.1 (constL z k Gv :: r.2)).1 z ≤
      modFactor WN k ^ treeHeight N k * X := by
    rw [nb_ext WN E e₂ hz₁]
    exact hzX.trans (Nat.le_mul_of_pos_left _ (pow_pos (modFactor_pos WN k) _))
  have n₃ := nb_foldSum WN E (q := q) (k := k) _ _ (length_rounds z q k _ _ _ hlen) hX2 n₂
  refine n₃.mono WN E (le_of_eq ?_)
  rw [hX, gswFactor, pow_succ]
  ring

theorem nb_foldl_blockStep (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) {A : ℕ} (hzA : nb WN E p z ≤ A)
    (hAa : RepNB WN E p repA A) (hAb : RepNB WN E p repB A) :
    ∀ (outs : List (OI N k)) (st : SLP ι × (OI N k → List (Wire ι))),
      Ext p st.1 → (∀ o, AllValid st.1 (st.2 o) ∧ NBL WN E st.1 (st.2 o) (gswFactor WN N k * A)) →
      let st' := outs.foldl (blockStep z q k hk repA repB) st
      Ext p st'.1 ∧ ∀ o, AllValid st'.1 (st'.2 o) ∧ NBL WN E st'.1 (st'.2 o) (gswFactor WN N k * A)
  | [], st, he, hg => ⟨he, hg⟩
  | o₀ :: os, st, he, hg => by
    have hc := coefCircuit_spec x hk (hz.ext he) (by rw [bv_ext x he hz]; exact hz0) (ha.ext x he)
      (hb.ext x he) o₀.1 o₀.2.1 o₀.2.2
    have nc := nb_coefCircuit WN E x hk (hz.ext he) (by rw [bv_ext x he hz]; exact hz0)
      (ha.ext x he) (hb.ext x he) o₀.1 o₀.2.1 o₀.2.2
      (by rw [nb_ext WN E he hz]; exact hzA) (hAa.ext WN E he ha.1) (hAb.ext WN E he hb.1)
    have he' : Ext p (blockStep z q k hk repA repB st o₀).1 := he.trans hc.ext
    have hg' : ∀ o, AllValid (blockStep z q k hk repA repB st o₀).1
        ((blockStep z q k hk repA repB st o₀).2 o) ∧
        NBL WN E (blockStep z q k hk repA repB st o₀).1
          ((blockStep z q k hk repA repB st o₀).2 o) (gswFactor WN N k * A) := by
      intro o
      by_cases hoo : o = o₀
      · subst hoo
        simp only [blockStep, Function.update_self]
        exact ⟨hc.valid, nc⟩
      · simp only [blockStep, Function.update_of_ne hoo]
        exact ⟨(hg o).1.ext hc.ext, NBL.ext WN E hc.ext (hg o).1 (hg o).2⟩
    simp only [List.foldl_cons]
    exact nb_foldl_blockStep hk hz hz0 ha hb hzA hAa hAb os _ he' hg'

/-- **The noise of a NAND block**: multiplied by `gswFactor WN N k`. -/
theorem nb_nandBlock (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) {A : ℕ} (hzA : nb WN E p z ≤ A)
    (hAa : RepNB WN E p repA A) (hAb : RepNB WN E p repB A) :
    RepNB WN E (nandBlock z q k hk repA repB p).1 (nandBlock z q k hk repA repB p).2
      (gswFactor WN N k * A) := by
  obtain ⟨-, hg⟩ := nb_foldl_blockStep WN E x hk hz hz0 ha hb hzA hAa hAb
    ((Finset.univ : Finset (OI N k)).toList) (p, fun _ => []) (Ext.refl p)
    (fun _ => ⟨by simp [AllValid], by simp [NBL]⟩)
  intro b
  simp only [nandBlock]
  refine (nb_getD WN E (hg (b.1, b.2.1, b.2.2.2)).2 _).trans le_rfl

theorem nb_constRep {p : SLP ι} (z : Wire ι) (Ψ : Matrix (Fin 2) (Fin 2 × Fin k)
    (Negacyclic (ZMod q) N)) : RepNB WN E p (constRep z k Ψ) (nb WN E p z) := fun b =>
  nb_getD WN E (nb_constL WN E p z k _) _

theorem gswFactor_pos (N k : ℕ) : 0 < gswFactor WN N k := by
  unfold gswFactor; exact Nat.mul_pos (pow_pos (modFactor_pos WN k) _) (by omega)

section CompileSLP

variable {A : Type*} (hk : q < 2 ^ k) (x : A × BI N k → Bool)
  (Ψ : A → Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))

theorem nb_repOf {prog : SLP (A × BI N k)} {z : Wire (A × BI N k)}
    {reps : List (BI N k → Wire (A × BI N k))} {B : ℕ} (hEB : E ≤ B)
    (hzB : nb WN E prog z ≤ B) (hr : ∀ r ∈ reps, RepNB WN E prog r B) (w : Wire A) :
    RepNB WN E prog (repOf z hk reps w) B := by
  cases w with
  | input i => intro b; simpa [repOf, nb_input] using hEB
  | one => exact fun b => (nb_constRep WN E z _ b).trans hzB
  | gate m =>
    simp only [repOf]
    by_cases hm : m < reps.length
    · rw [List.getD_eq_getElem _ _ hm]; exact hr _ (List.getElem_mem hm)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hm)]
      exact fun b => (nb_constRep WN E z _ b).trans hzB

theorem nb_foldl_compileStep
    (hx : ∀ i a c b j, x (i, a, c, b, j) = ((Ψ i a c).coeffs j).val.testBit b)
    {z : Wire (A × BI N k)} :
    ∀ (p : SLP A) (prog : SLP (A × BI N k)) (reps : List (BI N k → Wire (A × BI N k)))
      (vals : List (Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))) (B : ℕ),
      Valid prog z → bv x prog z = false → RepsInv x prog reps vals → E ≤ B →
      nb WN E prog z ≤ E → (∀ r ∈ reps, RepNB WN E prog r B) →
      ∀ r ∈ (p.foldl (compileStep z hk) (prog, reps)).2,
        RepNB WN E (p.foldl (compileStep z hk) (prog, reps)).1 r (gswFactor WN N k ^ p.length * B)
  | [], prog, reps, vals, B, _, _, _, _, _, hr => by simpa using hr
  | g :: p, prog, reps, vals, B, hz, hz0, h, hEB, hzE, hr => by
    have ha := repOf_spec hk x Ψ hx hz hz0 h g.a
    have hb := repOf_spec hk x Ψ hx hz hz0 h g.b
    obtain ⟨e₁, r₁⟩ := nandBlock_spec x hk hz hz0 ha hb
    have n₁ := nb_nandBlock WN E x hk hz hz0 ha hb (A := B) (hzE.trans hEB)
      (nb_repOf WN E hk hEB (hzE.trans hEB) hr g.a) (nb_repOf WN E hk hEB (hzE.trans hEB) hr g.b)
    have hz₁ := hz.ext e₁
    have hz0₁ : bv x (nandBlock z q k hk (repOf z hk reps g.a) (repOf z hk reps g.b) prog).1 z =
        false := by rw [bv_ext x e₁ hz]; exact hz0
    have hFB : B ≤ gswFactor WN N k * B := Nat.le_mul_of_pos_left _ (gswFactor_pos WN N k)
    have h₁ : RepsInv x (nandBlock z q k hk (repOf z hk reps g.a) (repOf z hk reps g.b) prog).1
        (reps ++ [(nandBlock z q k hk (repOf z hk reps g.a) (repOf z hk reps g.b) prog).2])
        (vals ++ [gswStep hk (SLP.wireVal Ψ (gswBin hk).G vals g.a)
          (SLP.wireVal Ψ (gswBin hk).G vals g.b)]) := by
      refine ⟨by simp [h.1], fun m hm hm' => ?_⟩
      by_cases hlt : m < reps.length
      · rw [List.getElem_append_left hlt, List.getElem_append_left (h.1 ▸ hlt)]
        exact (h.2 m hlt (h.1 ▸ hlt)).ext x e₁
      · have hm1 : m = reps.length := by simp at hm; omega
        subst hm1
        rw [List.getElem_append_right (Nat.le_refl _), List.getElem_append_right (h.1 ▸ Nat.le_refl _)]
        simp only [Nat.sub_self, h.1, List.getElem_singleton]
        exact r₁
    have hr₁ : ∀ r ∈ reps ++ [(nandBlock z q k hk (repOf z hk reps g.a) (repOf z hk reps g.b)
        prog).2], RepNB WN E (nandBlock z q k hk (repOf z hk reps g.a) (repOf z hk reps g.b)
          prog).1 r (gswFactor WN N k * B) := by
      intro r hr'
      rcases List.mem_append.mp hr' with hr' | hr'
      · obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hr'
        exact ((hr _ hr').ext WN E e₁ (h.2 m hm (h.1 ▸ hm)).1).mono WN E hFB
      · rw [List.mem_singleton] at hr'; subst hr'; exact n₁
    have ih := nb_foldl_compileStep hx p _ _ _ (gswFactor WN N k * B) hz₁ hz0₁ h₁
      (hEB.trans hFB) (by rw [nb_ext WN E e₁ hz]; exact hzE) hr₁
    intro r hr'
    have := ih r hr'
    rw [List.length_cons, pow_succ, mul_assoc]
    exact this

/-- **The noise of the compiled program**: within `gswFactor^n · E` for `n` gates. -/
theorem nb_compileSLP
    (hx : ∀ i a c b j, x (i, a, c, b, j) = ((Ψ i a c).coeffs j).val.testBit b)
    {z : Wire (A × BI N k)} (p : SLP A) (w : Wire A) (prog : SLP (A × BI N k))
    (hz : Valid prog z) (hz0 : bv x prog z = false) (hzE : nb WN E prog z ≤ E) :
    RepNB WN E (compileSLP z hk p w prog).1 (compileSLP z hk p w prog).2
      (gswFactor WN N k ^ p.length * E) := by
  have hr := nb_foldl_compileStep WN E hk x Ψ hx p prog [] [] E hz hz0
    ⟨rfl, fun _ h => absurd h (by simp)⟩ le_rfl hzE (by simp)
  obtain ⟨e, -⟩ := foldl_compileStep_spec hk x Ψ hx p prog [] [] hz hz0
    ⟨rfl, fun _ h => absurd h (by simp)⟩
  have hFE : E ≤ gswFactor WN N k ^ p.length * E :=
    Nat.le_mul_of_pos_left _ (pow_pos (gswFactor_pos WN N k) _)
  exact nb_repOf WN E hk hFE (by rw [nb_ext WN E e hz]; exact hzE.trans hFE) hr w

end CompileSLP

/-- **The noise of `f̂`**: every output wire of the program of `f̂` for a straight-line program of
`n` gates is within `gswFactor WN N k ^ n · E`. -/
theorem nb_fhatSLP {A : Type*} (hk : q < 2 ^ k) (p : SLP A) (w : Wire A) (b : BI N k) :
    nb WN E (fhatSLP (N := N) hk p w).1 ((fhatSLP (N := N) hk p w).2 b) ≤
      gswFactor WN N k ^ p.length * E := by
  let x₀ : A × BI N k → Bool := fun _ => false
  let Ψ₀ : A → Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N) := fun _ => 0
  have hx : ∀ i a c b j, x₀ (i, a, c, b, j) = ((Ψ₀ i a c).coeffs j).val.testBit b := by
    intro i a c b j; simp [x₀, Ψ₀]
  have h0 : bv x₀ [⟨.one, .one⟩] (Wire.gate 0 : Wire (A × BI N k)) = false := by
    have := bv_addNand x₀ ([] : SLP (A × BI N k)) .one .one trivial trivial
    simpa [addNand, bv, evalBool, valueOf, wireVal] using this
  have hz : nb WN E ([⟨.one, .one⟩] : SLP (A × BI N k)) (Wire.gate 0) ≤ E := by
    have := nb_addNand WN E ([] : SLP (A × BI N k)) .one .one
    simp only [addNand, List.nil_append, List.length_nil, nb_one, mul_zero, add_zero] at this
    rw [this]; exact Nat.zero_le _
  exact nb_compileSLP WN E hk x₀ Ψ₀ hx p w [⟨.one, .one⟩] (by simp [Valid]) h0 hz b

end SigabaNeo.Lattices
