import SigabaNeo.Lib.Lattices.Homomorphic.BoolArith
import SigabaNeo.Lib.Lattices.Homomorphic.BinaryDigits

/-!
# Ring-GSW evaluation as a Boolean straight-line program

The Ring-GSW NAND `Ψ = G − Ψ_a · G⁻¹(Ψ_b)` over `R_q = ℤ_q[X]/(X^N + 1)` with binary digits, on the
bits of the coefficients of the entries, as a polynomial-size Boolean program.

With `W = Fin 2 × Fin k` and `rot(v)_{t,j} = v_{t−j}` for `j ≤ t` and `−v_{N+t−j}` otherwise,

  `(G − Ψ_a G⁻¹(Ψ_b))_{a,col,t} = G_{a,col,t} − ∑_{c' ∈ W} ∑_{j < N} rot((Ψ_a)_{a,c'})_{t,j} d_{c',j}`

(`coeff_gswNand`), where `d_{c',j}` is the bit `c'.2` of the coefficient `j` of `(Ψ_b)_{c'.1,col}`:
the digits are the input bits themselves. One output coefficient is the sum modulo `q` of the
gadget's coefficient and the `|W| · N` terms, each computed from `0` by a bitwise `and` and one
modular addition or subtraction of `k`-bit numbers (`leaves`), then added by a balanced tree of
modular additions (`pairRound`, `rounds`, `treeHeight` rounds): the depth, and so the noise of
evaluating `f̂` homomorphically, grows with `log(|W| N)` per NAND (`coefCircuit`,
`coefCircuit_spec`).
-/

namespace SigabaNeo.Lattices

open Cslib SLP
open scoped Matrix

variable {N q k : ℕ} [NeZero q]

/-- The Ring-GSW gadget with binary digits. -/
noncomputable abbrev gswBin (hk : q < 2 ^ k) :
    GadgetMatrix (Negacyclic (ZMod q) N) (Fin 2) (Fin 2 × Fin k) :=
  gswGadget (binaryDigits N q k hk.le)

omit [NeZero q] in
/-- The negacyclic matrix, entrywise. -/
theorem rotMatrix_apply (v : Fin N → ZMod q) (t j : Fin N) :
    rotMatrix v t j = if h : j.val ≤ t.val then v ⟨t.val - j.val, by omega⟩
      else -v ⟨N + t.val - j.val, by omega⟩ := rfl

/-- The decomposition of the Ring-GSW gadget: the binary digit of the entry. -/
theorem gswBin_ginv (hk : q < 2 ^ k) (A : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))
    (c' col : Fin 2 × Fin k) : (gswBin hk).ginv A c' col = binaryDigit (A c'.1 col) c'.2 := by
  simp only [gswBin, gswGadget, gadgetOf, Matrix.of_apply, id]
  rw [Finset.sum_eq_single c'.1]
  · simp [binaryDigits]
  · intro b _ hb; simp [hb]
  · simp

/-- The digit `c'.2` of the coefficient `j` of `(Ψ_b)_{c'.1, col}`, in `ℤ_q`. -/
def digitZ (Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)) (col c' : Fin 2 × Fin k)
    (j : Fin N) : ZMod q :=
  if ((Ψb c'.1 col).coeffs j).val.testBit c'.2 then 1 else 0

/-- **The coefficients of a Ring-GSW NAND.** -/
theorem coeff_gswNand (hk : q < 2 ^ k) (Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))
    (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N) :
    (((gswBin hk).G - Ψa * (gswBin hk).ginv Ψb : Matrix (Fin 2) (Fin 2 × Fin k)
      (Negacyclic (ZMod q) N)) a col).coeffs t =
      ((gswBin hk).G a col).coeffs t +
        ∑ e : (Fin 2 × Fin k) × Fin N, -(rotMatrix (Ψa a e.1).coeffs t e.2 * digitZ Ψb col e.1 e.2) := by
  simp only [Matrix.sub_apply, Negacyclic.coeffs_sub, Pi.sub_apply, Matrix.mul_apply,
    Negacyclic.coeffs_sum, Finset.sum_apply, Negacyclic.coeffs_mul, gswBin_ginv]
  rw [sub_eq_add_neg]
  conv_rhs => rw [Fintype.sum_prod_type (f := fun e : (Fin 2 × Fin k) × Fin N =>
    -(rotMatrix (Ψa a e.1).coeffs t e.2 * digitZ Ψb col e.1 e.2))]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c' _
  show -((rotMatrix (Ψa a c').coeffs *ᵥ (binaryDigit (Ψb c'.1 col) c'.2).coeffs) t) = _
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp [digitZ, coeffs_binaryDigit]

/-! ### Representations of ciphertexts by wires -/

/-- The positions of the bits of a Ring-GSW ciphertext: row, column, bit, coefficient. -/
abbrev BI (N k : ℕ) := Fin 2 × (Fin 2 × Fin k) × Fin k × Fin N

variable {ι : Type*} (x : ι → Bool)

/-- `rep` represents `Ψ` in `p`: its wires are valid and carry the bits of the coefficients. -/
def Rep (p : SLP ι) (rep : BI N k → Wire ι) (Ψ : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)) :
    Prop :=
  (∀ b, Valid p (rep b)) ∧ ∀ a c i j, bv x p (rep (a, c, i, j)) = ((Ψ a c).coeffs j).val.testBit i

omit [NeZero q] in
theorem Rep.ext {p p' : SLP ι} (h : Ext p p') {rep : BI N k → Wire ι}
    {Ψ : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)} (hr : Rep x p rep Ψ) :
    Rep x p' rep Ψ :=
  ⟨fun b => (hr.1 b).ext h, fun a c i j => by rw [bv_ext x h (hr.1 _)]; exact hr.2 a c i j⟩

/-- The wires of a coefficient. -/
def coefW (rep : BI N k → Wire ι) (a : Fin 2) (c : Fin 2 × Fin k) (j : Fin N) : List (Wire ι) :=
  bitsL k fun i => rep (a, c, i, j)

theorem coefW_spec (hk : q < 2 ^ k) {p : SLP ι} {rep : BI N k → Wire ι}
    {Ψ : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)} (hr : Rep x p rep Ψ) (a : Fin 2)
    (c : Fin 2 × Fin k) (j : Fin N) :
    AllValid p (coefW rep a c j) ∧ (coefW rep a c j).length = k ∧
      nv x p (coefW rep a c j) = ((Ψ a c).coeffs j).val := by
  refine ⟨?_, length_bitsL _ _, ?_⟩
  · intro w hw
    simp only [coefW, bitsL, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    exact hr.1 _
  · rw [coefW, nv_bitsL x p k _ _ (fun i => hr.2 a c i j), Nat.mod_eq_of_lt]
    exact (ZMod.val_lt _).trans hk

/-- The value of a list of wires gives the values of its wires. -/
theorem bv_getD_of_nv (p : SLP ι) : ∀ (ws : List (Wire ι)) (i : ℕ), i < ws.length →
    bv x p (ws.getD i .one) = (nv x p ws).testBit i
  | [], i, h => by simp at h
  | w :: ws, 0, _ => by
    simp only [List.getD_cons_zero, nv, Nat.testBit_zero]
    cases bv x p w <;> simp [Nat.add_mul_mod_self_left]
  | w :: ws, i + 1, h => by
    simp only [List.getD_cons_succ, nv, Nat.testBit_succ]
    rw [bv_getD_of_nv p ws i (by simpa using h)]
    congr 1
    cases bv x p w <;> simp <;> omega

/-! ### One coefficient of a NAND -/

/-- The term `(c', j)` of a coefficient: `−rot((Ψ_a)_{a,c'})_{t,j} · d_{c',j}`. -/
def termZ (Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (e : (Fin 2 × Fin k) × Fin N) : ZMod q :=
  -(rotMatrix (Ψa a e.1).coeffs t e.2 * digitZ Ψb col e.1 e.2)

/-- One term: subtract or add the selected coefficient. -/
def termStep (z : Wire ι) (q k : ℕ) (repA repB : BI N k → Wire ι) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (st : SLP ι × List (Wire ι)) (e : (Fin 2 × Fin k) × Fin N) :
    SLP ι × List (Wire ι) :=
  if h : e.2.val ≤ t.val then
    let r := andL (repB (e.1.1, col, e.1.2, e.2)) st.1 (coefW repA a e.1 ⟨t.val - e.2.val, by omega⟩)
    modSub z q k r.1 st.2 r.2
  else
    let r := andL (repB (e.1.1, col, e.1.2, e.2)) st.1
      (coefW repA a e.1 ⟨N + t.val - e.2.val, by omega⟩)
    modAdd z q k r.1 st.2 r.2

/-- The invariant of the running sum. -/
structure AccSpec (p : SLP ι) (z : Wire ι) (st : SLP ι × List (Wire ι)) (v : ZMod q) : Prop where
  ext : Ext p st.1
  valid : AllValid st.1 st.2
  length : st.2.length = k
  value : nv x st.1 st.2 = v.val

theorem termStep_spec (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N)
    {st : SLP ι × List (Wire ι)} {v : ZMod q} (hst : AccSpec (k := k) x p z st v)
    (e : (Fin 2 × Fin k) × Fin N) :
    AccSpec (k := k) x p z (termStep z q k repA repB a col t st e) (v + termZ Ψa Ψb a col t e) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have ha' := ha.ext x hst.ext
  have hb' := hb.ext x hst.ext
  have hz' := hz.ext hst.ext
  have hz0' : bv x st.1 z = false := by rw [bv_ext x hst.ext hz]; exact hz0
  have hd := hb'.2 e.1.1 col e.1.2 e.2
  have hdig : digitZ Ψb col e.1 e.2 = if bv x st.1 (repB (e.1.1, col, e.1.2, e.2)) then 1 else 0 := by
    rw [hd]; rfl
  unfold termStep
  split_ifs with h
  · obtain ⟨hcv, hcl, hcn⟩ := coefW_spec x hk ha' a e.1 ⟨t.val - e.2.val, by omega⟩
    set r := andL (repB (e.1.1, col, e.1.2, e.2)) st.1 (coefW repA a e.1 ⟨t.val - e.2.val, by omega⟩) with hr_def
    have hr := andL_spec x (repB (e.1.1, col, e.1.2, e.2)) st.1 (coefW repA a e.1 ⟨t.val - e.2.val, by omega⟩)
      (hb'.1 _) hcv
    rw [← hr_def, hcn, hcl] at hr
    have hlt : (if bv x st.1 (repB (e.1.1, col, e.1.2, e.2)) then
        ((Ψa a e.1).coeffs ⟨t.val - e.2.val, by omega⟩).val else 0) < q := by
      split_ifs <;> first | exact ZMod.val_lt _ | exact hq
    have hm := modSub_spec x z q k r.1 st.2 r.2 (hz'.ext hr.ext)
      (by rw [bv_ext x hr.ext hz']; exact hz0') (hst.valid.ext hr.ext) hr.valid hst.length hr.length hk
      (by rw [nv_ext x hr.ext hst.valid, hst.value]; exact ZMod.val_lt _) (by rw [hr.value]; exact hlt)
    rw [nv_ext x hr.ext hst.valid, hst.value, hr.value] at hm
    refine ⟨hst.ext.trans (hr.ext.trans hm.ext), hm.valid, hm.length, ?_⟩
    rw [hm.value, modSub_val (ZMod.val_lt _) hlt]
    simp only [termZ, rotMatrix_apply, h, ↓reduceDIte, hdig]
    split_ifs <;> simp [ZMod.natCast_val, sub_eq_add_neg]
  · obtain ⟨hcv, hcl, hcn⟩ := coefW_spec x hk ha' a e.1 ⟨N + t.val - e.2.val, by omega⟩
    set r := andL (repB (e.1.1, col, e.1.2, e.2)) st.1 (coefW repA a e.1 ⟨N + t.val - e.2.val, by omega⟩) with hr_def
    have hr := andL_spec x (repB (e.1.1, col, e.1.2, e.2)) st.1 (coefW repA a e.1 ⟨N + t.val - e.2.val, by omega⟩)
      (hb'.1 _) hcv
    rw [← hr_def, hcn, hcl] at hr
    have hlt : (if bv x st.1 (repB (e.1.1, col, e.1.2, e.2)) then
        ((Ψa a e.1).coeffs ⟨N + t.val - e.2.val, by omega⟩).val else 0) < q := by
      split_ifs <;> first | exact ZMod.val_lt _ | exact hq
    have hm := modAdd_spec x z q k r.1 st.2 r.2 (hz'.ext hr.ext)
      (by rw [bv_ext x hr.ext hz']; exact hz0') (hst.valid.ext hr.ext) hr.valid hst.length hr.length hq
      hk.le (by rw [nv_ext x hr.ext hst.valid, hst.value]; exact ZMod.val_lt _)
      (by rw [hr.value]; exact hlt)
    rw [nv_ext x hr.ext hst.valid, hst.value, hr.value] at hm
    refine ⟨hst.ext.trans (hr.ext.trans hm.ext), hm.valid, hm.length, ?_⟩
    rw [hm.value, modAdd_val]
    simp only [termZ, rotMatrix_apply, h, ↓reduceDIte, hdig]
    split_ifs <;> simp [ZMod.natCast_val]

theorem foldl_termStep_spec (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N) :
    ∀ (terms : List ((Fin 2 × Fin k) × Fin N)) (st : SLP ι × List (Wire ι)) (v : ZMod q),
      AccSpec (k := k) x p z st v →
      AccSpec (k := k) x p z (terms.foldl (termStep z q k repA repB a col t) st)
        (v + (terms.map (termZ Ψa Ψb a col t)).sum)
  | [], st, v, h => by simpa using h
  | e :: es, st, v, h => by
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ← add_assoc]
    exact foldl_termStep_spec hk hz hz0 ha hb a col t es _ _ (termStep_spec x hk hz hz0 ha hb a col t h e)

/-! ### Summing by a balanced tree -/

/-- Pairwise sums of a list of values. -/
def pairSums {M : Type*} [Add M] : List M → List M
  | a :: b :: rest => (a + b) :: pairSums rest
  | l => l

omit [NeZero q] in
theorem sum_pairSums : ∀ (vs : List (ZMod q)), (pairSums vs).sum = vs.sum
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simp only [pairSums, List.sum_cons, sum_pairSums rest]; ring

theorem length_pairSums {M : Type*} [Add M] : ∀ (vs : List M),
    (pairSums vs).length = (vs.length + 1) / 2
  | [] => by simp [pairSums]
  | [_] => by simp [pairSums]
  | a :: b :: rest => by
    simp only [pairSums, List.length_cons, length_pairSums rest]; omega

/-- The computed numbers `L` have the values `vs`. -/
def LGood (p : SLP ι) (L : List (List (Wire ι))) (vs : List (ZMod q)) : Prop :=
  List.Forall₂ (fun ws v => AllValid p ws ∧ ws.length = k ∧ nv x p ws = v.val) L vs

omit [NeZero q] in
theorem LGood.ext {p p' : SLP ι} (h : Ext p p') {L : List (List (Wire ι))} {vs : List (ZMod q)}
    (hg : LGood (k := k) x p L vs) : LGood (k := k) x p' L vs :=
  hg.imp fun _ _ hw => ⟨hw.1.ext h, hw.2.1, by rw [nv_ext x h hw.1]; exact hw.2.2⟩

/-- One round: add adjacent numbers modulo `q`. -/
def pairRound (z : Wire ι) (q k : ℕ) : SLP ι → List (List (Wire ι)) → SLP ι × List (List (Wire ι))
  | p, a :: b :: rest =>
    let r := modAdd z q k p a b
    let r' := pairRound z q k r.1 rest
    (r'.1, r.2 :: r'.2)
  | p, l => (p, l)

theorem pairRound_spec (hk : q < 2 ^ k) {z : Wire ι} :
    ∀ (p : SLP ι) (L : List (List (Wire ι))) (vs : List (ZMod q)), Valid p z → bv x p z = false →
      LGood (k := k) x p L vs →
      Ext p (pairRound z q k p L).1 ∧ LGood (k := k) x (pairRound z q k p L).1
        (pairRound z q k p L).2 (pairSums vs)
  | p, [], _, _, _, h => by cases h; exact ⟨Ext.refl p, List.Forall₂.nil⟩
  | p, [a], _, _, _, h => by
    cases h with
    | cons h1 h2 => cases h2; exact ⟨Ext.refl p, List.Forall₂.cons h1 List.Forall₂.nil⟩
  | p, a :: b :: rest, vs, hz, hz0, h => by
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    cases h with
    | @cons _ va _ vs₁ ha h' =>
      cases h' with
      | @cons _ vb _ vs'' hb hr =>
        have hm := modAdd_spec x z q k p a b hz hz0 ha.1 hb.1 ha.2.1 hb.2.1 hq hk.le
          (by rw [ha.2.2]; exact ZMod.val_lt _) (by rw [hb.2.2]; exact ZMod.val_lt _)
        have ih := pairRound_spec hk (modAdd z q k p a b).1 rest vs'' (hz.ext hm.ext)
          (by rw [bv_ext x hm.ext hz]; exact hz0) (LGood.ext (k := k) x hm.ext hr)
        refine ⟨hm.ext.trans ih.1, List.Forall₂.cons ?_ ih.2⟩
        refine ⟨hm.valid.ext ih.1, hm.length, ?_⟩
        change nv x (pairRound z q k (modAdd z q k p a b).1 rest).1 _ = _
        rw [nv_ext x ih.1 hm.valid, hm.value, ha.2.2, hb.2.2, modAdd_val]
        simp

/-- `h` rounds. -/
def rounds (z : Wire ι) (q k : ℕ) : ℕ → SLP ι → List (List (Wire ι)) → SLP ι × List (List (Wire ι))
  | 0, p, L => (p, L)
  | h + 1, p, L =>
    let r := pairRound z q k p L
    rounds z q k h r.1 r.2

theorem rounds_spec (hk : q < 2 ^ k) {z : Wire ι} :
    ∀ (h : ℕ) (p : SLP ι) (L : List (List (Wire ι))) (vs : List (ZMod q)), Valid p z →
      bv x p z = false → LGood (k := k) x p L vs →
      Ext p (rounds z q k h p L).1 ∧ ∃ vs', vs'.sum = vs.sum ∧
        LGood (k := k) x (rounds z q k h p L).1 (rounds z q k h p L).2 vs'
  | 0, p, L, vs, _, _, hg => ⟨Ext.refl p, vs, rfl, hg⟩
  | h + 1, p, L, vs, hz, hz0, hg => by
    obtain ⟨e₁, g₁⟩ := pairRound_spec x hk p L vs hz hz0 hg
    obtain ⟨e₂, vs', hs, g₂⟩ := rounds_spec hk h _ _ _ (hz.ext e₁)
      (by rw [bv_ext x e₁ hz]; exact hz0) g₁
    exact ⟨e₁.trans e₂, vs', by rw [hs, sum_pairSums], g₂⟩

/-- The sum of the remaining numbers, from left to right (`0` if none). -/
def foldSum (z : Wire ι) (q k : ℕ) : SLP ι → List (List (Wire ι)) → SLP ι × List (Wire ι)
  | p, [] => (p, constL z k 0)
  | p, a :: rest => rest.foldl (fun st b => modAdd z q k st.1 st.2 b) (p, a)

theorem foldl_modAdd_spec (hk : q < 2 ^ k) {z : Wire ι} {p₀ : SLP ι} (hz : Valid p₀ z)
    (hz0 : bv x p₀ z = false) :
    ∀ (L : List (List (Wire ι))) (vs : List (ZMod q)) (st : SLP ι × List (Wire ι)) (v : ZMod q),
      AccSpec (k := k) x p₀ z st v → LGood (k := k) x st.1 L vs →
      AccSpec (k := k) x p₀ z (L.foldl (fun st b => modAdd z q k st.1 st.2 b) st) (v + vs.sum)
  | [], vs, st, v, hst, hg => by cases hg; simpa using hst
  | b :: rest, vs, st, v, hst, hg => by
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    cases hg with
    | @cons _ vb _ vs' hb hr =>
      have hz' := hz.ext hst.ext
      have hm := modAdd_spec x z q k st.1 st.2 b hz' (by rw [bv_ext x hst.ext hz]; exact hz0)
        hst.valid hb.1 hst.length hb.2.1 hq hk.le (by rw [hst.value]; exact ZMod.val_lt _)
        (by rw [hb.2.2]; exact ZMod.val_lt _)
      have hacc : AccSpec (k := k) x p₀ z (modAdd z q k st.1 st.2 b) (v + vb) :=
        ⟨hst.ext.trans hm.ext, hm.valid, hm.length, by
          rw [hm.value, hst.value, hb.2.2, modAdd_val]; simp⟩
      have := foldl_modAdd_spec hk hz hz0 rest vs' _ _ hacc (LGood.ext (k := k) x hm.ext hr)
      rw [List.foldl_cons, List.sum_cons, ← add_assoc]
      exact this

theorem foldSum_spec (hk : q < 2 ^ k) {z : Wire ι} (p : SLP ι) (L : List (List (Wire ι)))
    (vs : List (ZMod q)) (hz : Valid p z) (hz0 : bv x p z = false)
    (hg : LGood (k := k) x p L vs) : AccSpec (k := k) x p z (foldSum z q k p L) vs.sum := by
  cases hg with
  | nil =>
    obtain ⟨hcv, hcl, hcn⟩ := constL_spec x p z hz hz0 k 0
    exact ⟨Ext.refl p, hcv, hcl, by simp [foldSum, hcn]⟩
  | @cons a va rest vs' ha hr =>
    have := foldl_modAdd_spec x hk hz hz0 rest vs' (p, a) va
      ⟨Ext.refl p, ha.1, ha.2.1, ha.2.2⟩ hr
    simpa [foldSum, List.sum_cons] using this

/-- The terms of a coefficient, each computed from `0`. -/
def leaves (z : Wire ι) (q k : ℕ) (repA repB : BI N k → Wire ι) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) :
    SLP ι → List ((Fin 2 × Fin k) × Fin N) → SLP ι × List (List (Wire ι))
  | p, [] => (p, [])
  | p, e :: es =>
    let r := termStep z q k repA repB a col t (p, constL z k 0) e
    let r' := leaves z q k repA repB a col t r.1 es
    (r'.1, r.2 :: r'.2)

theorem leaves_spec (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N) :
    ∀ (es : List ((Fin 2 × Fin k) × Fin N)) (p' : SLP ι), Ext p p' →
      Ext p' (leaves z q k repA repB a col t p' es).1 ∧
        LGood (k := k) x (leaves z q k repA repB a col t p' es).1
          (leaves z q k repA repB a col t p' es).2 (es.map (termZ Ψa Ψb a col t))
  | [], p', _ => ⟨Ext.refl p', List.Forall₂.nil⟩
  | e :: es, p', he => by
    have hz' := hz.ext he
    have hz0' : bv x p' z = false := by rw [bv_ext x he hz]; exact hz0
    obtain ⟨hcv, hcl, hcn⟩ := constL_spec x p' z hz' hz0' k 0
    have h0 : AccSpec (k := k) x p' z (p', constL z k 0) (0 : ZMod q) :=
      ⟨Ext.refl p', hcv, hcl, by simp [hcn]⟩
    have ht := termStep_spec x hk hz' hz0' (ha.ext x he) (hb.ext x he) a col t h0 e
    rw [zero_add] at ht
    have ih := leaves_spec hk hz hz0 ha hb a col t es _ (he.trans ht.ext)
    refine ⟨ht.ext.trans ih.1, List.Forall₂.cons ?_ ih.2⟩
    exact ⟨ht.valid.ext ih.1, ht.length, (nv_ext x ih.1 ht.valid).trans ht.value⟩

/-- The number of rounds: enough to bring `2 |W| N + 1` numbers to one. -/
def treeHeight (N k : ℕ) : ℕ := Nat.clog 2 (Fintype.card ((Fin 2 × Fin k) × Fin N) + 1)

/-- One output coefficient of a NAND: the gadget's coefficient `Gv` and the `2 |W| N` terms,
summed by a balanced tree of modular additions (`treeHeight` rounds). -/
noncomputable def coefCircuit (z : Wire ι) (q k : ℕ) (repA repB : BI N k → Wire ι) (Gv : ℕ) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (p : SLP ι) : SLP ι × List (Wire ι) :=
  let r := leaves z q k repA repB a col t p ((Finset.univ : Finset ((Fin 2 × Fin k) × Fin N)).toList)
  let r' := rounds z q k (treeHeight N k) r.1 (constL z k Gv :: r.2)
  foldSum z q k r'.1 r'.2

/-- **One output coefficient of a NAND** is computed. -/
theorem coefCircuit_spec (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N) :
    AccSpec (k := k) x p z
      (coefCircuit z q k repA repB (((gswBin hk).G a col).coeffs t).val a col t p)
      ((((gswBin hk).G - Ψa * (gswBin hk).ginv Ψb : Matrix (Fin 2) (Fin 2 × Fin k)
        (Negacyclic (ZMod q) N)) a col).coeffs t) := by
  set es := (Finset.univ : Finset ((Fin 2 × Fin k) × Fin N)).toList
  set Gv := (((gswBin hk).G a col).coeffs t).val
  obtain ⟨e₁, g₁⟩ := leaves_spec x hk hz hz0 ha hb a col t es p (Ext.refl p)
  set r := leaves z q k repA repB a col t p es
  have hz₁ := hz.ext e₁
  have hz0₁ : bv x r.1 z = false := by rw [bv_ext x e₁ hz]; exact hz0
  obtain ⟨hcv, hcl, hcn⟩ := constL_spec x r.1 z hz₁ hz0₁ k Gv
  have g₁' : LGood (k := k) x r.1 (constL z k Gv :: r.2)
      ((((gswBin hk).G a col).coeffs t) :: es.map (termZ Ψa Ψb a col t)) :=
    List.Forall₂.cons ⟨hcv, hcl, by rw [hcn, Nat.mod_eq_of_lt ((ZMod.val_lt _).trans hk)]⟩ g₁
  obtain ⟨e₂, vs', hs, g₂⟩ := rounds_spec x hk (treeHeight N k) r.1 _ _ hz₁ hz0₁ g₁'
  have hz₂ := hz₁.ext e₂
  have hf := foldSum_spec x hk _ _ vs' hz₂ (by rw [bv_ext x e₂ hz₁]; exact hz0₁) g₂
  have hval : vs'.sum = (((gswBin hk).G - Ψa * (gswBin hk).ginv Ψb : Matrix (Fin 2) (Fin 2 × Fin k)
      (Negacyclic (ZMod q) N)) a col).coeffs t := by
    rw [hs, List.sum_cons, Finset.sum_map_toList, coeff_gswNand hk Ψa Ψb a col t]
    rfl
  rw [hval] at hf
  exact ⟨e₁.trans (e₂.trans hf.ext), hf.valid, hf.length, hf.value⟩

/-! ### A NAND on represented ciphertexts -/

/-- The output positions: row, column, coefficient. -/
abbrev OI (N k : ℕ) := Fin 2 × (Fin 2 × Fin k) × Fin N

/-- The step of the NAND block: compute one output coefficient. -/
noncomputable def blockStep (z : Wire ι) (q k : ℕ) [NeZero q] (hk : q < 2 ^ k) (repA repB : BI N k → Wire ι)
    (st : SLP ι × (OI N k → List (Wire ι))) (o : OI N k) : SLP ι × (OI N k → List (Wire ι)) :=
  let c := coefCircuit z q k repA repB (((gswBin (N := N) hk).G o.1 o.2.1).coeffs o.2.2).val o.1 o.2.1
    o.2.2 st.1
  (c.1, Function.update st.2 o c.2)

/-- **The Ring-GSW NAND** `G − Ψ_a G⁻¹(Ψ_b)` on represented ciphertexts. -/
noncomputable def nandBlock (z : Wire ι) (q k : ℕ) [NeZero q] (hk : q < 2 ^ k) (repA repB : BI N k → Wire ι) (p : SLP ι) :
    SLP ι × (BI N k → Wire ι) :=
  let r := ((Finset.univ : Finset (OI N k)).toList).foldl (blockStep z q k hk repA repB) (p, fun _ => [])
  (r.1, fun b => (r.2 (b.1, b.2.1, b.2.2.2)).getD b.2.2.1 .one)

/-- A computed coefficient. -/
def Good (p : SLP ι) (ws : List (Wire ι)) (v : ZMod q) : Prop :=
  AllValid p ws ∧ ws.length = k ∧ nv x p ws = v.val

omit [NeZero q] in
theorem Good.ext {p p' : SLP ι} (h : Ext p p') {ws : List (Wire ι)} {v : ZMod q}
    (hg : Good (k := k) x p ws v) : Good (k := k) x p' ws v :=
  ⟨hg.1.ext h, hg.2.1, by rw [nv_ext x h hg.1]; exact hg.2.2⟩

theorem foldl_blockStep_spec (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) (P : OI N k → Prop) :
    ∀ (outs : List (OI N k)) (st : SLP ι × (OI N k → List (Wire ι))),
      Ext p st.1 → (∀ o, P o → Good (k := k) x st.1 (st.2 o)
        ((((gswBin hk).G - Ψa * (gswBin hk).ginv Ψb : Matrix (Fin 2) (Fin 2 × Fin k)
          (Negacyclic (ZMod q) N)) o.1 o.2.1).coeffs o.2.2)) →
      let st' := outs.foldl (blockStep z q k hk repA repB) st
      Ext p st'.1 ∧ ∀ o, (P o ∨ o ∈ outs) → Good (k := k) x st'.1 (st'.2 o)
        ((((gswBin hk).G - Ψa * (gswBin hk).ginv Ψb : Matrix (Fin 2) (Fin 2 × Fin k)
          (Negacyclic (ZMod q) N)) o.1 o.2.1).coeffs o.2.2)
  | [], st, he, hg => ⟨he, fun o ho => hg o (by simpa using ho)⟩
  | o₀ :: os, st, he, hg => by
    have hc := coefCircuit_spec x hk (hz.ext he) (by rw [bv_ext x he hz]; exact hz0) (ha.ext x he)
      (hb.ext x he) o₀.1 o₀.2.1 o₀.2.2
    have he' : Ext p (blockStep z q k hk repA repB st o₀).1 := he.trans hc.ext
    have hg' : ∀ o, (P o ∨ o = o₀) → Good (k := k) x (blockStep z q k hk repA repB st o₀).1
        ((blockStep z q k hk repA repB st o₀).2 o)
        ((((gswBin hk).G - Ψa * (gswBin hk).ginv Ψb : Matrix (Fin 2) (Fin 2 × Fin k)
          (Negacyclic (ZMod q) N)) o.1 o.2.1).coeffs o.2.2) := by
      intro o ho
      by_cases hoo : o = o₀
      · subst hoo
        simp only [blockStep, Function.update_self]
        exact ⟨hc.valid, hc.length, hc.value⟩
      · simp only [blockStep, Function.update_of_ne hoo]
        exact (hg o (ho.resolve_right hoo)).ext x hc.ext
    have ih := foldl_blockStep_spec hk hz hz0 ha hb (fun o => P o ∨ o = o₀) os _ he' hg'
    simp only [List.foldl_cons]
    refine ⟨ih.1, fun o ho => ih.2 o ?_⟩
    rcases ho with ho | ho
    · exact Or.inl (Or.inl ho)
    · rcases List.mem_cons.mp ho with rfl | ho
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr ho

/-- **The NAND block represents the Ring-GSW NAND.** -/
theorem nandBlock_spec (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) {repA repB : BI N k → Wire ι}
    {Ψa Ψb : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)}
    (ha : Rep x p repA Ψa) (hb : Rep x p repB Ψb) :
    Ext p (nandBlock z q k hk repA repB p).1 ∧
      Rep x (nandBlock z q k hk repA repB p).1 (nandBlock z q k hk repA repB p).2
        ((gswBin hk).G - Ψa * (gswBin hk).ginv Ψb) := by
  obtain ⟨he, hg⟩ := foldl_blockStep_spec x hk hz hz0 ha hb (fun _ => False)
    ((Finset.univ : Finset (OI N k)).toList) (p, fun _ => []) (Ext.refl p) (fun _ h => h.elim)
  refine ⟨he, ?_, ?_⟩
  · simp only [nandBlock]
    intro b
    obtain ⟨hv, hl, -⟩ := hg (b.1, b.2.1, b.2.2.2) (Or.inr (Finset.mem_toList.mpr (Finset.mem_univ _)))
    show Valid _ (List.getD _ _ _)
    by_cases hi : b.2.2.1.val < (((Finset.univ : Finset (OI N k)).toList.foldl
        (blockStep z q k hk repA repB) (p, fun _ => [])).2 (b.1, b.2.1, b.2.2.2)).length
    · rw [List.getD_eq_getElem _ _ hi]; exact hv _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; trivial
  · simp only [nandBlock]
    intro a c i j
    obtain ⟨-, hl, hn⟩ := hg (a, c, j) (Or.inr (Finset.mem_toList.mpr (Finset.mem_univ _)))
    show bv x _ (List.getD _ _ _) = _
    rw [bv_getD_of_nv x _ _ _ (by rw [hl]; exact i.isLt), hn]

/-! ### Compiling a circuit -/

/-- The wires of a constant ciphertext. -/
def constRep (z : Wire ι) (k : ℕ) (Ψ : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)) :
    BI N k → Wire ι :=
  fun b => (constL z k ((Ψ b.1 b.2.1).coeffs b.2.2.2).val).getD b.2.2.1 .one

theorem constRep_spec (hk : q < 2 ^ k) {p : SLP ι} {z : Wire ι} (hz : Valid p z)
    (hz0 : bv x p z = false) (Ψ : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N)) :
    Rep x p (constRep z k Ψ) Ψ := by
  refine ⟨fun b => ?_, fun a c i j => ?_⟩
  · obtain ⟨hv, hl, -⟩ := constL_spec x p z hz hz0 k ((Ψ b.1 b.2.1).coeffs b.2.2.2).val
    show Valid p (List.getD _ _ _)
    by_cases hi : b.2.2.1.val < (constL z k ((Ψ b.1 b.2.1).coeffs b.2.2.2).val).length
    · rw [List.getD_eq_getElem _ _ hi]; exact hv _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; trivial
  · obtain ⟨-, hl, hn⟩ := constL_spec x p z hz hz0 k ((Ψ a c).coeffs j).val
    show bv x p (List.getD _ _ _) = _
    rw [bv_getD_of_nv x p _ _ (by rw [hl]; exact i.isLt), hn,
      Nat.mod_eq_of_lt ((ZMod.val_lt _).trans hk)]

/-- **Compile a circuit** into the Boolean program of its Ring-GSW evaluation: the program and the
wires of the evaluated ciphertext. The inputs are the bits of the input ciphertexts. -/
noncomputable def compileGSW {A : Type*} (z : Wire (A × BI N k)) (hk : q < 2 ^ k) :
    Circuit A → SLP (A × BI N k) → SLP (A × BI N k) × (BI N k → Wire (A × BI N k))
  | .input i, p => (p, fun b => .input (i, b))
  | .one, p => (p, constRep z k (gswBin (N := N) hk).G)
  | .nand f g, p =>
    let r₁ := compileGSW z hk f p
    let r₂ := compileGSW z hk g r₁.1
    nandBlock z q k hk r₁.2 r₂.2 r₂.1

/-- **The compiled program represents the Ring-GSW evaluation.** -/
theorem compileGSW_spec {A : Type*} (hk : q < 2 ^ k) (x : A × BI N k → Bool)
    (Ψ : A → Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))
    (hx : ∀ i a c b j, x (i, a, c, b, j) = ((Ψ i a c).coeffs j).val.testBit b)
    {z : Wire (A × BI N k)} :
    ∀ (f : Circuit A) (p : SLP (A × BI N k)), Valid p z → bv x p z = false →
      Ext p (compileGSW z hk f p).1 ∧
        Rep x (compileGSW z hk f p).1 (compileGSW z hk f p).2 (evalMat (gswBin hk) Ψ f)
  | .input i, p, _, _ => ⟨Ext.refl p, fun _ => trivial, fun a c b j => hx i a c b j⟩
  | .one, p, hz, hz0 => ⟨Ext.refl p, constRep_spec x hk hz hz0 _⟩
  | .nand f g, p, hz, hz0 => by
    obtain ⟨e₁, r₁⟩ := compileGSW_spec hk x Ψ hx f p hz hz0
    have hz₁ := hz.ext e₁
    have hz0₁ : bv x (compileGSW z hk f p).1 z = false := by rw [bv_ext x e₁ hz]; exact hz0
    obtain ⟨e₂, r₂⟩ := compileGSW_spec hk x Ψ hx g _ hz₁ hz0₁
    have hz₂ := hz₁.ext e₂
    have hz0₂ : bv x (compileGSW z hk g (compileGSW z hk f p).1).1 z = false := by
      rw [bv_ext x e₂ hz₁]; exact hz0₁
    obtain ⟨e₃, r₃⟩ := nandBlock_spec x hk hz₂ hz0₂ (r₁.ext x e₂) r₂
    exact ⟨e₁.trans (e₂.trans e₃), r₃⟩

/-- The program of `f̂`: a gate computing `0`, then the compiled evaluation. -/
noncomputable def fhatProgram {A : Type*} (hk : q < 2 ^ k) (f : Circuit A) :
    SLP (A × BI N k) × (BI N k → Wire (A × BI N k)) :=
  compileGSW (.gate 0) hk f [⟨.one, .one⟩]

/-- **`f̂` computes the bits of the Ring-GSW evaluation.** -/
theorem fhatProgram_spec {A : Type*} (hk : q < 2 ^ k) (x : A × BI N k → Bool)
    (Ψ : A → Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))
    (hx : ∀ i a c b j, x (i, a, c, b, j) = ((Ψ i a c).coeffs j).val.testBit b) (f : Circuit A)
    (a : Fin 2) (c : Fin 2 × Fin k) (b : Fin k) (j : Fin N) :
    bv x (fhatProgram (N := N) hk f).1 ((fhatProgram (N := N) hk f).2 (a, c, b, j)) =
      ((evalMat (gswBin hk) Ψ f a c).coeffs j).val.testBit b := by
  have h0 : bv x [⟨.one, .one⟩] (Wire.gate 0 : Wire (A × BI N k)) = false := by
    have := bv_addNand x ([] : SLP (A × BI N k)) .one .one trivial trivial
    simpa [addNand, bv, evalBool, valueOf, wireVal] using this
  exact (compileGSW_spec hk x Ψ hx f [⟨.one, .one⟩] (by simp [Valid]) h0).2.2 a c b j

/-! ### Compiling a straight-line program -/

/-- The wires of the ciphertext on a wire of the source program, from the wires of its gates
computed so far (`reps`); a gate not yet computed reads the ciphertext of `1`, as in `SLP.run`. -/
noncomputable def repOf {A : Type*} (z : Wire (A × BI N k)) (hk : q < 2 ^ k)
    (reps : List (BI N k → Wire (A × BI N k))) : Wire A → BI N k → Wire (A × BI N k)
  | .input i => fun b => .input (i, b)
  | .one => constRep z k (gswBin (N := N) hk).G
  | .gate m => reps.getD m (constRep z k (gswBin (N := N) hk).G)

/-- One gate of the source program: its NAND block. -/
noncomputable def compileStep {A : Type*} (z : Wire (A × BI N k)) (hk : q < 2 ^ k)
    (st : SLP (A × BI N k) × List (BI N k → Wire (A × BI N k))) (g : Gate A) :
    SLP (A × BI N k) × List (BI N k → Wire (A × BI N k)) :=
  let r := nandBlock z q k hk (repOf z hk st.2 g.a) (repOf z hk st.2 g.b) st.1
  (r.1, st.2 ++ [r.2])

/-- **Compile a straight-line program** gate by gate (each gate once) after `prog`: the program
and the wires of the ciphertext on `w`. -/
noncomputable def compileSLP {A : Type*} (z : Wire (A × BI N k)) (hk : q < 2 ^ k) (p : SLP A)
    (w : Wire A) (prog : SLP (A × BI N k)) : SLP (A × BI N k) × (BI N k → Wire (A × BI N k)) :=
  let st := p.foldl (compileStep z hk) (prog, [])
  (st.1, repOf z hk st.2 w)

section CompileSLP

variable {A : Type*} (hk : q < 2 ^ k) (x : A × BI N k → Bool)
  (Ψ : A → Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))

/-- The Ring-GSW NAND. -/
noncomputable abbrev gswStep (hk : q < 2 ^ k) (a b : Matrix (Fin 2) (Fin 2 × Fin k)
    (Negacyclic (ZMod q) N)) : Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N) :=
  (gswBin hk).G - a * (gswBin hk).ginv b

/-- The wires `reps` represent the ciphertexts `vals` of the gates computed so far. -/
def RepsInv (prog : SLP (A × BI N k)) (reps : List (BI N k → Wire (A × BI N k)))
    (vals : List (Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))) : Prop :=
  reps.length = vals.length ∧ ∀ m (h : m < reps.length) (h' : m < vals.length),
    Rep x prog reps[m] vals[m]

omit [NeZero q] in
theorem RepsInv.ext {prog prog' : SLP (A × BI N k)} (he : Ext prog prog')
    {reps : List (BI N k → Wire (A × BI N k))}
    {vals : List (Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))}
    (h : RepsInv x prog reps vals) : RepsInv x prog' reps vals :=
  ⟨h.1, fun m hm hm' => (h.2 m hm hm').ext x he⟩

theorem repOf_spec (hx : ∀ i a c b j, x (i, a, c, b, j) = ((Ψ i a c).coeffs j).val.testBit b)
    {prog : SLP (A × BI N k)} {z : Wire (A × BI N k)} (hz : Valid prog z)
    (hz0 : bv x prog z = false) {reps : List (BI N k → Wire (A × BI N k))}
    {vals : List (Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))}
    (h : RepsInv x prog reps vals) (w : Wire A) :
    Rep x prog (repOf z hk reps w) (SLP.wireVal Ψ (gswBin hk).G vals w) := by
  cases w with
  | input i => exact ⟨fun _ => trivial, fun a c b j => hx i a c b j⟩
  | one => exact constRep_spec x hk hz hz0 _
  | gate m =>
    simp only [repOf, SLP.wireVal]
    by_cases hm : m < reps.length
    · rw [List.getD_eq_getElem _ _ hm, List.getD_eq_getElem _ _ (h.1 ▸ hm)]
      exact h.2 m hm (h.1 ▸ hm)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hm),
        List.getD_eq_default _ _ (h.1 ▸ Nat.le_of_not_lt hm)]
      exact constRep_spec x hk hz hz0 _

theorem foldl_compileStep_spec
    (hx : ∀ i a c b j, x (i, a, c, b, j) = ((Ψ i a c).coeffs j).val.testBit b)
    {z : Wire (A × BI N k)} :
    ∀ (p : SLP A) (prog : SLP (A × BI N k)) (reps : List (BI N k → Wire (A × BI N k)))
      (vals : List (Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))),
      Valid prog z → bv x prog z = false → RepsInv x prog reps vals →
      Ext prog (p.foldl (compileStep z hk) (prog, reps)).1 ∧
        RepsInv x (p.foldl (compileStep z hk) (prog, reps)).1
          (p.foldl (compileStep z hk) (prog, reps)).2 (SLP.run Ψ (gswBin hk).G (gswStep hk) p vals)
  | [], prog, reps, vals, _, _, h => ⟨Ext.refl prog, h⟩
  | g :: p, prog, reps, vals, hz, hz0, h => by
    have ha := repOf_spec hk x Ψ hx hz hz0 h g.a
    have hb := repOf_spec hk x Ψ hx hz hz0 h g.b
    obtain ⟨e₁, r₁⟩ := nandBlock_spec x hk hz hz0 ha hb
    have hz₁ := hz.ext e₁
    have hz0₁ : bv x (nandBlock z q k hk (repOf z hk reps g.a) (repOf z hk reps g.b) prog).1 z =
        false := by rw [bv_ext x e₁ hz]; exact hz0
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
    obtain ⟨e₂, r₂⟩ := foldl_compileStep_spec hx p _ _ _ hz₁ hz0₁ h₁
    exact ⟨e₁.trans e₂, r₂⟩

/-- **The compiled program represents the Ring-GSW evaluation along the source program.** -/
theorem compileSLP_spec
    (hx : ∀ i a c b j, x (i, a, c, b, j) = ((Ψ i a c).coeffs j).val.testBit b)
    {z : Wire (A × BI N k)} (p : SLP A) (w : Wire A) (prog : SLP (A × BI N k))
    (hz : Valid prog z) (hz0 : bv x prog z = false) :
    Ext prog (compileSLP z hk p w prog).1 ∧
      Rep x (compileSLP z hk p w prog).1 (compileSLP z hk p w prog).2
        (SLP.valueOf Ψ (gswBin hk).G (gswStep hk) p w) := by
  obtain ⟨e, r⟩ := foldl_compileStep_spec hk x Ψ hx p prog [] [] hz hz0 ⟨rfl, fun _ h => absurd h (by simp)⟩
  exact ⟨e, repOf_spec hk x Ψ hx (hz.ext e) (by rw [bv_ext x e hz]; exact hz0) r w⟩

end CompileSLP

/-- The program of `f̂` for a wire `w` of a straight-line program: a gate computing `0`, then the
compiled evaluation. -/
noncomputable def fhatSLP {A : Type*} (hk : q < 2 ^ k) (p : SLP A) (w : Wire A) :
    SLP (A × BI N k) × (BI N k → Wire (A × BI N k)) :=
  compileSLP (.gate 0) hk p w [⟨.one, .one⟩]

/-- **`f̂` of a straight-line program computes the bits of its Ring-GSW evaluation.** -/
theorem fhatSLP_spec {A : Type*} (hk : q < 2 ^ k) (x : A × BI N k → Bool)
    (Ψ : A → Matrix (Fin 2) (Fin 2 × Fin k) (Negacyclic (ZMod q) N))
    (hx : ∀ i a c b j, x (i, a, c, b, j) = ((Ψ i a c).coeffs j).val.testBit b) (p : SLP A)
    (w : Wire A) (a : Fin 2) (c : Fin 2 × Fin k) (b : Fin k) (j : Fin N) :
    bv x (fhatSLP (N := N) hk p w).1 ((fhatSLP (N := N) hk p w).2 (a, c, b, j)) =
      ((SLP.valueOf Ψ (gswBin hk).G (gswStep hk) p w a c).coeffs j).val.testBit b := by
  have h0 : bv x [⟨.one, .one⟩] (Wire.gate 0 : Wire (A × BI N k)) = false := by
    have := bv_addNand x ([] : SLP (A × BI N k)) .one .one trivial trivial
    simpa [addNand, bv, evalBool, valueOf, wireVal] using this
  exact (compileSLP_spec hk x Ψ hx p w [⟨.one, .one⟩] (by simp [Valid]) h0).2.2 a c b j

end SigabaNeo.Lattices
