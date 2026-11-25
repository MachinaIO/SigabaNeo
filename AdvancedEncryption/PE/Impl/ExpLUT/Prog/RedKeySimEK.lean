import PE.Impl.ExpLUT.Prog.RedKeySimT

/-!
# `KGsim` on the VM (module 6b, part 1): slab kernels (generic VM)

Module 6b evaluates `R̂_F` slab by slab (`RedKeySimSlab.slab_simKey`). A slab is a list of `n`
rows of `2K` ring words (`seRows`, row-major). The slab operations of Corollary 1's propagation
are built from the following kernels (all generic over `N K`):

* `seAutC`: `σ_g^m` on every entry (`m = |rP|` passes, `g = |rKc|`) — **`exec_seAutC`**;
* `seRotC`: rotate the rows left by `|seC|` (`List.rotate`) — **`exec_seRotC`**;
* `seMapC`: every row `v ↦ v · G⁻¹(Y)` (`seGRow`, via `ginvMulC` on `[v; v]`) — **`exec_seMapC`**;
* `seAddHC`: the head row `+= v` and moved to the back — **`exec_seAddHC`**, hence `seAdd0C`
  (row `0 += v`) and `seAddTC` (row `p += v`, `p = |rPw2|`) — **`exec_seAdd0C`**,
  **`exec_seAddTC`** (`List.modify`);
* `seScaleC`: a row times a ring element (`seRowSmul`) — **`exec_seScaleC`**;
* `seSumC`: the entrywise sum of two slabs — **`exec_seSumC`**.

Registers (library scratch, never used by `ginvMulC`/`aStep` for these: `29`, `41`, `42`, `46`):
`seQ = 41` the slab queue, `seO = 42` the output queue / vector, `seC = 46` the row counter,
`seY = 29` the matrix `Y`; scratch `seR = 47`, `seV = 48`, `seE = 45`, `rX0`, `rX1`; caller's
`seMu = 2` (a scalar), `seAcc = 17` (an accumulator), `rTW = 22` (unary `n`), `rPw2 = 15`.
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-! ### Registers -/

/-- The slab queue. -/
@[simp, vmreg] abbrev seQ : Fin 64 := 41
/-- The output queue (or a vector). -/
@[simp, vmreg] abbrev seO : Fin 64 := 42
/-- The row counter. -/
@[simp, vmreg] abbrev seC : Fin 64 := 46
/-- The matrix `Y` of a row map. -/
@[simp, vmreg] abbrev seY : Fin 64 := 29
/-- A row temporary. -/
@[simp, vmreg] abbrev seR : Fin 64 := 47
/-- A vector temporary. -/
@[simp, vmreg] abbrev seV : Fin 64 := 48
/-- The entry counter. -/
@[simp, vmreg] abbrev seE : Fin 64 := 45
/-- A scalar (caller). -/
@[simp, vmreg] abbrev seMu : Fin 64 := 2
/-- An accumulator (caller). -/
@[simp, vmreg] abbrev seAcc : Fin 64 := 17

variable {N K : ℕ}

/-! ### Rows and slabs -/

/-- The words of a list of rows, row-major. -/
def seRows (L : List (Fin 2 × Fin K → Rq N K)) : List (Rq N K) := L.flatMap vecL

@[simp] theorem seRows_nil : seRows ([] : List (Fin 2 × Fin K → Rq N K)) = [] := rfl

@[simp] theorem seRows_cons (v : Fin 2 × Fin K → Rq N K) (L : List (Fin 2 × Fin K → Rq N K)) :
    seRows (v :: L) = vecL v ++ seRows L := rfl

@[simp] theorem seRows_append (L L' : List (Fin 2 × Fin K → Rq N K)) :
    seRows (L ++ L') = seRows L ++ seRows L' := by simp [seRows]

@[simp] theorem length_seRows (L : List (Fin 2 × Fin K → Rq N K)) :
    (seRows L).length = L.length * (2 * K) := by
  induction L with
  | nil => simp
  | cons v L ih => simp [ih]; ring

/-- The sum of two rows. -/
def seRowAdd (u v : Fin 2 × Fin K → Rq N K) : Fin 2 × Fin K → Rq N K := fun c => u c + v c

/-- A row times a scalar. -/
def seRowSmul (μ : Rq N K) (v : Fin 2 × Fin K → Rq N K) : Fin 2 × Fin K → Rq N K :=
  fun c => μ * v c

/-- `σ_g^m` on a row. -/
def seRowAut (g m : ℕ) (v : Fin 2 × Fin K → Rq N K) : Fin 2 × Fin K → Rq N K :=
  fun c => (aut N g)^[m] (v c)

/-- **`v · G⁻¹(Y)`** for a row `v` (binary digits). -/
def seGRow (v : Fin 2 × Fin K → Rq N K) (Y : Fin 2 → Fin 2 × Fin K → Rq N K) :
    Fin 2 × Fin K → Rq N K :=
  ginvMulm (fun _ => v) Y 0

theorem vecL_seRowAdd (u v : Fin 2 × Fin K → Rq N K) :
    vecL (seRowAdd u v) = List.zipWith (· + ·) (vecL u) (vecL v) := by
  simp only [vecL]; rw [List.zipWith_map, List.zipWith_self]; rfl

theorem vecL_seRowSmul (μ : Rq N K) (v : Fin 2 × Fin K → Rq N K) :
    vecL (seRowSmul μ v) = (vecL v).map (μ * ·) := by
  simp only [vecL, seRowSmul, List.map_map]; rfl

theorem seRows_zipWith : ∀ (L M : List (Fin 2 × Fin K → Rq N K)), L.length = M.length →
    seRows (List.zipWith seRowAdd L M) = List.zipWith (· + ·) (seRows L) (seRows M)
  | [], [], _ => rfl
  | u :: L, v :: M, h => by
    simp only [List.zipWith_cons_cons, seRows_cons, vecL_seRowAdd]
    rw [List.zipWith_append (by simp), seRows_zipWith L M (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem seRows_map_aut (g m : ℕ) (L : List (Fin 2 × Fin K → Rq N K)) :
    seRows (L.map (seRowAut g m)) = (seRows L).map ((aut N g)^[m]) := by
  induction L with
  | nil => rfl
  | cons v L ih => simp [ih, vecL, seRowAut]

/-! ### An entry loop: `d ++= σ_g(x)` for every entry `x` popped from `seQ` -/

/-- One entry of `seAutC`: pop, `σ_g`, push to the back. -/
def seAutE : Code :=
  .seq (.cp rX0 rZ) <| .seq (.mvR rX0 seQ) <| .seq (.op .aut rX0 rX0 rKc) (.app seQ rX0)

/-- The counter of the entries: `|rTW| · 2K`. -/
def seCntC : Code := .seq (.clr seC) <| .seq (.cp seE rTW) (.rep seE (.app seC rT2K))

theorem seAutE_writes_seC : seAutE.writes seC = false := by decide

theorem exec_seCntC (w : St) (n : ℕ) (hW : (w rTW).length = n)
    (h2 : w rT2K = List.replicate (2 * K) false) :
    (exec N K seCntC w seC).length = n * (2 * K) := by
  unfold seCntC
  simp only [exec_seq]
  have key := exec_rep_inv (N := N) (K := K) seE (.app seC rT2K) (by decide)
    (fun m w' => (w' seC).length = m * (2 * K) ∧ w' rT2K = List.replicate (2 * K) false)
    (exec N K (.cp seE rTW) (exec N K (.clr seC) w))
    ⟨by vm_simp; simp, by vm_simp; simp [h2]⟩ ?_
  · have hl : ((exec N K (.cp seE rTW) (exec N K (.clr seC) w)) seE).length = n := by
      vm_simp; simp [hW]
    rw [hl] at key
    exact key.1
  · intro m w' _ hP _
    obtain ⟨p1, p2⟩ := hP
    vm_simp
    refine ⟨?_, ?_⟩
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, List.length_append, p1, p2,
        List.length_replicate]
      ring
    · simp [Function.update_apply, p2]

theorem exec_seAutLoop (hN : 0 < N) (hK : 0 < K) (w : St) (l : List (Rq N K)) (E : ℕ)
    (hE : E ≤ l.length) (hQ : w seQ = encL N K l) (hC : (w seC).length = E)
    (hk : 0 < (w rKc).length) (hZ : w rZ = encRM N K 0) :
    exec N K (.rep seC seAutE) w seQ =
      encL N K (l.drop E ++ (l.take E).map (aut N (w rKc).length)) := by
  have key := exec_rep_inv2 (N := N) (K := K) seC seAutE seAutE_writes_seC
    (fun m w' => w' seQ = encL N K (l.drop m ++ (l.take m).map (aut N (w rKc).length))) w
    (by simp [hQ]) ?_
  · rw [hC] at key
    exact key
  · intro m w' hm hP _ hfr
    rw [hC] at hm
    have hZ' : w' rZ = encRM N K 0 := by rw [hfr _ (by decide) (by decide), hZ]
    have hk' : w' rKc = w rKc := hfr _ (by decide) (by decide)
    have e1 := drop_cons_getElem l (show m < l.length by omega)
    have t1 := take_succ_getElem l (show m < l.length by omega)
    rw [e1, List.cons_append, encL_cons] at hP
    unfold seAutE
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hP, hZ', hk', shiftIn_encRM',
      takeD_encRM_append, takeD_encRM, canonW_aut hK hN hk, t1, List.map_append, encL_append,
      List.map_cons, List.map_nil, encL_cons, List.append_assoc, drop_encRM_append, encL_nil,
      List.append_nil]

/-- One pass of `σ_g` over the slab. -/
def seAutPass : Code := .seq seCntC (.rep seC seAutE)

/-- **`σ_g^m` on every entry of the slab** (`m = |rP|`). -/
def seAutC : Code := .rep rP seAutPass

theorem seAutPass_writes_rP : seAutPass.writes rP = false := by decide

theorem exec_seAutPass (hN : 0 < N) (hK : 0 < K) (w : St) (L : List (Fin 2 × Fin K → Rq N K))
    (hL : (w rTW).length = L.length) (hQ : w seQ = encL N K (seRows L))
    (hk : 0 < (w rKc).length) (hT : MulTmpl N K w) :
    exec N K seAutPass w seQ = encL N K (seRows (L.map (seRowAut (w rKc).length 1))) := by
  unfold seAutPass
  rw [exec_seq]
  have hc := exec_seCntC (N := N) (K := K) w L.length hL hT.t2K
  set w1 := exec N K seCntC w with hw1
  have f1 : ∀ r : Fin 64, r ≠ seC → r ≠ seE → w1 r = w r := fun r h1 h2 =>
    exec_writes _ _ _ (by unfold seCntC; simp [Code.writes, Ne.symm h1, Ne.symm h2])
  have := exec_seAutLoop hN hK w1 (seRows L) (L.length * (2 * K)) (by simp)
    (by rw [f1 _ (by decide) (by decide), hQ]) hc
    (by rw [f1 _ (by decide) (by decide)]; exact hk) (by rw [f1 _ (by decide) (by decide), hT.z])
  rw [f1 _ (by decide) (by decide)] at this
  rw [this, List.drop_of_length_le (by simp), List.take_of_length_le (by simp), List.nil_append,
    ← Function.iterate_one (aut N (w rKc).length), ← seRows_map_aut]

theorem seRowAut_succ (g m : ℕ) (v : Fin 2 × Fin K → Rq N K) :
    seRowAut g 1 (seRowAut g m v) = seRowAut g (m + 1) v := by
  funext c
  show (aut N g)^[1] _ = _
  rw [Function.iterate_one]
  simp only [seRowAut]
  rw [Function.iterate_succ_apply']

theorem seAutPass_writes : ∀ r : Fin 64, seAutPass.writes r = true → r ∈ [seC, seE, rX0, seQ] := by
  decide

/-- **`σ_g^m` on every entry** (`m = |rP|`, `g = |rKc|`). -/
theorem exec_seAutC (hN : 0 < N) (hK : 0 < K) (w : St) (L : List (Fin 2 × Fin K → Rq N K))
    (hL : (w rTW).length = L.length) (hQ : w seQ = encL N K (seRows L))
    (hk : 0 < (w rKc).length) (hT : MulTmpl N K w) :
    exec N K seAutC w seQ = encL N K (seRows (L.map (seRowAut (w rKc).length (w rP).length))) := by
  have key := exec_rep_inv2 (N := N) (K := K) rP seAutPass seAutPass_writes_rP
    (fun m w' => w' seQ = encL N K (seRows (L.map (seRowAut (w rKc).length m)))) w
    (by rw [hQ]; congr 2; exact (List.map_id L).symm) ?_
  · exact key
  · intro m w' _ hP _ hfr
    have fr : ∀ r : Fin 64, r ∉ [seC, seE, rX0, seQ] → r ≠ rP →
        Function.update w' rP (w' rP).tail r = w r := fun r h1 h2 => by
      rw [Function.update_of_ne h2]
      exact hfr r (by cases h : seAutPass.writes r; rfl; exact absurd (seAutPass_writes r h) h1) h2
    have := exec_seAutPass hN hK (Function.update w' rP (w' rP).tail) (L.map (seRowAut (w rKc).length m))
      (by rw [fr _ (by decide) (by decide), hL, List.length_map])
      (by rw [Function.update_of_ne (by decide), hP])
      (by rw [fr _ (by decide) (by decide)]; exact hk)
      (hT.of_writes fun r hr => fr r (by revert r; decide) (by intro e; subst e; simp at hr))
    rw [this, fr _ (by decide) (by decide), List.map_map]
    congr 3
    funext v
    exact seRowAut_succ _ _ _

/-- The frame of a code from a list of the registers it may write. -/
theorem se_exec_frame (c : Code) (l : List (Fin 64)) (hc : ∀ r : Fin 64, c.writes r = true → r ∈ l)
    (w : St) (r : Fin 64) (hr : r ∉ l) : exec N K c w r = w r :=
  exec_writes _ _ _ (by cases e : c.writes r; rfl; exact absurd (hc r e) hr)

/-! ### Rotating the rows -/

/-- One row: from the front to the back. -/
def seRotBody : Code := .seq (.cp seR rT2KNK) <| .seq (.mv seR seQ rT2KNK) (.app seQ seR)

/-- **Rotate the rows left by `|seC|`.** -/
def seRotC : Code := .rep seC seRotBody

theorem seRotBody_writes_seC : seRotBody.writes seC = false := by decide

theorem seRotC_writes : ∀ r : Fin 64, seRotC.writes r = true → r ∈ [seC, seR, seQ] := by decide

theorem exec_seRotC (w : St) (L : List (Fin 2 × Fin K → Rq N K)) (k : ℕ) (hk : k ≤ L.length)
    (hQ : w seQ = encL N K (seRows L)) (hC : (w seC).length = k)
    (hT2 : w rT2KNK = encL N K (List.replicate (2 * K) 0)) :
    exec N K seRotC w seQ = encL N K (seRows (L.rotate k)) := by
  rw [List.rotate_eq_drop_append_take hk]
  have key := exec_rep_inv2 (N := N) (K := K) seC seRotBody seRotBody_writes_seC
    (fun m w' => w' seQ = encL N K (seRows (L.drop m ++ L.take m))) w (by simp [hQ]) ?_
  · rw [hC] at key; exact key
  · intro m w' hm hP _ hfr
    rw [hC] at hm
    have hT' : w' rT2KNK = encL N K (List.replicate (2 * K) 0) := by
      rw [hfr _ (by decide) (by decide), hT2]
    rw [drop_cons_getElem L (show m < L.length by omega)] at hP
    simp only [List.cons_append, seRows_cons, encL_append] at hP
    unfold seRotBody
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hT', hP, length_encL,
      List.length_replicate]
    rw [shiftIn_encL' _ _ (List.length_replicate), takeD_encL' _ _ (length_vecL _),
      drop_encL' _ _ (length_vecL _), take_succ_getElem L (show m < L.length by omega)]
    simp only [seRows_append, encL_append, List.append_assoc, seRows_cons, seRows_nil,
      List.append_nil]

/-! ### The row map `v ↦ v · G⁻¹(Y)` -/

/-- One row: `[v; v]` into `rGX`, `Y` into `rMA`, `ginvMulC`, row `0` appended to `seO`. -/
def seMapBody : Code :=
  .seq (.cp rGX rT2KNK) <| .seq (.mv rGX seQ rT2KNK) <| .seq (.app rGX rGX) <|
  .seq (.cp rMA seY) <| .seq ginvMulC <| .seq (.cp seR rT2KNK) <| .seq (.mv seR rMOut rT2KNK)
    (.app seO seR)

/-- **The row map**: `seO := [v · G⁻¹(Y) | v ∈ seQ]` (`|rTW|` rows, `Y` in `seY`). -/
def seMapC : Code := .seq (.clr seO) <| .seq (.cp seC rTW) (.rep seC seMapBody)

theorem seMapBody_writes_seC : seMapBody.writes seC = false := by decide

theorem seMapBody_writes : ∀ r : Fin 64, seMapBody.writes r = true →
    r = seQ ∨ r = seO ∨ (32 ≤ r.val ∧ r.val < 57 ∧ r ≠ seC) := by decide

theorem seMapC_writes : ∀ r : Fin 64, seMapC.writes r = true →
    r = seQ ∨ r = seO ∨ r = seC ∨ (32 ≤ r.val ∧ r.val < 57) := by decide

theorem matL_const (v : Fin 2 × Fin K → Rq N K) : matL (fun _ => v) = vecL v ++ vecL v :=
  matL_rows _

theorem exec_seMapBody (hK : 0 < K) (w : St) (v : Fin 2 × Fin K → Rq N K) (rest : List (Rq N K))
    (Y : Fin 2 → Fin 2 × Fin K → Rq N K) (hQ : w seQ = encL N K (vecL v ++ rest))
    (hY : w seY = encL N K (matL Y)) (hT : MulTmpl N K w) :
    exec N K seMapBody w seQ = encL N K rest ∧
    exec N K seMapBody w seO = w seO ++ encL N K (vecL (seGRow v Y)) ∧
    MulTmpl N K (exec N K seMapBody w) := by
  unfold seMapBody
  simp only [exec_seq]
  set w1 := exec N K (.cp rMA seY) (exec N K (.app rGX rGX) (exec N K (.mv rGX seQ rT2KNK)
    (exec N K (.cp rGX rT2KNK) w))) with hw1
  have h2 := hT.t2KNK
  have a1 : w1 rGX = encL N K (matL fun _ => v) ∧ w1 rMA = encL N K (matL Y) ∧
      w1 seQ = encL N K rest ∧ w1 seO = w seO := by
    rw [hw1]; vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h2, hQ, hY, length_encL,
      List.length_replicate, matL_const, encL_append, true_and]
    rw [shiftIn_encL' _ _ (List.length_replicate), takeD_encL' _ _ (length_vecL _),
      drop_encL' _ _ (length_vecL _)]
    simp
  obtain ⟨a1, a2, a3, a4⟩ := a1
  have T1 : MulTmpl N K w1 := hT.of_writes fun q hq => by
    rw [hw1]; vm_simp
    simp only [Function.update_apply]
    have h1 : q ≠ rMA := by intro e; subst e; simp at hq
    have h3 : q ≠ rGX := by intro e; subst e; simp at hq
    have h4 : q ≠ seQ := by intro e; subst e; simp at hq
    simp [h1, h3, h4]
  have g := exec_ginvMulC hK w1 (fun _ => v) Y a1 a2 T1
  set w2 := exec N K ginvMulC w1 with hw2
  have f2 : ∀ r : Fin 64, (r = seQ ∨ r = seO) → w2 r = w1 r := fun r hr =>
    exec_writes _ _ _ (by rcases hr with rfl | rfl <;> decide)
  have T2 : MulTmpl N K w2 := T1.of_writes fun q hq => exec_writes _ _ _ (ginvMulC_writes_ge q hq)
  have h2' := T2.t2KNK
  refine ⟨?_, ?_, ?_⟩
  · vm_simp; simp [Function.update_apply, f2 seQ (Or.inl rfl), a3]
  · vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, f2 seO (Or.inr rfl), a4, h2', g,
      length_encL, List.length_replicate, matL_rows]
    rw [shiftIn_encL' _ _ (List.length_replicate), encL_append,
      takeD_encL' _ _ (length_vecL _)]
    rfl
  · exact T2.of_writes fun q hq => by
      vm_simp
      have h1 : q ≠ seO := by intro e; subst e; simp at hq
      have h3 : q ≠ seR := by intro e; subst e; simp at hq
      have h4 : q ≠ rMOut := by intro e; subst e; simp at hq
      simp [Function.update_apply, h1, h3, h4]

/-- **The row map** over a slab of `n = |rTW|` rows. -/
theorem exec_seMapC (hK : 0 < K) (w : St) (L : List (Fin 2 × Fin K → Rq N K))
    (Y : Fin 2 → Fin 2 × Fin K → Rq N K) (hL : (w rTW).length = L.length)
    (hQ : w seQ = encL N K (seRows L)) (hY : w seY = encL N K (matL Y)) (hT : MulTmpl N K w) :
    exec N K seMapC w seO = encL N K (seRows (L.map fun v => seGRow v Y)) ∧
    MulTmpl N K (exec N K seMapC w) := by
  unfold seMapC
  simp only [exec_seq]
  set w1 := exec N K (.cp seC rTW) (exec N K (.clr seO) w) with hw1
  have f1 : ∀ r : Fin 64, r ≠ seC → r ≠ seO → w1 r = w r := fun r h1 h2 => by
    rw [hw1]; vm_simp; simp [Function.update_apply, h1, h2]
  have key := exec_rep_inv2 (N := N) (K := K) seC seMapBody seMapBody_writes_seC
    (fun m w' => w' seQ = encL N K (seRows (L.drop m)) ∧
      w' seO = encL N K (seRows ((L.take m).map fun v => seGRow v Y)) ∧ MulTmpl N K w') w1
    ⟨by rw [f1 _ (by decide) (by decide), hQ]; rfl, by rw [hw1]; vm_simp; simp,
      hT.of_writes fun q hq => f1 q (by intro e; subst e; simp at hq)
        (by intro e; subst e; simp at hq)⟩ ?_
  · have hc : (w1 seC).length = L.length := by rw [hw1]; vm_simp; simp [hL]
    rw [hc, List.take_length] at key
    exact ⟨key.2.1, key.2.2⟩
  · intro m w' hm hP _ hfr
    have hc : (w1 seC).length = L.length := by rw [hw1]; vm_simp; simp [hL]
    rw [hc] at hm
    obtain ⟨p1, p2, p3⟩ := hP
    rw [drop_cons_getElem L hm, seRows_cons] at p1
    have hY' : Function.update w' seC (w' seC).tail seY = encL N K (matL Y) := by
      rw [Function.update_of_ne (by decide), hfr _ (by decide) (by decide),
        f1 _ (by decide) (by decide), hY]
    obtain ⟨b1, b2, b3⟩ := exec_seMapBody hK (Function.update w' seC (w' seC).tail) L[m] _ Y
      (by rw [Function.update_of_ne (by decide), p1, encL_append]) hY'
      (p3.of_writes fun q hq => Function.update_of_ne (by intro e; subst e; simp at hq) _ _)
    refine ⟨b1, ?_, b3⟩
    rw [b2, Function.update_of_ne (by decide), p2, take_succ_getElem L hm]
    simp only [List.map_append, seRows_append, encL_append, List.map_cons, List.map_nil,
      seRows_cons, seRows_nil, List.append_nil]

/-! ### Adding a row -/

/-- One entry: `seQ ++= seR.pop + seV.pop`. -/
def seAddE : Code :=
  .seq (.cp rX0 rZ) <| .seq (.mvR rX0 seR) <| .seq (.cp rX1 rZ) <| .seq (.mvR rX1 seV) <|
  .seq (.op .add rX0 rX0 rX1) (.app seQ rX0)

/-- **The head row `u` of `seQ` becomes `u + v` (`v` in `seV`) at the back.** -/
def seAddHC : Code :=
  .seq (.cp seR rT2KNK) <| .seq (.mv seR seQ rT2KNK) <| .seq (.cp seE rT2K) (.rep seE seAddE)

theorem seAddE_writes_seE : seAddE.writes seE = false := by decide

theorem exec_seAddELoop (hK : 0 < K) (w : St) (l1 l2 : List (Rq N K)) (n : ℕ)
    (h1 : l1.length = n) (h2 : l2.length = n) (hA : w seR = encL N K l1)
    (hO : w seV = encL N K l2) (hC : (w seE).length = n) (hZ : w rZ = encRM N K 0) :
    exec N K (.rep seE seAddE) w seQ = w seQ ++ encL N K (List.zipWith (· + ·) l1 l2) := by
  have key := exec_rep_inv2 (N := N) (K := K) seE seAddE seAddE_writes_seE
    (fun m w' => w' seR = encL N K (l1.drop m) ∧ w' seV = encL N K (l2.drop m) ∧
      w' seQ = w seQ ++ encL N K (List.zipWith (· + ·) (l1.take m) (l2.take m))) w
    ⟨by simp [hA], by simp [hO], by simp⟩ ?_
  · rw [hC] at key
    rw [key.2.2, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  · intro m w' hm hP _ hfr
    rw [hC] at hm
    obtain ⟨p1, p2, p3⟩ := hP
    have p4 : w' rZ = encRM N K 0 := by rw [hfr _ (by decide) (by decide), hZ]
    have e1 := drop_cons_getElem l1 (show m < l1.length by omega)
    have e2 := drop_cons_getElem l2 (show m < l2.length by omega)
    have t1 := take_succ_getElem l1 (show m < l1.length by omega)
    have t2 := take_succ_getElem l2 (show m < l2.length by omega)
    rw [e1, encL_cons] at p1
    rw [e2, encL_cons] at p2
    unfold seAddE
    vm_simp
    refine ⟨?_, ?_, ?_⟩
    · simp [Function.update_apply, p1, p4]
    · simp [Function.update_apply, p2, p4]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, p2, p3, p4,
        shiftIn_encRM', takeD_encRM_append, takeD_encRM, canonW_add hK, t1, t2]
      rw [List.zipWith_append (by simp; omega), encL_append]
      simp

theorem seAddHC_writes : ∀ r : Fin 64, seAddHC.writes r = true →
    r ∈ [seR, seQ, seE, rX0, rX1, seV] := by decide

/-- **`seAddHC`**: `u :: L ↦ L ++ [u + v]`. -/
theorem exec_seAddHC (hK : 0 < K) (w : St) (u v : Fin 2 × Fin K → Rq N K)
    (L : List (Fin 2 × Fin K → Rq N K)) (hQ : w seQ = encL N K (seRows (u :: L)))
    (hV : w seV = encL N K (vecL v)) (hT : MulTmpl N K w) :
    exec N K seAddHC w seQ = encL N K (seRows (L ++ [seRowAdd u v])) := by
  unfold seAddHC
  simp only [exec_seq]
  set w1 := exec N K (.cp seE rT2K) (exec N K (.mv seR seQ rT2KNK) (exec N K (.cp seR rT2KNK) w))
    with hw1
  have h2 := hT.t2KNK
  have a : w1 seR = encL N K (vecL u) ∧ w1 seQ = encL N K (seRows L) ∧
      w1 seV = encL N K (vecL v) ∧ (w1 seE).length = 2 * K ∧ w1 rZ = encRM N K 0 := by
    rw [hw1]; vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h2, hQ, length_encL,
      List.length_replicate, seRows_cons, encL_append, hV, hT.t2K, hT.z, and_true, true_and]
    rw [shiftIn_encL' _ _ (List.length_replicate), takeD_encL' _ _ (length_vecL _),
      drop_encL' _ _ (length_vecL _)]
    exact ⟨rfl, rfl⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  rw [exec_seAddELoop hK w1 (vecL u) (vecL v) (2 * K) (length_vecL _) (length_vecL _) a1 a3 a4 a5,
    a2, ← vecL_seRowAdd, seRows_append, encL_append]
  simp

/-- **Row `0 += v`** (`v` in `seO`, `n = |rTW| ≥ 1` rows). -/
def seAdd0C : Code :=
  .seq (.cp seV seO) <| .seq seAddHC <| .seq (.cp seC rTW) <| .seq (.tl seC) seRotC

/-- **Row `p += v`**, `p = |rPw2| < n` (`v` in `seO`, `n = |rTW|` rows). -/
def seAddTC : Code :=
  .seq (.cp seV seO) <| .seq (.cp seC rPw2) <| .seq seRotC <| .seq seAddHC <|
  .seq (.cp seC rTW) <| .seq (.drop seC rPw2) <| .seq (.tl seC) seRotC

theorem seAdd0C_writes : ∀ r : Fin 64, seAdd0C.writes r = true →
    r ∈ [seR, seQ, seE, rX0, rX1, seV, seC] := by decide

theorem seAddTC_writes : ∀ r : Fin 64, seAddTC.writes r = true →
    r ∈ [seR, seQ, seE, rX0, rX1, seV, seC] := by decide

/-- The slab with `v` added to the row `p`. -/
def seAddAt (L : List (Fin 2 × Fin K → Rq N K)) (p : ℕ) (v : Fin 2 × Fin K → Rq N K) :
    List (Fin 2 × Fin K → Rq N K) :=
  L.modify p fun u => seRowAdd u v

theorem exec_seAdd0C (hK : 0 < K) (w : St) (v : Fin 2 × Fin K → Rq N K)
    (L : List (Fin 2 × Fin K → Rq N K)) (hL : (w rTW).length = L.length) (hL0 : 0 < L.length)
    (hQ : w seQ = encL N K (seRows L)) (hO : w seO = encL N K (vecL v)) (hT : MulTmpl N K w) :
    exec N K seAdd0C w seQ = encL N K (seRows (seAddAt L 0 v)) := by
  obtain ⟨u, L', rfl⟩ : ∃ u L', L = u :: L' := ⟨L.head (by rintro rfl; simp at hL0), L.tail,
    (List.cons_head_tail _).symm⟩
  unfold seAdd0C
  simp only [exec_seq]
  set w1 := exec N K (.cp seV seO) w with hw1
  have f1 : ∀ r : Fin 64, r ≠ seV → w1 r = w r := fun r h => by
    rw [hw1]; vm_simp; simp [Function.update_apply, h]
  have a := exec_seAddHC hK w1 u v L' (by rw [f1 _ (by decide), hQ])
    (by rw [hw1]; vm_simp; simp [hO]) (hT.of_writes fun q hq => f1 q (by intro e; subst e; simp at hq))
  set w2 := exec N K seAddHC w1 with hw2
  have f2 : ∀ r : Fin 64, r ∉ [seR, seQ, seE, rX0, rX1, seV] → w2 r = w r := fun r h => by
    rw [hw2, se_exec_frame _ _ seAddHC_writes _ _ h, f1 r (by intro e; subst e; simp at h)]
  have r := exec_seRotC (N := N) (K := K)
    (exec N K (.tl seC) (exec N K (.cp seC rTW) w2)) (L' ++ [seRowAdd u v]) L'.length (by simp)
    (by vm_simp; simp [Function.update_apply, a])
    (by vm_simp; simp [Function.update_apply, f2 rTW (by decide), hL])
    (by vm_simp; simp [Function.update_apply, f2 rT2KNK (by decide), hT.t2KNK])
  rw [r, List.rotate_append_length_eq]
  rfl

theorem exec_seAddTC (hK : 0 < K) (w : St) (v : Fin 2 × Fin K → Rq N K)
    (L : List (Fin 2 × Fin K → Rq N K)) (hL : (w rTW).length = L.length)
    (hp : (w rPw2).length < L.length)
    (hQ : w seQ = encL N K (seRows L)) (hO : w seO = encL N K (vecL v)) (hT : MulTmpl N K w) :
    exec N K seAddTC w seQ = encL N K (seRows (seAddAt L (w rPw2).length v)) := by
  set p := (w rPw2).length with hpdef
  have hp15 : (w 15).length = p := hpdef.symm
  unfold seAddTC
  simp only [exec_seq]
  set w1 := exec N K (.cp seC rPw2) (exec N K (.cp seV seO) w) with hw1
  have f1 : ∀ r : Fin 64, r ≠ seV → r ≠ seC → w1 r = w r := fun r h h' => by
    rw [hw1]; vm_simp; simp [Function.update_apply, h, h']
  have r1 := exec_seRotC (N := N) (K := K) w1 L p hp.le (by rw [f1 _ (by decide) (by decide), hQ])
    (by rw [hw1]; vm_simp; simp [Function.update_apply]; rfl)
    (by rw [f1 _ (by decide) (by decide), hT.t2KNK])
  set w2 := exec N K seRotC w1 with hw2
  have f2 : ∀ r : Fin 64, r ∉ [seC, seR, seQ] → r ≠ seV → w2 r = w r := fun r h h' => by
    rw [hw2, se_exec_frame _ _ seRotC_writes _ _ h, f1 r h' (by intro e; subst e; simp at h)]
  have hrot : L.rotate p = L[p] :: (L.drop (p + 1) ++ L.take p) := by
    rw [List.rotate_eq_drop_append_take hp.le, drop_cons_getElem L hp]; rfl
  rw [hrot] at r1
  have a := exec_seAddHC hK w2 L[p] v _ r1
    (by rw [hw2, exec_writes _ _ _ (by decide), hw1]; vm_simp; simp [Function.update_apply, hO])
    (hT.of_writes fun q hq => f2 q (by revert q; decide) (by intro e; subst e; simp at hq))
  set w3 := exec N K seAddHC w2 with hw3
  have f3 : ∀ r : Fin 64, r ∉ [seR, seQ, seE, rX0, rX1, seV, seC] → w3 r = w r := fun r h => by
    rw [hw3, se_exec_frame _ _ seAddHC_writes _ _ (fun h' => h (by simp at h' ⊢; tauto)),
      f2 r (fun h' => h (by simp at h' ⊢; tauto)) (by intro e; subst e; simp at h)]
  have r2 := exec_seRotC (N := N) (K := K)
    (exec N K (.tl seC) (exec N K (.drop seC rPw2) (exec N K (.cp seC rTW) w3)))
    (L.drop (p + 1) ++ L.take p ++ [seRowAdd L[p] v]) (L.drop (p + 1)).length (by simp)
    (by vm_simp; simp [Function.update_apply, a])
    (by vm_simp; simp [Function.update_apply, f3 rTW (by decide), f3 rPw2 (by decide), hL, hp15])
    (by vm_simp; simp [Function.update_apply, f3 rT2KNK (by decide), hT.t2KNK])
  rw [r2, List.append_assoc, List.rotate_append_length_eq, seAddAt,
    List.modify_eq_take_cons_drop hp]
  simp

/-! ### A row times a scalar -/

/-- One entry: `seO ++= μ · seV.pop`. -/
def seScE : Code :=
  .seq (.cp rX0 rZ) <| .seq (.mvR rX0 seV) <| .seq (.op .mul rX0 seMu rX0) (.app seO rX0)

/-- **`seO := μ · v`** (`v` in `seV`, `μ` in `seMu`). -/
def seScaleC : Code := .seq (.clr seO) <| .seq (.cp seE rT2K) (.rep seE seScE)

theorem seScE_writes_seE : seScE.writes seE = false := by decide

theorem seScaleC_writes : ∀ r : Fin 64, seScaleC.writes r = true → r ∈ [seO, seE, rX0, seV] := by
  decide

theorem exec_seScaleC (hK : 0 < K) (w : St) (μ : Rq N K) (v : Fin 2 × Fin K → Rq N K)
    (hV : w seV = encL N K (vecL v)) (hM : w seMu = encRM N K μ) (hT : MulTmpl N K w) :
    exec N K seScaleC w seO = encL N K (vecL (seRowSmul μ v)) := by
  unfold seScaleC
  simp only [exec_seq]
  set w1 := exec N K (.cp seE rT2K) (exec N K (.clr seO) w) with hw1
  have key := exec_rep_inv2 (N := N) (K := K) seE seScE seScE_writes_seE
    (fun m w' => w' seV = encL N K ((vecL v).drop m) ∧
      w' seO = encL N K (((vecL v).take m).map (μ * ·))) w1
    ⟨by rw [hw1]; vm_simp; simp [hV], by rw [hw1]; vm_simp; simp⟩ ?_
  · have hc : (w1 seE).length = 2 * K := by rw [hw1]; vm_simp; simp [hT.t2K]
    rw [hc, List.take_of_length_le (by simp)] at key
    rw [key.2, vecL_seRowSmul]
  · intro m w' hm hP _ hfr
    have hc : (w1 seE).length = 2 * K := by rw [hw1]; vm_simp; simp [hT.t2K]
    rw [hc] at hm
    obtain ⟨p1, p2⟩ := hP
    have p3 : w' rZ = encRM N K 0 := by
      rw [hfr _ (by decide) (by decide), hw1]; vm_simp; simp [hT.z]
    have p4 : w' seMu = encRM N K μ := by
      rw [hfr _ (by decide) (by decide), hw1]; vm_simp; simp [hM]
    have e1 := drop_cons_getElem (vecL v) (show m < (vecL v).length by simp; omega)
    have t1 := take_succ_getElem (vecL v) (show m < (vecL v).length by simp; omega)
    rw [e1, encL_cons] at p1
    unfold seScE
    vm_simp
    refine ⟨?_, ?_⟩
    · simp [Function.update_apply, p1, p3]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, p2, p3, p4,
        shiftIn_encRM', takeD_encRM_append, takeD_encRM, canonW_mul hK, t1, List.map_append,
        encL_append]
      simp

/-! ### The sum of two slabs -/

/-- One entry: `seAcc ++= seQ.pop + seO.pop`. -/
def seSumE : Code :=
  .seq (.cp rX0 rZ) <| .seq (.mvR rX0 seQ) <| .seq (.cp rX1 rZ) <| .seq (.mvR rX1 seO) <|
  .seq (.op .add rX0 rX0 rX1) (.app seAcc rX0)

/-- **`seAcc := seQ + seO`** entrywise (`|rTW|` rows). -/
def seSumC : Code := .seq seCntC <| .seq (.clr seAcc) (.rep seC seSumE)

theorem seSumE_writes_seC : seSumE.writes seC = false := by decide

theorem seSumC_writes : ∀ r : Fin 64, seSumC.writes r = true →
    r ∈ [seC, seE, seAcc, rX0, rX1, seQ, seO] := by decide

theorem exec_seSumC (hK : 0 < K) (w : St) (L M : List (Fin 2 × Fin K → Rq N K))
    (hL : (w rTW).length = L.length) (hM : M.length = L.length)
    (hQ : w seQ = encL N K (seRows L)) (hO : w seO = encL N K (seRows M)) (hT : MulTmpl N K w) :
    exec N K seSumC w seAcc = encL N K (seRows (List.zipWith seRowAdd L M)) := by
  unfold seSumC
  simp only [exec_seq]
  have hc := exec_seCntC (N := N) (K := K) w L.length hL hT.t2K
  set w1 := exec N K (.clr seAcc) (exec N K seCntC w) with hw1
  have f1 : ∀ r : Fin 64, r ≠ seC → r ≠ seE → r ≠ seAcc → w1 r = w r := fun r h1 h2 h3 => by
    rw [hw1, exec_clr, Function.update_of_ne h3]
    exact exec_writes _ _ _ (by unfold seCntC; simp [Code.writes, Ne.symm h1, Ne.symm h2])
  set l1 := seRows L
  set l2 := seRows M
  have hl1 : l1.length = L.length * (2 * K) := by simp [l1]
  have hl2 : l2.length = L.length * (2 * K) := by simp [l2, hM]
  have key := exec_rep_inv2 (N := N) (K := K) seC seSumE seSumE_writes_seC
    (fun m w' => w' seQ = encL N K (l1.drop m) ∧ w' seO = encL N K (l2.drop m) ∧
      w' seAcc = encL N K (List.zipWith (· + ·) (l1.take m) (l2.take m))) w1
    ⟨by rw [f1 _ (by decide) (by decide) (by decide), hQ]; simp,
      by rw [f1 _ (by decide) (by decide) (by decide), hO]; simp, by rw [hw1]; vm_simp; simp⟩ ?_
  · have hc1 : (w1 seC).length = L.length * (2 * K) := by
      rw [hw1, exec_clr, Function.update_of_ne (by decide), hc]
    rw [hc1] at key
    rw [key.2.2, List.take_of_length_le (by omega), List.take_of_length_le (by omega),
      seRows_zipWith L M hM.symm]
  · intro m w' hm hP _ hfr
    have hc1 : (w1 seC).length = L.length * (2 * K) := by
      rw [hw1, exec_clr, Function.update_of_ne (by decide), hc]
    rw [hc1] at hm
    obtain ⟨p1, p2, p3⟩ := hP
    have p4 : w' rZ = encRM N K 0 := by
      rw [hfr _ (by decide) (by decide), f1 _ (by decide) (by decide) (by decide), hT.z]
    have e1 := drop_cons_getElem l1 (show m < l1.length by omega)
    have e2 := drop_cons_getElem l2 (show m < l2.length by omega)
    have t1 := take_succ_getElem l1 (show m < l1.length by omega)
    have t2 := take_succ_getElem l2 (show m < l2.length by omega)
    rw [e1, encL_cons] at p1
    rw [e2, encL_cons] at p2
    unfold seSumE
    vm_simp
    refine ⟨?_, ?_, ?_⟩
    · simp [Function.update_apply, p1, p4]
    · simp [Function.update_apply, p2, p4]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, p2, p3, p4,
        shiftIn_encRM', takeD_encRM_append, takeD_encRM, canonW_add hK, t1, t2]
      rw [List.zipWith_append (by simp; omega), encL_append]
      simp

end AdvancedEncryption.ExpLUT.Prog
