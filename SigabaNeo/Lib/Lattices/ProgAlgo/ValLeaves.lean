import SigabaNeo.Lib.Lattices.ProgAlgo.ValArith

/-!
# The leaves of a coefficient on the word machine

A loop computing terms one by one (`jloopC term`): each round pops a digit (`V` bits) from the stream
`SD = 33` into `DIG = 31`, a coefficient (`k V` bits) from the stream `SC = 34` into `COEF = 30`,
runs the term code (`termSubC` or `termAddC`, result on `Z = 26`) and shifts the result into the
leaves buffer `LB = 32`. **`exec_jloopC`**: after `n` rounds `LB` ends with the last `n` results
shifted in, for any term code meeting `TermOk`.
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-- **Loops under an invariant.** -/
theorem exec_rep_inv {c : Fin 64} {B : Code} (I : ℕ → St → Prop)
    (hstep : ∀ n w, I n w → I (n + 1) (exec V f B (Function.update w c (w c).tail))) :
    ∀ w, I 0 w → I (w c).length (exec V f (.rep c B) w) := by
  intro w h0
  rw [exec_rep']
  generalize (w c).length = m
  induction m with
  | zero => exact h0
  | succ m ih => rw [Function.iterate_succ_apply']; exact hstep m _ ih

/-- Words of the leaves: `LB = 32` the buffer, `SD = 33` the digits, `SC = 34` the coefficients. -/
abbrev LB : Fin 64 := 32
abbrev SD : Fin 64 := 33
abbrev SC : Fin 64 := 34

/-- A term code: `Z := F (DIG, COEF)` for the coefficient of `k V` bits, writing only words below
`32` and not `COEF`, `DIG`, nor the templates. -/
structure TermOk (V K : ℕ) (f : List Bool → List Bool → List Bool) (one zv : List Bool) (T : Code)
    (F : List Bool → List (List Bool) → List Bool) : Prop where
  val : ∀ w (cs : List (List Bool)), Tmpl V K w → w 10 = one → w 11 = zv → cs.length = K + 1 →
    (∀ x ∈ cs, x.length = V) → w 30 = cs.flatten → exec V f T w 26 = F (w 31) cs
  len : ∀ d cs, cs.length = K + 1 → (∀ x ∈ cs, x.length = V) → (F d cs).length = (K + 1) * V
  wr32 : ∀ j ∈ wr T, j.val < 32
  wr30 : (30 : Fin 64) ∉ wr T
  wr31 : (31 : Fin 64) ∉ wr T
  wrT : ∀ j ∈ ([10, 11, 12, 13, 14, 15, 16, 20, 27, 29] : List (Fin 64)), j ∉ wr T

/-- One round: pop the digit and the coefficient, compute the term, push it. -/
def jBody (T : Code) : Code := ofList [.mvV 31 SD, .mv 30 SC 14, T, .mv LB 26 14]

/-- `|ctr|` rounds. -/
def jloopC (T : Code) (ctr : Fin 64) : Code := .rep ctr (jBody T)

/-- Move a block of `|c|` bits from a stream into a register of that width. -/
theorem exec_mv_pop {d s c : Fin 64} (h : ¬(d = s ∨ d = c ∨ s = c)) {w : St} {x L : List Bool}
    (hd : (w d).length = (w c).length) (hx : x.length = (w c).length) (hs : w s = x ++ L) :
    exec V f (.mv d s c) w = Function.update (Function.update w s L) d x := by
  simp only [exec, if_neg h, hs]
  rw [List.drop_left' hx, shiftIn, takeD_eq_take (by simp [hx]), List.take_left' hx,
    List.drop_left' hd]

/-- Shift a register of `|c|` bits into a buffer. -/
theorem exec_mv_push {d s c : Fin 64} (h : ¬(d = s ∨ d = c ∨ s = c)) {w : St}
    (hs : (w s).length = (w c).length) :
    exec V f (.mv d s c) w = Function.update (Function.update w s [])
      d ((w d ++ w s).drop (w c).length) := by
  simp only [exec, if_neg h, shiftIn, takeD_of_length' hs]
  rw [List.drop_eq_nil_of_le (by omega)]

theorem Tmpl.of_low {K : ℕ} {w w' : St} (h : Tmpl V K w)
    (e : ∀ j : Fin 64, j.val < 30 → w' j = w j) : Tmpl V K w' :=
  h.of_eq fun j hj => e j (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem constV_len {α : Type*} (one zv : α) : ∀ w m, (constV one zv w m).length = w
  | 0, _ => rfl
  | w + 1, m => by simp [constV, constV_len one zv w (m / 2)]

/-- The invariant of the rounds of `jloopC`. -/
structure JInv (V K : ℕ) (F : List Bool → List (List Bool) → List Bool) (ctr : Fin 64) (w₀ : St)
    (ds : List (List Bool)) (css : List (List (List Bool))) (rd rc : List Bool) (m : ℕ) (w : St) :
    Prop where
  sd : w SD = (ds.drop m).flatten ++ rd
  sc : w SC = ((css.drop m).map List.flatten).flatten ++ rc
  lb : w LB = (w₀ LB ++ ((List.zipWith F ds css).take m).flatten).drop (m * ((K + 1) * V))
  tm : Tmpl V K w
  c30 : (w 30).length = (K + 1) * V
  c31 : (w 31).length = V
  hi : ∀ j : Fin 64, 32 ≤ j.val → j ≠ LB → j ≠ SD → j ≠ SC → j ≠ ctr → w j = w₀ j
  one : w 10 = w₀ 10
  zv : w 11 = w₀ 11

theorem jinv_step {K : ℕ} {one zv : List Bool} {T : Code}
    {F : List Bool → List (List Bool) → List Bool}
    (hT : TermOk V K f one zv T F) {ctr : Fin 64} (hctr : 35 ≤ ctr.val) {w₀ : St}
    (h10 : w₀ 10 = one) (h11 : w₀ 11 = zv)
    {ds : List (List Bool)} {css : List (List (List Bool))} {rd rc : List Bool}
    (hl : ds.length = css.length) (hdv : ∀ x ∈ ds, x.length = V)
    (hcv : ∀ cs ∈ css, cs.length = K + 1 ∧ ∀ x ∈ cs, x.length = V) {m : ℕ} (hm : m < ds.length)
    {w : St} (h : JInv V K F ctr w₀ ds css rd rc m w) :
    JInv V K F ctr w₀ ds css rd rc (m + 1)
      (exec V f (jBody T) (Function.update w ctr (w ctr).tail)) := by
  have hm' : m < css.length := hl ▸ hm
  have cLB : ctr ≠ LB := fun e => by subst e; simp at hctr
  have cSD : ctr ≠ SD := fun e => by subst e; simp at hctr
  have cSC : ctr ≠ SC := fun e => by subst e; simp at hctr
  have cl : ∀ j : Fin 64, j.val < 35 → j ≠ ctr := fun j hj e => by subst e; omega
  set d := ds[m]
  set cs := css[m]
  have hd : d.length = V := hdv d (List.getElem_mem hm)
  obtain ⟨hcl, hcsv⟩ := hcv cs (List.getElem_mem hm')
  have hcf : cs.flatten.length = (K + 1) * V := by rw [length_flatten_of hcsv, hcl]
  set u0 := Function.update w ctr (w ctr).tail with hu0
  have u0_ : ∀ j, j ≠ ctr → u0 j = w j := fun j hj => by simp [u0, Function.update_of_ne hj]
  -- pop the digit
  have e1 : exec V f (.mvV 31 SD) u0 = Function.update (Function.update u0 SD
      ((ds.drop (m + 1)).flatten ++ rd)) 31 d := by
    refine exec_mvV_pop (by decide) (by rw [u0_ 31 (cl 31 (by decide))]; exact h.c31) hd ?_
    rw [u0_ SD cSD.symm, h.sd, List.drop_eq_getElem_cons hm, List.flatten_cons, List.append_assoc]
  set u1 := Function.update (Function.update u0 SD ((ds.drop (m + 1)).flatten ++ rd)) 31 d with hu1
  -- pop the coefficient
  have e2 : exec V f (.mv 30 SC 14) u1 = Function.update (Function.update u1 SC
      (((css.drop (m + 1)).map List.flatten).flatten ++ rc)) 30 cs.flatten := by
    refine exec_mv_pop (by decide) ?_ ?_ ?_
    · simp (config := {decide := true}) only [u1, Function.update_apply, if_false]
      rw [u0_ 30 (cl 30 (by decide)), u0_ 14 (cl 14 (by decide)), h.c30, h.tm.h14]
    · simp (config := {decide := true}) only [u1, Function.update_apply, if_false]
      rw [u0_ 14 (cl 14 (by decide)), h.tm.h14, hcf]
    · simp (config := {decide := true}) only [u1, Function.update_apply, if_false]
      rw [u0_ SC cSC.symm, h.sc, List.drop_eq_getElem_cons hm', List.map_cons, List.flatten_cons,
        List.append_assoc]
  set u2 := Function.update (Function.update u1 SC
      (((css.drop (m + 1)).map List.flatten).flatten ++ rc)) 30 cs.flatten with hu2
  have u2_ : ∀ j : Fin 64, j ≠ 30 → j ≠ SC → j ≠ 31 → j ≠ SD → j ≠ ctr → u2 j = w j :=
    fun j h30 hSC h31 hSD hc => by
      simp [u2, u1, Function.update_of_ne h30, Function.update_of_ne hSC, Function.update_of_ne h31,
        Function.update_of_ne hSD, u0_ j hc]
  have tm2 : Tmpl V K u2 := Tmpl.of_low h.tm fun j hj =>
    u2_ j (fun e => by subst e; simp at hj) (fun e => by subst e; simp at hj)
      (fun e => by subst e; simp at hj) (fun e => by subst e; simp at hj) (cl j (by omega))
  have u2_31 : u2 31 = d := by simp (config := {decide := true}) [u2, u1, Function.update_apply]
  have u2_30 : u2 30 = cs.flatten := by simp [u2]
  -- the term
  have e3 := hT.val u2 cs tm2
    (by rw [u2_ 10 (by decide) (by decide) (by decide) (by decide) (cl 10 (by decide)), h.one, h10])
    (by rw [u2_ 11 (by decide) (by decide) (by decide) (by decide) (cl 11 (by decide)), h.zv, h11])
    hcl hcsv u2_30
  rw [u2_31] at e3
  have u3_ : ∀ j : Fin 64, j ∉ wr T → exec V f T u2 j = u2 j := fun j hj => exec_not_mem T u2 j hj
  have u3hi : ∀ j : Fin 64, 32 ≤ j.val → exec V f T u2 j = u2 j := fun j hj =>
    u3_ j (fun hm => by have := hT.wr32 j hm; omega)
  have tm3 : Tmpl V K (exec V f T u2) := tm2.of_eq fun j hj => u3_ j (hT.wrT j hj)
  have hbody0 : exec V f (jBody T) u0 = exec V f (.mv LB 26 14) (exec V f T u2) := by
    simp only [jBody, exec_ofList, List.foldl_cons, List.foldl_nil]
    rw [e1, e2]
  rw [hbody0]
  generalize exec V f T u2 = u3 at e3 u3_ u3hi tm3
  -- push the term
  have hz : (u3 26).length = (u3 14).length := by
    rw [e3, hT.len d cs hcl hcsv, tm3.h14]
  have e4 : exec V f (.mv LB 26 14) u3 = Function.update (Function.update u3 26 []) LB
      ((u3 LB ++ u3 26).drop (u3 14).length) := exec_mv_push (by decide) hz
  rw [e4]
  have v : ∀ j : Fin 64, j ≠ LB → j ≠ 26 → Function.update (Function.update u3 26 []) LB
      ((u3 LB ++ u3 26).drop (u3 14).length) j = u3 j := fun j h1 h2 => by
    simp [Function.update_of_ne h1, Function.update_of_ne h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v SD (by decide) (by decide), u3hi SD (by decide)]
    simp (config := {decide := true}) [u2, u1, Function.update_apply]
  · rw [v SC (by decide) (by decide), u3hi SC (by decide)]
    simp (config := {decide := true}) [u2, Function.update_apply]
  · simp only [Function.update_self]
    rw [u3hi LB (by decide), tm3.h14, e3]
    have e2' : u2 LB = w LB := u2_ LB (by decide) (by decide) (by decide) (by decide) cLB.symm
    have hzl : ∀ x ∈ List.zipWith F ds css, x.length = (K + 1) * V := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_zipWith]
      exact hT.len _ _ (hcv _ (List.getElem_mem _)).1 (hcv _ (List.getElem_mem _)).2
    have htl : ((List.zipWith F ds css).take m).flatten.length = m * ((K + 1) * V) := by
      rw [length_flatten_of (V := (K + 1) * V) (fun x hx => hzl x (List.mem_of_mem_take hx)),
        List.length_take, List.length_zipWith, ← hl, min_self, min_eq_left hm.le]
    have htake : (List.zipWith F ds css).take (m + 1) =
        (List.zipWith F ds css).take m ++ [F d cs] := by
      rw [List.take_succ, List.getElem?_zipWith, List.getElem?_eq_getElem hm,
        List.getElem?_eq_getElem hm']
      rfl
    rw [e2', h.lb, drop_append_drop' (by rw [List.length_append, htl]; omega), List.append_assoc,
      htake, List.flatten_append, List.flatten_singleton]
    congr 1; ring
  · refine tm3.of_eq fun j hj => v j ?_ ?_ <;>
      (simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
       rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [v 30 (by decide) (by decide), u3_ 30 hT.wr30, u2_30, hcf]
  · rw [v 31 (by decide) (by decide), u3_ 31 hT.wr31, u2_31, hd]
  · intro j hj hLB hSD hSC hc
    rw [v j hLB (fun e => by subst e; simp at hj), u3hi j hj,
      u2_ j (fun e => by subst e; simp at hj) hSC (fun e => by subst e; simp at hj) hSD hc,
      h.hi j hj hLB hSD hSC hc]
  · rw [v 10 (by decide) (by decide), u3_ 10 (hT.wrT 10 (by decide)),
      u2_ 10 (by decide) (by decide) (by decide) (by decide) (cl 10 (by decide)), h.one]
  · rw [v 11 (by decide) (by decide), u3_ 11 (hT.wrT 11 (by decide)),
      u2_ 11 (by decide) (by decide) (by decide) (by decide) (cl 11 (by decide)), h.zv]

/-- **The loop of terms**: after `|ctr| = |ds|` rounds, the buffer `LB` ends with the `|ds|` terms
`F d cs` shifted in, the streams with their remainders. -/
theorem exec_jloopC {K : ℕ} {one zv : List Bool} {T : Code}
    {F : List Bool → List (List Bool) → List Bool}
    (hT : TermOk V K f one zv T F) {ctr : Fin 64} (hctr : 35 ≤ ctr.val) (w : St)
    (h10 : w 10 = one) (h11 : w 11 = zv)
    (ds : List (List Bool)) (css : List (List (List Bool))) (rd rc : List Bool)
    (hl : ds.length = css.length) (hdv : ∀ x ∈ ds, x.length = V)
    (hcv : ∀ cs ∈ css, cs.length = K + 1 ∧ ∀ x ∈ cs, x.length = V) (hn : (w ctr).length = ds.length)
    (htm : Tmpl V K w) (h30 : (w 30).length = (K + 1) * V) (h31 : (w 31).length = V)
    (hSD : w SD = ds.flatten ++ rd) (hSC : w SC = (css.map List.flatten).flatten ++ rc) :
    JInv V K F ctr w ds css rd rc ds.length (exec V f (jloopC T ctr) w) := by
  have := exec_rep_inv (V := V) (f := f) (c := ctr) (B := jBody T)
    (fun m w' => m ≤ ds.length → JInv V K F ctr w ds css rd rc m w')
    (fun m w' ih hm => jinv_step hT hctr h10 h11 hl hdv hcv (by omega) (ih (by omega))) w
    (fun _ => ⟨by simpa using hSD, by simpa using hSC, by simp, htm, h30, h31,
      fun _ _ _ _ _ _ => rfl, rfl, rfl⟩)
  rw [hn] at this
  exact this le_rfl

theorem modSubV_shape (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V) (q w : ℕ)
    (as bs : List (List Bool)) (hal : as.length = w) (hbl : bs.length = w) :
    (modSubV one (fV V f) zv q w as bs).length = w ∧
      ∀ x ∈ modSubV one (fV V f) zv q w as bs, x.length = V := by
  simp only [modSubV]
  refine ⟨?_, muxLV_len hf _ _⟩
  have l1 : (rippleV one (fV V f) as (notLV one (fV V f) bs) one).length = w + 1 := by
    rw [length_rippleV _ _ _ _ _ (by rw [length_notLV, hal, hbl]), hal]
  have l2 : (rippleV one (fV V f) ((rippleV one (fV V f) as (notLV one (fV V f) bs) one).take w)
      (constV one zv w q) zv).length = w + 1 := by
    rw [length_rippleV _ _ _ _ _ (by rw [List.length_take, l1, constV_len]; omega),
      List.length_take, l1]
    omega
  rw [length_muxLV, List.length_take, List.length_take, l1, l2]
  omega

/-- **`termSubC` is a term code.** -/
theorem termOk_sub (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (K : ℕ)
    (one zv : List Bool) (h1 : one.length = V) (hz : zv.length = V) :
    TermOk V K f one zv termSubC fun d cs => (modSubV one (fV V f) zv (2 ^ K) (K + 1)
      (List.replicate (K + 1) zv) (andLV one (fV V f) d cs)).flatten where
  val w cs ht h10 h11 hcl hcv hC := by rw [exec_termSubC hf w K ht cs hcl hcv hC, h10, h11]
  len d cs hcl hcv := by
    obtain ⟨l, v⟩ := modSubV_shape hf h1 hz (2 ^ K) (K + 1) (List.replicate (K + 1) zv)
      (andLV one (fV V f) d cs) (by simp) (by rw [length_andLV, hcl])
    rw [length_flatten_of v, l]
  wr32 := by decide
  wr30 := by decide
  wr31 := by decide
  wrT := by decide

theorem modAddV_shape (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V) (q w : ℕ)
    (as bs : List (List Bool)) (hal : as.length = w) (hbl : bs.length = w) :
    (modAddV one (fV V f) zv q w as bs).length = w ∧
      ∀ x ∈ modAddV one (fV V f) zv q w as bs, x.length = V := by
  simp only [modAddV]
  refine ⟨?_, fun x hx => muxLV_len hf _ _ x (List.mem_of_mem_take hx)⟩
  have l1 : (rippleV one (fV V f) as bs zv).length = w + 1 := by
    rw [length_rippleV _ _ _ _ _ (by rw [hal, hbl]), hal]
  have l2 : (rippleV one (fV V f) (rippleV one (fV V f) as bs zv)
      (constV one zv (w + 1) (2 ^ (w + 1) - q)) zv).length = w + 2 := by
    rw [length_rippleV _ _ _ _ _ (by rw [l1, constV_len]), l1]
  rw [List.length_take, length_muxLV, List.length_take, l1, l2]
  omega

/-- **`termAddC` is a term code.** -/
theorem termOk_add (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (K : ℕ)
    (one zv : List Bool) (h1 : one.length = V) (hz : zv.length = V) :
    TermOk V K f one zv termAddC fun d cs => (modAddV one (fV V f) zv (2 ^ K) (K + 1)
      (List.replicate (K + 1) zv) (andLV one (fV V f) d cs)).flatten where
  val w cs ht h10 h11 hcl hcv hC := by rw [exec_termAddC hf w K ht cs hcl hcv hC, h10, h11]
  len d cs hcl hcv := by
    obtain ⟨l, v⟩ := modAddV_shape hf h1 hz (2 ^ K) (K + 1) (List.replicate (K + 1) zv)
      (andLV one (fV V f) d cs) (by simp) (by rw [length_andLV, hcl])
    rw [length_flatten_of v, l]
  wr32 := by decide
  wr30 := by decide
  wr31 := by decide
  wrT := by decide

end ValVM

end SigabaNeo.Tape
