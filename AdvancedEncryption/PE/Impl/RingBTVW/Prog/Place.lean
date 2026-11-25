import PE.Impl.RingBTVW.Prog.SchemeWords2

/-!
# Placing the blocks on the tapes of a component

A component (`XProg 82`) keeps its values on the tapes `0 … 19` and runs every block of
`PE.Impl.RingBTVW.Prog.Blocks` through a frame that sends the block's output and inputs to chosen
value tapes and its scratch tapes to the tapes `20, 21, …` (`vTr`, `vSel`, `vHash`, `vMm`, `vAdd`,
`vGet`, `vJoin`, `vGad`, `vOne`). While the tapes from `20` on are blank (`Blank20`), a placed
block updates its output tape (`plc_trB`, …), and the updated store is again `Blank20` when the
output is a value tape (`Blank20.upd`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-- The tapes from `20` on are blank. -/
def Blank20 (s : Store 82) : Prop := ∀ t : Fin 82, 20 ≤ t.val → s t = []

theorem Blank20.upd {s : Store 82} (h : Blank20 s) {o : Fin 82} (ho : o.val < 20) (v : List Bool) :
    Blank20 (Function.update s o v) := fun t ht => by
  rw [Function.update_of_ne (fun e => by subst e; omega)]; exact h t ht

/-! ### The placements -/

/-- Output `o`, input `a`; scratch from `20`. -/
def vTr (o a : Fin 82) (j : Fin 21) : Fin 82 :=
  if j.val = 0 then o else if j.val = 1 then a else ⟨j.val + 18, by have := j.isLt; omega⟩

/-- Output `o`, inputs `a b c`; scratch from `20`. -/
def vSel (o a b c : Fin 82) (j : Fin 14) : Fin 82 :=
  if j.val = 0 then o else if j.val = 1 then a else if j.val = 2 then b else if j.val = 3 then c
  else ⟨j.val + 16, by have := j.isLt; omega⟩

/-- Output `o`, inputs `a b c`; scratch from `20`. -/
def vHash (o a b c : Fin 82) (j : Fin 46) : Fin 82 :=
  if j.val = 0 then o else if j.val = 1 then a else if j.val = 2 then b else if j.val = 3 then c
  else ⟨j.val + 16, by have := j.isLt; omega⟩

/-- Output `o`, inputs `a b`; scratch from `20`. -/
def vMm (o a b : Fin 82) (j : Fin 60) : Fin 82 :=
  if j.val = 0 then o else if j.val = 1 then a else if j.val = 2 then b
  else ⟨j.val + 17, by have := j.isLt; omega⟩

/-- Output `o`, inputs `a b`; scratch from `20`. -/
def vAdd (o a b : Fin 82) (j : Fin 29) : Fin 82 :=
  if j.val = 0 then o else if j.val = 1 then a else if j.val = 2 then b
  else ⟨j.val + 17, by have := j.isLt; omega⟩

/-- Output `o`, input `a`; scratch from `20`. -/
def vGet (o a : Fin 82) (j : Fin 11) : Fin 82 :=
  if j.val = 0 then o else if j.val = 1 then a else ⟨j.val + 18, by have := j.isLt; omega⟩

/-- Output `o`, inputs `a b c`; scratch from `20`. -/
def vJoin (o a b c : Fin 82) (j : Fin 12) : Fin 82 :=
  if j.val = 0 then o else if j.val = 1 then a else if j.val = 2 then b else if j.val = 3 then c
  else ⟨j.val + 16, by have := j.isLt; omega⟩

/-- Output `o`; scratch from `20`. -/
def vGad (o : Fin 82) (j : Fin 22) : Fin 82 :=
  if j.val = 0 then o else ⟨j.val + 19, by have := j.isLt; omega⟩

/-- Output `o`; scratch `20`. -/
def vOne (o : Fin 82) (j : Fin 2) : Fin 82 := if j.val = 0 then o else 20

theorem vTr_scr (o a : Fin 82) (i : Fin 21) (hi : 2 ≤ i.val) : 20 ≤ (vTr o a i).val := by
  unfold vTr; split_ifs <;> (try dsimp only) <;> omega
theorem vSel_scr (o a b c : Fin 82) (i : Fin 14) (hi : 4 ≤ i.val) : 20 ≤ (vSel o a b c i).val := by
  unfold vSel; split_ifs <;> (try dsimp only) <;> omega
theorem vHash_scr (o a b c : Fin 82) (i : Fin 46) (hi : 4 ≤ i.val) : 20 ≤ (vHash o a b c i).val := by
  unfold vHash; split_ifs <;> (try dsimp only) <;> omega
theorem vMm_scr (o a b : Fin 82) (i : Fin 60) (hi : 3 ≤ i.val) : 20 ≤ (vMm o a b i).val := by
  unfold vMm; split_ifs <;> (try dsimp only) <;> omega
theorem vAdd_scr (o a b : Fin 82) (i : Fin 29) (hi : 3 ≤ i.val) : 20 ≤ (vAdd o a b i).val := by
  unfold vAdd; split_ifs <;> (try dsimp only) <;> omega
theorem vGet_scr (o a : Fin 82) (i : Fin 11) (hi : 2 ≤ i.val) : 20 ≤ (vGet o a i).val := by
  unfold vGet; split_ifs <;> (try dsimp only) <;> omega
theorem vJoin_scr (o a b c : Fin 82) (i : Fin 12) (hi : 4 ≤ i.val) : 20 ≤ (vJoin o a b c i).val := by
  unfold vJoin; split_ifs <;> (try dsimp only) <;> omega
theorem vGad_scr (o : Fin 82) (i : Fin 22) (hi : 1 ≤ i.val) : 20 ≤ (vGad o i).val := by
  unfold vGad; split_ifs <;> (try dsimp only) <;> omega

/-! ### Placed laws -/

section Laws

variable {N K k : ℕ}

theorem plc_trB (o a : Fin 82) (h : Function.Injective (vTr o a)) (m r s B Z : ℕ) (S : Store 82)
    (hS : Blank20 S) :
    (frame ⟨vTr o a, h⟩ (trB m r s B Z)).law S =
      PMF.pure (Function.update S o (trW m r s B Z (S a))) :=
  law_frame_upd _ _ S 0 _ (law_trB m r s B Z _ fun i hi => hS _ (vTr_scr o a i hi))

theorem plc_selB (o a b c : Fin 82) (h : Function.Injective (vSel o a b c)) (n B : ℕ) (S : Store 82)
    (hS : Blank20 S) :
    (frame ⟨vSel o a b c, h⟩ (selB n B)).law S =
      PMF.pure (Function.update S o (selW n B (S a) (S b) (S c))) :=
  law_frame_upd _ _ S 0 _ (law_selB n B _ fun i hi => hS _ (vSel_scr o a b c i hi))

theorem plc_hashB (o a b c : Fin 82) (h : Function.Injective (vHash o a b c)) (P d : ℕ)
    (S : Store 82) (hS : Blank20 S) :
    (frame ⟨vHash o a b c, h⟩ (hashB P d N K)).law S =
      PMF.pure (Function.update S o (hashW P d N K (S a) (S b) (S c))) :=
  law_frame_upd _ _ S 0 _ (law_hashB P d N K _ fun i hi => hS _ (vHash_scr o a b c i hi))

theorem plc_mmB (o a b : Fin 82) (h : Function.Injective (vMm o a b)) (m n l : ℕ) (S : Store 82)
    (hS : Blank20 S) (ha : (S a).length = m * n * (N * K)) (hb : (S b).length = n * l * (N * K)) :
    (frame ⟨vMm o a b, h⟩ (mmB m n l N K)).law S =
      PMF.pure (Function.update S o (matMulW N K m n l (S a) (S b))) :=
  law_frame_upd _ _ S 0 _ (law_mmB m n l N K _ (fun i hi => hS _ (vMm_scr o a b i hi)) ha hb)

theorem plc_addB (o a b : Fin 82) (h : Function.Injective (vAdd o a b)) (L : ℕ) (S : Store 82)
    (hS : Blank20 S) (ha : (S a).length = L * N * K) (hb : (S b).length = L * N * K) :
    (frame ⟨vAdd o a b, h⟩ (addB L N K)).law S =
      PMF.pure (Function.update S o (matAddW N K L (S a) (S b))) :=
  law_frame_upd _ _ S 0 _ (law_addB L N K _ (fun i hi => hS _ (vAdd_scr o a b i hi)) ha hb)

theorem plc_subB (o a b : Fin 82) (h : Function.Injective (vAdd o a b)) (L : ℕ) (S : Store 82)
    (hS : Blank20 S) (ha : (S a).length = L * N * K) (hb : (S b).length = L * N * K) :
    (frame ⟨vAdd o a b, h⟩ (subB L N K)).law S =
      PMF.pure (Function.update S o (matSubW N K L (S a) (S b))) :=
  law_frame_upd _ _ S 0 _ (law_subB L N K _ (fun i hi => hS _ (vAdd_scr o a b i hi)) ha hb)

theorem plc_getB (o a : Fin 82) (h : Function.Injective (vGet o a)) (off L : ℕ) (S : Store 82)
    (hS : Blank20 S) :
    (frame ⟨vGet o a, h⟩ (getB off L)).law S =
      PMF.pure (Function.update S o (takeD L ((S a).drop off))) :=
  law_frame_upd _ _ S 0 _ (law_getB off L _ fun i hi => hS _ (vGet_scr o a i hi))

theorem plc_joinB (o a b c : Fin 82) (h : Function.Injective (vJoin o a b c)) (x y z : ℕ)
    (S : Store 82) (hS : Blank20 S) :
    (frame ⟨vJoin o a b c, h⟩ (joinB x y z)).law S =
      PMF.pure (Function.update S o (takeD x (S a) ++ takeD y (S b) ++ takeD z (S c))) :=
  law_frame_upd _ _ S 0 _ (law_joinB x y z _ fun i hi => hS _ (vJoin_scr o a b c i hi))

theorem plc_gadB (o : Fin 82) (h : Function.Injective (vGad o)) (S : Store 82) (hS : Blank20 S) :
    (frame ⟨vGad o, h⟩ (gadB N K k)).law S = PMF.pure (Function.update S o (gadW N K k)) :=
  law_frame_upd _ _ S 0 _ (law_gadB N K k _ fun i hi => hS _ (vGad_scr o i hi))

theorem plc_oneB (o : Fin 82) (h : Function.Injective (vOne o)) (hN : 0 < N) (hK : 0 < K)
    (S : Store 82) (hS : Blank20 S) :
    (frame ⟨vOne o, h⟩ (oneB N K)).law S = PMF.pure (Function.update S o (oneW N K)) :=
  law_frame_upd _ _ S 0 _ (law_oneB N K hN hK _ (hS 20 (by decide)))

end Laws

/-! ### Placed laws with the values named -/

section Named

variable {N K k : ℕ}

theorem plc_trB' (o a : Fin 82) (h : Function.Injective (vTr o a)) (m r s B Z : ℕ) (S : Store 82)
    (hS : Blank20 S) {A v : List Bool} (ha : S a = A) (hv : trW m r s B Z A = v) :
    (frame ⟨vTr o a, h⟩ (trB m r s B Z)).law S = PMF.pure (Function.update S o v) := by
  rw [plc_trB o a h m r s B Z S hS, ha, hv]

theorem plc_selB' (o a b c : Fin 82) (h : Function.Injective (vSel o a b c)) (n B : ℕ) (S : Store 82)
    (hS : Blank20 S) {X Y Z v : List Bool} (ha : S a = X) (hb : S b = Y) (hc : S c = Z)
    (hv : selW n B X Y Z = v) :
    (frame ⟨vSel o a b c, h⟩ (selB n B)).law S = PMF.pure (Function.update S o v) := by
  rw [plc_selB o a b c h n B S hS, ha, hb, hc, hv]

theorem plc_hashB' (o a b c : Fin 82) (h : Function.Injective (vHash o a b c)) (P d : ℕ)
    (S : Store 82) (hS : Blank20 S) {X Y Z v : List Bool} (ha : S a = X) (hb : S b = Y)
    (hc : S c = Z) (hv : hashW P d N K X Y Z = v) :
    (frame ⟨vHash o a b c, h⟩ (hashB P d N K)).law S = PMF.pure (Function.update S o v) := by
  rw [plc_hashB o a b c h P d S hS, ha, hb, hc, hv]

theorem plc_mmB' (o a b : Fin 82) (h : Function.Injective (vMm o a b)) (m n l : ℕ) (S : Store 82)
    (hS : Blank20 S) {X Y v : List Bool} (ha : S a = X) (hb : S b = Y)
    (hx : X.length = m * n * (N * K)) (hy : Y.length = n * l * (N * K))
    (hv : matMulW N K m n l X Y = v) :
    (frame ⟨vMm o a b, h⟩ (mmB m n l N K)).law S = PMF.pure (Function.update S o v) := by
  rw [plc_mmB o a b h m n l S hS (by rw [ha]; exact hx) (by rw [hb]; exact hy), ha, hb, hv]

theorem plc_addB' (o a b : Fin 82) (h : Function.Injective (vAdd o a b)) (L : ℕ) (S : Store 82)
    (hS : Blank20 S) {X Y v : List Bool} (ha : S a = X) (hb : S b = Y)
    (hx : X.length = L * N * K) (hy : Y.length = L * N * K) (hv : matAddW N K L X Y = v) :
    (frame ⟨vAdd o a b, h⟩ (addB L N K)).law S = PMF.pure (Function.update S o v) := by
  rw [plc_addB o a b h L S hS (by rw [ha]; exact hx) (by rw [hb]; exact hy), ha, hb, hv]

theorem plc_subB' (o a b : Fin 82) (h : Function.Injective (vAdd o a b)) (L : ℕ) (S : Store 82)
    (hS : Blank20 S) {X Y v : List Bool} (ha : S a = X) (hb : S b = Y)
    (hx : X.length = L * N * K) (hy : Y.length = L * N * K) (hv : matSubW N K L X Y = v) :
    (frame ⟨vAdd o a b, h⟩ (subB L N K)).law S = PMF.pure (Function.update S o v) := by
  rw [plc_subB o a b h L S hS (by rw [ha]; exact hx) (by rw [hb]; exact hy), ha, hb, hv]

theorem plc_getB' (o a : Fin 82) (h : Function.Injective (vGet o a)) (off L : ℕ) (S : Store 82)
    (hS : Blank20 S) {W v : List Bool} (ha : S a = W) (hv : takeD L (W.drop off) = v) :
    (frame ⟨vGet o a, h⟩ (getB off L)).law S = PMF.pure (Function.update S o v) := by
  rw [plc_getB o a h off L S hS, ha, hv]

theorem plc_joinB' (o a b c : Fin 82) (h : Function.Injective (vJoin o a b c)) (x y z : ℕ)
    (S : Store 82) (hS : Blank20 S) {X Y Z v : List Bool} (ha : S a = X) (hb : S b = Y)
    (hc : S c = Z) (hv : takeD x X ++ takeD y Y ++ takeD z Z = v) :
    (frame ⟨vJoin o a b c, h⟩ (joinB x y z)).law S = PMF.pure (Function.update S o v) := by
  rw [plc_joinB o a b c h x y z S hS, ha, hb, hc, hv]

end Named

end AdvancedEncryption.RingBTVW.Prog
