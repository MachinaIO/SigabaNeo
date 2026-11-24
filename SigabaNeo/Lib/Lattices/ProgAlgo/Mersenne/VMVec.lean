import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VMDot

/-!
# Vector operations on the ring-word machine

Vectors of ring words are held *flattened* in a register (`vs.flatten`, every word of `N K` bits).
Entrywise operations stream their operands (registers `110`, `111`) and shift the results into a
buffer (register `112`, initialized from a buffer template of the right width):

* `vecAddC cnt buf`, `vecSubC cnt buf`: `112 := (zipWith addRMW us vs).flatten` (resp. `subRMW`),
  `|w cnt|` entries, the buffer template `buf` of `|w cnt| · N K` bits (**`exec_vecAddC`**,
  `exec_vecSubC`);
* `vecAutC cnt buf t`: `112 := (us.map (autMW N K |w t|)).flatten` (**`exec_vecAutC`**).

Scratch: `113 … 119`. Generic helpers for buffers: `buf_push`, `buf_final`.
-/

namespace SigabaNeo.Tape

namespace RingVM

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {N K : ℕ}

/-! ### Buffers -/

theorem take_succ_getD {L : List (List Bool)} {i : ℕ} (hi : i < L.length) :
    L.take (i + 1) = L.take i ++ [L.getD i []] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]; rfl

/-- Pushing the word `i` of `L` into a buffer holding the first `i`. -/
theorem buf_push {B : List Bool} {L : List (List Bool)} {m i : ℕ}
    (hL : ∀ y ∈ L, y.length = m) (hi : i < L.length) :
    ((B ++ (L.take i).flatten).drop (i * m) ++ L.getD i []).drop m =
      (B ++ (L.take (i + 1)).flatten).drop ((i + 1) * m) := by
  have hl : (L.take i).length = i := by simp; omega
  have hx : (L.getD i []).length = m := hL _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  have := drop_append_flatten_succ (b := B) (vs := L.take i) hx (fun y hy => hL y (List.mem_of_mem_take hy))
  rw [hl] at this
  rw [this, ← take_succ_getD hi, List.length_take, min_eq_left (by omega)]

/-- After all words were pushed into a buffer of their total width. -/
theorem buf_final {B : List Bool} {L : List (List Bool)} {m : ℕ} (hB : B.length = L.length * m) :
    (B ++ (L.take L.length).flatten).drop (L.length * m) = L.flatten := by
  rw [List.take_length, drop_append_flatten hB]

theorem flatten_length_eq {L : List (List Bool)} {m : ℕ} (hL : ∀ y ∈ L, y.length = m) :
    L.flatten.length = L.length * m := length_flatten_of hL

theorem mem_getD {L : List (List Bool)} {i : ℕ} (hi : i < L.length) : L.getD i [] ∈ L := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

/-! ### Loops in steps, moves -/

/-- **A loop advancing an indexed invariant by `s` per round**, below the bound `T`; the invariant
ignores the counter `c`. -/
theorem exec_rep_step (c : Fin 200) (body : Code) (hc : c ∉ wr body) (P : ℕ → St → Prop)
    (hP : ∀ n w v, P n w → P n (Function.update w c v)) (s T : ℕ)
    (hb : ∀ n w, n + s ≤ T → P n w → P (n + s) (exec N K body w)) (n : ℕ) (w : St)
    (hT : n + (w c).length * s ≤ T) (h : P n w) :
    P (n + (w c).length * s) (exec N K (.rep c body) w) := by
  have := exec_rep_inv (N := N) (K := K) c body hc (fun i w' => P (n + i * s) w') w
    (by simpa using h) (fun i hi w' hw' _ => by
      have h1 := hb _ _ (by nlinarith) (hP _ _ ((w' c).tail) hw')
      rwa [show n + i * s + s = n + (i + 1) * s by ring] at h1)
  exact this

/-- **Move** a word of the template's width from the front of a stream into a buffer. -/
theorem exec_mv_move {d s c : Fin 200} (h : ¬(d = s ∨ d = c ∨ s = c)) {w : St} {x L : List Bool}
    (hx : x.length = (w c).length) (hs : w s = x ++ L) :
    exec N K (.mv d s c) w = Function.update (Function.update w s L) d ((w d ++ x).drop x.length) := by
  simp only [exec, if_neg h, hs, ValVM.shiftIn]
  rw [takeD_eq_take (by simp; omega), ← hx, List.take_left, List.drop_left]

/-! ### Entrywise binary operations -/

variable [NeZero (2 ^ K - 1)]

/-- The round: pop `u`, `v`, `116 := op u v`, push `116`. -/
def bin2 (op : Code) : Code := ofList [.mv 113 110 2, .mv 114 111 2, op, .mv 112 116 2]

/-- The loop, counter `117`, buffer template `118`. -/
def map2Core (op : Code) : Code := ofList [.cp 112 118, .cp 113 2, .cp 114 2, .rep 117 (bin2 op)]

/-- `112 := (zipWith addRMW 110 111).flatten`. -/
def vecAddC (cnt buf : Fin 200) : Code := ofList [.cp 117 cnt, .cp 118 buf, map2Core (.add 116 113 114)]

/-- `112 := (zipWith subRMW 110 111).flatten`. -/
def vecSubC (cnt buf : Fin 200) : Code := ofList [.cp 117 cnt, .cp 118 buf, map2Core (.sub 116 113 114)]

theorem wr_map2Core (op : Code) : wr (map2Core op) =
    [112, 113, 114, 117, 113, 110, 114, 111] ++ wr op ++ [112, 116] := by
  simp [map2Core, bin2, wr, wr_ofList]

theorem exec_map2Core (op : Code) (f : List Bool → List Bool → List Bool) (hwr : wr op = [116])
    (w : St)
    (hop : ∀ w' : St, w' 119 = w 119 →
      exec N K op w' = Function.update w' 116 (f (opd N K (w' 113)) (opd N K (w' 114))))
    (hf : ∀ a b, a.length = N * K → (f a b).length = N * K) (hc : Consts N K w)
    {us vs : List (List Bool)} (hus : ∀ x ∈ us, x.length = N * K) (hvs : ∀ x ∈ vs, x.length = N * K)
    (hl : us.length = vs.length) (h110 : w 110 = us.flatten) (h111 : w 111 = vs.flatten)
    (h117 : (w 117).length = us.length) (h118 : (w 118).length = us.length * (N * K)) :
    (exec N K (map2Core op) w) 112 = (List.zipWith f us vs).flatten ∧
      ∀ j, j ∉ wr (map2Core op) → (exec N K (map2Core op) w) j = w j := by
  set L := List.zipWith f us vs with hL
  have hLl : L.length = us.length := by simp [hL, hl]
  have hLw : ∀ y ∈ L, y.length = N * K := by
    intro y hy
    rw [hL, List.mem_iff_getElem] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [List.getElem_zipWith]
    exact hf _ _ (hus _ (List.getElem_mem _))
  set w1 := Function.update (Function.update (Function.update w 112 (w 118)) 113
    (List.replicate (N * K) false)) 114 (List.replicate (N * K) false) with hw1
  have e : exec N K (map2Core op) w = exec N K (.rep 117 (bin2 op)) w1 := by
    simp only [map2Core, exec_ofList_cons, exec_ofList_nil, exec, hw1,
      Function.update_of_ne (show (2 : Fin 200) ≠ 112 by decide),
      Function.update_of_ne (show (2 : Fin 200) ≠ 113 by decide), hc.zero]
  have hwrb : wr (bin2 op) = [113, 110, 114, 111] ++ [116] ++ [112, 116] := by
    simp [bin2, wr, wr_ofList, hwr]
  have h117' : (w1 117).length = us.length := by simp [hw1, h117]
  let P : ℕ → St → Prop := fun i w' =>
    Consts N K w' ∧ w' 110 = (us.drop i).flatten ∧ w' 111 = (vs.drop i).flatten ∧
      (w' 113).length = N * K ∧ (w' 114).length = N * K ∧
      w' 112 = (w 118 ++ (L.take i).flatten).drop (i * (N * K)) ∧
      ∀ j, j ∉ wr (map2Core op) → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 117 (bin2 op) (by rw [hwrb]; decide) P w1
    ⟨consts_update (consts_update (consts_update hc 112 (by decide) _) 113 (by decide) _) 114
        (by decide) _, by simp [hw1, h110], by simp [hw1, h111], by simp [hw1], by simp [hw1],
      by simp [hw1],
      fun j hj => by
        have h1 : j ≠ 112 := fun h => hj (by rw [h]; simp [map2Core, wr, wr_ofList])
        have h2 : j ≠ 113 := fun h => hj (by rw [h]; simp [map2Core, wr, wr_ofList])
        have h3 : j ≠ 114 := fun h => hj (by rw [h]; simp [map2Core, wr, wr_ofList])
        rw [hw1, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨hc', p110, p111, p113, p114, p112, pf⟩ := hw'
      rw [h117'] at hi
      have hiv : i < vs.length := by omega
      set s := Function.update w' 117 (w' 117).tail with hs
      have hsc : Consts N K s := consts_update hc' 117 (by decide) _
      have hu := hus _ (mem_getD hi)
      have hv := hvs _ (mem_getD hiv)
      have hLi : (L.getD i []).length = N * K := hLw _ (mem_getD (by rw [hLl]; exact hi))
      have hfv : f (us.getD i []) (vs.getD i []) = L.getD i [] := by
        rw [hL, List.getD_eq_getElem (List.zipWith f us vs) _ (by simp; omega),
          List.getElem_zipWith, List.getD_eq_getElem us _ hi, List.getD_eq_getElem vs _ hiv]
      set u := us.getD i [] with hu_def
      set v := vs.getD i [] with hv_def
      set y := L.getD i [] with hy_def
      have s1 := exec_mv_pop (N := N) (K := K) (d := 113) (s := 110) (c := 2) (w := s) (by decide)
        (v := u) (L := (us.drop (i + 1)).flatten)
        (by rw [hsc.zero]; simp [hs, p113]) (by rw [hsc.zero, List.length_replicate]; exact hu)
        (by simp only [hs, Function.update_of_ne (show (110 : Fin 200) ≠ 117 by decide), p110]
            exact flatten_drop_succ hi)
      set s1' := Function.update (Function.update s 110 (us.drop (i + 1)).flatten) 113 (u)
      have hs1c : Consts N K s1' := consts_update (consts_update hsc 110 (by decide) _) 113 (by decide) _
      have s2 := exec_mv_pop (N := N) (K := K) (d := 114) (s := 111) (c := 2) (w := s1') (by decide)
        (v := v) (L := (vs.drop (i + 1)).flatten)
        (by rw [hs1c.zero]; simp [s1', hs, p114]) (by rw [hs1c.zero, List.length_replicate]; exact hv)
        (by simp only [s1', hs, Function.update_of_ne (show (111 : Fin 200) ≠ 117 by decide),
              Function.update_of_ne (show (111 : Fin 200) ≠ 110 by decide),
              Function.update_of_ne (show (111 : Fin 200) ≠ 113 by decide), p111]
            exact flatten_drop_succ hiv)
      set s2' := Function.update (Function.update s1' 111 (vs.drop (i + 1)).flatten) 114 (v)
      have hs2c : Consts N K s2' := consts_update (consts_update hs1c 111 (by decide) _) 114 (by decide) _
      have s3 : exec N K op s2' = Function.update s2' 116 y := by
        have a0 : s2' 119 = w 119 := by
          simp only [s2', s1', hs, Function.update_apply, Fin.reduceEq, ↓reduceIte]
          exact pf 119 (by rw [wr_map2Core, hwr]; decide)
        have a1 : s2' 113 = u := by
          simp only [s2', s1', Function.update_apply, Fin.reduceEq, ↓reduceIte]
        have a2 : s2' 114 = v := by
          simp only [s2', Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [hop _ a0, ← hfv, a1, a2, opd_eq hu, opd_eq hv]
      set s3' := Function.update s2' 116 (y)
      have hs3c : Consts N K s3' := consts_update hs2c 116 (by decide) _
      have s4 := exec_mv_push (N := N) (K := K) (d := 112) (s := 116) (c := 2) (w := s3') (by decide)
        (by rw [hs3c.zero]; simp [s3', hLi])
      have ee : exec N K (bin2 op) s = Function.update (Function.update s3' 116 []) 112
          ((s3' 112 ++ s3' 116).drop (s3' 2).length) := by
        simp only [bin2, exec_ofList_cons, exec_ofList_nil]
        rw [s1, s2, s3, s4]
      rw [ee]
      have e112 : s3' 112 = (w 118 ++ (L.take i).flatten).drop (i * (N * K)) := by
        simp [s3', s2', s1', hs, p112]
      have e116 : s3' 116 = y := by simp [s3']
      refine ⟨consts_update (consts_update hs3c 116 (by decide) _) 112 (by decide) _, ?_, ?_, ?_, ?_,
        ?_, fun j hj => ?_⟩
      · simp [s3', s2', s1']
      · simp [s3', s2', s1']
      · simp [s3', s2', s1', hu]
      · simp [s3', s2', s1', hv]
      · rw [Function.update_self, e112, e116, hs3c.zero, List.length_replicate,
          buf_push hLw (by rw [hLl]; exact hi)]
      · have hjb : j ∉ wr (bin2 op) := fun hm => hj (by
          simp only [map2Core, wr, wr_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.mem_append, List.mem_cons]
          right; right; right; right; exact hm)
        have hne : ∀ r : Fin 200, r ∈ wr (bin2 op) → j ≠ r := fun r hr h => hjb (h ▸ hr)
        rw [hwrb] at hne
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hne
        have h117 : j ≠ 117 := fun h => hj (by rw [h]; simp [map2Core, wr, wr_ofList])
        simp only [s3', s2', s1', hs, Function.update_apply]
        rw [if_neg (hne 112 (by simp)), if_neg (hne 116 (by simp)), if_neg (hne 116 (by simp)),
          if_neg (hne 114 (by simp)), if_neg (hne 111 (by simp)), if_neg (hne 113 (by simp)),
          if_neg (hne 110 (by simp)), if_neg h117]
        exact pf j hj)
  rw [h117'] at hP
  obtain ⟨_, _, _, _, _, p112, pf⟩ := hP
  refine ⟨?_, fun j hj => by rw [e]; exact pf j hj⟩
  rw [e, p112, ← hLl, buf_final (by rw [hLl, h118])]

/-- **Entrywise sum.** -/
theorem exec_vecAddC (w : St) (hc : Consts N K w) (cnt buf : Fin 200) (hbuf' : buf ≠ 117)
    {us vs : List (List Bool)} (hus : ∀ x ∈ us, x.length = N * K) (hvs : ∀ x ∈ vs, x.length = N * K)
    (hl : us.length = vs.length) (h110 : w 110 = us.flatten) (h111 : w 111 = vs.flatten)
    (hcnt : (w cnt).length = us.length) (hbuf : (w buf).length = us.length * (N * K)) :
    (exec N K (vecAddC cnt buf) w) 112 = (List.zipWith (addRMW N K) us vs).flatten ∧
      ∀ j, j ∉ wr (vecAddC cnt buf) → (exec N K (vecAddC cnt buf) w) j = w j := by
  set w1 := Function.update (Function.update w 117 (w cnt)) 118 (w buf) with hw1
  have e : exec N K (vecAddC cnt buf) w = exec N K (map2Core (.add 116 113 114)) w1 := by
    simp only [vecAddC, exec_ofList_cons, exec_ofList_nil, exec, hw1,
      Function.update_of_ne hbuf']
  have hc1 : Consts N K w1 := consts_update (consts_update hc 117 (by decide) _) 118 (by decide) _
  have hb : (w1 118).length = us.length * (N * K) := by
    simp only [hw1, Function.update_self]; exact hbuf
  have ha : (w1 117).length = us.length := by
    simp only [hw1, Function.update_of_ne (show (117 : Fin 200) ≠ 118 by decide),
      Function.update_self]; exact hcnt
  obtain ⟨r1, r2⟩ := exec_map2Core (N := N) (K := K) (.add 116 113 114) (addRMW N K) rfl w1
    (fun _ _ => rfl) (fun a b ha => length_addRMW N K (by simpa using ha) b) hc1 hus hvs hl
    (by simp [hw1, h110]) (by simp [hw1, h111]) ha hb
  refine ⟨by rw [e]; exact r1, fun j hj => ?_⟩
  rw [e, r2 j (fun hm => hj (by
    simp only [vecAddC, wr, wr_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, List.mem_cons]
    right; right; exact hm))]
  have h1 : j ≠ 117 := fun h => hj (by rw [h]; simp [vecAddC, wr, wr_ofList])
  have h2 : j ≠ 118 := fun h => hj (by rw [h]; simp [vecAddC, wr, wr_ofList])
  rw [hw1, Function.update_of_ne h2, Function.update_of_ne h1]

/-- **Entrywise difference.** -/
theorem exec_vecSubC (w : St) (hc : Consts N K w) (cnt buf : Fin 200) (hbuf' : buf ≠ 117)
    {us vs : List (List Bool)} (hus : ∀ x ∈ us, x.length = N * K) (hvs : ∀ x ∈ vs, x.length = N * K)
    (hl : us.length = vs.length) (h110 : w 110 = us.flatten) (h111 : w 111 = vs.flatten)
    (hcnt : (w cnt).length = us.length) (hbuf : (w buf).length = us.length * (N * K)) :
    (exec N K (vecSubC cnt buf) w) 112 = (List.zipWith (subRMW N K) us vs).flatten ∧
      ∀ j, j ∉ wr (vecSubC cnt buf) → (exec N K (vecSubC cnt buf) w) j = w j := by
  set w1 := Function.update (Function.update w 117 (w cnt)) 118 (w buf) with hw1
  have e : exec N K (vecSubC cnt buf) w = exec N K (map2Core (.sub 116 113 114)) w1 := by
    simp only [vecSubC, exec_ofList_cons, exec_ofList_nil, exec, hw1,
      Function.update_of_ne hbuf']
  have hc1 : Consts N K w1 := consts_update (consts_update hc 117 (by decide) _) 118 (by decide) _
  have hb : (w1 118).length = us.length * (N * K) := by
    simp only [hw1, Function.update_self]; exact hbuf
  have ha : (w1 117).length = us.length := by
    simp only [hw1, Function.update_of_ne (show (117 : Fin 200) ≠ 118 by decide),
      Function.update_self]; exact hcnt
  obtain ⟨r1, r2⟩ := exec_map2Core (N := N) (K := K) (.sub 116 113 114) (subRMW N K) rfl w1
    (fun _ _ => rfl) (fun a b ha => length_subRMW N K (by simpa using ha) b) hc1 hus hvs hl
    (by simp [hw1, h110]) (by simp [hw1, h111]) ha hb
  refine ⟨by rw [e]; exact r1, fun j hj => ?_⟩
  rw [e, r2 j (fun hm => hj (by
    simp only [vecSubC, wr, wr_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, List.mem_cons]
    right; right; exact hm))]
  have h1 : j ≠ 117 := fun h => hj (by rw [h]; simp [vecSubC, wr, wr_ofList])
  have h2 : j ≠ 118 := fun h => hj (by rw [h]; simp [vecSubC, wr, wr_ofList])
  rw [hw1, Function.update_of_ne h2, Function.update_of_ne h1]

/-- `112 := (map (autMW N K |w t|) 110).flatten`. -/
def vecAutC (cnt buf t : Fin 200) : Code :=
  ofList [.cp 117 cnt, .cp 118 buf, .cp 119 t, .cp 111 110, map2Core (.aut 116 113 119)]

/-- **Entrywise automorphism** `σ_{|t|}`. -/
theorem exec_vecAutC (hN : 0 < N) (w : St) (hc : Consts N K w) (cnt buf t : Fin 200)
    (hbuf' : buf ≠ 117) (ht1 : t ≠ 117) (ht2 : t ≠ 118)
    {us : List (List Bool)} (hus : ∀ x ∈ us, x.length = N * K) (h110 : w 110 = us.flatten)
    (hcnt : (w cnt).length = us.length) (hbuf : (w buf).length = us.length * (N * K)) :
    (exec N K (vecAutC cnt buf t) w) 112 = (us.map (autMW N K (w t).length)).flatten ∧
      ∀ j, j ∉ wr (vecAutC cnt buf t) → (exec N K (vecAutC cnt buf t) w) j = w j := by
  set w1 := Function.update (Function.update (Function.update (Function.update w 117 (w cnt)) 118
    (w buf)) 119 (w t)) 111 (w 110) with hw1
  have e : exec N K (vecAutC cnt buf t) w = exec N K (map2Core (.aut 116 113 119)) w1 := by
    simp only [vecAutC, exec_ofList_cons, exec_ofList_nil, exec, hw1,
      Function.update_of_ne hbuf', Function.update_of_ne ht1, Function.update_of_ne ht2,
      Function.update_of_ne (show (110 : Fin 200) ≠ 117 by decide),
      Function.update_of_ne (show (110 : Fin 200) ≠ 118 by decide),
      Function.update_of_ne (show (110 : Fin 200) ≠ 119 by decide)]
  have hc1 : Consts N K w1 := consts_update (consts_update (consts_update (consts_update hc 117
    (by decide) _) 118 (by decide) _) 119 (by decide) _) 111 (by decide) _
  have hb : (w1 118).length = us.length * (N * K) := by
    simp only [hw1, Function.update_of_ne (show (118 : Fin 200) ≠ 111 by decide),
      Function.update_of_ne (show (118 : Fin 200) ≠ 119 by decide), Function.update_self]; exact hbuf
  have ha : (w1 117).length = us.length := by
    simp only [hw1, Function.update_of_ne (show (117 : Fin 200) ≠ 111 by decide),
      Function.update_of_ne (show (117 : Fin 200) ≠ 119 by decide),
      Function.update_of_ne (show (117 : Fin 200) ≠ 118 by decide), Function.update_self]; exact hcnt
  have h119 : w1 119 = w t := by
    simp only [hw1, Function.update_of_ne (show (119 : Fin 200) ≠ 111 by decide),
      Function.update_self]
  obtain ⟨r1, r2⟩ := exec_map2Core (N := N) (K := K) (.aut 116 113 119)
    (fun a _ => autMW N K (w t).length a) rfl w1
    (fun w' h' => by simp only [exec, h', h119]) (fun a _ _ => length_autMW N K _ a hN) hc1 hus hus
    rfl (by simp [hw1, h110]) (by simp [hw1, h110]) ha hb
  refine ⟨?_, fun j hj => ?_⟩
  · rw [e, r1]
    congr 1
    clear r1 r2 e
    induction us with
    | nil => rfl
    | cons x us ih => simp [List.zipWith]
  rw [e, r2 j (fun hm => hj (by
    simp only [vecAutC, wr, wr_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, List.mem_cons]
    right; right; right; right; exact hm))]
  have h1 : j ≠ 117 := fun h => hj (by rw [h]; simp [vecAutC, wr, wr_ofList])
  have h2 : j ≠ 118 := fun h => hj (by rw [h]; simp [vecAutC, wr, wr_ofList])
  have h3 : j ≠ 119 := fun h => hj (by rw [h]; simp [vecAutC, wr, wr_ofList])
  have h4 : j ≠ 111 := fun h => hj (by rw [h]; simp [vecAutC, wr, wr_ofList])
  rw [hw1, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
    Function.update_of_ne h1]

end RingVM

end SigabaNeo.Tape
