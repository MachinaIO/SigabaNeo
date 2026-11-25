import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMDot
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMLib

/-!
# `RingVM` kernels of the reduction's public data (package G2, `pubP`/`chalP`)

* **`hashC`**: the binary hash `Σ_{j<m} [z_j] · V_j` of a vector `V` (register `xV`, `m` words,
  kept) with the next `m` bits `z` of the stream `xZ` (consumed), into `xAcc`
  (**`exec_hashC`**); every programming column `zr i` of the reduction enters the public data
  only through such hashes (`hpOf`, `ct2`, `cb2`);
* buffers: `bufW b₀ ys` (the shift register `b₀` after the words `ys` were shifted in) and
  **`exec_push`**.
-/

namespace SigabaNeo.Tape.RingVM.Hash
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo

variable {N K : ℕ}

/-! ### Buffers -/

/-- The shift register `b₀` after the words `ys` (of `W` bits) were shifted in. -/
def bufW (W : ℕ) (b₀ : List Bool) (ys : List (List Bool)) : List Bool :=
  (b₀ ++ ys.flatten).drop (ys.length * W)

/-- **Pushing a word into a buffer.** -/
theorem exec_push {d s c : Fin 200} (h : ¬(d = s ∨ d = c ∨ s = c)) {w : St} {W : ℕ}
    {b₀ : List Bool} {ys : List (List Bool)} (hys : ∀ y ∈ ys, y.length = W)
    (hd : w d = bufW W b₀ ys) (hs : (w s).length = W) (hc : (w c).length = W) :
    exec N K (.mv d s c) w =
      Function.update (Function.update w s []) d (bufW W b₀ (ys ++ [w s])) := by
  rw [exec_mv_push h (by rw [hs, hc]), hd, hc, bufW, bufW]
  rw [drop_append_flatten_succ hs hys]

theorem bufW_full {W : ℕ} {b₀ : List Bool} {ys : List (List Bool)} (hys : ∀ y ∈ ys, y.length = W)
    (hb : b₀.length = ys.length * W) : bufW W b₀ ys = ys.flatten :=
  drop_append_flatten hb

theorem bufW_nil (W : ℕ) (b₀ : List Bool) : bufW W b₀ [] = b₀ := by simp [bufW]

theorem length_bufW {W : ℕ} {b₀ : List Bool} {ys : List (List Bool)} (hys : ∀ y ∈ ys, y.length = W) :
    (bufW W b₀ ys).length = b₀.length := by
  rw [bufW, List.length_drop, List.length_append, length_flatten_of hys]; omega

/-! ### The binary hash -/

/-- The registers of the hash. -/
@[simp] abbrev xV : Fin 200 := 150
@[simp] abbrev xZ : Fin 200 := 151
@[simp] abbrev xCm : Fin 200 := 152
@[simp] abbrev xVc : Fin 200 := 153
@[simp] abbrev xCc : Fin 200 := 154
@[simp] abbrev xAcc : Fin 200 := 155
@[simp] abbrev xv : Fin 200 := 156
@[simp] abbrev xBit : Fin 200 := 157
@[simp] abbrev xC1 : Fin 200 := 158
@[simp] abbrev xCNK : Fin 200 := 159
@[simp] abbrev xZero : Fin 200 := 160

/-- One round: pop `V_j`, pop `z_j`, add `V_j` when `z_j`. -/
def hashBody : Code :=
  .seq (.mv xv xVc xCNK) (.seq (.mv xBit xZ xC1) (.ifb xBit (.add xAcc xAcc xv) .nop))

/-- **The binary hash**: `xAcc := Σ_{j < |xCm|} [z_j] V_j`. -/
def hashC : Code :=
  .seq (.cp xVc xV) (.seq (.cp xCc xCm) (.seq (.cp xAcc xZero) (.rep xCc hashBody)))

/-- The value of a hash. -/
noncomputable def hashV (vs : List (List Bool)) (zs : List Bool) : RM N K :=
  (List.zipWith (fun v z => if z then decRM N K v else 0) vs zs).sum

theorem hashV_snoc (vs : List (List Bool)) (zs : List Bool) (hl : zs.length = vs.length)
    (v : List Bool) (z : Bool) :
    hashV (N := N) (K := K) (vs ++ [v]) (zs ++ [z]) =
      hashV vs zs + if z then decRM N K v else 0 := by
  rw [hashV, hashV, List.zipWith_append (by omega)]
  simp

theorem wr_hashBody : wr hashBody = [xv, xVc, xBit, xZ, xAcc] := rfl

theorem take_succ_of_lt {α : Type} {l : List α} {i : ℕ} (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]; rfl

/-- **The hash.** -/
theorem exec_hashC (w : St) (vs : List (List Bool)) (zs rest : List Bool)
    (hvs : ∀ v ∈ vs, v.length = N * K)
    (hV : w xV = vs.flatten) (hZ : w xZ = zs ++ rest) (hlen : zs.length = vs.length)
    (hCm : (w xCm).length = vs.length) (hC1 : (w xC1).length = 1) (hCNK : (w xCNK).length = N * K)
    (hZero : w xZero = List.replicate (N * K) false) (hv : (w xv).length = N * K)
    (hb : (w xBit).length = 1) :
    decRM N K (exec N K hashC w xAcc) = hashV vs zs ∧ (exec N K hashC w xAcc).length = N * K ∧
      exec N K hashC w xZ = rest ∧ (exec N K hashC w xv).length = N * K ∧
      (exec N K hashC w xBit).length = 1 ∧
      ∀ j, j ≠ xVc → j ≠ xCc → j ≠ xAcc → j ≠ xv → j ≠ xBit → j ≠ xZ →
        exec N K hashC w j = w j := by
  set w1 := Function.update (Function.update (Function.update w xVc (w xV)) xCc (w xCm)) xAcc
    (w xZero) with hw1
  have e1 : exec N K hashC w = exec N K (.rep xCc hashBody) w1 := rfl
  -- the invariant after `i` rounds
  let P : ℕ → St → Prop := fun i w' =>
    w' xVc = (vs.drop i).flatten ∧ w' xZ = zs.drop i ++ rest ∧
      (w' xAcc).length = N * K ∧ decRM N K (w' xAcc) = hashV (vs.take i) (zs.take i) ∧
      (w' xv).length = N * K ∧ (w' xBit).length = 1 ∧
      ∀ j, j ≠ xVc → j ≠ xCc → j ≠ xAcc → j ≠ xv → j ≠ xBit → j ≠ xZ → w' j = w j
  have hc : xCc ∉ wr hashBody := by rw [wr_hashBody]; decide
  have h0 : P 0 w1 := by
    refine ⟨by simp [Function.update_apply, w1, hV], by simp [Function.update_apply, w1, hZ], by simp [Function.update_apply, w1, hZero], ?_, by simp [Function.update_apply, w1, hv],
      by simp [Function.update_apply, w1, hb], fun j h1 h2 h3 _ _ _ => by simp [Function.update_apply, w1, h1, h2, h3]⟩
    simp [Function.update_apply, w1, hZero, hashV, decRM_replicate]
  have hlenc : (w1 xCc).length = vs.length := by simp [Function.update_apply, w1, hCm]
  have key := exec_rep_inv (N := N) (K := K) xCc hashBody hc P w1 h0 (fun i hi w' hP _ => by
    rw [hlenc] at hi
    obtain ⟨hVc, hZ', hAl, hAv, hvl, hbl, hfr⟩ := hP
    set u := Function.update w' xCc (w' xCc).tail
    have hu : ∀ j, j ≠ xCc → u j = w' j := fun j hj => Function.update_of_ne hj _ _
    -- pop `V_i`
    have hvi : vs[i] ∈ vs := List.getElem_mem hi
    have hdrop : (vs.drop i).flatten = vs[i] ++ (vs.drop (i + 1)).flatten := by
      rw [List.drop_eq_getElem_cons hi, List.flatten_cons]
    have hCNK' : (u xCNK).length = N * K := by rw [hu _ (by decide), hfr _ (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hCNK
    have hC1' : (u xC1).length = 1 := by rw [hu _ (by decide), hfr _ (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC1
    have s1 := exec_mv_pop (N := N) (K := K) (d := xv) (s := xVc) (c := xCNK) (by decide)
      (w := u) (v := vs[i]) (L := (vs.drop (i + 1)).flatten)
      (by rw [hu _ (by decide), hvl, hCNK']) (by rw [hvs _ hvi, hCNK'])
      (by rw [hu _ (by decide), hVc, hdrop])
    set u1 := Function.update (Function.update u xVc (vs.drop (i + 1)).flatten) xv vs[i]
    -- pop `z_i`
    have hzi : i < zs.length := by omega
    have hzdrop : zs.drop i ++ rest = [zs[i]] ++ (zs.drop (i + 1) ++ rest) := by
      rw [List.drop_eq_getElem_cons hzi]; rfl
    have u1Bit : u1 xBit = w' xBit := by simp [u1, u, Function.update_apply]
    have u1C1 : u1 xC1 = u xC1 := by simp [u1, Function.update_apply]
    have u1Z : u1 xZ = w' xZ := by simp [u1, u, Function.update_apply]
    have s2 := exec_mv_pop (N := N) (K := K) (d := xBit) (s := xZ) (c := xC1) (by decide)
      (w := u1) (v := [zs[i]]) (L := zs.drop (i + 1) ++ rest)
      (by rw [u1Bit, u1C1, hbl, hC1']) (by rw [u1C1, hC1']; rfl)
      (by rw [u1Z, hZ', hzdrop])
    set u2 := Function.update (Function.update u1 xZ (zs.drop (i + 1) ++ rest)) xBit [zs[i]]
    have v2Vc : u2 xVc = (vs.drop (i + 1)).flatten := by simp [u2, u1, Function.update_apply]
    have v2Z : u2 xZ = zs.drop (i + 1) ++ rest := by simp [u2, Function.update_apply]
    have v2Acc : u2 xAcc = w' xAcc := by simp [u2, u1, u, Function.update_apply]
    have v2v : u2 xv = vs[i] := by simp [u2, u1, Function.update_apply]
    have v2Bit : u2 xBit = [zs[i]] := by simp [u2]
    have v2fr : ∀ j, j ≠ xVc → j ≠ xCc → j ≠ xv → j ≠ xBit → j ≠ xZ → u2 j = w' j := by
      intro j h1 h2 h4 h5 h6
      simp only [u2, u1, u, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6]
    have ex : exec N K hashBody u = exec N K (.ifb xBit (.add xAcc xAcc xv) .nop) u2 := by
      show exec N K (.seq (.mv xBit xZ xC1) (.ifb xBit (.add xAcc xAcc xv) .nop))
        (exec N K (.mv xv xVc xCNK) u) = _
      rw [s1]
      show exec N K (.ifb xBit (.add xAcc xAcc xv) .nop) (exec N K (.mv xBit xZ xC1) u1) = _
      rw [s2]
    rw [ex]
    have htake : hashV (N := N) (K := K) (vs.take (i + 1)) (zs.take (i + 1)) =
        hashV (vs.take i) (zs.take i) + if zs[i] then decRM N K vs[i] else 0 := by
      rw [take_succ_of_lt hi, take_succ_of_lt hzi, hashV_snoc _ _ (by simp; omega)]
    have hvi' := hvs _ hvi
    by_cases hz : zs[i] = true
    · have ee : exec N K (.ifb xBit (.add xAcc xAcc xv) .nop) u2 =
          Function.update u2 xAcc (addRMW N K (w' xAcc) vs[i]) := by
        simp only [exec, v2Bit, hd, hz, List.headD_cons, if_true, v2Acc, v2v, opd_eq hAl, opd_eq hvi']
      rw [ee]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Function.update_of_ne (by decide), v2Vc]
      · rw [Function.update_of_ne (by decide), v2Z]
      · rw [Function.update_self, length_addRMW N K hAl]
      · rw [Function.update_self, decRM_addRMW hAl hvi', hAv, htake, if_pos hz]
      · rw [Function.update_of_ne (by decide), v2v, hvi']
      · rw [Function.update_of_ne (by decide), v2Bit]; rfl
      · intro j h1 h2 h3 h4 h5 h6
        rw [Function.update_of_ne h3, v2fr j h1 h2 h4 h5 h6, hfr j h1 h2 h3 h4 h5 h6]
    · have ee : exec N K (.ifb xBit (.add xAcc xAcc xv) .nop) u2 = u2 := by
        simp only [exec, v2Bit, hd, List.headD_cons, hz, Bool.false_eq_true, if_false]
      rw [ee]
      refine ⟨v2Vc, v2Z, by rw [v2Acc]; exact hAl, ?_, by rw [v2v, hvi'], by rw [v2Bit]; rfl, ?_⟩
      · rw [v2Acc, hAv, htake, if_neg hz, add_zero]
      · intro j h1 h2 h3 h4 h5 h6
        rw [v2fr j h1 h2 h4 h5 h6, hfr j h1 h2 h3 h4 h5 h6])
  rw [hlenc] at key
  obtain ⟨-, hZf, hAl, hAv, hvl, hbl, hfr⟩ := key
  rw [← e1] at hZf hAl hAv hvl hbl hfr
  refine ⟨?_, hAl, ?_, hvl, hbl, hfr⟩
  · rw [hAv, List.take_of_length_le le_rfl, List.take_of_length_le (by omega)]
  · rw [hZf, List.drop_of_length_le (by omega), List.nil_append]

/-! ### A phase of hashes

`hashPhase post`: for each of `|xCnt|` rounds, the hash of the next `m` bits of `xZ` with `xV`,
mapped by `post` (`xAcc ↦ xH`, scratch `xP`), plus the next word of the stream `xF`, its
canonical word shifted into the buffer `xOut`. -/

@[simp] abbrev xCnt : Fin 200 := 161
@[simp] abbrev xF : Fin 200 := 162
@[simp] abbrev xf : Fin 200 := 163
@[simp] abbrev xS : Fin 200 := 164
@[simp] abbrev xO : Fin 200 := 165
@[simp] abbrev xOut : Fin 200 := 166
@[simp] abbrev xH : Fin 200 := 167
@[simp] abbrev xP : Fin 200 := 168

/-- One round of a phase. -/
def phaseBody (post : Code) : Code :=
  .seq hashC (.seq post (.seq (.mv xf xF xCNK) (.seq (.add xS xH xf) (.seq (.canon xO xS)
    (.mv xOut xO xCNK)))))

/-- **A phase of hashes.** -/
def hashPhase (post : Code) : Code := .rep xCnt (phaseBody post)

/-- The registers a phase writes (besides those of `post`, within `[xH, xP]`). -/
def phW : List (Fin 200) := [xCnt, xVc, xCc, xAcc, xv, xBit, xZ, xF, xf, xS, xO, xOut, xH, xP]

theorem wr_hashC : wr hashC = [xVc, xCc, xAcc, xCc, xv, xVc, xBit, xZ, xAcc] := rfl

/-- **A phase of hashes**: the words `encRM (φ j (hash_j) + f_j)`; the post-map may keep a
state `Q j` in its scratch register `xP`. -/
theorem exec_hashPhase (hK : 0 < K) (post : Code) (φ : ℕ → RM N K → RM N K)
    (Q : ℕ → List Bool → Prop)
    (hwp : ∀ j ∈ wr post, j = xH ∨ j = xP) (w : St)
    (hpost : ∀ i, ∀ w' : St, (w' xAcc).length = N * K → (∀ j, j ∉ phW → w' j = w j) →
      Q i (w' xP) → (exec N K post w' xH).length = N * K ∧
        decRM N K (exec N K post w' xH) = φ i (decRM N K (w' xAcc)) ∧
        Q (i + 1) (exec N K post w' xP)) (hQ0 : Q 0 (w xP))
    (vs : List (List Bool)) (zss : List (List Bool)) (rest : List Bool)
    (fs : List (List Bool)) (restF : List Bool) (b₀ : List Bool) (ys₀ : List (List Bool))
    (hvs : ∀ v ∈ vs, v.length = N * K) (hzs : ∀ z ∈ zss, z.length = vs.length)
    (hfs : ∀ f ∈ fs, f.length = N * K) (hys₀ : ∀ y ∈ ys₀, y.length = N * K)
    (hn : (w xCnt).length = zss.length) (hnf : fs.length = zss.length)
    (hV : w xV = vs.flatten) (hZ : w xZ = zss.flatten ++ rest) (hF : w xF = fs.flatten ++ restF)
    (hOut : w xOut = bufW (N * K) b₀ ys₀)
    (hCm : (w xCm).length = vs.length) (hC1 : (w xC1).length = 1) (hCNK : (w xCNK).length = N * K)
    (hZero : w xZero = List.replicate (N * K) false) (hv : (w xv).length = N * K)
    (hb : (w xBit).length = 1) (hf : (w xf).length = N * K) :
    exec N K (hashPhase post) w xOut = bufW (N * K) b₀ (ys₀ ++
        (List.range zss.length).map fun j =>
          encRM N K (φ j (hashV vs (zss.getD j [])) + decRM N K (fs.getD j []))) ∧
      Q zss.length (exec N K (hashPhase post) w xP) ∧
      exec N K (hashPhase post) w xZ = rest ∧ exec N K (hashPhase post) w xF = restF ∧
      (exec N K (hashPhase post) w xv).length = N * K ∧
      (exec N K (hashPhase post) w xBit).length = 1 ∧ (exec N K (hashPhase post) w xf).length = N * K ∧
      ∀ j, j ∉ phW → exec N K (hashPhase post) w j = w j := by
  set outs : ℕ → List Bool := fun j =>
    encRM N K (φ j (hashV vs (zss.getD j [])) + decRM N K (fs.getD j []))
  let P : ℕ → St → Prop := fun i w' =>
    w' xZ = (zss.drop i).flatten ++ rest ∧ w' xF = (fs.drop i).flatten ++ restF ∧
      w' xOut = bufW (N * K) b₀ (ys₀ ++ (List.range i).map outs) ∧
      (w' xv).length = N * K ∧ (w' xBit).length = 1 ∧ (w' xf).length = N * K ∧
      Q i (w' xP) ∧ ∀ j, j ∉ phW → w' j = w j
  have hc : xCnt ∉ wr (phaseBody post) := by
    intro hm
    simp only [phaseBody, wr, wr_hashC, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with h | h | h
    · revert h; decide
    · rcases hwp _ h with h' | h' <;> revert h' <;> decide
    · revert h; decide
  have h0 : P 0 w := ⟨by simp [hZ], by simp [hF], by simp [hOut], hv, hb, hf, hQ0, fun _ _ => rfl⟩
  have key := exec_rep_inv (N := N) (K := K) xCnt (phaseBody post) hc P w h0 (fun i hi w' hP _ => by
    rw [hn] at hi
    obtain ⟨hZ', hF', hO', hvl, hbl, hfl, hQ, hfr⟩ := hP
    set u := Function.update w' xCnt (w' xCnt).tail
    have hu : ∀ j, j ≠ xCnt → u j = w' j := fun j hj => Function.update_of_ne hj _ _
    have hfrU : ∀ j, j ∉ phW → u j = w j := fun j hj => by
      rw [hu j (fun h => hj (by rw [h]; decide)), hfr j hj]
    have hzi : zss[i] ∈ zss := List.getElem_mem hi
    have hfi' : i < fs.length := by omega
    have hfi : fs[i] ∈ fs := List.getElem_mem hfi'
    -- the hash
    obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6⟩ := exec_hashC (N := N) (K := K) u vs zss[i]
      ((zss.drop (i + 1)).flatten ++ rest) hvs
      (by rw [hfrU _ (by decide)]; exact hV)
      (by rw [hu _ (by decide), hZ', List.drop_eq_getElem_cons hi, List.flatten_cons,
        List.append_assoc])
      (hzs _ hzi) (by rw [hfrU _ (by decide)]; exact hCm) (by rw [hfrU _ (by decide)]; exact hC1)
      (by rw [hfrU _ (by decide)]; exact hCNK) (by rw [hfrU _ (by decide)]; exact hZero)
      (by rw [hu _ (by decide)]; exact hvl) (by rw [hu _ (by decide)]; exact hbl)
    set u1 := exec N K hashC u
    have hfr1 : ∀ j, j ∉ phW → u1 j = w j := fun j hj => by
      rw [hA6 j (fun h => hj (by rw [h]; decide)) (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide)) (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide)) (fun h => hj (by rw [h]; decide))]
      exact hfrU j hj
    -- the post-map
    have hQ1 : Q i (u1 xP) := by
      rw [hA6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hu _ (by decide)]; exact hQ
    obtain ⟨hP1, hP2, hP3⟩ := hpost i u1 hA2 hfr1 hQ1
    set u2 := exec N K post u1
    have hnp : ∀ j, j ≠ xH → j ≠ xP → u2 j = u1 j := fun j h1 h2 =>
      exec_not_mem post u1 j fun hm => by rcases hwp j hm with h | h <;> contradiction
    -- the flood word
    have s3 := exec_mv_pop (N := N) (K := K) (d := xf) (s := xF) (c := xCNK) (by decide)
      (w := u2) (v := fs[i]) (L := (fs.drop (i + 1)).flatten ++ restF)
      (by rw [hnp _ (by decide) (by decide), hnp _ (by decide) (by decide),
        hA6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hA6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hu _ (by decide), hfl, hfrU _ (by decide), hCNK])
      (by rw [hfs _ hfi, hnp _ (by decide) (by decide),
        hA6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfrU _ (by decide), hCNK])
      (by rw [hnp _ (by decide) (by decide),
        hA6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hu _ (by decide), hF', List.drop_eq_getElem_cons hfi', List.flatten_cons,
        List.append_assoc])
    set u3 := Function.update (Function.update u2 xF ((fs.drop (i + 1)).flatten ++ restF)) xf fs[i]
    have hu3H : u3 xH = u2 xH := by simp [u3, Function.update_apply]
    have hu3f : u3 xf = fs[i] := by simp [u3]
    set x := addRMW N K (u2 xH) fs[i]
    have hxl : x.length = N * K := length_addRMW N K hP1 _
    have hxv : decRM N K x = φ i (decRM N K (u1 xAcc)) + decRM N K fs[i] := by
      rw [decRM_addRMW hP1 (hfs _ hfi), hP2]
    set u4 := Function.update u3 xS x
    have e4 : exec N K (.add xS xH xf) u3 = u4 := by
      simp only [exec, hu3H, hu3f, opd_eq hP1, opd_eq (hfs _ hfi), u4, x]
    set y := encRM N K (φ i (decRM N K (u1 xAcc)) + decRM N K fs[i])
    have hyl : y.length = N * K := length_encRM _ _ _
    set u5 := Function.update u4 xO y
    have e5 : exec N K (.canon xO xS) u4 = u5 := by
      simp only [exec, u4, Function.update_self, opd_eq hxl, canonW_eq hK hxl, hxv, u5, y]
    have hOut5 : u5 xOut = bufW (N * K) b₀ (ys₀ ++ (List.range i).map outs) := by
      simp only [u5, u4, u3, Function.update_apply]
      simp only [show (xOut = xO) = False from by decide, show (xOut = xS) = False from by decide,
        show (xOut = xf) = False from by decide, show (xOut = xF) = False from by decide, if_false]
      rw [hnp _ (by decide) (by decide),
        hA6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hu _ (by decide), hO']
    have hys : ∀ y ∈ ys₀ ++ (List.range i).map outs, y.length = N * K := by
      intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact hys₀ y h
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h; exact length_encRM _ _ _
    have s6 := exec_push (N := N) (K := K) (d := xOut) (s := xO) (c := xCNK) (by decide)
      (w := u5) hys hOut5 (by simp [u5, hyl])
      (by simp only [u5, u4, u3, Function.update_apply]
          simp only [show (xCNK = xO) = False from by decide, show (xCNK = xS) = False from by decide,
            show (xCNK = xf) = False from by decide, show (xCNK = xF) = False from by decide,
            if_false]
          rw [hnp _ (by decide) (by decide),
            hA6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hfrU _ (by decide), hCNK])
    have hy_eq : y = outs i := by
      simp only [y, outs, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hfi', hA1]
    have ex : exec N K (phaseBody post) u = Function.update (Function.update u5 xO []) xOut
        (bufW (N * K) b₀ ((ys₀ ++ (List.range i).map outs) ++ [u5 xO])) := by
      show exec N K (.seq (.mv xf xF xCNK) (.seq (.add xS xH xf) (.seq (.canon xO xS)
        (.mv xOut xO xCNK)))) (exec N K post (exec N K hashC u)) = _
      show exec N K (.seq (.add xS xH xf) (.seq (.canon xO xS) (.mv xOut xO xCNK)))
        (exec N K (.mv xf xF xCNK) u2) = _
      rw [s3]
      show exec N K (.seq (.canon xO xS) (.mv xOut xO xCNK)) (exec N K (.add xS xH xf) u3) = _
      rw [e4]
      show exec N K (.mv xOut xO xCNK) (exec N K (.canon xO xS) u4) = _
      rw [e5, s6]
    rw [ex]
    have hu5O : u5 xO = outs i := by simp [u5, hy_eq]
    have hfr5 : ∀ j, j ∉ phW → u5 j = w j := fun j hj => by
      have h1 : j ≠ xO := fun h => hj (by rw [h]; decide)
      have h2 : j ≠ xS := fun h => hj (by rw [h]; decide)
      have h3 : j ≠ xf := fun h => hj (by rw [h]; decide)
      have h4 : j ≠ xF := fun h => hj (by rw [h]; decide)
      have h5 : j ≠ xH := fun h => hj (by rw [h]; decide)
      have h6 : j ≠ xP := fun h => hj (by rw [h]; decide)
      simp only [u5, u4, u3, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3, Function.update_of_ne h4]
      rw [hnp j h5 h6]; exact hfr1 j hj
    have h52 : ∀ j, j ≠ xO → j ≠ xS → j ≠ xf → j ≠ xF → u5 j = u2 j := fun j h1 h2 h3 h4 => by
      simp only [u5, u4, u3, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3, Function.update_of_ne h4]
    have hfin : ∀ j, j ≠ xOut → j ≠ xO → j ≠ xS → j ≠ xf → j ≠ xF →
        Function.update (Function.update u5 xO []) xOut
          (bufW (N * K) b₀ ((ys₀ ++ (List.range i).map outs) ++ [u5 xO])) j = u2 j :=
      fun j h0 h1 h2 h3 h4 => by
        rw [Function.update_of_ne h0, Function.update_of_ne h1, h52 j h1 h2 h3 h4]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfin _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hnp _ (by decide) (by decide), hA3]
    · simp [u5, u4, u3, Function.update_apply]
    · rw [Function.update_self, hu5O, List.range_succ, List.map_append, List.map_singleton,
        List.append_assoc]
    · rw [hfin _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hnp _ (by decide) (by decide), hA4]
    · rw [hfin _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hnp _ (by decide) (by decide), hA5]
    · simp [u5, u4, u3, Function.update_apply, hfs _ hfi]
    · rw [hfin _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hP3
    · intro j hj
      have h1 : j ≠ xO := fun h => hj (by rw [h]; decide)
      have h2 : j ≠ xOut := fun h => hj (by rw [h]; decide)
      rw [Function.update_of_ne h2, Function.update_of_ne h1]
      exact hfr5 j hj)
  rw [hn] at key
  obtain ⟨hZf, hFf, hOf, hvl, hbl, hfl, hQf, hfr⟩ := key
  refine ⟨hOf, hQf, ?_, ?_, hvl, hbl, hfl, hfr⟩
  · show exec N K (.rep xCnt (phaseBody post)) w xZ = rest
    rw [hZf, List.drop_of_length_le le_rfl]; rfl
  · show exec N K (.rep xCnt (phaseBody post)) w xF = restF
    rw [hFf, List.drop_of_length_le (by omega)]; rfl

end SigabaNeo.Tape.RingVM.Hash