import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMDot
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.GadRow

/-!
# The end of decryption on the ring-word machine: the key sums

The sum `(y_F − κ_F) k_Fᵀ` of `Dec` (`decryptRaw_eq`) as codes of `RingVM` (registers `180 …
199`):

* `dotC cnt`: `acc += Σ_{e<n} x_e k_e` over the stream `x` (register `181`) and the key stream
  (register `182`), `n = |cnt|` (**`exec_dotC`**);
* `autVecC cnt buf`: the vector `X` (register `188`, `n` words) replaced by `σ_κ(X)` entrywise, `κ`
  the length of register `20` (**`exec_autVecC`**);
* `conjC cnt buf`: `acc += Σ_{i<W} Σ_{e<n} σ_κ^i(x_e) k_{i n + e}`, `W` the length of register `12`
  (**`exec_conjC`**): the blocks `β_i`, `η_{i,k}` of the key.
-/

namespace SigabaNeo.Tape

namespace RingVM

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {N K : ℕ} [NeZero (2 ^ K - 1)]

/-! ### `acc += Σ x_e k_e` -/

/-- One term. -/
def dotBody : Code := ofList [.mv 183 181 2, .mv 184 182 2, .mul 185 183 184, .add 180 180 185]

/-- **`acc += Σ_{e<|cnt|} x_e k_e`.** -/
def dotC (cnt : Fin 200) : Code := ofList [.cp 187 cnt, .rep 187 dotBody]

theorem wr_dotBody : wr dotBody = [183, 181, 184, 182, 185, 180] := rfl
theorem wr_dotC (cnt : Fin 200) : wr (dotC cnt) = [187, 187, 183, 181, 184, 182, 185, 180] := rfl

/-- The partial dot product. -/
noncomputable def dotL (xs ks : List (List Bool)) (n : ℕ) : RM N K :=
  ∑ e ∈ Finset.range n, decRM N K (xs.getD e []) * decRM N K (ks.getD e [])

theorem exec_dotBody (w : St) (hc : Consts N K w) {x k L L' : List Bool} (hx : x.length = N * K)
    (hk : k.length = N * K) (h181 : w 181 = x ++ L) (h182 : w 182 = k ++ L')
    (h183 : (w 183).length = N * K) (h184 : (w 184).length = N * K)
    (h180 : (w 180).length = N * K) :
    (exec N K dotBody w) 181 = L ∧ (exec N K dotBody w) 182 = L' ∧
      ((exec N K dotBody w) 183).length = N * K ∧ ((exec N K dotBody w) 184).length = N * K ∧
      ((exec N K dotBody w) 180).length = N * K ∧
      decRM N K ((exec N K dotBody w) 180) = decRM N K (w 180) + decRM N K x * decRM N K k ∧
      ∀ j, j ∉ wr dotBody → (exec N K dotBody w) j = w j := by
  have e : exec N K dotBody w = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update w 181 L) 183 x) 182 L') 184 k) 185 (mulRMW N K x k)) 180
      (addRMW N K (w 180) (mulRMW N K x k)) := by
    simp only [dotBody, exec_ofList_cons, exec_ofList_nil]
    rw [exec_mv_pop (by decide) (by rw [h183, hc.zero, List.length_replicate])
      (by rw [hx, hc.zero, List.length_replicate]) h181]
    rw [exec_mv_pop (by decide) (by
        simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [h184, hc.zero, List.length_replicate])
      (by simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
          rw [hk, hc.zero, List.length_replicate])
      (by simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]; exact h182)]
    simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, opd_eq hx, opd_eq hk,
      opd_eq h180, opd_mulRMW]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun j hj => exec_not_mem _ _ j hj⟩ <;> rw [e] <;>
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
  · exact hx
  · exact hk
  · exact length_addRMW N K h180 _
  · rw [decRM_addRMW h180 (length_mulRMW N K _ _), decRM_mulRMW hx hk]

/-- **The dot product with the key stream.** -/
theorem exec_dotC (w : St) (hc : Consts N K w) (cnt : Fin 200) (hcnt : 187 ≠ cnt)
    {xs ks : List (List Bool)} {L L' : List Bool}
    (hxs : ∀ x ∈ xs, x.length = N * K) (hks : ∀ x ∈ ks, x.length = N * K)
    (hxl : (w cnt).length ≤ xs.length) (hkl : (w cnt).length ≤ ks.length)
    (h181 : w 181 = xs.flatten ++ L) (h182 : w 182 = ks.flatten ++ L')
    (h183 : (w 183).length = N * K) (h184 : (w 184).length = N * K)
    (h180 : (w 180).length = N * K) :
    (exec N K (dotC cnt) w) 181 = (xs.drop (w cnt).length).flatten ++ L ∧
      (exec N K (dotC cnt) w) 182 = (ks.drop (w cnt).length).flatten ++ L' ∧
      ((exec N K (dotC cnt) w) 183).length = N * K ∧ ((exec N K (dotC cnt) w) 184).length = N * K ∧
      ((exec N K (dotC cnt) w) 180).length = N * K ∧
      decRM N K ((exec N K (dotC cnt) w) 180) =
        decRM N K (w 180) + dotL xs ks (w cnt).length ∧
      ∀ j, j ∉ wr (dotC cnt) → (exec N K (dotC cnt) w) j = w j := by
  set n := (w cnt).length
  set w1 := Function.update w 187 (w cnt) with hw1
  have e1 : exec N K (dotC cnt) w = exec N K (.rep 187 dotBody) w1 := rfl
  have h187 : (w1 187).length = n := by simp [hw1, n]
  let P : ℕ → St → Prop := fun i w' =>
    Consts N K w' ∧ w' 181 = (xs.drop i).flatten ++ L ∧ w' 182 = (ks.drop i).flatten ++ L' ∧
      (w' 183).length = N * K ∧ (w' 184).length = N * K ∧ (w' 180).length = N * K ∧
      decRM N K (w' 180) = decRM N K (w 180) + dotL xs ks i ∧
      ∀ j, j ∉ wr (dotC cnt) → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 187 dotBody (by decide) P w1
    ⟨consts_update hc 187 (by decide) _, by simp [hw1, h181], by simp [hw1, h182],
      by simp [hw1, h183], by simp [hw1, h184], by simp [hw1, h180], by simp [hw1, dotL],
      fun j hj => by
        rw [hw1, Function.update_of_ne (fun e => hj (by rw [e, wr_dotC]; simp))]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨hc', p181, p182, p183, p184, p180, pd, pf⟩ := hw'
      rw [h187] at hi
      set w'' := Function.update w' 187 (w' 187).tail
      have hc'' : Consts N K w'' := consts_update hc' 187 (by decide) _
      have hix : i < xs.length := by omega
      have hik : i < ks.length := by omega
      obtain ⟨b181, b182, b183, b184, b180, bd, bf⟩ := exec_dotBody w'' hc''
        (x := xs.getD i []) (k := ks.getD i []) (L := (xs.drop (i + 1)).flatten ++ L)
        (L' := (ks.drop (i + 1)).flatten ++ L')
        (hxs _ (by rw [List.getD_eq_getElem _ _ hix]; exact List.getElem_mem hix))
        (hks _ (by rw [List.getD_eq_getElem _ _ hik]; exact List.getElem_mem hik))
        (by simp only [w'', Function.update_of_ne (show (181 : Fin 200) ≠ 187 by decide), p181,
          flatten_drop_succ hix, List.append_assoc])
        (by simp only [w'', Function.update_of_ne (show (182 : Fin 200) ≠ 187 by decide), p182,
          flatten_drop_succ hik, List.append_assoc])
        (by simp only [w'', Function.update_of_ne (show (183 : Fin 200) ≠ 187 by decide)]; exact p183)
        (by simp only [w'', Function.update_of_ne (show (184 : Fin 200) ≠ 187 by decide)]; exact p184)
        (by simp only [w'', Function.update_of_ne (show (180 : Fin 200) ≠ 187 by decide)]; exact p180)
      refine ⟨consts_exec hc'' _ rfl, b181, b182, b183, b184, b180, ?_, fun j hj => ?_⟩
      · rw [bd]
        simp only [w'', Function.update_of_ne (show (180 : Fin 200) ≠ 187 by decide), pd, dotL,
          Finset.sum_range_succ, add_assoc]
      · rw [bf j (fun hm => hj (mem_of_all rfl hm))]
        simp only [w'']
        rw [Function.update_of_ne (fun e => hj (by rw [e, wr_dotC]; simp))]
        exact pf j hj)
  rw [h187] at hP
  obtain ⟨_, p181, p182, p183, p184, p180, pd, pf⟩ := hP
  rw [e1]
  exact ⟨p181, p182, p183, p184, p180, pd, pf⟩

theorem ne_lo {x y : Fin 200} (hx : x.val < 180) (hy : 180 ≤ y.val) : y ≠ x := by
  intro e; subst e; omega

theorem lo_ne {x : Fin 200} (hx : x.val < 180) (y : Fin 200) (hy : 180 ≤ y.val := by decide) :
    x ≠ y := by
  intro e; subst e; omega

theorem not_mem_hi {x : Fin 200} (hx : x.val < 180) {l : List (Fin 200)}
    (hl : l.all (fun y => decide (180 ≤ y.val)) = true) : x ∉ l := fun hm => by
  have := List.all_eq_true.mp hl x hm; simp at this; omega

/-! ### `X := σ_κ(X)` -/

/-- One entry. -/
def autBody : Code := ofList [.mv 183 190 2, .aut 191 183 20, .mv 189 191 2]

/-- **`X := σ_κ(X)` entrywise**, `κ = |reg 20|`, `n = |cnt|` entries, `buf` a template of `n N K`
bits. -/
def autVecC (cnt buf : Fin 200) : Code :=
  ofList [.cp 190 188, .cp 189 buf, .cp 187 cnt, .rep 187 autBody, .cp 188 189]

theorem wr_autBody : wr autBody = [183, 190, 191, 189, 191] := rfl
theorem wr_autVecC (cnt buf : Fin 200) :
    wr (autVecC cnt buf) = [190, 189, 187, 187, 183, 190, 191, 189, 191, 188] := rfl

theorem exec_autBody (hN : 0 < N) (w : St) (hc : Consts N K w) {x L : List Bool}
    (hx : x.length = N * K) (h190 : w 190 = x ++ L) (h183 : (w 183).length = N * K) :
    (exec N K autBody w) 190 = L ∧ ((exec N K autBody w) 183).length = N * K ∧
      (exec N K autBody w) 189 = (w 189 ++ autMW N K (w 20).length x).drop (N * K) ∧
      ∀ j, j ∉ wr autBody → (exec N K autBody w) j = w j := by
  have ha := length_autMW N K (w 20).length x hN
  have e : exec N K autBody w = Function.update (Function.update (Function.update
      (Function.update w 190 L) 183 x) 191 []) 189 ((w 189 ++ autMW N K (w 20).length x).drop (N * K))
      := by
    simp only [autBody, exec_ofList_cons, exec_ofList_nil]
    rw [exec_mv_pop (by decide) (by rw [h183, hc.zero, List.length_replicate])
      (by rw [hx, hc.zero, List.length_replicate]) h190]
    rw [exec_mv_push (d := 189) (s := 191) (c := 2) (by decide) (by
      simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, opd_eq hx]
      rw [ha, hc.zero, List.length_replicate])]
    simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, opd_eq hx, hc.zero,
      List.length_replicate]
    funext j
    simp only [Function.update_apply]
    split_ifs <;> rfl
  refine ⟨?_, ?_, ?_, fun j hj => exec_not_mem _ _ j hj⟩ <;> rw [e] <;>
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
  exact hx

/-- **`X := σ_κ(X)` entrywise.** -/
theorem exec_autVecC (hN : 0 < N) (w : St) (hc : Consts N K w) (cnt buf : Fin 200)
    (hcnt : cnt.val < 180) (hbf : buf.val < 180) {xs : List (List Bool)} (hxs : ∀ x ∈ xs, x.length = N * K) (hl : xs.length = (w cnt).length)
    (hbuf : (w buf).length = (w cnt).length * (N * K)) (h188 : w 188 = xs.flatten)
    (h183 : (w 183).length = N * K) :
    (exec N K (autVecC cnt buf) w) 188 = (xs.map (autMW N K (w 20).length)).flatten ∧
      ((exec N K (autVecC cnt buf) w) 183).length = N * K ∧
      ∀ j, j ∉ wr (autVecC cnt buf) → (exec N K (autVecC cnt buf) w) j = w j := by
  set n := (w cnt).length
  set f := autMW N K (w 20).length
  set w1 := exec N K (ofList [.cp 190 188, .cp 189 buf, .cp 187 cnt]) w with hw1
  have e1 : exec N K (autVecC cnt buf) w =
      exec N K (.cp 188 189) (exec N K (.rep 187 autBody) w1) := rfl
  have w1_eq : w1 = Function.update (Function.update (Function.update w 190 (w 188)) 189 (w buf))
      187 (w cnt) := by
    simp only [hw1, exec_ofList_cons, exec_ofList_nil, exec]
    rw [Function.update_of_ne (ne_lo hbf (by decide)).symm, Function.update_of_ne
      (ne_lo hcnt (by decide)).symm, Function.update_of_ne (ne_lo hcnt (by decide)).symm]
  have h187 : (w1 187).length = n := by rw [w1_eq]; simp [n]
  have hf : ∀ x, (f x).length = N * K := fun x => length_autMW N K _ x hN
  let P : ℕ → St → Prop := fun i w' =>
    Consts N K w' ∧ w' 190 = (xs.drop i).flatten ∧ (w' 183).length = N * K ∧
      w' 189 = (w buf ++ ((xs.take i).map f).flatten).drop (i * (N * K)) ∧
      ∀ j, j ∉ wr (autVecC cnt buf) → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 187 autBody (by decide) P w1
    ⟨by rw [w1_eq]; exact consts_update (consts_update (consts_update hc 190 (by decide) _) 189
        (by decide) _) 187 (by decide) _,
      by rw [w1_eq]; simp [h188], by rw [w1_eq]; simp [h183], by rw [w1_eq]; simp,
      fun j hj => by
        rw [w1_eq, Function.update_of_ne (fun e => hj (by rw [e, wr_autVecC]; simp)),
          Function.update_of_ne (fun e => hj (by rw [e, wr_autVecC]; simp)),
          Function.update_of_ne (fun e => hj (by rw [e, wr_autVecC]; simp))]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨hc', p190, p183, p189, pf⟩ := hw'
      rw [h187] at hi
      set w'' := Function.update w' 187 (w' 187).tail
      have hc'' : Consts N K w'' := consts_update hc' 187 (by decide) _
      have hix : i < xs.length := by omega
      have h20 : w'' 20 = w 20 := by
        simp only [w'', Function.update_of_ne (show (20 : Fin 200) ≠ 187 by decide)]
        exact pf 20 (by rw [wr_autVecC]; simp)
      obtain ⟨b190, b183, b189, bf⟩ := exec_autBody hN w'' hc'' (x := xs.getD i [])
        (L := (xs.drop (i + 1)).flatten)
        (hxs _ (by rw [List.getD_eq_getElem _ _ hix]; exact List.getElem_mem hix))
        (by simp only [w'', Function.update_of_ne (show (190 : Fin 200) ≠ 187 by decide), p190,
          flatten_drop_succ hix])
        (by simp only [w'', Function.update_of_ne (show (183 : Fin 200) ≠ 187 by decide)]; exact p183)
      refine ⟨consts_exec hc'' _ rfl, b190, b183, ?_, fun j hj => ?_⟩
      · rw [b189, h20]
        simp only [w'', Function.update_of_ne (show (189 : Fin 200) ≠ 187 by decide), p189]
        have hlen : ((xs.take i).map f).length = i := by simp; omega
        have := drop_append_flatten_succ (b := w buf) (vs := (xs.take i).map f)
          (x := f (xs.getD i [])) (hf _) (fun y hy => by
            obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy; exact hf z)
        rw [hlen] at this
        rw [this, List.take_succ, List.getElem?_eq_getElem hix, ← List.getD_eq_getElem _ [] hix]
        simp [List.map_append, Nat.add_mul, Nat.min_eq_left hix.le]
      · rw [bf j (fun hm => hj (mem_of_all rfl hm))]
        simp only [w'']
        rw [Function.update_of_ne (fun e => hj (by rw [e, wr_autVecC]; simp))]
        exact pf j hj)
  rw [h187] at hP
  obtain ⟨_, _, p183, p189, pf⟩ := hP
  have hxs' : xs.take n = xs := List.take_of_length_le (by omega)
  have hfin : (w buf ++ ((xs.take n).map f).flatten).drop (n * (N * K)) = (xs.map f).flatten := by
    rw [hxs']
    have := drop_append_flatten (b := w buf) (vs := xs.map f) (n := N * K) (by simp [hbuf, hl])
    simpa [hl] using this
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [e1]
    show Function.update (exec N K (.rep 187 autBody) w1) 188
      (exec N K (.rep 187 autBody) w1 189) 188 = _
    rw [Function.update_self, p189, hfin]
  · rw [e1]
    show (Function.update (exec N K (.rep 187 autBody) w1) 188
      (exec N K (.rep 187 autBody) w1 189) 183).length = _
    rw [Function.update_of_ne (show (183 : Fin 200) ≠ 188 by decide)]; exact p183
  · rw [e1]
    show Function.update (exec N K (.rep 187 autBody) w1) 188
      (exec N K (.rep 187 autBody) w1 189) j = _
    rw [Function.update_of_ne (fun e => hj (by rw [e, wr_autVecC]; simp))]
    exact pf j hj

/-! ### `acc += Σ_{i<W} Σ_e σ_κ^i(x_e) k_{i n + e}` -/

/-- One block `i`: the dot product with the next `n` keys, then `X := σ_κ(X)`. -/
def conjBody (cnt buf : Fin 200) : Code := ofList [.cp 181 188, dotC cnt, autVecC cnt buf]

/-- **The conjugate sums**, `W = |reg 12|` blocks. -/
def conjC (cnt buf : Fin 200) : Code := ofList [.cp 186 12, .rep 186 (conjBody cnt buf)]

theorem wr_conjBody (cnt buf : Fin 200) : wr (conjBody cnt buf) =
    [181, 187, 187, 183, 181, 184, 182, 185, 180, 190, 189, 187, 187, 183, 190, 191, 189, 191, 188] :=
  rfl

theorem wr_conjC (cnt buf : Fin 200) : wr (conjC cnt buf) = 186 :: 186 ::
    [181, 187, 187, 183, 181, 184, 182, 185, 180, 190, 189, 187, 187, 183, 190, 191, 189, 191, 188] :=
  rfl

/-- The conjugate sums of the first `m` blocks. -/
noncomputable def conjL (f : List Bool → List Bool) (xs ks : List (List Bool)) (n m : ℕ) : RM N K :=
  ∑ i ∈ Finset.range m, dotL (xs.map f^[i]) (ks.drop (i * n)) n

theorem exec_conjC (hN : 0 < N) (w : St) (hc : Consts N K w) (cnt buf : Fin 200)
    (hcnt : cnt.val < 180) (hbf : buf.val < 180) {xs ks : List (List Bool)} {L' : List Bool}
    (hxs : ∀ x ∈ xs, x.length = N * K) (hks : ∀ x ∈ ks, x.length = N * K)
    (hl : xs.length = (w cnt).length) (hkl : (w 12).length * (w cnt).length ≤ ks.length)
    (hbuf : (w buf).length = (w cnt).length * (N * K)) (h188 : w 188 = xs.flatten)
    (h182 : w 182 = ks.flatten ++ L') (h183 : (w 183).length = N * K)
    (h184 : (w 184).length = N * K) (h180 : (w 180).length = N * K) :
    (exec N K (conjC cnt buf) w) 182 =
        (ks.drop ((w 12).length * (w cnt).length)).flatten ++ L' ∧
      ((exec N K (conjC cnt buf) w) 180).length = N * K ∧
      decRM N K ((exec N K (conjC cnt buf) w) 180) = decRM N K (w 180) +
        conjL (autMW N K (w 20).length) xs ks (w cnt).length (w 12).length ∧
      ∀ j, j ∉ wr (conjC cnt buf) → (exec N K (conjC cnt buf) w) j = w j := by
  set n := (w cnt).length
  set W := (w 12).length
  set f := autMW N K (w 20).length
  set w1 := Function.update w 186 (w 12) with hw1
  have e1 : exec N K (conjC cnt buf) w = exec N K (.rep 186 (conjBody cnt buf)) w1 := rfl
  have h186 : (w1 186).length = W := by simp [hw1, W]
  have hf : ∀ x, (f x).length = N * K := fun x => length_autMW N K _ x hN
  have hfi : ∀ i x, x.length = N * K → (f^[i] x).length = N * K := by
    intro i; induction i with
    | zero => intro x hx; exact hx
    | succ i ih => intro x _; rw [Function.iterate_succ_apply']; exact hf _
  let P : ℕ → St → Prop := fun i w' =>
    Consts N K w' ∧ w' 188 = (xs.map f^[i]).flatten ∧
      w' 182 = (ks.drop (i * n)).flatten ++ L' ∧
      (w' 183).length = N * K ∧ (w' 184).length = N * K ∧ (w' 180).length = N * K ∧
      decRM N K (w' 180) = decRM N K (w 180) + conjL f xs ks n i ∧
      ∀ j, j ∉ wr (conjC cnt buf) → w' j = w j
  have hcntW : ∀ j : Fin 200, j.val < 180 → j ∉ wr (conjC cnt buf) := fun j hj =>
    not_mem_hi hj rfl
  have hP := exec_rep_inv (N := N) (K := K) 186 (conjBody cnt buf)
    (by rw [wr_conjBody]; simp) P w1
    ⟨consts_update hc 186 (by decide) _, by simp [hw1, h188], by simp [hw1, h182],
      by simp [hw1, h183], by simp [hw1, h184], by simp [hw1, h180], by simp [hw1, conjL],
      fun j hj => by
        rw [hw1, Function.update_of_ne (fun e => hj (by rw [e, wr_conjC]; simp))]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨hc', p188, p182, p183, p184, p180, pd, pf⟩ := hw'
      rw [h186] at hi
      set w'' := Function.update w' 186 (w' 186).tail
      have hc'' : Consts N K w'' := consts_update hc' 186 (by decide) _
      have hcnt'' : w'' cnt = w cnt := by
        simp only [w'', Function.update_of_ne (lo_ne hcnt 186)]
        exact pf cnt (hcntW cnt hcnt)
      have hbuf'' : w'' buf = w buf := by
        simp only [w'', Function.update_of_ne (lo_ne hbf 186)]
        exact pf buf (hcntW buf hbf)
      have h20 : w'' 20 = w 20 := by
        simp only [w'', Function.update_of_ne (show (20 : Fin 200) ≠ 186 by decide)]
        exact pf 20 (hcntW 20 (by decide))
      -- the copy
      set u1 := Function.update w'' 181 (w'' 188) with hu1
      have hcu : Consts N K u1 := consts_update hc'' 181 (by decide) _
      have hxs' : ∀ x ∈ xs.map f^[i], x.length = N * K := fun x hx => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx; exact hfi i z (hxs z hz)
      have hks' : ∀ x ∈ ks.drop (i * n), x.length = N * K := fun x hx => hks x (List.mem_of_mem_drop hx)
      have hkn : n ≤ (ks.drop (i * n)).length := by
        rw [List.length_drop]
        have : (i + 1) * n ≤ W * n := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul] at this; omega
      obtain ⟨d181, d182, d183, d184, d180, dd, df⟩ := exec_dotC u1 hcu cnt
        (lo_ne hcnt 187).symm hxs' hks' (L := []) (L' := L')
        (by rw [hu1, Function.update_of_ne (lo_ne hcnt 181), hcnt'']; simp; omega)
        (by rw [hu1, Function.update_of_ne (lo_ne hcnt 181), hcnt'']; exact hkn)
        (by simp only [hu1, Function.update_self, w'',
          Function.update_of_ne (show (188 : Fin 200) ≠ 186 by decide), p188, List.append_nil])
        (by simp only [hu1, w'', Function.update_of_ne (show (182 : Fin 200) ≠ 181 by decide),
          Function.update_of_ne (show (182 : Fin 200) ≠ 186 by decide), p182])
        (by simp only [hu1, w'', Function.update_of_ne (show (183 : Fin 200) ≠ 181 by decide),
          Function.update_of_ne (show (183 : Fin 200) ≠ 186 by decide)]; exact p183)
        (by simp only [hu1, w'', Function.update_of_ne (show (184 : Fin 200) ≠ 181 by decide),
          Function.update_of_ne (show (184 : Fin 200) ≠ 186 by decide)]; exact p184)
        (by simp only [hu1, w'', Function.update_of_ne (show (180 : Fin 200) ≠ 181 by decide),
          Function.update_of_ne (show (180 : Fin 200) ≠ 186 by decide)]; exact p180)
      have hu1cnt : u1 cnt = w cnt := by
        rw [hu1, Function.update_of_ne (lo_ne hcnt 181), hcnt'']
      set u2 := exec N K (dotC cnt) u1
      have hcu2 : Consts N K u2 := consts_exec hcu _ rfl
      have u2cnt : u2 cnt = w cnt := by
        rw [df cnt (not_mem_hi hcnt rfl), hu1, Function.update_of_ne (lo_ne hcnt 181), hcnt'']
      have u2buf : u2 buf = w buf := by
        rw [df buf (not_mem_hi hbf rfl), hu1, Function.update_of_ne (lo_ne hbf 181), hbuf'']
      have u2_20 : u2 20 = w 20 := by
        rw [df 20 (by rw [wr_dotC]; simp), hu1, Function.update_of_ne (by decide), h20]
      have u2_188 : u2 188 = (xs.map f^[i]).flatten := by
        rw [df 188 (by rw [wr_dotC]; simp), hu1, Function.update_of_ne (by decide)]
        simp only [w'', Function.update_of_ne (show (188 : Fin 200) ≠ 186 by decide)]
        exact p188
      obtain ⟨a188, a183, af⟩ := exec_autVecC hN u2 hcu2 cnt buf hcnt hbf hxs'
        (by rw [u2cnt]; simp; omega) (by rw [u2buf, u2cnt]; exact hbuf) u2_188 d183
      have e2 : exec N K (conjBody cnt buf) w'' = exec N K (autVecC cnt buf) u2 := rfl
      refine ⟨by rw [e2]; exact consts_exec hcu2 _ rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
      · rw [e2, a188, u2_20, List.map_map]
        congr 2
        funext x
        simp only [Function.comp_apply, f]
        rw [← Function.iterate_succ_apply' (autMW N K (w 20).length)]
      · rw [e2, af 182 (by rw [wr_autVecC]; simp), d182, List.drop_drop, hu1cnt]
        first
          | rw [show i * n + n = (i + 1) * n by ring]
          | rw [show n + i * n = (i + 1) * n by ring]
      · rw [e2]; exact a183
      · rw [e2, af 184 (by rw [wr_autVecC]; simp)]; exact d184
      · rw [e2, af 180 (by rw [wr_autVecC]; simp)]; exact d180
      · rw [e2, af 180 (by rw [wr_autVecC]; simp), dd, hu1cnt]
        simp only [hu1, w'', Function.update_of_ne (show (180 : Fin 200) ≠ 181 by decide),
          Function.update_of_ne (show (180 : Fin 200) ≠ 186 by decide), pd, conjL,
          Finset.sum_range_succ, add_assoc, hcnt'', Function.update_of_ne (lo_ne hcnt 181)]
        rfl
      · rw [e2, af j (fun hm => hj (mem_of_all rfl hm)), df j (fun hm => hj (mem_of_all rfl hm)), hu1,
          Function.update_of_ne (fun e => hj (by rw [e, wr_conjC]; simp))]
        simp only [w'']
        rw [Function.update_of_ne (fun e => hj (by rw [e, wr_conjC]; simp))]
        exact pf j hj)
  rw [h186] at hP
  obtain ⟨_, _, p182, _, _, p180, pd, pf⟩ := hP
  rw [e1]
  exact ⟨p182, p180, pd, pf⟩

/-! ### `X := a − b` -/

/-- One entry: pop `a_e`, `b_e`, push `a_e − b_e`. -/
def subBody : Code := ofList [.mv 194 192 2, .mv 195 193 2, .sub 196 194 195, .mv 198 196 2]

/-- **`X := a − b`** (streams `192`, `193`, `n = |cnt|` entries, `buf` a template of `n N K`
bits) into register `188`. -/
def subVecC (cnt buf : Fin 200) : Code :=
  ofList [.cp 198 buf, .cp 197 cnt, .rep 197 subBody, .cp 188 198]

theorem wr_subBody : wr subBody = [194, 192, 195, 193, 196, 198, 196] := rfl
theorem wr_subVecC (cnt buf : Fin 200) :
    wr (subVecC cnt buf) = [198, 197, 197, 194, 192, 195, 193, 196, 198, 196, 188] := rfl

theorem exec_subBody (w : St) (hc : Consts N K w) {a b La Lb : List Bool}
    (ha : a.length = N * K) (hb : b.length = N * K) (h192 : w 192 = a ++ La) (h193 : w 193 = b ++ Lb)
    (h194 : (w 194).length = N * K) (h195 : (w 195).length = N * K) :
    (exec N K subBody w) 192 = La ∧ (exec N K subBody w) 193 = Lb ∧
      ((exec N K subBody w) 194).length = N * K ∧ ((exec N K subBody w) 195).length = N * K ∧
      (exec N K subBody w) 198 = (w 198 ++ subRMW N K a b).drop (N * K) ∧
      ∀ j, j ∉ wr subBody → (exec N K subBody w) j = w j := by
  have hs := length_subRMW N K ha b
  have e : exec N K subBody w = Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update w 192 La) 194 a) 193 Lb) 195 b) 196 [])
      198 ((w 198 ++ subRMW N K a b).drop (N * K)) := by
    simp only [subBody, exec_ofList_cons, exec_ofList_nil]
    rw [exec_mv_pop (by decide) (by rw [h194, hc.zero, List.length_replicate])
      (by rw [ha, hc.zero, List.length_replicate]) h192]
    rw [exec_mv_pop (d := 195) (s := 193) (c := 2) (by decide)
      (by simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
          rw [h195, hc.zero, List.length_replicate])
      (by simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
          rw [hb, hc.zero, List.length_replicate])
      (by simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]; exact h193)]
    rw [exec_mv_push (d := 198) (s := 196) (c := 2) (by decide) (by
      simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, opd_eq ha, opd_eq hb]
      rw [hs, hc.zero, List.length_replicate])]
    simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, opd_eq ha, opd_eq hb,
      hc.zero, List.length_replicate]
    funext j
    simp only [Function.update_apply]
    split_ifs <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => exec_not_mem _ _ j hj⟩ <;> rw [e] <;>
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
  · exact ha
  · exact hb

/-- **`X := a − b`.** -/
theorem exec_subVecC (w : St) (hc : Consts N K w) (cnt buf : Fin 200)
    (hcnt : cnt.val < 180) (hbf : buf.val < 180) {as bs : List (List Bool)} {La Lb : List Bool}
    (has : ∀ x ∈ as, x.length = N * K) (hbs : ∀ x ∈ bs, x.length = N * K)
    (hla : as.length = (w cnt).length) (hlb : bs.length = (w cnt).length)
    (hbuf : (w buf).length = (w cnt).length * (N * K))
    (h192 : w 192 = as.flatten ++ La) (h193 : w 193 = bs.flatten ++ Lb)
    (h194 : (w 194).length = N * K) (h195 : (w 195).length = N * K) :
    (exec N K (subVecC cnt buf) w) 188 = (List.zipWith (subRMW N K) as bs).flatten ∧
      (exec N K (subVecC cnt buf) w) 192 = La ∧ (exec N K (subVecC cnt buf) w) 193 = Lb ∧
      ((exec N K (subVecC cnt buf) w) 194).length = N * K ∧
      ((exec N K (subVecC cnt buf) w) 195).length = N * K ∧
      ∀ j, j ∉ wr (subVecC cnt buf) → (exec N K (subVecC cnt buf) w) j = w j := by
  set n := (w cnt).length
  set w1 := exec N K (ofList [.cp 198 buf, .cp 197 cnt]) w with hw1
  have e1 : exec N K (subVecC cnt buf) w =
      exec N K (.cp 188 198) (exec N K (.rep 197 subBody) w1) := rfl
  have w1_eq : w1 = Function.update (Function.update w 198 (w buf)) 197 (w cnt) := by
    simp only [hw1, exec_ofList_cons, exec_ofList_nil, exec]
    rw [Function.update_of_ne (lo_ne hcnt 198)]
  have h197 : (w1 197).length = n := by rw [w1_eq]; simp [n]
  let zs := List.zipWith (subRMW N K) as bs
  have hzl : zs.length = n := by simp [zs, hla, hlb]
  have hzs : ∀ i, (i < n) → zs.getD i [] = subRMW N K (as.getD i []) (bs.getD i []) := by
    intro i hi
    simp only [zs, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
    rfl
  let P : ℕ → St → Prop := fun i w' =>
    Consts N K w' ∧ w' 192 = (as.drop i).flatten ++ La ∧ w' 193 = (bs.drop i).flatten ++ Lb ∧
      (w' 194).length = N * K ∧ (w' 195).length = N * K ∧
      w' 198 = (w buf ++ (zs.take i).flatten).drop (i * (N * K)) ∧
      ∀ j, j ∉ wr (subVecC cnt buf) → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 197 subBody (by decide) P w1
    ⟨by rw [w1_eq]; exact consts_update (consts_update hc 198 (by decide) _) 197 (by decide) _,
      by rw [w1_eq]; simp [h192], by rw [w1_eq]; simp [h193], by rw [w1_eq]; simp [h194],
      by rw [w1_eq]; simp [h195], by rw [w1_eq]; simp,
      fun j hj => by
        rw [w1_eq, Function.update_of_ne (fun e => hj (by rw [e, wr_subVecC]; simp)),
          Function.update_of_ne (fun e => hj (by rw [e, wr_subVecC]; simp))]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨hc', p192, p193, p194, p195, p198, pf⟩ := hw'
      rw [h197] at hi
      set w'' := Function.update w' 197 (w' 197).tail
      have hc'' : Consts N K w'' := consts_update hc' 197 (by decide) _
      have hia : i < as.length := by omega
      have hib : i < bs.length := by omega
      have hai : as.getD i [] ∈ as := by
        rw [List.getD_eq_getElem _ _ hia]; exact List.getElem_mem hia
      have hbi : bs.getD i [] ∈ bs := by
        rw [List.getD_eq_getElem _ _ hib]; exact List.getElem_mem hib
      obtain ⟨b192, b193, b194, b195, b198, bf⟩ := exec_subBody w'' hc''
        (a := as.getD i []) (b := bs.getD i []) (La := (as.drop (i + 1)).flatten ++ La)
        (Lb := (bs.drop (i + 1)).flatten ++ Lb)
        (has _ hai) (hbs _ hbi)
        (by simp only [w'', Function.update_of_ne (show (192 : Fin 200) ≠ 197 by decide), p192,
          flatten_drop_succ hia, List.append_assoc])
        (by simp only [w'', Function.update_of_ne (show (193 : Fin 200) ≠ 197 by decide), p193,
          flatten_drop_succ hib, List.append_assoc])
        (by simp only [w'', Function.update_of_ne (show (194 : Fin 200) ≠ 197 by decide)]; exact p194)
        (by simp only [w'', Function.update_of_ne (show (195 : Fin 200) ≠ 197 by decide)]; exact p195)
      refine ⟨consts_exec hc'' _ rfl, b192, b193, b194, b195, ?_, fun j hj => ?_⟩
      · rw [b198]
        simp only [w'', Function.update_of_ne (show (198 : Fin 200) ≠ 197 by decide), p198]
        have hzt : ∀ y ∈ zs.take i, y.length = N * K := fun y hy => by
          have hy' := List.mem_of_mem_take hy
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy'
          rw [← List.getD_eq_getElem _ [] hk, hzs k (by omega)]
          exact length_subRMW N K (has _ (by
            rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)) _
        have hlen : (zs.take i).length = i := by simp; omega
        have := drop_append_flatten_succ (b := w buf) (vs := zs.take i)
          (x := subRMW N K (as.getD i []) (bs.getD i []))
          (length_subRMW N K (has _ hai) _) hzt
        rw [hlen] at this
        rw [this, List.take_succ, List.getElem?_eq_getElem (show i < zs.length by omega),
          ← List.getD_eq_getElem _ [] (show i < zs.length by omega), hzs i hi]
        simp [Nat.add_mul, Nat.min_eq_left (show i ≤ zs.length by omega)]
      · rw [bf j (fun hm => hj (mem_of_all rfl hm))]
        simp only [w'']
        rw [Function.update_of_ne (fun e => hj (by rw [e, wr_subVecC]; simp))]
        exact pf j hj)
  rw [h197] at hP
  obtain ⟨_, p192, p193, p194, p195, p198, pf⟩ := hP
  have hzt : zs.take n = zs := List.take_of_length_le (by omega)
  have hzall : ∀ y ∈ zs, y.length = N * K := fun y hy => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    rw [← List.getD_eq_getElem _ [] hk, hzs k (by omega)]
    exact length_subRMW N K (has _ (by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)) _
  have hfin : (w buf ++ (zs.take n).flatten).drop (n * (N * K)) = zs.flatten := by
    rw [hzt]
    have := drop_append_flatten (b := w buf) (vs := zs) (n := N * K) (by rw [hbuf, hzl])
    rwa [hzl] at this
  have g : ∀ j : Fin 200, j ≠ 188 → exec N K (subVecC cnt buf) w j = exec N K (.rep 197 subBody) w1 j :=
    fun j hj => by rw [e1]; exact Function.update_of_ne hj _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [e1]
    show Function.update (exec N K (.rep 197 subBody) w1) 188
      (exec N K (.rep 197 subBody) w1 198) 188 = _
    rw [Function.update_self, p198, hfin]
  · rw [g _ (by decide), p192, List.drop_of_length_le (by omega)]; simp
  · rw [g _ (by decide), p193, List.drop_of_length_le (by omega)]; simp
  · rw [g _ (by decide)]; exact p194
  · rw [g _ (by decide)]; exact p195
  · rw [g j (fun e => hj (by rw [e, wr_subVecC]; simp))]; exact pf j hj

/-! ### Second halves of a stream of pairs, repeated words, the gadget row -/

/-- **Shift** a word of the template's width from a stream into a buffer. -/
theorem exec_mv_shift {d s c : Fin 200} (h : ¬(d = s ∨ d = c ∨ s = c)) {w : St} {v L : List Bool}
    (hv : v.length = (w c).length) (hs : w s = v ++ L) :
    exec N K (.mv d s c) w =
      Function.update (Function.update w s L) d ((w d ++ v).drop (w c).length) := by
  simp only [exec, if_neg h, ValVM.shiftIn, hs]
  rw [takeD_eq_take (by simp; omega), List.take_left' hv, List.drop_left' hv]

/-- **`199 :=` the second halves**: `|cnt|` rounds of dropping `|reg 6|` bits of the stream `192`
and moving the next `|reg 6|` bits into the buffer `199`. -/
def halvesC (cnt : Fin 200) : Code := ofList [.cp 197 cnt, .rep 197 (ofList [.drop 192 6, .mv 199 192 6])]

theorem wr_halvesC (cnt : Fin 200) : wr (halvesC cnt) = [197, 197, 192, 199, 192] := rfl

theorem exec_halvesC (w : St) (cnt : Fin 200) (hcnt : cnt.val < 180)
    {ps : List (List Bool × List Bool)} {L : List Bool}
    (hps : ∀ p ∈ ps, p.1.length = (w 6).length ∧ p.2.length = (w 6).length)
    (hl : ps.length = (w cnt).length) (h192 : w 192 = (ps.map fun p => p.1 ++ p.2).flatten ++ L)
    (h199 : (w 199).length = ps.length * (w 6).length) :
    (exec N K (halvesC cnt) w) 199 = (ps.map Prod.snd).flatten ∧
      (exec N K (halvesC cnt) w) 192 = L ∧
      ∀ j, j ∉ wr (halvesC cnt) → (exec N K (halvesC cnt) w) j = w j := by
  set V := (w 6).length
  set w1 := Function.update w 197 (w cnt) with hw1
  have e1 : exec N K (halvesC cnt) w = exec N K (.rep 197 (ofList [.drop 192 6, .mv 199 192 6])) w1 :=
    rfl
  have h197 : (w1 197).length = ps.length := by simp [hw1, hl]
  have h6 : w1 6 = w 6 := by simp [hw1]
  let P : ℕ → St → Prop := fun i w' =>
    w' 6 = w 6 ∧ w' 192 = ((ps.drop i).map fun p => p.1 ++ p.2).flatten ++ L ∧
      w' 199 = (w 199 ++ ((ps.take i).map Prod.snd).flatten).drop (i * V) ∧
      ∀ j, j ∉ wr (halvesC cnt) → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 197 (ofList [.drop 192 6, .mv 199 192 6]) (by decide) P w1
    ⟨h6, by simp [hw1, h192], by simp [hw1],
      fun j hj => by rw [hw1, Function.update_of_ne (fun e => hj (by rw [e, wr_halvesC]; simp))]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨p6, p192, p199, pf⟩ := hw'
      rw [h197] at hi
      have hpi := hps _ (List.getElem_mem hi)
      set w'' := Function.update w' 197 (w' 197).tail
      have e192 : w'' 192 = (ps[i].1 ++ ps[i].2) ++ ((ps.drop (i + 1)).map fun p => p.1 ++ p.2).flatten
          ++ L := by
        simp only [w'', Function.update_of_ne (show (192 : Fin 200) ≠ 197 by decide), p192]
        rw [List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons, List.append_assoc]
      have e6 : w'' 6 = w 6 := by
        simp only [w'', Function.update_of_ne (show (6 : Fin 200) ≠ 197 by decide), p6]
      set rest := ((ps.drop (i + 1)).map fun p => p.1 ++ p.2).flatten ++ L
      have ed : exec N K (.drop 192 6) w'' = Function.update w'' 192 (ps[i].2 ++ rest) := by
        simp only [exec, show ¬((192 : Fin 200) = 6) by decide, ↓reduceIte, e192, e6]
        simp only [List.append_assoc]
        rw [List.drop_left' hpi.1]
      set u := Function.update w'' 192 (ps[i].2 ++ rest)
      have u6 : u 6 = w 6 := by simp only [u, Function.update_of_ne (show (6 : Fin 200) ≠ 192 by decide), e6]
      have u199 : u 199 = w' 199 := by
        simp only [u, w'', Function.update_of_ne (show (199 : Fin 200) ≠ 192 by decide),
          Function.update_of_ne (show (199 : Fin 200) ≠ 197 by decide)]
      have em : exec N K (ofList [.drop 192 6, .mv 199 192 6]) w'' =
          Function.update (Function.update u 192 rest) 199 ((w' 199 ++ ps[i].2).drop V) := by
        simp only [exec_ofList_cons, exec_ofList_nil]
        rw [ed]
        rw [exec_mv_shift (v := ps[i].2) (L := rest) (by decide) (by rw [u6]; exact hpi.2)
          (by simp only [u, Function.update_self]), u6, u199]
      have hsnd : ∀ y ∈ (ps.take i).map Prod.snd, y.length = V := fun y hy => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
        exact (hps q (List.mem_of_mem_take hq)).2
      have hlen : ((ps.take i).map Prod.snd).length = i := by simp; omega
      refine ⟨?_, ?_, ?_, fun j hj => ?_⟩
      · rw [em]; simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]; exact u6
      · rw [em]; simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]; rfl
      · rw [em]; simp only [Function.update_self, p199]
        have := drop_append_flatten_succ (b := w 199) (vs := (ps.take i).map Prod.snd)
          (x := ps[i].2) hpi.2 hsnd
        rw [hlen] at this
        rw [this, List.take_succ, List.getElem?_eq_getElem hi, List.map_append, List.length_append,
          hlen]
        simp only [Option.toList_some, List.map_cons, List.map_nil, List.length_singleton]
      · have hj1 : j ≠ 199 := fun e => hj (by rw [e, wr_halvesC]; simp)
        have hj2 : j ≠ 192 := fun e => hj (by rw [e, wr_halvesC]; simp)
        have hj3 : j ≠ 197 := fun e => hj (by rw [e, wr_halvesC]; simp)
        rw [em, Function.update_of_ne hj1, Function.update_of_ne hj2]
        simp only [u, w'', Function.update_of_ne hj2, Function.update_of_ne hj3]
        exact pf j hj)
  rw [h197] at hP
  obtain ⟨_, p192, p199, pf⟩ := hP
  have hall : ∀ y ∈ ps.map Prod.snd, y.length = V := fun y hy => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy; exact (hps q hq).2
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, p199, List.take_of_length_le le_rfl]
    have := drop_append_flatten (b := w 199) (vs := ps.map Prod.snd) (n := V) (by simp [h199])
    simpa using this
  · rw [e1, p192, List.drop_of_length_le le_rfl]; simp
  · intro j hj; rw [e1]; exact pf j hj

/-- **The gadget row `G⁽²⁾`** into register `196`: `K` zero words, then the words of
`2^i`, `i < K` (doublings of the word of `1` on register `3`; register `5` holds `K − 1` bits). -/
def g1C : Code :=
  ofList [.cp 196 6, .cp 195 3, .cp 197 4, .rep 197 (ofList [.cp 194 195, .mv 196 194 2, .rotB 195 195 5])]

theorem wr_g1C : wr g1C = [196, 195, 197, 197, 194, 196, 194, 195] := rfl

theorem exec_g1C (w : St) (hc : Consts N K w) (h6 : w 6 = List.replicate (2 * K * (N * K)) false)
    (h3 : (w 3).length = N * K) (h5 : (w 5).length = K - 1) :
    (exec N K g1C w) 196 = List.replicate (K * (N * K)) false ++
        ((List.range K).map (gIt N K (w 3))).flatten ∧
      ∀ j, j ∉ wr g1C → (exec N K g1C w) j = w j := by
  set w1 := exec N K (ofList [.cp 196 6, .cp 195 3, .cp 197 4]) w with hw1
  have e1 : exec N K g1C w = exec N K (.rep 197 (ofList [.cp 194 195, .mv 196 194 2,
      .rotB 195 195 5])) w1 := rfl
  have w1_eq : w1 = Function.update (Function.update (Function.update w 196 (w 6)) 195 (w 3)) 197
      (w 4) := by
    simp only [hw1, exec_ofList_cons, exec_ofList_nil, exec, Function.update_apply, Fin.reduceEq,
      ↓reduceIte]
  have h197 : (w1 197).length = K := by rw [w1_eq]; simp [hc.k]
  let gs : ℕ → List (List Bool) := fun i => (List.range i).map (gIt N K (w 3))
  have hgl : ∀ i, ∀ y ∈ gs i, y.length = N * K := fun i y hy => by
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy; exact length_gIt h3 k
  let P : ℕ → St → Prop := fun i w' =>
    Consts N K w' ∧ w' 5 = w 5 ∧ w' 195 = gIt N K (w 3) i ∧
      w' 196 = (w 6 ++ (gs i).flatten).drop (i * (N * K)) ∧
      ∀ j, j ∉ wr g1C → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 197 (ofList [.cp 194 195, .mv 196 194 2,
      .rotB 195 195 5]) (by decide) P w1
    ⟨by rw [w1_eq]; exact consts_update (consts_update (consts_update hc 196 (by decide) _) 195
        (by decide) _) 197 (by decide) _,
      by rw [w1_eq]; simp, by rw [w1_eq]; simp [gIt], by rw [w1_eq]; simp [gs],
      fun j hj => by
        rw [w1_eq, Function.update_of_ne (fun e => hj (by rw [e, wr_g1C]; simp)),
          Function.update_of_ne (fun e => hj (by rw [e, wr_g1C]; simp)),
          Function.update_of_ne (fun e => hj (by rw [e, wr_g1C]; simp))]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨hc', p5, p195, p196, pf⟩ := hw'
      set w'' := Function.update w' 197 (w' 197).tail
      have hgi := length_gIt h3 i
      have e2 : exec N K (ofList [.cp 194 195, .mv 196 194 2, .rotB 195 195 5]) w'' =
          Function.update (Function.update (Function.update (Function.update w'' 194 (gIt N K (w 3) i))
            194 []) 196 ((w' 196 ++ gIt N K (w 3) i).drop (N * K))) 195
            (rotBW N K (w 5).length (gIt N K (w 3) i)) := by
        simp only [exec_ofList_cons, exec_ofList_nil]
        rw [show exec N K (.cp 194 195) w'' = Function.update w'' 194 (gIt N K (w 3) i) by
          simp only [exec, w'', Function.update_of_ne (show (195 : Fin 200) ≠ 197 by decide), p195]]
        have hz : (Function.update w'' 194 (gIt N K (w 3) i)) 2 = List.replicate (N * K) false := by
          simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, w'']; exact hc'.zero
        rw [exec_mv_shift (v := gIt N K (w 3) i) (L := []) (by decide)
          (by rw [hz, List.length_replicate]; exact hgi) (by simp)]
        simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, hz, List.length_replicate,
          w'', p5, p195, hc'.zero, opd_eq hgi]
      have hcE : Consts N K (exec N K (ofList [.cp 194 195, .mv 196 194 2, .rotB 195 195 5]) w'') :=
        consts_exec (consts_update hc' 197 (by decide) _) _ rfl
      refine ⟨hcE, ?_, ?_, ?_, fun j hj => ?_⟩
      · rw [e2]; simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, w'', p5]
      · rw [e2]; simp only [Function.update_self, p5]
        rw [h5, gIt, gIt, Function.iterate_succ_apply']
      · rw [e2]; simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p196]
        have hlen : (gs i).length = i := by simp [gs]
        have := drop_append_flatten_succ (b := w 6) (vs := gs i) (x := gIt N K (w 3) i) hgi (hgl i)
        rw [hlen] at this
        rw [this]
        simp [gs, List.range_succ]
      · have hj1 : j ≠ 195 := fun e => hj (by rw [e, wr_g1C]; simp)
        have hj2 : j ≠ 196 := fun e => hj (by rw [e, wr_g1C]; simp)
        have hj3 : j ≠ 194 := fun e => hj (by rw [e, wr_g1C]; simp)
        have hj4 : j ≠ 197 := fun e => hj (by rw [e, wr_g1C]; simp)
        rw [e2, Function.update_of_ne hj1, Function.update_of_ne hj2, Function.update_of_ne hj3,
          Function.update_of_ne hj3]
        simp only [w'', Function.update_of_ne hj4]
        exact pf j hj)
  rw [h197] at hP
  obtain ⟨_, _, _, p196, pf⟩ := hP
  refine ⟨?_, fun j hj => by rw [e1]; exact pf j hj⟩
  rw [e1, p196, h6]
  have hfl : ((gs K).flatten).length = K * (N * K) := by
    rw [length_flatten_of (hgl K)]; simp [gs]
  have e2 : 2 * K * (N * K) = K * (N * K) + K * (N * K) := by ring
  rw [List.drop_append_of_le_length (by simp; omega), List.drop_replicate, e2,
    Nat.add_sub_cancel]

/-- **`193 :=` the word of `src` repeated `|cnt|` times** (`buf` a template of the total width,
`|src| = |reg 6|`). -/
def repC (cnt src buf : Fin 200) : Code :=
  ofList [.cp 193 buf, .cp 197 cnt, .rep 197 (ofList [.cp 194 src, .mv 193 194 6])]

theorem wr_repC (cnt src buf : Fin 200) : wr (repC cnt src buf) = [193, 197, 197, 194, 193, 194] :=
  rfl

theorem exec_repC (w : St) (cnt src buf : Fin 200) (hcnt : cnt.val < 180) (hsrc1 : src ≠ 193)
    (hsrc2 : src ≠ 197) (hsrc3 : src ≠ 194) (hbuf : buf.val < 180) (hs : (w src).length = (w 6).length)
    (hb : (w buf).length = (w cnt).length * (w 6).length) :
    (exec N K (repC cnt src buf) w) 193 = (List.replicate (w cnt).length (w src)).flatten ∧
      ∀ j, j ∉ wr (repC cnt src buf) → (exec N K (repC cnt src buf) w) j = w j := by
  set V := (w 6).length
  set w1 := exec N K (ofList [.cp 193 buf, .cp 197 cnt]) w with hw1
  have e1 : exec N K (repC cnt src buf) w =
      exec N K (.rep 197 (ofList [.cp 194 src, .mv 193 194 6])) w1 := rfl
  have w1_eq : w1 = Function.update (Function.update w 193 (w buf)) 197 (w cnt) := by
    simp only [hw1, exec_ofList_cons, exec_ofList_nil, exec]
    rw [Function.update_of_ne (lo_ne hcnt 193)]
  have h197 : (w1 197).length = (w cnt).length := by rw [w1_eq]; simp
  let P : ℕ → St → Prop := fun i w' =>
    w' 6 = w 6 ∧ w' src = w src ∧
      w' 193 = (w buf ++ (List.replicate i (w src)).flatten).drop (i * V) ∧
      ∀ j, j ∉ wr (repC cnt src buf) → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 197 (ofList [.cp 194 src, .mv 193 194 6]) (by
      intro hm; simp only [wr, wr_ofList, List.flatMap_cons, List.flatMap_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil] at hm; rcases hm with h | h | h | h | h | h <;>
        first | exact absurd h (by decide) | (subst h; exact hsrc2 rfl) | simp_all) P w1
    ⟨by rw [w1_eq]; simp, by rw [w1_eq, Function.update_of_ne hsrc2, Function.update_of_ne hsrc1],
      by rw [w1_eq]; simp,
      fun j hj => by
        rw [w1_eq, Function.update_of_ne (fun e => hj (by rw [e, wr_repC]; simp)),
          Function.update_of_ne (fun e => hj (by rw [e, wr_repC]; simp))]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨p6, psrc, p193, pf⟩ := hw'
      set w'' := Function.update w' 197 (w' 197).tail
      have e2 : exec N K (ofList [.cp 194 src, .mv 193 194 6]) w'' =
          Function.update (Function.update (Function.update w'' 194 (w src)) 194 [])
            193 ((w'' 193 ++ w src).drop V) := by
        simp only [exec_ofList_cons, exec_ofList_nil]
        rw [show exec N K (.cp 194 src) w'' = Function.update w'' 194 (w src) by
          simp only [exec, w'', Function.update_of_ne hsrc2, psrc]]
        rw [exec_mv_shift (v := w src) (L := []) (by decide) (by
          simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, w'', p6]; exact hs) (by simp)]
        simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, w'', p6]
        rfl
      refine ⟨?_, ?_, ?_, fun j hj => ?_⟩
      · rw [e2]; simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, w'', p6]
      · rw [e2, Function.update_of_ne hsrc1, Function.update_of_ne hsrc3,
          Function.update_of_ne hsrc3]
        simp only [w'', Function.update_of_ne hsrc2, psrc]
      · rw [e2]
        simp only [Function.update_self, w'', Function.update_of_ne (show (193 : Fin 200) ≠ 197
          by decide), p193]
        have := drop_append_flatten_succ (b := w buf) (vs := List.replicate i (w src)) (x := w src)
          hs (fun y hy => by rw [List.eq_of_mem_replicate hy]; exact hs)
        rw [List.length_replicate] at this
        rw [this, List.replicate_succ']
        simp [Nat.add_mul]
      · have hj1 : j ≠ 193 := fun e => hj (by rw [e, wr_repC]; simp)
        have hj2 : j ≠ 194 := fun e => hj (by rw [e, wr_repC]; simp)
        have hj3 : j ≠ 197 := fun e => hj (by rw [e, wr_repC]; simp)
        rw [e2, Function.update_of_ne hj1, Function.update_of_ne hj2, Function.update_of_ne hj2]
        simp only [w'', Function.update_of_ne hj3]
        exact pf j hj)
  rw [h197] at hP
  obtain ⟨_, _, p193, pf⟩ := hP
  refine ⟨?_, fun j hj => by rw [e1]; exact pf j hj⟩
  rw [e1, p193]
  have := drop_append_flatten (b := w buf) (vs := List.replicate (w cnt).length (w src)) (n := V)
    (by rw [List.length_replicate, hb])
  simpa using this

/-! ### Decoding the bit -/

theorem decide_window_eq_xor {v K : ℕ} (hK : 2 ≤ K) (hv : v < 2 ^ K) :
    decide (2 ^ (K - 2) ≤ v ∧ v < 3 * 2 ^ (K - 2)) = (v.testBit (K - 2) ^^ v.testBit (K - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hp : 0 < 2 ^ k := by positivity
  have hq : v / 2 ^ k < 4 := by
    rw [Nat.div_lt_iff_lt_mul hp]; calc v < 2 ^ (k + 2) := hv
      _ = 4 * 2 ^ k := by ring
  have h1 : v / 2 ^ (k + 1) = v / 2 ^ k / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [h1]
  have hlo : 2 ^ k ≤ v ↔ 1 ≤ v / 2 ^ k := by rw [Nat.le_div_iff_mul_le hp, one_mul]
  have hhi : v < 3 * 2 ^ k ↔ v / 2 ^ k < 3 := by rw [Nat.div_lt_iff_lt_mul hp]
  rw [show decide (2 ^ k ≤ v ∧ v < 3 * 2 ^ k) = decide (1 ≤ v / 2 ^ k ∧ v / 2 ^ k < 3) by
    simp only [hlo, hhi]]
  generalize v / 2 ^ k = q at hq ⊢
  interval_cases q <;> rfl

theorem getD_concatN_lt {n K : ℕ} {f : ℕ → List Bool} (hf : ∀ i < n, (f i).length = K) (hn : 0 < n)
    {j : ℕ} (hj : j < K) : (concatN n f).getD j false = (f 0).getD j false := by
  have hb := block_concatN hf 0
  rw [if_pos hn] at hb
  have : (concatN n f).getD j false = (block K 0 (concatN n f)).getD j false := by
    simp only [block, zero_mul, List.drop_zero, List.getD_eq_getElem?_getD,
      List.getElem?_take, hj, ↓reduceIte]
  rw [this, hb]

/-- The bits `K − 2`, `K − 1` of the constant coefficient of a canonical word. -/
theorem drop_encRM_bits {N K : ℕ} (hN : 0 < N) (hK : 2 ≤ K) (a : RM N K) :
    hd ((encRM N K a).drop (K - 2)) = (coefG a 0).val.testBit (K - 2) ∧
      hd (((encRM N K a).drop (K - 2)).tail) = (coefG a 0).val.testBit (K - 1) := by
  have hf : ∀ i < N, (encM K (coefG a i)).length = K := fun _ _ => length_encM _ _
  have g : ∀ j < K, (encRM N K a).getD j false = (coefG a 0).val.testBit j := fun j hj => by
    rw [encRM, getD_concatN_lt hf hN hj, encM, getD_toBits]; simp [hj]
  have hl : K ≤ (encRM N K a).length := by
    rw [length_encRM]; exact Nat.le_mul_of_pos_left K hN
  constructor
  · rw [← g (K - 2) (by omega)]
    rw [List.getD_eq_getElem _ _ (by omega)]
    rw [List.drop_eq_getElem_cons (by omega)]; rfl
  · rw [← g (K - 1) (by omega)]
    rw [List.getD_eq_getElem _ _ (by omega)]
    rw [List.drop_eq_getElem_cons (show K - 2 < (encRM N K a).length by omega), List.tail_cons,
      show K - 2 + 1 = K - 1 by omega,
      List.drop_eq_getElem_cons (show K - 1 < (encRM N K a).length by omega)]
    rfl

/-- **The decoded bit** of the canonical word on register `191` into register `179`. -/
def decC : Code :=
  ofList [.cp 185 191, .drop 185 15,
    .ifb 185 (ofList [.tl 185, .ifb 185 (.cp 179 1) (.cp 179 75)])
      (ofList [.tl 185, .ifb 185 (.cp 179 75) (.cp 179 1)])]

theorem exec_decC (hN : 0 < N) (hK : 2 ≤ K) (w : St) (hc : Consts N K w) (h15 : (w 15).length = K - 2)
    (h75 : w 75 = [true]) (a : RM N K) (h191 : w 191 = encRM N K a) :
    (exec N K decC w) 179 =
      [decide (2 ^ (K - 2) ≤ (coefG a 0).val ∧ (coefG a 0).val < 3 * 2 ^ (K - 2))] := by
  have hv : (coefG a 0).val < 2 ^ K := by
    have := ZMod.val_lt (coefG a 0)
    have : 2 ^ K - 1 < 2 ^ K := Nat.sub_lt (by positivity) one_pos
    omega
  rw [decide_window_eq_xor hK hv]
  obtain ⟨b1, b2⟩ := drop_encRM_bits hN hK a
  simp only [decC, exec_ofList_cons, exec_ofList_nil, exec, Function.update_apply, Fin.reduceEq,
    ↓reduceIte, h191, h15, show ¬((185 : Fin 200) = 15) by decide]
  rw [b1]
  cases h1 : (coefG a 0).val.testBit (K - 2) <;> simp only [↓reduceIte, Bool.false_eq_true] <;>
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, b2] <;>
    cases h2 : (coefG a 0).val.testBit (K - 1) <;> simp [hc.one, h75]

/-! ### The key sums assembled -/

/-- Part `β`: `acc := Σ_{i<W} Σ_{c ∈ BCol} σ^i(b − B⁽²⁾)_c k`. -/
def finBC : Code := ofList [.cp 192 66, .cp 193 58, .cp 194 2, .cp 195 2, subVecC 17 16,
  .cp 180 2, .cp 182 65, .cp 183 2, .cp 184 2, conjC 17 16]

/-- The inputs of the key sums. -/
structure FinIn (N K : ℕ) (w : St) (bs B2s ks : List (List Bool)) : Prop where
  c : Consts N K w
  r16 : (w 16).length = (w 17).length * (N * K)
  b : w 66 = bs.flatten
  B2 : w 58 = B2s.flatten
  key : w 65 = ks.flatten
  bsl : bs.length = (w 17).length
  B2l : B2s.length = (w 17).length
  ksl : (w 12).length * (w 17).length ≤ ks.length
  bsw : ∀ x ∈ bs, x.length = N * K
  B2w : ∀ x ∈ B2s, x.length = N * K
  ksw : ∀ x ∈ ks, x.length = N * K

theorem exec_finBC (hN : 0 < N) (w : St) {bs B2s ks : List (List Bool)} (h : FinIn N K w bs B2s ks) :
    (exec N K finBC w) 182 = (ks.drop ((w 12).length * (w 17).length)).flatten ∧
      ((exec N K finBC w) 180).length = N * K ∧
      decRM N K ((exec N K finBC w) 180) =
        conjL (autMW N K (w 20).length) (List.zipWith (subRMW N K) bs B2s) ks (w 17).length
          (w 12).length ∧
      ∀ j : Fin 200, j.val < 180 → (exec N K finBC w) j = w j := by
  have hc := h.c
  set s1 := Function.update (Function.update (Function.update (Function.update w 192 (w 66)) 193
    (w 58)) 194 (w 2)) 195 (w 2) with hs1
  have hs1lo : ∀ j : Fin 200, j.val < 180 → s1 j = w j := fun j hj => by
    rw [hs1, Function.update_of_ne (lo_ne hj 195), Function.update_of_ne (lo_ne hj 194),
      Function.update_of_ne (lo_ne hj 193), Function.update_of_ne (lo_ne hj 192)]
  have hc1 : Consts N K s1 := consts_of_agree hc fun j hj => hs1lo j (by omega)
  obtain ⟨a188, -, -, -, -, af⟩ := exec_subVecC s1 hc1 17 16 (by decide) (by decide)
    (La := []) (Lb := []) h.bsw h.B2w (by rw [hs1lo 17 (by decide)]; exact h.bsl)
    (by rw [hs1lo 17 (by decide)]; exact h.B2l)
    (by rw [hs1lo 17 (by decide), hs1lo 16 (by decide)]; exact h.r16)
    (by simp [hs1, h.b]) (by simp [hs1, h.B2]) (by simp [hs1, hc.zero]) (by simp [hs1, hc.zero])
  set s2 := exec N K (subVecC 17 16) s1
  have hs2lo : ∀ j : Fin 200, j.val < 180 → s2 j = w j := fun j hj => by
    rw [af j (not_mem_hi hj rfl), hs1lo j hj]
  set s3 := Function.update (Function.update (Function.update (Function.update s2 180 (s2 2)) 182
    (s2 65)) 183 (s2 2)) 184 (s2 2) with hs3
  have hs3lo : ∀ j : Fin 200, j.val < 180 → s3 j = w j := fun j hj => by
    rw [hs3, Function.update_of_ne (lo_ne hj 184), Function.update_of_ne (lo_ne hj 183),
      Function.update_of_ne (lo_ne hj 182), Function.update_of_ne (lo_ne hj 180), hs2lo j hj]
  have hc3 : Consts N K s3 := consts_of_agree hc fun j hj => hs3lo j (by omega)
  have hxs : ∀ x ∈ List.zipWith (subRMW N K) bs B2s, x.length = N * K := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_zipWith]
    exact length_subRMW N K (h.bsw _ (List.getElem_mem _)) _
  have e : exec N K finBC w = exec N K (conjC 17 16) s3 := rfl
  obtain ⟨c182, c180, cd, cf⟩ := exec_conjC hN s3 hc3 17 16 (by decide) (by decide) (L' := [])
    hxs h.ksw (by rw [hs3lo 17 (by decide)]; simp [h.bsl, h.B2l])
    (by rw [hs3lo 17 (by decide), hs3lo 12 (by decide)]; exact h.ksl)
    (by rw [hs3lo 17 (by decide), hs3lo 16 (by decide)]; exact h.r16)
    (by simp only [hs3, Function.update_apply, Fin.reduceEq, ↓reduceIte]; exact a188)
    (by simp only [hs3, Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [hs2lo 65 (by decide), h.key, List.append_nil])
    (by simp only [hs3, Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [hs2lo 2 (by decide), hc.zero, List.length_replicate])
    (by simp only [hs3, Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [hs2lo 2 (by decide), hc.zero, List.length_replicate])
    (by simp only [hs3, Function.update_apply, Fin.reduceEq, ↓reduceIte]
        rw [hs2lo 2 (by decide), hc.zero, List.length_replicate])
  rw [hs3lo 12 (by decide), hs3lo 17 (by decide), hs3lo 20 (by decide)] at *
  refine ⟨by rw [e, c182, List.append_nil], by rw [e]; exact c180, ?_, ?_⟩
  · rw [e, cd]
    simp only [hs3, Function.update_apply, Fin.reduceEq, ↓reduceIte]
    rw [hs2lo 2 (by decide), hc.zero, decRM_replicate, zero_add]
  · intro j hj; rw [e, cf j (not_mem_hi hj rfl), hs3lo j hj]

/-- Part `η`: `acc += Σ_{i<W} Σ_{k,c} σ^i(h − (H⁽²⁾ − G⁽²⁾))_{k,c} k`. -/
def finHC : Code := ofList [.cp 192 59, .cp 199 19, halvesC 74, g1C, repC 74 196 19,
  .cp 192 199, .cp 194 2, .cp 195 2, subVecC 18 19,
  .cp 193 188, .cp 192 67, .cp 194 2, .cp 195 2, subVecC 18 19,
  .cp 183 2, .cp 184 2, conjC 18 19]

/-- The words of the gadget row `G⁽²⁾`. -/
def g1W (N K : ℕ) (one : List Bool) : List (List Bool) :=
  List.replicate K (List.replicate (N * K) false) ++ (List.range K).map (gIt N K one)

/-- The inputs of part `η`. -/
structure FinHIn (N K : ℕ) (w : St) (Hps : List (List (List Bool) × List (List Bool)))
    (hs ks : List (List Bool)) : Prop where
  c : Consts N K w
  r3 : (w 3).length = N * K
  r5 : (w 5).length = K - 1
  r6 : w 6 = List.replicate (2 * K * (N * K)) false
  r8 : (w 8).length = 2 * K
  r18 : (w 18).length = (w 74).length * (2 * K)
  r19 : (w 19).length = (w 18).length * (N * K)
  H : w 59 = (Hps.map fun p => p.1.flatten ++ p.2.flatten).flatten
  Hl : Hps.length = (w 74).length
  Hw : ∀ p ∈ Hps, p.1.length = 2 * K ∧ p.2.length = 2 * K ∧ (∀ x ∈ p.1, x.length = N * K) ∧
    ∀ x ∈ p.2, x.length = N * K
  h : w 67 = hs.flatten
  hl : hs.length = (w 18).length
  hw : ∀ x ∈ hs, x.length = N * K
  key : w 182 = ks.flatten
  ksl : (w 12).length * (w 18).length ≤ ks.length
  ksw : ∀ x ∈ ks, x.length = N * K
  acc : (w 180).length = N * K

set_option maxHeartbeats 2000000 in
theorem exec_finHC (hN : 0 < N) (hK : 0 < K) (w : St) {Hps : List (List (List Bool) × List (List Bool))}
    {hs ks : List (List Bool)} (h : FinHIn N K w Hps hs ks) :
    (exec N K finHC w) 182 = (ks.drop ((w 12).length * (w 18).length)).flatten ∧
      ((exec N K finHC w) 180).length = N * K ∧
      decRM N K ((exec N K finHC w) 180) = decRM N K (w 180) +
        conjL (autMW N K (w 20).length)
          (List.zipWith (subRMW N K) hs (List.zipWith (subRMW N K) (Hps.map Prod.snd).flatten
            (List.replicate (w 74).length (g1W N K (w 3))).flatten)) ks (w 18).length
          (w 12).length ∧
      ∀ j : Fin 200, j.val < 180 → (exec N K finHC w) j = w j := by
  have hc := h.c
  set m := (w 74).length
  set H1s := (Hps.map Prod.snd).flatten
  set G1s := (List.replicate m (g1W N K (w 3))).flatten
  have hw6 : (w 6).length = 2 * K * (N * K) := by rw [h.r6, List.length_replicate]
  have hflat : ∀ l : List (List Bool), (∀ x ∈ l, x.length = N * K) → l.length = 2 * K →
      l.flatten.length = (w 6).length := fun l hl hl2 => by
    rw [length_flatten_of hl, hl2, hw6]
  -- stage 1: the rows H⁽²⁾
  set t1 := Function.update (Function.update w 192 (w 59)) 199 (w 19) with ht1
  have t1lo : ∀ j : Fin 200, j.val < 180 → t1 j = w j := fun j hj => by
    rw [ht1, Function.update_of_ne (lo_ne hj 199), Function.update_of_ne (lo_ne hj 192)]
  set Hps' := Hps.map fun p => (p.1.flatten, p.2.flatten)
  obtain ⟨a199, -, af⟩ := exec_halvesC (N := N) (K := K) t1 74 (by decide) (ps := Hps') (L := [])
    (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨h1, h2, h3, h4⟩ := h.Hw q hq
      exact ⟨by rw [t1lo 6 (by decide)]; exact hflat _ h3 h1,
        by rw [t1lo 6 (by decide)]; exact hflat _ h4 h2⟩)
    (by rw [t1lo 74 (by decide)]; simp [Hps', h.Hl, m])
    (by simp only [ht1, Function.update_apply, Fin.reduceEq, ↓reduceIte, h.H, List.append_nil,
      Hps', List.map_map]; rfl)
    (by rw [show t1 199 = w 19 by simp [ht1], t1lo 6 (by decide), h.r19, h.r18, hw6]
        simp [Hps', h.Hl]; ring)
  set t2 := exec N K (halvesC 74) t1
  have t2lo : ∀ j : Fin 200, j.val < 180 → t2 j = w j := fun j hj => by
    rw [af j (not_mem_hi hj rfl), t1lo j hj]
  have hc2 : Consts N K t2 := consts_of_agree hc fun j hj => t2lo j (by omega)
  -- stage 2: G⁽²⁾ and its repetitions
  obtain ⟨g196, gf⟩ := exec_g1C t2 hc2 (by rw [t2lo 6 (by decide)]; exact h.r6)
    (by rw [t2lo 3 (by decide)]; exact h.r3) (by rw [t2lo 5 (by decide)]; exact h.r5)
  set t3 := exec N K g1C t2
  have t3lo : ∀ j : Fin 200, j.val < 180 → t3 j = w j := fun j hj => by
    rw [gf j (not_mem_hi hj rfl), t2lo j hj]
  have hg1 : (g1W N K (w 3)).flatten = t3 196 := by
    rw [g196, t2lo 3 (by decide), g1W, List.flatten_append, List.flatten_replicate_replicate]
  have hg1w : ∀ x ∈ g1W N K (w 3), x.length = N * K := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.eq_of_mem_replicate hx, List.length_replicate]
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx; exact length_gIt h.r3 k
  have hg1l : (g1W N K (w 3)).length = 2 * K := by simp [g1W]; ring
  obtain ⟨r193, rf⟩ := exec_repC (N := N) (K := K) t3 74 196 19 (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by rw [← hg1, t3lo 6 (by decide)]; exact hflat _ hg1w hg1l)
    (by rw [t3lo 19 (by decide), t3lo 74 (by decide), t3lo 6 (by decide), h.r19, h.r18, hw6]; ring)
  set t4 := exec N K (repC 74 196 19) t3
  have t4lo : ∀ j : Fin 200, j.val < 180 → t4 j = w j := fun j hj => by
    rw [rf j (not_mem_hi hj rfl), t3lo j hj]
  have t4_199 : t4 199 = H1s.flatten := by
    rw [rf 199 (by rw [wr_repC]; simp), gf 199 (by rw [wr_g1C]; simp), a199]
    simp only [Hps', List.map_map, H1s]
    rw [List.flatten_flatten]; simp [Function.comp_def]
  have t4_193 : t4 193 = G1s.flatten := by
    rw [r193, t3lo 74 (by decide), ← hg1]
    simp only [G1s, List.flatten_flatten, List.map_replicate]; rfl
  -- stage 3: H⁽²⁾ − G⁽²⁾
  set t5 := Function.update (Function.update (Function.update t4 192 (t4 199)) 194 (t4 2)) 195
    (t4 2) with ht5
  have t5lo : ∀ j : Fin 200, j.val < 180 → t5 j = w j := fun j hj => by
    rw [ht5, Function.update_of_ne (lo_ne hj 195), Function.update_of_ne (lo_ne hj 194),
      Function.update_of_ne (lo_ne hj 192), t4lo j hj]
  have hc5 : Consts N K t5 := consts_of_agree hc fun j hj => t5lo j (by omega)
  have H1w : ∀ x ∈ H1s, x.length = N * K := fun x hx => by
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
    exact (h.Hw q hq).2.2.2 x hxl
  have H1l : H1s.length = (w 18).length := by
    rw [List.length_flatten, h.r18, List.map_map]
    have : Hps.map (List.length ∘ Prod.snd) = Hps.map fun _ => 2 * K :=
      List.map_congr_left fun p hp => (h.Hw p hp).2.1
    rw [this, List.map_const', List.sum_replicate, h.Hl, smul_eq_mul]
  have G1w : ∀ x ∈ G1s, x.length = N * K := fun x hx => by
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
    rw [List.eq_of_mem_replicate hl] at hxl; exact hg1w x hxl
  have G1l : G1s.length = (w 18).length := by
    simp only [G1s, List.length_flatten, List.map_replicate, List.sum_replicate, hg1l, h.r18,
      smul_eq_mul, m]
  obtain ⟨b188, -, -, b194, b195, bf⟩ := exec_subVecC t5 hc5 18 19 (by decide) (by decide)
    (La := []) (Lb := []) H1w G1w (by rw [t5lo 18 (by decide)]; exact H1l)
    (by rw [t5lo 18 (by decide)]; exact G1l)
    (by rw [t5lo 18 (by decide), t5lo 19 (by decide)]; exact h.r19)
    (by simp only [ht5, Function.update_apply, Fin.reduceEq, ↓reduceIte, t4_199, List.append_nil])
    (by simp only [ht5, Function.update_apply, Fin.reduceEq, ↓reduceIte, t4_193, List.append_nil])
    (by simp only [ht5, Function.update_apply, Fin.reduceEq, ↓reduceIte, t4lo 2 (by decide),
      hc.zero, List.length_replicate])
    (by simp only [ht5, Function.update_apply, Fin.reduceEq, ↓reduceIte, t4lo 2 (by decide),
      hc.zero, List.length_replicate])
  set t6 := exec N K (subVecC 18 19) t5
  have t6lo : ∀ j : Fin 200, j.val < 180 → t6 j = w j := fun j hj => by
    rw [bf j (not_mem_hi hj rfl), t5lo j hj]
  -- stage 4: h − (H⁽²⁾ − G⁽²⁾)
  set xs1 := List.zipWith (subRMW N K) H1s G1s
  have xs1w : ∀ x ∈ xs1, x.length = N * K := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_zipWith]
    exact length_subRMW N K (H1w _ (List.getElem_mem _)) _
  have xs1l : xs1.length = (w 18).length := by simp [xs1, H1l, G1l]
  set t7 := Function.update (Function.update (Function.update (Function.update t6 193 (t6 188)) 192
    (t6 67)) 194 (t6 2)) 195 (t6 2) with ht7
  have t7lo : ∀ j : Fin 200, j.val < 180 → t7 j = w j := fun j hj => by
    rw [ht7, Function.update_of_ne (lo_ne hj 195), Function.update_of_ne (lo_ne hj 194),
      Function.update_of_ne (lo_ne hj 192), Function.update_of_ne (lo_ne hj 193), t6lo j hj]
  have hc7 : Consts N K t7 := consts_of_agree hc fun j hj => t7lo j (by omega)
  obtain ⟨d188, -, -, -, -, df⟩ := exec_subVecC t7 hc7 18 19 (by decide) (by decide)
    (La := []) (Lb := []) h.hw xs1w (by rw [t7lo 18 (by decide)]; exact h.hl)
    (by rw [t7lo 18 (by decide)]; exact xs1l)
    (by rw [t7lo 18 (by decide), t7lo 19 (by decide)]; exact h.r19)
    (by simp only [ht7, Function.update_apply, Fin.reduceEq, ↓reduceIte, t6lo 67 (by decide), h.h,
      List.append_nil])
    (by simp only [ht7, Function.update_apply, Fin.reduceEq, ↓reduceIte, b188, List.append_nil])
    (by simp only [ht7, Function.update_apply, Fin.reduceEq, ↓reduceIte, t6lo 2 (by decide),
      hc.zero, List.length_replicate])
    (by simp only [ht7, Function.update_apply, Fin.reduceEq, ↓reduceIte, t6lo 2 (by decide),
      hc.zero, List.length_replicate])
  set t8 := exec N K (subVecC 18 19) t7
  have t8lo : ∀ j : Fin 200, j.val < 180 → t8 j = w j := fun j hj => by
    rw [df j (not_mem_hi hj rfl), t7lo j hj]
  -- stage 5: the sums
  set xs2 := List.zipWith (subRMW N K) hs xs1
  have xs2w : ∀ x ∈ xs2, x.length = N * K := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_zipWith]
    exact length_subRMW N K (h.hw _ (List.getElem_mem _)) _
  set t9 := Function.update (Function.update t8 183 (t8 2)) 184 (t8 2) with ht9
  have t9lo : ∀ j : Fin 200, j.val < 180 → t9 j = w j := fun j hj => by
    rw [ht9, Function.update_of_ne (lo_ne hj 184), Function.update_of_ne (lo_ne hj 183), t8lo j hj]
  have hc9 : Consts N K t9 := consts_of_agree hc fun j hj => t9lo j (by omega)
  -- registers 180, 182 are untouched by the stages before the sums
  have t8_180 : t8 180 = w 180 := by
    rw [df 180 (by rw [wr_subVecC]; simp), ht7]
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
    rw [bf 180 (by rw [wr_subVecC]; simp), ht5]
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
    rw [rf 180 (by rw [wr_repC]; simp), gf 180 (by rw [wr_g1C]; simp),
      af 180 (by rw [wr_halvesC]; simp), ht1]
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
  have t8_182 : t8 182 = w 182 := by
    rw [df 182 (by rw [wr_subVecC]; simp), ht7]
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
    rw [bf 182 (by rw [wr_subVecC]; simp), ht5]
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
    rw [rf 182 (by rw [wr_repC]; simp), gf 182 (by rw [wr_g1C]; simp),
      af 182 (by rw [wr_halvesC]; simp), ht1]
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
  have e : exec N K finHC w = exec N K (conjC 18 19) t9 := rfl
  obtain ⟨c182, c180, cd, cf⟩ := exec_conjC hN t9 hc9 18 19 (by decide) (by decide) (L' := [])
    xs2w h.ksw (by rw [t9lo 18 (by decide)]; simp [xs2, h.hl, xs1l])
    (by rw [t9lo 18 (by decide), t9lo 12 (by decide)]; exact h.ksl)
    (by rw [t9lo 18 (by decide), t9lo 19 (by decide)]; exact h.r19)
    (by simp only [ht9, Function.update_apply, Fin.reduceEq, ↓reduceIte, d188])
    (by simp only [ht9, Function.update_apply, Fin.reduceEq, ↓reduceIte, t8_182, h.key,
      List.append_nil])
    (by simp only [ht9, Function.update_apply, Fin.reduceEq, ↓reduceIte, t8lo 2 (by decide),
      hc.zero, List.length_replicate])
    (by simp only [ht9, Function.update_apply, Fin.reduceEq, ↓reduceIte, t8lo 2 (by decide),
      hc.zero, List.length_replicate])
    (by simp only [ht9, Function.update_apply, Fin.reduceEq, ↓reduceIte, t8_180]; exact h.acc)
  rw [t9lo 12 (by decide), t9lo 18 (by decide), t9lo 20 (by decide)] at *
  refine ⟨by rw [e, c182, List.append_nil], by rw [e]; exact c180, ?_, ?_⟩
  · rw [e, cd]
    simp only [ht9, Function.update_apply, Fin.reduceEq, ↓reduceIte, t8_180]
  · intro j hj; rw [e, cf j (not_mem_hi hj rfl), t9lo j hj]

/-- Part `c_F`: `acc += Σ_c (c_F − A_F⁽²⁾)_c k_c` (`c_F` on `176`, `A_F` on `177`). -/
def finFC : Code := ofList [.cp 192 176, .cp 193 177, .drop 193 6, .cp 194 2, .cp 195 2, subVecC 8 6,
  .cp 181 188, .cp 183 2, .cp 184 2, dotC 8]

theorem exec_finFC (w : St) (hc : Consts N K w) {cFs AF0s AF1s ks : List (List Bool)}
    (r6 : w 6 = List.replicate (2 * K * (N * K)) false) (r8 : (w 8).length = 2 * K)
    (hcF : w 176 = cFs.flatten) (hAF : w 177 = AF0s.flatten ++ AF1s.flatten)
    (hcFl : cFs.length = 2 * K) (hA0 : AF0s.length = 2 * K) (hA1 : AF1s.length = 2 * K)
    (hcFw : ∀ x ∈ cFs, x.length = N * K) (hA0w : ∀ x ∈ AF0s, x.length = N * K)
    (hA1w : ∀ x ∈ AF1s, x.length = N * K) (hk : w 182 = ks.flatten) (hkl : 2 * K ≤ ks.length)
    (hkw : ∀ x ∈ ks, x.length = N * K) (hacc : (w 180).length = N * K) :
    ((exec N K finFC w) 180).length = N * K ∧
      decRM N K ((exec N K finFC w) 180) = decRM N K (w 180) +
        dotL (List.zipWith (subRMW N K) cFs AF1s) ks (2 * K) ∧
      ∀ j : Fin 200, j.val < 180 → (exec N K finFC w) j = w j := by
  have hw6 : (w 6).length = 2 * K * (N * K) := by rw [r6, List.length_replicate]
  set t1 := exec N K (ofList [.cp 192 176, .cp 193 177, .drop 193 6, .cp 194 2, .cp 195 2]) w
    with ht1
  have t1_eq : t1 = Function.update (Function.update (Function.update (Function.update w 192
      (w 176)) 193 AF1s.flatten) 194 (w 2)) 195 (w 2) := by
    simp only [ht1, exec_ofList_cons, exec_ofList_nil, exec, Function.update_apply, Fin.reduceEq,
      ↓reduceIte, Function.update_idem, hAF]
    rw [List.drop_left' (by rw [length_flatten_of hA0w, hA0, hw6]; try ring)]
  have t1lo : ∀ j : Fin 200, j.val < 180 → t1 j = w j := fun j hj => by
    rw [t1_eq, Function.update_of_ne (lo_ne hj 195), Function.update_of_ne (lo_ne hj 194),
      Function.update_of_ne (lo_ne hj 193), Function.update_of_ne (lo_ne hj 192)]
  have hc1 : Consts N K t1 := consts_of_agree hc fun j hj => t1lo j (by omega)
  obtain ⟨a188, -, -, -, -, af⟩ := exec_subVecC t1 hc1 8 6 (by decide) (by decide)
    (La := []) (Lb := []) hcFw hA1w (by rw [t1lo 8 (by decide), r8]; exact hcFl)
    (by rw [t1lo 8 (by decide), r8]; exact hA1)
    (by rw [t1lo 8 (by decide), t1lo 6 (by decide), r8, hw6])
    (by simp [t1_eq, hcF]) (by simp [t1_eq])
    (by simp [t1_eq, hc.zero]) (by simp [t1_eq, hc.zero])
  set t2 := exec N K (subVecC 8 6) t1
  have t2lo : ∀ j : Fin 200, j.val < 180 → t2 j = w j := fun j hj => by
    rw [af j (not_mem_hi hj rfl), t1lo j hj]
  have t2_180 : t2 180 = w 180 := by
    rw [af 180 (by rw [wr_subVecC]; simp), t1_eq]; simp
  have t2_182 : t2 182 = w 182 := by
    rw [af 182 (by rw [wr_subVecC]; simp), t1_eq]; simp
  set xs := List.zipWith (subRMW N K) cFs AF1s
  have xsw : ∀ x ∈ xs, x.length = N * K := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_zipWith]
    exact length_subRMW N K (hcFw _ (List.getElem_mem _)) _
  set t3 := Function.update (Function.update (Function.update t2 181 (t2 188)) 183 (t2 2)) 184
    (t2 2) with ht3
  have t3lo : ∀ j : Fin 200, j.val < 180 → t3 j = w j := fun j hj => by
    rw [ht3, Function.update_of_ne (lo_ne hj 184), Function.update_of_ne (lo_ne hj 183),
      Function.update_of_ne (lo_ne hj 181), t2lo j hj]
  have hc3 : Consts N K t3 := consts_of_agree hc fun j hj => t3lo j (by omega)
  have e : exec N K finFC w = exec N K (dotC 8) t3 := rfl
  obtain ⟨-, -, -, -, d180, dd, df⟩ := exec_dotC t3 hc3 8 (by decide) (L := []) (L' := []) xsw hkw
    (by rw [t3lo 8 (by decide), r8]; simp [xs, hcFl, hA1])
    (by rw [t3lo 8 (by decide), r8]; exact hkl)
    (by simp only [ht3, Function.update_apply, Fin.reduceEq, ↓reduceIte, a188, List.append_nil])
    (by simp only [ht3, Function.update_apply, Fin.reduceEq, ↓reduceIte, t2_182, hk,
      List.append_nil])
    (by simp only [ht3, Function.update_apply, Fin.reduceEq, ↓reduceIte, t2lo 2 (by decide),
      hc.zero, List.length_replicate])
    (by simp only [ht3, Function.update_apply, Fin.reduceEq, ↓reduceIte, t2lo 2 (by decide),
      hc.zero, List.length_replicate])
    (by simp only [ht3, Function.update_apply, Fin.reduceEq, ↓reduceIte, t2_180]; exact hacc)
  rw [t3lo 8 (by decide), r8] at dd
  refine ⟨by rw [e]; exact d180, ?_, fun j hj => ?_⟩
  · rw [e, dd]
    simp only [ht3, Function.update_apply, Fin.reduceEq, ↓reduceIte, t2_180]
  · rw [e, df j (not_mem_hi hj rfl), t3lo j hj]

/-- **`μ' = c_m − d₂ − acc`, canonical, decoded** into register `179` (`d` on `64`, `c_m` on
`72`). -/
def outC : Code := ofList [.cp 190 64, .cp 191 2, .mv 191 190 2, .mv 191 190 2, .sub 191 72 191,
  .sub 191 191 180, .canon 191 191, decC]

theorem exec_outC (hN : 0 < N) (hK : 2 ≤ K) (w : St) (hc : Consts N K w)
    (h15 : (w 15).length = K - 2) (h75 : w 75 = [true]) {d0 d1 : List Bool}
    (hd0 : d0.length = N * K) (hd1 : d1.length = N * K) (h64 : w 64 = d0 ++ d1)
    (h72 : (w 72).length = N * K) (h180 : (w 180).length = N * K) :
    (exec N K outC w) 179 = [decide (2 ^ (K - 2) ≤ (coefG (decRM N K (w 72) - decRM N K d1 -
        decRM N K (w 180)) 0).val ∧ (coefG (decRM N K (w 72) - decRM N K d1 -
        decRM N K (w 180)) 0).val < 3 * 2 ^ (K - 2))] := by
  have hK0 : 0 < K := by omega
  set t1 := exec N K (ofList [.cp 190 64, .cp 191 2, .mv 191 190 2, .mv 191 190 2]) w with ht1
  have t1_eq : t1 = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update w 190 (w 64)) 191 (w 2)) 190 d1) 191 d0) 190 []) 191 d1 := by
    simp only [ht1, exec_ofList_cons, exec_ofList_nil]
    rw [show exec N K (.cp 191 2) (exec N K (.cp 190 64) w) =
      Function.update (Function.update w 190 (w 64)) 191 (w 2) from rfl]
    have s2 : exec N K (.mv 191 190 2) (Function.update (Function.update w 190 (w 64)) 191 (w 2)) =
        Function.update (Function.update (Function.update (Function.update w 190 (w 64)) 191 (w 2))
          190 d1) 191 d0 :=
      exec_mv_pop (v := d0) (L := d1) (by decide) (by simp [hc.zero])
        (by simp [hc.zero, hd0]) (by simp [h64])
    rw [s2]
    exact exec_mv_pop (v := d1) (L := []) (by decide) (by simp [hc.zero, hd0])
      (by simp [hc.zero, hd1]) (by simp)
  have hs1 := length_subRMW N K h72 d1
  have hs2 := length_subRMW N K hs1 (w 180)
  have e : exec N K outC w = exec N K decC (Function.update t1 191
      (canonW N K (subRMW N K (subRMW N K (w 72) d1) (w 180)))) := by
    show exec N K decC (exec N K (.canon 191 191) (exec N K (.sub 191 191 180)
      (exec N K (.sub 191 72 191) t1))) = _
    simp only [exec, t1_eq, Function.update_apply, Fin.reduceEq, ↓reduceIte, Function.update_idem,
      opd_eq h72, opd_eq hd1, opd_eq hs1, opd_eq h180, opd_eq hs2]
  rw [e, exec_decC hN hK _ (consts_of_agree hc fun j hj => by
      rw [Function.update_of_ne (by intro h; subst h; simp at hj), t1_eq]
      simp only [Function.update_apply]
      split_ifs <;> first | rfl | (exfalso; subst_vars; simp at hj))
    (by simp [t1_eq, h15]) (by simp [t1_eq, h75])
    (decRM N K (subRMW N K (subRMW N K (w 72) d1) (w 180)))
    (by simp only [Function.update_self]; rw [canonW_eq hK0 hs2])]
  rw [decRM_subRMW hs1 h180, decRM_subRMW h72 hd1]

/-! ### The end of decryption -/

/-- **The end of decryption**: the three key sums, `μ'`, its decoded bit on register `179`. -/
def finC : Code := ofList [finBC, finHC, finFC, outC]

/-- The inputs of the end of decryption (on the registers below `180`). -/
structure FinAll (N K : ℕ) (w : St) (bs B2s : List (List Bool))
    (Hps : List (List (List Bool) × List (List Bool))) (hs cFs AF0s AF1s ks : List (List Bool))
    (d0 d1 : List Bool) : Prop where
  fin : FinIn N K w bs B2s ks
  r3 : (w 3).length = N * K
  r5 : (w 5).length = K - 1
  r6 : w 6 = List.replicate (2 * K * (N * K)) false
  r8 : (w 8).length = 2 * K
  r15 : (w 15).length = K - 2
  r18 : (w 18).length = (w 74).length * (2 * K)
  r19 : (w 19).length = (w 18).length * (N * K)
  r75 : w 75 = [true]
  H : w 59 = (Hps.map fun p => p.1.flatten ++ p.2.flatten).flatten
  Hl : Hps.length = (w 74).length
  Hw : ∀ p ∈ Hps, p.1.length = 2 * K ∧ p.2.length = 2 * K ∧ (∀ x ∈ p.1, x.length = N * K) ∧
    ∀ x ∈ p.2, x.length = N * K
  h : w 67 = hs.flatten
  hl : hs.length = (w 18).length
  hw : ∀ x ∈ hs, x.length = N * K
  ksl : (w 12).length * (w 17).length + (w 12).length * (w 18).length + 2 * K ≤ ks.length
  cF : w 176 = cFs.flatten
  AF : w 177 = AF0s.flatten ++ AF1s.flatten
  cFl : cFs.length = 2 * K
  A0l : AF0s.length = 2 * K
  A1l : AF1s.length = 2 * K
  cFw : ∀ x ∈ cFs, x.length = N * K
  A0w : ∀ x ∈ AF0s, x.length = N * K
  A1w : ∀ x ∈ AF1s, x.length = N * K
  d : w 64 = d0 ++ d1
  d0l : d0.length = N * K
  d1l : d1.length = N * K
  cm : (w 72).length = N * K

/-- The value of `μ'` the end of decryption decodes. -/
noncomputable def finVal (N K : ℕ) (w : St) (bs B2s : List (List Bool))
    (Hps : List (List (List Bool) × List (List Bool))) (hs cFs AF1s ks : List (List Bool))
    (d1 : List Bool) : RM N K :=
  decRM N K (w 72) - decRM N K d1 -
    (conjL (autMW N K (w 20).length) (List.zipWith (subRMW N K) bs B2s) ks (w 17).length
        (w 12).length +
      conjL (autMW N K (w 20).length)
          (List.zipWith (subRMW N K) hs (List.zipWith (subRMW N K) (Hps.map Prod.snd).flatten
            (List.replicate (w 74).length (g1W N K (w 3))).flatten))
          (ks.drop ((w 12).length * (w 17).length)) (w 18).length (w 12).length +
      dotL (List.zipWith (subRMW N K) cFs AF1s)
          ((ks.drop ((w 12).length * (w 17).length)).drop ((w 12).length * (w 18).length)) (2 * K))

/-- **The end of decryption.** -/
theorem exec_finC (hN : 0 < N) (hK : 2 ≤ K) (w : St) {bs B2s : List (List Bool)}
    {Hps : List (List (List Bool) × List (List Bool))} {hs cFs AF0s AF1s ks : List (List Bool)}
    {d0 d1 : List Bool} (h : FinAll N K w bs B2s Hps hs cFs AF0s AF1s ks d0 d1) :
    (exec N K finC w) 179 = [decide (2 ^ (K - 2) ≤ (coefG (finVal N K w bs B2s Hps hs cFs AF1s ks d1)
        0).val ∧ (coefG (finVal N K w bs B2s Hps hs cFs AF1s ks d1) 0).val < 3 * 2 ^ (K - 2))] := by
  have hc := h.fin.c
  obtain ⟨b182, b180, bd, bf⟩ := exec_finBC hN w h.fin
  set w1 := exec N K finBC w
  have hk1 : w1 182 = (ks.drop ((w 12).length * (w 17).length)).flatten := b182
  have hH : FinHIn N K w1 Hps hs (ks.drop ((w 12).length * (w 17).length)) :=
    { c := consts_of_agree hc fun j hj => bf j (by omega)
      r3 := by rw [bf 3 (by decide)]; exact h.r3
      r5 := by rw [bf 5 (by decide)]; exact h.r5
      r6 := by rw [bf 6 (by decide)]; exact h.r6
      r8 := by rw [bf 8 (by decide)]; exact h.r8
      r18 := by rw [bf 18 (by decide), bf 74 (by decide)]; exact h.r18
      r19 := by rw [bf 19 (by decide), bf 18 (by decide)]; exact h.r19
      H := by rw [bf 59 (by decide)]; exact h.H
      Hl := by rw [bf 74 (by decide)]; exact h.Hl
      Hw := h.Hw
      h := by rw [bf 67 (by decide)]; exact h.h
      hl := by rw [bf 18 (by decide)]; exact h.hl
      hw := h.hw
      key := hk1
      ksl := by rw [bf 12 (by decide), bf 18 (by decide), List.length_drop]; have := h.ksl; omega
      ksw := fun x hx => h.fin.ksw x (List.mem_of_mem_drop hx)
      acc := b180 }
  obtain ⟨c182, c180, cd, cf⟩ := exec_finHC hN (by omega) w1 hH
  set w2 := exec N K finHC w1
  have w2lo : ∀ j : Fin 200, j.val < 180 → w2 j = w j := fun j hj => by rw [cf j hj, bf j hj]
  have hc2 : Consts N K w2 := consts_of_agree hc fun j hj => w2lo j (by omega)
  obtain ⟨f180, fd, ff⟩ := exec_finFC w2 hc2 (cFs := cFs) (AF0s := AF0s) (AF1s := AF1s)
    (by rw [w2lo 6 (by decide)]; exact h.r6) (by rw [w2lo 8 (by decide)]; exact h.r8)
    (by rw [w2lo 176 (by decide)]; exact h.cF) (by rw [w2lo 177 (by decide)]; exact h.AF)
    h.cFl h.A0l h.A1l h.cFw h.A0w h.A1w c182
    (by rw [List.length_drop, List.length_drop, bf 12 (by decide), bf 18 (by decide)]
        have := h.ksl; omega)
    (fun x hx => h.fin.ksw x (List.mem_of_mem_drop (List.mem_of_mem_drop hx))) c180
  set w3 := exec N K finFC w2
  have w3lo : ∀ j : Fin 200, j.val < 180 → w3 j = w j := fun j hj => by rw [ff j hj, w2lo j hj]
  have hc3 : Consts N K w3 := consts_of_agree hc fun j hj => w3lo j (by omega)
  have e : exec N K finC w = exec N K outC w3 := rfl
  have hval : decRM N K (w3 72) - decRM N K d1 - decRM N K (w3 180) =
      finVal N K w bs B2s Hps hs cFs AF1s ks d1 := by
    rw [fd, cd, bd, w3lo 72 (by decide)]
    rw [bf 20 (by decide), bf 12 (by decide), bf 18 (by decide), bf 74 (by decide),
      bf 3 (by decide)]
    simp only [finVal]
  rw [e, exec_outC hN hK w3 hc3 (by rw [w3lo 15 (by decide)]; exact h.r15)
    (by rw [w3lo 75 (by decide)]; exact h.r75) h.d0l h.d1l (by rw [w3lo 64 (by decide)]; exact h.d)
    (by rw [w3lo 72 (by decide)]; exact h.cm) f180, hval]

end RingVM

end SigabaNeo.Tape
