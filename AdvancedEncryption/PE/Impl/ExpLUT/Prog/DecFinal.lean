import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VMDot

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

end RingVM

end SigabaNeo.Tape
