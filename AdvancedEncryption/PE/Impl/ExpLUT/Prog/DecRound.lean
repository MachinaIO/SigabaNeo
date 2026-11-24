import PE.Impl.ExpLUT.Prog.DecCalls

/-!
# Rows, families, and one round `Aut_{g_t}` on the pair (public matrix, encoding) (Dec, F4)

* `deintCall`: a family of matrices split into the families of its rows;
* `joinC`, `row0C`, `row1C`: matrices from rows and back (scratch register `139`);
* **`roundC t`** (registers `120 … 139`): from `A` (`120`), `c` (`121`), `H_{g_t}` (`122`),
  `H_{g_t^{-1}}` (`123`), `h_{g_t}` (`124`), `h_{g_t^{-1}}` (`125`), the family `A^aut_t`
  (`126`), the family `c^aut_t` (`127`), the pair `autStep` of `DecAlg` on `120`, `121`
  (**`exec_roundC`**).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT Matrix

variable {D : Dims}

/-- The frame of a two-output call. -/
def Fr2 (d₁ d₂ : Fin 200) (w w' : St) : Prop :=
  ∀ j : Fin 200, (j.val < 80 ∨ 120 ≤ j.val) → j ≠ d₁ → j ≠ d₂ → w' j = w j

/-! ### Families of matrices -/

/-- `d₀`, `d₁ :=` the families of rows of the family of matrices on `src`. -/
def deintCall (src d₀ d₁ : Fin 200) : Code := ofList [.cp 106 src, deintC, .cp d₀ 107, .cp d₁ 108]

theorem flatten_famV {fss : List (List (List Bool))} (h : FamOK D.N D.K fss) :
    ∀ x ∈ fss.map List.flatten, x.length = 2 * D.K * (D.N * D.K) := fun x hx => by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  rw [length_flatten_of (h v hv).2, (h v hv).1]

theorem exec_deintCall (w : St) (hw : EC D w) (src d₀ d₁ : Fin 200) (hd : d₀ ≠ d₁)
    (h0 : ¬(80 ≤ d₀.val ∧ d₀.val < 120)) {f₀ f₁ : List (List (List Bool))}
    {F₀ F₁ : Dig D.K → Col D.K → Rg D} (hF₀ : RepFV D f₀ F₀) (hF₁ : RepFV D f₁ F₁)
    (hs : w src = (List.zipWith (· ++ ·) (f₀.map List.flatten) (f₁.map List.flatten)).flatten) :
    (exec D.N D.K (deintCall src d₀ d₁) w) d₀ = (f₀.map List.flatten).flatten ∧
      (exec D.N D.K (deintCall src d₀ d₁) w) d₁ = (f₁.map List.flatten).flatten ∧
      Fr2 d₀ d₁ w (exec D.N D.K (deintCall src d₀ d₁) w) := by
  set w1 := Function.update w 106 (w src) with hw1
  have hc1 : Consts D.N D.K w1 := consts_update hw.ck.c 106 (by decide) _
  have ag : ∀ j : Fin 200, j.val < 80 → w1 j = w j := fun j hj => by
    rw [hw1, Function.update_of_ne (by intro e; subst e; simp at hj)]
  obtain ⟨a107, a108, af⟩ := exec_deintC w1 hc1 (by rw [ag 6 (by decide)]; exact hw.r6)
    (by rw [ag 8 (by decide)]; exact hw.r8) (by rw [ag 9 (by decide)]; exact hw.r9)
    (by rw [ag 10 (by decide)]; exact hw.r10) (flatten_famV hF₀.ok) (flatten_famV hF₁.ok)
    (by simp [hF₀.len]) (by simp [hF₁.len]) (by rw [hw1, Function.update_self, hs])
  have e : exec D.N D.K (deintCall src d₀ d₁) w = Function.update (Function.update
      (exec D.N D.K deintC w1) d₀ ((exec D.N D.K deintC w1) 107)) d₁
      (Function.update (exec D.N D.K deintC w1) d₀ ((exec D.N D.K deintC w1) 107) 108) := rfl
  have h108 : (108 : Fin 200) ≠ d₀ := fun e => h0 (by rw [← e]; decide)
  refine ⟨?_, ?_, fun j hj n0 n1 => ?_⟩
  · rw [e, Function.update_of_ne hd, Function.update_self, a107]
  · rw [e, Function.update_self, Function.update_of_ne h108, a108]
  · rw [e, Function.update_of_ne n1, Function.update_of_ne n0, af j (not_mem_mid rfl hj), hw1,
      Function.update_of_ne (mid_ne hj (by decide))]

/-! ### Rows and matrices -/

/-- `dst := a ++ b` (two rows of `2K` words into a matrix). -/
def joinC (a b dst : Fin 200) : Code :=
  ofList [.cp dst 7, .cp 139 a, .mv dst 139 6, .cp 139 b, .mv dst 139 6]

/-- `dst :=` row `0` of the matrix on `src`. -/
def row0C (src dst : Fin 200) : Code := ofList [.cp dst 6, .cp 139 src, .mv dst 139 6]

/-- `dst :=` row `1` of the matrix on `src`. -/
def row1C (src dst : Fin 200) : Code := ofList [.cp dst src, .drop dst 6]

theorem lenV {vs : List (List Bool)} {v : Col D.K → Rg D} (h : RepV D vs v) :
    vs.flatten.length = 2 * D.K * (D.N * D.K) := by rw [length_flatten_of h.wid, h.len]

theorem exec_joinC (w : St) (hw : EC D w) (a b dst : Fin 200) (hd1 : dst ≠ 139) (hd2 : dst.val ≥ 120)
    (hb : b ≠ dst) (ha : a ≠ dst) (hb' : b ≠ 139)
    {r₀ r₁ : List (List Bool)} {M : Matrix (Fin 2) (Col D.K) (Rg D)}
    (h₀ : RepV D r₀ (M 0)) (h₁ : RepV D r₁ (M 1)) (ha' : w a = r₀.flatten) (hb'' : w b = r₁.flatten) :
    (exec D.N D.K (joinC a b dst) w) dst = (r₀ ++ r₁).flatten ∧ RepM D (r₀ ++ r₁) M ∧
      Fr2 dst 139 w (exec D.N D.K (joinC a b dst) w) := by
  have l6 : (w 6).length = 2 * D.K * (D.N * D.K) := by rw [hw.r6, List.length_replicate]
  have hdlo : ∀ k : Fin 200, k.val < 80 → k ≠ dst := fun k hk e => by subst e; omega
  have e : exec D.N D.K (joinC a b dst) w = Function.update (Function.update (Function.update
      (Function.update (Function.update w dst (w 7)) 139 []) dst
      ((w 7 ++ r₀.flatten).drop (w 6).length)) 139 [])
      dst (((w 7 ++ r₀.flatten).drop (w 6).length ++ r₁.flatten).drop (w 6).length) := by
    have n6 : dst ≠ 6 := (hdlo 6 (by decide)).symm
    have n7 : dst ≠ 7 := (hdlo 7 (by decide)).symm
    set s1 := Function.update (Function.update w dst (w 7)) 139 r₀.flatten with hs1
    have e1 : exec D.N D.K (.mv dst 139 6) s1 = Function.update (Function.update s1 139 []) dst
        ((w 7 ++ r₀.flatten).drop (w 6).length) := by
      rw [exec_mv_shift (v := r₀.flatten) (L := []) (by simp only [not_or]; exact ⟨hd1, n6, by decide⟩)
        (by rw [hs1, Function.update_of_ne (by decide), Function.update_of_ne (Ne.symm n6), lenV h₀, l6])
        (by simp [hs1])]
      simp [hs1, Function.update_of_ne (by decide : (6 : Fin 200) ≠ 139), Function.update_of_ne (Ne.symm n6),
        Function.update_of_ne hd1]
    set s2 := Function.update (Function.update s1 139 []) dst ((w 7 ++ r₀.flatten).drop (w 6).length)
      with hs2
    have e2 : exec D.N D.K (.cp 139 b) s2 = Function.update s2 139 r₁.flatten := by
      simp [exec, hs2, hs1, Function.update_of_ne hb, Function.update_of_ne hb', hb'']
    have e3 : exec D.N D.K (.mv dst 139 6) (Function.update s2 139 r₁.flatten) =
        Function.update (Function.update (Function.update s2 139 r₁.flatten) 139 []) dst
          (((w 7 ++ r₀.flatten).drop (w 6).length ++ r₁.flatten).drop (w 6).length) := by
      rw [exec_mv_shift (v := r₁.flatten) (L := []) (by simp only [not_or]; exact ⟨hd1, n6, by decide⟩)
        (by simp only [hs2, hs1, Function.update_apply, show ¬((6 : Fin 200) = 139) by decide,
          ↓reduceIte, Ne.symm n6]; rw [lenV h₁, l6]) (by simp)]
      simp [hs2, Function.update_of_ne (by decide : (6 : Fin 200) ≠ 139), Function.update_of_ne (Ne.symm n6),
        Function.update_of_ne hd1, hs1]
    have e0 : exec D.N D.K (.cp 139 a) (Function.update w dst (w 7)) = s1 := by
      simp [exec, hs1, Function.update_of_ne ha, ha']
    show exec D.N D.K (.mv dst 139 6) (exec D.N D.K (.cp 139 b) (exec D.N D.K (.mv dst 139 6)
      (exec D.N D.K (.cp 139 a) (Function.update w dst (w 7))))) = _
    rw [e0, e1, e2, e3, hs2, hs1]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> rfl
  have l7 : (w 7).length = 2 * (w 6).length := by
    rw [hw.ck.mat, List.length_replicate, l6]; ring
  have hj : ((w 7 ++ r₀.flatten).drop (w 6).length ++ r₁.flatten).drop (w 6).length =
      (r₀ ++ r₁).flatten := by
    rw [List.flatten_append, List.drop_append_of_le_length (by simp; omega), List.drop_drop,
      List.drop_left' (by omega)]
  refine ⟨by rw [e, Function.update_self, hj], RepM.of_rows h₀ h₁, fun j hj' n0 n1 => ?_⟩
  rw [e]
  simp only [Function.update_apply, n0, n1, ↓reduceIte]

theorem flatten_take_drop {ms : List (List Bool)} {M : Matrix (Fin 2) (Col D.K) (Rg D)}
    (h : RepM D ms M) : ms.flatten = (ms.take (2 * D.K)).flatten ++ (ms.drop (2 * D.K)).flatten := by
  rw [← List.flatten_append, List.take_append_drop]

theorem exec_row0C (w : St) (hw : EC D w) (src dst : Fin 200) (hd1 : dst ≠ 139) (hd2 : 120 ≤ dst.val)
    (hs : src ≠ dst) {ms : List (List Bool)} {M : Matrix (Fin 2) (Col D.K) (Rg D)} (h : RepM D ms M)
    (hsrc : w src = ms.flatten) :
    (exec D.N D.K (row0C src dst) w) dst = (ms.take (2 * D.K)).flatten ∧
      Fr2 dst 139 w (exec D.N D.K (row0C src dst) w) := by
  have l6 : (w 6).length = 2 * D.K * (D.N * D.K) := by rw [hw.r6, List.length_replicate]
  have n6 : dst ≠ 6 := fun e => by subst e; simp at hd2
  have e0 : exec D.N D.K (.cp 139 src) (exec D.N D.K (.cp dst 6) w) =
      Function.update (Function.update w dst (w 6)) 139 ms.flatten := by
    simp [exec, Function.update_of_ne hs, hsrc]
  have e : exec D.N D.K (row0C src dst) w = Function.update (Function.update
      (Function.update w dst (w 6)) 139 (ms.drop (2 * D.K)).flatten) dst
      (ms.take (2 * D.K)).flatten := by
    show exec D.N D.K (.mv dst 139 6) (exec D.N D.K (.cp 139 src) (exec D.N D.K (.cp dst 6) w)) = _
    rw [e0, exec_mv_shift (v := (ms.take (2 * D.K)).flatten) (L := (ms.drop (2 * D.K)).flatten)
      (by simp only [not_or]; exact ⟨hd1, n6, by decide⟩)
      (by rw [Function.update_of_ne (by decide), Function.update_of_ne (Ne.symm n6),
        lenV h.row₀, l6]) (by rw [Function.update_self, flatten_take_drop h])]
    simp only [Function.update_idem, Function.update_of_ne hd1, Function.update_self,
      Function.update_of_ne (by decide : (6 : Fin 200) ≠ 139), Function.update_of_ne (Ne.symm n6),
      List.drop_left' rfl]
  refine ⟨by rw [e, Function.update_self], fun j hj n0 n1 => ?_⟩
  rw [e]; simp only [Function.update_apply, n0, n1, ↓reduceIte]

theorem exec_row1C (w : St) (hw : EC D w) (src dst : Fin 200) (hd2 : 120 ≤ dst.val)
    {ms : List (List Bool)} {M : Matrix (Fin 2) (Col D.K) (Rg D)} (h : RepM D ms M)
    (hsrc : w src = ms.flatten) :
    (exec D.N D.K (row1C src dst) w) dst = (ms.drop (2 * D.K)).flatten ∧
      Fr dst w (exec D.N D.K (row1C src dst) w) := by
  have n6 : dst ≠ 6 := fun e => by subst e; simp at hd2
  have e : exec D.N D.K (row1C src dst) w = Function.update w dst
      ((w src).drop (w 6).length) := by
    simp [row1C, exec_ofList_cons, exec_ofList_nil, exec, n6, Function.update_of_ne (Ne.symm n6)]
  refine ⟨?_, fun j _ n0 => by rw [e, Function.update_of_ne n0]⟩
  rw [e, Function.update_self, hsrc, flatten_take_drop h, hw.r6, List.length_replicate,
    List.drop_left' (lenV h.row₀)]

end AdvancedEncryption.ExpLUT.Prog
