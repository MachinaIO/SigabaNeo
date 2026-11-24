import PE.Impl.ExpLUT.Prog.DecBlocks
import PE.Impl.ExpLUT.Prog.DecFinal

/-!
# Calls of the `RingVM` blocks between the registers of the evaluation (Dec, package F4)

Each call copies its operands into the block's input registers (in `[80, 120)`), runs the block
and copies the result to a destination register `dst` outside `[80, 120)`; every other register
outside `[80, 120)` is unchanged (`Fr`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT Matrix

variable {D : Dims}

/-- The frame of a call: registers outside `[80, 120)` other than `dst` are unchanged. -/
def Fr (dst : Fin 200) (w w' : St) : Prop :=
  ∀ j : Fin 200, (j.val < 80 ∨ 120 ≤ j.val) → j ≠ dst → w' j = w j

theorem mid_ne {j a : Fin 200} (hj : j.val < 80 ∨ 120 ≤ j.val) (ha : 80 ≤ a.val ∧ a.val < 120) :
    j ≠ a := by
  intro e; subst e; omega

theorem Fr.app {dst : Fin 200} {w w' : St} (h : Fr dst w w') {j : Fin 200} (hj : j.val < 80 ∨ 120 ≤ j.val)
    (hd : j ≠ dst) : w' j = w j := h j hj hd

theorem EC.of_fr {dst : Fin 200} {w w' : St} (hw : EC D w) (h : Fr dst w w') (hd : 80 ≤ dst.val) :
    EC D w' := hw.of_agree fun j hj => h j (Or.inl hj) (by intro e; subst e; omega)

/-! ### `σ_{g_t}` entrywise -/

/-- `dst := σ_{g_t}(src)` entrywise (`cnt` words, buffer `buf`). -/
def autCall (t : ℕ) (src dst cnt buf : Fin 200) : Code :=
  ofList [.cp 110 src, vecAutC cnt buf (kReg t), .cp dst 112]

theorem exec_autCall (w : St) (hw : EC D w) (t : ℕ) (ht : t < 22) (src dst cnt buf : Fin 200)
    (hcnt : cnt.val < 80) (hbuf : buf.val < 80) {us : List (List Bool)}
    (hus : ∀ x ∈ us, x.length = D.N * D.K) (hsrc : w src = us.flatten)
    (hc : (w cnt).length = us.length) (hb : (w buf).length = us.length * (D.N * D.K)) :
    (exec D.N D.K (autCall t src dst cnt buf) w) dst = (us.map (autMW D.N D.K (κD D t))).flatten ∧
      Fr dst w (exec D.N D.K (autCall t src dst cnt buf) w) := by
  set w1 := Function.update w 110 (w src) with hw1
  have hc1 : Consts D.N D.K w1 := consts_update hw.ck.c 110 (by decide) _
  have hk : w1 (kReg t) = List.replicate (κD D t) false := by
    rw [hw1, Function.update_of_ne (by simp [kReg, Fin.ext_iff]; omega)]; exact hw.ck.kap t ht
  obtain ⟨a112, af⟩ := exec_vecAutC (N := D.N) (K := D.K) D.N_pos w1 hc1 cnt buf (kReg t)
    (by intro e; subst e; simp at hbuf) (by simp [kReg, Fin.ext_iff]; omega)
    (by simp [kReg, Fin.ext_iff]; omega) hus (by simp [hw1, hsrc])
    (by rw [hw1, Function.update_of_ne (by intro e; subst e; simp at hcnt)]; exact hc)
    (by rw [hw1, Function.update_of_ne (by intro e; subst e; simp at hbuf)]; exact hb)
  rw [hk, List.length_replicate] at a112
  have e : exec D.N D.K (autCall t src dst cnt buf) w =
      Function.update (exec D.N D.K (vecAutC cnt buf (kReg t)) w1) dst
        ((exec D.N D.K (vecAutC cnt buf (kReg t)) w1) 112) := rfl
  refine ⟨by rw [e, Function.update_self, a112], fun j hj hd => ?_⟩
  rw [e, Function.update_of_ne hd, af j (not_mem_mid rfl hj), hw1,
    Function.update_of_ne (mid_ne hj (by decide))]

/-! ### `v G⁻¹(M)`, `V G⁻¹(M)`, the Mul sum, entrywise sums -/

/-- `dst := v G⁻¹(M)` (`v` on `src`, `M` on `msrc`). -/
def ginvCall (src msrc dst : Fin 200) : Code := ofList [.cp 90 src, .cp 91 msrc, vecGinvC, .cp dst 92]

theorem exec_ginvCall (w : St) (hw : EC D w) (src msrc dst : Fin 200) (hs : msrc ≠ 90)
    {vs ms : List (List Bool)} {v : Col D.K → Rg D} {M : Matrix (Fin 2) (Col D.K) (Rg D)}
    (hv : RepV D vs v) (hm : RepM D ms M) (h1 : w src = vs.flatten) (h2 : w msrc = ms.flatten) :
    ∃ os, (exec D.N D.K (ginvCall src msrc dst) w) dst = os.flatten ∧
      RepV D os (v ᵥ* (setting D).ginv M) ∧ Fr dst w (exec D.N D.K (ginvCall src msrc dst) w) := by
  set w1 := Function.update (Function.update w 90 (w src)) 91 (w msrc) with hw1
  have hw1' : EC D w1 := hw.of_agree fun j hj => by
    rw [hw1, Function.update_of_ne (by intro e; subst e; simp at hj),
      Function.update_of_ne (by intro e; subst e; simp at hj)]
  obtain ⟨os, h92, hr, hf⟩ := vecGinv_rep w1 hw1' hv hm
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_self, h1])
    (by rw [hw1, Function.update_self, h2])
  have e : exec D.N D.K (ginvCall src msrc dst) w =
      Function.update (exec D.N D.K vecGinvC w1) dst ((exec D.N D.K vecGinvC w1) 92) := by
    simp only [ginvCall, exec_ofList_cons, exec_ofList_nil, exec, hw1]
    rw [Function.update_of_ne hs]
  refine ⟨os, by rw [e, Function.update_self, h92], hr, fun j hj hd => ?_⟩
  rw [e, Function.update_of_ne hd, hf j hj, hw1, Function.update_of_ne (mid_ne hj (by decide)),
    Function.update_of_ne (mid_ne hj (by decide))]

/-- `dst := V G⁻¹(M)` row by row. -/
def matCall (src msrc dst : Fin 200) : Code := ofList [.cp 100 src, .cp 91 msrc, matGinvC, .cp dst 102]

theorem exec_matCall (w : St) (hw : EC D w) (src msrc dst : Fin 200) (hs : msrc ≠ 100)
    {vs ms : List (List Bool)} {V M : Matrix (Fin 2) (Col D.K) (Rg D)}
    (hv : RepM D vs V) (hm : RepM D ms M) (h1 : w src = vs.flatten) (h2 : w msrc = ms.flatten) :
    ∃ os, (exec D.N D.K (matCall src msrc dst) w) dst = os.flatten ∧
      RepM D os (fun a => V a ᵥ* (setting D).ginv M) ∧
      Fr dst w (exec D.N D.K (matCall src msrc dst) w) := by
  set w1 := Function.update (Function.update w 100 (w src)) 91 (w msrc) with hw1
  have hw1' : EC D w1 := hw.of_agree fun j hj => by
    rw [hw1, Function.update_of_ne (by intro e; subst e; simp at hj),
      Function.update_of_ne (by intro e; subst e; simp at hj)]
  obtain ⟨os, h102, hr, hf⟩ := matGinv_rep w1 hw1' hv hm
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_self, h1])
    (by rw [hw1, Function.update_self, h2])
  have e : exec D.N D.K (matCall src msrc dst) w =
      Function.update (exec D.N D.K matGinvC w1) dst ((exec D.N D.K matGinvC w1) 102) := by
    simp only [matCall, exec_ofList_cons, exec_ofList_nil, exec, hw1]
    rw [Function.update_of_ne hs]
  refine ⟨os, by rw [e, Function.update_self, h102], hr, fun j hj hd => ?_⟩
  rw [e, Function.update_of_ne hd, hf j hj, hw1, Function.update_of_ne (mid_ne hj (by decide)),
    Function.update_of_ne (mid_ne hj (by decide))]

/-- `dst :=` the Mul sum of the matrix on `asrc` and the family on `fsrc`. -/
def accCall (asrc fsrc dst : Fin 200) : Code := ofList [.cp 103 asrc, .cp 104 fsrc, mulAccC, .cp dst 105]

theorem exec_accCall (w : St) (hw : EC D w) (asrc fsrc dst : Fin 200) (hs : fsrc ≠ 103)
    {as : List (List Bool)} {fss : List (List (List Bool))} {A : Matrix (Fin 2) (Col D.K) (Rg D)}
    {F : Dig D.K → Col D.K → Rg D} (hA : RepM D as A) (hF : RepFV D fss F)
    (h1 : w asrc = as.flatten) (h2 : w fsrc = (fss.map List.flatten).flatten) :
    ∃ os, (exec D.N D.K (accCall asrc fsrc dst) w) dst = os.flatten ∧
      RepV D os (fun j => ∑ ri : Col D.K, (F (ri.1, j, ri.2) ᵥ* (setting D).ginv A) ri) ∧
      Fr dst w (exec D.N D.K (accCall asrc fsrc dst) w) := by
  set w1 := Function.update (Function.update w 103 (w asrc)) 104 (w fsrc) with hw1
  have hw1' : EC D w1 := hw.of_agree fun j hj => by
    rw [hw1, Function.update_of_ne (by intro e; subst e; simp at hj),
      Function.update_of_ne (by intro e; subst e; simp at hj)]
  obtain ⟨os, h105, hr, hf⟩ := mulAcc_rep w1 hw1' hA hF
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_self, h1])
    (by rw [hw1, Function.update_self, h2])
  have e : exec D.N D.K (accCall asrc fsrc dst) w =
      Function.update (exec D.N D.K mulAccC w1) dst ((exec D.N D.K mulAccC w1) 105) := by
    simp only [accCall, exec_ofList_cons, exec_ofList_nil, exec, hw1]
    rw [Function.update_of_ne hs]
  refine ⟨os, by rw [e, Function.update_self, h105], hr, fun j hj hd => ?_⟩
  rw [e, Function.update_of_ne hd, hf j hj, hw1, Function.update_of_ne (mid_ne hj (by decide)),
    Function.update_of_ne (mid_ne hj (by decide))]

/-- `dst := a + b` entrywise (`2K` words). -/
def addCall (a b dst : Fin 200) : Code := ofList [.cp 110 a, .cp 111 b, vecAddC 8 6, .cp dst 112]

/-- `dst := a − b` entrywise (`2K` words). -/
def subCall (a b dst : Fin 200) : Code := ofList [.cp 110 a, .cp 111 b, vecSubC 8 6, .cp dst 112]

theorem exec_addCall (w : St) (hw : EC D w) (a b dst : Fin 200) (ha : b ≠ 110)
    {us vs : List (List Bool)} {u v : Col D.K → Rg D} (hu : RepV D us u) (hv : RepV D vs v)
    (h1 : w a = us.flatten) (h2 : w b = vs.flatten) :
    (exec D.N D.K (addCall a b dst) w) dst = (List.zipWith (addRMW D.N D.K) us vs).flatten ∧
      RepV D (List.zipWith (addRMW D.N D.K) us vs) (u + v) ∧
      Fr dst w (exec D.N D.K (addCall a b dst) w) := by
  set w1 := Function.update (Function.update w 110 (w a)) 111 (w b) with hw1
  have hc1 : Consts D.N D.K w1 := consts_update (consts_update hw.ck.c 110 (by decide) _) 111
    (by decide) _
  obtain ⟨a112, af⟩ := exec_vecAddC w1 hc1 8 6 (by decide) hu.wid hv.wid (by rw [hu.len, hv.len])
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_self, h1])
    (by rw [hw1, Function.update_self, h2])
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hw.r8,
      List.length_replicate, hu.len])
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hw.r6,
      List.length_replicate, hu.len])
  have e : exec D.N D.K (addCall a b dst) w =
      Function.update (exec D.N D.K (vecAddC 8 6) w1) dst ((exec D.N D.K (vecAddC 8 6) w1) 112) := by
    simp only [addCall, exec_ofList_cons, exec_ofList_nil, exec, hw1]
    rw [Function.update_of_ne ha]
  refine ⟨by rw [e, Function.update_self, a112], hu.zip_add hv, fun j hj hd => ?_⟩
  rw [e, Function.update_of_ne hd, af j (not_mem_mid rfl hj), hw1,
    Function.update_of_ne (mid_ne hj (by decide)), Function.update_of_ne (mid_ne hj (by decide))]

theorem exec_subCall (w : St) (hw : EC D w) (a b dst : Fin 200) (ha : b ≠ 110)
    {us vs : List (List Bool)} {u v : Col D.K → Rg D} (hu : RepV D us u) (hv : RepV D vs v)
    (h1 : w a = us.flatten) (h2 : w b = vs.flatten) :
    (exec D.N D.K (subCall a b dst) w) dst = (List.zipWith (subRMW D.N D.K) us vs).flatten ∧
      RepV D (List.zipWith (subRMW D.N D.K) us vs) (u - v) ∧
      Fr dst w (exec D.N D.K (subCall a b dst) w) := by
  set w1 := Function.update (Function.update w 110 (w a)) 111 (w b) with hw1
  have hc1 : Consts D.N D.K w1 := consts_update (consts_update hw.ck.c 110 (by decide) _) 111
    (by decide) _
  obtain ⟨a112, af⟩ := exec_vecSubC w1 hc1 8 6 (by decide) hu.wid hv.wid (by rw [hu.len, hv.len])
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_self, h1])
    (by rw [hw1, Function.update_self, h2])
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hw.r8,
      List.length_replicate, hu.len])
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hw.r6,
      List.length_replicate, hu.len])
  have e : exec D.N D.K (subCall a b dst) w =
      Function.update (exec D.N D.K (vecSubC 8 6) w1) dst ((exec D.N D.K (vecSubC 8 6) w1) 112) := by
    simp only [subCall, exec_ofList_cons, exec_ofList_nil, exec, hw1]
    rw [Function.update_of_ne ha]
  refine ⟨by rw [e, Function.update_self, a112], hu.zip_sub hv, fun j hj hd => ?_⟩
  rw [e, Function.update_of_ne hd, af j (not_mem_mid rfl hj), hw1,
    Function.update_of_ne (mid_ne hj (by decide)), Function.update_of_ne (mid_ne hj (by decide))]

end AdvancedEncryption.ExpLUT.Prog
