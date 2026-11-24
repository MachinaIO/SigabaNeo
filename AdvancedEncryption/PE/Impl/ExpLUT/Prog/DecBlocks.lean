import PE.Impl.ExpLUT.Prog.DecRep

/-!
# The `RingVM` blocks on represented vectors and matrices (Dec, package F4)

The constants of the evaluation (`EC`): Fork B's `CK` (registers `0 … 56`, the templates `κ_t`,
`2N − 2^{b'}`) and the buffers `6` (`2K N K` bits), `8` (`2K`), `9` (`2`), `10` (a vector family),
`76` (`4K` bits). The blocks of `VMVec`, `VMGinv`, `VMFam` on words representing vectors and
matrices (`RepV`, `RepM`, `RepFV`), with the scheme's operations as results:

* `vecGinv_rep`: `v G⁻¹(M)`; `matGinv_rep`: `V G⁻¹(M)` row by row; `mulAcc_rep`: the Mul sum;
* `vecAut_repV`/`vecAut_repM`: `σ_{g_t}` entrywise; `vecAdd_repV`, `vecSub_repV`.

Every block writes only registers in `[80, 120)` (`wr_mid`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT Matrix

variable {D : Dims}

variable (D) in
/-- **The constants of the evaluation.** -/
structure EC (w : St) : Prop where
  ck : CK D.N D.K (2 ^ 22) 22 (κD D) (ρD D.N) w
  r6 : w 6 = List.replicate (2 * D.K * (D.N * D.K)) false
  r8 : w 8 = List.replicate (2 * D.K) false
  r9 : w 9 = List.replicate 2 false
  r10 : w 10 = List.replicate (2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))) false
  r76 : w 76 = List.replicate (4 * D.K) false

theorem EC.of_agree {w w' : St} (h : EC D w) (hw : ∀ j : Fin 200, j.val < 80 → w' j = w j) :
    EC D w' where
  ck :=
    { c := consts_of_agree h.ck.c fun j hj => hw j (by omega)
      one := by rw [hw 3 (by decide)]; exact h.ck.one
      km1 := by rw [hw 5 (by decide)]; exact h.ck.km1
      mat := by rw [hw 7 (by decide)]; exact h.ck.mat
      tw := by rw [hw 12 (by decide)]; exact h.ck.tw
      tb := by rw [hw 13 (by decide)]; exact h.ck.tb
      t14 := by rw [hw 14 (by decide)]; exact h.ck.t14
      vk := by rw [hw 56 (by decide)]; exact h.ck.vk
      kap := fun t ht => by rw [hw _ (by simp [kReg]; omega)]; exact h.ck.kap t ht
      rho := fun b' hb => by rw [hw _ (by simp [rReg]; omega)]; exact h.ck.rho b' hb }
  r6 := by rw [hw 6 (by decide)]; exact h.r6
  r8 := by rw [hw 8 (by decide)]; exact h.r8
  r9 := by rw [hw 9 (by decide)]; exact h.r9
  r10 := by rw [hw 10 (by decide)]; exact h.r10
  r76 := by rw [hw 76 (by decide)]; exact h.r76

/-- A register outside `[80, 120)` is not written by a code whose writes are all inside. -/
theorem not_mem_mid {l : List (Fin 200)} (hl : l.all (fun x => decide (80 ≤ x.val ∧ x.val < 120)) = true)
    {j : Fin 200} (hj : j.val < 80 ∨ 120 ≤ j.val) : j ∉ l := fun hm => by
  have := List.all_eq_true.mp hl j hm; simp at this; omega

theorem wid_flatten {us : List (List Bool)} (h : ∀ x ∈ us, x.length = D.N * D.K) :
    us.flatten.length = us.length * (D.N * D.K) := length_flatten_of h

/-! ### `v G⁻¹(M)` -/

theorem vecGinv_rep (w : St) (hw : EC D w) {vs ms : List (List Bool)} {v : Col D.K → Rg D}
    {M : Matrix (Fin 2) (Col D.K) (Rg D)} (hv : RepV D vs v) (hm : RepM D ms M)
    (h90 : w 90 = vs.flatten) (h91 : w 91 = ms.flatten) :
    ∃ os, (exec D.N D.K vecGinvC w) 92 = os.flatten ∧ RepV D os (v ᵥ* (setting D).ginv M) ∧
      ∀ j : Fin 200, j.val < 80 ∨ 120 ≤ j.val → (exec D.N D.K vecGinvC w) j = w j := by
  obtain ⟨os, h92, hl, hwd, hval, hf⟩ := exec_vecGinvC D.K_pos w hw.ck.c hw.r6 hw.r8 hv.wid hv.len
    hm.wid hm.len h90 h91
  refine ⟨os, h92, ⟨hl, hwd, fun c => ?_⟩, fun j hj => hf j (not_mem_mid rfl hj)⟩
  rw [hval _ (cidx_lt c), ddotV_ginv hv hm]; rfl

/-! ### `V G⁻¹(M)` -/

theorem matGinv_rep (w : St) (hw : EC D w) {vs ms : List (List Bool)}
    {V M : Matrix (Fin 2) (Col D.K) (Rg D)} (hv : RepM D vs V) (hm : RepM D ms M)
    (h100 : w 100 = vs.flatten) (h91 : w 91 = ms.flatten) :
    ∃ os, (exec D.N D.K matGinvC w) 102 = os.flatten ∧
      RepM D os (fun a => V a ᵥ* (setting D).ginv M) ∧
      ∀ j : Fin 200, j.val < 80 ∨ 120 ≤ j.val → (exec D.N D.K matGinvC w) j = w j := by
  have h0 := hv.row₀
  have h1 := hv.row₁
  obtain ⟨os₀, os₁, h102, g0, g1, hf⟩ := exec_matGinvC D.K_pos w hw.ck.c hw.r6 hw.ck.mat hw.r8
    h0.wid h0.len h1.wid h1.len hm.wid hm.len
    (by rw [h100, ← List.flatten_append, List.take_append_drop]) h91
  refine ⟨os₀ ++ os₁, by rw [h102, List.flatten_append], RepM.of_rows ⟨g0.1, g0.2.1, fun c => ?_⟩
    ⟨g1.1, g1.2.1, fun c => ?_⟩, fun j hj => hf j (not_mem_mid rfl hj)⟩
  · rw [g0.2.2 _ (cidx_lt c), ddotV_ginv h0 hm]; rfl
  · rw [g1.2.2 _ (cidx_lt c), ddotV_ginv h1 hm]; rfl

/-! ### The Mul sum -/

theorem mulAcc_rep (w : St) (hw : EC D w) {as : List (List Bool)} {fss : List (List (List Bool))}
    {A : Matrix (Fin 2) (Col D.K) (Rg D)} {F : Dig D.K → Col D.K → Rg D} (hA : RepM D as A)
    (hF : RepFV D fss F) (h103 : w 103 = as.flatten) (h104 : w 104 = (fss.map List.flatten).flatten) :
    ∃ os, (exec D.N D.K mulAccC w) 105 = os.flatten ∧
      RepV D os (fun j => ∑ ri : Col D.K, (F (ri.1, j, ri.2) ᵥ* (setting D).ginv A) ri) ∧
      ∀ j : Fin 200, j.val < 80 ∨ 120 ≤ j.val → (exec D.N D.K mulAccC w) j = w j := by
  obtain ⟨os, h105, hl, hwd, hval, hf⟩ := exec_mulAccC D.K_pos w hw.ck.c hw.r6 hw.r8 hw.ck.vk
    hF.ok hF.len hA.wid hA.len h103 h104
  refine ⟨os, h105, ⟨hl, hwd, fun c => ?_⟩, fun j hj => hf j (not_mem_mid rfl hj)⟩
  rw [hval _ (cidx_lt c), mulAccV_eq hF hA]

/-! ### Entrywise operations -/

theorem getD_map_of_lt {us : List (List Bool)} (f : List Bool → List Bool) {i : ℕ} (hi : i < us.length) :
    (us.map f).getD i [] = f (us.getD i []) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

theorem getD_zipWith_of_lt {us vs : List (List Bool)} (f : List Bool → List Bool → List Bool) {i : ℕ}
    (hu : i < us.length) (hv : i < vs.length) :
    (List.zipWith f us vs).getD i [] = f (us.getD i []) (vs.getD i []) := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_zipWith, List.getD_eq_getElem _ _ hu,
    List.getD_eq_getElem _ _ hv]

theorem RepV.map_aut {us : List (List Bool)} {u : Col D.K → Rg D} (h : RepV D us u) (t : ℕ) :
    RepV D (us.map (autMW D.N D.K (κD D t))) (fun c => (setting D).E.σ ((setting D).kf t) (u c)) where
  len := by rw [List.length_map, h.len]
  wid x hx := by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx; exact length_autMW _ _ _ _ D.N_pos
  val c := by
    have hc := cidx_lt c
    rw [getD_map_of_lt _ (by rw [h.len]; exact hc), decRM_autMW (κD_pos D t)
      (h.wid _ (getD_mem (by rw [h.len]; exact hc))), h.val c, σ_kf]

theorem RepM.map_aut {us : List (List Bool)} {M : Matrix (Fin 2) (Col D.K) (Rg D)} (h : RepM D us M)
    (t : ℕ) : RepM D (us.map (autMW D.N D.K (κD D t)))
      (fun a c => (setting D).E.σ ((setting D).kf t) (M a c)) where
  len := by rw [List.length_map, h.len]
  wid x hx := by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx; exact length_autMW _ _ _ _ D.N_pos
  val a c := by
    have hc := cidx_lt c
    have ha := a.isLt
    have hi : 2 * D.K * a.val + cidx D.K c < us.length := by
      rw [h.len]; rcases (show a.val = 0 ∨ a.val = 1 by omega) with e | e <;> rw [e] <;> omega
    rw [getD_map_of_lt _ hi, decRM_autMW (κD_pos D t) (h.wid _ (getD_mem hi)), h.val a c, σ_kf]

theorem RepV.zip_add {us vs : List (List Bool)} {u v : Col D.K → Rg D} (hu : RepV D us u)
    (hv : RepV D vs v) : RepV D (List.zipWith (addRMW D.N D.K) us vs) (u + v) where
  len := by rw [List.length_zipWith, hu.len, hv.len, min_self]
  wid x hx := by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_zipWith]
    exact length_addRMW _ _ (hu.wid _ (List.getElem_mem _)) _
  val c := by
    have hc := cidx_lt c
    rw [getD_zipWith_of_lt _ (by rw [hu.len]; exact hc) (by rw [hv.len]; exact hc),
      decRM_addRMW (hu.wid _ (getD_mem (by rw [hu.len]; exact hc)))
        (hv.wid _ (getD_mem (by rw [hv.len]; exact hc))), hu.val c, hv.val c, Pi.add_apply]

theorem RepV.zip_sub {us vs : List (List Bool)} {u v : Col D.K → Rg D} (hu : RepV D us u)
    (hv : RepV D vs v) : RepV D (List.zipWith (subRMW D.N D.K) us vs) (u - v) where
  len := by rw [List.length_zipWith, hu.len, hv.len, min_self]
  wid x hx := by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_zipWith]
    exact length_subRMW _ _ (hu.wid _ (List.getElem_mem _)) _
  val c := by
    have hc := cidx_lt c
    rw [getD_zipWith_of_lt _ (by rw [hu.len]; exact hc) (by rw [hv.len]; exact hc),
      decRM_subRMW (hu.wid _ (getD_mem (by rw [hu.len]; exact hc)))
        (hv.wid _ (getD_mem (by rw [hv.len]; exact hc))), hu.val c, hv.val c, Pi.sub_apply]

theorem RepM.zip_add {us vs : List (List Bool)} {U V : Matrix (Fin 2) (Col D.K) (Rg D)}
    (hu : RepM D us U) (hv : RepM D vs V) : RepM D (List.zipWith (addRMW D.N D.K) us vs) (U + V) where
  len := by rw [List.length_zipWith, hu.len, hv.len, min_self]
  wid x hx := by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_zipWith]
    exact length_addRMW _ _ (hu.wid _ (List.getElem_mem _)) _
  val a c := by
    have hc := cidx_lt c
    have ha := a.isLt
    have hi : 2 * D.K * a.val + cidx D.K c < 4 * D.K := by
      rcases (show a.val = 0 ∨ a.val = 1 by omega) with e | e <;> rw [e] <;> omega
    rw [getD_zipWith_of_lt _ (by rw [hu.len]; exact hi) (by rw [hv.len]; exact hi),
      decRM_addRMW (hu.wid _ (getD_mem (by rw [hu.len]; exact hi)))
        (hv.wid _ (getD_mem (by rw [hv.len]; exact hi))), hu.val a c, hv.val a c]
    rfl

end AdvancedEncryption.ExpLUT.Prog
