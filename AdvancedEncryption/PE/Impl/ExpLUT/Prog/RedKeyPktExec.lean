import PE.Impl.ExpLUT.Prog.RedKeyPktAsm
/-!
# The packet stream, part 15: the run of `pktC D` (at `D`)

* **`exec_pkPre`**: `pkMoveC`, the walk's constants and `pkWalkC` leave the payload queues
  `swQZ`, `swQU` of the walk (`exec_swLoopC`) and keep the inputs;
* **`exec_pkPub`**: the public phase's constants and `pbPubC` write the skeleton's public queues;
* **`exec_pkFin`**: the loops' constants and `pkFinC` write the stream (`ptStream_eq`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid

variable (D : Dims)

theorem tos_cons (r : Fin 64) (a : TemplateWord) (ops : List (Fin 64 × TemplateWord)) (w : St) :
    templateOpsState ((r, a) :: ops) w = templateOpsState ops (Function.update w r a.value) := rfl

theorem tos_nil (w : St) : templateOpsState [] w = w := rfl

/-- Evaluate a register of a template state (no evaluation of the unary words). -/
macro "pk_tos" : tactic => `(tactic| (
  simp only [templateOpsState, pkSwOps, pkPbOps, pkLpOps, List.foldl_cons, List.foldl_nil,
    TemplateWord.value, Function.update_apply, vmreg];
  try simp only [Fin.reduceEq, ite_true, ite_false, List.length_replicate]))

theorem encRM_one' (hN : 0 < D.N) : encRM D.N D.K (1 : Rq D.N D.K) =
    [true] ++ List.replicate (D.N * D.K - 1) false := by
  rw [encRM_one hN D.hK]
  have h1 : 1 ≤ D.K := by have := D.hK; omega
  have e : D.K - 1 + (D.N - 1) * D.K = D.N * D.K - 1 := by
    obtain ⟨n, hn⟩ : ∃ n, D.N = n + 1 := ⟨D.N - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel, Nat.succ_mul]; omega
  rw [List.cons_append, ← List.replicate_add, e]; rfl

theorem pkMove_eq (w : St) : exec D.N D.K pkMoveC w =
    Function.update (Function.update (Function.update (Function.update (Function.update w pkRaw (w 0))
      0 []) 6 []) 5 [true]) rB1 [false] := by
  simp only [pkMoveC, exec_seq, exec_cp, exec_clr]
  rw [exec_bitsC _ _ _ (by decide) (by decide) (by decide) _ (by simp)]

/-- **The walk set-up and the walk.** -/
theorem exec_pkPre (hN : 0 < D.N) (w : St) (R C : List Bool) (h0 : w 0 = R) (h4 : w 4 = C)
    (blk : ℕ → List Bool) (hblk : ∀ i, (blk i).length = 8) (L : List Bool)
    (hR : R = (List.range 16).flatMap blk ++ L) :
    let v := exec D.N D.K pkWalkC (exec D.N D.K (templateOpsC (pkSwOps D)) (exec D.N D.K pkMoveC w))
    v swQZ = (List.range 16).flatMap (fun i => swMonoW D.N D.K
        (swSt C tlK (fun i => hornerB (blk i) 0) i) (encRM D.N D.K 1)) ∧
      v swQU = (List.range 16).flatMap (fun i => swMonoW D.N D.K
        (swSt C tlK (fun i => hornerB (blk i) 0) i + 2 ^ 14 * hornerB (blk i) 0) (encRM D.N D.K 1)) ∧
      v 0 = [] ∧ v pkRaw = R ∧ v 1 = w 1 ∧ v 2 = w 2 ∧ v 5 = [true] ∧ v rB1 = [false] := by
  intro v
  set w1 := exec D.N D.K pkMoveC w with hw1
  have e1 : w1 = _ := pkMove_eq D w
  have t5 : w1 5 = [true] := by rw [e1]; simp [Function.update_apply]
  have tB : w1 rB1 = [false] := by rw [e1]; simp [Function.update_apply]
  have e2 := exec_templateOpsC (N := D.N) (K := D.K) (pkSwOps D) w1
    (fun op hop => ⟨(pkSw_targets D op hop).2.1, (pkSw_targets D op hop).2.2.1⟩) t5 tB
  set w2 := exec D.N D.K (templateOpsC (pkSwOps D)) w1 with hw2
  have v2 : ∀ r, w2 r = templateOpsState (pkSwOps D) w1 r := fun r => by rw [e2]
  set w3 := exec D.N D.K (.cp swCcur 4) (exec D.N D.K (.cp swA pkRaw)
    (exec D.N D.K (.app swOne pkT1) w2)) with hw3
  have v3 : ∀ r, r ≠ swCcur → r ≠ swA → r ≠ swOne → w3 r = w2 r := by
    intro r a b c; simp [hw3, Function.update_apply, a, b, c]
  have hc : SwConst D.N D.K tlK (encRM D.N D.K 1) w3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [v3 _ (by decide) (by decide) (by decide), v2]
      pk_tos
    · rw [v3 _ (by decide) (by decide) (by decide), v2]
      pk_tos
    · rw [v3 _ (by decide) (by decide) (by decide), v2]
      pk_tos
    · simp only [hw3, exec_cp, exec_app, Function.update_apply]
      simp only [show (swOne : Fin 64) ≠ swCcur by decide, show (swOne : Fin 64) ≠ swA by decide,
        if_false, if_true, v2]
      rw [encRM_one' D hN]
      pk_tos
    · rw [v3 _ (by decide) (by decide) (by decide), v2]
      pk_tos
    · rw [v3 _ (by decide) (by decide) (by decide), v2]
      pk_tos
    · rw [v3 _ (by decide) (by decide) (by decide), v2]
      pk_tos
  have w1r : ∀ r, r ≠ pkRaw → r ≠ 0 → r ≠ 6 → r ≠ 5 → r ≠ rB1 → w1 r = w r := by
    intro r a b c d e; rw [e1]; simp [Function.update_apply, a, b, c, d, e]
  have hA : w3 swA = (List.range 16).flatMap blk ++ L := by
    have e : w3 swA = w2 pkRaw := by simp [hw3, Function.update_apply]
    rw [e, v2]
    pk_tos
    rw [e1]; simp only [Function.update_apply, vmreg]
    simp only [Fin.reduceEq, ite_true, ite_false, h0, hR]
  have hC : w3 swCcur = C := by
    have e : w3 swCcur = w2 4 := by simp [hw3, Function.update_apply]
    rw [e, v2]
    pk_tos
    rw [w1r 4 (by decide) (by decide) (by decide) (by decide) (by decide), h4]
  have h16 : (w3 swT16).length = 16 := by
    rw [v3 _ (by decide) (by decide) (by decide), v2]
    pk_tos
  obtain ⟨q1, q2, q3⟩ := exec_swLoopC (N := D.N) (K := D.K) w3 hc blk hblk L C hA hC h16
  have hv : v = exec D.N D.K swLoopC w3 := rfl
  have fr : ∀ r, (r = 0 ∨ r = pkRaw ∨ r = 1 ∨ r = 2 ∨ r = 5 ∨ r = rB1) → v r = w2 r := by
    intro r hr
    rw [hv, q3 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      v3 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  refine ⟨q1, q2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [fr 0 (by simp), v2]; pk_tos; rw [e1]; simp only [Function.update_apply, vmreg];
       simp only [Fin.reduceEq, ite_true, ite_false, h0])
    | (rw [fr pkRaw (by simp), v2]; pk_tos; rw [e1]; simp only [Function.update_apply, vmreg];
       simp only [Fin.reduceEq, ite_true, ite_false, h0])
    | (rw [fr 1 (by simp), v2]; pk_tos; rw [e1]; simp only [Function.update_apply, vmreg];
       simp only [Fin.reduceEq, ite_true, ite_false])
    | (rw [fr 2 (by simp), v2]; pk_tos; rw [e1]; simp only [Function.update_apply, vmreg];
       simp only [Fin.reduceEq, ite_true, ite_false])
    | (rw [fr 5 (by simp), v2]; pk_tos; rw [e1]; simp only [Function.update_apply, vmreg];
       simp only [Fin.reduceEq, ite_true, ite_false])
    | (rw [fr rB1 (by simp), v2]; pk_tos; rw [e1]; simp only [Function.update_apply, vmreg];
       simp only [Fin.reduceEq, ite_true, ite_false])

theorem pk_gD_pos : 0 < gD D := by simp [gD, gGen]

theorem pkPub_keeps : ∀ r : Fin 64, (r = 0 ∨ r = pkRaw ∨ r = 5) → pbPubC.writes r = false := by
  decide

/-- **The public phase**: the queues `ptPB`, `ptPS` (with the walk's payloads `z`, `u`) and `A₀`. -/
theorem exec_pkPub (mpk : MPKt D) (ct : CTt D) (u : St) (h1 : u 1 = (ctEnc D).enc ct)
    (h2 : u 2 = (mpkEnc D).enc mpk) (z uu : ℕ → List Bool)
    (hz : u swQZ = (List.range 16).flatMap z) (hu : u swQU = (List.range 16).flatMap uu)
    (lz : ∀ i, (z i).length = D.N * D.K) (lu : ∀ i, (uu i).length = D.N * D.K)
    (h5 : u 5 = [true]) (h38 : u rB1 = [false]) :
    let v := exec D.N D.K pbPubC (exec D.N D.K (templateOpsC (pkPbOps D)) u)
    v ptPB = (List.range D.b).flatMap (fun t => ptGW D mpk ct t ++ (ptAaW D mpk t ++ ptHfW D mpk t)) ∧
      v ptPS = (List.range 16).flatMap (fun i =>
        (pbAinW D mpk i ++ (pbAW D mpk i ++ (pbCbW D ct i ++ z i))) ++ uu i) ∧
      v ptA0 = ptA0W D mpk ∧ (v ptTB).length = D.b ∧ (v ptT16).length = 16 ∧
      (v ptTM).length = 4 * D.K * (D.N * D.K) ∧ (v ptTAa).length = 16 * D.K ^ 3 * (D.N * D.K) ∧
      (v pbTN).length = D.N * D.K ∧ v 0 = u 0 ∧ v pkRaw = u pkRaw ∧ v 5 = u 5 ∧ v rB1 = u rB1 := by
  intro v
  have hK : 0 < D.K := by have := D.hK; omega
  have hN : 0 < D.N := Nat.pos_of_ne_zero (by simp [Dims.N])
  have e1 := exec_templateOpsC (N := D.N) (K := D.K) (pkPbOps D) u
    (fun op hop => ⟨(pkPb_targets D op hop).2.1, (pkPb_targets D op hop).2.2.1⟩) h5 h38
  set u1 := exec D.N D.K (templateOpsC (pkPbOps D)) u with hu1
  have v1 : ∀ r, u1 r = templateOpsState (pkPbOps D) u r := fun r => by rw [e1]
  have u12 : u1 2 = (mpkEnc D).enc mpk := by rw [v1]; pk_tos; exact h2
  have u11 : u1 1 = (ctEnc D).enc ct := by rw [v1]; pk_tos; exact h1
  have lOH : (u1 pbOH).length = pbOffHv D := by rw [v1]; pk_tos
  have lOh : (u1 pbOh).length = pbOffhv D := by rw [v1]; pk_tos
  have lOAa : (u1 pbOAa).length = pbOffAav D := by rw [v1]; pk_tos
  have lOAin : (u1 pbOAin).length = pbOffAinv D := by rw [v1]; pk_tos
  have lOa : (u1 pbOa).length = pbOffav D := by rw [v1]; pk_tos
  have lOcb : (u1 pbOcb).length = pbOffcbv D := by rw [v1]; pk_tos
  have lOA0 : (u1 pbOA0).length = pbOffA0v D := by rw [v1]; pk_tos
  have lTM : (u1 ptTM).length = 4 * D.K * (D.N * D.K) := by rw [v1]; pk_tos
  have lTAa : (u1 ptTAa).length = 16 * D.K ^ 3 * (D.N * D.K) := by rw [v1]; pk_tos
  have lTV : (u1 pbTV).length = 2 * D.K * (D.N * D.K) := by rw [v1]; pk_tos
  have lTC : (u1 pbTC).length = 2 * D.K := by rw [v1]; pk_tos
  have lTN : (u1 pbTN).length = D.N * D.K := by rw [v1]; pk_tos
  have lKg : (u1 pbKg).length = gD D := by rw [v1]; pk_tos
  have lTB : (u1 ptTB).length = D.b := by rw [v1]; pk_tos
  have lT16 : (u1 ptT16).length = 16 := by rw [v1]; pk_tos
  have uB1 : u1 rB1 = [false] := by rw [v1]; pk_tos; exact h38
  have uQZ : u1 swQZ = (List.range 16).flatMap z := by rw [v1]; pk_tos; exact hz
  have uQU : u1 swQU = (List.range 16).flatMap uu := by rw [v1]; pk_tos; exact hu
  obtain ⟨tH, hQH⟩ : ∃ tH, (u1 2).drop (u1 pbOH).length = (List.range D.b).flatMap
      (fun t => ptHfW D mpk t ++ encL D.N D.K (pbR0 D mpk t ++ pbR1 D mpk t)) ++ tH :=
    ⟨_, by rw [u12, lOH, pkDrop_H, pbFH_eq]⟩
  obtain ⟨th, hQh⟩ : ∃ th, (u1 1).drop (u1 pbOh).length = (List.range D.b).flatMap
      (fun t => pbH0W D mpk ct t ++ encL D.N D.K (pbR2 D mpk ct t)) ++ th :=
    ⟨_, by rw [u11, lOh, pkDrop_h, pbFh_eq D mpk ct]⟩
  obtain ⟨tA, hQA⟩ : ∃ tA, (u1 2).drop (u1 pbOAa).length =
      (List.range D.b).flatMap (ptAaW D mpk) ++ tA :=
    ⟨_, by rw [u12, lOAa, pkDrop_Aa, pbFAa_eq]⟩
  obtain ⟨tAin, hAin⟩ : ∃ tAin, (u1 2).drop (u1 pbOAin).length =
      (List.range 16).flatMap (pbAinW D mpk) ++ tAin :=
    ⟨_, by rw [u12, lOAin, pkDrop_Ain, pbFAin_eq]⟩
  obtain ⟨ta, ha⟩ : ∃ ta, (u1 2).drop (u1 pbOa).length =
      (List.range 16).flatMap (pbAW D mpk) ++ ta :=
    ⟨_, by rw [u12, lOa, pkDrop_a, pbFa_eq]⟩
  obtain ⟨tcb, hcb⟩ : ∃ tcb, (u1 1).drop (u1 pbOcb).length =
      (List.range 16).flatMap (pbCbW D ct) ++ tcb :=
    ⟨_, by rw [u11, lOcb, pkDrop_cb, pbFcb_eq]⟩
  obtain ⟨tA0, hA0⟩ : ∃ tA0, (u1 2).drop (u1 pbOA0).length = ptA0W D mpk ++ tA0 :=
    ⟨_, by rw [u12, lOA0, pkDrop_A0]; exact congrArg (· ++ _) (matE_enc D mpk.A0)⟩
  obtain ⟨P1, P2, P3⟩ := exec_pbPubC (N := D.N) (K := D.K) hN hK D.b u1 (ptHfW D mpk)
    (pbH0W D mpk ct) (ptAaW D mpk) (pbAinW D mpk) (pbAW D mpk) (pbCbW D ct) z uu (pbR0 D mpk)
    (pbR1 D mpk) (pbR2 D mpk ct) (ptA0W D mpk) tH th tA tAin ta tcb tA0 hQH hQh hQA hAin ha hcb hA0
    uQZ uQU (fun t => by rw [lTM, pbLen_Hf]) (fun t => by rw [lTM, pbLen_H01 D mpk t])
    (fun t => by rw [lTV, (pbLen_V D mpk ct t).1]) (fun t => by rw [lTV, (pbLen_V D mpk ct t).2.1])
    (fun t => by rw [lTAa, pbLen_Aa]) (fun t => by rw [lTC, (pbLen_R D mpk ct t).1])
    (fun t => by rw [lTC, (pbLen_R D mpk ct t).2.1]) (fun t => by rw [lTC, (pbLen_R D mpk ct t).2.2])
    (fun i => by rw [lTAa, pbLen_Ain]) (fun i => by rw [lTV, (pbLen_V D mpk ct i).2.2.1])
    (fun i => by rw [lTV, (pbLen_V D mpk ct i).2.2.2]) (fun i => by rw [lTN, lz])
    (fun i => by rw [lTN, lu]) (by rw [lTM, pbLen_A0]) lTB uB1 lT16 lTN
    (by rw [lKg]; exact pk_gD_pos D)
  have hv : v = exec D.N D.K pbPubC u1 := rfl
  have kin : ∀ r, pbInR r = true → v r = u1 r := fun r hr => exec_writes _ _ _ (pbPubC_keeps r hr)
  have k0 : ∀ r, (r = 0 ∨ r = pkRaw ∨ r = 5) → v r = u r := fun r hr => by
    rw [hv, exec_writes _ _ _ (pkPub_keeps r hr), v1]
    rcases hr with rfl | rfl | rfl <;> pk_tos
  refine ⟨?_, P2, P3, by rw [kin _ rfl, lTB], by rw [kin _ rfl, lT16], by rw [kin _ rfl, lTM],
    by rw [kin _ rfl, lTAa], by rw [kin _ rfl, lTN], k0 0 (by simp), k0 pkRaw (by simp),
    k0 5 (by simp), by rw [kin _ rfl, uB1, h38]⟩
  rw [hv, P1, lKg]
  refine List.flatMap_congr fun t _ => ?_
  rw [pbG_eq]

/-! ### The slab loops -/

theorem pk_flatten_rep {α : Type*} (a : α) : ∀ n m : ℕ,
    (List.replicate n (List.replicate m a)).flatten = List.replicate (n * m) a
  | 0, _ => by simp
  | n + 1, m => by
    rw [List.replicate_succ, List.flatten_cons, pk_flatten_rep a n m, ← List.replicate_add]
    congr 1; ring

theorem pk_encL_rep {N K : ℕ} (n : ℕ) (a : Rq N K) :
    encL N K (List.replicate n a) = (List.replicate n (encRM N K a)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, encL_cons, ih, List.replicate_succ, List.flatten_cons]

theorem pkZ2_eq : ptZ2W D = List.replicate (2 * D.K * (D.N * D.K)) false := by
  rw [ptZ2W, ptZRow, encL_replicate_zero]

theorem pkZL_eq : ptZLW' D = List.replicate ((2 ^ D.b - 1) * (2 * D.K) * (D.N * D.K)) false := by
  rw [ptZLW', ptZRow, pk_flatten_rep, encL_replicate_zero]

theorem pkRows_len (zr : PrI (setting D) Pos → Wb D → Bool) :
    (∀ r ∈ ptRA D zr, r.length = D.mb) ∧ (∀ r ∈ ptRR0 D zr, r.length = D.mb) ∧
      (∀ r ∈ ptRZ D zr, r.length = D.mb) ∧ (∀ r ∈ ptRRin D zr, r.length = D.mb) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · intro r hr
    simp only [ptRA, ptRR0, ptRZ, ptRRin, List.mem_map] at hr
    obtain ⟨j, -, rfl⟩ := hr
    simp [ptRowOf]

theorem pkLen_rows (zr : PrI (setting D) Pos → Wb D → Bool) :
    (ptRA D zr).length = D.b * (ptND D * ptNC D) ∧ (ptRR0 D zr).length = ptNC D ∧
      (ptRZ D zr).length = 16 * ptNC D ∧ (ptRRin D zr).length = 16 * (ptND D * ptNC D) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ptRA, List.length_map, length_enum_prod', length_enumDCS]
    exact congrArg (· * _) (List.length_finRange (n := D.b))
  · rw [ptRR0, List.length_map, length_enumColS]
  · rw [ptRZ, List.length_map, length_enum_prod', length_enumColS]; rfl
  · rw [ptRRin, List.length_map, length_enum_prod', length_enumDCS]; rfl

theorem pkFin_keeps : ptInlLoopC.writes 1 = false ∧ ptInlLoopC.writes 2 = false ∧
    (pkClrL pkScratch).writes 0 = false := by decide

/-- **The end of the run**: the loops' constants, the `zr` rows, both slab loops write the stream. -/
theorem exec_pkFin (mpk : MPKt D) (ct : CTt D) (C : List Bool) (x : Pos → ℕ)
    (zr : PrI (setting D) Pos → Wb D → Bool) (u : St)
    (hPB : u ptPB = (List.range D.b).flatMap (fun t => ptGW D mpk ct t ++ (ptAaW D mpk t ++ ptHfW D mpk t)))
    (hPS : u ptPS = (List.range 16).flatMap (fun i => ptSPW D mpk ct C x i ++ ptPUW D C x i))
    (hA0 : u ptA0 = ptA0W D mpk) (lTB : (u ptTB).length = D.b) (lT16 : (u ptT16).length = 16)
    (lTM : (u ptTM).length = 4 * D.K * (D.N * D.K))
    (lTAa : (u ptTAa).length = 16 * D.K ^ 3 * (D.N * D.K)) (lTN : (u pbTN).length = D.N * D.K)
    (h0 : u 0 = []) (hR : (u pkRaw).drop (pbOffzr D) = (zrEnc D).enc zr)
    (h5 : u 5 = [true]) (h38 : u rB1 = [false]) :
    exec D.N D.K pkFinC (exec D.N D.K (templateOpsC (pkLpOps D)) u) rAinS =
      encL D.N D.K ((seRestL D).flatMap (sePkOf D mpk C ct x (ExpLUT.progOf zr))) := by
  have hN : 0 < D.N := Nat.pos_of_ne_zero (by simp [Dims.N])
  have e1 := exec_templateOpsC (N := D.N) (K := D.K) (pkLpOps D) u
    (fun op hop => ⟨(pkLp_targets D op hop).2.1, (pkLp_targets D op hop).2.2.1⟩) h5 h38
  set u1 := exec D.N D.K (templateOpsC (pkLpOps D)) u with hu1
  have v1 : ∀ r, u1 r = templateOpsState (pkLpOps D) u r := fun r => by rw [e1]
  -- the state before the `Ā` loop
  set u3 := exec D.N D.K (.drop ptZR pkZoff) (exec D.N D.K (.cp ptZR pkRaw)
    (exec D.N D.K (.app ptOne 4) u1)) with hu3
  have f3 : ∀ r, r ≠ ptZR → r ≠ ptOne → u3 r = u1 r := by
    intro r a b; simp [hu3, Function.update_apply, a, b]
  have z3 : u3 ptZR = (ptRZ D zr ++ (ptRR0 D zr ++ (ptRRin D zr ++ ptRA D zr))).flatten := by
    have e : u3 ptZR = (u1 pkRaw).drop (u1 pkZoff).length := by simp [hu3, Function.update_apply]
    rw [e, ptZRWord_eq, ← hR, v1, v1]
    pk_tos
  have o3 : u3 ptOne = encRM D.N D.K 1 := by
    have e : u3 ptOne = u1 ptOne ++ u1 4 := by simp [hu3, Function.update_apply]
    rw [e, v1, v1, encRM_one' D hN]
    pk_tos
  have sk3 : PtSkIn D.b (ptGW D mpk ct) (ptAaW D mpk) (ptHfW D mpk) (ptSPW D mpk ct C x)
      (ptPUW D C x) (ptA0W D mpk) u3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun i => ?_, fun i => ?_⟩
    · rw [f3 _ (by decide) (by decide), v1]; pk_tos; exact hPB
    · rw [f3 _ (by decide) (by decide), v1]; pk_tos; exact hPS
    · rw [f3 _ (by decide) (by decide), v1]; pk_tos; exact hA0
    · rw [f3 _ (by decide) (by decide), v1]; pk_tos; exact lTB
    · rw [f3 _ (by decide) (by decide), v1]; pk_tos; exact lT16
    · rw [f3 _ (by decide) (by decide), v1, pbLen_G]; pk_tos; exact lTM.symm
    · rw [f3 _ (by decide) (by decide), v1, pbLen_Hf]; pk_tos; exact lTM.symm
    · rw [f3 _ (by decide) (by decide), v1, pbLen_Aa]; pk_tos; exact lTAa.symm
    · rw [f3 _ (by decide) (by decide), v1, pbLen_SP]; pk_tos
    · rw [f3 _ (by decide) (by decide), v1, pbLen_PU]; pk_tos; exact lTN.symm
  have rc3 : PtRowConst D.mb (ptNC D) (ptND D) (encRM D.N D.K 1) (encRM D.N D.K 0) (ptZ2W D)
      (ptZLW' D) u3 := by
    refine ⟨?_, ?_, ?_, o3, ?_, ?_, ?_⟩
    · rw [f3 _ (by decide) (by decide), v1]; pk_tos
    · rw [f3 _ (by decide) (by decide), v1]; pk_tos
    · rw [f3 _ (by decide) (by decide), v1]; pk_tos
    · rw [f3 _ (by decide) (by decide), v1, encRM_zero]; pk_tos
    · rw [f3 _ (by decide) (by decide), v1, pkZ2_eq]; pk_tos
    · rw [f3 _ (by decide) (by decide), v1, pkZL_eq]; pk_tos
  obtain ⟨lA, lR0, lZ, lRin⟩ := pkRows_len D zr
  obtain ⟨i1, i2⟩ := exec_ptInlLoopC (N := D.N) (K := D.K) D.mb (ptNC D) (ptND D) D.b
    (encRM D.N D.K 1) (encRM D.N D.K 0) (ptZ2W D) (ptZLW' D) (ptRA D zr) (ptRR0 D zr) (ptRZ D zr)
    (ptRRin D zr) lA lR0 lZ lRin
    (pkLen_rows D zr).1.ge (pkLen_rows D zr).2.1.ge (pkLen_rows D zr).2.2.1.ge
    (pkLen_rows D zr).2.2.2.ge
    u3 sk3 rc3 z3
    (by rw [f3 _ (by decide) (by decide), v1]; pk_tos)
    (by rw [f3 _ (by decide) (by decide), v1]; pk_tos; rw [ptRZ, List.length_map])
    (by rw [f3 _ (by decide) (by decide), v1]; pk_tos; rw [ptRR0, List.length_map])
    (by rw [f3 _ (by decide) (by decide), v1]; pk_tos; rw [ptRRin, List.length_map])
  set u4 := exec D.N D.K ptInlLoopC u3 with hu4
  obtain ⟨hk1, hk2, hk3⟩ := pkFin_keeps
  set u5 := exec D.N D.K (.cp ptBT 2) (exec D.N D.K (.cp ptZS 1) u4) with hu5
  have f5 : ∀ r, r ≠ ptBT → r ≠ ptZS → u5 r = u4 r := by
    intro r a b; simp [hu5, Function.update_apply, a, b]
  have in5 : PtInrIn D.mb (ptNC D) (ptND D) D.b (encRM D.N D.K 1) (encRM D.N D.K 0) (ptZ2W D)
      (ptZLW' D) (ptGW D mpk ct) (ptAaW D mpk) (ptHfW D mpk) (ptSPW D mpk ct C x) (ptPUW D C x)
      (ptA0W D mpk) u5 := by
    refine ⟨sk3.of_frame fun r hr => ?_, rc3.of_frame fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · rw [f5 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)]
      exact i2 r (Or.inr (Or.inl hr))
    · rw [f5 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)]
      exact i2 r (Or.inl hr)
    · have e : u5 ptBT = u4 2 := by simp [hu5, Function.update_apply]
      rw [e, hu4, exec_writes _ _ _ hk2, f3 _ (by decide) (by decide), v1]; pk_tos
    · rw [f5 _ (by decide) (by decide), i2 _ (by simp), f3 _ (by decide) (by decide), v1]; pk_tos
    · have e : u5 ptZS = u4 1 := by simp [hu5, Function.update_apply]
      rw [e, hu4, exec_writes _ _ _ hk1, f3 _ (by decide) (by decide), v1]; pk_tos
    · rw [ptZ2W, ptZRow, pk_encL_rep]
  obtain ⟨j1, -⟩ := exec_ptInrLoopC (N := D.N) (K := D.K) D.mb (ptNC D) (ptND D) D.b
    (encRM D.N D.K 1) (encRM D.N D.K 0) (ptZ2W D) (ptZLW' D) u5 in5
  have hE : exec D.N D.K pkFinC u1 = exec D.N D.K (pkClrL pkScratch)
      (exec D.N D.K ptInrLoopC u5) := rfl
  rw [hE, exec_writes _ _ _ hk3, j1, f5 _ (by decide) (by decide), i1,
    f3 _ (by decide) (by decide), v1]
  have e0 : templateOpsState (pkLpOps D) u rAinS = [] := by pk_tos; exact h0
  rw [e0, List.nil_append]
  exact ptStream_eq D zr mpk ct C x

/-! ### The whole run -/

theorem swSt_lt (C : List Bool) (tl : ℕ) (xs : ℕ → ℕ) : ∀ i, swSt C tl xs i < 2 ^ 14
  | 0 => by simp [swSt]
  | i + 1 => by rw [swSt]; exact val_lt_two_pow_takeD _ _

/-- The attribute is the head of the raw word: `16` blocks of `8` bits. -/
theorem pkAttr_eq (a : Attribute w8) :
    attrEnc.enc a = (List.range 16).flatMap fun i => symbolBits w8 (a ⟨i % 16, Nat.mod_lt _ (by decide)⟩) := by
  show (List.ofFn a).flatMap (symbolBits w8) = _
  rw [List.ofFn_eq_map, List.flatMap_map]
  exact pbPos_range (fun t => symbolBits w8 (a t))

theorem pkXs_eq (a : Attribute w8) :
    (fun i => hornerB (symbolBits w8 (a ⟨i % 16, Nat.mod_lt _ (by decide)⟩)) 0) =
      fun j => attrN a ⟨j % 16, Nat.mod_lt _ (by decide)⟩ := by
  funext i
  rw [hornerB_symbolBits]; rfl

/-- **The run of `pktC D`**: the stream of the packets of all slabs. -/
theorem exec_pktC (hN22 : 2 ^ 22 ≤ 2 * D.N) (σ : RawSec D) (mpk : MPKt D) (ct : CTt D)
    (C : List Bool) (hC : ValidC C) (w : St) (h0 : w 0 = (rawEnc D).enc σ)
    (h1 : w 1 = (ctEnc D).enc ct) (h2 : w 2 = (mpkEnc D).enc mpk) (h4 : w 4 = C) :
    exec D.N D.K (pktC D) w rAinS = encL D.N D.K ((seRestL D).flatMap
      (sePkOf D mpk C ct (attrN σ.1) (ExpLUT.progOf σ.2.2.2.2.2.2))) := by
  have hN : 0 < D.N := Nat.pos_of_ne_zero (by simp [Dims.N])
  have hN2 : 2 ≤ D.N := by
    by_contra h
    have : D.N ≤ 1 := by omega
    have : (2 : ℕ) ^ 22 ≤ 2 := by omega
    norm_num at this
  set x := attrN σ.1 with hx
  set blk : ℕ → List Bool := fun i => symbolBits w8 (σ.1 ⟨i % 16, Nat.mod_lt _ (by decide)⟩)
  have hblk : ∀ i, (blk i).length = 8 := fun i => length_symbolBits w8 _
  have hR : (rawEnc D).enc σ = (List.range 16).flatMap blk ++ ((instEnc D).prod
      ((vecE D (BCol (Wb D) D.K)).prod ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).prod
      ((rEnc D).prod ((floodEnc D).prod (zrEnc D)))))).enc σ.2 := by
    rw [← pkAttr_eq]; rfl
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := exec_pkPre D hN w _ C h0 h4 blk hblk _ hR
  set v := exec D.N D.K pkWalkC (exec D.N D.K (templateOpsC (pkSwOps D)) (exec D.N D.K pkMoveC w))
    with hv
  have hxs : (fun i => hornerB (blk i) 0) = fun j => x ⟨j % 16, Nat.mod_lt _ (by decide)⟩ :=
    pkXs_eq σ.1
  have hxlt : ∀ t, x t < 2 ^ 8 := fun t => (σ.1 t).isLt
  have hst : ∀ i < 16, swSt C tlK (fun i => hornerB (blk i) 0) i = (bpOf (progOf C)).state x i := by
    intro i hi
    rw [hxs]; exact swSt_eq_state C hC x hxlt i (by omega)
  have hz : v swQZ = (List.range 16).flatMap (pbZW D C x) := by
    rw [q1]
    refine List.flatMap_congr fun i hi => ?_
    have hi' : i < 16 := List.mem_range.mp hi
    have hl := swSt_lt C tlK (fun i => hornerB (blk i) 0) i
    rw [hst i hi'] at hl ⊢
    rw [swMonoW_eq D hN2 (by omega)]; rfl
  have hu : v swQU = (List.range 16).flatMap (pbUW D C x) := by
    rw [q2]
    refine List.flatMap_congr fun i hi => ?_
    have hi' : i < 16 := List.mem_range.mp hi
    have hl := swSt_lt C tlK (fun i => hornerB (blk i) 0) i
    have hb : hornerB (blk i) 0 = x ⟨i % 16, Nat.mod_lt _ (by decide)⟩ := congrFun hxs i
    have hxi := hxlt ⟨i % 16, Nat.mod_lt _ (by decide)⟩
    rw [hst i hi'] at hl ⊢
    rw [hb, swMonoW_eq D hN2 (by omega)]; rfl
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := exec_pkPub D mpk ct v
    (by rw [q5, h1]) (by rw [q6, h2]) (pbZW D C x) (pbUW D C x) hz hu
    (fun i => (pbLen_ZU D C x i).1) (fun i => (pbLen_ZU D C x i).2) q7 q8
  set u := exec D.N D.K pbPubC (exec D.N D.K (templateOpsC (pkPbOps D)) v) with hu'
  have hPS : u ptPS = (List.range 16).flatMap (fun i => ptSPW D mpk ct C x i ++ ptPUW D C x i) := by
    rw [p2]
    refine List.flatMap_congr fun i _ => ?_
    rw [pbSP_eq, pbPU_eq]
  have F := exec_pkFin D mpk ct C x σ.2.2.2.2.2.2 u p1 hPS p3 p4 p5 p6 p7 p8 (by rw [p9, q3])
    (by rw [p10, q4, pkDrop_zr]) (by rw [p11, q7]) (by rw [p12, q8])
  exact F

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
