import PE.Impl.ExpLUT.Prog.EncHelperMath

/-! # Canonical automorphism ciphertext words -/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG
  SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

variable (D : Dims)

/-- Normalizing the iterated automorphism produces the canonical scheme word. -/
theorem canonW_autTW (a : Rg D) (j : ℕ) :
    canonW D.N D.K (autTW D.N D.K (gD D) j (wd D a)) =
      wd D ((setting D).E.σ ((setting D).idx j) a) := by
  rw [canonW_eq D.K_pos (length_autTW D.N_pos (length_wd D a) j),
    autTW, decRM_autIt D (length_wd D a), decRM_wd]
  rfl

/-- The lower gadget row subtracts the transformed helper before canonicalization. -/
theorem canonW_autTW_sub (a b : Rg D) (j : ℕ) :
    canonW D.N D.K (subRMW D.N D.K (autTW D.N D.K (gD D) j (wd D a))
      (autTW D.N D.K (gD D) j (wd D b))) =
      wd D ((setting D).E.σ ((setting D).idx j) a -
        (setting D).E.σ ((setting D).idx j) b) := by
  have ha := length_autTW (g := gD D) D.N_pos (length_wd D a) j
  have hb := length_autTW (g := gD D) D.N_pos (length_wd D b) j
  rw [canonW_eq D.K_pos (length_subRMW _ _ ha _), decRM_subRMW ha hb,
    autTW, autTW, decRM_autIt D (length_wd D a), decRM_autIt D (length_wd D b),
    decRM_wd, decRM_wd]
  rfl

/-- One upper-row iteration consumes and transforms one canonical ring entry. -/
theorem gc0Step_word (a : Rg D) (j : ℕ) (out rest : List Bool) :
    gc0Step D.N D.K (gD D) j (out, wd D a ++ rest) =
      ((out ++ wd D ((setting D).E.σ ((setting D).idx j) a)).drop (D.N * D.K), rest) := by
  simp only [gc0Step, show wd D a = encRM D.N D.K a from rfl,
    MVM.takeD_encRM_append, MVM.drop_encRM_append]
  rw [show encRM D.N D.K a = wd D a from rfl, canonW_autTW]

/-- One lower-row iteration consumes both the matrix entry and its helper entry. -/
theorem gc1Step_word (a b : Rg D) (j : ℕ) (out rest rest' : List Bool) :
    gc1Step D.N D.K (gD D) j (out, wd D a ++ rest, wd D b ++ rest') =
      ((out ++ wd D ((setting D).E.σ ((setting D).idx j) a -
        (setting D).E.σ ((setting D).idx j) b)).drop (D.N * D.K), rest, rest') := by
  simp only [gc1Step, show wd D a = encRM D.N D.K a from rfl,
    show wd D b = encRM D.N D.K b from rfl,
    MVM.takeD_encRM_append, MVM.drop_encRM_append]
  rw [show encRM D.N D.K a = wd D a from rfl,
    show encRM D.N D.K b = wd D b from rfl, canonW_autTW_sub]

/-- The full upper-row loop transforms a stream without retaining any input entries. -/
theorem gc0Step_iter (j : ℕ) (l : List (Rg D)) (out rest : List Bool)
    (hout : l.length * (D.N * D.K) ≤ out.length) :
    (gc0Step D.N D.K (gD D) j)^[l.length]
        (out, MVM.encL D.N D.K l ++ rest) =
      ((out ++ MVM.encL D.N D.K
        (l.map ((setting D).E.σ ((setting D).idx j)))).drop
          (l.length * (D.N * D.K)), rest) := by
  induction l generalizing out with
  | nil => simp [MVM.encL]
  | cons a l ih =>
    have hn : D.N * D.K ≤ out.length := by
      simp only [List.length_cons, Nat.succ_mul] at hout; omega
    have hlen : ((out ++ wd D ((setting D).E.σ ((setting D).idx j) a)).drop
        (D.N * D.K)).length = out.length := by
      rw [List.length_drop, List.length_append, length_wd]; omega
    simp only [List.length_cons, Function.iterate_succ_apply, MVM.encL_cons,
      List.append_assoc]
    rw [show encRM D.N D.K a = wd D a from rfl, gc0Step_word,
      ih _ (by rw [hlen]; simp only [List.length_cons, Nat.succ_mul] at hout; omega)]
    simp only [List.map_cons, MVM.encL_cons]
    rw [List.drop_append_of_le_length hn, List.append_assoc]
    rw [Nat.succ_mul, Nat.add_comm (l.length * (D.N * D.K)) (D.N * D.K),
      ← List.drop_drop, List.drop_append_of_le_length hn]
    rfl

/-- The lower-row loop consumes equal-length matrix/helper streams in lockstep. -/
theorem gc1Step_iter (j : ℕ) (l l' : List (Rg D)) (out rest rest' : List Bool)
    (hlen : l'.length = l.length) (hout : l.length * (D.N * D.K) ≤ out.length) :
    (gc1Step D.N D.K (gD D) j)^[l.length]
        (out, MVM.encL D.N D.K l ++ rest, MVM.encL D.N D.K l' ++ rest') =
      ((out ++ MVM.encL D.N D.K (List.zipWith
        (fun a b ↦ (setting D).E.σ ((setting D).idx j) a -
          (setting D).E.σ ((setting D).idx j) b) l l')).drop
          (l.length * (D.N * D.K)), rest, rest') := by
  induction l generalizing l' out with
  | nil =>
    have hl' : l' = [] := List.length_eq_zero_iff.mp hlen
    subst l'
    simp [MVM.encL]
  | cons a l ih =>
    cases l' with
    | nil => simp at hlen
    | cons b l' =>
      have heq : l'.length = l.length := by simpa using hlen
      have hn : D.N * D.K ≤ out.length := by
        simp only [List.length_cons, Nat.succ_mul] at hout; omega
      have ho : ((out ++ wd D ((setting D).E.σ ((setting D).idx j) a -
          (setting D).E.σ ((setting D).idx j) b)).drop (D.N * D.K)).length =
          out.length := by rw [List.length_drop, List.length_append, length_wd]; omega
      simp only [List.length_cons, Function.iterate_succ_apply, MVM.encL_cons,
        List.append_assoc]
      rw [show encRM D.N D.K a = wd D a from rfl,
        show encRM D.N D.K b = wd D b from rfl, gc1Step_word,
        ih l' _ heq (by rw [ho]; simp only [List.length_cons, Nat.succ_mul] at hout; omega)]
      simp only [List.zipWith_cons_cons, MVM.encL_cons]
      rw [List.drop_append_of_le_length hn, List.append_assoc]
      rw [Nat.succ_mul, Nat.add_comm (l.length * (D.N * D.K)) (D.N * D.K),
        ← List.drop_drop, List.drop_append_of_le_length hn]
      rfl

/-- The vector codec is the canonical ring-word stream in enumeration order. -/
theorem vecE_encL {α : Type} [Encode.Enum α] (f : α → Rg D) :
    (vecE D α).enc f = MVM.encL D.N D.K ((Encode.Enum.list (α := α)).map f) := rfl

theorem gc0Step_vec (j : ℕ) (v : Col D.K → Rg D) (out rest : List Bool)
    (hout : (D.K + D.K) * (D.N * D.K) ≤ out.length) :
    (gc0Step D.N D.K (gD D) j)^[D.K + D.K]
      (out, (vecE D (Col D.K)).enc v ++ rest) =
      ((out ++ (vecE D (Col D.K)).enc
        (fun c ↦ (setting D).E.σ ((setting D).idx j) (v c))).drop
          ((D.K + D.K) * (D.N * D.K)), rest) := by
  simpa only [vecE_encL, List.length_map, length_col, List.map_map, Function.comp_def]
    using gc0Step_iter D j ((Encode.Enum.list (α := Col D.K)).map v) out rest
      (by simpa only [List.length_map, length_col] using hout)

theorem gc1Step_vec (j : ℕ) (v h : Col D.K → Rg D) (out rest rest' : List Bool)
    (hout : (D.K + D.K) * (D.N * D.K) ≤ out.length) :
    (gc1Step D.N D.K (gD D) j)^[D.K + D.K]
      (out, (vecE D (Col D.K)).enc v ++ rest, (vecE D (Col D.K)).enc h ++ rest') =
      ((out ++ (vecE D (Col D.K)).enc (fun c ↦
        (setting D).E.σ ((setting D).idx j) (v c) -
          (setting D).E.σ ((setting D).idx j) (h c))).drop
            ((D.K + D.K) * (D.N * D.K)), rest, rest') := by
  simpa only [vecE_encL, List.length_map, length_col, List.zipWith_map, List.zipWith_self]
    using gc1Step_iter D j ((Encode.Enum.list (α := Col D.K)).map v)
      ((Encode.Enum.list (α := Col D.K)).map h) out rest rest' (by simp)
      (by simpa only [List.length_map, length_col] using hout)

/-- Both loops together produce the scheme's gadget ciphertext and consume both streams. -/
theorem gcSteps_scheme (j : ℕ) (H : Matrix (Fin 2) (Col D.K) (Rg D))
    (h : Col D.K → Rg D) (out rest rest' : List Bool)
    (hout : (D.K + D.K + (D.K + D.K)) * (D.N * D.K) ≤ out.length) :
    let r := (gc0Step D.N D.K (gD D) j)^[D.K + D.K]
      (out, (matE D (Fin 2) (Col D.K)).enc H ++ rest)
    (gc1Step D.N D.K (gD D) j)^[D.K + D.K]
      (r.1, r.2, (vecE D (Col D.K)).enc h ++ rest') =
      ((out ++ (matE D (Fin 2) (Col D.K)).enc
        (gcAut (setting D) ((setting D).idx j) H h)).drop
          ((D.K + D.K + (D.K + D.K)) * (D.N * D.K)), rest, rest') := by
  have hn : (D.K + D.K) * (D.N * D.K) ≤ out.length := by
    rw [Nat.add_mul] at hout; omega
  have hlen : ((out ++ (vecE D (Col D.K)).enc (fun c ↦
      (setting D).E.σ ((setting D).idx j) (H 0 c))).drop
        ((D.K + D.K) * (D.N * D.K))).length = out.length := by
    rw [List.length_drop, List.length_append, length_vecE', length_col]; omega
  simp only [matE_fin2, List.append_assoc]
  rw [gc0Step_vec D j (H 0) out _ hn]
  dsimp only
  rw [gc1Step_vec D j (H 1) h _ rest rest' (by rw [hlen]; exact hn)]
  have hr0 : (gcAut (setting D) ((setting D).idx j) H h) 0 =
      fun c ↦ (setting D).E.σ ((setting D).idx j) (H 0 c) := by
    funext c
    change (setting D).E.σ ((setting D).idx j) (H 0 c) -
      (if (0 : Fin 2) = 1 then (setting D).E.σ ((setting D).idx j) (h c) else 0) = _
    simp
  have hr1 : (gcAut (setting D) ((setting D).idx j) H h) 1 =
      fun c ↦ (setting D).E.σ ((setting D).idx j) (H 1 c) -
        (setting D).E.σ ((setting D).idx j) (h c) := by
    funext c
    change (setting D).E.σ ((setting D).idx j) (H 1 c) -
      (if (1 : Fin 2) = 1 then (setting D).E.σ ((setting D).idx j) (h c) else 0) = _
    simp
  rw [matE_fin2 D (α := Col D.K) (gcAut (setting D) ((setting D).idx j) H h), hr0, hr1,
    List.drop_append_of_le_length hn, List.append_assoc]
  conv_rhs =>
    rw [Nat.add_mul, ← List.drop_drop]
    rw [List.drop_append_of_le_length hn]

/-- The actual gadget-ciphertext program returns canonical scheme words and empty scratch. -/
theorem run_gcAutP_scheme (S : Store 60) (j : ℕ)
    (H : Matrix (Fin 2) (Col D.K) (Rg D)) (h : Col D.K → Rg D)
    (rest rest' : List Bool) (hs : ∀ i : Fin 60, 9 ≤ i.val → S i = [])
    (hK : (S 5).length = D.K) (hN : (S 6).length = D.N)
    (hNK : (S 7).length = D.N * D.K) (hL : (S 8).length = D.K + D.K)
    (hg : (S 3).length = gD D) (hj : (S 4).length = j)
    (hH : S 1 = (matE D (Fin 2) (Col D.K)).enc H ++ rest)
    (hh : S 2 = (vecE D (Col D.K)).enc h ++ rest')
    (hout : (D.K + D.K + (D.K + D.K)) * (D.N * D.K) ≤ (S 0).length) :
    gcAutP.run S = Function.update (Function.update (Function.update S 0
      ((S 0 ++ (matE D (Fin 2) (Col D.K)).enc
        (gcAut (setting D) ((setting D).idx j) H h)).drop
          ((D.K + D.K + (D.K + D.K)) * (D.N * D.K)))) 1 rest) 2 rest' := by
  rw [run_gcAutP D.K_pos D.N_pos S hs hK hN hNK, hg, hj, hL, hH, hh]
  rw [gcSteps_scheme D j H h (S 0) rest rest' hout]
  rfl

end AdvancedEncryption.ExpLUT.Prog.EncW
