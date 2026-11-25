import PE.Impl.ExpLUT.Prog.RedKeyPktState

/-!
# The packet stream, part 10: the walk computes the payloads (at `D`)

* **`swSt_eq_state`**: for a predicate word of `predLen` bits and an attribute, the walk's states
  (`tl = tlK`, symbols `x_i`) are the states of `bpOf (progOf C)` (`i ≤ 15`);
* **`swMonoW_eq`**: `swMonoW N K e (encRM 1) = encRM (X^e)` for `e ≤ 2N`;
* `hornerB_symbolBits`: the Horner value of the bits of a symbol is the symbol;
* **`swPayloads`**: the two queues of `exec_swLoopC` are the words of `pz_i = X^{z_i}`,
  `pu_i = X^{z_i + w x_{read i}}` (`ptPUW` and the last entries of `ptSPW`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM decRM val toBits)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- **The Horner value of the bits of a symbol.** -/
theorem hornerB_symbolBits : ∀ a : Symbol w8, hornerB (symbolBits w8 a) 0 = a.val := by
  decide

variable (D : Dims)

/-- **The payload words.** -/
theorem swMonoW_eq (hN : 2 ≤ D.N) {e : ℕ} (he : e ≤ 2 * D.N) :
    swMonoW D.N D.K e (encRM D.N D.K 1) = encRM D.N D.K ((setting D).E.X ^ e) := by
  have hl : (encRM D.N D.K (1 : Rq D.N D.K)).length = D.N * D.K :=
    SigabaNeo.Lattices.Algo.length_encRM _ _ _
  rw [swMonoW, takeD_of_length' hl, canonW_eq D.K_pos (by rw [SigabaNeo.Tape.length_rhoMW_iter]; exact hl),
    RedChal.decRM_rho_sub' hl he, SigabaNeo.Lattices.Algo.decRM_encRM D.K_pos, mul_one]

theorem val_lt_two_pow_takeD (n : ℕ) (l : List Bool) : val (takeD n l) < 2 ^ n := by
  have := SigabaNeo.Lattices.Algo.val_lt (takeD n l)
  rwa [length_takeD] at this

/-- **The walk's states are the states of the branching program.** -/
theorem swSt_eq_state (C : List Bool) (hC : C.length = predLen) (x : Pos → ℕ)
    (hx : ∀ t, x t < 2 ^ 8) :
    ∀ i ≤ 15, swSt C tlK (fun j => x ⟨j % 16, Nat.mod_lt _ (by decide)⟩) i =
      (bpOf (progOf C)).state x i
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := swSt_eq_state C hC x hx i (by omega)
    rw [swSt, ih]
    show _ = bpStep (progOf C) i ((bpOf (progOf C)).state x i) (x ⟨i % 16, _⟩)
    have hz : (bpOf (progOf C)).state x i < 2 ^ 14 := by
      rw [← ih]
      cases i with
      | zero => show 0 < 2 ^ 14; norm_num
      | succ i => rw [swSt]; exact val_lt_two_pow_takeD _ _
    have hxi := hx ⟨i % 16, Nat.mod_lt _ (by decide)⟩
    set z := (bpOf (progOf C)).state x i with hzdef
    set a := x ⟨i % 16, Nat.mod_lt _ (by decide)⟩ with hadef
    rw [bpStep, dif_pos (by omega)]
    simp only [progOf, readSt]
    have hu : (uOf (toSt z) (toSym a)).val = z + 2 ^ 14 * a := by
      simp only [uOf, toSt, toSym, stateBits, Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hxi]
    rw [hu, List.drop_drop]
    have hlen : stateBits * (2 ^ lutBits * i + (z + 2 ^ 14 * a)) + 14 ≤ C.length := by
      rw [hC, predLen]; simp only [stateBits, lutBits]
      have e22 : (2 : ℕ) ^ 22 = 4194304 := by norm_num
      have e14 : (2 : ℕ) ^ 14 = 16384 := by norm_num
      have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
      rw [e22, e14] at *
      rw [e8] at hxi
      omega
    have hpos : tlK * i + 14 * (z + 2 ^ 14 * a) = stateBits * (2 ^ lutBits * i + (z + 2 ^ 14 * a)) := by
      simp only [tlK, stateBits, lutBits]; ring
    rw [hpos, takeD_eq_take (by rw [List.length_drop]; omega)]
    rw [Nat.mod_eq_of_lt (by
      have := SigabaNeo.Lattices.Algo.val_lt (List.take stateBits
        (List.drop (stateBits * (2 ^ lutBits * i + (z + 2 ^ 14 * a))) C))
      simp only [List.length_take] at this
      calc _ < 2 ^ min stateBits _ := this
        _ ≤ 2 ^ stateBits := Nat.pow_le_pow_right (by norm_num) (Nat.min_le_left _ _))]

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
