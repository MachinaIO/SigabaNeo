import SigabaNeoStd.Lattices.ProgAlgo.ValMain
import SigabaNeoStd.Lattices.ProgAlgo.ValRegRP

/-!
# The runs of `f̂` and of the predicate on a register stream

The stage-II codes: the same preambles as `fhatC`, `gswC` (`fhatPreL`, `gswPreL`: the inputs, the
constant, the store `C :: ins ++ C^(W − n)`), then the register loop `rloopC` on the instruction
stream `RP.rpW W rp` on `GS` (`3 W` bits per instruction, the destination popped from the stream)
instead of the stage-I counter loop.

* `exec_fhatCR`: `OUTW` ends with the word of `fhatV` at the wire of the register written last of
  the unfolding `RP.toSLP rp`;
* `exec_gswCR`: `OUTW` ends with the value of the unfolding at that wire, for the step `f`.

The number `n` of inputs is the length of the template `T10`.
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo SigabaNeo.Encode

set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-- **The run of `f̂` on a register stream.** -/
def fhatCR : Code :=
  ofList [.gate 11 10 10, zkvC, ttkC, tt2C, insC, .cp RES TSl, cbC, .cp CBW RES, stC, rloopC nandC]

theorem fhatCR_eq : fhatCR = ofList (fhatPreL ++ [rloopC nandC]) := rfl

/-- **The predicate's run on a register stream.** -/
def gswCR : Code := ofList [insGC, .cp CBW 10, stC, rloopC (.gate RES IA IB)]

theorem gswCR_eq : gswCR = ofList (gswPreL ++ [rloopC (.gate RES IA IB)]) := rfl

/-- **The run of `f̂` on a register stream**: `OUTW` ends with the word of the output bundle of
`f̂` at the wire of the register written last, for the input bundles `inBW` built from the
streams. -/
theorem exec_fhatCR (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {n W' N K W A1 Ad : ℕ} (hN : 0 < N) {one : List Bool} (rp : RP (Fin n) W') (hW : n + W' ≤ W)
    {ins' : Instr (Fin n) W'} (hl : rp.getLast? = some ins')
    {bW wW : Fin n × BI N (K + 1) → List Bool} (hb : ∀ j, (bW j).length = A1)
    (hx : ∀ j, (wW j).length = Ad) {ent : Fin n → Fin 2 × (Fin 2 × Fin (K + 1)) → List Bool}
    (he : ∀ i q, (ent i q).length = N * K) {RB RW RPs : List Bool} (w : St)
    (h : FInit V K N W A1 Ad one (RP.rpW W rp) rp.length bW wW ent RB RW RPs w) :
    exec V f fhatCR w OUTW = bw (fhatV one (fV V f) (inBW bW wW ent) (enumT N (K + 1))
      (enumO N (K + 1)) (gvExp (2 ^ K)) (2 ^ K) (RP.toSLP rp).1 ((RP.toSLP rp).2 ins'.dst)) := by
  have h1 : one.length = V := by rw [← h.vone]; exact h.tm.h10
  have hin : ∀ i b, (inBW bW wW ent i b).length = V := fun i b => by
    simp [inBW, jw, hb, hx, h.hV]; have := h.hNK; omega
  obtain ⟨S1, c4⟩ := exec_fhatPre hf hN (by omega) hb hx he w h
  rw [fhatCR_eq, exec_ofList_append]
  have E4 : ∀ j, j ∉ wr (ofList fhatPreL) → exec V f (ofList fhatPreL) w j = w j :=
    fun j hj => exec_not_mem _ _ _ hj
  generalize exec V f (ofList fhatPreL) w = w4 at S1 c4 E4
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
  have hz : (fV V f one one).length = V := by rw [fV]; exact hf _ _ (by simp) (by simp)
  have hcl : (cstW V f N K one).length = (Enum.list (α := BI N (K + 1))).length * V :=
    length_bw (constRepVV_len one _ h1 hz _)
  have hinsu : ∀ x ∈ (List.finRange n).map (fun i => bw (inBW bW wW ent i)),
      x.length = (Enum.list (α := BI N (K + 1))).length * V := fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact length_bw (hin i)
  have hD : RegData ((Enum.list (α := BI N (K + 1))).length * V) W (cstW V f N K one)
      (cstW V f N K one :: (List.finRange n).map (fun i => bw (inBW bW wW ent i)) ++
        List.replicate (W - n) (cstW V f N K one)) (rpSP rp) w4 := ⟨hcl, by
      intro x hx
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact hcl
      · exact hinsu x hx
      · rw [List.eq_of_mem_replicate hx, hcl], by simp; omega,
    bnd_rpSP hW rp,
    by rw [E4 TSl (by decide +kernel), h.tsl],
    by rw [E4 TST (by decide +kernel), h.tst],
    by rw [E4 TD2 (by decide +kernel), h.td2],
    by rw [E4 TW (by decide +kernel), h.tw, List.length_replicate]⟩
  exact outw_rloopC_nand hf hN h1 hin rp hW w4 hD c4 S1 (by rw [E4 GS (by decide +kernel), h.gsw])
    (by rw [E4 GCNT (by decide +kernel), h.gcnt]) hl

/-- **The predicate's run on a register stream**: `OUTW` ends with the value of the unfolding at
the wire of the register written last, on the joint words of the inputs. -/
theorem exec_gswCR (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {n W' W A2 Ad M : ℕ} {one : List Bool} (rp : RP (Fin n) W') (hW : n + W' ≤ W)
    {ins' : Instr (Fin n) W'} (hl : rp.getLast? = some ins') {pW rW : Fin n → List Bool}
    (hp : ∀ i, (pW i).length = A2) (hr : ∀ i, (rW i).length = Ad) {xs RB RW : List Bool} (w : St)
    (h : GInit V W A2 Ad M one (RP.rpW W rp) rp.length pW rW xs RB RW w) :
    exec V f gswCR w OUTW = valueOf (fun i : Fin n => jw (pW i) (rW i) (xs.getD i.val false) M 1)
      one f (RP.toSLP rp).1 ((RP.toSLP rp).2 ins'.dst) := by
  have h1 : one.length = V := by rw [← h.vone]; exact h.it.h10
  have hin : ∀ i, (jw (pW i) (rW i) (xs.getD i.val false) M 1).length = V := fun i => by
    simp [jw, hp, hr, h.it.hV]; have := h.it.hNK; omega
  have S1 := exec_gswPre (V := V) (f := f) (by omega) hp hr w h
  rw [gswCR_eq, exec_ofList_append]
  have E2 : ∀ j, j ∉ wr (ofList gswPreL) → exec V f (ofList gswPreL) w j = w j :=
    fun j hj => exec_not_mem _ _ _ hj
  generalize exec V f (ofList gswPreL) w = w2 at S1 E2
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
  have hD : RegData V W one (one :: (List.finRange n).map (fun i =>
        jw (pW i) (rW i) (xs.getD i.val false) M 1) ++ List.replicate (W - n) one)
      (rpSP rp) w2 := ⟨h1, by
      intro x hx
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at hx
      rcases hx with rfl | ⟨i, -, rfl⟩ | hx
      · exact h1
      · exact hin i
      · rw [List.eq_of_mem_replicate hx, h1], by simp; omega,
    bnd_rpSP hW rp,
    by rw [E2 TSl (by decide +kernel), h.tsl],
    by rw [E2 TST (by decide +kernel), h.tst],
    by rw [E2 TD2 (by decide +kernel), h.td2],
    by rw [E2 TW (by decide +kernel), h.tw, List.length_replicate]⟩
  exact outw_rloopC_gate hf h1 hin rp hW w2 hD S1 (by rw [E2 GS (by decide +kernel), h.gsw])
    (by rw [E2 GCNT (by decide +kernel), h.gcnt]) hl

end ValVM

end SigabaNeo.Tape
