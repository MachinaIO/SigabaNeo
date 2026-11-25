import SigabaNeoStd.Machines.Prog.FrameParse
import SigabaNeoStd.Machines.Prog.VecBound
import SigabaNeoStd.Machines.Prog.Lookup
import SigabaNeoStd.Lattices.ProgAlgo.SpecZ

/-!
# The frame parser with doubled templates and a per-tape clock

`Prog.decodeP` writes its templates (the `K`-bit counter template and the output register of
`T + 1` bits) as literal words, `60 (K + T)` states, and its machine `decodeM` is clocked by the
uniform bound. `decodeX neg K T : XProg 14` builds the two templates by doubling (`natP`, a
counter on the extra tape `13`), sets the one-bit registers (`regsP`) and runs the same parsing
loop `coreP` (framed on the first `13` tapes):

* **`law_decodeX`**: the output on tape `2` is `decodeW neg K T w`;
* `decodeMX neg K T n`: its machine with the per-tape clock (`XProg.toMachineT`), with
  **`run_decodeMX`** (the point mass at `decodeW`), **`states_decodeMX_le`**
  (`≤ 2 · (195 m + 36) + 7000` for `K, T + 1 < 2^m`), `tapes = 14` and **`time_decodeMX_le`**:
  the parsing loop is charged `(2M + 3)(4 + 25 n + 4 n K)` (certified by the abstract interpreter,
  `check_coreP`), the templates `(2K + 1)(4M + 12) + (2T + 3)(4M + 12)`, `M = n + K + T + 1`.
-/

namespace SigabaNeo.Tape

open Cslib

namespace Prog

open scoped Prog

/-- The one-bit registers of the parser. -/
def regsP : Prog 13 :=
  setConst 6 [false] ⨾ setConst 7 [false] ⨾ setConst 8 [false] ⨾ setConst 9 [false] ⨾
    setConst 10 [false] ⨾ setConst 11 [true] ⨾ setConst 12 [false]

/-- The registers, then the parsing loop. -/
def parseCore (neg : Bool) : Prog 13 := regsP ⨾ coreP neg

theorem denote_regsP (s : Store 13) :
    regsP.denote s = pure (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update s 6 [false]) 7 [false]) 8 [false]) 9
        [false]) 10 [false]) 11 [true]) 12 [false]) := by
  simp only [regsP, denote, denote_setConst, pure_bind]

theorem wf_parseCore (neg : Bool) : (parseCore neg).WF :=
  ⟨⟨wf_setConst _ _, wf_setConst _ _, wf_setConst _ _, wf_setConst _ _, wf_setConst _ _,
    wf_setConst _ _, wf_setConst _ _⟩, wf_of_wfB (by cases neg <;> decide)⟩

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecZ in
/-- The sweeps of the parsing loop: `4 + 25 n + 4 n K` (`n` the input, `K` the template). -/
def wCore : Poly := [([], 4), ([0, 1], 25), ([0, 1, 0, 1], 4)]

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecZ in
def σCore : Asg := [vv 1, [], vv 2, [], vv 3, [], pC 1, pC 1, pC 1, pC 1, pC 1, pC 1, pC 1]

open SigabaNeo.Tape.Sym in
theorem check_coreP (neg : Bool) : check 8 (coreP neg) σCore [] wCore = true := by
  cases neg <;> decide +kernel

end Prog

namespace XProg

/-- The first `13` tapes among `14`. -/
def eFP : Fin 13 ↪ Fin 14 := Fin.castSuccEmb

/-- **The frame parser with doubled templates.** -/
def decodeX (neg : Bool) (K T : ℕ) : XProg 14 :=
  seq (natP 4 13 K) (seq (natP 2 13 (T + 1)) (frame eFP (prog (Prog.parseCore neg))))

theorem wf_decodeX (neg : Bool) (K T : ℕ) : (decodeX neg K T).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, Prog.wf_parseCore neg⟩

/-- **The law of the frame parser**: tape `2` holds `decodeW neg K T w`. -/
theorem law_decodeX (neg : Bool) (K T : ℕ) (w : List Bool) :
    ((decodeX neg K T).law (inputStore 0 w)).map (fun s => s 2) =
      PMF.pure (Prog.decodeW neg K T w) := by
  rw [decodeX, law_seq, law_natP (by decide) _ _ (by simp [inputStore]), PMF.pure_bind, law_seq,
    law_natP (by decide) _ _ (by simp [inputStore]), PMF.pure_bind, law_frame, law_prog]
  set s := Function.update (Function.update (inputStore (0 : Fin 14) w) 4 (List.replicate K false)) 2
    (List.replicate (T + 1) false)
  have hs : (fun j => s (eFP j)) = Function.update (Function.update (inputStore (0 : Fin 13) w) 4
      (List.replicate K false)) 2 (List.replicate (T + 1) false) := by
    funext j; fin_cases j <;> simp [s, eFP, inputStore]
  have hreg : Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (inputStore (0 : Fin 13) w)
        4 (List.replicate K false)) 2 (List.replicate (T + 1) false)) 6 [false]) 7 [false]) 8 [false])
          9 [false]) 10 [false]) 11 [true]) 12 [false] =
      Prog.fpSt (List.replicate K false) w [] []
        ⟨false, false, false, false, false, true, false, [], List.replicate (T + 1) false⟩ := by
    funext t; fin_cases t <;> rfl
  rw [hs, Prog.law, Prog.parseCore, Prog.denote, Prog.denote_regsP, pure_bind, hreg,
    Prog.denote_eq_run _ (Prog.noGrow_coreP neg), ProbComp.eval_pure, PMF.pure_map, PMF.pure_map,
    Prog.run_coreP]
  show PMF.pure (embedF eFP s _ (eFP 2)) = _
  rw [embedF_apply_self]
  rfl

/-- **The machine of the frame parser**, for inputs of at most `n` bits. -/
noncomputable def decodeMX (neg : Bool) (K T n : ℕ) : Machine := (decodeX neg K T).toMachineT 0 2 n

theorem run_decodeMX (neg : Bool) (K T n : ℕ) (w : List Bool) (hw : w.length ≤ n) :
    (decodeMX neg K T n).run w = PMF.pure (Prog.decodeW neg K T w) := by
  rw [decodeMX, run_toMachineT _ (wf_decodeX neg K T) 0 2 n w hw, law_decodeX]

theorem tapes_decodeMX (neg : Bool) (K T n : ℕ) : (decodeMX neg K T n).tapes = 14 := rfl

/-- **The states of the frame parser**: `O(m)` for templates below `2^m`. -/
theorem states_decodeMX_le (neg : Bool) {K T n m : ℕ} (hK : K < 2 ^ m) (hT : T + 1 < 2 ^ m) :
    (decodeMX neg K T n).states ≤ 2 * (195 * m + 36) + 7000 := by
  rw [decodeMX, states_toMachineT, card_state]
  have h1 := size_natP_le (k := 14) 4 13 K m hK
  have h2 := size_natP_le (k := 14) 2 13 (T + 1) m hT
  have h3 : (Prog.parseCore neg).size ≤ 6000 := by cases neg <;> decide +kernel
  simp only [decodeX, size_seq, size_frame, size_prog]
  omega

/-- The per-tape bound after the templates. -/
def ℓT (n K T : ℕ) : Fin 14 → ℕ :=
  natB 2 13 (T + 1) (natB 4 13 K (Prog.inputBound 0 n))

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecZ in
/-- **The clock of the frame parser.** -/
theorem time_decodeMX_le (neg : Bool) (K T n : ℕ) :
    (decodeMX neg K T n).time ≤
      (2 * n + 2) + ((2 * K + 1) * (4 * (n + K + T + 1) + 12) +
        ((2 * (T + 1) + 1) * (4 * (n + K + T + 1) + 12) +
          (14 * (2 * (n + K + T + 1 + 14) + 5) +
            (2 * (n + K + T + 1) + 3) * (4 + 25 * n + 4 * n * K)))) +
        (2 * (n + K + T + 1) + 2) := by
  set M := n + K + T + 1
  have hin : ∀ i, Prog.inputBound (0 : Fin 14) n i ≤ M := fun i => by
    simp only [Prog.inputBound, Function.update_apply]; split_ifs <;> omega
  have h1 := VB.natP (t := (4 : Fin 14)) (c := 13) (by decide) K hin (by omega)
  have a1 := fun i => natB_le' (t := (4 : Fin 14)) (c := 13) (n := K) hin (show K ≤ M by omega) i
  have h2 := VB.natP (t := (2 : Fin 14)) (c := 13) (by decide) (T + 1) a1 (by omega)
  have a2 := fun i => natB_le' (t := (2 : Fin 14)) (c := 13) (n := T + 1) a1 (show T + 1 ≤ M by omega) i
  -- the registers
  set ℓ2 := ℓT n K T
  have hℓ2 : ∀ j : Fin 13, ℓ2 (eFP j) ≤ M := fun j => a2 _
  have hR := Prog.timeBoundT_le_pcount Prog.regsP
    (by simp [Prog.regsP, Prog.setConst, Prog.LoopFree]) (fun j => ℓ2 (eFP j)) hℓ2
  have hpc : Prog.pcount Prog.regsP = 14 := rfl
  rw [hpc] at hR
  have hRl : Prog.lenBoundT Prog.regsP (fun j => ℓ2 (eFP j)) =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (fun j => ℓ2 (eFP j)) 6 1) 7 1) 8 1) 9 1) 10 1) 11 1)
          12 1 := by
    funext t
    simp only [Prog.regsP, Prog.setConst, List.foldr_cons, List.foldr_nil, Prog.lenBoundT,
      Prim.lenT, Function.update_apply]
    fin_cases t <;> simp
  -- the parsing loop
  have hC := VB.checkMap (Prog.check_coreP neg) [M, n, T + 1, K] (u := id) Function.injective_id
    (a := Prog.lenBoundT Prog.regsP (fun j => ℓ2 (eFP j))) (b := fun _ => M)
    (fun j => by
      rw [hRl]
      fin_cases j <;> simp [ℓ2, ℓT, natB, Prog.inputBound, eFP, Prog.σCore, aGet, pEval_vv, pC,
        pEval, mEval])
    (fun t => by
      rw [hRl]
      simp only [Function.update_apply]; split_ifs <;> first | exact hℓ2 t | simp [top] <;> omega)
    (fun j hj => absurd hj (by simp)) (fun _ _ => le_rfl) (fun t ht => absurd rfl (ht t))
  rw [Prog.map_id] at hC
  have hT : timeBoundT (decodeX neg K T) (Prog.inputBound 0 n) ≤
      (2 * K + 1) * (4 * M + 12) + ((2 * (T + 1) + 1) * (4 * M + 12) +
        (14 * (2 * (M + 14) + 5) + (2 * M + 3) * (4 + 25 * n + 4 * n * K))) := by
    refine Nat.add_le_add (h1 _ le_rfl).1 (Nat.add_le_add (h2 _ (h1 _ le_rfl).2).1 ?_)
    refine (timeBoundT_mono _ (h2 _ (h1 _ le_rfl).2).2).trans ?_
    show Prog.timeBoundT Prog.regsP _ + Prog.timeBoundT (Prog.coreP neg) _ ≤ _
    refine Nat.add_le_add hR ((hC _ le_rfl).1.trans (le_of_eq ?_))
    simp [Prog.wCore, pEval, mEval, top]; ring
  have hL : lenBoundT (decodeX neg K T) (Prog.inputBound 0 n) 2 ≤ M := by
    show lenBoundT (frame eFP (prog (Prog.parseCore neg))) (lenBoundT (natP 2 13 (T + 1))
      (lenBoundT (natP 4 13 K) (Prog.inputBound 0 n))) 2 ≤ M
    refine ((lenBoundT_mono (frame eFP (prog (Prog.parseCore neg))) (h2 _ (h1 _ le_rfl).2).2) 2).trans ?_
    show embedF eFP _ _ (eFP 2) ≤ _
    rw [embedF_apply_self]
    exact (hC _ le_rfl).2 2
  show (2 * n + 2) + timeBoundT (decodeX neg K T) (Prog.inputBound 0 n) +
    (2 * lenBoundT (decodeX neg K T) (Prog.inputBound 0 n) 2 + 2) ≤ _
  omega

end XProg

end SigabaNeo.Tape
