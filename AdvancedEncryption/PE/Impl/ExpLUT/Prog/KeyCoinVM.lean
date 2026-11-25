import PE.Impl.ExpLUT.Prog.KeyCoins

/-! The actual queue decoder, initialized from fair coins, has the key-box law. -/
namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape.MVM Cslib Cslib.BitString
open Cslib.Probability
open SigabaNeo.Lattices.Algo (encRM)

/-- Install every input of the queue decoder; unrelated registers may contain arbitrary data. -/
noncomputable def coinDecodeStart (D : Dims) (B : ℕ) (w : St) (cs : List Bool) : St :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update w rCoin cs) rTBk (List.replicate B false))
          rTKmB (List.replicate (D.K - B) false))
        rTN (List.replicate D.N false))
      rC2 (encRM D.N D.K (Negacyclic.ofCoeffs fun _ ↦ cB D B)))
    rDqn (List.replicate (nPI D) false)

/-- Execution consumes all coins and emits the short family in the declared enumeration order. -/
theorem exec_coinDecodeStart (D : Dims) (B : ℕ) (hK : 0 < D.K) (hBK : B ≤ D.K)
    (w : St) (cs : List Bool) (hcs : cs.length = nPI D * D.N * B) :
    exec D.N D.K decQC (coinDecodeStart D B w cs) rDq =
      encL D.N D.K ((Enum.list (α := PIdxD D)).map (coinDec D B cs)) ∧
    exec D.N D.K decQC (coinDecodeStart D B w cs) rCoin = [] := by
  rw [map_coinDec]
  apply exec_decQC hK (coinDecodeStart D B w cs) cs [] B (nPI D) hBK
    (by simpa [Nat.mul_assoc] using hcs) (cB D B)
  all_goals simp [coinDecodeStart]

/-- Distribution of the actual decoded queue, including its initialization. -/
theorem map_uniformList_exec_coinDecodeStart (D : Dims) (B : ℕ)
    (hK : 0 < D.K) (hBK : B ≤ D.K) (hB : 2 ^ B ≤ D.q) (r : ℕ) (w : St) :
    (uniformList (nPI D * D.N * B)).map
      (fun cs ↦ exec D.N D.K decQC (coinDecodeStart D B w cs) rDq) =
    (PMF.uniformOfFinset (kbOf D B hB r).Big (kbOf D B hB r).hBig).map
      (fun p ↦ encL D.N D.K ((Enum.list (α := PIdxD D)).map p)) := by
  rw [← map_uniformList_coinDec_kbOf D B hB r, PMF.map_comp]
  apply PMF.map_congr_support
  intro cs hcs
  exact (exec_coinDecodeStart D B hK hBK w cs (length_of_mem_support_uniformList hcs)).1

/-- The decoder compiles to a well-formed tape program. -/
theorem wf_compile_decQC : (compile decQC).WF := by
  apply wf_compile
  simp [Code.WFc, decQC, decQBody, decC, decBody, Code.writes]

/-- The compiled tape decoder has exactly the same output queue as the register semantics. -/
theorem law_compile_coinDecodeStart (D : Dims) (B : ℕ) (hN : 0 < D.N)
    (hK : 0 < D.K) (hBK : B ≤ D.K) (w : St) (cs : List Bool)
    (hcs : cs.length = nPI D * D.N * B) :
    ((compile decQC).law (enc D.N D.K (coinDecodeStart D B w cs))).map
      (fun s ↦ s (tR rDq)) =
    PMF.pure (encL D.N D.K ((Enum.list (α := PIdxD D)).map (coinDec D B cs))) := by
  rw [law_compile hN hK]
  simp [enc, (exec_coinDecodeStart D B hK hBK w cs hcs).1]

end AdvancedEncryption.ExpLUT.Prog
