import PE.Impl.ExpLUT.AH.Games
import SigabaNeo.Lib.Lattices.BitLaw
import SigabaNeo.Lib.Machines.FiniteAlg

/-!
# The simulator (package G)

The simulator outputs the encoding of a ciphertext with independent `unifW` entries (`ctUW`, fair
coins only), whatever the public key: `simMachine D`, with `simSpec : SimSpec D (simMachine D)`.
It is obtained from `Machine.exists_finiteAlg'` (the inputs `(pw, mpk)` range over a finite set);
its cost does not enter `PE.AttributeHiding` (only the existence of a simulator does). An explicit
program is `unifCanonP D.N D.K nCT` of package F followed by the output frame.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo Cslib Cslib.Probability

variable (D : Dims)

theorem bitLaw_unifW : BitLaw (unifW D) (D.N * D.K) := ⟨decRM D.N D.K, rfl⟩

/-- The simulator's ciphertext law is an image of fair bits. -/
theorem bitLaw_ctUW : ∃ m, BitLaw (ctUW D) m := by
  have h1 := bitLaw_unifW D
  unfold ctUW iidFam iidLaw
  exact ⟨_, BitLaw.bind (BitLaw.pi h1) fun _ => BitLaw.bind (BitLaw.pi (BitLaw.pi h1)) fun _ =>
    BitLaw.bind (BitLaw.pi (BitLaw.pi (BitLaw.pi h1))) fun _ =>
    BitLaw.bind (BitLaw.pi (BitLaw.pi h1)) fun _ =>
    BitLaw.bind (BitLaw.pi (BitLaw.pi (BitLaw.pi h1))) fun _ =>
    BitLaw.bind (BitLaw.pi h1) fun _ => BitLaw.map h1 _⟩

theorem exists_simMachine : ∃ M : Machine, SimSpec D M := by
  obtain ⟨m, g, hg⟩ := bitLaw_ctUW D
  obtain ⟨M, hM, -⟩ := Machine.exists_finiteAlg' (A := MPKt D)
    (fun mpk => [pwW, (mpkEnc D).enc mpk])
    (fun a b h => by
      simp only [List.cons.injEq, and_true, true_and] at h
      exact (mpkEnc D).inj h) m (fun _ w => [(ctEnc D).enc (g w)])
  refine ⟨M, fun mpk => ?_⟩
  rw [hM mpk, hg, PMF.map_comp]
  rfl

/-- **The simulator.** -/
noncomputable def simMachine : Machine := Classical.choose (exists_simMachine D)

theorem simSpec : SimSpec D (simMachine D) := Classical.choose_spec (exists_simMachine D)

end AdvancedEncryption.ExpLUT.Prog
