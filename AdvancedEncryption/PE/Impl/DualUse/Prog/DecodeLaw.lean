import PE.Impl.DualUse.Prog.Decode

/-!
# The law of the decoded instances

The instance read off a registry word (`inst3Of`, `inst5Of`) has, under the registry's real and
uniform Ring-LWE laws, exactly the laws of the instances of the hybrids (`inst3Real`,
`inst3Unif`, `nfReal`, `nfUnif`): the `hinst` hypothesis of `acceptProb_reduction_accOn`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW
  Cslib Cslib.Probability

variable {N K k : ℕ}

theorem realLaw_map_inst3Of (err : SecretDist) :
    (ModuleLWE.realLaw (params3 N (2 ^ K) k err).toModule).map (inst3Of (N := N) (K := K) (k := k)) =
      inst3Real (k := k) (polyOf (N := N) (ModuleLWE.coeffLaw (2 ^ K) err)) := by
  rw [ringLWE_realLaw_eq (params3 N (2 ^ K) k err), PMF.map_comp, inst3Real_eq,
    ← ringReal_reindex (params3 N (2 ^ K) k err).m (enumFin (Col k)), PMF.map_comp]
  congr 1
  funext v
  exact inst3Of_encodeRing v

theorem idealLaw_map_inst3Of (err : SecretDist) :
    (ModuleLWE.idealLaw (params3 N (2 ^ K) k err).toModule).map (inst3Of (N := N) (K := K) (k := k)) =
      inst3Unif (k := k) (R := Rg N K) := by
  rw [ringLWE_idealLaw_eq (params3 N (2 ^ K) k err), PMF.map_comp, inst3Unif_eq,
    ← uniform_reindex (params3 N (2 ^ K) k err).m (enumFin (Col k)), PMF.map_comp]
  congr 1
  funext v
  exact inst3Of_encodeRing v

set_option maxHeartbeats 1000000 in
theorem realLaw_map_inst5Of (d : ℕ) (err : SecretDist) :
    (ModuleLWE.realLaw (params5 N (2 ^ K) k (Fin d) err).toModule).map
        (inst5Of (N := N) (K := K) (k := k) d) =
      nfReal (Wd := Fin d) (k := k) (polyOf (N := N) (ModuleLWE.coeffLaw (2 ^ K) err)) := by
  rw [ringLWE_realLaw_eq (params5 N (2 ^ K) k (Fin d) err), PMF.map_comp, nfReal_eq,
    ← ringReal_reindex (params5 N (2 ^ K) k (Fin d) err).m (enumFin (Idx5 (Fin d) k)), PMF.map_comp]
  congr 1
  funext v
  exact inst5Of_encodeRing d v

set_option maxHeartbeats 1000000 in
theorem idealLaw_map_inst5Of (d : ℕ) (err : SecretDist) :
    (ModuleLWE.idealLaw (params5 N (2 ^ K) k (Fin d) err).toModule).map
        (inst5Of (N := N) (K := K) (k := k) d) =
      nfUnif (Wd := Fin d) (k := k) (R := Rg N K) := by
  rw [ringLWE_idealLaw_eq (params5 N (2 ^ K) k (Fin d) err), PMF.map_comp, nfUnif_eq,
    ← uniform_reindex (params5 N (2 ^ K) k (Fin d) err).m (enumFin (Idx5 (Fin d) k)), PMF.map_comp]
  congr 1
  funext v
  exact inst5Of_encodeRing d v

end AdvancedEncryption.DualUse.Prog
