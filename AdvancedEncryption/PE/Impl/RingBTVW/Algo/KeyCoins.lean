import PE.Impl.RingBTVW.ImplBase
import SigabaNeoStd.Lattices.Algo.Coins

/-!
# Key generation from explicit fair coins

The big box of key generation is the image of `c.mB` bits (`Conf.emb`). One try of box rejection is
then a fixed function of exactly `c.mB` fair coins:

* `keyLaw_coins`: `keyLaw` with the big box `univ.map emb` is the image of `m` uniform bits under
  `l ↦ boxTry … (emb (bitsOf m l))`, for any trapdoor `T` (the real one or the simulated `simTrap W_f`);
* `keyM_coins`: the law of `KeyGen` (`keyM`) is the image of `c.mB` uniform bits under
  `l ↦ keyTry msk C (c.emb (bitsOf c.mB l))`, for every gate list `C`;
* `keyM_coins_window`: for the predicates of the class, `keyTry` is `boxTry` with the real trapdoor
  of `msk` and the key matrix `keyMatrix msk.1 (predC C)`.
-/

namespace AdvancedEncryption.RingBTVW.Algo

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo Cslib Cslib.Probability
  AdvancedEncryption.RingBTVW.Fresh AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
  AdvancedEncryption.PE.Gates AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

section General

variable {R : Type*} [CommRing R] [DecidableEq R] {k : ℕ} {S : Setting R k} {Wd Wt : Type*}
  [Fintype Wd] [Fintype Wt]

/-- **The key law is a function of `m` fair coins.** -/
theorem keyLaw_coins {m : ℕ} (emb : (Fin m → Bool) ↪ KeyShort Wd Wt R)
    (hBig : (Finset.univ.map emb).Nonempty) (Small : Finset (KeyShort Wd Wt R))
    (dec : R → (Col k → R)) (mpk : MPK S Wd Wt) (T : (Col k → R) → KeyShort Wd Wt R) :
    keyLaw (Finset.univ.map emb) Small hBig dec mpk T =
      (BitString.uniformList m).map
        (fun l => boxTry Small (shortMap mpk) dec T mpk.p (emb (bitsOf m l))) :=
  boxSample_coins emb Small (shortMap mpk) dec T mpk.p

end General

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **`KeyGen` is a function of `c.mB` fair coins.** -/
theorem keyM_coins (msk : SKey hk c) (C : List Bool) :
    keyM hk c msk C =
      (BitString.uniformList c.mB).map (fun l => keyTry hk c msk C (c.emb (bitsOf c.mB l))) := by
  unfold keyM Conf.Big
  rw [uniformOfFinset_map_eq, PMF.map_comp, Function.comp_def]

/-- For the predicates of the class, one try is `boxTry` with the real trapdoor of `msk`. -/
theorem keyM_coins_window (msk : SKey hk c) (C : List Bool) (hC : ValidC C) :
    keyM hk c msk C =
      (BitString.uniformList c.mB).map (fun l => (msk.1, keyOfOutput
        (boxTry c.Small (shortMap msk.1) c.dec
          (realTrap (S := Sdw (N := N) hk) (trapMat msk.2.1 msk.2.2) (keyMatrix msk.1 (predC C)))
          msk.1.p (c.emb (bitsOf c.mB l))))) := by
  rw [keyM_coins]
  refine congrArg (fun g => PMF.map g _) (funext fun l => ?_)
  have hT : keyTry hk c msk C = keyTryW hk c msk C := funext fun p => by simp [keyTry, hC]
  rw [hT]
  rfl

end AdvancedEncryption.RingBTVW.Algo
