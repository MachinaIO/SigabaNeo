import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonPivotData

namespace SigabaNeo.Wall1.Watson.Pivot

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def sqSum (z : Z) := z 0^2 + z 1^2 + z 2^2 + z 3^2 + z 4^2
def slackInt (p : V) (z : Z) := 2 * (sqSum z - 1) + dot (normal z) p

def smallTest (z : Z) : Prop :=
  (∀ i, |z i| ≤ 1) ∨ ∃ j, |z j| = 2 ∧ ∀ i, i ≠ j → |z i| = 1

instance (z : Z) : Decidable (smallTest z) := by unfold smallTest; infer_instance

def edgeIndex : Matrix (Fin 5) (Fin 5) (Fin 10) :=
  !![0,0,1,2,3; 0,0,4,5,6; 1,4,0,7,8; 2,5,7,0,9; 3,6,8,9,0]

def Image.permutation (im : Image) (i : Fin 5) : Fin 5 := im.perm[i.val]?.getD 0
def Image.flip (im : Image) (i : Fin 5) := im.signs[i.val]?.getD false
def signInt (flip : Bool) : ℤ := if flip then -1 else 1

def Image.Valid (im : Image) : Prop :=
  (∀ i j, im.permutation i = im.permutation j → i = j) ∧
  ∀ t : Fin 10, unpack im.edges t = signInt (im.flip (left t)) * signInt (im.flip (right t)) *
    centers im.rep (edgeIndex (im.permutation (left t)) (im.permutation (right t)))

instance (im : Image) : Decidable im.Valid := by unfold Image.Valid; infer_instance

def Checks (k : Fin 24) : Prop :=
  let b := blocks k
  0 < b.frames.size ∧
  (∀ j : Fin b.frames.size, checkFrame (centers k) b j) ∧
  (∀ (j : Fin b.frames.size) (i : Fin 10),
    let z := row b j i
    smallTest z ∧ 0 < sqSum z ∧ slackInt (centers k) z = 0 ∧
      dest b j i < b.frames.size + b.images.size) ∧
  ∀ t : Fin b.images.size, (imageAt b t).Valid

instance (k : Fin 24) : Decidable (Checks k) := by unfold Checks; dsimp only; infer_instance

theorem checks (k : Fin 24) : Checks k := by
  fin_cases k <;> decide +kernel

end SigabaNeo.Wall1.Watson.Pivot

#print axioms SigabaNeo.Wall1.Watson.Pivot.checks
