import PE.Impl.RingBTVW.Security
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat

/-!
# Finiteness and encodings of the dual-use scheme's values

Over a finite ring, public keys, ciphertexts and keys are finite types
(`instFiniteMPK`, …), and any finite type has an injective encoding as words (`finEnc`: the binary
index of an element in an enumeration). These are the encodings the machines read and write.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Turing.MultiTapeTM

/-- The words of a finite type: the binary index of an element. -/
noncomputable def finEnc (α : Type) [Finite α] : α ↪ List Bool :=
  haveI := Fintype.ofFinite α
  ⟨fun a => encNat (Fintype.equivFin α a : ℕ), fun _ _ h =>
    (Fintype.equivFin α).injective (Fin.ext (encNat.injective h))⟩

variable {R : Type} [CommRing R] [Finite R] {k : ℕ} {S : Setting R k} {Wd Wt : Type}
  [Finite Wd] [Finite Wt] [Finite S.Attr] [Finite S.ctBits.Index]

instance instFiniteMPK : Finite (MPK S Wd Wt) :=
  Finite.of_injective (fun m : MPK S Wd Wt => (m.B₀, m.B₁, m.Bj, m.p)) fun a b h => by
    cases a; cases b; simp_all

instance instFiniteCiphertext : Finite (Ciphertext S Wd Wt) :=
  Finite.of_injective (fun c : Ciphertext S Wd Wt => (c.Ψ, c.c₀, c.c₁, c.cj, c.κ)) fun a b h => by
    cases a; cases b; simp_all

instance instFiniteSecretKey : Finite (SecretKey Wd Wt (R := R) (k := k)) :=
  Finite.of_injective (fun s : SecretKey Wd Wt (R := R) (k := k) => (s.k₀, s.k₁, s.k₂))
    fun a b h => by cases a; cases b; simp_all

end AdvancedEncryption.RingBTVW
