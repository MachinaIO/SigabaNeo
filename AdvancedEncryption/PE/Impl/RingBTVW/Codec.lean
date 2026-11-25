import PE.Impl.RingBTVW.ImplBase
import SigabaNeoStd.Encode.Ring

/-!
# Explicit encodings of the keys and ciphertexts

Fixed-length bit encodings that an algorithm can read and write: every ring element is its `N`
coefficients of `K` bits, matrices and families are read in the order of the explicit enumerations
of their index types (`SigabaNeo.Encode.Enum`), and records are the concatenations of their fields.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

instance : Enum (Sdw (N := N) hk).Attr := inferInstanceAs (Enum (Fin nA))
instance : Enum (Sdw (N := N) hk).ctBits.Index := inferInstanceAs (Enum (Fin 2 × Col k × Fin k × Fin N))

/-- Matrices over the ring. -/
def matEnc (r s : Type) [Enum r] [Enum s] :
    FixedEnc (Matrix r s (Rg N K)) ((Enum.list (α := r)).length *
      ((Enum.list (α := s)).length * (N * K))) :=
  FixedEnc.fun (FixedEnc.fun (ringEnc N K))

/-- **Public keys**: `B₀`, `B₁`, the `B_j`, `p`. -/
def pkEnc :=
  ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).prod ((matEnc (Fin 1) (TrapCol k)).prod
    ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
      (matEnc (Fin 1) (Col k))).prod (ringEnc N K)))).comap
    (fun m : PK hk c => (m.B₀, m.B₁, m.Bj, m.p)) (fun a b h => by
      cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨h1, h2, h3, h4⟩ := h; subst h1 h2 h3 h4; rfl)

/-- **Ciphertexts**: the `Ψᵢ`, `c₀`, `c₁`, the `c_j`, `κ`. -/
def ctEnc :=
  ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr) (matEnc (N := N) (K := K) (Fin 2) (Col k))).prod
    ((matEnc (Fin 1) (Fin c.d)).prod ((matEnc (Fin 1) (TrapCol k)).prod
      ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (matEnc (Fin 1) (Col k))).prod (ringEnc N K))))).comap
    (fun ct : CT hk c => (ct.Ψ, ct.c₀, ct.c₁, ct.cj, ct.κ)) (fun a b h => by
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h; subst h1 h2 h3 h4 h5; rfl)

/-- The three parts of a secret key. -/
def keyEnc :=
  ((matEnc (N := N) (K := K) (Fin c.d) (Fin 1)).prod ((matEnc (TrapCol k) (Fin 1)).prod
    (matEnc (Col k) (Fin 1)))).comap
    (fun sk : SecretKey (Fin c.d) (TrapCol k) (R := Rg N K) (k := k) => (sk.k₀, sk.k₁, sk.k₂))
    (fun a b h => by
      cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl)

/-- **Keys of predicates**: the public key and the secret key. -/
def skEnc := (pkEnc hk c).prod (keyEnc (N := N) (K := K) c)

/-- **Master secret keys**: the public key and the trapdoor `(e, t)`. -/
def mskEnc :=
  (pkEnc hk c).prod ((matEnc (N := N) (K := K) (Fin 1) (Col k)).prod (ringEnc N K))

end AdvancedEncryption.RingBTVW
