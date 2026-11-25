import PE.Impl.RingBTVW.Registry
import PE.Impl.RingBTVW.Flooding
import SigabaNeoStd.Lattices.BitLaw

/-!
# The laws of the dual-use scheme are realized by fair coins

Over `R = ℤ_{2^K}[X]/(X^N + 1)`, with centered binomial errors and flooding errors of width
`2^w`, every law the scheme draws is the image of uniform bits (`SigabaNeo.Lattices.BitLaw`): the
uniform rows, the error rows, the binary matrices `Rᵢ`, the coins of `Enc` (`bitLaw_coins`) and
the trapdoor part of `Setup` (`bitLaw_inst3Real`). A machine with fair coins realizes them exactly.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability

variable {N K k : ℕ}

/-- A uniform row of ring elements. -/
theorem bitLaw_uniform_row (ι : Type) [Fintype ι] [DecidableEq ι] :
    BitLaw (PMF.uniformOfFintype (Matrix (Fin 1) ι (Negacyclic (ZMod (2 ^ K)) N)))
      (Fintype.card (Fin 1) * (Fintype.card ι * (N * K))) :=
  BitLaw.uniform_fun (BitLaw.uniform_fun (BitLaw.uniform_ring N K))

/-- A row of ring elements with independent coefficients from a bit law. -/
theorem bitLaw_rowLaw {χc : PMF (ZMod (2 ^ K))} {m : ℕ} (h : BitLaw χc m) (ι : Type) [Fintype ι] :
    BitLaw (rowLaw (polyOf (N := N) χc) ι) (Fintype.card ι * (N * m)) :=
  (BitLaw.pi (BitLaw.polyOf h)).map _

variable {S : Setting (Negacyclic (ZMod (2 ^ K)) N) k} [Fintype S.Attr] [DecidableEq S.Attr]
  {Wd : Type} [Fintype Wd] [DecidableEq Wd]

omit [DecidableEq S.Attr] in
/-- The binary matrices `Rᵢ`. -/
theorem bitLaw_rm : ∃ m, BitLaw (lawRmBin (S := S) (Wd := Wd)) m :=
  ⟨_, (BitLaw.pi (BitLaw.uniform_bits Wd)).map _⟩

omit [DecidableEq S.Attr] in
/-- **The coins of `Enc`** other than the encodings' errors. -/
theorem bitLaw_rest {χc : PMF (ZMod (2 ^ K))} {m : ℕ} (h : BitLaw χc m) :
    ∃ m', BitLaw (lawRestNF (S := S) (Wd := Wd) lawRmBin (polyOf (N := N) χc)) m' := by
  obtain ⟨mR, hR⟩ := bitLaw_rm (S := S) (Wd := Wd)
  unfold lawRestNF
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure]
  exact ⟨_, BitLaw.bind (BitLaw.polyOf h) fun σ =>
    BitLaw.bind (BitLaw.uniform_ring N K) fun u₀ =>
    BitLaw.bind (bitLaw_rowLaw h Wd) fun e₀ =>
    BitLaw.bind (bitLaw_rowLaw h (Col k)) fun ea =>
    BitLaw.bind (bitLaw_rowLaw h (Col k)) fun ez =>
    BitLaw.bind hR fun Rm =>
    BitLaw.bind (BitLaw.polyOf h) fun e' => BitLaw.pure _⟩

/-- **All the coins of `Enc`**, with flooding errors of width `2^w`. -/
theorem bitLaw_coins [DecidableEq S.ctBits.Index] {χc : PMF (ZMod (2 ^ K))} {m : ℕ}
    (h : BitLaw χc m) (w : ℕ) :
    haveI : NeZero (2 ^ w) := ⟨by positivity⟩
    ∃ m', BitLaw (lawCoins (lawRestNF (S := S) (Wd := Wd) lawRmBin (polyOf (N := N) χc))
      (floodRows (S := S) (2 ^ w))) m' := by
  have : NeZero (2 ^ w) := ⟨by positivity⟩
  obtain ⟨m₁, h₁⟩ := bitLaw_rest (S := S) (Wd := Wd) h
  exact ⟨_, BitLaw.bind h₁ fun rest =>
    ((BitLaw.floodLaw (N := N) (Q := 2 ^ K) (JC S) w).map _).map (coinsOf rest)⟩

/-- **The trapdoor part of `Setup`**: `(a, t a + e)`. -/
theorem bitLaw_inst3Real {χc : PMF (ZMod (2 ^ K))} {m : ℕ} (h : BitLaw χc m) :
    ∃ m', BitLaw (inst3Real (k := k) (polyOf (N := N) χc)) m' := by
  unfold inst3Real
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure]
  exact ⟨_, BitLaw.bind (bitLaw_uniform_row (Col k)) fun a =>
    BitLaw.bind (BitLaw.polyOf h) fun t =>
    BitLaw.bind (bitLaw_rowLaw h (Col k)) fun e => BitLaw.pure _⟩

end AdvancedEncryption.RingBTVW
