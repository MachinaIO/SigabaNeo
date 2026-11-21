import PE.Impl.DualUse.SetupLaw
import PE.Impl.DualUse.Correctness
import PE.Impl.DualUse.BitLaws
import PE.Impl.DualUse.Encodings
import PE.Impl.DualUse.Flooding
import PE.Impl.Gates.DateWindow
import PE.Impl.Bridge
import SigabaNeo.Lib.Machines.FiniteAlg
import SigabaNeo.Lib.Machines.GatesSLP

/-!
# The dual-use scheme for date windows: configuration and laws

For the universe of `PE.DateWindow` (a date as 10 bits, one-bit messages), over
`R = ℤ_{2^K}[X]/(X^N + 1)` (`ringSetting`, the attribute bits `Fin 10`), the configuration `Conf`
fixes the remaining parameters of the scheme. `Setup`, `Enc` and `KeyGen` are machines realizing
the scheme's laws exactly (`Machine.exists_finiteAlg`, with the coin maps of `DualUse.BitLaws`),
`Dec` a deterministic machine computing the scheme's decryption
(`Machine.exists_finiteAlg_det`), and `Eval` the evaluation of window predicates
(`Gates.DateWindow.winEvalMachine`: it authorizes only the gate lists `winWord w` of windows). A
predicate is a gate list, read as a straight-line program by `predOf`. Inputs that encode no
valid value (wrong parameters, predicates longer than `L`) are answered arbitrarily.

`correct_of_scheme`: the implementation is correct as soon as the scheme decrypts correctly with
probability at least `1 − 2^{-κ}` for every window predicate whose last gate is `false` on `x`.
The implementation is expressive for `L ≥ dateBound` (`expressive`).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

/-! ### Generic facts -/

/-- Words of length at most `L`. -/
abbrev ShortWord (L : ℕ) := {C : List Bool // C.length ≤ L}

instance (L : ℕ) : Finite (ShortWord L) := (List.finite_length_le Bool L).to_subtype

theorem length_le_encodeTuple {xs : List (List Bool)} {C : List Bool} (h : C ∈ xs) :
    C.length ≤ (encodeTuple xs).length := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    have e : encodeTuple (a :: xs) = Turing.MultiTapeTM.frame a ++ encodeTuple xs := rfl
    rw [e, List.length_append, Turing.MultiTapeTM.length_frame]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- A run whose output word is the tuple of `outs v`, for `v` from a law `μ`. -/
theorem run_of_machine {Alg : Type} {sig : Alg → AlgSig} (impl : Impl sig) (a : Alg)
    (pw : List Bool) (xs : List (List Bool)) {β : Type} (μ : PMF β)
    (outs : β → List (List Bool)) (hlen : ∀ v, (outs v).length = (sig a).outputs.length)
    (h : (impl.machine a).run (encodeTuple (pw :: xs)) = μ.map fun v => encodeTuple (outs v)) :
    impl.run a pw xs = μ.map outs := by
  unfold Impl.run
  rw [h, PMF.map_comp]
  congr 1
  funext v
  simp only [Function.comp_apply, ← hlen v, decodeTuple_encodeTuple]

theorem bitLaw_map_eq {α β : Type} {μ : PMF α} {m : ℕ} {g : List Bool → α}
    (h : μ = (BitString.uniformList m).map g) (f : α → β) :
    μ.map f = (BitString.uniformList m).map (f ∘ g) := by
  rw [h, PMF.map_comp]

/-! ### The configuration -/

/-- The ring. -/
abbrev Rg (N K : ℕ) := Negacyclic (ZMod (2 ^ K)) N

instance (K : ℕ) : NeZero (2 ^ K) := ⟨by positivity⟩

/-- The parameters of the implementation besides `(N, K, k)`. -/
structure Conf (N K k : ℕ) where
  /-- `N > 0`. -/
  hN : 0 < N
  /-- The number of columns of `B₀`. -/
  d : ℕ
  /-- The law of an error coefficient. -/
  χc : PMF (ZMod (2 ^ K))
  /-- Its number of fair coins. -/
  mχ : ℕ
  /-- It is realized by fair coins. -/
  hχ : BitLaw χc mχ
  /-- The flooding width is `2^w`. -/
  w : ℕ
  /-- The number of coins of the big box. -/
  mB : ℕ
  /-- The big box, as the image of `mB` bits. -/
  emb : (Fin mB → Bool) ↪ KeyShort (Fin d) (TrapCol k) (Rg N K)
  /-- The small box. -/
  Small : Finset (KeyShort (Fin d) (TrapCol k) (Rg N K))
  /-- The gadget decomposition. -/
  dec : Rg N K → (Col k → Rg N K)
  /-- The bound on the input words of `Eval`, and on the predicates of `KeyGen` and `Dec`. -/
  L : ℕ

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The setting: the attribute bits of a date. -/
noncomputable abbrev Sdw : Setting (Rg N K) k := ringSetting N (2 ^ K) k hk (Fin 10)

instance : DecidableEq (Sdw (N := N) hk).ctBits.Index :=
  inferInstanceAs (DecidableEq (Fin 2 × Col k × Fin k × Fin N))

/-- The public key, the master secret key, the key and the ciphertext. -/
abbrev PK := MPK (Sdw (N := N) hk) (Fin c.d) (TrapCol k)
abbrev SKey := MSK (Sdw (N := N) hk) (Fin c.d)
abbrev SK := PK hk c × SecretKey (Fin c.d) (TrapCol k) (R := Rg N K) (k := k)
abbrev CT := Ciphertext (Sdw (N := N) hk) (Fin c.d) (TrapCol k)

/-- The big box. -/
def Conf.Big : Finset (KeyShort (Fin c.d) (TrapCol k) (Rg N K)) := Finset.univ.map c.emb

theorem Conf.hBig : c.Big.Nonempty := Finset.univ_nonempty.map

/-- The parameters' word. -/
def pw : List Bool := paramsWord dateUniverse params

/-- The predicate of a gate list. -/
def predC (C : List Bool) : SLP (Fin 10) × Wire (Fin 10) := predOf 10 (parse C)

/-! ### The laws of the scheme -/

/-- The law of `Setup`. -/
noncomputable def setupM : PMF (PK hk c × SKey hk c) :=
  setupLaw (S := Sdw (N := N) hk) (Wd := Fin c.d) (polyOf c.χc)

/-- The law of the coins of `Enc`. -/
noncomputable def coinsM : PMF (EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k)) :=
  haveI : NeZero (2 ^ c.w) := ⟨by positivity⟩
  lawCoins (lawRestNF lawRmBin (polyOf c.χc)) (floodRows (S := Sdw (N := N) hk) (2 ^ c.w))

/-- The law of `Enc`. -/
noncomputable def encM (mpk : PK hk c) (x : Date) (b : Bool) : PMF (CT hk c) :=
  (coinsM hk c).map (encrypt mpk (bitsOf x) b)

/-- The key of a predicate outside the class: the zero key (it decrypts nothing). -/
def dummyKey : SecretKey (Fin c.d) (TrapCol k) (R := Rg N K) (k := k) := ⟨0, 0, 0⟩

/-- One try of box rejection for a key of the box element `p`. -/
noncomputable def keyTryW (msk : SKey hk c) (C : List Bool) :
    KeyShort (Fin c.d) (TrapCol k) (Rg N K) → SK hk c := fun p =>
  (msk.1, keyOfOutput (if p - realTrap (S := Sdw (N := N) hk) (trapMat msk.2.1 msk.2.2) (keyMatrix msk.1 (predC C))
      (c.dec (msk.1.p - shortMap msk.1 p)) ∈ c.Small then
    some (p - realTrap (S := Sdw (N := N) hk) (trapMat msk.2.1 msk.2.2) (keyMatrix msk.1 (predC C))
      (c.dec (msk.1.p - shortMap msk.1 p)), c.dec (msk.1.p - shortMap msk.1 p)) else none))

open Classical in
/-- One try of `KeyGen`: a key only for the predicates of the class (window predicates), the
zero key otherwise. Keys of gate lists outside the class would decrypt challenges whose attribute
`Eval` does not authorize. -/
noncomputable def keyTry (msk : SKey hk c) (C : List Bool) :
    KeyShort (Fin c.d) (TrapCol k) (Rg N K) → SK hk c := fun p =>
  if ∃ w : Window, winWord w = C then keyTryW hk c msk C p else (msk.1, dummyKey c)

/-- The law of `KeyGen`: the public key and a key from `keyLaw` with the trapdoor of `msk`. -/
noncomputable def keyM (msk : SKey hk c) (C : List Bool) : PMF (SK hk c) :=
  (PMF.uniformOfFinset c.Big c.hBig).map (keyTry hk c msk C)

theorem keyM_eq (msk : SKey hk c) (C : List Bool) (hC : ∃ w : Window, winWord w = C) :
    keyM hk c msk C = (keyLaw c.Big c.Small c.hBig c.dec msk.1
      (realTrap (S := Sdw (N := N) hk) (trapMat msk.2.1 msk.2.2) (keyMatrix msk.1 (predC C)))).map
        fun o => (msk.1, keyOfOutput o) := by
  have : keyTry hk c msk C = keyTryW hk c msk C := funext fun p => by simp [keyTry, hC]
  unfold keyM keyLaw boxSample
  rw [this, PMF.map_comp]
  rfl

theorem keyM_of_not (msk : SKey hk c) (C : List Bool) (hC : ¬ ∃ w : Window, winWord w = C) :
    keyM hk c msk C = PMF.pure (msk.1, dummyKey c) := by
  have : keyTry hk c msk C = fun _ => (msk.1, dummyKey c) := funext fun p => by simp [keyTry, hC]
  unfold keyM
  rw [this]
  exact PMF.map_const _ _

/-- The output of `Dec`. -/
noncomputable def decM (sk : SK hk c) (C : List Bool) (ct : CT hk c) : List Bool :=
  [decodeBit c.hN (decryptRaw sk.1 (predC C) sk.2 ct)]

end AdvancedEncryption.DualUse
