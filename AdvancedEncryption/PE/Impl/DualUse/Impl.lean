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
# The machines of the dual-use scheme for date windows

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

/-- One try of box rejection for a key of `C`. -/
noncomputable def keyTry (msk : SKey hk c) (C : List Bool) :
    KeyShort (Fin c.d) (TrapCol k) (Rg N K) → SK hk c := fun p =>
  (msk.1, keyOfOutput (if p - realTrap (S := Sdw (N := N) hk) (trapMat msk.2.1 msk.2.2) (keyMatrix msk.1 (predC C))
      (c.dec (msk.1.p - shortMap msk.1 p)) ∈ c.Small then
    some (p - realTrap (S := Sdw (N := N) hk) (trapMat msk.2.1 msk.2.2) (keyMatrix msk.1 (predC C))
      (c.dec (msk.1.p - shortMap msk.1 p)), c.dec (msk.1.p - shortMap msk.1 p)) else none))

/-- The law of `KeyGen`: the public key and a key from `keyLaw` with the trapdoor of `msk`. -/
noncomputable def keyM (msk : SKey hk c) (C : List Bool) : PMF (SK hk c) :=
  (PMF.uniformOfFinset c.Big c.hBig).map (keyTry hk c msk C)

theorem keyM_eq (msk : SKey hk c) (C : List Bool) :
    keyM hk c msk C = (keyLaw c.Big c.Small c.hBig c.dec msk.1
      (realTrap (S := Sdw (N := N) hk) (trapMat msk.2.1 msk.2.2) (keyMatrix msk.1 (predC C)))).map
        fun o => (msk.1, keyOfOutput o) := by
  unfold keyM keyLaw boxSample
  rw [PMF.map_comp]
  rfl

/-- The output of `Dec`. -/
noncomputable def decM (sk : SK hk c) (C : List Bool) (ct : CT hk c) : List Bool :=
  [decodeBit c.hN (decryptRaw sk.1 (predC C) sk.2 ct)]

/-! ### The machines -/

theorem exists_setupMachine : ∃ M : Machine, M.run (encodeTuple [pw]) =
    (setupM hk c).map fun v => encodeTuple [finEnc _ v.1, finEnc _ v.2] := by
  obtain ⟨m, g, hg⟩ := bitLaw_setup (S := Sdw (N := N) hk) (Wd := Fin c.d) c.hχ
  obtain ⟨M, hM⟩ := Machine.exists_finiteAlg (A := Unit) (fun _ => [pw]) (fun _ _ _ => rfl) m
    (fun _ w => [finEnc _ (g w).1, finEnc _ (g w).2])
  exact ⟨M, by rw [hM (), setupM, hg, PMF.map_comp]; rfl⟩

/-- The machine of `Setup`. -/
noncomputable def setupMachine : Machine := Classical.choose (exists_setupMachine hk c)

theorem exists_encMachine : ∃ M : Machine, ∀ (mpk : PK hk c) (x : Date) (b : Bool),
    M.run (encodeTuple [pw, finEnc _ mpk, encDate x, [b]]) =
      (encM hk c mpk x b).map fun ct => encodeTuple [finEnc _ ct] := by
  obtain ⟨m, g, hg⟩ := bitLaw_coins (S := Sdw (N := N) hk) (Wd := Fin c.d) c.hχ c.w
  obtain ⟨M, hM⟩ := Machine.exists_finiteAlg (A := PK hk c × Date × Bool)
    (fun a => [pw, finEnc _ a.1, encDate a.2.1, [a.2.2]]) (fun a a' h => by
      simp only [List.cons.injEq, and_true, true_and] at h
      exact Prod.ext ((finEnc _).injective h.1) (Prod.ext (encDate.injective h.2.1)
        h.2.2)) m
    (fun a w => [finEnc _ (encrypt a.1 (bitsOf a.2.1) a.2.2 (g w))])
  refine ⟨M, fun mpk x b => ?_⟩
  rw [hM (mpk, x, b), encM, PMF.map_comp, coinsM, hg, PMF.map_comp]
  rfl

/-- The machine of `Enc`. -/
noncomputable def encMachine : Machine := Classical.choose (exists_encMachine hk c)

theorem exists_keyMachine : ∃ M : Machine, ∀ (msk : SKey hk c) (C : List Bool), C.length ≤ c.L →
    M.run (encodeTuple [pw, finEnc _ msk, C]) =
      (keyM hk c msk C).map fun sk => encodeTuple [finEnc _ sk] := by
  classical
  obtain ⟨g, hg⟩ := BitLaw.uniformOfFinset_map c.mB c.emb
  obtain ⟨M, hM⟩ := Machine.exists_finiteAlg (A := SKey hk c × ShortWord c.L)
    (fun a => [pw, finEnc _ a.1, a.2.1]) (fun a a' h => by
      simp only [List.cons.injEq, and_true, true_and] at h
      exact Prod.ext ((finEnc _).injective h.1) (Subtype.ext h.2)) c.mB
    (fun a w => [finEnc _ (keyTry hk c a.1 a.2.1 (g w))])
  refine ⟨M, fun msk C hC => ?_⟩
  rw [hM (msk, ⟨C, hC⟩), keyM, PMF.map_comp]
  change _ = PMF.map _ (PMF.uniformOfFinset (Finset.univ.map c.emb) _)
  rw [hg, PMF.map_comp]
  rfl

/-- The machine of `KeyGen`. -/
noncomputable def keyMachine : Machine := Classical.choose (exists_keyMachine hk c)

theorem exists_decMachine : ∃ M : Machine, M.Deterministic ∧
    ∀ (sk : SK hk c) (C : List Bool) (ct : CT hk c), C.length ≤ c.L →
      M.run (encodeTuple [pw, finEnc _ sk, C, finEnc _ ct]) =
        PMF.pure (encodeTuple [decM hk c sk C ct]) := by
  obtain ⟨M, hdet, hM⟩ := Machine.exists_finiteAlg_det (A := SK hk c × ShortWord c.L × CT hk c)
    (fun a => [pw, finEnc _ a.1, a.2.1.1, finEnc _ a.2.2]) (fun a a' h => by
      simp only [List.cons.injEq, and_true, true_and] at h
      exact Prod.ext ((finEnc _).injective h.1) (Prod.ext (Subtype.ext h.2.1)
        ((finEnc _).injective h.2.2)))
    (fun a => decM hk c a.1 a.2.1.1 a.2.2)
  exact ⟨M, hdet, fun sk C ct hC => hM (sk, ⟨C, hC⟩, ct)⟩

/-- The machine of `Dec`. -/
noncomputable def decMachine : Machine := Classical.choose (exists_decMachine hk c)

/-- **The implementation.** -/
noncomputable def impl : Impl PE.sig where
  machine
    | .setup => setupMachine hk c
    | .enc => encMachine hk c
    | .keyGen => keyMachine hk c
    | .dec => decMachine hk c
    | .eval => winEvalMachine c.L
  deterministic a h := by
    cases a
    all_goals first
      | exact absurd h (by decide)
      | exact (Classical.choose_spec (exists_decMachine hk c)).1
      | exact winEvalMachine_deterministic _

/-! ### Correctness -/

/-- **Correctness from the scheme**: the implementation is correct if the scheme decrypts
correctly with probability at least `1 − 2^{-κ}` for every window predicate whose last gate is
`false` on `x`. -/
theorem correct_of_scheme
    (hscheme : ∀ (x : Date) (w : Window), (winWord w).length ≤ c.L →
      evalGates (encDate x, parse (winWord w)) = false → ∀ b : Bool,
        1 - ((2 : ℝ) ^ params.corrBits)⁻¹ ≤
          (((setupM hk c).bind fun v => (keyM hk c v.2 (winWord w)).bind fun sk =>
            (encM hk c v.1 x b).map fun ct => decM hk c sk (winWord w) ct) [b]).toReal) :
    Correct dateUniverse params (impl hk c) := by
  have hauth : ∀ C (x : Date), Authorized (U := dateUniverse) params (impl hk c) C x →
      C.length ≤ c.L ∧ (∃ w : Window, winWord w = C) ∧ evalGates (encDate x, parse C) = false := by
    intro C x h
    obtain ⟨h1, h2, h3⟩ := (win_authorized_iff (impl hk c) rfl C x).mp h
    exact ⟨(length_le_encodeTuple (by simp)).trans h1, h2, h3⟩
  refine correct_of_laws (U := dateUniverse) params (impl hk c) (finEnc _) (finEnc _) (finEnc _)
    (finEnc _) (setupM hk c) (keyM hk c) (encM hk c) (decM hk c) ?_ ?_ ?_ ?_ ?_
  · unfold PE.setup
    rw [run_of_machine (impl hk c) .setup (paramsWord dateUniverse params) [] (setupM hk c)
      (fun v => [finEnc _ v.1, finEnc _ v.2]) (fun _ => rfl)
      (Classical.choose_spec (exists_setupMachine hk c)), PMF.map_comp]
    rfl
  · intro msk C x hC
    unfold keyGen
    rw [run_of_machine (impl hk c) .keyGen (paramsWord dateUniverse params) [finEnc _ msk, C] (keyM hk c msk C) (fun sk => [finEnc _ sk])
      (fun _ => rfl) (Classical.choose_spec (exists_keyMachine hk c) msk C (hauth C x hC).1),
      PMF.map_comp]
    rfl
  · intro mpk x b
    unfold enc
    rw [run_of_machine (impl hk c) .enc (paramsWord dateUniverse params)
      [finEnc _ mpk, dateUniverse.encAttr x, dateUniverse.encMsg b] (encM hk c mpk x b) (fun ct => [finEnc _ ct])
      (fun _ => rfl) (Classical.choose_spec (exists_encMachine hk c) mpk x b), PMF.map_comp]
    rfl
  · intro sk C ct x hC
    unfold dec
    rw [run_of_machine (impl hk c) .dec (paramsWord dateUniverse params) [finEnc _ sk, C, finEnc _ ct]
      (PMF.pure (decM hk c sk C ct))
      (fun r => [r]) (fun _ => rfl) (by
        rw [PMF.pure_map]
        exact (Classical.choose_spec (exists_decMachine hk c)).2 sk C ct (hauth C x hC).1),
      PMF.pure_map, PMF.pure_map]
    rfl
  · intro x C hC b
    obtain ⟨h1, ⟨w, rfl⟩, h3⟩ := hauth C x hC
    exact hscheme x w h1 h3 b

/-- **Expressiveness.** -/
theorem expressive (hL : dateBound ≤ c.L) : Expressive dateUniverse params (impl hk c) :=
  expressive_win (impl hk c) rfl hL

end AdvancedEncryption.DualUse
