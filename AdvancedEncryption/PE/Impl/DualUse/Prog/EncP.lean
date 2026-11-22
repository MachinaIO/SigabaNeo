import PE.Impl.DualUse.Prog.EncSem
import SigabaNeo.Lib.Machines.Prog.Moves

/-!
# `Enc` as a tape program

`encP X : XProg 124` realizes the law `encM` of `Enc` exactly:

1. **parsing** (`parseP`): the input `encodeTuple [pw, mpk, x, [M]]` (tape `120`) is read frame by
   frame (`unframeP`, counters built by `natP`): the fields `B₀`, `B₁`, the `B_j`, `p` of `mpk`,
   the date bits and the message bit land on the tapes `1 … 6`;
2. **the coins** (framed samplers, scratch `52 … 56`): `s`, `e₀`, `e₁ = [σ | ea | ez]`, the binary
   `Rᵢ`, the flooding errors, `e'` on the tapes `7 … 12`;
3. **templates** (`natP`, built by doubling): the output register `0` and the tapes `13 … 38`;
4. **the core** `encCoreP` (framed on the tapes `0 … 119`);
5. **the output**: the frame of the output register on tape `122` (`frameApP`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

/-! ### Parsing -/

/-- Drop `n` bits of the input (counter template `121`, scratch `123`). -/
def dropChunk (n : ℕ) : XProg 124 :=
  seq (natP 121 123 n) (seq (dropP 120 123 121) (prog (.prim (.clear 121))))

/-- Read `n` framed bits of the input into `D`. -/
def ufChunk (D : Fin 124) (n : ℕ) : XProg 124 :=
  seq (natP 121 123 n) (seq (unframeP 120 D 123 121) (prog (.prim (.clear 121))))

theorem law_dropChunk (n : ℕ) (s : Store 124) (h121 : s 121 = []) (h123 : s 123 = []) :
    (dropChunk n).law s = PMF.pure (Function.update s 120 ((s 120).drop n)) := by
  rw [dropChunk, law_seq, law_natP (by decide) n s h123, PMF.pure_bind, law_seq,
    law_dropP (by decide) (by decide) _ (by simp [h123]), PMF.pure_bind, law_prim]
  congr 1
  funext t
  simp only [Prim.apply, Function.update_apply]
  by_cases h1 : t = 121
  · subst h1; simp [h121]
  · simp [h1]

theorem law_ufChunk (D : Fin 124) (hD : D.val < 120) (n : ℕ) (s : Store 124) (h121 : s 121 = [])
    (h123 : s 123 = []) (u rest : List Bool) (hW : s 120 = u.flatMap (fun b => [true, b]) ++ rest)
    (hn : u.length = n) :
    (ufChunk D n).law s = PMF.pure (Function.update (Function.update s D (s D ++ u)) 120 rest) := by
  have hD120 : (120 : Fin 124) ≠ D := fun h => by subst h; simp at hD
  have hD121 : D ≠ 121 := fun h => by subst h; simp at hD
  have hD123 : D ≠ 123 := fun h => by subst h; simp at hD
  rw [ufChunk, law_seq, law_natP (by decide) n s h123, PMF.pure_bind, law_seq,
    law_unframeP hD120 (by decide) hD123 (by decide) _ (by simp [h123]) u rest
      (by simp [Function.update_apply, hW]) (by simp [hn]), PMF.pure_bind, law_prim]
  congr 1
  funext t
  simp only [Prim.apply, Function.update_apply]
  by_cases h1 : t = 121
  · subst h1; simp [h121, Ne.symm hD121]
  · by_cases h2 : t = D
    · subst h2; simp [h1, hD120]
    · simp [h1, h2]

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The parser of the input of `Enc`.** -/
def parseP : XProg 124 :=
  seq (dropChunk (2 * pw.length + 1)) <|
  seq (ufChunk 1 ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))) <|
  seq (ufChunk 2 ((Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)))) <|
  seq (ufChunk 3 ((Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
    ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Col k)).length * (N * K))))) <|
  seq (ufChunk 4 (N * K)) <| seq (prog (.prim (.tail 120))) <| seq (ufChunk 5 10) <|
  seq (prog (.prim (.tail 120))) <| ufChunk 6 1

theorem flatMap_pairs_append (u v : List Bool) :
    (u ++ v).flatMap (fun b => [true, b]) =
      u.flatMap (fun b => [true, b]) ++ v.flatMap (fun b => [true, b]) := List.flatMap_append

theorem length_frame (w : List Bool) : (Turing.MultiTapeTM.frame w).length = 2 * w.length + 1 := by
  simp [Turing.MultiTapeTM.frame]; ring

set_option maxHeartbeats 4000000 in
/-- **The law of the parser.** -/
theorem law_parseP (mpk : PK hk c) (x : Date) (b : Bool) (s : Store 124)
    (hin : s 120 = encodeTuple [pw, (pkEnc hk c).enc mpk, encDate x, [b]])
    (hD : ∀ i : Fin 124, 1 ≤ i.val → i.val ≤ 6 → s i = []) (h121 : s 121 = []) (h123 : s 123 = []) :
    (parseP hk c).law s = PMF.pure
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update s 1 ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc mpk.B₀))
          2 ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc mpk.B₁))
          3 ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
            (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc mpk.Bj))
          4 ((ringEnc N K).enc mpk.p)) 5 (encDate x)) 6 [b]) 120 [false]) := by
  have e : encodeTuple [pw, (pkEnc hk c).enc mpk, encDate x, [b]] =
      Turing.MultiTapeTM.frame pw ++ (Turing.MultiTapeTM.frame ((pkEnc hk c).enc mpk) ++
        (Turing.MultiTapeTM.frame (encDate x) ++ (Turing.MultiTapeTM.frame [b] ++ []))) := rfl
  rw [parseP, law_seq, law_dropChunk _ s h121 h123, PMF.pure_bind]
  rw [hin, e, ← length_frame, List.drop_left' rfl]
  set wB0 := (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc mpk.B₀
  set wB1 := (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc mpk.B₁
  set wBj := (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
    (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc mpk.Bj
  set wp := (ringEnc N K).enc mpk.p
  set P : List Bool → List Bool := fun u => u.flatMap (fun b => [true, b])
  have hpk : Turing.MultiTapeTM.frame ((pkEnc hk c).enc mpk) =
      P wB0 ++ (P wB1 ++ (P wBj ++ (P wp ++ [false]))) := by
    show (wB0 ++ (wB1 ++ (wBj ++ wp))).flatMap _ ++ [false] = _
    simp only [List.flatMap_append, List.append_assoc, P]
  have hfx : ∀ w : List Bool, Turing.MultiTapeTM.frame w = P w ++ [false] := fun w => rfl
  rw [hpk, hfx (encDate x), hfx [b]]
  simp only [List.append_assoc, List.append_nil]
  have hs : ∀ i : Fin 124, i ≠ 120 → Function.update s 120 (P wB0 ++ (P wB1 ++ (P wBj ++ (P wp ++
      ([false] ++ (P (encDate x) ++ ([false] ++ (P [b] ++ [false])))))))) i = s i :=
    fun i hi => Function.update_of_ne hi _ _
  rw [law_seq, law_ufChunk 1 (by decide) _ _ (by simp [h121]) (by simp [h123]) wB0 _ (by simp only [Function.update_self]; rfl)
    ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).length _), PMF.pure_bind]
  rw [law_seq, law_ufChunk 2 (by decide) _ _ (by simp [h121]) (by simp [h123]) wB1 _ (by simp only [Function.update_self]; rfl)
    ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).length _), PMF.pure_bind]
  rw [law_seq, law_ufChunk 3 (by decide) _ _ (by simp [h121]) (by simp [h123]) wBj _ (by simp only [Function.update_self]; rfl)
    ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
      (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).length _), PMF.pure_bind]
  rw [law_seq, law_ufChunk 4 (by decide) _ _ (by simp [h121]) (by simp [h123]) wp _ (by simp only [Function.update_self]; rfl)
    ((ringEnc N K).length _), PMF.pure_bind]
  rw [law_seq, law_prim, PMF.pure_bind]
  rw [law_seq, law_ufChunk 5 (by decide) _ _ (by simp [Prim.apply, h121]) (by simp [Prim.apply, h123])
    (encDate x) _ (by simp only [Prim.apply, Function.update_self, List.tail_cons]; rfl) (Gates.DateWindow.length_encDate x), PMF.pure_bind]
  rw [law_seq, law_prim, PMF.pure_bind]
  rw [law_ufChunk 6 (by decide) 1 _ ?q1 ?q2 [b] [false] ?q3 rfl]
  · congr 1
    funext t
    fin_cases t <;> simp [Prim.apply, hD]
  · simp [Prim.apply, h121]
  · simp [Prim.apply, h123]
  · simp only [Prim.apply, Function.update_self, List.tail_cons]; rfl

end AdvancedEncryption.DualUse.Prog
