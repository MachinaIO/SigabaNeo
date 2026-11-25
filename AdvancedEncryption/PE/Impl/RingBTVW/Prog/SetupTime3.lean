import PE.Impl.RingBTVW.Prog.SetupTime

/-!
# Time bounds of the setups of hybrid 3 and of the ideal side, and of the χ sampler

Shape bounds bundled as `Bnd` (scratch threshold `S₀`, appended bits `a`, scratch growth `s`, a
monotone time `T`), with the combinators of the programs (`Bnd.seq`, `Bnd.count`, `Bnd.rep`,
`Bnd.ite`), so every bound below is an explicit term (`ATBb p B`: `p` has the shape bound `B`).

* `atbb_cbdP` / `atbb_chiP`: the χ sampler, `bChi`;
* **`time_setup3P`**, **`time_setupIP`**: for any sampler `Pχ` with a shape bound `Bχ` leaving
  tape `6` alone, `timeBoundT (setup3P hk c Pχ) (io2 a b 0) ≤ time3 hk c Bχ a b` (resp. `timeI`);
  `time_setup3P_conf`, `time_setupIP_conf` for `confP` and `chiP`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg Matrix
  AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

/-! ### Bundled shape bounds -/

/-- A shape bound: threshold, appended bits, scratch growth, monotone time. -/
structure Bnd where
  S₀ : ℕ
  a : ℕ
  s : ℕ
  T : ℕ → ℕ → ℕ
  mono : Mono2 T

/-- `p` has the shape bound `B` (output tape `0`). -/
def ATBb (p : XProg 7) (B : Bnd) : Prop := ATB p (0 : Fin 7) B.S₀ B.a B.s B.T

/-- Sequencing. -/
def Bnd.seq (B C : Bnd) : Bnd :=
  ⟨max B.S₀ C.S₀, B.a + C.a, B.s + C.s, fun x S => B.T x S + C.T (x + B.a) (S + B.s),
    mono2_seq _ _ B.mono C.mono⟩

/-- A counted loop of `n` rounds. -/
def Bnd.count (n : ℕ) (B : Bnd) : Bnd :=
  ⟨max B.S₀ n, n * B.a, n * B.s, countT n B.a B.s B.T, countT_mono B.mono⟩

/-- A branch. -/
def Bnd.ite (B C : Bnd) : Bnd :=
  ⟨max B.S₀ C.S₀, max B.a C.a, max B.s C.s, fun x S => max (B.T x S) (C.T x S) + 1,
    fun x x' S S' hx hS => Nat.add_le_add_right (max_le_max (B.mono x x' S S' hx hS)
      (C.mono x x' S S' hx hS)) 1⟩

/-- A primitive (or a block of primitive cost) appending `a` bits, growing the scratch by `s`. -/
def Bnd.prim (a s : ℕ) : Bnd := ⟨0, a, s, tBit, mono_tBit⟩

/-- `n` copies. -/
def Bnd.rep (B : Bnd) : ℕ → Bnd
  | 0 => Bnd.prim 0 0
  | n + 1 => Bnd.seq B (Bnd.rep B n)

theorem ATBb.seq {p q : XProg 7} {B C : Bnd} (hp : ATBb p B) (hq : ATBb q C) :
    ATBb (XProg.seq p q) (B.seq C) := ATB.seq2 hp hq

theorem ATBb.mono' {p : XProg 7} {B C : Bnd} (h : ATBb p B) (hS : B.S₀ ≤ C.S₀) (ha : B.a ≤ C.a)
    (hs : B.s ≤ C.s) (hT : ∀ x S, C.S₀ ≤ S → B.T x S ≤ C.T x S) : ATBb p C := ATB.mono h hS ha hs hT

theorem ATBb.ifBit {p q : XProg 7} (i : Fin 7) {B C : Bnd} (hp : ATBb p B) (hq : ATBb q C) :
    ATBb (XProg.ifBit i p q) (B.ite C) :=
  ATB.ifBit i (hp.mono' (B := B) (C := ⟨max B.S₀ C.S₀, max B.a C.a, max B.s C.s, B.T, B.mono⟩)
      (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) fun _ _ _ => le_rfl)
    (hq.mono' (B := C) (C := ⟨max B.S₀ C.S₀, max B.a C.a, max B.s C.s, C.T, C.mono⟩)
      (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) fun _ _ _ => le_rfl)

theorem ATBb.ifBlank {p q : XProg 7} (i : Fin 7) {B C : Bnd} (hp : ATBb p B) (hq : ATBb q C) :
    ATBb (XProg.ifBlank i p q) (B.ite C) :=
  ATB.ifBlank i (hp.mono' (B := B) (C := ⟨max B.S₀ C.S₀, max B.a C.a, max B.s C.s, B.T, B.mono⟩)
      (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) fun _ _ _ => le_rfl)
    (hq.mono' (B := C) (C := ⟨max B.S₀ C.S₀, max B.a C.a, max B.s C.s, C.T, C.mono⟩)
      (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) fun _ _ _ => le_rfl)

theorem ATBb.prim {p : Prim 7} {a s : ℕ}
    (h : ∀ x S, p.lenT (shp (0 : Fin 7) x S) ≤ shp 0 (x + a) (S + s)) :
    ATBb (prog (.prim p)) (Bnd.prim a s) := ATB.prim p fun x S _ => h x S

theorem ATBb.count {t c : Fin 7} (htr : t ≠ 0) (hcr : c ≠ 0) (hct : c ≠ t) {body : XProg 7}
    {B : Bnd} (hb : ATBb body B) (hc : body.Preserves c) (n : ℕ) :
    ATBb (withCount t c n (forN c t body)) (B.count n) :=
  ATB.count htr hcr hct hb hc B.mono n

theorem atbb_nopX : ATBb nopX (Bnd.prim 0 0) := ATBb.prim fun x S i => by
  simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> simp_all

theorem ATBb.rep {p : XProg 7} {B : Bnd} (h : ATBb p B) : ∀ n, ATBb (repX p n) (B.rep n)
  | 0 => atbb_nopX
  | n + 1 => h.seq (ATBb.rep h n)

/-! ### Blocks -/

/-- A fair bit. -/
def bCoin : Bnd := ⟨1, 1, 0, tCoin, mono_tCoin⟩

theorem atbb_coinAp : ATBb (coinAp 0 2) bCoin := atb_coinAp

/-- The bound of `n` fair bits. -/
def bCoins (n : ℕ) : Bnd := bCoin.count n

theorem atbb_coinsF (n : ℕ) : ATBb (coinsF n) (bCoins n) :=
  ATBb.count (t := 3) (c := 4) (by decide) (by decide) (by decide) atbb_coinAp
    (preserves_coinAp (by decide) (by decide)) n

/-- The bound of `n` zeros. -/
def bZeros (n : ℕ) : Bnd := (Bnd.prim 1 0).count n

theorem atbb_bitAp0 (b : Bool) : ATBb (bitAp 0 b) (Bnd.prim 1 0) := atb_bitAp0 b

theorem atbb_zerosF (n : ℕ) : ATBb (zerosF n) (bZeros n) :=
  ATBb.count (t := 3) (c := 4) (by decide) (by decide) (by decide) (atbb_bitAp0 false)
    (preserves_bitAp _ (by decide)) n

/-- A binary ring element. -/
def bEntB (N K : ℕ) : Bnd := bCoin.seq (bZeros (N * K - 1))

theorem atbb_entB (N K : ℕ) : ATBb (entB N K) (bEntB N K) := atbb_coinAp.seq (atbb_zerosF _)

/-- A flooding coefficient. -/
def bEntF (K w : ℕ) : Bnd := (bCoins (min w K)).seq (bZeros (K - w))

theorem atbb_entF (K w : ℕ) : ATBb (entF K w) (bEntF K w) := (atbb_coinsF _).seq (atbb_zerosF _)

theorem atbb_repF {body : XProg 7} {B : Bnd} (hb : ATBb body B) (hc : body.Preserves 6) (n : ℕ) :
    ATBb (repF n body) (B.count n) :=
  ATBb.count (t := 5) (c := 6) (by decide) (by decide) (by decide) hb hc n

/-! ### The χ sampler -/

/-- A fair bit on the scratch tape `2`. -/
def bCoin2 : Bnd := ⟨1, 0, 1, tCoin, mono_tCoin⟩

theorem atbb_coinAp2 : ATBb (coinAp 2 4) bCoin2 := by
  show ATB (coinAp 2 4) (0 : Fin 7) 1 0 1 tCoin
  have h1 := ATB.coin (r := (0 : Fin 7)) (i := 4) (by decide)
  have h2 : ATB (prog (.prim (.snocHead 2 4))) (0 : Fin 7) 0 0 1 tBit :=
    ATB.prim _ fun x S _ i => by
      simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> simp_all <;> omega
  have h3 : ATB (prog (.prim (.clear 4))) (0 : Fin 7) 0 0 0 tBit :=
    ATB.prim _ fun x S _ i => by
      simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> omega
  have h23 : ATB (prog (.seq (.prim (.snocHead 2 4)) (.prim (.clear 4)))) (0 : Fin 7) 0 (0 + 0)
      (1 + 0) (fun x S => tBit x S + tBit (x + 0) (S + 1)) := fun x S hS => h2.seq h3 x S hS
  refine (ATB.seq2 h1 h23).mono (by simp) le_rfl le_rfl fun x S _ => ?_
  simp only [tBit, tCoin]; omega

theorem atbb_bitAp3 : ATBb (bitAp 3 true) (Bnd.prim 0 1) := ATBb.prim fun x S i => by
  simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> simp_all <;> omega

theorem atbb_tail (j : Fin 7) (hj : j ≠ 0) : ATBb (prog (.prim (.tail j))) (Bnd.prim 0 0) :=
  ATBb.prim fun x S i => by
    simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> simp_all <;> omega

theorem atbb_clear (j : Fin 7) : ATBb (prog (.prim (.clear j))) (Bnd.prim 0 0) :=
  ATBb.prim fun x S i => by
    simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> simp_all

/-- One step of the unary count. -/
def bStep : Bnd := ((Bnd.prim 0 1).ite (Bnd.prim 0 0)).seq (Bnd.prim 0 0)

theorem atbb_upStep : ATBb upStep bStep :=
  (ATBb.ifBit 2 atbb_bitAp3 atbb_nopX).seq (atbb_tail 2 (by decide))

theorem atbb_downStep : ATBb downStep (((Bnd.prim 0 0).ite (Bnd.prim 0 0)).seq (Bnd.prim 0 0)) :=
  (ATBb.ifBit 2 (atbb_tail 3 (by decide)) atbb_nopX).seq (atbb_tail 2 (by decide))

/-- Appending a fixed word of `n` bits. -/
def bWord : ℕ → Bnd
  | 0 => Bnd.prim 0 0
  | n + 1 => (Bnd.prim 1 0).seq (bWord n)

theorem atbb_wordAp : ∀ w : List Bool, ATBb (wordAp 0 w) (bWord w.length)
  | [] => atbb_nopX
  | b :: w => (atbb_bitAp0 b).seq (atbb_wordAp w)

/-- The leaf of the chain. -/
def bLeaf (K L : ℕ) : Bnd := (Bnd.prim 0 0).seq ((bWord L).seq ((Bnd.prim 1 0).count (K - L)))

theorem atbb_leafP (K L : ℕ) (v : ℤ) : ATBb (leafP K L v) (bLeaf K L) := by
  have h := (atbb_wordAp ((zmodEnc L).enc (v : ZMod (2 ^ L))))
  rw [(zmodEnc L).length] at h
  exact (atbb_clear 3).seq (h.seq (ATBb.count (t := 3) (c := 4) (by decide) (by decide) (by decide)
    (atbb_bitAp0 _) (preserves_bitAp _ (by decide)) (K - L)))

/-- The chain of tests with `f` tests left. -/
def bChain (K L : ℕ) : ℕ → Bnd
  | 0 => bLeaf K L
  | f + 1 => (bLeaf K L).ite ((Bnd.prim 0 0).seq (bChain K L f))

theorem atbb_chainP (K L η : ℕ) : ∀ f j, ATBb (chainP K L η f j) (bChain K L f)
  | 0, j => atbb_leafP K L _
  | f + 1, j => ATBb.ifBlank 3 (atbb_leafP K L _) ((atbb_tail 3 (by decide)).seq
      (atbb_chainP K L η f (j + 1)))

/-- **The bound of the centered binomial sampler.** -/
def bCbd (η L K : ℕ) : Bnd :=
  (bCoin2.rep (η + η)).seq (((Bnd.prim 0 1).rep η).seq ((bStep.rep η).seq
    ((((Bnd.prim 0 0).ite (Bnd.prim 0 0)).seq (Bnd.prim 0 0)).rep η |>.seq (bChain K L (η + η)))))

theorem atbb_cbdP (η L K : ℕ) : ATBb (cbdP η L K) (bCbd η L K) :=
  (ATBb.rep atbb_coinAp2 _).seq ((ATBb.rep atbb_bitAp3 _).seq ((ATBb.rep atbb_upStep _).seq
    ((ATBb.rep atbb_downStep _).seq (atbb_chainP K L η _ _))))

/-- The bound of the χ sampler of `confP`. -/
def bChi : Bnd := bCbd 16 6 Params.Kp

theorem atbb_chiP : ATBb chiP bChi := atbb_cbdP _ _ _

/-! ### The setups of hybrid 3 and of the ideal side -/

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (Bχ : Bnd)

/-- The bound of the coins `rest`. -/
def bRest : Bnd :=
  (bCoins (N * K)).seq ((Bχ.count ((Enum.list (α := Fin c.d)).length * N)).seq
    (((Bχ.count N).seq ((Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).seq
        (Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)))).seq
      (((bEntB N K).count (nR hk c)).seq (Bχ.count N))))

theorem atbb_restP {Pχ : XProg 7} (hχ : ATBb Pχ Bχ) (h6 : Pχ.Preserves 6) :
    ATBb (restP hk c Pχ) (bRest hk c Bχ) :=
  (atbb_coinsF _).seq ((atbb_repF hχ h6 _).seq (((atbb_repF hχ h6 _).seq ((atbb_repF hχ h6 _).seq
    (atbb_repF hχ h6 _))).seq ((atbb_repF (atbb_entB N K) (preserves6_entB N K) _).seq
      (atbb_repF hχ h6 _))))

/-- The bound of the random part of the secret of hybrid 3. -/
def bTail3 : Bnd :=
  (bCoins ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))).seq
    ((bCoins (nW hk c)).seq ((bCoins (N * K)).seq ((bRest hk c Bχ).seq
      ((bEntF K c.w).count (nE (N := N) hk)))))

theorem atbb_tail3P {Pχ : XProg 7} (hχ : ATBb Pχ Bχ) (h6 : Pχ.Preserves 6) :
    ATBb (tail3P hk c Pχ) (bTail3 hk c Bχ) :=
  (atbb_coinsF _).seq ((atbb_coinsF _).seq ((atbb_coinsF _).seq ((atbb_restP hk c Bχ hχ h6).seq
    (atbb_repF (atbb_entF K c.w) (preserves6_entF K c.w) _))))

/-- **The time of the setup of hybrid 3**, from the bounds `a`, `b` of its two inputs. -/
def time3 (a b : ℕ) : ℕ :=
  tApp a (max b (bTail3 hk c Bχ).S₀) b + (bTail3 hk c Bχ).T (a + b) (max b (bTail3 hk c Bχ).S₀)

theorem time_appendTail {tl : XProg 7} {B : Bnd} (h : ATBb tl B) (a b : ℕ) :
    timeBoundT (XProg.seq (appendTapeP 0 1 3 4) tl) (io2 (R := 5) a b 0) ≤
      tApp a (max b B.S₀) b + B.T (a + b) (max b B.S₀) := by
  set S := max b B.S₀
  have hℓ : io2 (R := 5) a b 0 ≤ shp (0 : Fin 7) a S := fun i => by
    simp only [io2, shp]; split_ifs <;> simp_all <;> omega
  obtain ⟨h1, h2⟩ := appendTape_bounds (le_max_left b _) hℓ (by simp [io2])
  exact Nat.add_le_add h1 (ATB.time h (le_max_right _ _) h2)

theorem time_setup3P {Pχ : XProg 7} (hχ : ATBb Pχ Bχ) (h6 : Pχ.Preserves 6) (a b : ℕ) :
    timeBoundT (setup3P hk c Pχ) (io2 (R := 5) a b 0) ≤ time3 hk c Bχ a b :=
  time_appendTail (atbb_tail3P hk c Bχ hχ h6) a b

/-- The bound of the coins of `Enc`. -/
def bEncCoins : Bnd :=
  (bCoins (N * K)).seq ((Bχ.count ((Enum.list (α := Fin c.d)).length * N)).seq
    (((Bχ.count N).seq ((Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).seq
        (Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)))).seq
      (((bEntB N K).count (nR hk c)).seq (((bEntF K c.w).count (nE (N := N) hk)).seq
        (Bχ.count N)))))

/-- The bound of the uniform ciphertext. -/
def bCt : Bnd :=
  (bCoins (nPsi (N := N) hk)).seq ((bCoins (nC0 (N := N) (K := K) c)).seq
    ((bCoins (nC1 (N := N) (K := K) (k := k))).seq ((bCoins (nCj (N := N) hk)).seq
      (bCoins (N * K)))))

/-- The bound of the random part of the secret of the ideal side. -/
def bTailI : Bnd :=
  (bCoins ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))).seq
    ((bCoins (nW hk c)).seq ((bCoins (N * K)).seq ((bEncCoins hk c Bχ).seq (bCt hk c))))

theorem atbb_tailIP {Pχ : XProg 7} (hχ : ATBb Pχ Bχ) (h6 : Pχ.Preserves 6) :
    ATBb (tailIP hk c Pχ) (bTailI hk c Bχ) :=
  (atbb_coinsF _).seq ((atbb_coinsF _).seq ((atbb_coinsF _).seq
    (((atbb_coinsF _).seq ((atbb_repF hχ h6 _).seq (((atbb_repF hχ h6 _).seq
      ((atbb_repF hχ h6 _).seq (atbb_repF hχ h6 _))).seq
      ((atbb_repF (atbb_entB N K) (preserves6_entB N K) _).seq
        ((atbb_repF (atbb_entF K c.w) (preserves6_entF K c.w) _).seq (atbb_repF hχ h6 _)))))).seq
    ((atbb_coinsF _).seq ((atbb_coinsF _).seq ((atbb_coinsF _).seq ((atbb_coinsF _).seq
      (atbb_coinsF _))))))))

/-- **The time of the setup of the ideal side.** -/
def timeI (a b : ℕ) : ℕ :=
  tApp a (max b (bTailI hk c Bχ).S₀) b + (bTailI hk c Bχ).T (a + b) (max b (bTailI hk c Bχ).S₀)

theorem time_setupIP {Pχ : XProg 7} (hχ : ATBb Pχ Bχ) (h6 : Pχ.Preserves 6) (a b : ℕ) :
    timeBoundT (setupIP hk c Pχ) (io2 (R := 5) a b 0) ≤ timeI hk c Bχ a b :=
  time_appendTail (atbb_tailIP hk c Bχ hχ h6) a b

/-- **The setup of hybrid 3 for `confP`.** -/
theorem time_setup3P_conf (a b : ℕ) :
    timeBoundT (setup3P Params.hkp Params.confP chiP) (io2 (R := 5) a b 0) ≤
      time3 Params.hkp Params.confP bChi a b :=
  time_setup3P _ _ _ atbb_chiP preserves6_chiP a b

/-- **The setup of the ideal side for `confP`.** -/
theorem time_setupIP_conf (a b : ℕ) :
    timeBoundT (setupIP Params.hkp Params.confP chiP) (io2 (R := 5) a b 0) ≤
      timeI Params.hkp Params.confP bChi a b :=
  time_setupIP _ _ _ atbb_chiP preserves6_chiP a b

end AdvancedEncryption.RingBTVW.Prog
