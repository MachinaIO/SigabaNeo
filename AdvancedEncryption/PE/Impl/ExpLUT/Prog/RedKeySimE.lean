import PE.Impl.ExpLUT.Prog.RedKeySimEB
import PE.Impl.ExpLUT.Prog.RedKeySimEP
import PE.Impl.ExpLUT.Prog.RedKeySimTD

/-!
# `KGsim` on the VM (module 6b, part 9): `R̂_F = simKey …` into `rxRh` (at `D`)

`simKeyC D = seLoopKC ; sePostMC D.mb` (`sePostMC mb = natC seMb rBit1 mb ; sePostC`): one paired evaluation per slab `r ∈ Rest` (the `m̄` slabs `inl w`,
then the `2b · 2K` slabs `inr ρ`, `seRestL`), each slab appended to `rAinS`; then the split and
the two transpositions into `rxRh = 24` (`RedKeySimEP`).

**`exec_simKeyC`**: under the input contract `SimKeyIn` (below), `rxRh = encL (rowsWord R̂_F)` with
`R̂_F = simKey (helperMap D) mpk (bpOf (progOf C)) ct x P` — module 5's input `rxRh`
(`RedKeyX.exec_simXC`); **`exec_simKeyXC`** composes with `simXC` (through a set-up code `setX`
with the contract `SetXOk`): register `16` = `rowsWord (simX (helperMap D) (h1Of mpk) A_F R̂_F)`.

### The input contract `SimKeyIn` (to be established by modules 7/8)

* the constants of the evaluation `SeConst` (registers `18 … 27`, `rKc`, the templates `57 … 63`):
  `rTb` = unary `b`, `rBit1 = [false]`, `seTRec` of one record's length, `rTW` = unary `W = 2^b`,
  `rKc` of length `g`, `MulTmpl`, `rOne = 1`, `rMu0 = X⁻¹`, `rT4K`, `rTtab` (unary `tlK`),
  `rXc = X^{2^{14} − 1}`, `rTe` = unary `14`;
* the stream `rAinS = encL (seRestL.flatMap sePkOf)`: per slab `r` (`seRestL` order) the packet
  `sePacket`: the per-bit records of `seBitsOf … (seHrOf P r) (seCrOf P r) (seRhoOf P r)`
  (`gc t = gcAut (σ_{g^{2^t}}) H_{g_t^{-1}} h_{g_t^{-1}}`, the rows of `R^aut_t`, `R_{C_{g_t}}`,
  `A^aut_t`, the row of `R_{H_{g_t}}`, `H_{g_t}`), the start slab `slabβ row0 R₀ r`, `A₀`, and the
  `16` step records (`A^in_{i mod 16}`, `C^in_{read i}`, `pz_i = X^{z_i}`, the row `0` of
  `Z^in_{read i}` and `R^in_{read i}` of the slab, `pu_i = X^{z_i + w x_{read i}}`);
  **the payloads `pz_i`, `pu_i` (the BP states `z_i` of `F = bpOf (progOf C)` on `x`) are part of
  the contract**: module 8 writes them into the step records;
* `rCs = Cf` with `Cf.drop (16 tlK k) = C ++ _` for every slab `k` (the coefficient word is
  consumed by `16` tables per slab: module 8 lays out `|seRestL|` copies of `C` padded to `16 tlK`
  bits), followed by a word of length `m̄` (`|Cf.drop (16 tlK |seRestL|)| = m̄`, the split counter);
* the slab counter `seLoopC = 28` of length `|seRestL|`, `ValidC C`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib Matrix
open SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Lattices.Algo (encRM)

/-! ### The predicate word beyond its `predLen` bits is never read -/

theorem readSt_append {C : List Bool} (u : List Bool) {p : ℕ} (hp : p + stateBits ≤ C.length) :
    readSt (C ++ u) p = readSt C p := by
  have e : ((C ++ u).drop p).take stateBits = (C.drop p).take stateBits := by
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  simp only [readSt, e]

theorem progOf_append {C : List Bool} (hC : C.length = predLen) (u : List Bool) :
    progOf (C ++ u) = progOf C := by
  unfold progOf
  congr 1
  · funext i z a
    apply readSt_append
    have hi := i.isLt
    have hu := (uOf z a).isLt
    simp only [stp_len, lutBits, stateBits] at hi hu ⊢
    rw [hC, predLen]
    have : 2 ^ 22 * i.val + (uOf z a).val + 1 ≤ 2 ^ 22 * 15 := by omega
    omega
  · funext z a
    have hu := (uOf z a).isLt
    simp only [lutBits, stateBits] at hu
    rw [List.getD_append _ _ _ _ (by rw [hC, predLen]; omega)]

variable (D : Dims)

/-! ### The slabs and their packets -/

/-- **The slabs, in order**: the `Ā` slabs `inl w`, then the `η` slabs `inr ρ` (`Enum` order). -/
def seRestL : List (Rest (Wb D) (Jh D) (setting D).τ) :=
  (List.finRange D.mb).map Sum.inl ++ (Enum.list (α := Jh D × (Fin 2 × Fin D.K))).map Sum.inr

theorem length_enumB : (Enum.list (α := Jh D × (Fin 2 × Fin D.K))).length = D.b * (2 * (2 * D.K)) := by
  rw [Enum.length_prod, Enum.length_prod, len_fin, len_fin, length_enum_col]
  ring

theorem length_seRestL : (seRestL D).length = D.mb + D.b * (2 * (2 * D.K)) := by
  simp [seRestL, length_enumB]

/-- **The packet of the slab `r`** (`F = bpOf (progOf C)`). -/
noncomputable def sePkOf (mpk : MPKt D) (C : List Bool) (ct : CTt D) (x : Pos → ℕ)
    (P : Prog (setting D) (Wb D) (Jh D) Pos) (r : Rest (Wb D) (Jh D) (setting D).τ) : List (Rg D) :=
  sePacket (seBitsOf D (evalPub (helperMap D) mpk).aut (evalData (helperMap D) mpk ct).aut
      (seHrOf D P r) (seCrOf D P r) (seRhoOf D P r)) D.b (seSlabL D (slabβ (setting D).row0 P.R0 r))
    (fun a c => mpk.A0 a c) (AinK D mpk)
    (fun i a c => (evalData (helperMap D) mpk ct).Cin ((bpOf (progOf C)).read i) a c)
    (fun i => (setting D).E.X ^ (bpOf (progOf C)).state x i)
    (fun i => (setting D).E.X ^ ((bpOf (progOf C)).state x i +
      (bpOf (progOf C)).w * x ((bpOf (progOf C)).read i)))
    (fun i c => seZvOf D P r ((bpOf (progOf C)).read i) c)
    (fun i d _ c => seRvOf D P r ((bpOf (progOf C)).read i) d c)

/-- **The input contract of `simKeyC`.** -/
structure SimKeyIn (mpk : MPKt D) (C : List Bool) (ct : CTt D) (x : Pos → ℕ)
    (P : Prog (setting D) (Wb D) (Jh D) Pos) (Cf : List Bool) (w : St) : Prop where
  cst : SeConst w (gD D) D.b (2 ^ D.b) tlK (xInvG (ZMod (2 ^ D.K - 1)) D.N) (xcK D)
  S : w rAinS = encL D.N D.K ((seRestL D).flatMap (sePkOf D mpk C ct x P))
  Cs : w rCs = Cf
  blocks : ∀ k < (seRestL D).length, ∃ u, Cf.drop (tlK * 16 * k) = C ++ u
  tail : (Cf.drop (tlK * 16 * (seRestL D).length)).length = D.mb
  loop : (w seLoopC).length = (seRestL D).length
  valid : ValidC C

/-- **`R̂_F` into `rxRh`.** -/
def simKeyC : Code := .seq seLoopKC (sePostMC D.mb)

/-- The zero per-bit data (for the indices past the slabs). -/
def seBits0 : SeBits D.N D.K := ⟨0, 0, 0, 0, 0, 0⟩

theorem flatMap_range_congr {α : Type*} {f g : ℕ → List α} :
    ∀ {n : ℕ}, (∀ k < n, f k = g k) → (List.range n).flatMap f = (List.range n).flatMap g
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append,
      flatMap_range_congr (fun k hk => h k (by omega))]
    simp [h n (by omega)]

theorem seRows_seSlabL (s : Slab (setting D)) :
    seRows (seSlabL D s) = (List.range (2 ^ D.b)).flatMap fun i =>
      if h : i < 2 ^ D.b then vecL (s ⟨i, h⟩) else vecL 0 := by
  rw [seRows, seSlabL, List.flatMap_map]
  refine (flatMap_range_getElem (List.finRange (setting D).E.W) _
    (fun i => if h : i < 2 ^ D.b then vecL (s ⟨i, h⟩) else vecL 0) (fun m hm => ?_)).trans ?_
  · have hm' : m < 2 ^ D.b := by simpa using hm
    simp only [hm', ↓reduceDIte, List.getElem_finRange]
    rfl
  · rw [List.length_finRange]; rfl

/-- **`simKeyC` computes `R̂_F = simKey …` into `rxRh`** (row-major, module 5's input). -/
theorem exec_simKeyC (hb : D.b = 22) (hbK : D.b < D.K) (mpk : MPKt D) (C : List Bool) (ct : CTt D)
    (x : Pos → ℕ) (P : Prog (setting D) (Wb D) (Jh D) Pos) (Cf : List Bool) (w : St)
    (hin : SimKeyIn D mpk C ct x P Cf w) :
    exec D.N D.K (simKeyC D) w rxRh = encL D.N D.K (rowsWord (α := LColS D) (β := Fin 2 × Fin D.K)
      (fun ℓ c => simKey (helperMap D) mpk (bpOf (progOf C)) ct x P ℓ c)) := by
  set Lr := seRestL D with hLr'
  have hK : 0 < D.K := by omega
  have hn : 2 ^ D.b ≤ 2 ^ D.K - 1 := by
    have : 2 ^ D.b < 2 ^ D.K := Nat.pow_lt_pow_right (by norm_num) hbK
    omega
  -- the per-slab data, by index
  let rk : ℕ → Option (Rest (Wb D) (Jh D) (setting D).τ) := fun k => Lr[k]?
  let Dk : ℕ → SeBits D.N D.K := fun k => (rk k).elim (seBits0 D) fun r =>
    seBitsOf D (evalPub (helperMap D) mpk).aut (evalData (helperMap D) mpk ct).aut
      (seHrOf D P r) (seCrOf D P r) (seRhoOf D P r)
  let L0k : ℕ → List (Fin 2 × Fin D.K → Rq D.N D.K) := fun k =>
    (rk k).elim (List.replicate (2 ^ D.b) 0) fun r => seSlabL D (slabβ (setting D).row0 P.R0 r)
  let zk : ℕ → ℕ → Fin 2 × Fin D.K → Rq D.N D.K := fun k => (rk k).elim 0 fun r =>
    fun i c => seZvOf D P r ((bpOf (progOf C)).read i) c
  let rdk : ℕ → ℕ → DigI D.K → Fin 2 → Fin 2 × Fin D.K → Rq D.N D.K := fun k => (rk k).elim 0
    fun r => fun i d _ c => seRvOf D P r ((bpOf (progOf C)).read i) d c
  have hsome : ∀ k (h : k < Lr.length), rk k = some Lr[k] := fun k h => List.getElem?_eq_getElem h
  have hS : w rAinS = encL D.N D.K ((List.range Lr.length).flatMap fun k =>
      sePacket (Dk k) D.b (L0k k) (fun a c => mpk.A0 a c) (AinK D mpk)
        (fun i a c => (evalData (helperMap D) mpk ct).Cin ((bpOf (progOf C)).read i) a c)
        (fun i => (setting D).E.X ^ (bpOf (progOf C)).state x i)
        (fun i => (setting D).E.X ^ ((bpOf (progOf C)).state x i +
          (bpOf (progOf C)).w * x ((bpOf (progOf C)).read i))) (zk k) (rdk k)) := by
    rw [hin.S, flatMap_range_getElem Lr _ _ (fun m hm => ?_)]
    simp only [Dk, L0k, zk, rdk, hsome m hm, Option.elim_some]
    rfl
  have hL0 : ∀ k, (L0k k).length = 2 ^ D.b := by
    intro k
    simp only [L0k]
    cases rk k with
    | none => simp
    | some r => simp only [Option.elim_some]; exact length_seSlabL D _
  obtain ⟨l1, l2, l3⟩ := exec_seLoopKC D.N_pos hK w (gD D) D.b (2 ^ D.b) tlK (odd_gD D).pos
    (by omega) hn _ _ hin.cst Lr.length Dk L0k (fun a c => mpk.A0 a c) (AinK D mpk)
    (fun _ i a c => (evalData (helperMap D) mpk ct).Cin ((bpOf (progOf C)).read i) a c)
    (fun _ i => (setting D).E.X ^ (bpOf (progOf C)).state x i)
    (fun _ i => (setting D).E.X ^ ((bpOf (progOf C)).state x i +
      (bpOf (progOf C)).w * x ((bpOf (progOf C)).read i))) zk rdk Cf hL0 le_rfl
    (by positivity) hS hin.Cs hin.loop
  -- every output slab is a slab of `R̂_F`
  have hout : ∀ k (h : k < Lr.length),
      seRows (seEvalVM (seCvs (2 ^ D.b) D.b tlK (xcK D) (Cf.drop (tlK * 16 * k))) (gD D) (Dk k) D.b
        (xInvG (ZMod (2 ^ D.K - 1)) D.N) (2 ^ D.b) (AinK D mpk) (fun a c => mpk.A0 a c)
        (fun i a c => (evalData (helperMap D) mpk ct).Cin ((bpOf (progOf C)).read i) a c)
        (fun i => (setting D).E.X ^ (bpOf (progOf C)).state x i)
        (fun i => (setting D).E.X ^ ((bpOf (progOf C)).state x i +
          (bpOf (progOf C)).w * x ((bpOf (progOf C)).read i))) (zk k) (rdk k) (L0k k) 16) =
      seRows (seSlabL D (slab (simKey (helperMap D) mpk (bpOf (progOf C)) ct x P) Lr[k])) := by
    intro k h
    obtain ⟨u, hu⟩ := hin.blocks k h
    have e := seSlabL_simKey D P Lr[k] hb mpk (C ++ u) ct x
    rw [progOf_append hin.valid] at e
    rw [e, hu]
    simp only [Dk, L0k, zk, rdk, hsome k h, Option.elim_some]
    rfl
  have hLr : Lr.length = D.mb + D.b * (2 * (2 * D.K)) := length_seRestL D
  have hS2 : exec D.N D.K seLoopKC w rAinS = encL D.N D.K
      (((List.range D.mb).flatMap fun k => (List.range (2 ^ D.b)).flatMap
        (rowsInl D (fun ℓ c => simKey (helperMap D) mpk (bpOf (progOf C)) ct x P ℓ c) k)) ++
      ((List.range (D.b * (2 * (2 * D.K)))).flatMap fun k => (List.range (2 ^ D.b)).flatMap
        (rowsInr D (fun ℓ c => simKey (helperMap D) mpk (bpOf (progOf C)) ct x P ℓ c) k))) := by
    rw [l1, hLr, List.range_add, List.flatMap_append, List.flatMap_map]
    congr 2
    · refine flatMap_range_congr fun k hk => ?_
      have hk' : k < Lr.length := by omega
      rw [hout k hk']
      have e : Lr[k] = Sum.inl ⟨k, hk⟩ := by
        simp [hLr', seRestL, hk]
      rw [e, seRows_seSlabL]
      refine flatMap_range_congr fun i hi => ?_
      rw [rowsInl_slab D _ hi hk]
      simp [hi]
    · refine flatMap_range_congr fun k hk => ?_
      have hk2 : k < (Enum.list (α := Jh D × (Fin 2 × Fin D.K))).length := by
        rw [length_enumB]; exact hk
      rw [hout (D.mb + k) (by omega)]
      have e : Lr[D.mb + k] = Sum.inr (Enum.list (α := Jh D × (Fin 2 × Fin D.K)))[k] := by
        simp [hLr', seRestL]
      rw [e, seRows_seSlabL]
      refine flatMap_range_congr fun i hi => ?_
      rw [rowsInr_slab D _ hi hk2]
      simp [hi]
  have hP := exec_sePostMC (exec D.N D.K seLoopKC w) (2 ^ D.b) D.mb D.b _ _
    (length_rowsInl D _) (length_rowsInr D _) hS2
    (by rw [l3 _ (by decide)]; exact hin.cst.tw)
    (by rw [l3 _ (by decide)]; exact hin.cst.bit1)
    (by rw [l3 _ (by decide), hin.cst.tb, List.length_replicate])
    (hin.cst.tm.of_writes fun q hq => l3 q (by simp [seConstR]; omega))
  unfold simKeyC
  rw [exec_seq, hP, rowsWord_trans, length_enumB]
  rfl

/-! ### Composition with module 5 -/

/-- **The contract of the set-up code between `simKeyC` and `simXC`** (on the state `w1` after
`simKeyC`): it establishes module 5's inputs (`XIn`: the helper queue `rxH`, the templates; `rxTs`,
`rxOne`) and keeps `rxRh`. (After `simKeyC` only the constants `SeConst`, `rxRh` and the tail of
`rCs` survive; module 8 provides `setX`, e.g. by carrying the helper queue in the tail of `rCs`.) -/
structure SetXOk (setX : Code) (mpk : MPKt D) (w1 : St) : Prop where
  xin : XIn (gD D) D.b (xHs D mpk) (xHi D mpk) (exec D.N D.K setX w1)
  rh : exec D.N D.K setX w1 rxRh = w1 rxRh
  ts : (exec D.N D.K setX w1 rxTs).length = 2 ^ D.b * D.mb
  one : exec D.N D.K setX w1 rxOne = encRM D.N D.K 1

/-- **`R̂_F`, then `X`**: `simKeyC ; setX ; simXC` leaves the rows of
`X = simX (helperMap D) (h1Of mpk) A_F R̂_F` (`R̂_F = simKey (helperMap D) mpk (bpOf (progOf C)) ct x
P`) in register `16` — exactly `SimTryReady.rows` of module 4. -/
theorem exec_simKeyXC (hb : D.b = 22) (hbK : D.b < D.K) (mpk : MPKt D) (C : List Bool) (ct : CTt D)
    (x : Pos → ℕ) (P : Prog (setting D) (Wb D) (Jh D) Pos) (Cf : List Bool) (w : St)
    (hin : SimKeyIn D mpk C ct x P Cf w) (setX : Code)
    (hX : SetXOk D setX mpk (exec D.N D.K (simKeyC D) w))
    (AF : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    exec D.N D.K (.seq (simKeyC D) (.seq setX simXC)) w 16 = encL D.N D.K
      (rowsWord (α := PIdxS D) (β := ZIdxS D) (simX (helperMap D) (h1Of mpk) AF
        (simKey (helperMap D) mpk (bpOf (progOf C)) ct x P))) := by
  simp only [exec_seq]
  exact (exec_simXC D mpk AF _ _ hX.xin
    (by rw [hX.rh]; exact exec_simKeyC D hb hbK mpk C ct x P Cf w hin) hX.ts hX.one).1

/-- `simKeyC` is well formed (every `rep` body leaves its counter alone). -/
theorem wf_sePostC : sePostC.WFc := by
  unfold sePostC seSplitC sePopsC sePopC seRtC seNBC transC
  repeat constructor

theorem wf_seLoopKC : seLoopKC.WFc := by
  unfold seLoopKC seSlabC seLoadC seEvalC2 sePopsC sePopC
  repeat constructor

theorem wf_simKeyC : (simKeyC D).WFc := ⟨wf_seLoopKC, wf_sePostMC _ wf_sePostC⟩

end AdvancedEncryption.ExpLUT.Prog
