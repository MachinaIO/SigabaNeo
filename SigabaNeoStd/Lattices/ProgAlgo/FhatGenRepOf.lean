import SigabaNeoStd.Lattices.ProgAlgo.FhatGenBlock
import SigabaNeoStd.Machines.GatesSLP

/-!
# Generating gate tapes: the representations of the source wires

`oLoop body`: a nand-free body run once per output position `o` of `enumO` (in the registers
`43 … 46`, odometer `odoO`), each appending a chunk `f o` to a list (`iter_oLoop`). Instances:
the representation of an input (`inRepC`) and of the constant `1` (`constRepC`).
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-- The registers `43 … 46` hold the output position `o`. -/
def ODig {N k : ℕ} (o : OI N k) (σ : St) : Prop :=
  σ.sc 43 = o.1.val ∧ σ.sc 44 = o.2.1.1.val ∧ σ.sc 45 = o.2.1.2.val ∧ σ.sc 46 = o.2.2.val

/-- The loop over the output positions. -/
def oLoop (body : Code) : Code := .rep 12 (.seq body odoO)

theorem iter_oLoop {N k : ℕ} (hk : 0 < k) (hN : 0 < N) {body : Code} {tgt : LR}
    {f : OI N k → List ℕ} {Q : St → Prop} (hf : ∀ o, (f o).length = k)
    (hQ : ∀ σ : St, Q σ → σ.sc 2 = k ∧ σ.sc 5 = N ∧ σ.sc 6 = 2)
    (hQo : ∀ (σ : St) (a b c d : ℕ), Q σ → Q (setSL σ (Function.update (Function.update
      (Function.update (Function.update σ.sc 43 a) 44 b) 45 c) 46 d) σ.ls))
    (hB : ∀ (σ : St) (o : OI N k), Q σ → ODig o σ → (σ.ls tgt).length + k ≤ E.C →
      Q (exec E body σ) ∧ ODig o (exec E body σ) ∧
        (exec E body σ).ls tgt = σ.ls tgt ++ f o)
    (hM : 4 * k * N + 2 ≤ E.M) (hkM : k ≤ E.M) (hNM : N ≤ E.M) :
    ∀ (i : ℕ) (σ : St) (L0 : List ℕ), i ≤ 4 * k * N → Q σ → σ.sc 43 = 0 → σ.sc 44 = 0 →
      σ.sc 45 = 0 → σ.sc 46 = 0 → σ.ls tgt = L0 → L0.length + 4 * k * N * k ≤ E.C →
      Q ((exec E (.seq body odoO))^[i] σ) ∧
        ((exec E (.seq body odoO))^[i] σ).ls tgt =
          L0 ++ (((enumO N k).take i).map f).flatten ∧
        ∃ a c1 c2 t, ((exec E (.seq body odoO))^[i] σ).sc 43 = a ∧
          ((exec E (.seq body odoO))^[i] σ).sc 44 = c1 ∧
          ((exec E (.seq body odoO))^[i] σ).sc 45 = c2 ∧
          ((exec E (.seq body odoO))^[i] σ).sc 46 = t ∧
          ((a * 2 + c1) * k + c2) * N + t = i ∧ c1 < 2 ∧ c2 < k ∧ t < N
  | 0, σ, L0, _, hq, h43, h44, h45, h46, hL, _ =>
    ⟨hq, by simp [hL], 0, 0, 0, 0, h43, h44, h45, h46, by ring, by omega, hk, hN⟩
  | i + 1, σ, L0, hi, hq, h43, h44, h45, h46, hL, hcap => by
    obtain ⟨hq1, hl1, a, c1, c2, t, h43', h44', h45', h46', hidx, hc1, hc2, ht⟩ :=
      iter_oLoop hk hN hf hQ hQo hB hM hkM hNM i σ L0 (by omega) hq h43 h44 h45 h46 hL hcap
    rw [Function.iterate_succ_apply']
    set τ := (exec E (.seq body odoO))^[i] σ
    have ha : a < 2 := by
      by_contra h
      have : 4 * k * N ≤ ((a * 2 + c1) * k + c2) * N + t := by nlinarith
      omega
    set o : OI N k := (⟨a, ha⟩, (⟨c1, hc1⟩, ⟨c2, hc2⟩), ⟨t, ht⟩)
    have ho : (enumO N k)[i]? = some o := by rw [← hidx]; exact enumO_getElem? o
    have hlen : (((enumO N k).take i).map f).flatten.length = i * k := by
      rw [length_flatten_of' (V := k) _ (fun w hw => by
        obtain ⟨o', _, rfl⟩ := List.mem_map.mp hw; exact hf o')]
      simp [List.length_take, length_enumO']; left; omega
    obtain ⟨hq2, ⟨d43, d44, d45, d46⟩, hl2⟩ := hB τ o hq1 ⟨h43', h44', h45', h46'⟩
      (by rw [hl1, List.length_append, hlen]; nlinarith)
    obtain ⟨hk2, hN2, h62⟩ := hQ _ hq2
    obtain ⟨a', c1', c2', t', h4, hidx', hc1', hc2', ht'⟩ := exec_odoO (E := E) (exec E body τ)
      a c1 c2 t hk2 hN2 h62 d43 d44 d45 d46 hc1 hc2 ht (by omega) hkM hNM (by omega)
    rw [exec_seq, h4]
    refine ⟨hQo _ _ _ _ _ hq2, ?_, a', c1', c2', t', by simp [setSL, Function.update_apply],
      by simp [setSL, Function.update_apply], by simp [setSL, Function.update_apply],
      by simp [setSL, Function.update_apply], by omega, hc1', hc2', ht'⟩
    simp only [setSL]
    rw [hl2, hl1, List.take_succ, ho, Option.toList_some, List.map_append, List.flatten_append,
      List.append_assoc]
    simp

/-! ### The representation of an input -/

/-- The codec index of a bit `(a, (c1, c2), i, j)` of a ciphertext: `a`, then the column, the bit,
the coefficient. -/
def codec {N k : ℕ} (b : BI N k) : ℕ :=
  (((b.1.val * 2 + b.2.1.1.val) * k + b.2.1.2.val) * k + b.2.2.1.val) * N + b.2.2.2.val

/-- `62 := base (61) + codec (a, (c1, c2), i (42), t)`. -/
def valC : Code :=
  .seq (.mov 62 43) (.seq (maddC 62 6 44 53) (.seq (maddC 62 2 45 53) (.seq (maddC 62 2 42 53)
    (.seq (maddC 62 5 46 53) (.add 62 61)))))

/-- One output position of an input: its `k` bits. -/
def inBody (tgt : LR) : Code :=
  .seq (.zero 42) (.rep 2 (.seq valC (.seq (.lpush tgt 62) (.inc 42))))

theorem codec_lt {N k : ℕ} (b : BI N k) : codec b < 4 * k * N * k := by
  obtain ⟨a, ⟨c1, c2⟩, i, j⟩ := b
  have := a.isLt; have := c1.isLt; have := c2.isLt; have := i.isLt; have := j.isLt
  simp only [codec]
  have mx : ∀ {x m y n : ℕ}, x < m → y < n → x * n + y < m * n := by
    intro x m y n hx hy
    calc x * n + y < x * n + n := by omega
      _ = (x + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right _ hx
  have h1 : a.val * 2 + c1.val < 4 := by omega
  have h2 := mx (mx (mx h1 c2.isLt) i.isLt) j.isLt
  calc _ < 4 * k * k * N := h2
    _ = 4 * k * N * k := by ring

theorem exec_valC {N k : ℕ} (σ : St) (o : OI N k) (i : Fin k) (base : ℕ) (hd : ODig o σ)
    (h2 : σ.sc 2 = k) (h5 : σ.sc 5 = N) (h6 : σ.sc 6 = 2) (h42 : σ.sc 42 = i.val)
    (h61 : σ.sc 61 = base) (hM : base + 4 * k * N * k ≤ E.M) :
    ∃ sc', exec E valC σ = setSL σ sc' σ.ls ∧
      sc' 62 = base + codec ((o.1, o.2.1, i, o.2.2) : BI N k) ∧
      ∀ r : SR, r ≠ 53 → r ≠ 62 → sc' r = σ.sc r := by
  obtain ⟨h43, h44, h45, h46⟩ := hd
  obtain ⟨a, ⟨c1, c2⟩, t⟩ := o
  simp only at h43 h44 h45 h46 ⊢
  have hc := codec_lt ((a, (c1, c2), i, t) : BI N k)
  simp only [codec] at hc ⊢
  have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by subst h; exact c2.elim0)
  have hN : 0 < N := Nat.pos_of_ne_zero (fun h => by subst h; exact t.elim0)
  have hx1 : a.val * 2 + c1.val ≤ (a.val * 2 + c1.val) * k + c2.val :=
    le_trans (Nat.le_mul_of_pos_right _ hk) (Nat.le_add_right _ _)
  have hx2 : (a.val * 2 + c1.val) * k + c2.val ≤ ((a.val * 2 + c1.val) * k + c2.val) * k + i.val :=
    le_trans (Nat.le_mul_of_pos_right _ hk) (Nat.le_add_right _ _)
  have hx3 : ((a.val * 2 + c1.val) * k + c2.val) * k + i.val ≤
      (((a.val * 2 + c1.val) * k + c2.val) * k + i.val) * N + t.val :=
    le_trans (Nat.le_mul_of_pos_right _ hN) (Nat.le_add_right _ _)
  simp only [valC, exec_seq]
  rw [show exec E (.mov 62 43) σ = setSL σ (Function.update σ.sc 62 a.val) σ.ls by
    simp [exec, setSL, h43]]
  rw [exec_maddC 62 6 44 53 (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [setSL, Function.update_apply, h6, h44]; omega)]
  rw [exec_maddC 62 2 45 53 (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [setSL, Function.update_apply, h6, h44, h2, h45]; omega)]
  rw [exec_maddC 62 2 42 53 (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [setSL, Function.update_apply, h6, h44, h2, h45, h42]; omega)]
  rw [exec_maddC 62 5 46 53 (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [setSL, Function.update_apply, h6, h44, h2, h45, h42, h5, h46]; omega)]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [exec, setSL, Function.update_apply, h6, h44, h2, h45, h42, h5, h46, h61]
    rw [min_eq_left (by omega)]; ring
  · intro r h53 h62
    simp [exec, setSL, Function.update_apply, h53, h62]

/-- The codec index with the bit as a natural. -/
def codecN {N k : ℕ} (o : OI N k) (i : ℕ) : ℕ :=
  (((o.1.val * 2 + o.2.1.1.val) * k + o.2.1.2.val) * k + i) * N + o.2.2.val

/-- The registers an input-representation body relies on. -/
def InQ (N k base : ℕ) (σ : St) : Prop :=
  σ.sc 2 = k ∧ σ.sc 5 = N ∧ σ.sc 6 = 2 ∧ σ.sc 61 = base

theorem iter_inner {N k : ℕ} (tgt : LR) (o : OI N k) (base : ℕ)
    (hM : base + 4 * k * N * k ≤ E.M) (hkM : k ≤ E.M) :
    ∀ (j i0 : ℕ) (σ : St), i0 + j ≤ k → InQ N k base σ → ODig o σ → σ.sc 42 = i0 →
      (σ.ls tgt).length + j ≤ E.C →
      ∃ sc', (exec E (.seq valC (.seq (.lpush tgt 62) (.inc 42))))^[j] σ =
          setSL σ sc' (Function.update σ.ls tgt (σ.ls tgt ++
            (List.range j).map fun x => base + codecN o (i0 + x))) ∧
        ∀ r : SR, r ≠ 42 → r ≠ 53 → r ≠ 62 → sc' r = σ.sc r
  | 0, i0, σ, _, _, _, _, _ => ⟨σ.sc, by simp [setSL], fun _ _ _ _ => rfl⟩
  | j + 1, i0, σ, hj, hq, hd, h42, hC => by
    rw [Function.iterate_succ_apply, exec_seq]
    have hi0 : i0 < k := by omega
    obtain ⟨sc1, e1, d1, f1⟩ := exec_valC (E := E) σ o ⟨i0, hi0⟩ base hd hq.1 hq.2.1 hq.2.2.1 h42
      hq.2.2.2 hM
    rw [e1, exec_seq]
    have hv : base + codec ((o.1, o.2.1, ⟨i0, hi0⟩, o.2.2) : BI N k) ≤ E.M := by
      have := codec_lt ((o.1, o.2.1, ⟨i0, hi0⟩, o.2.2) : BI N k); omega
    set σ2 : St := setSL σ (Function.update sc1 42 (i0 + 1)) (Function.update σ.ls tgt
      (σ.ls tgt ++ [base + codecN o i0]))
    have e2 : exec E (.inc 42) (exec E (.lpush tgt 62) (setSL σ sc1 σ.ls)) = σ2 := by
      rw [exec_lpush_lt (setSL σ sc1 σ.ls) tgt 62 (by simp [setSL]; omega)
        (by simp [setSL, d1]; exact hv)]
      simp only [exec, setSL, σ2, d1, f1 42 (by decide) (by decide), h42,
        min_eq_left (show i0 + 1 ≤ E.M by omega)]
      rfl
    rw [e2]
    have hfr : ∀ r : SR, r ≠ 42 → r ≠ 53 → r ≠ 62 → σ2.sc r = σ.sc r := fun r a b c => by
      simp [σ2, setSL, Function.update_of_ne a, f1 r b c]
    obtain ⟨sc', e', f'⟩ := iter_inner tgt o base hM hkM j (i0 + 1) σ2 (by omega)
      ⟨by rw [hfr 2 (by decide) (by decide) (by decide), hq.1],
        by rw [hfr 5 (by decide) (by decide) (by decide), hq.2.1],
        by rw [hfr 6 (by decide) (by decide) (by decide), hq.2.2.1],
        by rw [hfr 61 (by decide) (by decide) (by decide), hq.2.2.2]⟩
      ⟨by rw [hfr 43 (by decide) (by decide) (by decide), hd.1],
        by rw [hfr 44 (by decide) (by decide) (by decide), hd.2.1],
        by rw [hfr 45 (by decide) (by decide) (by decide), hd.2.2.1],
        by rw [hfr 46 (by decide) (by decide) (by decide), hd.2.2.2]⟩
      (by simp [σ2, setSL]) (by simp [σ2, setSL]; omega)
    refine ⟨sc', ?_, fun r a b c => (f' r a b c).trans (hfr r a b c)⟩
    rw [e']
    simp only [σ2, setSL, Function.update_idem, Function.update_self, List.append_assoc]
    congr 3
    rw [List.range_succ_eq_map]
    simp [codecN, codec, Nat.add_comm, Nat.add_left_comm]

theorem exec_inBody {N k : ℕ} (tgt : LR) (o : OI N k) (base : ℕ) (σ : St)
    (hM : base + 4 * k * N * k ≤ E.M) (hkM : k ≤ E.M) (hq : InQ N k base σ) (hd : ODig o σ)
    (hC : (σ.ls tgt).length + k ≤ E.C) :
    InQ N k base (exec E (inBody tgt) σ) ∧ ODig o (exec E (inBody tgt) σ) ∧
      (exec E (inBody tgt) σ).ls tgt = σ.ls tgt ++ (List.range k).map (fun x => base + codecN o x) ∧
      (∀ r : SR, r ≠ 42 → r ≠ 53 → r ≠ 62 → (exec E (inBody tgt) σ).sc r = σ.sc r) ∧
      ∀ l : LR, l ≠ tgt → (exec E (inBody tgt) σ).ls l = σ.ls l := by
  set σ0 := setSL σ (Function.update σ.sc 42 0) σ.ls
  have e0 : exec E (.zero 42) σ = σ0 := rfl
  have hs0 : ∀ r : SR, r ≠ 42 → σ0.sc r = σ.sc r := fun r h => by
    simp [σ0, setSL, Function.update_of_ne h]
  obtain ⟨sc', e', f'⟩ := iter_inner (E := E) tgt o base hM hkM k 0 σ0 (by omega)
    ⟨by rw [hs0 2 (by decide), hq.1], by rw [hs0 5 (by decide), hq.2.1],
      by rw [hs0 6 (by decide), hq.2.2.1], by rw [hs0 61 (by decide), hq.2.2.2]⟩
    ⟨by rw [hs0 43 (by decide), hd.1], by rw [hs0 44 (by decide), hd.2.1],
      by rw [hs0 45 (by decide), hd.2.2.1], by rw [hs0 46 (by decide), hd.2.2.2]⟩
    (by simp [σ0, setSL]) (by simp [σ0, setSL]; exact hC)
  have hrun : exec E (inBody tgt) σ = setSL σ0 sc' (Function.update σ0.ls tgt (σ0.ls tgt ++
      (List.range k).map fun x => base + codecN o (0 + x))) := by
    rw [inBody, exec_seq, e0, exec_rep, show σ0.sc 2 = k by rw [hs0 2 (by decide), hq.1], e']
  have g : ∀ r : SR, r ≠ 42 → r ≠ 53 → r ≠ 62 → (exec E (inBody tgt) σ).sc r = σ.sc r :=
    fun r a b c => by rw [hrun]; simp only [setSL]; rw [f' r a b c, hs0 r a]
  refine ⟨⟨by rw [g 2 (by decide) (by decide) (by decide), hq.1],
    by rw [g 5 (by decide) (by decide) (by decide), hq.2.1],
    by rw [g 6 (by decide) (by decide) (by decide), hq.2.2.1],
    by rw [g 61 (by decide) (by decide) (by decide), hq.2.2.2]⟩,
    ⟨by rw [g 43 (by decide) (by decide) (by decide), hd.1],
    by rw [g 44 (by decide) (by decide) (by decide), hd.2.1],
    by rw [g 45 (by decide) (by decide) (by decide), hd.2.2.1],
    by rw [g 46 (by decide) (by decide) (by decide), hd.2.2.2]⟩, ?_, g, fun l hl => ?_⟩
  · rw [hrun]; simp [σ0, setSL]
  · rw [hrun]; simp [σ0, setSL, Function.update_of_ne hl]

/-- **The representation of an input** (base `ix (i, 0)` in `61`) into `tgt`. -/
def inRepC (tgt : LR) : Code :=
  .seq (.seq (.zero 43) (.seq (.zero 44) (.seq (.zero 45) (.seq (.zero 46) (.lnil tgt)))))
    (oLoop (inBody tgt))

theorem exec_inRepC {A : Type*} {N k : ℕ} (hk : 0 < k) (hN : 0 < N)
    (ix' : A × BI N k → ℕ) (i : A) (base : ℕ) (hix : ∀ b, ix' (i, b) = base + codec b)
    (tgt : LR) (σ : St) (hq : InQ N k base σ) (h12 : σ.sc 12 = 4 * k * N)
    (hM : base + 4 * k * N * k + 4 * k * N + 2 ≤ E.M) (hC : 4 * k * N * k ≤ E.C) :
    InQ N k base (exec E (inRepC tgt) σ) ∧
      (exec E (inRepC tgt) σ).ls tgt = repList E ix' (fun b => Wire.input (i, b)) ∧
      (∀ r : SR, r.val < 42 ∨ (46 < r.val ∧ r.val ≠ 53 ∧ r.val ≠ 62) →
        (exec E (inRepC tgt) σ).sc r = σ.sc r) ∧
      ∀ l : LR, l ≠ tgt → (exec E (inRepC tgt) σ).ls l = σ.ls l := by
  have hkM : k ≤ E.M := by nlinarith
  have hNM : N ≤ E.M := by nlinarith
  set σ0 := setSL σ (Function.update (Function.update (Function.update (Function.update σ.sc 43 0)
    44 0) 45 0) 46 0) (Function.update σ.ls tgt [])
  have e0 : exec E (.seq (.zero 43) (.seq (.zero 44) (.seq (.zero 45) (.seq (.zero 46)
      (.lnil tgt))))) σ = σ0 := rfl
  have hs0 : ∀ r : SR, r.val < 43 ∨ 46 < r.val → σ0.sc r = σ.sc r := fun r hr => by
    simp only [σ0, setSL]
    rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide)]
  let Q : St → Prop := fun τ => InQ N k base τ ∧
    (∀ r : SR, r.val < 42 ∨ (46 < r.val ∧ r.val ≠ 53 ∧ r.val ≠ 62) → τ.sc r = σ.sc r) ∧
    ∀ l : LR, l ≠ tgt → τ.ls l = σ.ls l
  have hQ0 : Q σ0 := ⟨⟨by rw [hs0 2 (by decide), hq.1], by rw [hs0 5 (by decide), hq.2.1],
      by rw [hs0 6 (by decide), hq.2.2.1], by rw [hs0 61 (by decide), hq.2.2.2]⟩,
    fun r hr => hs0 r (by omega), fun l hl => by simp [σ0, setSL, Function.update_of_ne hl]⟩
  have hf : ∀ o : OI N k, ((List.range k).map fun x => base + codecN o x).length = k :=
    fun o => by simp
  have it := iter_oLoop (E := E) (tgt := tgt) (f := fun o => (List.range k).map
      fun x => base + codecN o x) (Q := Q) hk hN hf (fun τ h => ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩)
    (fun τ a b c d h => ⟨⟨by simp [setSL, h.1.1], by simp [setSL, h.1.2.1],
      by simp [setSL, h.1.2.2.1], by simp [setSL, h.1.2.2.2]⟩,
      fun r hr => by
        simp only [setSL]
        rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide)]
        exact h.2.1 r hr, fun l hl => h.2.2 l hl⟩)
    (fun τ o h hd hC' => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := exec_inBody (E := E) tgt o base τ (by omega) hkM h.1 hd hC'
      exact ⟨⟨a1, fun r hr => by
          rw [a4 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
            (by rintro rfl; revert hr; decide)]; exact h.2.1 r hr,
        fun l hl => by rw [a5 l hl]; exact h.2.2 l hl⟩, a2, a3⟩)
    (by omega) hkM hNM (4 * k * N) σ0 [] le_rfl hQ0 (by simp [σ0, setSL])
    (by simp [σ0, setSL]) (by simp [σ0, setSL]) (by simp [σ0, setSL]) (by simp [σ0, setSL])
    (by simpa using hC)
  have hrun : exec E (inRepC tgt) σ = (exec E (.seq (inBody tgt) odoO))^[4 * k * N] σ0 := by
    rw [inRepC, exec_seq, e0, oLoop, exec_rep, hs0 12 (by decide), h12]
  obtain ⟨hQ, hL, -⟩ := it
  rw [hrun]
  refine ⟨hQ.1, ?_, hQ.2.1, hQ.2.2⟩
  rw [hL, List.nil_append, List.take_of_length_le (by rw [length_enumO']), repList]
  congr 1
  apply List.map_congr_left; intro o _
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [pos, hix, codec, codecN]

/-! ### The representation of `1` -/

/-- One output position of the constant `1`: its gadget coefficient bits. -/
def cBody (tgt : LR) : Code := .seq (constC 2 12 (gvBody 12)) (takeC 2 12 tgt)

/-- The registers the constant representation relies on. -/
def CQ (k K N : ℕ) (σ : St) : Prop :=
  Cst (E := E) k K σ ∧ σ.sc 5 = N ∧ σ.sc 6 = 2 ∧ σ.sc 7 = 0

theorem exec_cBody (hnM : E.n + 1 ≤ E.M) {N k K : ℕ} (tgt : LR) (htgt : tgt ≠ 12) (o : OI N k)
    (σ : St) (hkM : k ≤ E.M) (hq : CQ (E := E) k K N σ) (hd : ODig o σ)
    (hI : Inv E σ) (hC : (σ.ls tgt).length + k ≤ E.C) :
    CQ (E := E) k K N (exec E (cBody tgt) σ) ∧ ODig o (exec E (cBody tgt) σ) ∧
      (exec E (cBody tgt) σ).ls tgt =
        σ.ls tgt ++ (constL (.gate 0 : Wire ι) k (gvExp (2 ^ K) o)).map (pos E ix) ∧
      (∀ r : SR, r ≠ 41 → r ≠ 42 → (exec E (cBody tgt) σ).sc r = σ.sc r) ∧
      ∀ l : LR, l ≠ tgt → l ≠ 12 → (exec E (cBody tgt) σ).ls l = σ.ls l := by
  obtain ⟨⟨⟨h0, h1⟩, h2, h3, h4⟩, h5, h6, h7⟩ := hq
  obtain ⟨h43, h44, h45, h46⟩ := hd
  have hQ : ∀ τ : St, OReg (E := E) k K o.1.val o.2.1.1.val o.2.1.2.val o.2.2.val τ → ∀ v ls',
      OReg (E := E) k K o.1.val o.2.1.1.val o.2.1.2.val o.2.2.val
        (setSL τ (Function.update τ.sc 42 v) ls') := by
    intro τ ⟨⟨⟨a0, a1⟩, a2, a3, a4⟩, a7, a43, a44, a45, a46⟩ v ls'
    simp only [setSL]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
      (rw [Function.update_of_ne (by decide)]; assumption)
  have h1' := exec_constC (E := E) (cnt := 2) (l := 12)
    (Q := OReg (E := E) k K o.1.val o.2.1.1.val o.2.1.2.val o.2.2.val) (by decide) hQ
    (fun τ i hq hi hl => exec_gvBody hnM 12 τ i hq hi hl) σ
    ⟨⟨⟨h0, h1⟩, h2, h3, h4⟩, h7, h43, h44, h45, h46⟩ (by rw [h2]; exact hkM) (by rw [h2]; omega)
  rw [h2, ← map_pos_constL_gv (ix := ix) o] at h1'
  set G := (constL (.gate 0 : Wire ι) k (gvExp (2 ^ K) o)).map (pos E ix)
  have hG : G.length = k := by simp [G, constL_length]
  set σ1 := setSL σ (Function.update σ.sc 42 k) (Function.update σ.ls 12 G)
  have hI1 : Inv E σ1 := by
    have := inv_exec E (constC 2 12 (gvBody 12)) σ hI; rw [h1'] at this; exact this
  obtain ⟨sc2, h2', f2⟩ := exec_takeC (E := E) (n := 2) (lA := 12) (lR := tgt) (Ne.symm htgt)
    G [] (σ.ls tgt) σ1 hI1 (by simp [σ1, setSL]) (by simp [σ1, setSL, htgt])
    (by simp [σ1, setSL, h2, hG]) (by rw [hG]; exact hC)
  have hrun : exec E (cBody tgt) σ = setSL σ sc2
      (Function.update (Function.update σ1.ls 12 []) tgt (σ.ls tgt ++ G)) := by
    rw [cBody, exec_seq, h1', h2']; rfl
  have g : ∀ r : SR, r ≠ 41 → r ≠ 42 → (exec E (cBody tgt) σ).sc r = σ.sc r := fun r a b => by
    rw [hrun]; simp only [setSL]; rw [f2 r (by simpa using a)]
    simp [σ1, setSL, Function.update_of_ne b]
  refine ⟨⟨⟨⟨by rw [g 0 (by decide) (by decide), h0], by rw [g 1 (by decide) (by decide), h1]⟩,
    by rw [g 2 (by decide) (by decide), h2], by rw [g 3 (by decide) (by decide), h3],
    by rw [g 4 (by decide) (by decide), h4]⟩, by rw [g 5 (by decide) (by decide), h5],
    by rw [g 6 (by decide) (by decide), h6], by rw [g 7 (by decide) (by decide), h7]⟩,
    ⟨by rw [g 43 (by decide) (by decide), h43], by rw [g 44 (by decide) (by decide), h44],
    by rw [g 45 (by decide) (by decide), h45], by rw [g 46 (by decide) (by decide), h46]⟩,
    by rw [hrun]; simp [setSL], g, fun l a b => ?_⟩
  rw [hrun]; simp [σ1, setSL, Function.update_of_ne a, Function.update_of_ne b]

/-- **The representation of the constant `1`** into `tgt`. -/
def constRepC (tgt : LR) : Code :=
  .seq (.seq (.zero 43) (.seq (.zero 44) (.seq (.zero 45) (.seq (.zero 46) (.lnil tgt)))))
    (oLoop (cBody tgt))

theorem exec_constRepC (hnM : E.n + 1 ≤ E.M) {N k K : ℕ} (hk : 0 < k) (hN : 0 < N) (tgt : LR)
    (htgt : tgt ≠ 12) (σ : St) (hq : CQ (E := E) k K N σ) (h12 : σ.sc 12 = 4 * k * N)
    (hI : Inv E σ) (hM : 4 * k * N + 2 ≤ E.M) (hkM : k ≤ E.M) (hNM : N ≤ E.M)
    (hC : 4 * k * N * k ≤ E.C) :
    CQ (E := E) k K N (exec E (constRepC tgt) σ) ∧ Inv E (exec E (constRepC tgt) σ) ∧
      (exec E (constRepC tgt) σ).ls tgt =
        repList E ix (constRepV (.gate 0 : Wire ι) (gvExp (2 ^ K) : OI N k → ℕ)) ∧
      (∀ r : SR, r.val < 41 ∨ 46 < r.val → (exec E (constRepC tgt) σ).sc r = σ.sc r) ∧
      ∀ l : LR, l ≠ tgt → l ≠ 12 → (exec E (constRepC tgt) σ).ls l = σ.ls l := by
  set σ0 := setSL σ (Function.update (Function.update (Function.update (Function.update σ.sc 43 0)
    44 0) 45 0) 46 0) (Function.update σ.ls tgt [])
  have e0 : exec E (.seq (.zero 43) (.seq (.zero 44) (.seq (.zero 45) (.seq (.zero 46)
      (.lnil tgt))))) σ = σ0 := rfl
  have hs0 : ∀ r : SR, r.val < 43 ∨ 46 < r.val → σ0.sc r = σ.sc r := fun r hr => by
    simp only [σ0, setSL]
    rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide)]
  have hI0 : Inv E σ0 := by
    have := inv_exec E (.seq (.zero 43) (.seq (.zero 44) (.seq (.zero 45) (.seq (.zero 46)
      (.lnil tgt))))) σ hI
    rw [e0] at this; exact this
  let Q : St → Prop := fun τ => CQ (E := E) k K N τ ∧ Inv E τ ∧
    (∀ r : SR, r.val < 41 ∨ 46 < r.val → τ.sc r = σ.sc r) ∧
    ∀ l : LR, l ≠ tgt → l ≠ 12 → τ.ls l = σ.ls l
  obtain ⟨⟨⟨q0, q1⟩, q2, q3, q4⟩, q5, q6, q7⟩ := hq
  have hQ0 : Q σ0 := ⟨⟨⟨⟨by rw [hs0 0 (by decide), q0], by rw [hs0 1 (by decide), q1]⟩,
      by rw [hs0 2 (by decide), q2], by rw [hs0 3 (by decide), q3], by rw [hs0 4 (by decide), q4]⟩,
      by rw [hs0 5 (by decide), q5], by rw [hs0 6 (by decide), q6], by rw [hs0 7 (by decide), q7]⟩,
    hI0, fun r hr => hs0 r (by omega),
    fun l hl _ => by simp [σ0, setSL, Function.update_of_ne hl]⟩
  have it := iter_oLoop (E := E) (tgt := tgt)
    (f := fun o => (constL (.gate 0 : Wire ι) k (gvExp (2 ^ K) o)).map (pos E ix)) (Q := Q) hk hN
    (fun o => by simp [constL_length]) (fun τ h => ⟨h.1.1.2.1, h.1.2.1, h.1.2.2.1⟩)
    (fun τ a b c d h => ⟨⟨⟨⟨by simp [setSL, rONE, Function.update_apply, h.1.1.1.1],
      by simp [setSL, rZ, Function.update_apply, h.1.1.1.2]⟩,
      by simp [setSL, h.1.1.2.1], by simp [setSL, h.1.1.2.2.1], by simp [setSL, h.1.1.2.2.2]⟩,
      by simp [setSL, h.1.2.1], by simp [setSL, h.1.2.2.1], by simp [setSL, h.1.2.2.2]⟩,
      h.2.1, fun r hr => by
        simp only [setSL]
        rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide)]
        exact h.2.2.1 r hr, fun l a b => h.2.2.2 l a b⟩)
    (fun τ o h hd hC' => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := exec_cBody (ix := ix) hnM tgt htgt o τ hkM h.1 hd h.2.1 hC'
      exact ⟨⟨a1, inv_exec E _ τ h.2.1, fun r hr => by
          rw [a4 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)]
          exact h.2.2.1 r hr,
        fun l a b => by rw [a5 l a b]; exact h.2.2.2 l a b⟩, a2, a3⟩)
    hM hkM hNM (4 * k * N) σ0 [] le_rfl hQ0 (by simp [σ0, setSL])
    (by simp [σ0, setSL]) (by simp [σ0, setSL]) (by simp [σ0, setSL]) (by simp [σ0, setSL])
    (by simpa using hC)
  have hrun : exec E (constRepC tgt) σ = (exec E (.seq (cBody tgt) odoO))^[4 * k * N] σ0 := by
    rw [constRepC, exec_seq, e0, oLoop, exec_rep, hs0 12 (by decide), h12]
  obtain ⟨hQ, hL, -⟩ := it
  rw [hrun]
  refine ⟨hQ.1, hQ.2.1, ?_, hQ.2.2.1, hQ.2.2.2⟩
  rw [hL, List.nil_append, List.take_of_length_le (by rw [length_enumO']), repList]
  congr 1
  apply List.map_congr_left; intro o _
  simp only [constRepV]
  rw [ofFn_getD _ _ (constL_length _ _ _)]

/-! ### The dispatch on a wire index -/

/-- **The representation of the source wire of index `|60|`** (in the format of gate lists:
`0` is `1`, `1 … 10` the inputs, then the gates) into `tgt`; the earlier block outputs are the
list `22` (`|59|` of them, `B = |10|` wires each). Constants: `13 = 1`, `14 = 11`. -/
def repOfC (tgt : LR) : Code :=
  .ifLt 7 60
    (.ifLt 60 14
      (.seq (.mov 61 60) (.seq (.sub 61 13) (.seq (maddC 61 10 7 53) (inRepC tgt))))
      (.seq (.mov 58 60) (.seq (.sub 58 14) (.ifLt 58 59
        (.seq (maddC 58 10 7 53) (sliceC tgt 22 58 10 20)) (constRepC tgt)))))
    (constRepC tgt)

theorem slice_reps {N k : ℕ} {ι : Type*} (E : Env) (ix : ι → ℕ) (reps : List (BI N k → Wire ι))
    (m : ℕ) (hm : m < reps.length) :
    (((reps.map (repList E ix)).flatten.drop (m * (4 * k * N * k))).take (4 * k * N * k)) =
      repList E ix reps[m] := by
  rw [drop_take_flatten' _ (fun w hw => by
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hw; exact length_repList E ix r) m (by simpa using hm)]
  simp

/-- The constants the representations need: `CQ`, `10 = B`, `12 = 4kN`, `13 = 1`, `14 = 11`. -/
def RQ (k K N : ℕ) (σ : St) : Prop :=
  CQ (E := E) k K N σ ∧ σ.sc 10 = 4 * k * N * k ∧ σ.sc 12 = 4 * k * N ∧ σ.sc 13 = 1 ∧ σ.sc 14 = 11

set_option maxHeartbeats 4000000 in
theorem exec_repOfC (hnM : E.n + 1 ≤ E.M) {N k K : ℕ} (hk : 0 < k) (hN : 0 < N)
    (ix' : Fin 10 × BI N k → ℕ) (hix : ∀ i b, ix' (i, b) = i.val * (4 * k * N * k) + codec b)
    (tgt : LR) (htgt : tgt.val < 12 ∨ (12 < tgt.val ∧ tgt.val < 20) ∨ 22 < tgt.val)
    (reps : List (BI N k → Wire (Fin 10 × BI N k))) (v : ℕ) (σ : St)
    (hq : RQ (E := E) k K N σ) (hI : Inv E σ) (h60 : σ.sc 60 = v) (h59 : σ.sc 59 = reps.length)
    (h22 : σ.ls 22 = (reps.map (repList E ix')).flatten)
    (hM : (reps.length + 11) * (4 * k * N * k) + 4 * k * N + 2 ≤ E.M)
    (hC : 4 * k * N * k ≤ E.C) :
    (exec E (repOfC tgt) σ).ls tgt =
        repList E ix' (repOfL (.gate 0) (gvExp (2 ^ K)) reps (ofIdx 10 v)) ∧
      RQ (E := E) k K N (exec E (repOfC tgt) σ) ∧ Inv E (exec E (repOfC tgt) σ) ∧
      (∀ r : SR, r.val < 16 ∨ 62 < r.val ∨ r.val = 59 ∨ r.val = 60 →
        (exec E (repOfC tgt) σ).sc r = σ.sc r) ∧
      ∀ l : LR, l ≠ tgt → l ≠ 12 → l ≠ 20 → (exec E (repOfC tgt) σ).ls l = σ.ls l := by
  obtain ⟨hcq, h10, h12, h13, h14⟩ := hq
  have hB : 4 * k * N * k ≤ E.M := by nlinarith
  have hkM : k ≤ E.M := by nlinarith
  have hNM : N ≤ E.M := by nlinarith
  have ht12 : tgt ≠ 12 := by rintro rfl; revert htgt; decide
  have hRQ : ∀ τ : St, (∀ r : SR, r.val < 16 → τ.sc r = σ.sc r) → RQ (E := E) k K N τ :=
    fun τ h => ⟨⟨⟨⟨by rw [h 0 (by decide), hcq.1.1.1], by rw [h 1 (by decide), hcq.1.1.2]⟩,
      by rw [h 2 (by decide), hcq.1.2.1], by rw [h 3 (by decide), hcq.1.2.2.1],
      by rw [h 4 (by decide), hcq.1.2.2.2]⟩, by rw [h 5 (by decide), hcq.2.1],
      by rw [h 6 (by decide), hcq.2.2.1], by rw [h 7 (by decide), hcq.2.2.2]⟩,
      by rw [h 10 (by decide), h10], by rw [h 12 (by decide), h12], by rw [h 13 (by decide), h13],
      by rw [h 14 (by decide), h14]⟩
  -- the constant case
  have hconst : (repOfL (.gate 0) (gvExp (2 ^ K)) reps (.one : Wire (Fin 10)) :
      BI N k → Wire (Fin 10 × BI N k)) = constRepV (.gate 0) (gvExp (2 ^ K)) := rfl
  have caseC : ∀ w : Wire (Fin 10), (repOfL (.gate 0) (gvExp (2 ^ K)) reps w :
      BI N k → Wire (Fin 10 × BI N k)) = constRepV (.gate 0) (gvExp (2 ^ K)) →
      (exec E (constRepC tgt) σ).ls tgt = repList E ix' (repOfL (.gate 0) (gvExp (2 ^ K)) reps w) ∧
      RQ (E := E) k K N (exec E (constRepC tgt) σ) ∧ Inv E (exec E (constRepC tgt) σ) ∧
      (∀ r : SR, r.val < 16 ∨ 62 < r.val ∨ r.val = 59 ∨ r.val = 60 →
        (exec E (constRepC tgt) σ).sc r = σ.sc r) ∧
      ∀ l : LR, l ≠ tgt → l ≠ 12 → l ≠ 20 → (exec E (constRepC tgt) σ).ls l = σ.ls l := by
    intro w hw
    obtain ⟨_, a2, a3, a4, a5⟩ := exec_constRepC (ix := ix') hnM hk hN tgt ht12 σ hcq h12 hI
      (by nlinarith) hkM hNM hC
    exact ⟨by rw [a3, hw], hRQ _ (fun r hr => a4 r (by omega)), a2,
      fun r hr => a4 r (by omega), fun l a b _ => a5 l a b⟩
  by_cases hv0 : v = 0
  · subst hv0
    have e : exec E (repOfC tgt) σ = exec E (constRepC tgt) σ := by
      simp [repOfC, exec_ifLt, h60, hcq.2.2.2]
    rw [e]; exact caseC _ (by simp only [ofIdx, ite_true]; rfl)
  by_cases hv : v < 11
  · -- an input
    have hi : v - 1 < 10 := by omega
    set σ1 := setSL σ (Function.update (Function.update σ.sc 61 ((v - 1) * (4 * k * N * k))) 53
      (v - 1)) σ.ls
    have e1 : exec E (maddC 61 10 7 53) (exec E (.sub 61 13) (exec E (.mov 61 60) σ)) = σ1 := by
      rw [exec_maddC 61 10 7 53 (by decide) (by decide) (by decide) (by decide) (by decide) _
        (by simp [exec, h60, h13, h10, hcq.2.2.2]; nlinarith)]
      simp only [exec, σ1, setSL, h60, h13, h10, hcq.2.2.2, Function.update_self,
        Function.update_idem, Function.update_of_ne (show (61 : SR) ≠ 10 by decide),
        Function.update_of_ne (show (53 : SR) ≠ 61 by decide), Function.update_of_ne
        (show (7 : SR) ≠ 53 by decide), Function.update_of_ne (show (7 : SR) ≠ 61 by decide),
        Function.update_of_ne (show (10 : SR) ≠ 61 by decide), Nat.add_zero]
      congr 1; funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
    have hs1 : ∀ r : SR, r ≠ 53 → r ≠ 61 → σ1.sc r = σ.sc r := fun r a b => by
      simp [σ1, setSL, Function.update_of_ne a, Function.update_of_ne b]
    have e : exec E (repOfC tgt) σ = exec E (inRepC tgt) σ1 := by
      simp only [repOfC, exec_ifLt, h60, hcq.2.2.2, h14, show 0 < v by omega, hv, ite_true,
        exec_seq]
      rw [e1]
    obtain ⟨a1, a2, a3, a4⟩ := exec_inRepC (E := E) hk hN ix' ⟨v - 1, hi⟩ ((v - 1) * (4 * k * N * k))
      (fun b => hix _ b) tgt σ1 ⟨by rw [hs1 2 (by decide) (by decide), hcq.1.2.1],
        by rw [hs1 5 (by decide) (by decide), hcq.2.1], by rw [hs1 6 (by decide) (by decide),
        hcq.2.2.1], by simp [σ1, setSL]⟩ (by rw [hs1 12 (by decide) (by decide), h12])
      (by nlinarith) hC
    have hI1 : Inv E σ1 := by
      have := inv_exec E (.seq (.mov 61 60) (.seq (.sub 61 13) (maddC 61 10 7 53))) σ hI
      simp only [exec_seq] at this; rw [e1] at this; exact this
    rw [e]
    have hw : ofIdx 10 v = .input ⟨v - 1, hi⟩ := by simp [ofIdx, hv0, hi]
    refine ⟨by rw [a2, hw]; rfl, hRQ _ (fun r hr => by
        rw [a3 r (by omega), hs1 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)]),
      inv_exec E _ σ1 hI1, fun r hr => ?_, fun l a b _ => by rw [a4 l a]; simp [σ1, setSL]⟩
    have nv : ∀ (r : SR) (c : ℕ), r.val ≠ c → ∀ d : SR, d.val = c → r ≠ d :=
      fun r c h d hd e => h (by rw [e, hd])
    rw [a3 r (by omega), hs1 r (nv r 53 (by omega) 53 rfl) (nv r 61 (by omega) 61 rfl)]
  · -- a gate
    have nv : ∀ (r : SR) (c : ℕ), r.val ≠ c → ∀ d : SR, d.val = c → r ≠ d :=
      fun r c h d hd e => h (by rw [e, hd])
    have hw : ofIdx 10 v = .gate (v - 11) := by
      simp only [ofIdx, hv0, ite_false, show ¬ (v - 1 < 10) by omega, dite_false]; congr 1
    set m := v - 11
    set σ2 := setSL σ (Function.update σ.sc 58 m) σ.ls
    have e2 : exec E (.sub 58 14) (exec E (.mov 58 60) σ) = σ2 := by
      simp only [exec, σ2, setSL, h60, h14, Function.update_self, Function.update_idem,
        Function.update_of_ne (show (14 : SR) ≠ 58 by decide)]
      rfl
    have pre : exec E (repOfC tgt) σ = exec E (.ifLt 58 59 (.seq (maddC 58 10 7 53)
        (sliceC tgt 22 58 10 20)) (constRepC tgt)) σ2 := by
      simp only [repOfC, exec_ifLt, h60, hcq.2.2.2, h14, show 0 < v by omega, hv, ite_true,
        ite_false, exec_seq]
      rw [e2]
    rw [pre, exec_ifLt, show σ2.sc 58 = m by simp [σ2, setSL],
      show σ2.sc 59 = reps.length by simp [σ2, setSL, h59]]
    by_cases hm : m < reps.length
    · rw [if_pos hm, exec_seq]
      set σ3 := setSL σ (Function.update (Function.update σ.sc 58 (m * (4 * k * N * k))) 53 m)
        σ.ls
      have e3 : exec E (maddC 58 10 7 53) σ2 = σ3 := by
        rw [exec_maddC 58 10 7 53 (by decide) (by decide) (by decide) (by decide) (by decide) _
          (by simp [σ2, setSL, h10, hcq.2.2.2]; nlinarith)]
        simp only [σ3, σ2, setSL, Function.update_self, Function.update_idem, h10, hcq.2.2.2,
          Function.update_of_ne (show (10 : SR) ≠ 58 by decide),
          Function.update_of_ne (show (7 : SR) ≠ 58 by decide),
          Function.update_of_ne (show (7 : SR) ≠ 53 by decide), Nat.add_zero]
        congr 1; funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
      rw [e3]
      have hI3 : Inv E σ3 := hI
      have hl22 : (σ3.ls 22).length = reps.length * (4 * k * N * k) := by
        simp only [σ3, setSL, h22]
        rw [length_flatten_of' (V := 4 * k * N * k) _ (fun w hw => by
          obtain ⟨r, _, rfl⟩ := List.mem_map.mp hw; exact length_repList E ix' r)]
        simp
      obtain ⟨sc4, h4, f4⟩ := exec_sliceC (E := E) tgt 22 58 10 20
        (by rintro h; rw [← h] at htgt; revert htgt; decide) σ3 hI3
        (by rw [hl22]; simp [σ3, setSL, h10]; nlinarith) (by decide)
        (by simp [σ3, setSL, h10]; exact hC)
      have hs3 : ∀ r : SR, r ≠ 53 → r ≠ 58 → σ3.sc r = σ.sc r := fun r a b => by
        simp [σ3, setSL, Function.update_of_ne a, Function.update_of_ne b]
      have hIn := inv_exec E (sliceC tgt 22 58 10 20) σ3 hI3
      rw [h4] at hIn
      rw [h4]
      refine ⟨?_, hRQ _ (fun r hr => by
          show sc4 r = _
          rw [f4 r (by simp only [List.mem_singleton]; exact nv r 41 (by omega) 41 rfl),
            hs3 r (nv r 53 (by omega) 53 rfl) (nv r 58 (by omega) 58 rfl)]),
        hIn, fun r hr => ?_, fun l a b c => ?_⟩
      · simp only [setSL, Function.update_self]
        simp only [σ3, setSL, h22, h10, hw, repOfL, Function.update_self,
          Function.update_of_ne (show (10 : SR) ≠ 53 by decide),
          Function.update_of_ne (show (10 : SR) ≠ 58 by decide),
          Function.update_of_ne (show (58 : SR) ≠ 53 by decide)]
        rw [slice_reps E ix' reps m hm, List.getD_eq_getElem _ _ hm]
      · show sc4 r = _
        rw [f4 r (by simp only [List.mem_singleton]; exact nv r 41 (by omega) 41 rfl),
          hs3 r (nv r 53 (by omega) 53 rfl) (nv r 58 (by omega) 58 rfl)]
      · simp [setSL, Function.update_of_ne a, Function.update_of_ne c, σ3]
    · rw [if_neg hm]
      have hs2 : ∀ r : SR, r ≠ 58 → σ2.sc r = σ.sc r := fun r a => by
        simp [σ2, setSL, Function.update_of_ne a]
      obtain ⟨_, a2, a3, a4, a5⟩ := exec_constRepC (ix := ix') hnM hk hN tgt ht12 σ2
        ⟨⟨⟨by rw [hs2 0 (by decide), hcq.1.1.1], by rw [hs2 1 (by decide), hcq.1.1.2]⟩,
          by rw [hs2 2 (by decide), hcq.1.2.1], by rw [hs2 3 (by decide), hcq.1.2.2.1],
          by rw [hs2 4 (by decide), hcq.1.2.2.2]⟩, by rw [hs2 5 (by decide), hcq.2.1],
          by rw [hs2 6 (by decide), hcq.2.2.1], by rw [hs2 7 (by decide), hcq.2.2.2]⟩
        (by rw [hs2 12 (by decide), h12]) hI (by nlinarith) hkM hNM hC
      refine ⟨?_, hRQ _ (fun r hr => by rw [a4 r (by omega), hs2 r (nv r 58 (by omega) 58 rfl)]),
        a2, fun r hr => by rw [a4 r (by omega), hs2 r (nv r 58 (by omega) 58 rfl)],
        fun l a b _ => (a5 l a b).trans rfl⟩
      rw [a3, hw]; simp only [repOfL]; rw [List.getD_eq_default _ _ (by omega)]

end FhatGen

end SigabaNeo.Lattices
