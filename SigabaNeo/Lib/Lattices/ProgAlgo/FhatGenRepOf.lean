import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenBlock

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

end FhatGen

end SigabaNeo.Lattices
