import PE.Impl.ExpLUT.Prog.RedKeyC4A
import PE.Impl.ExpLUT.Prog.KeyTimeTemplates
/-!
# Cost certificate of `mid`, phase M3 (part 1): the verified analyzer with **template leaves**

`RedKeyC4A`'s analyzer `anA` handles codes with `natC` leaves (`AC`). Phase M3 (`pkOf pkt`) also
contains `templateOpsC` blocks whose `.bits` words are `N K`-bit literals (`emitBitsC`: one `app`
per bit — not analyzable instruction by instruction). This file adds a leaf for any template word
(`TemplateWord.code r w`, `|w.value| ≤ v`), certified by F3's `compile_template`.

* **`AD`**: `AC` codes, template leaves `tw r v`, sequences; **`AD.Er`** (description);
* **`anD`**: the analyzer (a template leaf needs registers `5`, `rB1` `≤ 1` on its box and bumps
  them to `1`: the certificate runs from the layout where they are exactly `1`);
* **`anD_sound`**, **`m3Ok_cert`** (as `RedKeyC4A.c4Ok_cert`);
* **`twL`**, **`twL_er`**: a template list `templateOpsC ops` as a chain of leaves.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC3M

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.ExpLUT.Prog.RedKeyC4

/-- A code with `natC` leaves (`AC`) and template leaves. -/
inductive AD where
  | a (ac : AC)
  | tw (r : Fin 64) (v : ℕ)
  | s (p q : AD)

/-- `ad` describes the code `c`. -/
inductive AD.Er : AD → Code → Prop
  | a {ac : AC} {c : Code} : AC.Er ac c → AD.Er (.a ac) c
  | tw (r : Fin 64) (v : ℕ) (w : TemplateWord) (h : w.value.length ≤ v) :
      AD.Er (.tw r v) (w.code r)
  | s {p q : AD} {cp cq : Code} : AD.Er p cp → AD.Er q cq → AD.Er (.s p q) (.seq cp cq)

/-- The transformer of a template leaf. -/
def m3TwT (r : Fin 64) (v : ℕ) : C4T := [(r.val, ⟨v, none⟩), (5, ⟨1, none⟩), (38, ⟨1, none⟩)]

/-- **The analyzer on `AD`.** -/
def anD (M N K : ℕ) : AD → List ℕ → List C4H → Option C4R
  | .a ac, E, hs => anA M N K ac E hs
  | .tw r v, E, hs =>
    if r ≠ 5 ∧ r ≠ rB1 ∧ E.getD 5 0 ≤ 1 ∧ E.getD 38 0 ≤ 1 ∧ v ≤ M then
      some ⟨m3TwT r v, (32 * v + 6) * (2 * M + 5), ((E.set 38 1).set 5 1).set r.val v, hs⟩
    else none
  | .s p q, E, hs =>
    match anD M N K p E hs with
    | none => none
    | some r1 =>
      match anD M N K q r1.out r1.hs with
      | none => none
      | some r2 => some ⟨tcomp r1.t r2.t, r1.T + r2.T, r2.out, r2.hs⟩

theorem m3_tAp_cons (k : Fin 64) (e : C4E) (t : C4T) (x : Fin 64 → ℕ) :
    tAp ((k.val, e) :: t) x = Function.update (tAp t x) k (e.ev x) := by
  funext q
  simp only [tAp, tget, Function.update_apply]
  by_cases h : q = k
  · subst h; simp
  · have : Nat.beq k.val q.val = false := by
      rcases hb : Nat.beq k.val q.val
      · rfl
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hb)).symm h
    rw [this, if_neg h]
    rfl

theorem m3_tAp_tw (r : Fin 64) (v : ℕ) (x : Fin 64 → ℕ) :
    tAp (m3TwT r v) x =
      Function.update (Function.update (Function.update x 38 1) 5 1) r v := by
  unfold m3TwT
  rw [m3_tAp_cons r, show (5 : ℕ) = (5 : Fin 64).val from rfl, m3_tAp_cons 5,
    show (38 : ℕ) = (38 : Fin 64).val from rfl, m3_tAp_cons 38, tAp_nil]
  rfl

section Sound

variable {M N K : ℕ}

/-- The template leaf. -/
theorem m3_sound_tw (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) (hM1 : 1 ≤ M)
    (r : Fin 64) (v : ℕ) (w : TemplateWord) (hw : w.value.length ≤ v) (E : List ℕ)
    (hs : List C4H) (res : C4R) (h : anD M N K (.tw r v) E hs = some res) (hE64 : E.length = 64)
    (hE : ∀ i, bx E i ≤ M) : Sound M N K (w.code r) E res := by
  simp only [anD] at h
  split_ifs at h with hc
  obtain ⟨h5, hf, hE5, hE38, hv⟩ := hc
  simp only [Option.some.injEq] at h; subst h
  have hb : bx (((E.set 38 1).set 5 1).set r.val v) =
      Function.update (Function.update (Function.update (bx E) 38 1) 5 1) r v := by
    rw [bx_set _ (by simp [hE64]), show (5 : ℕ) = (5 : Fin 64).val from rfl,
      bx_set _ (by simp [hE64]), show (38 : ℕ) = (38 : Fin 64).val from rfl, bx_set _ hE64]
  refine ⟨by simp [hE64], ?_, fun x hx => ⟨?_, ?_⟩⟩
  · rw [hb]; intro i
    simp only [Function.update_apply]; split_ifs
    · exact hv
    · exact hM1
    · exact hM1
    · exact hE i
  · rw [hb, m3_tAp_tw]; intro i
    simp only [Function.update_apply]
    split_ifs
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact hx i
  · rw [m3_tAp_tw]
    set y := Function.update (Function.update x 38 1) 5 1 with hy
    have hx5 : x 5 ≤ 1 := (hx 5).trans hE5
    have hx38 : x 38 ≤ 1 := (hx 38).trans hE38
    have hxy : x ≤ y := by
      intro i
      simp only [hy, Function.update_apply]
      split_ifs with h1 h2
      · subst h1; exact hx5
      · subst h2; exact hx38
      · exact le_rfl
    have hyM : ∀ i, y i ≤ M := by
      intro i
      simp only [hy, Function.update_apply]
      split_ifs
      · exact hM1
      · exact hM1
      · exact (hx i).trans (hE i)
    have hin := layout_inputs M N K y hyM hNK hN hK
    have hc := compile_template r h5 hf w M (layout M N K y) hin.top
      (by simp [hy]) (by simp [hy, Function.update_apply]) (hw.trans hv)
    refine hc.mono (layout_mono M N K hxy) ?_ (Nat.mul_le_mul (by omega) le_rfl)
    apply le_layout M N K _ _ (natResult_top _ _ _ _ hin.top (hw.trans hv))
    · rw [natResult_low _ _ _ _ 35 (by decide)]; exact hin.templateK
    · rw [natResult_low _ _ _ _ 36 (by decide)]; exact hin.templateN
    · rw [natResult_low _ _ _ _ 37 (by decide)]; exact hin.zeros.le
    · rw [natResult_low _ _ _ _ 38 (by decide)]; exact hin.ones
    · intro q
      rw [natResult_register, layout_register]
      simp only [Function.update_apply]
      split_ifs <;> first | exact le_rfl | exact hw

theorem anD_sound (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) (hM1 : 1 ≤ M) :
    ∀ (ad : AD) (c : Code), AD.Er ad c → ∀ (E : List ℕ) (hs : List C4H) (r : C4R),
      anD M N K ad E hs = some r → E.length = 64 → (∀ i, bx E i ≤ M) → Sound M N K c E r := by
  intro ad c had
  induction had with
  | a hac => exact anA_sound hNK hN hK hM1 _ _ hac
  | tw r v w hw =>
    intro E hs res h hE64 hE
    exact m3_sound_tw hNK hN hK hM1 r v w hw E hs res h hE64 hE
  | s hp hq ihp ihq =>
    intro E hs r h hE64 hE
    simp only [anD] at h
    split at h
    · simp at h
    · rename_i r1 h1
      split at h
      · simp at h
      · rename_i r2 h2
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨l1, t1, s1⟩ := ihp E hs r1 h1 hE64 hE
        obtain ⟨l2, t2, s2⟩ := ihq r1.out r1.hs r2 h2 l1 t1
        refine ⟨l2, t2, fun x hx => ?_⟩
        obtain ⟨o1, c1⟩ := s1 x hx
        obtain ⟨o2, c2⟩ := s2 _ o1
        rw [tAp_tcomp]
        exact ⟨o2, c1.seq c2⟩

/-- **The check** (as `c4Ok`). -/
def m3Ok (M N K : ℕ) (ad : AD) (E : List ℕ) (hs : List C4H) (Eo : List ℕ) (T : ℕ) : Bool :=
  match anD M N K ad E hs with
  | none => false
  | some r => Nat.beq E.length 64 && topL E M && leL r.out Eo && Nat.ble r.T T

/-- **The certificate of a checked code.** -/
theorem m3Ok_cert (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) (hM1 : 1 ≤ M)
    {ad : AD} {c : Code} (had : AD.Er ad c) {E : List ℕ} {hs : List C4H} {Eo : List ℕ}
    {T : ℕ} (h : m3Ok M N K ad E hs Eo T = true) (x : Fin 64 → ℕ) (hx : x ≤ bx E) :
    Cert (compile c) (layout M N K x) (layout M N K (bx Eo)) T := by
  unfold m3Ok at h
  split at h
  · simp at h
  · rename_i r hr
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨h64, htop⟩, hle⟩, hT⟩ := h
    obtain ⟨-, -, hs⟩ := anD_sound hNK hN hK hM1 ad c had E _ r hr h64 (topL_sound htop)
    obtain ⟨ho, hc⟩ := hs x hx
    exact hc.mono le_rfl (layout_mono M N K (ho.trans (leL_sound hle))) hT

end Sound

/-! ### Template lists -/

/-- A template list as a chain of leaves (ending in `nop`). -/
def twL : List (Fin 64 × ℕ) → AD
  | [] => .a (.c .nop)
  | (r, v) :: L => .s (.tw r v) (twL L)

theorem twL_er : ∀ (ops : List (Fin 64 × TemplateWord)) (L : List (Fin 64 × ℕ)),
    List.Forall₂ (fun op l => op.1 = l.1 ∧ op.2.value.length ≤ l.2) ops L →
    AD.Er (twL L) (templateOpsC ops)
  | [], [], _ => .a (.c _)
  | (r, w) :: ops, (r', v) :: L, h => by
    obtain ⟨⟨e, hv⟩, h'⟩ := List.forall₂_cons.mp h
    simp only at e hv
    subst e
    exact .s (.tw r v w hv) (twL_er ops L h')

end AdvancedEncryption.ExpLUT.Prog.RedKeyC3M
