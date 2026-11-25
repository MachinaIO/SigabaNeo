import PE.Impl.ExpLUT.Prog.RedChalCode

/-!
# Parsing the raw secret (package G2, `chalP`)

**`exec_parseC`**: `parseC` splits the word of the raw secret (register `ra`) into its fields:
the attribute bits (`rAttr`), the values of the instance (`rV`; the public parts are dropped),
`B⁽²⁾` (`rB2`), `H⁽²⁾` (`rH2`), `d₂` (`rd2`), the flooding errors (`xF`), and the programming bits
`Z_t` (`rZ`), `R₀` (`rR0`), `R^in` (`rRin`), `R^aut` (left in `ra`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog.RedVM

variable {D : Dims}

/-! ### The fields of the raw secret as words -/

section Fields

variable (σ : RawSec D)

/-- The values of the instance. -/
noncomputable def instVW : List Bool := (vecE D (Fin (circParamsD D).rows)).enc (toPair D σ.2.1).2

/-- `B⁽²⁾`. -/
noncomputable def b2W : List Bool := (vecE D (BCol (Wb D) D.K)).enc σ.2.2.1

/-- `H⁽²⁾`. -/
noncomputable def h2W : List Bool := (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc σ.2.2.2.1

/-- The flooding errors. -/
noncomputable def flW : List Bool := (floodEnc D).enc σ.2.2.2.2.2.1

/-- The programming bits of `Z_t`. -/
def zZW : List Bool := (zrBlocks σ.2.2.2.2.2.2 fun p : Pos × Col D.K => .inl p).flatten

/-- The programming bits of `R₀`. -/
def zR0W : List Bool := (zrBlocks σ.2.2.2.2.2.2 fun c : Col D.K => .inr (.inl c)).flatten

/-- The programming bits of `R^in`. -/
def zRinW : List Bool :=
  (zrBlocks σ.2.2.2.2.2.2 fun p : Pos × Dig D.K × Col D.K => .inr (.inr (.inl p))).flatten

/-- The programming bits of `R^aut`. -/
def zAutW : List Bool :=
  (zrBlocks σ.2.2.2.2.2.2 fun p : Fin D.b × Dig D.K × Col D.K => .inr (.inr (.inr p))).flatten

end Fields

theorem length_zrBlocks {α : Type} [Enum α] (zr : PrI (setting D) Pos → Wb D → Bool)
    (ι : α → PrI (setting D) Pos) : (zrBlocks zr ι).flatten.length = nE α * nE (Wb D) := by
  rw [length_flatten_of (n := nE (Wb D)), zrBlocks, List.length_map]
  intro x hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  simp

theorem length_enc {β : Type} {n : ℕ} (e : FixedEnc β n) (b : β) : (e.enc b).length = e.len :=
  e.length b

/-! ### The parse -/

/-- **Drop** a word of the template's width from a stream. -/
theorem exec_drop_pop {N K : ℕ} {t c : Fin 200} (h : t ≠ c) {w : St} {v L : List Bool}
    (hv : (w c).length = v.length) (hs : w t = v ++ L) :
    exec N K (.drop t c) w = Function.update w t L := by
  simp only [exec, h, ite_false, hs, hv, List.drop_left]

/-- The registers `parseC` writes. -/
def parseW : List (Fin 200) := [rAttr, ra, rV, rB2, rH2, rd2, xF, rZ, rR0, rRin]

/-- **The parse.** -/
theorem exec_parseC (σ : RawSec D) (w : St) (hra : w ra = (rawEnc D).enc σ)
    (h128 : (w c128).length = 128) (hAt : (w rAttr).length = 128)
    (hI : (w cInst).length = (vecE D (Fin (circParamsD D).rows)).len)
    (hV : (w rV).length = (vecE D (Fin (circParamsD D).rows)).len)
    (hB : (w cB2).length = (vecE D (BCol (Wb D) D.K)).len)
    (hB' : (w rB2).length = (vecE D (BCol (Wb D) D.K)).len)
    (hH : (w cH2).length = (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).len)
    (hH' : (w rH2).length = (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).len)
    (hNK : (w xCNK).length = D.N * D.K) (hd : (w rd2).length = D.N * D.K)
    (hF : (w cFl).length = (floodEnc D).len) (hF' : (w xF).length = (floodEnc D).len)
    (hZ : (w cZ).length = nE (Pos × Col D.K) * nE (Wb D))
    (hZ' : (w rZ).length = nE (Pos × Col D.K) * nE (Wb D))
    (hR : (w cR0).length = nE (Col D.K) * nE (Wb D))
    (hR' : (w rR0).length = nE (Col D.K) * nE (Wb D))
    (hI2 : (w cRin).length = nE (Pos × Dig D.K × Col D.K) * nE (Wb D))
    (hI2' : (w rRin).length = nE (Pos × Dig D.K × Col D.K) * nE (Wb D)) :
    exec D.N D.K parseC w rAttr = encAttribute w8 σ.1 ∧ exec D.N D.K parseC w rV = instVW σ ∧
      exec D.N D.K parseC w rB2 = b2W σ ∧ exec D.N D.K parseC w rH2 = h2W σ ∧
      exec D.N D.K parseC w rd2 = encRM D.N D.K σ.2.2.2.2.1 ∧ exec D.N D.K parseC w xF = flW σ ∧
      exec D.N D.K parseC w rZ = zZW σ ∧ exec D.N D.K parseC w rR0 = zR0W σ ∧
      exec D.N D.K parseC w rRin = zRinW σ ∧ exec D.N D.K parseC w ra = zAutW σ ∧
      ∀ j, j ∉ parseW → exec D.N D.K parseC w j = w j := by
  have e0 : w ra = encAttribute w8 σ.1 ++ ((vecE D (Fin (circParamsD D).rows)).enc
      (toPair D σ.2.1).1 ++ (instVW σ ++ (b2W σ ++ (h2W σ ++ (encRM D.N D.K σ.2.2.2.2.1 ++
        (flW σ ++ (zZW σ ++ (zR0W σ ++ (zRinW σ ++ zAutW σ))))))))) := by
    rw [hra, rawEnc_split, instEnc_enc, zrEnc_split]
    simp only [List.append_assoc]
    rfl
  simp only [parseC, exec_ofList_cons, exec_ofList_nil]
  rw [exec_mv_pop (d := rAttr) (s := ra) (c := c128) (by decide) (by rw [hAt, h128])
    (by rw [length_encAttribute, h128]) e0]
  rw [exec_drop_pop (t := ra) (c := cInst) (by decide)
    (v := (vecE D (Fin (circParamsD D).rows)).enc (toPair D σ.2.1).1) (L := (instVW σ ++ (b2W σ ++ (h2W σ ++ (encRM D.N D.K σ.2.2.2.2.1 ++ (flW σ ++ (zZW σ ++ (zR0W σ ++ (zRinW σ ++ zAutW σ)))))))))
    (by simp [Function.update_apply, hI, length_enc]) (by simp [Function.update_apply])]
  rw [exec_mv_pop (d := rV) (s := ra) (c := cInst) (v := instVW σ) (L := (b2W σ ++ (h2W σ ++ (encRM D.N D.K σ.2.2.2.2.1 ++ (flW σ ++ (zZW σ ++ (zR0W σ ++ (zRinW σ ++ zAutW σ)))))))) (by decide)
    (by simp [Function.update_apply, hV, hI]) (by simp [Function.update_apply, hI, instVW] <;> exact length_enc _ _)
    (by simp [Function.update_apply])]
  rw [exec_mv_pop (d := rB2) (s := ra) (c := cB2) (v := b2W σ) (L := (h2W σ ++ (encRM D.N D.K σ.2.2.2.2.1 ++ (flW σ ++ (zZW σ ++ (zR0W σ ++ (zRinW σ ++ zAutW σ))))))) (by decide)
    (by simp [Function.update_apply, hB, hB']) (by simp [Function.update_apply, hB, b2W] <;> exact length_enc _ _)
    (by simp [Function.update_apply])]
  rw [exec_mv_pop (d := rH2) (s := ra) (c := cH2) (v := h2W σ) (L := (encRM D.N D.K σ.2.2.2.2.1 ++ (flW σ ++ (zZW σ ++ (zR0W σ ++ (zRinW σ ++ zAutW σ)))))) (by decide)
    (by simp [Function.update_apply, hH, hH']) (by simp [Function.update_apply, hH, h2W] <;> exact length_enc _ _)
    (by simp [Function.update_apply])]
  rw [exec_mv_pop (d := rd2) (s := ra) (c := xCNK) (v := encRM D.N D.K σ.2.2.2.2.1) (L := (flW σ ++ (zZW σ ++ (zR0W σ ++ (zRinW σ ++ zAutW σ))))) (by decide)
    (by simp [Function.update_apply, hd, hNK]) (by simp [Function.update_apply, hNK, length_encRM])
    (by simp [Function.update_apply])]
  rw [exec_mv_pop (d := xF) (s := ra) (c := cFl) (v := flW σ) (L := (zZW σ ++ (zR0W σ ++ (zRinW σ ++ zAutW σ)))) (by decide)
    (by simp [Function.update_apply, hF, hF']) (by simp [Function.update_apply, hF, flW] <;> exact length_enc _ _)
    (by simp [Function.update_apply])]
  rw [exec_mv_pop (d := rZ) (s := ra) (c := cZ) (v := zZW σ) (L := (zR0W σ ++ (zRinW σ ++ zAutW σ))) (by decide)
    (by simp [Function.update_apply, hZ, hZ']) (by rw [zZW, length_zrBlocks]; simp [Function.update_apply, hZ])
    (by simp [Function.update_apply])]
  rw [exec_mv_pop (d := rR0) (s := ra) (c := cR0) (v := zR0W σ) (L := (zRinW σ ++ zAutW σ)) (by decide)
    (by simp [Function.update_apply, hR, hR']) (by rw [zR0W, length_zrBlocks]; simp [Function.update_apply, hR])
    (by simp [Function.update_apply])]
  rw [exec_mv_pop (d := rRin) (s := ra) (c := cRin) (v := zRinW σ) (L := zAutW σ) (by decide)
    (by simp [Function.update_apply, hI2, hI2']) (by rw [zRinW, length_zrBlocks]; simp [Function.update_apply, hI2])
    (by simp [Function.update_apply])]
  refine ⟨by simp [Function.update_apply], by simp [Function.update_apply],
    by simp [Function.update_apply], by simp [Function.update_apply],
    by simp [Function.update_apply], by simp [Function.update_apply],
    by simp [Function.update_apply], by simp [Function.update_apply],
    by simp [Function.update_apply], by simp [Function.update_apply], ?_⟩
  intro j hj
  simp only [parseW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hj
  simp [Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

end AdvancedEncryption.ExpLUT.Prog.RedChal
