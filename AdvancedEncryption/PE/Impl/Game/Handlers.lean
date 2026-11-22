import PE.Impl.Game.Generic
import SigabaNeo.Lib.Machines.Inline.Regions
import SigabaNeo.Lib.Machines.Inline.ProgRoutine
import SigabaNeo.Lib.Machines.Inline.Oracle
import SigabaNeo.Lib.Encode.Enum

/-!
# Handlers for the generic attribute-hiding oracle

Tape-language handlers (`selH`, `keyH`, `chalH`) for the oracle of the generic experiment
(`Generic.oracle`) with the challenger's secret drawn from an *instance word* `w` kept in the
oracle state (`oracleW`): the state is `(w, s)` with `s : GState U Sig`, and the selection draws
`σ ← setupW w x`.

## The state tape (`encState`)

* before the selection (`s = {}`): the instance word `w` itself, so that the initial state tape
  is the instance word (`encState_init`);
* after it: `false :: bad :: msgWord msg ++ encAttr x ++ encSig σ`, with
  `msgWord none = false :: 0^nM` and `msgWord (some μ) = true :: encMsg μ`.

Instance words never start with `false` (`InvS`), so the first bit tells the two apart. All
fields of the selected state have fixed lengths (`Codes`) and the secret comes last, so it is
parsed by a fixed number of pops.

## The handlers

Each handler is a framed program on `R + 8` tapes (`SigabaNeo.Tape.glue`, `SigabaNeo.Tape.comp`):
the query, the answer, the state tape, five glue scratch tapes and `R` scratch tapes for the
components. The components are framed programs `XProg (R + 2)` with given laws (`Comps`):
`setupP` (instance word, attribute ↦ secret), `pubP`, `keyP`, `authP`, `chalP`. The decoders of
attributes and messages are length tests (`testLen`): the encodings are onto the words of their
length (`Codes.full_attr`, `Codes.full_msg`).
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo SigabaNeo.Tape Cslib

variable {U : Universe} {Sig : Type}

/-! ### Encodings -/

/-- Fixed-length encodings of the secret, the attributes and the messages; the latter two are onto
the words of their length. -/
structure Codes (U : Universe) (Sig : Type) where
  /-- The length of an encoded attribute. -/
  nA : ℕ
  /-- The length of an encoded message. -/
  nM : ℕ
  /-- The length of an encoded secret. -/
  nS : ℕ
  /-- The encoding of the secret. -/
  sig : Encode.FixedEnc Sig nS
  len_attr : ∀ x, (U.encAttr x).length = nA
  len_msg : ∀ μ, (U.encMsg μ).length = nM
  full_attr : ∀ w : List Bool, w.length = nA → ∃ x, U.encAttr x = w
  full_msg : ∀ w : List Bool, w.length = nM → ∃ μ, U.encMsg μ = w

namespace Codes

variable (cd : Codes U Sig)

/-- The message field of the state. -/
def msgWord : Option U.Msg → List Bool
  | none => false :: List.replicate cd.nM false
  | some μ => true :: U.encMsg μ

theorem length_msgWord (m : Option U.Msg) : (cd.msgWord m).length = cd.nM + 1 := by
  cases m <;> simp [msgWord, cd.len_msg]

/-- The selected state: `false :: bad :: msgWord msg ++ encAttr x ++ encSig σ`. -/
def selWord (bad : Bool) (m : Option U.Msg) (x : U.Attr) (σ : Sig) : List Bool :=
  false :: bad :: (cd.msgWord m ++ (U.encAttr x ++ cd.sig.enc σ))

/-- **The state encoding.** -/
def encState (st : List Bool × GState U Sig) : List Bool :=
  match st.2.attr, st.2.sec with
  | some x, some σ => cd.selWord st.2.bad st.2.msg x σ
  | _, _ => st.1

theorem encState_init (w : List Bool) : cd.encState (w, {}) = w := rfl

theorem length_selWord (bad : Bool) (m : Option U.Msg) (x : U.Attr) (σ : Sig) :
    (cd.selWord bad m x σ).length = cd.nM + cd.nA + cd.nS + 3 := by
  simp [selWord, length_msgWord, cd.len_attr, cd.sig.length]; omega

theorem decode_attr (x : U.Attr) : decode U.encAttr (U.encAttr x) = some x := by
  have h : ∃ a, U.encAttr a = U.encAttr x := ⟨x, rfl⟩
  simp only [decode, h, dite_true, Option.some.injEq]
  exact U.encAttr.injective (Classical.choose_spec h)

theorem decode_msg (μ : U.Msg) : decode U.encMsg (U.encMsg μ) = some μ := by
  have h : ∃ a, U.encMsg a = U.encMsg μ := ⟨μ, rfl⟩
  simp only [decode, h, dite_true, Option.some.injEq]
  exact U.encMsg.injective (Classical.choose_spec h)

theorem decode_attr_none {b : List Bool} (hb : b.length ≠ cd.nA) : decode U.encAttr b = none := by
  have h : ¬ ∃ a, U.encAttr a = b := fun ⟨a, ha⟩ => hb (ha ▸ cd.len_attr a)
  simp [decode, h]

theorem decode_msg_none {b : List Bool} (hb : b.length ≠ cd.nM) : decode U.encMsg b = none := by
  have h : ¬ ∃ a, U.encMsg a = b := fun ⟨a, ha⟩ => hb (ha ▸ cd.len_msg a)
  simp [decode, h]

end Codes

/-! ### The oracle with an instance word -/

/-- The oracle of the experiment with the secret of the selection drawn from `setupW w x` for the
instance word `w` kept in the state. -/
noncomputable def oracleW (sp : Spec U Sig) (setupW : List Bool → U.Attr → PMF Sig) :
    Fin 3 × List Bool → StateT (List Bool × GState U Sig) PMF (List Bool) := fun q st =>
  (oracle { sp with setup := setupW st.1 } q st.2).map fun r => (r.1, (st.1, r.2))

/-- The states the handlers serve: an admissible instance word (`IW`, at most `W` bits, not
starting with `false`) and either the initial experiment state or a selected one with an
admissible secret (`Ok`). -/
def InvS (IW : List Bool → Prop) (W : ℕ) (Ok : Sig → Prop) (st : List Bool × GState U Sig) : Prop :=
  IW st.1 ∧ st.1.length ≤ W ∧ st.1.head? ≠ some false ∧
    (st.2 = {} ∨ ∃ x σ, st.2.attr = some x ∧ st.2.sec = some σ ∧ Ok σ)

/-! ### The programs -/

section Programs

variable {R : ℕ}

/-- The glue tape `j`. -/
abbrev gt (j : Fin 8) : Fin (R + 8) := glueEmb j

/-- Do nothing. -/
def skipG : XProg (R + 8) := glue (.prim (.copy 0 0))

/-- `X := drop n (true :: b)` (the length test of the query `b` against `n`). -/
def lenPrep (n : ℕ) : Prog 8 :=
  .seq (.prim (.copy 3 0)) (.seq (.prim (.cons 3 true)) (Prog.dropN n 3))

/-- `succ` if the query has `n` bits, `fail` otherwise. -/
def testLen (n : ℕ) (succ fail : XProg (R + 8)) : XProg (R + 8) :=
  .seq (glue (lenPrep n)) (.ifBlank (gt 3) fail
    (.seq (glue (.prim (.tail 3))) (.ifBlank (gt 3) succ (.seq (glue (.prim (.clear 3))) fail))))

/-- `d := b` for a query `b` of `n` bits, through `X` (the syntactic bound of `d` is `n`). -/
def takeQ (n : ℕ) (d : Fin 8) : Prog 8 :=
  .seq (.prim (.copy 3 0)) (.seq (Prog.moveFront n 3 d 7) (.prim (.clear 3)))

variable (cd : Codes U Sig)

/-- The new selected state: `S := false^(nM+3) ++ b ++ S`. -/
def buildSel : Prog 8 :=
  .seq (.prim (.copy 3 0)) (.seq (Prog.prependN cd.nA 3 2 4 5) (Prog.consN (cd.nM + 3) 2 false))

/-- The selection, for a query `b = encAttr x` and the instance word `w` on the state tape. -/
def selCore (setupP pubP : XProg (R + 2)) : XProg (R + 8) :=
  .seq (glue (takeQ cd.nA 4))
    (.seq (comp 2 4 (by decide) setupP)
      (.seq (glue (.prim (.copy 1 2)))
        (.seq (comp 1 4 (by decide) pubP) (glue (buildSel cd)))))

/-- **The handler of the selection.** -/
def selH (setupP pubP : XProg (R + 2)) : XProg (R + 8) :=
  let init := testLen cd.nA (selCore cd setupP pubP) skipG
  .ifBit (gt 2) init (.ifBlank (gt 2) init skipG)

/-- Parse a selected state: `Y := [bad]`, `X := msgWord msg`, `Z := encAttr x`, `S := encSig σ`. -/
def parseSel : Prog 8 :=
  .seq (.prim (.tail 2)) (.seq (.prim (.pop 2 4))
    (.seq (Prog.moveFront (cd.nM + 1) 2 3 7) (Prog.moveFront cd.nA 2 5 7)))

/-- Rebuild the selected state from `Y`, `X`, `Z` and `S` (clearing `U` first). -/
def rebuildK : Prog 8 :=
  .seq (.prim (.clear 6)) (.seq (Prog.prependN cd.nA 5 2 6 7) (.seq (Prog.prependN (cd.nM + 1) 3 2 6 7)
    (.seq (.prim (.consHead 2 4)) (.seq (.prim (.clear 4)) (.prim (.cons 2 false))))))

/-- `Y := [true]`. -/
def setBad : Prog 8 := .seq (.prim (.clear 4)) (.prim (.cons 4 true))

/-- A key query on a selected state. -/
def keySel (keyP authP : XProg (R + 2)) : XProg (R + 8) :=
  .seq (glue (parseSel cd))
    (.seq (glue (.seq (.prim (.copy 1 2)) (.prim (.copy 6 0))))
      (.seq (comp 1 6 (by decide) keyP)
        (.seq (glue (.seq (.prim (.copy 6 0)) (.prim (.copy 7 5))))
          (.seq (comp 6 7 (by decide) authP)
            (.seq (.ifBit (gt 6) (glue setBad) skipG) (glue (rebuildK cd)))))))

/-- **The handler of the key queries.** -/
def keyH (keyP authP : XProg (R + 2)) : XProg (R + 8) :=
  .ifBit (gt 2) skipG (.ifBlank (gt 2) skipG (keySel cd keyP authP))

/-- Put back `bad` and the marker. -/
def restoreC : Prog 8 :=
  .seq (.prim (.consHead 2 4)) (.seq (.prim (.clear 4)) (.prim (.cons 2 false)))

/-- Parse the rest of a selected state with no message: `Z := encAttr x`, `S := encSig σ`. -/
def parseC : Prog 8 :=
  .seq (.prim (.tail 2)) (.seq (Prog.dropN cd.nM 2) (Prog.moveFront cd.nA 2 5 7))

/-- Rebuild the selected state with the message `b`. -/
def rebuildC : Prog 8 :=
  .seq (Prog.prependN cd.nA 5 2 6 7) (.seq (.prim (.copy 3 0)) (.seq (Prog.prependN cd.nM 3 2 6 7)
    (.seq (.prim (.cons 2 true)) (restoreC))))

/-- The challenge on a selected state with no message, for a query `b = encMsg μ`. -/
def chalFresh (chalP : XProg (R + 2)) : XProg (R + 8) :=
  .seq (glue (parseC cd))
    (.seq (glue (.seq (.prim (.copy 1 2)) (takeQ cd.nM 6)))
      (.seq (comp 1 6 (by decide) chalP) (glue (rebuildC cd))))

/-- The challenge on a selected state. -/
def chalSel (chalP : XProg (R + 2)) : XProg (R + 8) :=
  .seq (glue (.seq (.prim (.tail 2)) (.prim (.pop 2 4))))
    (.ifBit (gt 2) (glue restoreC) (testLen cd.nM (chalFresh cd chalP) (glue restoreC)))

/-- **The handler of the challenge.** -/
def chalH (chalP : XProg (R + 2)) : XProg (R + 8) :=
  .ifBit (gt 2) skipG (.ifBlank (gt 2) skipG (chalSel cd chalP))

end Programs

/-! ### The components -/

/-- The component programs and their laws: each maps its input words on its tapes `0`, `1` (its
`R` scratch tapes blank) to its output word on tape `0`, every other tape blank. -/
structure Comps (R : ℕ) (cd : Codes U Sig) (sp : Spec U Sig)
    (setupW : List Bool → U.Attr → PMF Sig) (IW : List Bool → Prop) (Ok : Sig → Prop) where
  /-- The secret from the instance word and the attribute. -/
  setupP : XProg (R + 2)
  /-- The public key from the secret. -/
  pubP : XProg (R + 2)
  /-- The answer to a key query from the secret and the query. -/
  keyP : XProg (R + 2)
  /-- The authorization bit from the query and the attribute. -/
  authP : XProg (R + 2)
  /-- The challenge from the secret and the message. -/
  chalP : XProg (R + 2)
  wf_setup : setupP.WF
  wf_pub : pubP.WF
  wf_key : keyP.WF
  wf_auth : authP.WF
  wf_chal : chalP.WF
  law_setup : ∀ w x, IW w → XProg.law setupP (io2 w (U.encAttr x) []) =
    (setupW w x).map fun σ => io2 (cd.sig.enc σ) [] []
  ok_setup : ∀ w x, IW w → ∀ σ ∈ (setupW w x).support, Ok σ
  law_pub : ∀ σ, Ok σ → XProg.law pubP (io2 (cd.sig.enc σ) [] []) = PMF.pure (io2 (sp.pub σ) [] [])
  law_key : ∀ σ C, Ok σ → XProg.law keyP (io2 (cd.sig.enc σ) C []) =
    (sp.key σ C).map fun sk => io2 sk [] []
  law_auth : ∀ C x, XProg.law authP (io2 C (U.encAttr x) []) = PMF.pure (io2 [sp.auth C x] [] [])
  law_chal : ∀ σ μ, Ok σ → XProg.law chalP (io2 (cd.sig.enc σ) (U.encMsg μ) []) =
    (sp.chal σ μ).map fun ct => io2 ct [] []

end AdvancedEncryption.PE.Generic
