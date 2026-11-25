import PE.Impl.ExpLUT.Prog.EncInit
import PE.Impl.ExpLUT.Prog.EncCoins

/-! # Fixed-length normalization of the encryption input queues -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog
open PE.BranchingProgram

/-- Copy exactly `n` bits through a fixed-width carry sweep, padding with false when needed. -/
def trimP {k : ℕ} (src tmp : Fin k) (n : ℕ) : SigabaNeo.Tape.Prog k :=
  .seq (putW tmp (List.replicate n false))
    (.seq (.prim (.carry takeOp tmp src)) (.seq (cp src tmp) (clr tmp)))

theorem run_trimP {k : ℕ} (src tmp : Fin k) (hne : src ≠ tmp) (n : ℕ) (S : Store k) :
    (trimP src tmp n).run S = Function.update (Function.update S src (takeD n (S src))) tmp [] := by
  simp only [trimP, Prog.run_seq, run_putW, run_prim, Prim.apply, cp, clr,
    Function.update_self, Function.update_of_ne hne, carryOp_takeOp, List.length_replicate]
  funext i
  by_cases ht : i = tmp <;> by_cases hs : i = src <;> simp_all

theorem wf_trimP {k : ℕ} (src tmp : Fin k) (n : ℕ) : (trimP src tmp n).WF :=
  ⟨wf_putW _ _, trivial, trivial, trivial⟩

theorem coinFree_trimP {k : ℕ} (src tmp : Fin k) (n : ℕ) : (trimP src tmp n).CoinFree := by
  simpa only [trimP, CoinFree, coinFreeB, Bool.and_eq_true, and_true] using coinFree_putW tmp _

theorem lenBoundT_trimP {k : ℕ} (src tmp : Fin k) (n : ℕ) (ℓ : Fin k → ℕ) :
    lenBoundT (trimP src tmp n) ℓ = Function.update (Function.update ℓ src n) tmp 0 := by
  simp only [trimP, lenBoundT, lenBoundT_putW, List.length_replicate, Prim.lenT, Function.update_self]
  funext i
  by_cases ht : i = tmp <;> by_cases hs : i = src <;> simp_all

noncomputable def coinLength (D : Dims) : ℕ := D.N * D.K +
  (fixedSize (vecE D (BCol (Wb D) D.K)) +
    (fixedSize (matE D (Jh D) (Col D.K)) +
      (fixedSize (floodEnc D) + D.N * D.K)))

def publicLength (D : Dims) : ℕ := fixedSize (mpkEnc D) + 129

theorem length_encCoinWord (D : Dims) (r : EncCoins (setting D) (Wb D) (Jh D) Pos) :
    (encCoinWord D r).length = coinLength D := by
  simp only [encCoinWord, List.length_append,
    (vecE D (BCol (Wb D) D.K)).length r.eb, (matE D (Jh D) (Col D.K)).length r.eh,
    FixedEnc.length, coinLength, fixedSize]

theorem length_publicWord (D : Dims) (mpk : MPKt D) (x : Attribute w8) (μ : Bool) :
    ((mpkEnc D).enc mpk ++ (encAttribute w8 x ++ [μ])).length = publicLength D := by
  simp only [List.length_append, FixedEnc.length, length_encAttribute, List.length_cons,
    List.length_nil, publicLength, fixedSize]

end AdvancedEncryption.ExpLUT.Prog.EncW
