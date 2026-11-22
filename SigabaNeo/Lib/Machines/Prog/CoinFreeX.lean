import SigabaNeo.Lib.Machines.Prog.Frame
import SigabaNeo.Lib.Machines.Prog.Pass

/-!
# Coin-free framed programs

`XProg.CoinFree p`: no leaf of `p` draws a coin (`Prog.CoinFree` on every leaf). Such a program
has a point-mass law (`law_eq_pure_of_coinFree`), and its compiled machine ignores the coin.
-/

namespace SigabaNeo.Tape

namespace XProg

/-- The syntactic test: no leaf draws a coin. -/
def coinFreeB : {k : ℕ} → XProg k → Bool
  | _, prog p => p.coinFreeB
  | _, frame _ p => coinFreeB p
  | _, seq p q => coinFreeB p && coinFreeB q
  | _, ifBlank _ p q => coinFreeB p && coinFreeB q
  | _, ifBit _ p q => coinFreeB p && coinFreeB q
  | _, loop _ body => coinFreeB body

/-- `p` draws no coin. -/
def CoinFree {k : ℕ} (p : XProg k) : Prop := p.coinFreeB = true

theorem coinFree_prog {k : ℕ} {p : Prog k} (h : p.CoinFree) : (prog p).CoinFree := h

theorem coinFree_frame {k m : ℕ} (e : Fin m ↪ Fin k) {p : XProg m} (h : p.CoinFree) :
    (frame e p).CoinFree := h

theorem coinFree_seq {k : ℕ} {p q : XProg k} (hp : p.CoinFree) (hq : q.CoinFree) :
    (seq p q).CoinFree := by
  simp only [CoinFree, coinFreeB, Bool.and_eq_true] at *; exact ⟨hp, hq⟩

theorem coinFree_ifBlank {k : ℕ} (i : Fin k) {p q : XProg k} (hp : p.CoinFree)
    (hq : q.CoinFree) : (ifBlank i p q).CoinFree := by
  simp only [CoinFree, coinFreeB, Bool.and_eq_true] at *; exact ⟨hp, hq⟩

theorem coinFree_ifBit {k : ℕ} (i : Fin k) {p q : XProg k} (hp : p.CoinFree)
    (hq : q.CoinFree) : (ifBit i p q).CoinFree := by
  simp only [CoinFree, coinFreeB, Bool.and_eq_true] at *; exact ⟨hp, hq⟩

theorem coinFree_loop {k : ℕ} (i : Fin k) {body : XProg k} (h : body.CoinFree) :
    (loop i body).CoinFree := h

end XProg

end SigabaNeo.Tape
