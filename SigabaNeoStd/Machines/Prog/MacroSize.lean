import SigabaNeoStd.Machines.Prog.Macros
import SigabaNeoStd.Machines.Prog.FrameSize

/-!
# The state counts of the macros

`Prog.size` of the iterated macros of `Prog.Macros` (`iter`, `moveFront`, `moveRev`, `prependN`,
`consN`, `dropN`): each is affine in the iteration count. A primitive has `36` states, or `60`
when it pads (`cons`, `snoc`, `consHead`, `snocHead`).
-/

namespace SigabaNeo.Tape

namespace Prog

variable {k : ℕ}

@[simp] theorem size_prim (p : Prim k) : (prim p).size = (3 + 2 * p.pad) * 12 := rfl
@[simp] theorem size_coin (i : Fin k) : (coin i).size = 37 := rfl
@[simp] theorem size_seq (p q : Prog k) : (seq p q).size = p.size + q.size := rfl
@[simp] theorem size_ifBlank (i : Fin k) (p q : Prog k) :
    (ifBlank i p q).size = p.size + q.size + 1 := rfl
@[simp] theorem size_ifBit (i : Fin k) (p q : Prog k) :
    (ifBit i p q).size = p.size + q.size + 1 := rfl
@[simp] theorem size_loop (i : Fin k) (body : Prog k) : (loop i body).size = body.size + 39 := rfl

/-- **The states of an iteration**: `n` copies of the body and the final no-op. -/
@[simp] theorem size_iter (z : Fin k) (p : Prog k) : ∀ n, (iter z p n).size = n * p.size + 36
  | 0 => by simp [iter, Prim.pad]
  | n + 1 => by rw [iter, size_seq, size_iter z p n]; ring

@[simp] theorem size_stepF (src dst tmp : Fin k) : (stepF src dst tmp).size = 132 := by
  simp [stepF, Prim.pad]

@[simp] theorem size_stepR (src dst tmp : Fin k) : (stepR src dst tmp).size = 132 := by
  simp [stepR, Prim.pad]

@[simp] theorem size_moveFront (n : ℕ) (src dst tmp : Fin k) :
    (moveFront n src dst tmp).size = 132 * n + 36 := by
  simp [moveFront]; ring

@[simp] theorem size_moveRev (n : ℕ) (src dst tmp : Fin k) :
    (moveRev n src dst tmp).size = 132 * n + 36 := by
  simp [moveRev]; ring

@[simp] theorem size_prependN (n : ℕ) (src dst t₁ t₂ : Fin k) :
    (prependN n src dst t₁ t₂).size = 264 * n + 72 := by
  simp [prependN]; ring

@[simp] theorem size_consN (n : ℕ) (i : Fin k) (b : Bool) : (consN n i b).size = 60 * n + 36 := by
  simp [consN, Prim.pad]; ring

@[simp] theorem size_dropN (n : ℕ) (i : Fin k) : (dropN n i).size = 36 * n + 36 := by
  simp [dropN, Prim.pad]; ring

end Prog

end SigabaNeo.Tape
