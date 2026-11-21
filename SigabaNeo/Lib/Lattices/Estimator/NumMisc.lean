import SigabaNeo.Lib.Lattices.Estimator.Params

/-! Numerics shared by the guessing, Gröbner-basis and coded-BKW estimates.
Gaussian widths use the upstream default constructor's unbounded support. -/
namespace SigabaNeo.Lattices.Estimator.NumMisc
open Fx

def width (x : ND) : Fx :=
  match x.kind with
  | .gauss s => 8 * mul SQRT2PI s + 3 * ONE
  | _ => let (a,b) := x.bounds.getD (0,0); ofInt (b-a+1)

def tail (x : ND) : Fx :=
  match x.kind with
  | .gauss _ => ONE - 2 * exp (-4 * PI)
  | _ => ONE

def repeatBits (logp : Fx) : Fx :=
  if logp ≥ log2 (ofRat 99 100) then 0
  else if logp < -40 * ONE then log2 (ln (100 * ONE)) - logp
  else log2Nat (ceil (div (-(ln (100 * ONE))) (ln (ONE - exp2 logp)))).toNat

/-- Upstream precision-one local_minimum iterator. -/
def search {α : Type} (start stop : ℕ) (eval : ℕ → α) (smaller : α → α → Bool) : Option α := Id.run do
  let mut lo : Int := start
  let mut hi : Int := (stop : Int) - 1
  let mut x := hi
  let mut dir : Int := -1
  let mut best := none
  let mut seen : List Int := []
  for _ in [:stop-start] do
    if x < (start : Int) || x ≥ (stop : Int) || seen.contains x then break
    seen := x :: seen
    let y := eval x.toNat
    if best.all (smaller y) then
      best := some y
      if dir.natAbs == 2 then
        x := x-1
        dir := -1
      else if dir == -1 then
        hi := x
        x := (lo+hi+1)/2
        dir := -2
      else
        lo := x
        x := (lo+hi)/2
        dir := 2
    else if dir == -1 then
      x := x+2
      dir := 1
    else if dir == 1 then break
    else if dir == -2 then
      lo := x
      x := (lo+hi+1)/2
    else
      hi := x
      x := (lo+hi)/2
  return best
end SigabaNeo.Lattices.Estimator.NumMisc
