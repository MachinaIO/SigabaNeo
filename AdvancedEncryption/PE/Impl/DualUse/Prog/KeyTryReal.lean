import PE.Impl.DualUse.Prog.KeyTrySimLaw
import PE.Impl.DualUse.Algo.KeyTry
import SigabaNeo.Lib.Lattices.ProgAlgo.SimJoint

/-!
# One try of key generation with the real trapdoor, as a tape program

`keyTryRP : Prog 101` computes one try of `KeyGen` (`Algo.keyTryCoreW` with the predicate in the
class) from the words of the public key, of the trapdoor `(e, t)`, of the key row `B_f̂` and of the
coins (`run_keyTryRP`, `keyTryRW_eq_core`). It reuses the phases `ph1` (the blocks of the public
key, the big-box element), `ph2` (the decomposition `z`) and `ph4` (the output) of the simulated
try (`ProgKey`, relabelled onto the first `90` tapes), with a new third phase `ph3R`:

* `94 := G̲`, `95 := B_f̂ − G̲`, `96 := G̲⁻¹(B_f̂ − G̲)`, `97 := y = G̲⁻¹(B_f̂ − G̲) z`;
* `98 := e · y`, `99 := t y`, `38 := T = (e · y, t y, y)`;
* `39 := x = p − (0, T)`, `40 := [x ∈ ball]`.

Tapes: as `keyTrySimP` (`0` output, `1` public key, `2` the word of `B_f̂`, `3` coins, `4` the radius,
`5` `powW K (B − 1)`, `6 … 25` templates, `26 … 40` work, `41 … 89` scratch), and `90` the word of
`e`, `91` the word of `t`, templates `92` (`2k · N`), `93` (`2k · 2k · N · K`), `100` (`2k`), work
`94 … 99`.
-/

namespace AdvancedEncryption.DualUse.ProgKeyR

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.DualUse.Algo AdvancedEncryption.DualUse.ProgKey Matrix
open scoped SigabaNeo.Tape.Prog

variable {N K k : ℕ}

/-! ### The word algorithm -/

/-- **One try of key generation with the real trapdoor, on words**, in the form of the program. -/
def keyTryRW (N K k d B : ℕ) (sW pkW eW tW bfW l : List Bool) : List Bool :=
  let pW := embW ((d + nT k) * N) B K l
  let zW := decW N K k (subRW N K (pkW.drop (pkW.length - N * K))
    (shortMapW N K d (nT k) (pkW.take (d * (N * K)))
      ((pkW.drop (d * (N * K))).take (nT k * (N * K))) pW))
  let yW := matMulW N K (2 * k) (2 * k) 1
    (ginvW N K k (matSubW N K (1 * (2 * k)) bfW (gadW N K k))) zW
  let TW := matMulW N K 1 (2 * k) 1 eW yW ++ (matMulW N K 1 1 (2 * k) tW yW ++ yW)
  let xW := matSubW N K (d + nT k) pW (zeroW (d * (N * K)) ++ TW)
  pkW ++ if ballW ((d + nT k) * N) K sW xW = true then xW ++ zW
    else zeroW (d * (N * K)) ++ (zeroW (nT k * (N * K)) ++ zeroW (2 * k * (N * K)))

theorem matSubW_append {a b : ℕ} {x₁ x₂ y₁ y₂ : List Bool} (hx : x₁.length = a * (N * K))
    (hy : y₁.length = a * (N * K)) :
    matSubW N K (a + b) (x₁ ++ x₂) (y₁ ++ y₂) = matSubW N K a x₁ y₁ ++ matSubW N K b x₂ y₂ := by
  rw [matSubW, Algo.concatN_add]
  congr 1
  · apply concatN_congr
    intro i hi
    have h1 : rget N K i (x₁ ++ x₂) = rget N K i x₁ := by
      simp only [rget, block, List.drop_append, hx]
      rw [List.take_append_of_le_length (by
        have := Nat.mul_le_mul_right (N * K) (show i + 1 ≤ a by omega)
        rw [Nat.succ_mul] at this; simp [hx]; omega)]
    have h2 : rget N K i (y₁ ++ y₂) = rget N K i y₁ := by
      simp only [rget, block, List.drop_append, hy]
      rw [List.take_append_of_le_length (by
        have := Nat.mul_le_mul_right (N * K) (show i + 1 ≤ a by omega)
        rw [Nat.succ_mul] at this; simp [hy]; omega)]
    rw [h1, h2]
  · apply concatN_congr
    intro i hi
    have h1 : rget N K (a + i) (x₁ ++ x₂) = rget N K i x₂ := by
      simp only [rget, block]
      rw [show (a + i) * (N * K) = x₁.length + i * (N * K) by rw [hx]; ring, ← List.drop_drop,
        List.drop_left]
    have h2 : rget N K (a + i) (y₁ ++ y₂) = rget N K i y₂ := by
      simp only [rget, block]
      rw [show (a + i) * (N * K) = y₁.length + i * (N * K) by rw [hy]; ring, ← List.drop_drop,
        List.drop_left]
    rw [h1, h2]

theorem matSubW_zero {a : ℕ} {x : List Bool} (hx : x.length = a * (N * K)) :
    matSubW N K a x (zeroW (a * (N * K))) = x := by
  conv_rhs => rw [← concatN_block (n := a) (K := N * K) hx]
  rw [matSubW]
  apply concatN_congr
  intro i hi
  have hb : (rget N K i x).length = N * K := length_block (N := a) hx hi
  have hz : rget N K i (zeroW (a * (N * K))) = zeroW (N * K) := by
    simp only [rget, block, zeroW, List.drop_replicate, List.take_replicate]
    congr 1
    have : (i + 1) * (N * K) ≤ a * (N * K) := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this
    omega
  rw [hz, ← enc_zeroR N K, ← enc_decR hb, subRW_enc, sub_zero, enc_decR hb]
  rfl

/-- **The word algorithm is one try of `KeyGen`** (`keyTryCoreW` with the predicate in the class),
for words of the right lengths. -/
theorem keyTryRW_eq_core {d B : ℕ} (sW pkW eW tW bfW l : List Bool)
    (ht : tW.length = N * K) :
    keyTryRW N K k d B sW pkW eW tW bfW l = keyTryCoreW N K k d B sW true pkW eW tW bfW l := by
  have hp : (embW ((d + nT k) * N) B K l).length = (d + nT k) * N * K := length_embW _ _ _ _
  have hx : ∀ T : List Bool, T.length = nT k * (N * K) →
      matSubW N K (d + nT k) (embW ((d + nT k) * N) B K l) (zeroW (d * (N * K)) ++ T) =
        subShiftW N K d (nT k) (embW ((d + nT k) * N) B K l) T := by
    intro T hT
    have e : embW ((d + nT k) * N) B K l = (embW ((d + nT k) * N) B K l).take (d * (N * K)) ++
        (embW ((d + nT k) * N) B K l).drop (d * (N * K)) := (List.take_append_drop _ _).symm
    rw [subShiftW]
    conv_lhs => rw [e]
    rw [matSubW_append (by rw [List.length_take, hp]; apply min_eq_left; nlinarith)
      (by simp [zeroW]), matSubW_zero (by rw [List.length_take, hp]; apply min_eq_left; nlinarith)]
  have hT : ∀ y : List Bool, (matMulW N K 1 (2 * k) 1 eW y ++ (matMulW N K 1 1 (2 * k) tW y ++ y)) =
      dotW N K (2 * k) eW y ++ (smulVW N K (2 * k) tW y ++ y) := by
    intro y
    rw [← dotW_eq_matMulW, matMulW_one_one _ ht]
    rfl
  unfold keyTryRW keyTryCoreW trapShiftW
  dsimp only
  rw [hT, hx _ (by
    rw [List.length_append, List.length_append]
    simp only [dotW, length_sumLoop, length_matMulW, smulVW]
    rw [length_concatN (K := N * K) (fun i _ => length_mulRW N K _ _)]
    simp [nT]; ring), Bool.true_and]

/-! ### Placements on `101` tapes -/

/-- The first `90` tapes. -/
def ι : Fin 90 → Fin 101 := fun i => ⟨i.val, by omega⟩

theorem ι_inj : Function.Injective ι := fun a b h => Fin.ext (by simpa [ι] using h)

/-- Arguments `v`, scratch at `off`. -/
def plR {n : ℕ} (c off : ℕ) (v : Fin c → Fin 101) (h : n + off ≤ 90) : Fin n → Fin 101 :=
  fun i => if hi : i.val < c then v ⟨i.val, hi⟩ else ⟨i.val + off, by omega⟩

/-- Scratch is blank. -/
def Scr (t : Store 101) : Prop := ∀ j : Fin 101, 41 ≤ j.val → j.val < 90 → t j = []

theorem plR_scratch {n c off : ℕ} {v : Fin c → Fin 101} {h : n + off ≤ 90} {t : Store 101}
    (ht : Scr t) (hoff : 41 ≤ c + off) (b : ℕ) (hb : c ≤ b) :
    ∀ i : Fin n, b ≤ i.val → t (plR c off v h i) = [] := by
  intro i hi
  apply ht
  · simp only [plR, dite_cond_eq_false (eq_false (show ¬ i.val < c by omega))]; show 41 ≤ i.val + off
    omega
  · simp only [plR, dite_cond_eq_false (eq_false (show ¬ i.val < c by omega))]; show i.val + off < 90
    omega

theorem Scr.upd {t : Store 101} (ht : Scr t) {i : Fin 101} (hi : i.val < 41 ∨ 90 ≤ i.val)
    (w : List Bool) : Scr (Function.update t i w) := by
  intro j h1 h2
  rw [Function.update_of_ne (by rintro rfl; omega)]
  exact ht j h1 h2

def gadR : Fin 21 → Fin 101 := plR 6 35 ![94, 6, 7, 8, 12, 20] (by norm_num)
def subR : Fin 28 → Fin 101 := plR 5 36 ![95, 2, 94, 6, 92] (by norm_num)
def ginvR : Fin 35 → Fin 101 := plR 6 35 ![96, 95, 6, 92, 12, 93] (by norm_num)
def mmR (o x y m n l O : Fin 101) : Fin 59 → Fin 101 :=
  plR 10 31 ![o, x, y, 6, 7, 8, m, n, l, O] (by norm_num)
def mvR (a b c : Fin 101) : Fin 5 → Fin 101 := ![a, b, 41, 42, c]
def bzR (o x y a b : Fin 101) : Fin 28 → Fin 101 := plR 5 36 ![o, x, y, a, b] (by norm_num)
def ballR : Fin 23 → Fin 101 := plR 6 35 ![40, 39, 4, 6, 10, 14] (by norm_num)

theorem run_gadR (t : Store 101) (ht : Scr t) {K N k : ℕ} (hK : (t 6).length = K)
    (hN : (t 7).length = N) (hNK : (t 8).length = N * K) (hk : (t 12).length = k)
    (hO : (t 20).length = 2 * k * (N * K)) :
    run (map gadR gadP) t = Function.update t 94 (gadW N K k) :=
  run_gadP_map (by decide) t (fun i hi => plR_scratch ht (by norm_num) 6 le_rfl i hi) hK hN hNK hk hO

theorem run_bzR {o x y a b : Fin 101} (hu : Function.Injective (bzR o x y a b)) (t : Store 101)
    (ht : Scr t) {K N L : ℕ} (hK : (t a).length = K) (hLN : (t b).length = L * N)
    (hx : (t x).length = L * N * K) (hy : (t y).length = L * N * K) :
    run (map (bzR o x y a b) subRWP) t = Function.update t o (matSubW N K L (t x) (t y)) :=
  run_subRWP_mat_map hu t (fun i hi => plR_scratch ht (by norm_num) 5 le_rfl i hi) hK hLN hx hy

theorem run_ginvR (t : Store 101) (ht : Scr t) {K N k : ℕ} (hK : (t 6).length = K)
    (hB : (t 92).length = 2 * k * N) (hk : (t 12).length = k)
    (hO : (t 93).length = 2 * k * (2 * k * (N * K))) (hb : (t 95).length = 2 * k * (N * K)) :
    run (map ginvR ginvP) t = Function.update t 96 (ginvW N K k (t 95)) :=
  run_ginvP_map (by decide) t (fun i hi => plR_scratch ht (by norm_num) 6 le_rfl i hi) hK hB hk hO hb

theorem run_mmR {o x y m n l O : Fin 101} (hu : Function.Injective (mmR o x y m n l O))
    (t : Store 101) (ht : Scr t) {K N m' n' l' : ℕ} (hK : (t 6).length = K)
    (hN : (t 7).length = N) (hNK : (t 8).length = N * K) (hm : (t m).length = m')
    (hn : (t n).length = n') (hl : (t l).length = l') (hO : (t O).length = m' * l' * (N * K))
    (hx : (t x).length = m' * n' * (N * K)) (hy : (t y).length = n' * l' * (N * K)) :
    run (map (mmR o x y m n l O) matMulP) t = Function.update t o (matMulW N K m' n' l' (t x) (t y)) :=
  run_matMulP_map hu t (fun i hi => plR_scratch ht (by norm_num) 10 le_rfl i hi) hK hN hNK hm hn hl
    hO hx hy

theorem run_mvR {a b c : Fin 101} (hu : Function.Injective (mvR a b c)) (t : Store 101)
    (ht : Scr t) :
    run (map (mvR a b c) mvP) t = Function.update (Function.update t a ((t a).drop (t c).length)) b
      ((t b ++ takeD (t c).length (t a)).drop (t c).length) :=
  run_mvP_map hu t (ht 41 (by decide) (by decide)) (ht 42 (by decide) (by decide))

theorem run_ballR (t : Store 101) (ht : Scr t) {n K : ℕ} (hK0 : 0 < K)
    (hw : (t 39).length = n * K) (hS : (t 4).length = K) (hK : (t 6).length = K)
    (hn : (t 10).length = n) (h1 : (t 14).length = 1) :
    run (map ballR ballP) t = Function.update t 40 [ballW n K (t 4) (t 39)] :=
  run_ballP_map (by decide) hK0 t (fun i hi => plR_scratch ht (by norm_num) 6 le_rfl i hi) hw hS hK
    hn h1

/-! ### Phase 3 -/

/-- **The real shift, the shifted key and the ball test.** -/
def ph3R : Prog 101 :=
  map gadR gadP ⨾ map subR subRWP ⨾ map ginvR ginvP ⨾ map (mmR 97 96 36 13 100 15 20) matMulP ⨾
    map (mmR 98 90 97 14 13 15 29) matMulP ⨾ map (mmR 99 91 97 14 15 13 20) matMulP ⨾
    cp 38 19 ⨾ map (mvR 98 38 29) mvP ⨾ map (mvR 99 38 20) mvP ⨾ map (mvR 97 38 20) mvP ⨾
    cp 37 11 ⨾ setZero 37 ⨾ map (mvR 38 37 19) mvP ⨾ map (bzR 39 30 37 6 10) subRWP ⨾
    map ballR ballP

set_option maxHeartbeats 4000000 in
theorem run_ph3R {d : ℕ} (hK0 : 0 < K) (t : Store 101) (hs : Scr t)
    (h37 : t 37 = []) (h38 : t 38 = [])
    (hbf : (t 2).length = 2 * k * (N * K)) (hS : (t 4).length = K)
    (hK : (t 6).length = K) (hN : (t 7).length = N) (hNK : (t 8).length = N * K)
    (hn : (t 10).length = (d + nT k) * N) (hnK : (t 11).length = (d + nT k) * N * K)
    (hk : (t 12).length = k)
    (h13 : (t 13).length = 2 * k) (h14 : (t 14).length = 1) (h15 : (t 15).length = 1)
    (h19 : (t 19).length = nT k * (N * K))
    (h20 : (t 20).length = 2 * k * (N * K)) (h29 : (t 29).length = N * K)
    (hp : (t 30).length = (d + nT k) * N * K) (hz : (t 36).length = 2 * k * (N * K))
    (he : (t 90).length = 2 * k * (N * K)) (htt : (t 91).length = N * K)
    (h92 : (t 92).length = 2 * k * N) (h93 : (t 93).length = 2 * k * (2 * k * (N * K)))
    (h100 : (t 100).length = 2 * k) :
    let gW := gadW N K k
    let DW := matSubW N K (1 * (2 * k)) (t 2) gW
    let yW := matMulW N K (2 * k) (2 * k) 1 (ginvW N K k DW) (t 36)
    let xW := matSubW N K (d + nT k) (t 30) (zeroW (d * (N * K)) ++
      (matMulW N K 1 (2 * k) 1 (t 90) yW ++ (matMulW N K 1 1 (2 * k) (t 91) yW ++ yW)))
    run ph3R t = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update t 94 gW) 95 DW) 96 (ginvW N K k DW)) 97 []) 98 []) 99 []) 38 [])
        37 (zeroW (d * (N * K)) ++ (matMulW N K 1 (2 * k) 1 (t 90) yW ++
          (matMulW N K 1 1 (2 * k) (t 91) yW ++ yW)))) 39 xW) 40 [ballW ((d + nT k) * N) K (t 4) xW] := by
  intro gW DW yW xW
  have hgl : gW.length = 2 * k * (N * K) := length_gadW N K k
  have hDl : DW.length = 2 * k * (N * K) := by
    rw [length_matSubW (by rw [hbf]; ring)]; ring
  have hyl : yW.length = 2 * k * (N * K) := by rw [length_matMulW]; ring
  set A := matMulW N K 1 (2 * k) 1 (t 90) yW with hA
  set B := matMulW N K 1 1 (2 * k) (t 91) yW with hB
  have hAl : A.length = N * K := by rw [hA, length_matMulW]; ring
  have hBl : B.length = 2 * k * (N * K) := by rw [hB, length_matMulW]; ring
  set TW := A ++ (B ++ yW) with hTW
  have hTl : TW.length = nT k * (N * K) := by
    rw [hTW, List.length_append, List.length_append, hAl, hBl, hyl]; simp [nT]; ring
  -- the products
  set u1 := Function.update t 94 gW with hu1
  have s1 : run (map gadR gadP) t = u1 := run_gadR (K := K) (N := N) (k := k) t hs hK hN hNK hk h20
  have hs1 : Scr u1 := hs.upd (by decide) _
  set u2 := Function.update u1 95 DW with hu2
  have s2 : run (map subR subRWP) u1 = u2 :=
    run_bzR (K := K) (N := N) (L := 1 * (2 * k)) (by decide) u1 hs1
      (by simp [hu1, hK]) (by simp [hu1, h92]) (by simp [hu1, hbf]; ring) (by simp [hu1, hgl]; ring)
  have hs2 : Scr u2 := hs1.upd (by decide) _
  set u3 := Function.update u2 96 (ginvW N K k DW) with hu3
  have s3 : run (map ginvR ginvP) u2 = u3 := by
    rw [run_ginvR (K := K) (N := N) (k := k) u2 hs2 (by simp [hu2, hu1, hK]) (by simp [hu2, hu1, h92]) (by simp [hu2, hu1, hk])
      (by simp [hu2, hu1, h93]) (by simp [hu2, hDl])]
    show _ = Function.update u2 96 (ginvW N K k DW)
    congr 1
  have hs3 : Scr u3 := hs2.upd (by decide) _
  set u4 := Function.update u3 97 yW with hu4
  have s4 : run (map (mmR 97 96 36 13 100 15 20) matMulP) u3 = u4 := by
    rw [run_mmR (K := K) (N := N) (m' := 2 * k) (n' := 2 * k) (l' := 1) (by decide) u3 hs3
      (by simp [hu3, hu2, hu1, hK]) (by simp [hu3, hu2, hu1, hN]) (by simp [hu3, hu2, hu1, hNK])
      (by simp [hu3, hu2, hu1, h13]) (by simp [hu3, hu2, hu1, h100]) (by simp [hu3, hu2, hu1, h15])
      (by simp [hu3, hu2, hu1, h20]) (by simp [hu3, length_ginvW]; ring)
      (by simp [hu3, hu2, hu1, hz])]
    show _ = Function.update u3 97 yW
    congr 1
  have hs4 : Scr u4 := hs3.upd (by decide) _
  set u5 := Function.update u4 98 A with hu5
  have s5 : run (map (mmR 98 90 97 14 13 15 29) matMulP) u4 = u5 := by
    rw [run_mmR (K := K) (N := N) (m' := 1) (n' := 2 * k) (l' := 1) (by decide) u4 hs4
      (by simp [hu4, hu3, hu2, hu1, hK]) (by simp [hu4, hu3, hu2, hu1, hN])
      (by simp [hu4, hu3, hu2, hu1, hNK]) (by simp [hu4, hu3, hu2, hu1, h14])
      (by simp [hu4, hu3, hu2, hu1, h13]) (by simp [hu4, hu3, hu2, hu1, h15])
      (by simp [hu4, hu3, hu2, hu1, h29]) (by simp [hu4, hu3, hu2, hu1, he])
      (by simp [hu4, hyl])]
    show _ = Function.update u4 98 A
    congr 1
  have hs5 : Scr u5 := hs4.upd (by decide) _
  set u6 := Function.update u5 99 B with hu6
  have s6 : run (map (mmR 99 91 97 14 15 13 20) matMulP) u5 = u6 := by
    rw [run_mmR (K := K) (N := N) (m' := 1) (n' := 1) (l' := 2 * k) (by decide) u5 hs5
      (by simp [hu5, hu4, hu3, hu2, hu1, hK]) (by simp [hu5, hu4, hu3, hu2, hu1, hN])
      (by simp [hu5, hu4, hu3, hu2, hu1, hNK]) (by simp [hu5, hu4, hu3, hu2, hu1, h14])
      (by simp [hu5, hu4, hu3, hu2, hu1, h15]) (by simp [hu5, hu4, hu3, hu2, hu1, h13])
      (by simp [hu5, hu4, hu3, hu2, hu1, h20]) (by simp [hu5, hu4, hu3, hu2, hu1, htt])
      (by simp [hu5, hu4, hyl])]
    show _ = Function.update u5 99 B
    congr 1
  have hs6 : Scr u6 := hs5.upd (by decide) _
  -- the shift `T`, shifted into the register `38`
  set u7 := Function.update u6 38 (t 19) with hu7
  have hs7 : Scr u7 := hs6.upd (by decide) _
  set u8 := Function.update (Function.update u7 98 []) 38 ((t 19 ++ A).drop (N * K)) with hu8
  have s8 : run (map (mvR 98 38 29) mvP) u7 = u8 := by
    rw [run_mvR (by decide) u7 hs7]
    have a98 : u7 98 = A := by simp [hu7, hu6, hu5]
    have a29 : u7 29 = t 29 := by simp [hu7, hu6, hu5, hu4, hu3, hu2, hu1]
    have a38 : u7 38 = t 19 := by simp [hu7]
    rw [a98, a29, a38, h29, takeD_of_length' hAl, List.drop_eq_nil_of_le (le_of_eq hAl)]
  have hs8 : Scr u8 := (hs7.upd (by decide) _).upd (by decide) _
  set u9 := Function.update (Function.update u8 99 []) 38
    (((t 19 ++ A).drop (N * K) ++ B).drop (2 * k * (N * K))) with hu9
  have s9 : run (map (mvR 99 38 20) mvP) u8 = u9 := by
    rw [run_mvR (by decide) u8 hs8]
    have a99 : u8 99 = B := by simp [hu8, hu7, hu6]
    have a20 : u8 20 = t 20 := by simp [hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1]
    have a38 : u8 38 = (t 19 ++ A).drop (N * K) := by simp [hu8]
    rw [a99, a20, a38, h20, takeD_of_length' hBl, List.drop_eq_nil_of_le (le_of_eq hBl)]
  have hs9 : Scr u9 := (hs8.upd (by decide) _).upd (by decide) _
  have hT : ((((t 19 ++ A).drop (N * K) ++ B).drop (2 * k * (N * K))) ++ yW).drop
      (2 * k * (N * K)) = TW := by
    have e1 := drop_append_drop (t 19) A B
    rw [hAl, hBl] at e1
    have e2 := drop_append_drop (t 19) (A ++ B) yW
    rw [List.length_append, hAl, hBl, hyl] at e2
    rw [e1, e2, List.drop_left' (show (t 19).length = N * K + 2 * k * (N * K) + 2 * k * (N * K) by
      rw [h19]; simp [nT]; ring), List.append_assoc]
  set u10 := Function.update (Function.update u9 97 []) 38 TW with hu10
  have s10 : run (map (mvR 97 38 20) mvP) u9 = u10 := by
    rw [run_mvR (by decide) u9 hs9]
    have a97 : u9 97 = yW := by simp [hu9, hu8, hu7, hu6, hu5, hu4]
    have a20 : u9 20 = t 20 := by simp [hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1]
    have a38 : u9 38 = ((t 19 ++ A).drop (N * K) ++ B).drop (2 * k * (N * K)) := by simp [hu9]
    rw [a97, a20, a38, h20, takeD_of_length' hyl, List.drop_eq_nil_of_le (le_of_eq hyl), hT]
  have hs10 : Scr u10 := (hs9.upd (by decide) _).upd (by decide) _
  -- `x = p − (0, T)`
  set ZT := zeroW (d * (N * K)) ++ TW with hZT
  set u11 := Function.update u10 37 (zeroW ((d + nT k) * N * K)) with hu11
  have hs11 : Scr u11 := hs10.upd (by decide) _
  set u12 := Function.update (Function.update u11 38 []) 37 ZT with hu12
  have s12 : run (map (mvR 38 37 19) mvP) u11 = u12 := by
    rw [run_mvR (by decide) u11 hs11]
    have a38 : u11 38 = TW := by simp [hu11, hu10]
    have a19 : u11 19 = t 19 := by simp [hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1]
    have a37 : u11 37 = zeroW ((d + nT k) * N * K) := by simp [hu11]
    rw [a38, a19, a37, h19, takeD_of_length' hTl, List.drop_eq_nil_of_le (le_of_eq hTl)]
    congr 1
    rw [hZT, zeroW, zeroW, show (d + nT k) * N * K = nT k * (N * K) + d * (N * K) by ring,
      ← List.replicate_append_replicate, List.append_assoc,
      List.drop_left' (List.length_replicate ..)]
  have hs12 : Scr u12 := (hs11.upd (by decide) _).upd (by decide) _
  have hZl : ZT.length = (d + nT k) * N * K := by
    rw [hZT, List.length_append, hTl, zeroW, List.length_replicate]; ring
  set u13 := Function.update u12 39 xW with hu13
  have s13 : run (map (bzR 39 30 37 6 10) subRWP) u12 = u13 := by
    rw [run_bzR (K := K) (N := N) (L := d + nT k) (by decide) u12 hs12
      (by simp [hu12, hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1, hK])
      (by simp [hu12, hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1, hn])
      (by simp [hu12, hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1, hp])
      (by simp [hu12, hZl])]
    show _ = Function.update u12 39 xW
    congr 1
  have hs13 : Scr u13 := hs12.upd (by decide) _
  have hxl : xW.length = (d + nT k) * N * K := by
    show (matSubW N K (d + nT k) _ _).length = _
    rw [length_matSubW (by rw [hp]; ring)]; ring
  have s14 : run (map ballR ballP) u13 = Function.update u13 40
      [ballW ((d + nT k) * N) K (t 4) xW] := by
    rw [run_ballR (n := (d + nT k) * N) u13 hs13 hK0 (by simp [hu13, hxl])
      (by simp [hu13, hu12, hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1, hS])
      (by simp [hu13, hu12, hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1, hK])
      (by simp [hu13, hu12, hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1, hn])
      (by simp [hu13, hu12, hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1, h14])]
    simp [hu13, hu12, hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1]
  simp only [ph3R, run_seq, run_copy, run_setZero]
  have c7 : Function.update u6 38 (u6 19) = u7 := by
    simp [hu7, hu6, hu5, hu4, hu3, hu2, hu1]
  have c11 : Function.update u10 37 (List.replicate (Function.update u10 37 (u10 11) 37).length
      false) = u11 := by
    simp [hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1, hnK, zeroW]
  rw [s1, s2, s3, s4, s5, s6, c7, s8, s9, s10, Function.update_idem, c11, s12, s13, s14]
  funext j
  fin_cases j <;> simp [hu13, hu12, hu11, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1]

/-! ### The whole try -/

/-- **One try of key generation with the real trapdoor**, as a tape program. -/
def keyTryRP : Prog 101 :=
  map ι (ph1 ⨾ ph2) ⨾ ph3R ⨾ map ι ph4 ⨾ clr 94 ⨾ clr 95 ⨾ clr 96

theorem extend_ι (v : Store 90) (s : Store 101) :
    Function.extend ι v s = fun j => if h : j.val < 90 then v ⟨j.val, h⟩ else s j := by
  funext j
  by_cases h : j.val < 90
  · rw [dif_pos h]
    have e : j = ι ⟨j.val, h⟩ := rfl
    conv_lhs => rw [e]
    exact ι_inj.extend_apply v s _
  · rw [dif_neg h, Function.extend_apply']
    rintro ⟨a, ha⟩
    exact h (by rw [← ha]; exact a.isLt)

theorem comp_ι_apply (s : Store 101) (j : Fin 90) : (s ∘ ι) j = s ⟨j.val, by omega⟩ := rfl

set_option maxHeartbeats 4000000 in
/-- **`keyTryRP` computes `keyTryRW`**: tape `0` receives the word of the try, every other tape is
unchanged. -/
theorem run_keyTryRP {d B P : ℕ} (hK0 : 0 < K) (s : Store 101)
    (hs : ∀ j : Fin 101, 26 ≤ j.val → j.val < 90 → s j = [])
    (hw : ∀ j : Fin 101, 94 ≤ j.val → j.val < 100 → s j = [])
    (hpk : (s 1).length = P) (hsz : d * (N * K) + nT k * (N * K) ≤ P)
    (hbf : (s 2).length = 2 * k * (N * K)) (hS : (s 4).length = K)
    (hc : s 5 = powW K (B - 1)) (hK : (s 6).length = K) (hN : (s 7).length = N)
    (hNK : (s 8).length = N * K) (hB : (s 9).length = B) (hn : (s 10).length = (d + nT k) * N)
    (hnK : (s 11).length = (d + nT k) * N * K) (hk : (s 12).length = k)
    (h13 : (s 13).length = 2 * k) (h14 : (s 14).length = 1) (h15 : (s 15).length = 1)
    (h16 : (s 16).length = d) (h17 : (s 17).length = nT k) (h18 : (s 18).length = d * (N * K))
    (h19 : (s 19).length = nT k * (N * K)) (h20 : (s 20).length = 2 * k * (N * K))
    (h21 : (s 21).length = d * N) (h22 : (s 22).length = P - N * K) (h23 : (s 23).length = P)
    (h24 : (s 24).length = P + (d + nT k) * N * K + 2 * k * (N * K))
    (he : (s 90).length = 2 * k * (N * K)) (htt : (s 91).length = N * K)
    (h92 : (s 92).length = 2 * k * N) (h93 : (s 93).length = 2 * k * (2 * k * (N * K)))
    (h100 : (s 100).length = 2 * k) :
    run keyTryRP s = Function.update s 0
      (keyTryRW N K k d B (s 4) (s 1) (s 90) (s 91) (s 2) (s 3)) := by
  set s' : Store 90 := s ∘ ι with hs'
  have b' : ∀ j : Fin 90, 26 ≤ j.val → s' j = [] := fun j hj => hs _ hj j.isLt
  have g : ∀ (i : Fin 90) (j : Fin 101), i.val = j.val → s' i = s j := fun i j h => by
    rw [hs', Function.comp_apply]; congr 1; exact Fin.ext h
  have hNKP : N * K ≤ P := by
    have : N * K ≤ nT k * (N * K) := Nat.le_mul_of_pos_left _ (by simp [nT])
    omega
  have hl0 : ((s 1).take (d * (N * K))).length = d * (N * K) := by
    rw [List.length_take, hpk]; omega
  have hl1 : (((s 1).drop (d * (N * K))).take (nT k * (N * K))).length = nT k * (N * K) := by
    rw [List.length_take, List.length_drop, hpk]; omega
  have hl2 : ((s 1).drop ((s 1).length - N * K)).length = N * K := by
    rw [List.length_drop, hpk]; omega
  have hl3 : (embW ((d + nT k) * N) B K (s 3)).length = (d + nT k) * N * K := length_embW _ _ _ _
  -- phases 1 and 2 on the first 90 tapes
  have r12 : run (ph1 ⨾ ph2) s' = Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update s'
      27 ((s 1).take (d * (N * K)))) 28 (((s 1).drop (d * (N * K))).take (nT k * (N * K))))
      29 ((s 1).drop ((s 1).length - N * K))) 30 (embW ((d + nT k) * N) B K (s 3)))
      26 ((embW ((d + nT k) * N) B K (s 3)).drop (d * (N * K))))
      31 ((embW ((d + nT k) * N) B K (s 3)).take (d * (N * K))))
      32 (dotW N K d ((s 1).take (d * (N * K))) ((embW ((d + nT k) * N) B K (s 3)).take
        (d * (N * K)))))
      33 (dotW N K (nT k) (((s 1).drop (d * (N * K))).take (nT k * (N * K)))
        ((embW ((d + nT k) * N) B K (s 3)).drop (d * (N * K)))))
      34 (shortMapW N K d (nT k) ((s 1).take (d * (N * K)))
        (((s 1).drop (d * (N * K))).take (nT k * (N * K))) (embW ((d + nT k) * N) B K (s 3))))
      35 (subRW N K ((s 1).drop ((s 1).length - N * K)) (shortMapW N K d (nT k)
        ((s 1).take (d * (N * K))) (((s 1).drop (d * (N * K))).take (nT k * (N * K)))
        (embW ((d + nT k) * N) B K (s 3)))))
      36 (decW N K k (subRW N K ((s 1).drop ((s 1).length - N * K)) (shortMapW N K d (nT k)
        ((s 1).take (d * (N * K))) (((s 1).drop (d * (N * K))).take (nT k * (N * K)))
        (embW ((d + nT k) * N) B K (s 3))))) := by
    rw [run_seq, run_ph1 (N := N) (K := K) (k := k) (d := d) (B := B) (P := P) s' b'
      (by rw [g 1 1 rfl, hpk]) hsz (by rw [g 5 5 rfl, hc]) (by rw [g 6 6 rfl, hK])
      (by rw [g 9 9 rfl, hB]) (by rw [g 10 10 rfl, hn]) (by rw [g 11 11 rfl, hnK])
      (by rw [g 18 18 rfl, h18]) (by rw [g 19 19 rfl, h19]) (by rw [g 22 22 rfl, h22])]
    rw [run_ph2 (N := N) (K := K) (k := k) (d := d) _
      (by (repeat' (apply ProgKey.clean_upd' (by decide))); exact fun j hj => b' j (by omega))
      (by simp [b'])
      (by simp [g 6 6 rfl, hK]) (by simp [g 7 7 rfl, hN]) (by simp [g 8 8 rfl, hNK])
      (by simp [g 12 12 rfl, hk]) (by simp [g 14 14 rfl, h14]) (by simp [g 15 15 rfl, h15])
      (by simp [g 16 16 rfl, h16]) (by simp [g 17 17 rfl, h17]) (by simp [g 18 18 rfl, h18])
      (by simp [g 20 20 rfl, h20]) (by simp [g 1 1 rfl, hl0]) (by simp [g 1 1 rfl, hl1])
      (by simp [g 1 1 rfl, hl2]) (by simp [g 3 3 rfl, hl3])]
    have e1 : s' 1 = s 1 := g 1 1 rfl
    have e3 : s' 3 = s 3 := g 3 3 rfl
    simp [e1, e3]
  set V := run (ph1 ⨾ ph2) s' with hV
  set t := Function.extend ι V s with ht
  have tl : ∀ (j : Fin 101) (h : j.val < 90), t j = V ⟨j.val, h⟩ := by
    intro j h; rw [ht, extend_ι]; exact dif_pos h
  have th : ∀ j : Fin 101, 90 ≤ j.val → t j = s j := by
    intro j h; rw [ht, extend_ι]; exact dif_neg (by omega)
  have upd_ne : ∀ (w : Store 90) (i a : Fin 90) (v : List Bool), a.val ≠ i.val →
      Function.update w i v a = w a := fun w i a v h =>
    Function.update_of_ne (fun e => h (congrArg Fin.val e)) _ _
  have tV : ∀ j : Fin 90, (j.val < 26 ∨ 36 < j.val) → V j = s' j := by
    intro j hj
    rw [r12]
    repeat rw [upd_ne _ _ _ _ (by simp; omega)]
  have tsc : Scr t := by
    intro j h1 h2
    rw [tl j h2, tV _ (by simp; omega)]
    exact b' _ (by simp; omega)
  have tS : ∀ j : Fin 101, (h : j.val < 26) → t j = s j := by
    intro j h
    rw [tl j (by omega), tV _ (by simp; omega)]
    rfl
  have t29 : t 29 = (s 1).drop ((s 1).length - N * K) := by
    rw [tl 29 (by decide), r12]; simp
  have t30 : t 30 = embW ((d + nT k) * N) B K (s 3) := by rw [tl 30 (by decide), r12]; simp
  set zW := decW N K k (subRW N K ((s 1).drop ((s 1).length - N * K)) (shortMapW N K d (nT k)
    ((s 1).take (d * (N * K))) (((s 1).drop (d * (N * K))).take (nT k * (N * K)))
    (embW ((d + nT k) * N) B K (s 3)))) with hzW
  have t36 : t 36 = zW := by rw [tl 36 (by decide), r12]; simp [hzW]
  have t37 : t 37 = [] := by
    rw [tl 37 (by decide), r12]; simp [hs']; exact hs 37 (by decide) (by decide)
  have t38 : t 38 = [] := by
    rw [tl 38 (by decide), r12]; simp [hs']; exact hs 38 (by decide) (by decide)
  have hzl : zW.length = 2 * k * (N * K) := ProgKey.length_decW N K k _
  have r3 := run_ph3R (N := N) (K := K) (k := k) (d := d) hK0 t tsc t37 t38
    (by rw [tS 2 (by decide), hbf]) (by rw [tS 4 (by decide), hS]) (by rw [tS 6 (by decide), hK])
    (by rw [tS 7 (by decide), hN]) (by rw [tS 8 (by decide), hNK]) (by rw [tS 10 (by decide), hn])
    (by rw [tS 11 (by decide), hnK]) (by rw [tS 12 (by decide), hk])
    (by rw [tS 13 (by decide), h13]) (by rw [tS 14 (by decide), h14])
    (by rw [tS 15 (by decide), h15]) (by rw [tS 19 (by decide), h19])
    (by rw [tS 20 (by decide), h20]) (by rw [t29, hl2]) (by rw [t30, hl3]) (by rw [t36, hzl])
    (by rw [th 90 (by decide), he]) (by rw [th 91 (by decide), htt])
    (by rw [th 92 (by decide), h92]) (by rw [th 93 (by decide), h93])
    (by rw [th 100 (by decide), h100])
  dsimp only at r3
  set u := run ph3R t with hu
  have upd_ne' : ∀ (w : Store 101) (i a : Fin 101) (v : List Bool), a.val ≠ i.val →
      Function.update w i v a = w a := fun w i a v h =>
    Function.update_of_ne (fun e => h (congrArg Fin.val e)) _ _
  have uT : ∀ j : Fin 101, (j.val < 37 ∨ (40 < j.val ∧ j.val < 94) ∨ j.val = 100) → u j = t j := by
    intro j hj
    rw [r3]
    repeat rw [upd_ne' _ _ _ _ (by simp; omega)]
  have u39 := congrFun r3 39
  have u40 := congrFun r3 40
  simp only [Function.update_self, Function.update_of_ne (show (39 : Fin 101) ≠ 40 by decide)] at u39 u40
  obtain ⟨b, hb⟩ : ∃ b, u 40 = [b] := ⟨_, u40⟩
  clear_value u t V
  have hxl : (u 39).length = (d + nT k) * N * K := by
    rw [u39, length_matSubW (by rw [t30, hl3]; ring)]; ring
  have hag : ∀ j : Fin 90, (j.val < 26 ∨ 40 < j.val) → (u ∘ ι) j = s' j := by
    intro j hj
    show u (ι j) = s' j
    rw [uT _ (by show j.val < 37 ∨ (40 < j.val ∧ j.val < 94) ∨ j.val = 100; omega),
      tl _ (by show j.val < 90; omega), tV _ (by show j.val < 26 ∨ 36 < j.val; omega)]
    rfl
  have h40 : (u ∘ ι) 40 = [b] := hb
  have r4 := ProgKey.run_ph4 (N := N) (K := K) (k := k) (d := d) (P := P) s' (u ∘ ι)
    hag b' b h40
    (by show (u 1).length = P; rw [uT 1 (by decide), tS 1 (by decide), hpk])
    (by show (u 11).length = _; rw [uT 11 (by decide), tS 11 (by decide), hnK])
    (by show (u 20).length = _; rw [uT 20 (by decide), tS 20 (by decide), h20])
    (by show (u 23).length = _; rw [uT 23 (by decide), tS 23 (by decide), h23])
    (by show (u 24).length = _; rw [uT 24 (by decide), tS 24 (by decide), h24])
    (by show (u 39).length = _; exact hxl)
    (by show (u 36).length = _; rw [uT 36 (by decide), t36, hzl])
  rw [t30, t36, th 90 (by decide), th 91 (by decide), tS 2 (by decide)] at u39
  rw [tS 4 (by decide), t30, t36, th 90 (by decide), th 91 (by decide), tS 2 (by decide)] at u40
  have hbv := hb.symm.trans u40
  simp only [List.cons.injEq, and_true] at hbv
  have hout : (u ∘ ι) 1 ++ (if b = true then (u ∘ ι) 39 ++ (u ∘ ι) 36 else zeroW (d * (N * K)) ++
      (zeroW (nT k * (N * K)) ++ zeroW (2 * k * (N * K)))) =
      keyTryRW N K k d B (s 4) (s 1) (s 90) (s 91) (s 2) (s 3) := by
    have e1 : (u ∘ ι) 1 = s 1 := by
      show u 1 = s 1; rw [uT 1 (by decide), tS 1 (by decide)]
    have e36 : (u ∘ ι) 36 = zW := by show u 36 = zW; rw [uT 36 (by decide), t36]
    have e39 : (u ∘ ι) 39 = u 39 := rfl
    rw [e1, e36, e39, u39, hbv]
    rfl
  simp only [keyTryRP, run_seq, run_clear]
  rw [run_map ι_inj (ph1 ⨾ ph2) s, ← hs', ← hV, ← ht, ← hu, run_map ι_inj ph4 u, r4, hout]
  funext j
  by_cases hj : j.val < 90
  · rw [upd_ne' _ _ _ _ (by simp; omega), upd_ne' _ _ _ _ (by simp; omega),
      upd_ne' _ _ _ _ (by simp; omega), extend_ι]
    dsimp only
    rw [dif_pos hj]
    by_cases h0 : j.val = 0
    · have : j = 0 := Fin.ext h0
      subst this
      rfl
    · rw [upd_ne' s 0 j _ (by simp; omega)]
      rw [upd_ne s' 0 ⟨j.val, hj⟩ _ (by simp; omega)]
      rfl
  · rw [upd_ne' s 0 j _ (by simp; omega)]
    by_cases h96 : j.val = 96
    · rw [show j = 96 from Fin.ext h96, Function.update_self, hw 96 (by decide) (by decide)]
    rw [upd_ne' _ 96 j _ h96]
    by_cases h95 : j.val = 95
    · rw [show j = 95 from Fin.ext h95, Function.update_self, hw 95 (by decide) (by decide)]
    rw [upd_ne' _ 95 j _ h95]
    by_cases h94 : j.val = 94
    · rw [show j = 94 from Fin.ext h94, Function.update_self, hw 94 (by decide) (by decide)]
    rw [upd_ne' _ 94 j _ h94, extend_ι]
    dsimp only
    rw [dif_neg hj]
    by_cases hlow : j.val < 94 ∨ j.val = 100
    · rw [uT j (by omega), th j (by omega)]
    · have h97 : j.val = 97 ∨ j.val = 98 ∨ j.val = 99 := by omega
      rw [hw j (by omega) (by omega), r3]
      rcases h97 with h | h | h
      · rw [show j = 97 from Fin.ext h]; simp
      · rw [show j = 98 from Fin.ext h]; simp
      · rw [show j = 99 from Fin.ext h]; simp

end AdvancedEncryption.DualUse.ProgKeyR
