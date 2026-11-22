import PE.Impl.DualUse.Algo.KeyTrySim
import SigabaNeo.Lib.Lattices.ProgAlgo.BoxProgs
import SigabaNeo.Lib.Lattices.ProgAlgo.Nand

/-!
# One try of key generation with the simulated trapdoor, as a tape program

`keyTrySimP : Prog 90` computes the word algorithm `keyTrySimW` (`Algo.KeyTrySim`) on tapes
(`run_keyTrySimP`), composing the verified programs `embP`, `ballP`, `decP` (`BoxProgs`),
`matMulP`, `addRWP`, `subRWP` (`ProgAlgo`) and the stream moves `mvP`, `dropP`. With the coin loop
`coinsP` in front (`keyTrySimCoinsP`), its law on the store is the image of `m` fair coins
(`law_keyTrySimCoinsP`).

Tapes:
* inputs: `0` output, `1` the public key `pk` (`P` bits), `2` the word of `W_f`, `3` the coins `l`,
  `4` the radius word `sW`, `5` the word `powW K (B − 1)`;
* templates (any content, of the given lengths): `6` `K`, `7` `N`, `8` `N·K`, `9` `B`, `10`
  `n = (d + L)·N`, `11` `n·K`, `12` `k`, `13` `2k`, `14` `15` `1`, `16` `d`, `17` `L = 1 + 4k`,
  `18` `d·N·K`, `19` `L·N·K`, `20` `2k·N·K`, `21` `d·N`, `22` `P − N·K`, `23` `P`, `24` the output
  length `P + n·K + 2k·N·K`, `25` `m` (the number of coins);
* working tapes `26 … 40` and scratch `41 … 89`, blank before and after.

The program has four phases: reading the public key and the big-box element (`ph1`), the
decomposition `z` (`ph2`), the shift and the ball test (`ph3`), writing the output (`ph4`).
-/

namespace AdvancedEncryption.DualUse.ProgKey

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices.Algo
  AdvancedEncryption.DualUse.Algo
open scoped SigabaNeo.Tape.Prog

/-! ### Placements -/

/-- A stream move `a → b` with the template `c`. -/
def mvAt (a b c : Fin 90) : Fin 5 → Fin 90 := ![a, b, 41, 42, c]

theorem run_mvAt {a b c : Fin 90} (hu : Function.Injective (mvAt a b c)) (t : Store 90)
    (h41 : t 41 = []) (h42 : t 42 = []) :
    run (map (mvAt a b c) mvP) t = Function.update (Function.update t a ((t a).drop (t c).length)) b
      ((t b ++ takeD (t c).length (t a)).drop (t c).length) := run_mvP_map hu t h41 h42

/-- The tapes `0 … c−1` of a program on given tapes, its scratch at `c + off`. -/
def plc {n : ℕ} (c off : ℕ) (v : Fin c → Fin 90) (h : n + off ≤ 90) : Fin n → Fin 90 :=
  fun i => if hi : i.val < c then v ⟨i.val, hi⟩ else ⟨i.val + off, by omega⟩

theorem plc_scratch {n c off : ℕ} {v : Fin c → Fin 90} {h : n + off ≤ 90} (t : Store 90)
    (ht : ∀ j : Fin 90, 41 ≤ j.val → t j = []) (hoff : 41 ≤ c + off) :
    ∀ i : Fin n, c ≤ i.val → t (plc c off v h i) = [] := by
  intro i hi
  apply ht
  simp only [plc, dite_cond_eq_false (eq_false (show ¬ i.val < c by omega))]
  show 41 ≤ i.val + off
  omega

/-- `matMulP` with output `o`, inputs `x`, `y`, the templates `6` `7` `8` and `m`, `n`, `l`, `O`. -/
def mmAt (o x y m n l O : Fin 90) : Fin 59 → Fin 90 := plc 10 31 ![o, x, y, 6, 7, 8, m, n, l, O] rfl.le

theorem run_mmAt {o x y m n l O : Fin 90} (hu : Function.Injective (mmAt o x y m n l O))
    {K N m' n' l' : ℕ} (t : Store 90) (ht : ∀ j : Fin 90, 41 ≤ j.val → t j = [])
    (hK : (t 6).length = K) (hN : (t 7).length = N) (hNK : (t 8).length = N * K)
    (hm : (t m).length = m') (hn : (t n).length = n') (hl : (t l).length = l')
    (hO : (t O).length = m' * l' * (N * K)) (hx : (t x).length = m' * n' * (N * K))
    (hy : (t y).length = n' * l' * (N * K)) :
    run (map (mmAt o x y m n l O) matMulP) t =
      Function.update t o (matMulW N K m' n' l' (t x) (t y)) :=
  run_map_eq_update hu _ t 0 _ (run_matMulP (t ∘ mmAt o x y m n l O)
    (plc_scratch t ht (by norm_num)) hK hN hNK hm hn hl hO hx hy)

/-- A block program `bzip` (`addRWP`, `subRWP`) with output `o`, inputs `x`, `y`, templates `a`, `b`. -/
def bzAt (o x y a b : Fin 90) : Fin 28 → Fin 90 := plc 5 36 ![o, x, y, a, b] (by norm_num)

theorem run_addAt {o x y : Fin 90} (hu : Function.Injective (bzAt o x y 6 7)) {K N : ℕ}
    (t : Store 90) (ht : ∀ j : Fin 90, 41 ≤ j.val → t j = []) (hK : (t 6).length = K)
    (hN : (t 7).length = N) (hx : (t x).length = N * K) (hy : (t y).length = N * K) :
    run (map (bzAt o x y 6 7) addRWP) t = Function.update t o (addRW N K (t x) (t y)) :=
  run_map_eq_update hu _ t 0 _ (run_addRWP (t ∘ bzAt o x y 6 7) (plc_scratch t ht (by norm_num))
    hK hN hx hy)

theorem run_subAt {o x y : Fin 90} (hu : Function.Injective (bzAt o x y 6 7)) {K N : ℕ}
    (t : Store 90) (ht : ∀ j : Fin 90, 41 ≤ j.val → t j = []) (hK : (t 6).length = K)
    (hN : (t 7).length = N) (hx : (t x).length = N * K) (hy : (t y).length = N * K) :
    run (map (bzAt o x y 6 7) subRWP) t = Function.update t o (subRW N K (t x) (t y)) :=
  run_map_eq_update hu _ t 0 _ (run_subRWP (t ∘ bzAt o x y 6 7) (plc_scratch t ht (by norm_num))
    hK hN hx hy)

theorem run_matSubAt {o x y b : Fin 90} (hu : Function.Injective (bzAt o x y 6 b)) {K N L : ℕ}
    (t : Store 90) (ht : ∀ j : Fin 90, 41 ≤ j.val → t j = []) (hK : (t 6).length = K)
    (hLN : (t b).length = L * N) (hx : (t x).length = L * N * K) (hy : (t y).length = L * N * K) :
    run (map (bzAt o x y 6 b) subRWP) t = Function.update t o (matSubW N K L (t x) (t y)) :=
  run_map_eq_update hu _ t 0 _ (run_subRWP_mat (t ∘ bzAt o x y 6 b)
    (plc_scratch t ht (by norm_num)) hK hLN hx hy)

/-- `embP`: output `30`, coins `3`, templates `9` `6` `10`, the constant `5`, template `11`. -/
def embAt : Fin 22 → Fin 90 := plc 7 34 ![30, 3, 9, 6, 10, 5, 11] (by norm_num)

theorem run_embAt {n B K : ℕ} (t : Store 90) (ht : ∀ j : Fin 90, 41 ≤ j.val → t j = [])
    (hB : (t 9).length = B) (hK : (t 6).length = K) (hn : (t 10).length = n)
    (hc : t 5 = powW K (B - 1)) (hO : (t 11).length = n * K) :
    run (map embAt embP) t = Function.update t 30 (embW n B K (t 3)) :=
  run_map_eq_update (by decide) _ t 0 _ (run_embP (t ∘ embAt) (plc_scratch t ht (by norm_num))
    hB hK hn hc hO)

/-- `decP`: output `36`, input `35`, templates `6` `7` `12` `8` `20`. -/
def decAt : Fin 37 → Fin 90 := plc 7 34 ![36, 35, 6, 7, 12, 8, 20] (by norm_num)

theorem run_decAt {K N k : ℕ} (t : Store 90) (ht : ∀ j : Fin 90, 41 ≤ j.val → t j = [])
    (hu : (t 35).length = N * K) (hK : (t 6).length = K) (hN : (t 7).length = N)
    (hk : (t 12).length = k) (hNK : (t 8).length = N * K) (hO : (t 20).length = 2 * k * (N * K)) :
    run (map decAt decP) t = Function.update t 36 (decW N K k (t 35)) :=
  run_map_eq_update (by decide) _ t 0 _ (run_decP (t ∘ decAt) (plc_scratch t ht (by norm_num))
    hu hK hN hk hNK hO)

/-- `ballP`: output `40`, input `39`, the radius `4`, templates `6` `10` `14`. -/
def ballAt : Fin 23 → Fin 90 := plc 6 35 ![40, 39, 4, 6, 10, 14] (by norm_num)

theorem run_ballAt {n K : ℕ} (hK0 : 0 < K) (t : Store 90) (ht : ∀ j : Fin 90, 41 ≤ j.val → t j = [])
    (hw : (t 39).length = n * K) (hS : (t 4).length = K) (hK : (t 6).length = K)
    (hn : (t 10).length = n) (h1 : (t 14).length = 1) :
    run (map ballAt ballP) t = Function.update t 40 [ballW n K (t 4) (t 39)] :=
  run_map_eq_update (by decide) _ t 0 _ (run_ballP hK0 (t ∘ ballAt)
    (plc_scratch t ht (by norm_num)) hw hS hK hn h1)

/-- `dropP` on the stream `26` with the template `22`. -/
def dropAt : Fin 3 → Fin 90 := ![26, 41, 22]

theorem run_dropAt (t : Store 90) (h41 : t 41 = []) :
    run (map dropAt dropP) t = Function.update t 26 ((t 26).drop (t 22).length) :=
  run_dropP_map (by decide) t h41

theorem clean_upd {t : Store 90} {i : Fin 90} {v : List Bool} (hi : i.val < 41)
    (ht : ∀ j : Fin 90, 41 ≤ j.val → t j = []) : ∀ j : Fin 90, 41 ≤ j.val → Function.update t i v j = [] := by
  intro j hj
  rw [Function.update_of_ne (by rintro rfl; omega)]
  exact ht j hj

/-! ### Phase 1: the blocks of the public key, the big-box element -/

/-- `27 := B₀`, `28 := B₁`, `29 := p_pub` (from the public key `1`), `30 := emb(coins)`. -/
def ph1 : Prog 90 :=
  cp 26 1 ⨾ cp 27 18 ⨾ map (mvAt 26 27 18) mvP ⨾ cp 28 19 ⨾ map (mvAt 26 28 19) mvP ⨾ cp 26 1 ⨾
    map dropAt dropP ⨾ cp 29 26 ⨾ clr 26 ⨾ map embAt embP

theorem run_ph1 {N K k d B P : ℕ} (t : Store 90) (ht : ∀ j : Fin 90, 26 ≤ j.val → t j = [])
    (hpk : (t 1).length = P) (hsz : d * (N * K) + nT k * (N * K) ≤ P)
    (hc : t 5 = powW K (B - 1)) (hK : (t 6).length = K) (hB : (t 9).length = B)
    (hn : (t 10).length = (d + nT k) * N) (hnK : (t 11).length = (d + nT k) * N * K)
    (h18 : (t 18).length = d * (N * K)) (h19 : (t 19).length = nT k * (N * K))
    (h22 : (t 22).length = P - N * K) :
    run ph1 t = Function.update (Function.update (Function.update (Function.update t
      27 ((t 1).take (d * (N * K))))
      28 (((t 1).drop (d * (N * K))).take (nT k * (N * K))))
      29 ((t 1).drop ((t 1).length - N * K)))
      30 (embW ((d + nT k) * N) B K (t 3)) := by
  have e1 : takeD (t 18).length (t 1) = (t 1).take (d * (N * K)) := by
    rw [h18]; exact takeD_eq_take (by omega)
  have e2 : takeD (t 19).length ((t 1).drop (t 18).length) =
      ((t 1).drop (d * (N * K))).take (nT k * (N * K)) := by
    rw [h18, h19]; exact takeD_eq_take (by simp; omega)
  simp only [ph1, run_seq, run_copy, run_clear]
  rw [run_mvAt (a := 26) (b := 27) (c := 18) (by decide) _ (by simp [ht]) (by simp [ht])]
  rw [run_mvAt (a := 26) (b := 28) (c := 19) (by decide) _ (by simp [ht]) (by simp [ht])]
  rw [run_dropAt _ (by simp [ht])]
  have ht41 : ∀ j : Fin 90, 41 ≤ j.val → t j = [] := fun j hj => ht j (by omega)
  rw [run_embAt (n := (d + nT k) * N) (B := B) (K := K) _ (by (repeat' (apply clean_upd (by decide))); exact ht41)
    (by simp [hB]) (by simp [hK]) (by simp [hn]) (by simp [hc]) (by simp [hnK])]
  funext j
  fin_cases j <;> simp [ht, e1, e2, hpk, h22]

/-! ### Phase 2: the decomposition `z` -/

theorem dotW_eq_matMulW (N K n : ℕ) (x y : List Bool) : dotW N K n x y = matMulW N K 1 n 1 x y := by
  simp [dotW, matMulW, concatN]

/-- `26 := p₁`, `31 := p₀`, `32 := B₀ · p₀`, `33 := B₁ · p₁`, `34` their sum, `35 := p_pub − 34`,
`36 := z = G̲⁻¹(35)`. -/
def ph2 : Prog 90 :=
  cp 26 30 ⨾ cp 31 18 ⨾ map (mvAt 26 31 18) mvP ⨾ map (mmAt 32 27 31 14 16 15 29) matMulP ⨾
    map (mmAt 33 28 26 14 17 15 29) matMulP ⨾ map (bzAt 34 32 33 6 7) addRWP ⨾
    map (bzAt 35 29 34 6 7) subRWP ⨾ map decAt decP

theorem run_ph2 {N K k d : ℕ} (t : Store 90) (ht : ∀ j : Fin 90, 31 ≤ j.val → t j = [])
    (h26 : t 26 = []) (hK : (t 6).length = K) (hN : (t 7).length = N) (hNK : (t 8).length = N * K)
    (hk : (t 12).length = k) (h14 : (t 14).length = 1) (h15 : (t 15).length = 1)
    (h16 : (t 16).length = d) (h17 : (t 17).length = nT k)
    (h18 : (t 18).length = d * (N * K)) (h20 : (t 20).length = 2 * k * (N * K))
    (hb0 : (t 27).length = d * (N * K)) (hb1 : (t 28).length = nT k * (N * K))
    (hpp : (t 29).length = N * K) (hp : (t 30).length = (d + nT k) * N * K) :
    run ph2 t = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update t
      26 ((t 30).drop (d * (N * K))))
      31 ((t 30).take (d * (N * K))))
      32 (dotW N K d (t 27) ((t 30).take (d * (N * K)))))
      33 (dotW N K (nT k) (t 28) ((t 30).drop (d * (N * K)))))
      34 (shortMapW N K d (nT k) (t 27) (t 28) (t 30)))
      35 (subRW N K (t 29) (shortMapW N K d (nT k) (t 27) (t 28) (t 30))))
      36 (decW N K k (subRW N K (t 29) (shortMapW N K d (nT k) (t 27) (t 28) (t 30)))) := by
  have ht41 : ∀ j : Fin 90, 41 ≤ j.val → t j = [] := fun j hj => ht j (by omega)
  have e1 : takeD (t 18).length (t 30) = (t 30).take (d * (N * K)) := by
    rw [h18]; exact takeD_eq_take (by rw [hp]; nlinarith)
  have e1'' : List.take (t 18).length (t 30) = List.take (d * (N * K)) (t 30) := by rw [h18]
  have hl0 : ((t 30).take (d * (N * K))).length = d * (N * K) := by
    rw [List.length_take, hp]; apply min_eq_left; nlinarith
  have hl1 : ((t 30).drop (d * (N * K))).length = nT k * (N * K) := by
    rw [List.length_drop, hp]; rw [Nat.add_mul, Nat.add_mul]; ring_nf; omega
  simp only [ph2, run_seq, run_copy]
  rw [run_mvAt (a := 26) (b := 31) (c := 18) (by decide) _ (by simp [ht]) (by simp [ht])]
  rw [run_mmAt (o := 32) (x := 27) (y := 31) (O := 29) (K := K) (N := N) (m' := 1) (n' := d) (l' := 1)
    (by decide) _ (by (repeat' (apply clean_upd (by decide))); exact ht41)
    (by simp [hK]) (by simp [hN]) (by simp [hNK]) (by simp [h14]) (by simp [h16]) (by simp [h15])
    (by simp [hpp]) (by simp [hb0]) (by simp [e1, hl0])]
  rw [run_mmAt (o := 33) (x := 28) (y := 26) (O := 29) (K := K) (N := N) (m' := 1) (n' := nT k) (l' := 1)
    (by decide) _ (by (repeat' (apply clean_upd (by decide))); exact ht41)
    (by simp [hK]) (by simp [hN]) (by simp [hNK]) (by simp [h14]) (by simp [h17]) (by simp [h15])
    (by simp [hpp]) (by simp [hb1]) (by simp [h18, hl1])]
  rw [run_addAt (o := 34) (x := 32) (y := 33) (K := K) (N := N)
    (by decide) _ (by (repeat' (apply clean_upd (by decide))); exact ht41)
    (by simp [hK]) (by simp [hN]) (by simp [length_matMulW]) (by simp [length_matMulW])]
  rw [run_subAt (o := 35) (x := 29) (y := 34) (K := K) (N := N)
    (by decide) _ (by (repeat' (apply clean_upd (by decide))); exact ht41)
    (by simp [hK]) (by simp [hN]) (by simp [hpp]) (by simp [length_addRW, length_matMulW])]
  rw [run_decAt (K := K) (N := N) (k := k) _ (by (repeat' (apply clean_upd (by decide))); exact ht41)
    (by simp [length_subRW, hpp]) (by simp [hK]) (by simp [hN]) (by simp [hk]) (by simp [hNK])
    (by simp [h20])]
  have hsm : addRW N K (matMulW N K 1 d 1 (t 27) ((t 30).take (d * (N * K))))
      (matMulW N K 1 (nT k) 1 (t 28) ((t 30).drop (d * (N * K)))) =
      shortMapW N K d (nT k) (t 27) (t 28) (t 30) := by
    rw [shortMapW, dotW_eq_matMulW, dotW_eq_matMulW]
  have e1' : takeD (d * (N * K)) (t 30) = (t 30).take (d * (N * K)) := by
    have := e1; rwa [h18] at this
  have ed : List.drop (d * (N * K)) (t 18 ++ List.take (d * (N * K)) (t 30)) =
      List.take (d * (N * K)) (t 30) := List.drop_left' h18
  funext j
  fin_cases j <;> simp [ht, e1', h18, ed, hsm, dotW_eq_matMulW]

/-! ### Phase 3: the shift, the shifted key, the ball test -/

/-- `37 := W_f z`, `39 := x = (p₀ − W_f z, p₁)`, `40 := [x ∈ ball]` (`26`, `38` consumed). -/
def ph3 : Prog 90 :=
  map (mmAt 37 2 36 16 13 15 18) matMulP ⨾ map (bzAt 38 31 37 6 21) subRWP ⨾ cp 39 11 ⨾
    map (mvAt 38 39 18) mvP ⨾ map (mvAt 26 39 19) mvP ⨾ map ballAt ballP

theorem run_ph3 {N K k d : ℕ} (hK0 : 0 < K) (t : Store 90) (ht : ∀ j : Fin 90, 37 ≤ j.val → t j = [])
    (hwf : (t 2).length = d * (2 * k) * (N * K)) (hS : (t 4).length = K)
    (hK : (t 6).length = K) (hN : (t 7).length = N) (hNK : (t 8).length = N * K)
    (hn : (t 10).length = (d + nT k) * N) (hnK : (t 11).length = (d + nT k) * N * K)
    (h13 : (t 13).length = 2 * k) (h14 : (t 14).length = 1) (h15 : (t 15).length = 1)
    (h16 : (t 16).length = d) (h18 : (t 18).length = d * (N * K))
    (h19 : (t 19).length = nT k * (N * K)) (h21 : (t 21).length = d * N)
    (hp1 : (t 26).length = nT k * (N * K)) (hp0 : (t 31).length = d * (N * K))
    (hz : (t 36).length = 2 * k * (N * K)) :
    run ph3 t = Function.update (Function.update (Function.update (Function.update
      (Function.update t
      37 (simShiftW N K k d (t 2) (t 36)))
      38 [])
      39 (matSubW N K d (t 31) (simShiftW N K k d (t 2) (t 36)) ++ t 26))
      26 [])
      40 [ballW ((d + nT k) * N) K (t 4)
        (matSubW N K d (t 31) (simShiftW N K k d (t 2) (t 36)) ++ t 26)] := by
  have ht41 : ∀ j : Fin 90, 41 ≤ j.val → t j = [] := fun j hj => ht j (by omega)
  set T := simShiftW N K k d (t 2) (t 36) with hT
  set X := matSubW N K d (t 31) T with hX
  have hTl : T.length = d * (N * K) := by rw [hT, simShiftW, length_matMulW]; ring
  have hXl : X.length = d * (N * K) := by
    rw [hX, matSubW_eq_subRW, length_subRW _ _ (by rw [hp0]; ring)]; ring
  have s1 : run (map (mmAt 37 2 36 16 13 15 18) matMulP) t = Function.update t 37 T :=
    run_mmAt (K := K) (N := N) (m' := d) (n' := 2 * k) (l' := 1) (by decide) _ ht41 hK hN hNK h16 h13
      h15 (by rw [h18]; ring) hwf (by rw [hz]; ring)
  have s2 : run (map (bzAt 38 31 37 6 21) subRWP) (Function.update t 37 T) =
      Function.update (Function.update t 37 T) 38 X := by
    rw [run_matSubAt (K := K) (N := N) (L := d) (by decide) _
      (by (repeat' (apply clean_upd (by decide))); exact ht41)
      (by simp [hK]) (by simp [h21]) (by simp [hp0]; ring) (by simp [hTl]; ring)]
    simp [hX]
  have s3 : run (map (mvAt 38 39 18) mvP)
      (Function.update (Function.update (Function.update t 37 T) 38 X) 39 (t 11)) =
      Function.update (Function.update (Function.update (Function.update (Function.update t 37 T)
        38 X) 39 (t 11)) 38 []) 39 ((t 11 ++ X).drop (d * (N * K))) := by
    rw [run_mvAt (a := 38) (b := 39) (c := 18) (by decide) _ (by simp [ht]) (by simp [ht])]
    simp only [Function.update_self, Function.update_of_ne (show (38 : Fin 90) ≠ 39 by decide),
      Function.update_of_ne (show (18 : Fin 90) ≠ 39 by decide),
      Function.update_of_ne (show (18 : Fin 90) ≠ 38 by decide),
      Function.update_of_ne (show (18 : Fin 90) ≠ 37 by decide), h18]
    rw [takeD_of_length' hXl, List.drop_eq_nil_of_le (le_of_eq hXl)]
  set S3 := Function.update (Function.update (Function.update (Function.update (Function.update t 37 T)
        38 X) 39 (t 11)) 38 []) 39 ((t 11 ++ X).drop (d * (N * K))) with hS3
  have hx : ((t 11 ++ X).drop (d * (N * K)) ++ t 26).drop (nT k * (N * K)) = X ++ t 26 := by
    have := drop_append_drop (t 11) X (t 26)
    rw [hXl, hp1] at this
    rw [this, List.drop_left']
    rw [hnK]; ring
  have s4 : run (map (mvAt 26 39 19) mvP) S3 =
      Function.update (Function.update S3 26 []) 39 (X ++ t 26) := by
    rw [run_mvAt (a := 26) (b := 39) (c := 19) (by decide) _ (by simp [hS3, ht]) (by simp [hS3, ht])]
    have a26 : S3 26 = t 26 := by simp [hS3]
    have a19 : S3 19 = t 19 := by simp [hS3]
    have a39 : S3 39 = (t 11 ++ X).drop (d * (N * K)) := by simp [hS3]
    rw [a26, a19, a39, h19, takeD_of_length' hp1, List.drop_eq_nil_of_le (le_of_eq hp1), hx]
  have hXl' : (X ++ t 26).length = (d + nT k) * N * K := by
    rw [List.length_append, hXl, hp1]; ring
  have s5 : run (map ballAt ballP) (Function.update (Function.update S3 26 []) 39 (X ++ t 26)) =
      Function.update (Function.update (Function.update S3 26 []) 39 (X ++ t 26)) 40
        [ballW ((d + nT k) * N) K (t 4) (X ++ t 26)] := by
    rw [run_ballAt (n := (d + nT k) * N) (K := K) hK0 _
      (by (repeat' (apply clean_upd (by decide))); exact ht41)
      (by simp [hXl']) (by simp [hS3, hS]) (by simp [hS3, hK]) (by simp [hS3, hn]) (by simp [hS3, h14])]
    simp [hS3]
  have c3 : Function.update (Function.update (Function.update t 37 T) 38 X) 39
      (Function.update (Function.update t 37 T) 38 X 11) =
      Function.update (Function.update (Function.update t 37 T) 38 X) 39 (t 11) := by simp
  simp only [ph3, run_seq, run_copy]
  rw [s1, s2, c3, s3, s4, s5]
  funext j
  fin_cases j <;> simp [hS3]

end AdvancedEncryption.DualUse.ProgKey
