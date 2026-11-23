import PE.Impl.ExpLUT.Correctness
import PE.Impl.ExpLUT.KeyGen

/-!
# Correctness of the scheme, at the norm level (§5.2, Theorem 1)

With the coins of `Enc` bounded (`CoinBounds`: base errors `e_b`, `e_k`, `e_m` at most `B_χ`,
flooding errors `e₀`, `e_t`, and of the digit encodings at most `B_fl`) and a key with coefficients
at most `K`:

* `rowBnd_decErr`: every entry of `e_F` is at most `max(B_χ, B_F)` with
  `B_F = step^[T] B_fl` (Lemma 9 with `B₀ = β = B_C = B_fl`; `B_F ≤ γ^T (B_fl + Δ)` by
  `stepBound_iterate_le`);
* `nrm_decNoise_le`: `‖e_m − e_F k_Fᵀ‖ ≤ B_χ + N n max(B_χ, B_F) K` (`corrBound`), `N = |KCol|`
  the number of ring elements of a key;
* **`decrypt_correct_of_bounds`** (Theorem 1): for `F(x) = 0` and a valid key, decryption
  returns `m` if `decode` recovers `m` from `⌊q/2⌉ m + e` for every `e` within `corrBound`;
* `decrypt_correct_of_mem_support`: the same for every accepted output of key generation
  (`keyLaw` with a good covered trapdoor), whose short part lies in `Small` and whose gadget part
  is a decomposition.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R} {Wb J Pos : Type*} [Fintype Wb] [Fintype J]
  (N : NormSpec S)

/-- The bounds on the coins of `Enc`. -/
structure CoinBounds (r : EncCoins S Wb J Pos) (Bχ Bfl : ℕ) : Prop where
  eb : RowBnd N r.eb Bχ
  eh : ∀ k, RowBnd N (r.eh k) Bχ
  em : N.nrm r.em ≤ Bχ
  eaut : ∀ t d, RowBnd N (r.eaut t d) Bfl
  ein : ∀ t, RowBnd N (r.ein t) Bfl
  edin : ∀ t d, RowBnd N (r.edin t d) Bfl
  e0 : RowBnd N r.e0 Bfl

variable {N}

theorem rowBnd_finExt {ι : Type*} {f : Fin S.b → ι → R} {B : ℕ} (h : ∀ t, RowBnd N (f t) B) (t : ℕ) :
    RowBnd N (finExt f t) B := by
  intro i
  unfold finExt
  split_ifs with ht
  · exact h _ i
  · simp [N.nrm_zero]

omit [Fintype Wb] [Fintype J] in
/-- The errors of the ciphertext data of `Enc` are bounded (Lemma 9's hypotheses). -/
theorem errBounds_encErrs (M : HelperMap S J) {r : EncCoins S Wb J Pos} {Bχ Bfl : ℕ}
    (hr : CoinBounds N r Bχ Bfl) : ErrBounds N (encErrs M r) Bfl Bfl Bfl Bχ where
  e0 := hr.e0
  fin := hr.ein
  ein := hr.edin
  hf := rowBnd_finExt fun t => hr.eh _
  hi := rowBnd_finExt fun t => hr.eh _
  caut := fun t d i => by
    show N.nrm (finExt (S := S) r.eaut t d i) ≤ Bfl
    unfold finExt
    split_ifs
    · exact hr.eaut _ d i
    · simp [N.nrm_zero]

variable (S) in
/-- `B_F = step^[T] B_fl`: the error bound of `c_F` (Lemma 9). -/
def evalBound (T Bχ Bfl : ℕ) : ℕ := (stepBound S Bfl Bχ Bfl)^[T] Bfl

omit [Fintype Wb] [Fintype J] in
/-- **The error row `e_F`** is bounded by `max(B_χ, B_F)`. -/
theorem rowBnd_decErr (M : HelperMap S J) {w : ℕ} (half : R) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (x : Pos → ℕ) (m : R) {r : EncCoins S Wb J Pos} {Bχ Bfl : ℕ} (hD : 1 ≤ S.gfac)
    (hr : CoinBounds N r Bχ Bfl) :
    RowBnd N (decErr M w half mpk F x m r) (max Bχ (evalBound S F.T Bχ Bfl)) := by
  intro c
  rcases c with ⟨i, c⟩ | ⟨i, k, c⟩ | c
  · exact ((N.nrm_σ _ _ (S.idx_odd _)).trans (hr.eb c)).trans (le_max_left _ _)
  · exact ((N.nrm_σ _ _ (S.idx_odd _)).trans (hr.eh k c)).trans (le_max_left _ _)
  · exact (rowBnd_evalErr F _ _ x hD (errBounds_encErrs M hr) c).trans (le_max_right _ _)

variable (S Wb J) in
/-- The correctness bound `B_χ + N n max(B_χ, B_F) K`, `N` the number of ring elements of a key. -/
def corrBound (T Bχ Bfl K : ℕ) : ℕ :=
  Bχ + Fintype.card (KCol Wb J S.τ S.E.W) * (S.E.n * max Bχ (evalBound S T Bχ Bfl) * K)

/-- `‖v kᵀ‖ ≤ |ι| · n · B · K`. -/
theorem nrm_dotProduct_le {ι : Type*} [Fintype ι] {v k : ι → R} {B K : ℕ} (hv : RowBnd N v B)
    (hk : RowBnd N k K) : N.nrm (v ⬝ᵥ k) ≤ Fintype.card ι * (S.E.n * B * K) :=
  (N.nrm_sum_le _ _ _ fun c _ => (N.nrm_mul _ _).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ (hv c)) (hk c))).trans (by rw [Finset.card_univ])

/-- **The noise of decryption** `e_m − e_F k_Fᵀ` is at most `corrBound`. -/
theorem nrm_decNoise_le (M : HelperMap S J) {w : ℕ} (half : R) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (x : Pos → ℕ) (m : R) {r : EncCoins S Wb J Pos} {Bχ Bfl K : ℕ} (hD : 1 ≤ S.gfac)
    (hr : CoinBounds N r Bχ Bfl) {k : KCol Wb J S.τ S.E.W → R} (hK : RowBnd N k K) :
    N.nrm (r.em - decErr M w half mpk F x m r ⬝ᵥ k) ≤ corrBound S Wb J F.T Bχ Bfl K :=
  (N.nrm_sub _ _).trans (Nat.add_le_add hr.em
    (nrm_dotProduct_le (rowBnd_decErr M half mpk F x m hD hr) hK))

/-- **Theorem 1** (correctness, deterministic form): for `F(x) = 0`, a valid key with coefficients
at most `K` and coins within the bounds, decryption returns `m`, provided `decode` recovers `m`
from `⌊q/2⌉ m + e` for every `e` within `corrBound`. -/
theorem decrypt_correct_of_bounds (h8 : Lemma8 S) (M : HelperMap S J) {w : ℕ} (half : R)
    (mpk : MPK S Wb J Pos) (F : BP Pos) (hF : F.WF S.E.W) (hw : F.w = w) (x : Pos → ℕ)
    (hx : ∀ t, x t < F.nsym) (hFx : F.eval x = 0) (m : R) (r : EncCoins S Wb J Pos)
    {Bχ Bfl K : ℕ} (hD : 1 ≤ S.gfac) (hr : CoinBounds N r Bχ Bfl) (k : KCol Wb J S.τ S.E.W → R)
    (hk : ValidKey M mpk F k) (hK : RowBnd N k K) {Msg : Type*} (decode : R → Msg) (mm : Msg)
    (hdecode : ∀ e, N.nrm e ≤ corrBound S Wb J F.T Bχ Bfl K → decode (half * m + e) = mm) :
    decrypt decode M mpk F k (encrypt M w half mpk x m r) = mm := by
  unfold decrypt
  rw [decryptRaw_encrypt h8 M half mpk F hF hw x hx hFx m r k hk, add_sub_assoc]
  exact hdecode _ (nrm_decNoise_le M half mpk F x m hD hr hK)

variable [DecidableEq R]

/-- **Theorem 1 for the keys of `KeyGen`**: every accepted output of one try of box rejection with
a good covered trapdoor decrypts correctly, when the small box and the decompositions are within
`K`. -/
theorem decrypt_correct_of_mem_support (h8 : Lemma8 S) (M : HelperMap S J) {w : ℕ} (half : R)
    (mpk : MPK S Wb J Pos) (F : BP Pos) (hF : F.WF S.E.W) (hw : F.w = w) (x : Pos → ℕ)
    (hx : ∀ t, x t < F.nsym) (hFx : F.eval x = 0) (m : R) (r : EncCoins S Wb J Pos)
    {Bχ Bfl K : ℕ} (hD : 1 ≤ S.gfac) (hr : CoinBounds N r Bχ Bfl)
    (Big Small : Finset (PIdx Wb J S.τ S.E.W → R)) (hBig : Big.Nonempty)
    (dec : (Fin S.E.W → R) → ZIdx S.τ S.E.W → R) (hdec : ∀ y, gadZ (dec y) = y)
    (T : (ZIdx S.τ S.E.W → R) → PIdx Wb J S.τ S.E.W → R) (hT : GoodTrap M mpk F T)
    (hcov : ∀ x ∈ Small, ∀ y, x + T (dec y) ∈ Big)
    (hSmall : ∀ v ∈ Small, RowBnd N v K) (hdecK : ∀ y, RowBnd N (dec y) K)
    (o : (PIdx Wb J S.τ S.E.W → R) × (ZIdx S.τ S.E.W → R))
    (ho : some o ∈ (keyLaw Big Small hBig dec M mpk F T).support)
    {Msg : Type*} (decode : R → Msg) (mm : Msg)
    (hdecode : ∀ e, N.nrm e ≤ corrBound S Wb J F.T Bχ Bfl K → decode (half * m + e) = mm) :
    decrypt decode M mpk F (keyOfOutput (some o)) (encrypt M w half mpk x m r) = mm := by
  obtain ⟨hs, ⟨y, hy⟩, hv⟩ := valid_of_mem_support Big Small hBig dec hdec M mpk F T hT hcov o ho
  refine decrypt_correct_of_bounds h8 M half mpk F hF hw x hx hFx m r hD hr _ hv ?_ decode mm hdecode
  intro c
  rcases c with ⟨i, w' | c⟩ | q
  · exact hSmall _ hs _
  · show N.nrm (o.2 (i, c)) ≤ K
    rw [← hy]; exact hdecK y _
  · exact hSmall _ hs _

end AdvancedEncryption.ExpLUT
