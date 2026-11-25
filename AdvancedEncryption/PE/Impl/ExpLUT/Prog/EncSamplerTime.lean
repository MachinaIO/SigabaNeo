import PE.Impl.ExpLUT.Prog.EncCoins
import PE.Impl.RingBTVW.Prog.SetupTime3
/-! # Compositional length and clock bounds for the complete encryption sampler -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.RingBTVW.Prog

/-- One's-complement leaves have the same length and time bound as the generic leaves. -/
theorem atbb_chainPM (K L η : ℕ) : ∀ f j, ATBb (chainPM K L η f j) (bChain K L f)
  | 0, j => atbb_leafP K L _
  | f + 1, j => ATBb.ifBlank 3 (atbb_leafP K L _) ((atbb_tail 3 (by decide)).seq
      (atbb_chainPM K L η f (j + 1)))

theorem atbb_cbdPM (η L K : ℕ) : ATBb (cbdPM η L K) (bCbd η L K) :=
  (ATBb.rep atbb_coinAp2 _).seq ((ATBb.rep atbb_bitAp3 _).seq ((ATBb.rep atbb_upStep _).seq
    ((ATBb.rep atbb_downStep _).seq (atbb_chainPM K L η _ _))))

/-- Explicit shape bound for all three independent blocks of the coin queue. -/
def encCoinsBound (D : Dims) (η L e : ℕ) : Bnd :=
  ((bCbd η L D.K).count (nEncSmall D * D.N)).seq
    (((bEntF D.K e).count (nFl D * D.N)).seq ((bCbd η L D.K).count D.N))

theorem atbb_encCoinsP (D : Dims) (η L e : ℕ) :
    ATBb (encCoinsP D η L e) (encCoinsBound D η L e) :=
  (atbb_repF (atbb_cbdPM η L D.K) (preserves_cbdPM η L D.K (by simp [Outside])) _).seq
    ((atbb_repF (atbb_entF D.K e) (preserves6_entF D.K e) _).seq
      (atbb_repF (atbb_cbdPM η L D.K) (preserves_cbdPM η L D.K (by simp [Outside])) _))

end AdvancedEncryption.ExpLUT.Prog
