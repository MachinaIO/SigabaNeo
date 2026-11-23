import SigabaNeo.Lib.Lattices.Research.Wall1.HermiteSevenTwentyFour
import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledSuffixDescent

/-! Certified log-length bounds for physical suffixes using sharp ranks five and six,
two Mordell steps, and the Blichfeldt bound from rank nine onward. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane.ProvedProfile
open Real Finset TerminalProjection TerminalInterval BKZ

def gamma (k : ℕ) : ℝ :=
  if k = 7 then (64/3 : ℝ) ^ (1/5 : ℝ)
  else if k = 8 then (64/3 : ℝ) ^ (7/30 : ℝ)
  else if k = 24 then blichfeldtConstant 24 else flagGamma k

private theorem gamma_pos (k : ℕ) : 0 < gamma k := by
  unfold gamma flagGamma
  repeat' split
  all_goals first | positivity | exact auditedGamma_pos _ | exact blichfeldtConstant_pos _

theorem family (k : ℕ) (hk : 2 ≤ k) : FamilyHermite k (gamma k) := by
  by_cases h : k ≤ 8
  · interval_cases k
    · exact familyHermite_two
    · exact familyHermite_three
    · exact familyHermite_four
    · exact familyHermite_of_intrinsic (Watson.intrinsic_five_of_finite_gram
        (Watson.finite_gram_of_vertex_coverage Watson.vertexCoverage))
    · exact familyHermite_of_intrinsic Watson.intrinsic_rank_six
    · exact familyHermite_of_intrinsic Watson.intrinsic_seven_mordell
    · exact familyHermite_of_intrinsic Watson.intrinsic_eight_mordell
  · by_cases h24 : k = 24
    · subst k
      apply familyHermite_of_intrinsic
      change IntrinsicHermite 24 (2/π * Gamma ((24:ℝ)/2+2)^(2/(24:ℝ)))
      rw [show (24:ℝ)/2+2 = (13:ℕ)+1 by norm_num, Gamma_nat_eq_factorial]
      convert Watson.intrinsic_twentyfour_blichfeldt using 1
      norm_num
    · let : NeZero k := ⟨by omega⟩
      simpa only [gamma, ite_eq_right (show k ≠ 7 by omega), ite_eq_right (show k ≠ 8 by omega),
        ite_eq_right h24, flagGamma, ite_eq_right (show k ≠ 1 by omega), auditedGamma,
        ite_eq_right (show ¬(2 ≤ k ∧ k ≤ 8) by omega)] using familyHermite_blichfeldt k

-- Upper endpoints in units of 10⁻¹² for γ, log γ, the mean penalty and the running log cap.
private def rows : Array (ℕ × ℕ × ℕ × ℕ) := #[
  (1000000000000, 0, 0, 0),
  (1000000000000, 0, 0, 0),
  (1154700538382, 143841036231, 71920518116, 143841036232),
  (1259921049897, 231049060191, 129682783164, 245207313260),
  (1414213562376, 346573590285, 187445048212, 360731843355),
  (1515716566513, 415888308340, 239431086755, 447375240925),
  (1665366355314, 510045132453, 290435600001, 545458166228),
  (1844215822965, 612054158942, 341440113247, 647467192718),
  (2042272555119, 714063185431, 392444626493, 749476219209),
  (2240646452560, 806764419127, 442867402689, 846249612253),
  (2373267119106, 864267537116, 490882265863, 923016034421),
  (2505032482190, 918301701397, 536797350933, 995948201632),
  (2636039289650, 969277521558, 580855420095, 1065494180874),
  (2766368182017, 1017535334299, 623252725691, 1132020392841),
  (2896087147768, 1063360566535, 664151209020, 1195831492288),
  (3025254088492, 1106995084154, 703686747740, 1257184289817),
  (3153918757730, 1148645729724, 741974938731, 1316297803593),
  (3282124249903, 1188490849938, 779115277792, 1373360702761),
  (3409908160017, 1226685358389, 815194258922, 1428536938117),
  (3537303498493, 1263364713300, 850287723181, 1481970079831),
  (3664339421152, 1298648079301, 884462672637, 1533786712288),
  (3791041817775, 1332640867279, 917778694319, 1584099127959),
  (3917433791161, 1365436794319, 950289094184, 1633007491344),
  (4043536050444, 1397119569170, 982041811666, 1680601596251),
  (4169367236587, 1427764282474, 1013080165633, 1726962306870),
  (4294944193753, 1457438562049, 1043443469010, 1772162750035),
  (4420282197046, 1486203539540, 1073167539801, 1816269309571),
  (4545395144904, 1514114664426, 1102285129502, 1859342461715),
  (4670295722524, 1541222393559, 1130826284939, 1901437481719),
  (4794995541475, 1567572778510, 1158818655984, 1942605045239),
  (4919505259569, 1593207968452, 1186287758889, 1982891743115),
  (5043834684267, 1618166642839, 1213257202937, 2022340524357),
  (5167992862296, 1642484385347, 1239748886572, 2060991079246),
  (5291988157620, 1666194008464, 1265783167955, 2098880172187),
  (5415828319583, 1689325836362, 1291379013961, 2136041932142),
  (5539520542650, 1711907952368, 1316554130908, 2172508107092),
  (5663071518991, 1733966416225, 1341325079712, 2208308287825),
  (5786487484916, 1755525455499, 1365707377706, 2243470105456),
  (5909774262007, 1776607634753, 1389715588987, 2278019406364),
  (6032937293663, 1797234005517, 1413363404850, 2311980407609),
  (6155981677667, 1817424239637, 1436663715615, 2345375835434),
  (6278912195285, 1837196748167, 1459628674968, 2378227049052),
  (6401733337336, 1856568787658, 1482269757745, 2410554151574),
  (6524449327598, 1875556555412, 1504597811977, 2442376089683),
  (6647064143889, 1894175275066, 1526623105874, 2473710743407),
  (6769581537079, 1912439273654, 1548355370348, 2504575007175),
  (6892005048288, 1930362051153, 1569803837584, 2534984863161),
  (7014338024461, 1947956343382, 1590977276100, 2564955447791),
  (7136583632520, 1965234179004, 1611884022686, 2594501112188),
  (7258744872228, 1982206931280, 1632532011554, 2623635477194),
  (7380824587918, 1998885365153, 1652928800995, 2652371483572),
  (7502825479199, 2015279680159, 1673081597797, 2680721437877),
  (7624750110750, 2031399549598, 1692997279656, 2708697054455),
  (7746600921285, 2047254156357, 1712682415775, 2736309493954),
  (7868380231788, 2062852225720, 1732143285829, 2763569398689),
  (7990090253072, 2078202055471, 1751385897454, 2790486925190),
  (8111733092736, 2093311543541, 1770416002396, 2817071774167),
  (8233310761581, 2108188213456, 1789239111445, 2843333218173),
  (8354825179525, 2122839237776, 1807860508268, 2869280127156),
  (8476278181073, 2137271459723, 1826285262232, 2894920992094),
  (8597671520378, 2151491413157, 1844518240310, 2920263946889),
  (8719006875921, 2165505341061, 1862564118153, 2945316788684),
  (8840285854866, 2179319212653, 1880427390388, 2970086996715),
  (8961509997091, 2192938739251, 1898112380221, 2994581749847),
  (9082680778944, 2206369389013, 1915623248388, 3018807942895),
  (9203799616731, 2219616400614, 1932964001518, 3042772201825),
  (9324867869972, 2232684795992, 1950138499949, 3066480897945),
  (9445886844437, 2245579392200, 1967150465042, 3089940161142),
  (9566857794971, 2258304812469, 1984003486031, 3113155892266),
  (9687781928149, 2270865496519, 2000701026447, 3136133774707),
  (9808660404747, 2283265710203, 2017246430145, 3158879285247),
  (9929494342057, 2295509554513, 2033642926963, 3181397704220),
  (10050284816065, 2307600974013, 2049893638048, 3203694125055),
  (10171032863480, 2319543764737, 2066001580859, 3225773463228),
  (10291739483651, 2331341581592, 2081969673884, 3247640464680),
  (10412405640361, 2342997945304, 2097800741082, 3269299713734),
  (10533032263511, 2354516248941, 2113497516075, 3290755640546),
  (10653620250716, 2365899764040, 2129062646102, 3312012528122),
  (10774170468793, 2377151646374, 2144498695754, 3333074518941),
  (10894683755173, 2388274941376, 2159808150507, 3353945621195),
  (11015160919233, 2399272589250, 2174993420060, 3374629714685),
  (11135602743545, 2410147429785, 2190056841497, 3395130556390),
  (11256009985062, 2420902206902, 2205000682281, 3415451785732),
  (11376383376238, 2431539572938, 2219827143092, 3435596929561),
  (11496723626086, 2442062092700, 2234538360518, 3455569406868),
  (11617031421175, 2452472247288, 2249136409609, 3475372533253),
  (11737307426585, 2462772437722, 2263623306302, 3495009525163),
  (11857552286798, 2472964988360, 2278001009723, 3514483503903),
  (11977766626553, 2483052150148, 2292271424380, 3533797499454),
  (12097951051653, 2493036103692, 2306436402242, 3552954454088),
  (12218106149728, 2502918962171, 2320497744727, 3571957225813),
  (12338232490967, 2512702774101, 2334457204584, 3590808591635),
  (12458330628807, 2522389525959, 2348316487694, 3609511250674),
  (12578401100587, 2531981144675, 2362077254785, 3628067827123),
  (12698444428178, 2541479499995, 2375741123065, 3646480873063),
  (12818461118576, 2550886406737, 2389309667782, 3664752871151),
  (12938451664465, 2560203626929, 2402784423714, 3682886237179),
  (13058416544759, 2569432871841, 2416166886589, 3700883322510),
  (13178356225117, 2578575803933, 2429458514445, 3718746416412),
  (13298271158430, 2587634038693, 2442660728929, 3736477748276),
  (13418161785290, 2596609146403, 2455774916538, 3754079489740),
  (13538028534434, 2605502653816, 2468802429808, 3771553756716),
  (13657871823175, 2614316045754, 2481744588451, 3788902611328),
  (13777692057802, 2623050766641, 2494602680445, 3806128063766),
  (13897489633972, 2631708221956, 2507377963076, 3823232074054),
  (14017264937083, 2640289779631, 2520071663940, 3840216553756),
  (14137018342626, 2648796771377, 2532684981899, 3857083367588),
  (14256750216529, 2657230493963, 2545219088003, 3873834334985),
  (14376460915478, 2665592210425, 2557675126370, 3890471231583),
  (14496150787230, 2673883151238, 2570054215034, 3906995790653),
  (14615820170915, 2682104515425, 2582357446757, 3923409704470),
  (14735469397317, 2690257471628, 2594585889810, 3939714625624),
  (14855098789151, 2698343159124, 2606740588725, 3955912168287),
  (14974708661325, 2706362688811, 2618822565015, 3972003909421),
  (15094299321193, 2714317144144, 2630832817866, 3987991389938),
  (15213871068798, 2722207582031, 2642772324805, 4003876115821),
  (15333424197099, 2730035033704, 2654642042343, 4019659559195),
  (15452958992203, 2737800505539, 2666442906592, 4035343159362),
  (15572475733572, 2745504979860, 2678175833857, 4050928323787),
  (15691974694230, 2753149415694, 2689841721212, 4066416429059),
  (15811456140966, 2760734749511, 2701441447051, 4081808821807),
  (15930920334520, 2768261895923, 2712975871618, 4097106819580),
  (16050367529765, 2775731748367, 2724445837521, 4112311711705),
  (16169797975888, 2783145179753, 2735852170225, 4127424760102),
  (16289211916557, 2790503043089, 2747195678531, 4142447200076),
  (16408609590081, 2797806172086, 2758477155032, 4157380241075),
  (16527991229576, 2805055381739, 2769697376559, 4172225067429),
  (16647357063105, 2812251468881, 2780857104611, 4186982839052),
  (16766707313836, 2819395212722, 2791957085764, 4201654692125),
  (16886042200172, 2826487375369, 2802998052075, 4216241739760),
  (17005361935894, 2833528702322, 2813980721464, 4230745072625),
  (17124666730290, 2840519922956, 2824905798091, 4245165759569),
  (17243956788277, 2847461750985, 2835773972714, 4259504848207),
  (17363232310530, 2854354884906, 2846585923036, 4273763365489),
  (17482493493595, 2861200008432, 2857342314046, 4287942318262),
  (17601740530000, 2867997790907, 2868043798341, 4302042693795),
  (17720973608373, 2874748887709, 2878691016444, 4316065460299),
  (17840192913539, 2881453940635, 2889284597109, 4330011567427),
  (17959398626628, 2888113578275, 2899825157614, 4343881946752),
  (18078590925169, 2894728416375, 2910313304051, 4357677512239),
  (18197769983192, 2901299058182, 2920749631599, 4371399160690),
  (18316935971315, 2907826094786, 2931134724795, 4385047772188),
  (18436089056834, 2914310105443, 2941469157794, 4398624210516),
  (18555229403811, 2920751657888, 2951753494618, 4412129323562),
  (18674357173157, 2927151308644, 2961988289404, 4425563943726),
  (18793472522713, 2933509603310, 2972174086638, 4438928888293),
  (18912575607328, 2939827076853, 2982311421386, 4452224959813),
  (19031666578936, 2946104253878, 2992400819516, 4465452946455),
  (19150745586624, 2952341648899, 3002442797914, 4478613622364),
  (19269812776713, 2958539766591, 3012437864694, 4491707747990),
  (19388868292817, 2964699102047, 3022386519399, 4504736070423),
  (19507912275917, 2970820141014, 3032289253203, 4517699323710),
  (19626944864419, 2976903360132, 3042146549098, 4530598229164),
  (19745966194223, 2982949227159, 3051958882083, 4543433495663),
  (19864976398781, 2988958201188, 3061726719342, 4556205819936),
  (19983975609155, 2994930732866, 3071450520423, 4568915886856)]

private def g (k : ℕ) : ℚ := (rows[k]!.1 : ℚ)/10^12
private def lg (k : ℕ) : ℚ := (rows[k]!.2.1 : ℚ)/10^12
private def peel (k : ℕ) : ℚ := (rows[k]!.2.2.1 : ℚ)/10^12
def logCap (k : ℕ) : ℚ := (rows[k]!.2.2.2 : ℚ)/10^12

private def gammaSq : ℕ → ℚ
  | 0 => 1
  | 1 => 9*3.14159265358979323847/16
  | k+2 => ((k:ℚ)/2+2)^2 * gammaSq k

private theorem gamma_sq (k : ℕ) : Gamma ((k:ℝ)/2+2)^2 ≤ (gammaSq k:ℝ) := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [gammaSq, Gamma_two]
  | one =>
    have hh := Gamma_add_one (show (3/2:ℝ) ≠ 0 by norm_num)
    have h := Gamma_add_one (show (1/2:ℝ) ≠ 0 by norm_num)
    norm_num at hh h ⊢
    rw [hh,h,Gamma_one_half_eq,mul_pow,mul_pow,sq_sqrt pi_pos.le]
    norm_num [gammaSq]
    linarith [pi_lt_d20]
  | more k ih _ =>
    rw [show ((k+2:ℕ):ℝ)/2+2 = ((k:ℝ)/2+2)+1 by push_cast; ring,
      Gamma_add_one (by positivity), mul_pow]
    simpa [gammaSq] using mul_le_mul_of_nonneg_left ih (sq_nonneg ((k:ℝ)/2+2))

private def hp : ℕ → ℚ
  | 2 => 4/3 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 64/3 | 7 => 64 | 8 => 256 | _ => 1

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem gamma_bound (k : ℕ) (hk : k ≤ 155) : gamma k ≤ g k := by
  have cert : ∀ i : Fin 156, 0 < g i ∧ (if i.val = 0 ∨ i.val = 1 then 1 ≤ g i
    else if i.val = 7 then 64/3 ≤ g i ^ 5 else if i.val = 8 then (64/3)^7 ≤ g i ^ 30 else if i.val ≤ 6 then hp i ≤ g i ^ i.val
    else gammaSq i ≤ (g i * 3.14159265358979323846/2)^i.val) := by decide +kernel
  obtain ⟨hg,H⟩ := cert ⟨k,by omega⟩
  change 0 < g k at hg
  have hg' : 0 < (g k : ℝ) := by exact_mod_cast hg
  change (if k = 0 ∨ k = 1 then _ else _) at H
  by_cases h0 : k = 0
  · subst k
    norm_num [gamma,flagGamma,auditedGamma,blichfeldtConstant,g,rows]
    exact (div_le_one pi_pos).mpr (by linarith [pi_gt_three])
  by_cases h1 : k = 1
  · subst k; norm_num [gamma,flagGamma,g,rows]
  by_cases h7 : k = 7
  · subst k
    change (64/3 : ℝ) ^ (1/5 : ℝ) ≤ _
    rw [one_div]
    apply (rpow_inv_le_iff_of_pos (by norm_num) hg'.le (by norm_num : (0:ℝ) < 5)).2
    norm_num [g,rows]
  by_cases h8 : k = 8
  · subst k
    change (64/3 : ℝ) ^ (7/30 : ℝ) ≤ _
    rw [div_eq_mul_inv (7:ℝ) 30, rpow_mul (by norm_num), ← Nat.cast_ofNat (R:=ℝ) (n:=7), rpow_natCast]
    apply (rpow_inv_le_iff_of_pos (by positivity) hg'.le (by norm_num : (0:ℝ) < 30)).2
    norm_num [g,rows]
  have hk' : 0 < (k:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero h0)
  have eq : gamma k = auditedGamma k := by
    by_cases h24 : k = 24
    · subst k; rfl
    · simp [gamma,h7,h8,h24,flagGamma,h1]
  rw [eq,auditedGamma]
  by_cases hs : k ≤ 6
  · rw [ite_eq_left ⟨by omega,by omega⟩,div_eq_mul_inv,← rpow_def_of_pos]
    · apply (rpow_inv_le_iff_of_pos (by interval_cases k <;> norm_num [hermitePower]) hg'.le hk').mpr
      rw [rpow_natCast]
      have hh : hp k ≤ g k^k := by simpa [h0,h1,h7,h8,hs] using H
      have eq : hermitePower k = (hp k : ℝ) := by interval_cases k <;> norm_num [hermitePower,hp]
      rw [eq]; exact_mod_cast hh
    · interval_cases k <;> norm_num [hermitePower]
  · rw [ite_eq_right (by omega)]
    unfold blichfeldtConstant
    have hG := Gamma_pos_of_pos (by positivity : 0 < (k:ℝ)/2+2)
    have poweq : Gamma ((k:ℝ)/2+2)^(2/(k:ℝ)) = (Gamma ((k:ℝ)/2+2)^2)^((k:ℝ)⁻¹) := by
      rw [← rpow_natCast_mul hG.le]; norm_num [div_eq_mul_inv]
    rw [poweq,div_mul_eq_mul_div,div_le_iff₀ pi_pos]
    suffices (Gamma ((k:ℝ)/2+2)^2)^((k:ℝ)⁻¹) ≤ g k*π/2 by linarith
    apply (rpow_inv_le_iff_of_pos (sq_nonneg _) (by positivity) hk').mpr
    rw [rpow_natCast]
    have hh : gammaSq k ≤ (g k*3.14159265358979323846/2)^k := by simpa [h0,h1,h7,h8,hs] using H
    apply (gamma_sq k).trans ((Rat.cast_le (K := ℝ)).2 hh |>.trans ?_)
    push_cast
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    linarith [pi_gt_d20]

private theorem log_gamma (k : ℕ) (hk : k ≤ 155) : log (gamma k) ≤ lg k := by
  have check : ∀ i : Fin 156, 0 ≤ lg i ∧ g i ≤ taylor (lg i/4) 20 ^ 4 := by decide +kernel
  obtain ⟨h₁,h₂⟩ := check ⟨k,by omega⟩
  change 0 ≤ lg k at h₁
  change g k ≤ taylor (lg k/4) 20 ^ 4 at h₂
  apply (log_le_iff_le_exp (gamma_pos _)).mpr
  apply (gamma_bound _ hk).trans
  have hh := exp_lower (lg k/4) (taylor (lg k/4) 20) (by positivity) le_rfl
  have ht : 0 ≤ taylor (lg k/4) 20 := by unfold taylor; positivity
  have eq : (lg k:ℝ) = (4:ℕ)*((lg k/4:ℚ):ℝ) := by push_cast; ring
  rw [eq, exp_nat_mul]
  apply ((Rat.cast_le (K := ℝ)).2 h₂).trans
  rw [Rat.cast_pow]
  exact pow_le_pow_left₀ (by exact_mod_cast ht) hh 4

/-- Convert the physical Hermite inequalities into an upper bound for each log length. -/
theorem physical_log_cap {m : ℕ} (Q : PhysicalSuffix m) (l : ℕ)
    (hl : 1 ≤ l) (hm : l ≤ m) (ht : m ≤ 155) : Q.a l ≤ (logCap l : ℝ) := by
  have rpos : 0 < planeRadius := by unfold planeRadius areaCut; positivity
  have terminal : Q.a 1 ≤ 0 := sub_nonpos.mpr (log_le_log (suffixLength_pos ..) Q.short)
  have step (k : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m) :
      Q.a k ≤ (lg k : ℝ)/2 + (∑ r ∈ Icc 1 k, Q.a r)/(k:ℝ) := by
    have h := suffix_hermite Q.steps Q.state k hk (by rw [Q.rank_eq]; exact hkm) (family k hk)
    have pos := suffixLength_pos Q.steps Q.state
    have pp := prod_pos (s := Icc 1 k) (fun i _ ↦ pos i)
    have H := log_le_log (sq_pos_of_pos (pos k)) h
    rw [log_pow,log_mul (gamma_pos _).ne' (rpow_pos_of_pos pp _).ne',log_rpow pp,
      log_prod (fun i _ ↦ (pos i).ne')] at H
    have hk' : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    simp only [PhysicalSuffix.a,sum_sub_distrib,sum_const,Nat.card_Icc,nsmul_eq_mul,
      Nat.add_one_sub_one]
    have bound := log_gamma k (hkm.trans ht)
    field_simp [hk'.ne'] at H ⊢
    norm_num1 at H
    nlinarith [mul_le_mul_of_nonneg_right bound hk'.le]
  have mean (k : ℕ) (lo : 1 ≤ k) (hi : k ≤ m) :
      (∑ r ∈ Icc 1 k, Q.a r)/(k:ℝ) ≤ (peel k : ℝ) := by
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hz : k = 0
      · subst k; simpa [peel,rows] using terminal
      have hk : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hz
      have hp : 0 < (k:ℝ)+1 := by positivity
      have old := ih (by omega) (by omega)
      have H := step (k+1) (by omega) hi
      rw [sum_Icc_succ_top (by omega),Nat.cast_succ] at H ⊢
      have cert : ∀ i : Fin 155, 0 < i.val →
          peel i + lg (i.val+1)/(2*(i.val:ℚ)) ≤ peel (i.val+1) := by decide +kernel
      have C := (Rat.cast_le (K:=ℝ)).2 (cert ⟨k,by omega⟩ (by change 0 < k; omega))
      change ((peel k + lg (k+1)/(2*(k:ℚ)) : ℚ):ℝ) ≤ _ at C
      push_cast at C
      apply le_trans _ C
      apply le_trans _ (add_le_add_left old _)
      field_simp [hk.ne',hp.ne'] at H ⊢
      nlinarith
  by_cases h : l = 1
  · subst l; simpa [logCap,rows] using terminal
  have cert : ∀ i : Fin 156, lg i/2 + peel i ≤ logCap i := by decide +kernel
  have HH := (Rat.cast_le (K:=ℝ)).2 (cert ⟨l,by omega⟩)
  change ((lg l/2+peel l:ℚ):ℝ) ≤ _ at HH
  push_cast at HH
  linarith only [HH,step l (by omega) hm,mean l hl hm]

def cap (k : ℕ) : ℝ := exp (logCap k : ℝ)

theorem physical_cap {m : ℕ} (Q : PhysicalSuffix m) {l k : ℕ} (hl : 1 ≤ l) (hm : l ≤ m)
    (ht : m ≤ 155) (hlk : l ≤ k) (hk : k ≤ 155) : exp (Q.a l) ≤ cap k := by
  have check : ∀ i : Fin 155, logCap i ≤ logCap (i.val+1) := by decide +kernel
  have mono : logCap l ≤ logCap k := by
    induction k, hlk using Nat.le_induction with
    | base => rfl
    | succ k _ ih => exact (ih (by omega)).trans (check ⟨k,by omega⟩)
  exact exp_le_exp.mpr ((physical_log_cap Q l hl hm ht).trans (by exact_mod_cast mono))

end SigabaNeo.Wall1.ControlledPlane.ProvedProfile

#print axioms SigabaNeo.Wall1.ControlledPlane.ProvedProfile.family
#print axioms SigabaNeo.Wall1.ControlledPlane.ProvedProfile.physical_cap
