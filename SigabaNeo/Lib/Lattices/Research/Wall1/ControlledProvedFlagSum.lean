import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledProvedFlags

/-! Outward rational certificate for the full triangular sum. Each omitted entry costs 10⁻²⁶. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane.ProvedProfile
open Real Finset TerminalProjection TerminalInterval

set_option maxRecDepth 10000
set_option maxHeartbeats 0

-- Cumulative upper log caps, lower determinant logs and lower width corrections in 10⁻¹².
private def logs : Array (ℕ × ℕ × ℕ) := #[
  (0, 3244170895030000, 2194329801438),
  (0, 3236060467792424, 2193340681432),
  (143841036232, 3227950040554848, 2192349600830),
  (389048349492, 3219839613317272, 2191356551844),
  (749780192847, 3211729186079696, 2190361526640),
  (1197155433772, 3203618758842120, 2189364517336),
  (1742613600000, 3195508331604544, 2188365516005),
  (2390080792718, 3187397904366968, 2187364514670),
  (3139557011927, 3179287477129392, 2186361505306),
  (3985806624180, 3171177049891816, 2185356479842),
  (4908822658601, 3163066622654240, 2184349430156),
  (5904770860233, 3154956195416664, 2183340348078),
  (6970265041107, 3146845768179088, 2182329225388),
  (8102285433948, 3138735340941512, 2181316053815),
  (9298116926236, 3130624913703936, 2180300825040),
  (10555301216053, 3122514486466360, 2179283530691),
  (11871599019646, 3114404059228784, 2178264162346),
  (13244959722407, 3106293631991208, 2177242711531),
  (14673496660524, 3098183204753632, 2176219169720),
  (16155466740355, 3090072777516056, 2175193528335),
  (17689253452643, 3081962350278480, 2174165778744),
  (19273352580602, 3073856930897123, 2173135912263),
  (20906360071946, 3065767530131144, 2172103920152),
  (22586961668197, 3057694116323200, 2171069793620),
  (24313923975067, 3049636657878513, 2170033523819),
  (26086086725102, 3041595123264745, 2168995101847),
  (27902356034673, 3033569481011873, 2167954518745),
  (29761698496388, 3025559699712070, 2166911765499),
  (31663135978107, 3017565748019579, 2165866833040),
  (33605741023346, 3009587594650591, 2164819712238),
  (35588632766461, 3001625208383123, 2163770393910),
  (37610973290818, 2993678558056895, 2162718868811),
  (39671964370064, 2985747612573209, 2161665127641),
  (41770844542251, 2977832340894827, 2160609161040),
  (43906886474393, 2969932712045848, 2159550959587),
  (46079394581485, 2962048695111591, 2158490513802),
  (48287702869310, 2954180259238469, 2157427814146),
  (50531172974766, 2946327373633871, 2156362851017),
  (52809192381130, 2938490007566041, 2155295614753),
  (55121172788739, 2930668130363957, 2154226095628),
  (57466548624173, 2922861711417213, 2153154283857),
  (59844775673225, 2915070720175898, 2152080169588),
  (62255329824799, 2907295126150475, 2151003742907),
  (64697705914482, 2899534898911663, 2149924993837),
  (67171416657889, 2891790008090319, 2148843912335),
  (69675991665064, 2884060423377318, 2147760488292),
  (72210976528225, 2876346114523433, 2146674711535),
  (74775931976016, 2868647051339220, 2145586571824),
  (77370433088204, 2860963203694897, 2144496058851),
  (79994068565398, 2853294541520227, 2143403162241),
  (82646440048970, 2845641034804400, 2142307871551),
  (85327161486847, 2838002653595916, 2141210176269),
  (88035858541302, 2830379368002469, 2140110065815),
  (90772168035256, 2822771148190827, 2139007529535),
  (93535737433945, 2815177964386718, 2137902556710),
  (96326224359135, 2807599786874712, 2136795136545),
  (99143296133302, 2800036585998105, 2135685258176),
  (101986629351475, 2792488332158804, 2134572910665),
  (104855909478631, 2784954995817209, 2133458083001),
  (107750830470725, 2777436547492099, 2132340764101),
  (110671094417614, 2769932957760517, 2131220942804),
  (113616411206298, 2762444197257654, 2130098607877),
  (116586498203013, 2754970236676733, 2128973748010),
  (119581079952860, 2747511046768897, 2127846351816),
  (122599887895755, 2740066598343092, 2126716407833),
  (125642660097580, 2732636862265955, 2125583904517),
  (128709140995525, 2725221809461698, 2124448830250),
  (131799081156667, 2717821410911994, 2123311173331),
  (134912237048933, 2710435637655867, 2122170921982),
  (138048370823640, 2703064460789574, 2121028064342),
  (141207250108887, 2695707851466495, 2119882588468),
  (144388647813107, 2688365780897019, 2118734482338),
  (147592341938162, 2681038220348431, 2117583733844),
  (150818115401390, 2673725141144801, 2116430330795),
  (154065755866070, 2666426514666870, 2115274260916),
  (157335055579804, 2659142312351939, 2114115511846),
  (160625811220350, 2651872505693757, 2112954071138),
  (163937823748472, 2644617066242409, 2111789926258),
  (167270898267413, 2637375965604206, 2110623064585),
  (170624843888608, 2630149175441573, 2109453473408),
  (173999473603293, 2622936667472937, 2108281139929),
  (177394604159683, 2615738413472618, 2107106051256),
  (180810055945415, 2608554385270719, 2105928194410),
  (184245652874976, 2601384554753013, 2104747556317),
  (187701222281844, 2594228893860836, 2103564123812),
  (191176594815097, 2587087374590976, 2102377883635),
  (194671604340260, 2579959968995562, 2101188822433),
  (198186087844163, 2572846649181957, 2099996926755),
  (201719885343617, 2565747387312648, 2098802183056),
  (205272839797705, 2558662155605136, 2097604577693),
  (208844797023518, 2551590926331829, 2096404096924),
  (212435605615153, 2544533671819931, 2095200726909),
  (216045116865827, 2537490364451338, 2093994453706),
  (219673184692950, 2530460976662524, 2092785263274),
  (223319665566013, 2523445480944439, 2091573141469),
  (226984418437164, 2516443849842398, 2090358074042),
  (230667304674343, 2509456055955974, 2089140046643),
  (234368187996853, 2502482071938890, 2087919044815),
  (238086934413265, 2495521870498915, 2086695053996),
  (241823412161541, 2488575424397754, 2085468059515),
  (245577491651281, 2481642706450944, 2084238046595),
  (249349045407997, 2474723689527744, 2083005000347),
  (253137948019325, 2467818346551032, 2081768905774),
  (256944076083091, 2460926650497199, 2080529747767),
  (260767308157145, 2454048574396042, 2079287511103),
  (264607524710901, 2447184091330658, 2078042180447),
  (268464608078489, 2440333174437340, 2076793740348),
  (272338442413474, 2433495796905471, 2075542175239),
  (276228913645057, 2426671931977420, 2074287469436),
  (280135909435710, 2419861552948436, 2073029607137),
  (284059319140180, 2413064633166545, 2071768572421),
  (287999033765804, 2406281146032444, 2070504349244),
  (291954945934091, 2399511064999399, 2069236921443),
  (295926949843512, 2392754363573139, 2067966272728),
  (299914941233450, 2386011015311753, 2066692386689),
  (303918817349271, 2379280993825587, 2065415246787),
  (307938476908466, 2372564272777141, 2064134836356),
  (311973820067828, 2365860825880964, 2062851138603),
  (316024748391615, 2359170626903554, 2061564136605),
  (320091164820674, 2352493649663254, 2060273813309),
  (324172973642481, 2345829868030148, 2058980151526),
  (328270080462061, 2339179255925961, 2057683133938),
  (332382392173766, 2332541787323956, 2056382743088),
  (336509816933868, 2325917436248833, 2055078961384),
  (340652264133944, 2319306176776625, 2053771771097),
  (344809644375019, 2312707983034599, 2052461154357),
  (348981869442448, 2306122829201154, 2051147093154),
  (353168852281500, 2299550689505720, 2049829569335),
  (357370506973625, 2292991538228657, 2048508564604),
  (361586748713385, 2286445349701153, 2047184060518),
  (365817493786010, 2279912098305126, 2045856038489),
  (370062659545579, 2273391758473123, 2044524479779),
  (374322164393786, 2266884304688219, 2043189365501),
  (378595927759275, 2260389711483918, 2041850676616),
  (382883870077537, 2253907953444052, 2040508393930),
  (387185912771332, 2247439005202684, 2039162498098),
  (391501978231631, 2240982841444006, 2037812969613),
  (395831989799058, 2234539436902243, 2036459788814),
  (400175871745810, 2228108766361550, 2035102935878),
  (404533549258049, 2221690804655918, 2033742390821),
  (408904948418739, 2215285526669072, 2032378133495),
  (413289996190927, 2208892907334374, 2031010143585),
  (417688620401443, 2202512921634724, 2029638400612),
  (422100749725005, 2196145544602465, 2028262883926),
  (426526313668731, 2189790751319282, 2026883572707),
  (430965242557024, 2183448516916105, 2025500445960),
  (435417467516837, 2177118816573013, 2024113482519),
  (439882920463292, 2170801625519137, 2022722661038),
  (444361534085656, 2164496919032561, 2021327959994),
  (448853241833646, 2158204672440227, 2019929357684),
  (453357977904069, 2151924861117839, 2018526832220),
  (457875677227779, 2145657460489764, 2017120361532),
  (462406275456943, 2139402446028938, 2015709923361),
  (466949708952606, 2133159793256769, 2014295495260),
  (471505914772542, 2126929477743044, 2012877054593),
  (476074830659398, 2120711475105828, 2011454578527)]

private def nontrivial : Array (Array ℕ) := #[
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[3],
  #[9],
  #[33],
  #[132, 3],
  #[522, 7],
  #[2005, 22],
  #[7446, 74],
  #[26693, 254, 4],
  #[92307, 842, 9],
  #[307765, 2703, 25],
  #[988913, 8363, 70],
  #[3060938, 24924, 199, 3],
  #[9122431, 71490, 548, 6],
  #[26165277, 197262, 1450, 12],
  #[72192819, 523347, 3696, 27],
  #[190560537, 1327683, 9006, 61],
  #[475715783, 3183895, 20736, 133],
  #[1122624630, 7213978, 45089, 275, 3],
  #[2503147542, 15435852, 92539, 541, 5],
  #[5270978277, 31175222, 179175, 1002, 7],
  #[10476889167, 59400548, 327109, 1750, 11],
  #[19646653060, 106720353, 562785, 2882, 16],
  #[34740322138, 180696180, 911988, 4466, 23],
  #[57894475258, 288177134, 1391203, 6512, 31],
  #[90878740293, 432650861, 1996643, 8930, 40],
  #[134297524990, 611133955, 2694427, 11506, 49],
  #[186727163220, 811715392, 3416887, 13923, 56],
  #[244134113732, 1013168555, 4069388, 15813, 61],
  #[299966605800, 1187698837, 4548751, 16845, 62],
  #[346160041423, 1306795926, 4769179, 16819, 59],
  #[374947628249, 1348683055, 4687065, 15731, 52],
  #[380958595190, 1304758630, 4314945, 13773, 44],
  #[362840579896, 1182440928, 3718522, 11280, 34],
  #[323739468107, 1003140505, 2997669, 8636, 25],
  #[270409014441, 796111933, 2258940, 6176, 18],
  #[211295076966, 590617530, 1590069, 4122, 12],
  #[154344097528, 409298993, 1044701, 2567, 8],
  #[105318672952, 264759636, 640177, 1489, 5],
  #[67082618272, 159737282, 365594, 805, 3],
  #[39853872497, 89817856, 194419, 405],
  #[22067105039, 47029564, 96197, 190],
  #[11378485491, 22912493, 44249, 83],
  #[5459200228, 10377651, 18906, 34],
  #[2435068707, 4365903, 7497, 14],
  #[1008913380, 1704554, 2757, 6],
  #[387945029, 617039, 940, 3],
  #[138313112, 206906, 297],
  #[45680017, 64206, 88],
  #[13961791, 18421, 25],
  #[3945292, 4882, 7],
  #[1029676, 1195, 3],
  #[247944, 270],
  #[55028, 57],
  #[11244, 12],
  #[2114, 3],
  #[366],
  #[59],
  #[10],
  #[3]]

private def cum (k : ℕ) : ℚ := (logs[k]!.1:ℚ)/10^12
private def floorLog (k : ℕ) : ℚ := (logs[k]!.2.1:ℚ)/10^12
private def widthLog (j : ℕ) : ℚ := (logs[j]!.2.2:ℚ)/10^12
private def units (i j : ℕ) : ℕ := (((nontrivial[i]?).getD #[])[j]?).getD 1

private def up (x : ℚ) := taylor x 20 + x^20*21/(Nat.factorial 20 * 20)
private theorem exp_up {x : ℚ} {n : ℕ} (hn : 0 < n) (hx : 0 ≤ x/n) (hx' : x/n ≤ 1) :
    exp (x:ℝ) ≤ ((up (x/n)^n : ℚ):ℝ) := by
  have e : (x:ℝ) = (n:ℝ)*((x/n:ℚ):ℝ) := by push_cast; field_simp
  rw [e,exp_nat_mul,Rat.cast_pow]
  exact pow_le_pow_left₀ (exp_pos _).le (exp_upper _ _ hx hx' le_rfl) _

private theorem exp_down {x : ℚ} {n : ℕ} (hn : 0 < n) (hx : 0 ≤ x/n) :
    ((taylor (x/n) 20^n:ℚ):ℝ) ≤ exp (x:ℝ) := by
  have e : (x:ℝ) = (n:ℝ)*((x/n:ℚ):ℝ) := by push_cast; field_simp
  have h := exp_lower (x/n) _ hx le_rfl
  rw [e,exp_nat_mul,Rat.cast_pow]
  exact pow_le_pow_left₀ (by exact_mod_cast (show 0 ≤ taylor (x/n) 20 by
    unfold taylor; positivity)) h _

private theorem log_lower {a b : ℚ} (hb : 0 < b) (hx : 0 ≤ a/16) (hx' : a/16 ≤ 1)
    (h : up (a/16)^16 ≤ b) : (a:ℝ) ≤ log (b:ℝ) := by
  apply (le_log_iff_exp_le (by exact_mod_cast hb)).mpr
  exact (exp_up (n := 16) (by decide +kernel) (by simpa using hx) (by simpa using hx')).trans
    ((Rat.cast_le (K := ℝ)).2 h)

private theorem log_upper {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b/16)
    (h : a ≤ taylor (b/16) 20 ^ 16) : log (a:ℝ) ≤ b := by
  apply (log_le_iff_le_exp (by exact_mod_cast ha)).mpr
  exact ((Rat.cast_le (K := ℝ)).2 h).trans (exp_down (n := 16) (by decide +kernel) (by simpa using hb))

private theorem floor_le (i : ℕ) (hi : i ≤ 154) : (floorLog i:ℝ) ≤ terminalLogFloor i := by
  have low : (8.110427237575:ℝ) ≤ log 3329 := by
    simpa using (log_lower (a:=8.110427237575) (b:=3329) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
  have high : log 3329 ≤ 8.110427237576 := by
    simpa using (log_upper (a:=3329) (b:=8.110427237576) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have cap : log 56.2142 ≤ 4.029169394024 := by
    simpa using (log_upper (a:=56.2142) (b:=4.029169394024) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  induction i with
  | zero =>
    rw [terminalLogFloor,log_pow]
    have hh : floorLog 0 = 400*8.110427237575 := by decide +kernel
    rw [hh]; push_cast; linarith
  | succ i ih =>
    have cert : ∀ i : Fin 154, floorLog (i.val+1) ≤ max (floorLog i-8.110427237576)
      (505/506*floorLog i-4.029169394024/2) := by decide +kernel
    have hh := (Rat.cast_le (K := ℝ)).2 (cert ⟨i,by omega⟩)
    push_cast at hh
    apply hh.trans
    rw [terminalLogFloor]
    have ih' := ih (by omega)
    apply max_le_max <;> linarith

private theorem caps_diff (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 155) :
    capSum b-capSum a ≤ (cum b:ℝ)-cum a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b _ ih =>
    have cert : ∀ i : Fin 155, cum (i.val+1) = cum i + logCap (i.val+1) := by decide +kernel
    have eq := congrArg (fun x : ℚ ↦ (x:ℝ)) (cert ⟨b,by omega⟩)
    change (cum (b+1):ℝ) = ((cum b+logCap (b+1):ℚ):ℝ) at eq
    rw [Rat.cast_add] at eq
    have hs : capSum (b+1) = capSum b + log (cap (b+1)) := sum_Icc_succ_top (by omega) _
    rw [eq,hs]
    linarith [(show log (cap (b+1)) ≤ (logCap (b+1):ℝ) by simp [cap]), ih (by omega)]

private theorem width_le (j : ℕ) (hj : j < 155) :
    log (sqrt (2*π/(506-j:ℝ))) ≤ -(widthLog j:ℝ) := by
  have cert : ∀ j : Fin 155, 0 ≤ 2*widthLog j/8 ∧ 2*widthLog j/8 ≤ 1 ∧
      (up (2*widthLog j/8)^8)*(2*3.14159265358979323847) ≤ 506-(j.val:ℚ) := by decide +kernel
  obtain ⟨hn,hh,H⟩ := cert ⟨j,hj⟩
  have ht := exp_up (x:=2*widthLog j) (n:=8) (by decide +kernel) (by simpa using hn) (by simpa using hh)
  push_cast at ht
  have H' := (Rat.cast_le (K := ℝ)).2 H
  push_cast at H'
  have hj' : (j:ℝ) < 155 := by exact_mod_cast hj
  have hp : 0 < 506-(j:ℝ) := by linarith
  have e : exp (2*(widthLog j:ℝ)) * (2*π) ≤ 506-(j:ℝ) := by
    apply le_trans _ H'
    apply mul_le_mul ht _ (by positivity) ((exp_pos _).le.trans ht)
    linarith [pi_lt_d20]
  rw [log_sqrt (by positivity), log_div (by positivity) hp.ne']
  have h := log_le_log (mul_pos (exp_pos _) (by positivity)) e
  rw [log_mul (exp_pos _).ne' (by positivity),log_exp] at h
  linarith

private def argument (i j : ℕ) : ℚ :=
  let k := 155-i
  let b : ℚ := 506-j
  506*3.401937574248-0.693147180559+b/2-floorLog i+cum k-cum (k-j) +
    b*max 0 (logCap (k-j)-widthLog j) + 505*0.0000000001 + 26*2.302585092995

private theorem charge_units (u : FlagIndex) : charge u * 10^26 ≤ units u.1.val u.2.val := by
  let i := u.1.val
  let j := u.2.val
  let k := 155-i
  let p := 505-j
  let w := cap (k-j)
  let z := max 1 (w * sqrt (2*π/(p+1:ℝ)))
  have hi : i < 154 := u.1.isLt
  have hj : j < 155-i := u.2.isLt
  have hp : (p:ℝ) = 505-j := by dsimp [p]; rw [Nat.cast_sub (by omega),Nat.cast_ofNat]
  have hb : 0 < (p+1:ℝ) := by positivity
  have hz₁ : 1 ≤ z := le_max_left ..
  have hz : 0 < z := zero_lt_one.trans_le hz₁
  have hw : 0 < w := exp_pos _
  have ha : planeRadius = sqrt (2704/3) := by
    unfold planeRadius areaCut
    rw [mul_div_assoc',div_div,← sq,sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have ht : 30 ≤ planeRadius := ha ▸ le_sqrt_of_sq_le (by norm_num)
  have ht₀ : 0 < planeRadius := by linarith
  have logR : log planeRadius ≤ 3.401937574248 := by
    rw [ha,log_sqrt (by norm_num)]
    have h := log_upper (a:=2704/3) (b:=2*3.401937574248) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    push_cast at h
    linarith
  have log₂ : (0.693147180559:ℝ) ≤ log 2 := by
    simpa using (log_lower (a:=0.693147180559) (b:=2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
  have log₁₀ : log 10 ≤ 2.302585092995 := by
    simpa using (log_upper (a:=10) (b:=2.302585092995) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have width : log z ≤ max 0 ((logCap (k-j):ℝ)-widthLog j) := by
    rcases max_choice 1 (w*sqrt (2*π/(p+1:ℝ))) with h | h
    · change log (max _ _) ≤ _; rw [h,log_one]; exact le_max_left ..
    · change log (max _ _) ≤ _; rw [h,log_mul hw.ne' (by positivity)]
      apply le_trans _ (le_max_right ..)
      have h' : (p+1:ℝ) = 506-j := by linarith
      rw [h']
      exact add_le_add (le_of_eq (log_exp _)) (width_le j (by omega)) |>.trans_eq (by ring)
  have quadratic : π*w^2/z^2 ≤ (p+1:ℝ)/2 := by
    have h := pow_le_pow_left₀ (mul_nonneg hw.le (sqrt_nonneg _)) (le_max_right 1
      (w*sqrt (2*π/(p+1:ℝ)))) 2
    change _ ≤ z^2 at h
    rw [mul_pow,sq_sqrt (by positivity),mul_div_assoc',div_le_iff₀ hb] at h
    apply (div_le_iff₀ (sq_pos_of_pos hz)).mpr
    linarith only [h]
  have hθ : 0 < terminalTheta (planeRadius*z) ∧ log (terminalTheta (planeRadius*z)) ≤ 0.0000000001 := by
    let y := planeRadius*z
    have hy : 30 ≤ y := by exact (by norm_num : (30:ℝ)=30*1) ▸ mul_le_mul ht hz₁ zero_le_one ht₀.le
    have ha' : 40 ≤ π*y^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr pi_gt_three.le) (sq_nonneg y),sq_nonneg (y-30)]
    have E : (10:ℝ)^12 ≤ exp 40 := by
      have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (2:ℝ))
        (by linarith [add_one_le_exp (1:ℝ)] : (2:ℝ) ≤ exp 1) 40
      rw [← exp_nat_mul] at h
      norm_num at h ⊢
      linarith
    have hneg : exp (-π*y^2) ≤ 1/10^12 := by
      rw [neg_mul,exp_neg,inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (E.trans (exp_le_exp.mpr ha'))
    have hneg' : exp (-3*π*y^2) ≤ 1/10^12 :=
      (exp_le_exp.mpr (by linarith : -3*π*y^2 ≤ -π*y^2)).trans hneg
    have hd : 0 < 1-exp (-3*π*y^2) := by linarith
    have ht' : 0 < terminalTheta y := by unfold terminalTheta; positivity
    refine ⟨ht',(log_le_sub_one_of_pos ht').trans ?_⟩
    change 1+2*exp (-π*y^2)/(1-exp (-3*π*y^2))-1 ≤ _
    rw [add_sub_cancel_left]
    apply (div_le_iff₀ hd).mpr; linarith
  have H : 0 < charge u := by
    change 0 < planeRadius^506/2*exp _*z^(p+1)*terminalTheta (planeRadius*z)^p
    positivity [hθ.1]
  have hlog : log (charge u * 10^26) ≤ (argument i j:ℝ) := by
    change log (planeRadius^506/2*exp (π*w^2/z^2-terminalLogFloor i+capSum k-capSum (k-j))*
      z^(p+1)*terminalTheta (planeRadius*z)^p * 10^26) ≤ _
    rw [log_mul (by positivity [hθ.1]) (by positivity),
      log_mul (by positivity) (pow_ne_zero p hθ.1.ne'),log_mul (by positivity) (by positivity),
      log_mul (by positivity) (exp_pos _).ne',log_div (by positivity) (by norm_num)]
    simp only [log_pow,log_exp,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    unfold argument
    push_cast
    have h₁ := mul_le_mul_of_nonneg_left width hb.le
    have h₂ := mul_le_mul_of_nonneg_left hθ.2 (Nat.cast_nonneg p : 0 ≤ (p:ℝ))
    have h₃ := caps_diff (k-j) k (Nat.sub_le ..) (by dsimp [k]; omega)
    have h₄ := floor_le i (by omega)
    dsimp only [k] at h₁ h₃
    rw [hp] at h₁ h₂ quadratic ⊢
    dsimp only [k]
    nlinarith only [h₁,h₂,h₃,h₄,quadratic,hp,logR,log₂,log₁₀,(Nat.cast_nonneg j : 0 ≤ (j:ℝ))]
  have cert : ∀ (i : Fin 154) (j : Fin (155-i.val)),
    let x := argument i j
    if x ≤ 0 then 1 ≤ units i j else x/32 ≤ 1 ∧ up (x/32)^32 ≤ (units i j:ℚ) := by decide +kernel
  have hc := cert u.1 u.2
  change (if argument i j ≤ 0 then _ else _) at hc
  rw [← exp_log (mul_pos H (by positivity))]
  apply (exp_le_exp.mpr hlog).trans
  split at hc
  · exact ((exp_le_one_iff.mpr (by exact_mod_cast ‹argument i j ≤ 0›))).trans (by exact_mod_cast hc)
  · obtain ⟨hh,hh'⟩ := hc
    apply (exp_up (n:=32) (by decide +kernel) (div_nonneg (le_of_not_ge ‹¬argument i j ≤ 0›) (by norm_num))
      (by simpa using hh)).trans
    exact_mod_cast hh'

theorem charge_sum : (∑ u : FlagIndex, charge u) ≤ 3781668308231/(10:ℝ)^26 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun u _ ↦ charge_units u)
  rw [← Finset.sum_mul] at h
  have hc : (∑ i : Fin 154, ∑ j : Fin (155-i.val), units i j) ≤ 3781668308231 := by decide +kernel
  have ht : (∑ u : FlagIndex, (units u.1 u.2:ℝ)) ≤ 3781668308231 := by
    rw [Fintype.sum_sigma]
    exact_mod_cast hc
  linarith only [h,ht]

end SigabaNeo.Wall1.ControlledPlane.ProvedProfile

#print axioms SigabaNeo.Wall1.ControlledPlane.ProvedProfile.charge_sum
