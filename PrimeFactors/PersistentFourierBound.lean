import PrimeFactors.PersistentLocalSurvivors

namespace PrimeFactors.PersistentFourierBound

set_option Elab.async false

open PersistentLocalSurvivors

/-- The affine hyperbola that counts square roots above each midpoint is
parametrized once by the nonzero field elements. This change of variables
converts every nonzero Fourier coefficient to a Kloosterman sum and a
correction from the ramified points. -/
noncomputable def hyperbolaEquiv {F : Type*} [Field F] {n : F} (unit : n≠0) (two : (2:F)≠0) :
    {z : F × F // z.2^2 = z.1^2-n} ≃ {x : F // x≠0} where
  toFun z := ⟨z.val.1+z.val.2,by
    have pair : (z.val.1+z.val.2)*(z.val.1-z.val.2)=n := by linear_combination -z.property
    intro zero; exact unit (by simpa [zero] using pair.symm)⟩
  invFun x := ⟨((x.val+n/x.val)/2,(x.val-n/x.val)/2),by
    dsimp; field_simp [two,x.property]; ring⟩
  left_inv z := by
    have pair : (z.val.1+z.val.2)*(z.val.1-z.val.2)=n := by linear_combination -z.property
    have nz : z.val.1+z.val.2≠0 := by intro zero; exact unit (by simpa [zero] using pair.symm)
    have partner : n/(z.val.1+z.val.2)=z.val.1-z.val.2 := (div_eq_iff nz).mpr (by rw [mul_comm,pair])
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> rw [partner] <;> field_simp <;> ring
  right_inv x := by
    apply Subtype.ext; dsimp; field_simp; ring

theorem weighted_hyperbola {F R : Type*} [Field F] [Fintype F] [DecidableEq F]
    [AddCommMonoid R] {n : F} (unit : n≠0) (two : (2:F)≠0) (weight : F → R) :
    ∑ z : {z : F × F // z.2^2 = z.1^2-n}, weight z.val.1 =
      ∑ x : {x : F // x≠0}, weight ((x.val+n/x.val)/2) :=
  ((hyperbolaEquiv unit two).symm.sum_comp (fun z => weight z.val.1)).symm



/-- Testing potential divisors through 33 suffices below 1,110. -/
noncomputable def trial (p : ℕ) : Bool :=
  5≤p && p≤1109 && (List.range 32).all (fun j => p==j+2 || p%(j+2)!=0)

theorem trial_correct (p : ℕ) : trial p ↔ 5≤p ∧ p≤1109 ∧ p.Prime := by
  simp only [trial, Bool.and_eq_true, decide_eq_true_eq,List.all_eq_true,
    List.mem_range,Bool.or_eq_true,beq_iff_eq,bne_iff_ne]
  constructor
  · rintro ⟨⟨small,large⟩,tests⟩
    refine ⟨small,large,?_⟩
    by_contra composite
    have low := (Nat.minFac_prime (by omega : p≠1)).two_le
    have high : p.minFac<34 := by
      have sq := Nat.minFac_sq_le_self (by omega) composite
      by_contra! h; have := Nat.pow_le_pow_left h 2; omega
    have pass := tests (p.minFac-2) (by omega)
    rw [Nat.sub_add_cancel low] at pass
    rcases pass with same|miss
    · have := (Nat.not_prime_iff_minFac_lt (by omega : 2≤p)).mp composite; omega
    · exact miss (Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd p))
  · rintro ⟨small,large,prime⟩
    refine ⟨⟨small,large⟩,fun j _ => ?_⟩
    by_cases h : p=j+2
    · exact Or.inl h
    · exact Or.inr (fun zero => (prime.eq_one_or_self_of_dvd (j+2)
        (Nat.dvd_of_mod_eq_zero zero)).elim (by omega) (fun eq => h eq.symm))

private noncomputable def trialBlock (i : ℕ) : List ℕ :=
  ((List.range 32).map (fun j => 32*i+j)).filter trial

private noncomputable def block0 : List ℕ := [5,7,11,13,17,19,23,29,31]
private noncomputable def block1 : List ℕ := [37,41,43,47,53,59,61]
private noncomputable def block2 : List ℕ := [67,71,73,79,83,89]
private noncomputable def block3 : List ℕ := [97,101,103,107,109,113,127]
private noncomputable def block4 : List ℕ := [131,137,139,149,151,157]
private noncomputable def block5 : List ℕ := [163,167,173,179,181,191]
private noncomputable def block6 : List ℕ := [193,197,199,211,223]
private noncomputable def block7 : List ℕ := [227,229,233,239,241,251]
private noncomputable def block8 : List ℕ := [257,263,269,271,277,281,283]
private noncomputable def block9 : List ℕ := [293,307,311,313,317]
private noncomputable def block10 : List ℕ := [331,337,347,349]
private noncomputable def block11 : List ℕ := [353,359,367,373,379,383]
private noncomputable def block12 : List ℕ := [389,397,401,409]
private noncomputable def block13 : List ℕ := [419,421,431,433,439,443]
private noncomputable def block14 : List ℕ := [449,457,461,463,467,479]
private noncomputable def block15 : List ℕ := [487,491,499,503,509]
private noncomputable def block16 : List ℕ := [521,523,541]
private noncomputable def block17 : List ℕ := [547,557,563,569,571]
private noncomputable def block18 : List ℕ := [577,587,593,599,601,607]
private noncomputable def block19 : List ℕ := [613,617,619,631]
private noncomputable def block20 : List ℕ := [641,643,647,653,659,661]
private noncomputable def block21 : List ℕ := [673,677,683,691,701]
private noncomputable def block22 : List ℕ := [709,719,727,733]
private noncomputable def block23 : List ℕ := [739,743,751,757,761]
private noncomputable def block24 : List ℕ := [769,773,787,797]
private noncomputable def block25 : List ℕ := [809,811,821,823,827,829]
private noncomputable def block26 : List ℕ := [839,853,857,859,863]
private noncomputable def block27 : List ℕ := [877,881,883,887]
private noncomputable def block28 : List ℕ := [907,911,919]
private noncomputable def block29 : List ℕ := [929,937,941,947,953]
private noncomputable def block30 : List ℕ := [967,971,977,983,991]
private noncomputable def block31 : List ℕ := [997,1009,1013,1019,1021]
private noncomputable def block32 : List ℕ := [1031,1033,1039,1049,1051]
private noncomputable def block33 : List ℕ := [1061,1063,1069,1087]
private noncomputable def block34 : List ℕ := [1091,1093,1097,1103,1109]

private noncomputable def primeBlocks : List (List ℕ) :=
  [block0,block1,block2,block3,block4,block5,block6,block7,block8,block9,block10,block11,block12,block13,block14,block15,block16,block17,block18,block19,block20,block21,block22,block23,block24,block25,block26,block27,block28,block29,block30,block31,block32,block33,block34]

/-- Each source integer occurs in exactly one quotient-and-remainder block. -/
theorem covers (p : ℕ) (h : p≤1109) :
    p/32<35 ∧ p%32<32 ∧ 32*(p/32)+p%32=p := by omega

private theorem checkBlock0 : trialBlock 0=block0 := by decide +kernel
private theorem checkBlock1 : trialBlock 1=block1 := by decide +kernel
private theorem checkBlock2 : trialBlock 2=block2 := by decide +kernel
private theorem checkBlock3 : trialBlock 3=block3 := by decide +kernel
private theorem checkBlock4 : trialBlock 4=block4 := by decide +kernel
private theorem checkBlock5 : trialBlock 5=block5 := by decide +kernel
private theorem checkBlock6 : trialBlock 6=block6 := by decide +kernel
private theorem checkBlock7 : trialBlock 7=block7 := by decide +kernel
private theorem checkBlock8 : trialBlock 8=block8 := by decide +kernel
private theorem checkBlock9 : trialBlock 9=block9 := by decide +kernel
private theorem checkBlock10 : trialBlock 10=block10 := by decide +kernel
private theorem checkBlock11 : trialBlock 11=block11 := by decide +kernel
private theorem checkBlock12 : trialBlock 12=block12 := by decide +kernel
private theorem checkBlock13 : trialBlock 13=block13 := by decide +kernel
private theorem checkBlock14 : trialBlock 14=block14 := by decide +kernel
private theorem checkBlock15 : trialBlock 15=block15 := by decide +kernel
private theorem checkBlock16 : trialBlock 16=block16 := by decide +kernel
private theorem checkBlock17 : trialBlock 17=block17 := by decide +kernel
private theorem checkBlock18 : trialBlock 18=block18 := by decide +kernel
private theorem checkBlock19 : trialBlock 19=block19 := by decide +kernel
private theorem checkBlock20 : trialBlock 20=block20 := by decide +kernel
private theorem checkBlock21 : trialBlock 21=block21 := by decide +kernel
private theorem checkBlock22 : trialBlock 22=block22 := by decide +kernel
private theorem checkBlock23 : trialBlock 23=block23 := by decide +kernel
private theorem checkBlock24 : trialBlock 24=block24 := by decide +kernel
private theorem checkBlock25 : trialBlock 25=block25 := by decide +kernel
private theorem checkBlock26 : trialBlock 26=block26 := by decide +kernel
private theorem checkBlock27 : trialBlock 27=block27 := by decide +kernel
private theorem checkBlock28 : trialBlock 28=block28 := by decide +kernel
private theorem checkBlock29 : trialBlock 29=block29 := by decide +kernel
private theorem checkBlock30 : trialBlock 30=block30 := by decide +kernel
private theorem checkBlock31 : trialBlock 31=block31 := by decide +kernel
private theorem checkBlock32 : trialBlock 32=block32 := by decide +kernel
private theorem checkBlock33 : trialBlock 33=block33 := by decide +kernel
private theorem checkBlock34 : trialBlock 34=block34 := by decide +kernel

theorem complete_blocks : (List.range 35).map trialBlock = primeBlocks := by
  change ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34].map trialBlock) = primeBlocks
  simp only [List.map_cons,List.map_nil,primeBlocks,
    checkBlock0,checkBlock1,checkBlock2,checkBlock3,checkBlock4,checkBlock5,checkBlock6,
    checkBlock7,checkBlock8,checkBlock9,checkBlock10,checkBlock11,checkBlock12,checkBlock13,
    checkBlock14,checkBlock15,checkBlock16,checkBlock17,checkBlock18,checkBlock19,checkBlock20,
    checkBlock21,checkBlock22,checkBlock23,checkBlock24,checkBlock25,checkBlock26,checkBlock27,
    checkBlock28,checkBlock29,checkBlock30,checkBlock31,checkBlock32,checkBlock33,checkBlock34]

noncomputable def oddModuli : List ℕ := primeBlocks.flatten

noncomputable def modulus : ℕ := oddModuli.prod

noncomputable def densityNum : ℕ := (oddModuli.map (fun p => p-3)).prod

noncomputable def densityDen : ℕ := (oddModuli.map (fun p => 2*p)).prod

/-- Integer certificates for 256 times each square root. Verifying a
certificate uses one small squaring and comparison at each prime. -/
noncomputable def upperRoots : List (ℕ × ℕ) := [
  (5,573), (7,678), (11,850), (13,924), (17,1056), (19,1116), (23,1228), (29,1379),
  (31,1426), (37,1558), (41,1640), (43,1679), (47,1756), (53,1864), (59,1967), (61,2000),
  (67,2096), (71,2158), (73,2188), (79,2276), (83,2333), (89,2416), (97,2522), (101,2573),
  (103,2599), (107,2649), (109,2673), (113,2722), (127,2885), (131,2931), (137,2997), (139,3019),
  (149,3125), (151,3146), (157,3208), (163,3269), (167,3309), (173,3368), (179,3426), (181,3445),
  (191,3538), (193,3557), (197,3594), (199,3612), (211,3719), (223,3823), (227,3858), (229,3874),
  (233,3908), (239,3958), (241,3975), (251,4056), (257,4104), (263,4152), (269,4199), (271,4215),
  (277,4261), (281,4292), (283,4307), (293,4383), (307,4486), (311,4515), (313,4530), (317,4558),
  (331,4658), (337,4700), (347,4769), (349,4783), (353,4810), (359,4851), (367,4905), (373,4945),
  (379,4984), (383,5011), (389,5050), (397,5101), (401,5127), (409,5178), (419,5241), (421,5253),
  (431,5315), (433,5328), (439,5364), (443,5389), (449,5425), (457,5473), (461,5497), (463,5509),
  (467,5533), (479,5603), (487,5650), (491,5673), (499,5719), (503,5742), (509,5776), (521,5844),
  (523,5855), (541,5955), (547,5988), (557,6042), (563,6075), (569,6107), (571,6118), (577,6150),
  (587,6203), (593,6235), (599,6266), (601,6276), (607,6308), (613,6339), (617,6359), (619,6370),
  (631,6431), (641,6482), (643,6492), (647,6512), (653,6542), (659,6572), (661,6582), (673,6642),
  (677,6661), (683,6691), (691,6730), (701,6778), (709,6817), (719,6865), (727,6903), (733,6931),
  (739,6960), (743,6979), (751,7016), (757,7044), (761,7063), (769,7100), (773,7118), (787,7182),
  (797,7228), (809,7282), (811,7291), (821,7336), (823,7345), (827,7362), (829,7371), (839,7416),
  (853,7477), (857,7495), (859,7504), (863,7521), (877,7582), (881,7599), (883,7608), (887,7625),
  (907,7710), (911,7727), (919,7761), (929,7803), (937,7837), (941,7853), (947,7878), (953,7903),
  (967,7961), (971,7978), (977,8002), (983,8027), (991,8059), (997,8084), (1009,8132), (1013,8148),
  (1019,8172), (1021,8180), (1031,8220), (1033,8228), (1039,8252), (1049,8292), (1051,8300), (1061,8339),
  (1063,8347), (1069,8371), (1087,8441), (1091,8456), (1093,8464), (1097,8479), (1103,8503), (1109,8526)]

noncomputable def relativeErrorNum : ℕ :=
  (upperRoots.map (fun z => 256*(z.1-3)+2*z.1*(256+z.2))).prod

noncomputable def relativeErrorDen : ℕ := (oddModuli.map (fun p => 256*(p-3))).prod

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 4096 in
/-- The Fourier error bound is below one tenth of the zero-frequency term. -/
theorem completion_arithmetic :
    upperRoots.map Prod.fst = oddModuli ∧
    (upperRoots.all (fun z => 65536*z.1 < z.2^2) = true) ∧
    oddModuli.length = 184 ∧
    2^1557 ≤ modulus ∧ modulus < 2^1558 ∧
    10*1559*relativeErrorNum < (2^1019/3456)*relativeErrorDen ∧
    5*(2^819+1)*densityDen < 32*(2^1019/3456)*densityNum := by decide +kernel

private noncomputable def accepted (p h : ℕ) : Bool :=
  let d := (h%p)^2+p-(713%p)
  ((List.range p).any (fun a => a^2%p == d%p)) && d%p != 0

private noncomputable def center (active : Bool) (p m h : ℕ) : ℤ :=
  if active then (if accepted p h then (p:ℤ) else 0)-m else m

/-- This integer is 385 times one exact-conductor contribution.
Centering a local indicator suppresses its zero Fourier frequency. -/
private noncomputable def contribution (d : ℕ) : ℤ :=
  ((List.range 137).map (fun t =>
    let h := 27+3456*t
    center (d%5==0) 5 2 h * center (d%7==0) 7 3 h * center (d%11==0) 11 4 h)).sum

set_option maxRecDepth 8192 in
/-- Independent enumeration of the surviving midpoints and the centered
expansion. The last identity uses the prime product 385 as denominator. -/
theorem short_completion :
    ([1,5,7,11,35,55,77,385].map contribution) =
      [3288,72,16,-54,-16,-6,138,-358] ∧
    ((List.range 137).filter (fun t =>
      let h := 27+3456*t
      accepted 5 h && accepted 7 h && accepted 11 h)).length = 8 ∧
    (3288+72+16-54-16-6+138-358:ℤ) = 8*385 := by decide +kernel

end PrimeFactors.PersistentFourierBound
