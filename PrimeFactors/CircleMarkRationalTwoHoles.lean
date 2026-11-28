import PrimeFactors.CircleMarkRationalDeficit

/-! The missing signed ratios and squares in a rectangle just below saturation.
Writing p=(H+1)(D+1)+s, the classification uses ordinary divisors of s. -/
namespace PrimeFactors.CircleMarkRationalTwoHoles

open Finset CircleMarkRationalCover
open scoped Classical

private theorem not_cast_zero {p n : ℕ} [NeZero p] (pos : 0<n) (small : n<p) :
    (n:ZMod p)≠0 := fun h =>
  (Nat.not_dvd_of_pos_of_lt pos small) ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)

private theorem length_bounds {p H D s : ℕ} (sp : 0<s) (sh : s≤H) (sd : s≤D)
    (area : p=(H+1)*(D+1)+s) : H+1<p ∧ 2*s<p := by
  have one := Nat.le_mul_of_pos_right (H+1) (show 0<D+1 by omega)
  have two := Nat.mul_le_mul_left (H+1) (show 2≤D+1 by omega)
  omega

/-- A divisor of the area deficit gives a genuinely missing root, of either sign.
The numerator and denominator are both bounded in this argument. -/
theorem miss_of_divisor {p H D s t : ℕ} [hp : Fact p.Prime] (sp : 0<s)
    (sh : s≤H) (sd : s≤D) (area : p=(H+1)*(D+1)+s)
    (dt : t∣s) {r : ZMod p} (rt : (t:ZMod p)*r=(H+1:ℕ) ∨ (t:ZMod p)*r=-((H+1:ℕ):ZMod p)) :
    ¬Represents r H D := by
  have tp := Nat.pos_of_dvd_of_pos dt sp
  have ts := Nat.le_of_dvd sp dt
  have lsmall := (length_bounds sp sh sd area).1
  have cp : (H+1).Coprime p :=
    (hp.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) lsmall)).symm
  have c : (H+1).Coprime t := by
    apply Nat.Coprime.of_dvd_right dt
    rw [area,Nat.add_comm ((H+1)*(D+1)),Nat.mul_comm (H+1),Nat.coprime_add_mul_right_right] at cp
    exact cp
  rintro ⟨i,mi,j,mj,ratio⟩
  obtain ⟨ip,ih⟩ := mem_Icc.mp mi
  obtain ⟨jp,jd⟩ := mem_Icc.mp mj
  have first : (i:ZMod p)^2=((j:ZMod p)*r)^2 := by
    rcases ratio with eq|eq <;> simp [eq]
  have second : ((t:ZMod p)*r)^2=((H+1:ℕ):ZMod p)^2 := by
    rcases rt with eq|eq <;> rw [eq]
    exact neg_sq _
  have sq : ((i*t:ℕ):ZMod p)^2=((j*(H+1):ℕ):ZMod p)^2 := by
    rw [Nat.cast_mul,Nat.cast_mul,mul_pow,mul_pow,first,←second]
    ring
  have ti_bound : i*t<p := by
    have h := Nat.mul_le_mul (by omega : i≤H+1) (by omega : t≤D+1)
    omega
  have jl_bound : j*(H+1)<p := by
    have h := Nat.mul_le_mul_right (H+1) (by omega : j≤D+1)
    rw [Nat.mul_comm (D+1)] at h
    omega
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp sq with same|neg
  · have eq := congrArg ZMod.val same
    rw [ZMod.val_natCast_of_lt ti_bound,ZMod.val_natCast_of_lt jl_bound] at eq
    have dvd : H+1∣i*t := eq ▸ dvd_mul_left _ _
    exact (Nat.not_dvd_of_pos_of_lt ip (by omega)) (c.dvd_of_dvd_mul_right dvd)
  · have zero : ((i*t+j*(H+1):ℕ):ZMod p)=0 := by rw [Nat.cast_add,neg,neg_add_cancel]
    have exactSum : i*t+j*(H+1)=p := Nat.eq_of_dvd_of_lt_two_mul
      (by have := Nat.mul_pos ip tp; omega) ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp zero) (by omega)
    have counts : j+(D+1-j)=D+1 := by omega
    have id : i*t=(D+1-j)*(H+1)+s := by
      nlinarith only [congrArg (fun z : ℕ => z*(H+1)) counts,exactSum,area]
    have divides : t∣(D+1-j)*(H+1) := (Nat.dvd_add_iff_left dt).mpr (id ▸ dvd_mul_left _ _)
    have span := Nat.le_of_dvd (by omega : 0<D+1-j) (c.symm.dvd_of_dvd_mul_right divides)
    have le := Nat.mul_le_mul_right (H+1) span
    have under := Nat.mul_lt_mul_of_pos_right (by omega : i<H+1) tp
    rw [Nat.mul_comm (H+1)] at under
    omega

/-- Positive orientation for a divisor; the other orientation is its negative. -/
private noncomputable def slope (p L t : ℕ) [Fact p.Prime] : ZMod p := (L:ZMod p)/(t:ZMod p)

private theorem slope_nz {p L t : ℕ} [Fact p.Prime] (lp : 0<L) (ls : L<p) (tp : 0<t) (ts : t<p) :
    slope p L t ≠0 := div_ne_zero (not_cast_zero lp ls) (not_cast_zero tp ts)

private theorem cancel_slope {p L t : ℕ} [Fact p.Prime] (pos : 0<t) (small : t<p) :
    (t:ZMod p)*slope p L t=L := by
  rw [mul_comm,slope,div_mul_cancel₀ _ (not_cast_zero pos small)]

private theorem candidate_iff {p L t : ℕ} [Fact p.Prime] (pos : 0<t) (small : t<p) (r : ZMod p) :
    (t:ZMod p)*r=L ∨ (t:ZMod p)*r= -(L:ZMod p) ↔
    r=slope p L t ∨ r= -slope p L t := by
  have nz := not_cast_zero pos small
  have id := cancel_slope (L:=L) pos small
  rw [←id,←mul_neg,mul_right_inj' nz,mul_right_inj' nz]

private noncomputable def positive (p H s : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  s.divisors.image (fun t => slope p (H+1) t)

private theorem sign_separation {p L s t u : ℕ} [Fact p.Prime] (lp : 0<L) (ls : L<p)
    (room : 2*s<p) (sp : 0<s) (tdiv : t∣s) (udiv : u∣s) :
    (slope p L t=slope p L u ↔ t=u) ∧ slope p L t≠-slope p L u := by
  have tp := Nat.pos_of_dvd_of_pos tdiv sp
  have up := Nat.pos_of_dvd_of_pos udiv sp
  have ts := Nat.le_of_dvd sp tdiv
  have us := Nat.le_of_dvd sp udiv
  have nzT := not_cast_zero tp (by omega : t<p)
  have nzU := not_cast_zero up (by omega : u<p)
  have nzL := not_cast_zero lp ls
  constructor
  · constructor
    · intro eqn
      change (L:ZMod p)/t=(L:ZMod p)/u at eqn
      have e := (div_eq_div_iff nzT nzU).mp eqn
      have eq := congrArg ZMod.val (mul_left_cancel₀ nzL e)
      rw [ZMod.val_natCast_of_lt (by omega : t<p),ZMod.val_natCast_of_lt (by omega : u<p)] at eq
      omega
    · rintro rfl; rfl
  · intro eqn
    change (L:ZMod p)/t= -((L:ZMod p)/u) at eqn
    rw [←neg_div] at eqn
    have e := (div_eq_div_iff nzT nzU).mp eqn
    have sum : (u:ZMod p)+(t:ZMod p)=0 := by
      apply mul_left_cancel₀ nzL
      rw [mul_add,mul_zero,e,neg_mul,neg_add_cancel]
    have bad := (ZMod.natCast_zmod_eq_zero_iff_dvd (u+t) p).mp (by simpa using sum)
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0<u+t) (by omega : u+t<p)) bad

/-- Both signs of the ratios with numerator `H+1` and denominator dividing `s`. -/
noncomputable def candidates (p H s : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  positive p H s ∪ (positive p H s).image Neg.neg

private theorem mem_candidates {p H s : ℕ} [Fact p.Prime] {r : ZMod p} :
    r∈candidates p H s ↔ ∃ t∈s.divisors,r=slope p (H+1) t ∨ r= -slope p (H+1) t := by
  constructor
  · intro mem
    rcases mem_union.mp mem with h|h
    · obtain ⟨t,m,rfl⟩ := mem_image.mp h
      exact ⟨t,m,Or.inl rfl⟩
    · obtain ⟨z,zm,rfl⟩ := mem_image.mp h
      obtain ⟨t,m,rfl⟩ := mem_image.mp zm
      exact ⟨t,m,Or.inr rfl⟩
  · rintro ⟨t,tm,rfl|rfl⟩
    · exact mem_union_left _ (mem_image.mpr ⟨t,tm,rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨_,mem_image.mpr ⟨t,tm,rfl⟩,rfl⟩)

/-- Both signs count separately as roots; exactly one square is lost for each divisor. -/
theorem candidate_counts {p H D s : ℕ} [Fact p.Prime]
    (sp : 0<s) (sh : s≤H) (sd : s≤D) (area : p=(H+1)*(D+1)+s) :
    (candidates p H s).card=2*s.divisors.card ∧
    ((candidates p H s).image (fun z => z^2)).card=s.divisors.card := by
  let A := positive p H s
  obtain ⟨ls,room⟩ := length_bounds sp sh sd area
  have indices (t u : ℕ) (tm : t∈s.divisors) (um : u∈s.divisors) :=
    sign_separation (by omega : 0<H+1) ls room sp (Nat.mem_divisors.mp tm).1 (Nat.mem_divisors.mp um).1
  have cardA : A.card=s.divisors.card :=
    card_image_of_injOn (fun t tm u um eqn => ((indices t u tm um).1).mp eqn)
  have sep : Disjoint A (A.image Neg.neg) := by
    apply disjoint_left.mpr
    intro z zm minus
    obtain ⟨t,tm,eqn⟩ := mem_image.mp zm
    obtain ⟨w,wm,wz⟩ := mem_image.mp minus
    obtain ⟨u,um,wu⟩ := mem_image.mp wm
    exact (indices t u tm um).2 (eqn.trans (wz.symm.trans (congrArg Neg.neg wu.symm)))
  have img : (candidates p H s).image (fun z => z^2)=A.image (fun z => z^2) := by
    simp [candidates,A,image_union,image_image,Function.comp_def]
  refine ⟨?_,?_⟩
  · rw [candidates,card_union_of_disjoint sep,card_image_of_injective _ neg_injective,cardA]
    omega
  · rw [img]
    apply Eq.trans (card_image_of_injOn ?_) cardA
    intro x xm y ym eqn
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp eqn with eq|neg
    · exact eq
    · exact False.elim (disjoint_left.mp sep xm (mem_image.mpr ⟨y,ym,neg.symm⟩))

/-- Nonzero roots for which the signed rectangle contains no representative. -/
noncomputable def missingRoots (p H D : ℕ) [NeZero p] : Finset (ZMod p) :=
  univ.filter fun r : ZMod p => r≠0 ∧ ¬Represents r H D

/-- The square targets obtained from a nonzero missing root. -/
noncomputable def missingSquares (p H D : ℕ) [NeZero p] : Finset (ZMod p) :=
  (missingRoots p H D).image (fun r => r^2)

/-- Below both side lengths, the roots missing from the rectangle are exactly
the signed divisor ratios. -/
theorem missingRoots_eq {p H D s : ℕ} [Fact p.Prime] (sp : 0<s)
    (sh : s≤H) (sd : s≤D) (area : p=(H+1)*(D+1)+s) :
    missingRoots p H D = candidates p H s := by
  obtain ⟨ls,room⟩ := length_bounds sp sh sd area
  ext r
  simp only [missingRoots,mem_filter,mem_univ,true_and,mem_candidates]
  constructor
  · rintro ⟨nz,miss⟩
    obtain ⟨t,td,rel⟩ := CircleMarkRationalDeficit.divisor_of_miss
      (by omega) nz area sp (by omega) (by omega) miss
    have tp := Nat.pos_of_dvd_of_pos td sp
    have ts := Nat.le_of_dvd sp td
    exact ⟨t,Nat.mem_divisors.mpr ⟨td,sp.ne'⟩,(candidate_iff tp (by omega) r).mp rel⟩
  · rintro ⟨t,tm,sgn⟩
    have td := (Nat.mem_divisors.mp tm).1
    have tp := Nat.pos_of_dvd_of_pos td sp
    have ts := Nat.le_of_dvd sp td
    have nonzero := slope_nz (by omega : 0<H+1) ls tp (by omega)
    refine ⟨?_,miss_of_divisor sp sh sd area td ((candidate_iff tp (by omega) r).mpr sgn)⟩
    rcases sgn with equal|opposite
    · exact equal ▸ nonzero
    · exact opposite ▸ neg_ne_zero.mpr nonzero

/-- The denominator divides the known deficit. Every resulting sign and
denominator gives a missing nonzero root. -/
theorem miss_iff {p H D s : ℕ} [Fact p.Prime] {r : ZMod p} (nz : r≠0)
    (sp : 0<s) (sh : s≤H) (sd : s≤D) (area : p=(H+1)*(D+1)+s) :
    ¬Represents r H D ↔ ∃ t∈s.divisors,
      r=((H+1:ℕ):ZMod p)/(t:ZMod p) ∨ r= -(((H+1:ℕ):ZMod p)/(t:ZMod p)) := by
  have member : r∈missingRoots p H D ↔ ¬Represents r H D := by simp [missingRoots,nz]
  rw [←member,missingRoots_eq sp sh sd area,mem_candidates]
  rfl

/-- A quadratic-residue target is missed exactly when it equals the square
of one of the divisor ratios. -/
theorem square_miss_iff {p H D s : ℕ} [Fact p.Prime] {a : ℤ}
    (square : legendreSym p a=1) (sp : 0<s) (sh : s≤H) (sd : s≤D)
    (area : p=(H+1)*(D+1)+s) :
    ¬SquareHit p a H D ↔ ∃ t∈s.divisors, (a:ZMod p)=((H+1:ℕ):ZMod p)^2/(t:ZMod p)^2 := by
  have nz : (a:ZMod p)≠0 := by
    intro zero
    rw [legendreSym,zero,quadraticChar_zero] at square
    contradiction
  obtain ⟨r,eqn⟩ := (isSquare_iff_exists_sq _).mp ((legendreSym.eq_one_iff p nz).mp square)
  have rn : r≠0 := fun z => nz (by simp [eqn,z])
  rw [square_iff eqn.symm H D,miss_iff rn sp sh sd area,eqn]
  simp only [←div_pow,sq_eq_sq_iff_eq_or_eq_neg]

/-- An integer target belongs to the exceptional square set precisely when it
is a nonzero square and the rectangle has no solution at that target. -/
theorem mem_missingSquares {p H D : ℕ} [Fact p.Prime] {a : ℤ} :
    (a:ZMod p)∈missingSquares p H D ↔
      (a:ZMod p)≠0 ∧ IsSquare (a:ZMod p) ∧ ¬SquareHit p a H D := by
  constructor
  · intro m
    obtain ⟨r,rm,eqn⟩ := mem_image.mp m
    obtain ⟨nz,miss⟩ := (mem_filter.mp rm).2
    exact ⟨eqn ▸ pow_ne_zero _ nz,(isSquare_iff_exists_sq _).mpr ⟨r,eqn.symm⟩,
      fun hit => miss ((square_iff eqn H D).mp hit)⟩
  · rintro ⟨nz,square,miss⟩
    obtain ⟨r,eqn⟩ := (isSquare_iff_exists_sq _).mp square
    have rn : r≠0 := fun z => nz (by simp [eqn,z])
    exact mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_univ _,rn,fun h => miss
      ((square_iff eqn.symm H D).mpr h)⟩,eqn.symm⟩

/-- The exact loss amounts to two roots and one square per positive divisor
of the deficit, regardless of the rectangle's aspect ratio. -/
theorem missing_counts {p H D s : ℕ} [Fact p.Prime] (sp : 0<s)
    (sh : s≤H) (sd : s≤D) (area : p=(H+1)*(D+1)+s) :
    (missingRoots p H D).card=2*s.divisors.card ∧ (missingSquares p H D).card=s.divisors.card := by
  simpa only [missingSquares,missingRoots_eq sp sh sd area] using candidate_counts sp sh sd area

private theorem two_sides {p H D : ℕ} [hp : Fact p.Prime] (hpos : 0<H) (dpos : 0<D)
    (area : p=(H+1)*(D+1)+2) : 2≤H ∧ 2≤D := by
  have odd := hp.out.eq_two_or_odd
  constructor
  · by_contra! h
    have one : H=1 := by omega
    rw [one] at area
    omega
  · by_contra! h
    have one : D=1 := by omega
    rw [one] at area
    omega

/-- At deficit two the complete exceptional set consists of both signs of
`H+1` and `(H+1)/2`. Counting squares collapses these four roots to two. -/
theorem two_holes {p H D : ℕ} [Fact p.Prime] (hpos : 0<H) (dpos : 0<D)
    (area : p=(H+1)*(D+1)+2) :
    (∀ r : ZMod p, r∈missingRoots p H D ↔
      r=((H+1:ℕ):ZMod p) ∨ r= -((H+1:ℕ):ZMod p) ∨
      r=((H+1:ℕ):ZMod p)/2 ∨ r= -(((H+1:ℕ):ZMod p)/2)) ∧
    (missingRoots p H D).card=4 ∧ (missingSquares p H D).card=2 := by
  obtain ⟨sh,sd⟩ := two_sides hpos dpos area
  have divisors : (2:ℕ).divisors={1,2} := by decide
  constructor
  · intro r
    rw [missingRoots_eq (by decide : 0<2) sh sd area,mem_candidates,divisors]
    simp [slope,or_assoc]
  · have counts := missing_counts (by decide : 0<2) sh sd area
    exact counts

/-- In the two-hole formula, `(H+1)/2` and the inverse denominator endpoint
differ only in sign. -/
theorem two_holes_reciprocal {p H D : ℕ} [Fact p.Prime] (hpos : 0<H) (dpos : 0<D)
    (area : p=(H+1)*(D+1)+2) :
    ((H+1:ℕ):ZMod p)/2 = -(((D+1:ℕ):ZMod p)⁻¹) := by
  obtain ⟨sh,sd⟩ := two_sides hpos dpos area
  have rev : p=(D+1)*(H+1)+2 := by simpa only [Nat.mul_comm] using area
  obtain ⟨ds,room⟩ := length_bounds (by decide : 0<2) sd sh rev
  have dunit := not_cast_zero (by omega : 0<D+1) ds
  have two : (2:ZMod p)≠0 := by exact_mod_cast not_cast_zero (p:=p) (by decide : 0<2) (by omega : 2<p)
  have relation : (p:ZMod p)=(((H+1)*(D+1)+2:ℕ):ZMod p) := congrArg (fun n : ℕ => (n:ZMod p)) area
  rw [ZMod.natCast_self,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at relation
  apply (div_eq_iff two).mpr
  rw [neg_mul]
  apply mul_left_cancel₀ dunit
  rw [mul_neg,←mul_assoc,mul_inv_cancel₀ dunit,one_mul]
  linear_combination -relation

/-- The square 6-by-6 rectangle modulo 53 has deficit four and misses three
nonzero square targets, as 4 has exactly three divisors. -/
theorem fifty_three : (missingRoots 53 6 6).card=6 ∧ (missingSquares 53 6 6).card=3 := by
  letI : Fact (Nat.Prime 53) := ⟨by decide⟩
  exact missing_counts (s:=4) (by decide) (by decide) (by decide) (by decide)

end PrimeFactors.CircleMarkRationalTwoHoles
