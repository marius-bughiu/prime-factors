import PrimeFactors.PrimePowerSumFilter
import PrimeFactors.UniversalSpacing

/-! Difference sets for the two-adic factor-sum classes. At the singular square
branch the signed high digits have an exact difference test and an unsigned
sum-of-two-squares test. -/
namespace PrimeFactors.TwoAdicSumSpacing
open PrimePowerSumFilter FactorSumSpacing

private abbrev R (k : ℕ) := ZMod (2^(k+3))
private abbrev Sq (k : ℕ) (y : ℤ) := IsSquare (y : R k)
private abbrev Good (k : ℕ) (y : ℤ) := IsSquare (digit (y : R k))

private theorem cast_low {a b : ℤ} {k : ℕ} (eq : (a : R k)=(b : R k)) : a%8=b%8 := by
  have dv : (8:ℤ) ∣ ((2^(k+3):ℕ):ℤ) := by
    push_cast
    rw [pow_add]
    exact dvd_mul_left _ _
  exact Int.modEq_iff_dvd.mpr (dv.trans ((ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp eq))

private theorem sq_low (k : ℕ) {y : ℤ} (ok : Sq k y) : y%8=0 ∨ y%8=1 ∨ y%8=4 := by
  have h := ok.choose_spec
  -- Reduce the chosen square modulo eight.
  have hz : ∃ a : ℤ, (y : R k)=((a^2 : ℤ) : R k) := by
    obtain ⟨a,ha⟩ := ZMod.intCast_surjective ok.choose
    exact ⟨a,by rw [Int.cast_pow,ha,pow_two]; exact h⟩
  obtain ⟨a,ha⟩ := hz
  have rem : y%8=((a%8)^2)%8 := (cast_low ha).trans (((Int.mod_modEq a 8).symm).pow 2)
  have a0 : 0≤a%8 := by omega
  have a8 : a%8<8 := by omega
  interval_cases h : a%8 <;> norm_num [h] at rem <;> omega

private theorem lift_one (k : ℕ) {y : ℤ} (rem : y%8=1) : Sq k y := by
  have eq : y=1+8*(y/8) := by omega
  simpa only [←eq] using PersistentLocalSurvivors.dyadic_unit_square (y/8) (k+3)

private theorem digit_mod (y : ℤ) : (y+4*y^2)%8 = ((y%8)+4*(y%8)^2)%8 :=
  let h := (Int.mod_modEq y 8).symm
  h.add ((h.pow 2).mul_left 4)

private theorem good_low (k : ℕ) {y : ℤ} (ok : Good k y) : y%8=0 ∨ y%8=4 ∨ y%8=5 := by
  have sq : Sq k (y+4*y^2) := by simpa only [Sq,Good,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_pow,digit] using ok
  have rem := sq_low k sq
  rw [digit_mod] at rem
  have lo : 0≤y%8 := by omega
  have hi : y%8<8 := by omega
  interval_cases h : y%8 <;> norm_num [h] at rem ⊢

private theorem good_five (k : ℕ) {y : ℤ} (h : y%8=5) : Good k y := by
  have mod : (y+4*y^2)%8=1 := by rw [digit_mod,h]; decide
  simpa only [Sq,Good,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_pow,digit] using lift_one k mod

private theorem good_even (k : ℕ) {y : ℤ} (h : y%2=0) : Good k y ↔ Sq k y := by
  have sy : IsSquare (1+4*(y : R k)) := by
    simpa only [Sq,Good,Int.cast_add,Int.cast_one,Int.cast_mul,Int.cast_ofNat] using
      lift_one k (by omega : (1+4*y)%8=1)
  obtain ⟨v,hv⟩ := sy
  have uv : IsUnit v := by
    apply isUnit_mul_self_iff.mp
    rw [←hv]
    let a := (y : R k)
    have cop := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬2∣1+4*a.val)).symm.pow_right (k+3)
    simpa [a] using (ZMod.isUnit_iff_coprime _ _).mpr cop
  obtain ⟨u,rfl⟩ := uv
  have d : digit (y : R k)=(y : R k)*(u:R k)*(u:R k) := by
    unfold digit
    linear_combination (y : R k)*hv
  rw [show Good k y ↔ IsSquare ((y : R k)*(u:R k)*(u:R k)) by rw [←d]]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z*↑(u⁻¹),?_⟩
    calc (y : R k) = (((y : R k)*u*u)*↑(u⁻¹))*↑(u⁻¹) := by simp [mul_assoc]
         _ = _ := by rw [hz]; ring
  · rintro ⟨z,hz⟩
    exact ⟨z*(u:R k),by rw [hz]; ring⟩

private theorem good_even_square (k : ℕ) (x : ℤ) : Good k (4*x^2) :=
  (good_even k (by omega)).mpr ⟨2*(x:R k),by push_cast; ring⟩

private theorem low_shift (k : ℕ) (d : ℤ) (hi : d%8=5 ∨ d%8=1) :
    ∃ y : ℤ, Good k y ∧ Good k (y+d) := by
  rcases hi with h|h
  · exact ⟨0,by simpa using good_even_square k 0,good_five k (by omega)⟩
  · exact ⟨4,by simpa using good_even_square k 1,good_five k (by omega)⟩

/-- High digits within one sign coexist at difference d precisely when d is not 2 mod 4. -/
theorem digit_difference (k : ℕ) (d : ℤ) :
    (∃ y : ℤ, IsSquare (digit (y : ZMod (2^(k+3)))) ∧
      IsSquare (digit ((y+d : ℤ) : ZMod (2^(k+3))))) ↔ d%4≠2 := by
  constructor
  · rintro ⟨y,a,b⟩
    have l := good_low k a
    have r := good_low k b
    omega
  · intro ok
    by_cases mult : d%4=0
    · by_cases eight : d%8=0
      · exact ⟨5,good_five k (by decide),good_five k (by omega)⟩
      · let a := (d/4-1)/2
        have h : d=4*(2*a+1) := by dsimp [a]; omega
        refine ⟨4*a^2,good_even_square k _,?_⟩
        rw [show 4*a^2+d=4*(a+1)^2 by linear_combination h]
        exact good_even_square k _
    · by_cases positive : d%8=5 ∨ d%8=1
      · exact low_shift k d positive
      · obtain ⟨y,a,b⟩ := low_shift k (-d) (by omega)
        exact ⟨y+(-d),b,by simpa using a⟩

/-- A sum of an odd and an even helpful digit realizes both residues 1 and 5 modulo 8. -/
private theorem mix_sum (k : ℕ) {h : ℤ} (low : h%4=1) :
    ∃ a b : ℤ, h=a+b ∧ Good k a ∧ Good k b := by
  by_cases five : h%8=5
  · exact ⟨h,0,by ring,good_five k five,by simpa using good_even_square k 0⟩
  · exact ⟨h-4,4,by ring,good_five k (by omega),by simpa using good_even_square k 1⟩

private theorem sum_two_good (k : ℕ) {h : ℤ} (low : h%8=2) :
    ∃ a b : ℤ, h=a+b ∧ Good k a ∧ Good k b :=
  ⟨5,h-5,by ring,good_five k (by decide),good_five k (by omega)⟩

/-- Numbers 1 modulo 4 or 2 modulo 8 are sums of two squares at every dyadic depth. -/
private theorem square_sum_at (k : ℕ) {h : ℤ} (low : h%4=1 ∨ h%8=2) :
    ∃ x y : R k, (h : R k)=x^2+y^2 := by
  let a : ℤ := if h%8=1 then 0 else if h%8=2 then 1 else 2
  have rem : (h-a^2)%8=1 := by
    dsimp [a]
    split_ifs <;> norm_num <;> omega
  obtain ⟨u,hu⟩ := lift_one k rem
  refine ⟨u,a,?_⟩
  push_cast at hu
  linear_combination hu

/-- Across opposite signs, the attainable sums of the two high digits are exactly
the sums of two ordinary squares at the same precision. -/
theorem digit_sum (k : ℕ) (h : ℤ) :
    (∃ a b : ℤ, h=a+b ∧ IsSquare (digit (a : ZMod (2^(k+3)))) ∧
      IsSquare (digit (b : ZMod (2^(k+3))))) ↔
    ∃ x y : ZMod (2^(k+3)), (h : ZMod (2^(k+3)))=x^2+y^2 := by
  constructor
  · rintro ⟨a,b,rfl,ha,hb⟩
    have la := good_low k ha
    have lb := good_low k hb
    by_cases even : a%2=0 ∧ b%2=0
    · obtain ⟨x,hx⟩ := (good_even k even.1).mp ha
      obtain ⟨y,hy⟩ := (good_even k even.2).mp hb
      exact ⟨x,y,by rw [Int.cast_add,hx,hy]; ring⟩
    · exact square_sum_at k (by omega)
  · rintro ⟨x,y,eq⟩
    obtain ⟨a,ra⟩ := ZMod.intCast_surjective (x^2)
    have rb : ((h-a : ℤ) : R k)=y^2 := by rw [Int.cast_sub,ra,eq]; ring
    have sa : Sq k a := ⟨x,by rwa [←pow_two]⟩
    have sb : Sq k (h-a) := ⟨y,by rwa [←pow_two]⟩
    have la := sq_low k sa
    have lb := sq_low k sb
    by_cases even : a%2=0 ∧ (h-a)%2=0
    · exact ⟨a,h-a,by ring,(good_even k even.1).mpr sa,(good_even k even.2).mpr sb⟩
    · by_cases both : a%2=1 ∧ (h-a)%2=1
      · exact sum_two_good k (by omega)
      · exact mix_sum k (by omega)

/-- Exact normalized difference classes at all precisions from 128 upward. -/
def UnitGap (k : ℕ) (t : ℤ) : Prop :=
  (∃ d : ℤ, t=16*d ∧ d%4≠2) ∨
  ∃ h : ℤ, (t=4+16*h ∨ t=-(4+16*h)) ∧
    ∃ x y : ZMod (2^(k+3)), (h : ZMod (2^(k+3)))=x^2+y^2

private theorem pair_gap {m : ℕ} {n : ZMod m} {s q t : ℤ}
    (a : AdmissibleSum n (s : ZMod m)) (b : AdmissibleSum n (q : ZMod m))
    (delta : q=s+t) : Gap m n (t : ZMod m) := by
  refine ⟨s,a,?_⟩
  simpa only [delta,Int.cast_add] using b

/-- For product one the two high-digit tests describe every displacement and produce
both traces whenever the displacement passes. -/
theorem unit_gap (k : ℕ) (t : ℤ) : Gap (2^(k+7)) 1 (t : ZMod _) ↔ UnitGap k t := by
  constructor
  · rintro ⟨s,sa,sb⟩
    obtain ⟨z,rz⟩ := ZMod.intCast_surjective s
    obtain ⟨a,signa,ha⟩ := (unit_normal_form (k+3) z).mp (by simpa only [rz] using sa)
    obtain ⟨b,signb,hb⟩ := (unit_normal_form (k+3) (z+t)).mp (by simpa only [Int.cast_add,rz] using sb)
    have sum := (digit_sum k (a+b)).mp ⟨a,b,rfl,ha,hb⟩
    rcases signa with x|x <;> rcases signb with y|y
    · exact Or.inl ⟨b-a,by linarith only [x,y],
        (digit_difference k _).mp ⟨a,ha,by simpa using hb⟩⟩
    · exact Or.inr ⟨a+b,Or.inr (by linarith only [x,y]),sum⟩
    · exact Or.inr ⟨a+b,Or.inl (by linarith only [x,y]),sum⟩
    · exact Or.inl ⟨a-b,by linarith only [x,y],
        (digit_difference k _).mp ⟨b,hb,by simpa using ha⟩⟩
  · have pos (a : ℤ) (h : Good k a) := (singular_branch (k+3) a).mpr h
    have neg (a : ℤ) (h : Good k a) :=
      (unit_normal_form (k+3) (-(2+16*a))).mpr ⟨a,Or.inr rfl,h⟩
    rintro (⟨d,rfl,ok⟩|⟨h,sign,ok⟩)
    · obtain ⟨a,ha,hb⟩ := (digit_difference k d).mpr ok
      exact pair_gap (pos a ha) (pos (a+d) hb) (by ring)
    · obtain ⟨a,b,rfl,ha,hb⟩ := (digit_sum k h).mpr ok
      rcases sign with rfl|rfl
      · exact pair_gap (neg a ha) (pos b hb) (by ring)
      · exact pair_gap (pos a ha) (neg b hb) (by ring)

/-- Rescaling by a unit changes the product by its square and the displacement by
the unit. This applies in every modulus, including those with singular trace fibers. -/
theorem scale_iff {m : ℕ} (r : (ZMod m)ˣ) (t : ZMod m) :
    Gap m ((r:ZMod m)*r) ((r:ZMod m)*t) ↔ Gap m 1 t := by
  constructor
  · rintro ⟨s,a,b⟩
    let w := (↑(r⁻¹) : ZMod m)*s
    have rw' : (r : ZMod m)*w=s := by dsimp only [w]; rw [←mul_assoc]; simp
    exact ⟨w,(normalize r w).mp (rw' ▸ a),(normalize r (w+t)).mp (by rwa [mul_add,rw'])⟩
  · rintro ⟨s,a,b⟩
    exact ⟨(r : ZMod m)*s,(normalize r s).mpr a,by simpa only [mul_add] using (normalize r (s+t)).mpr b⟩

/-- Given just a product 1 modulo 8, a square-root unit exists at every depth;
the normalized integer displacement has the exact test above. -/
theorem square_product {N : ℕ} (residue : N%8=1) (k : ℕ) :
    ∃ r : (ZMod (2^(k+7)))ˣ, (r : ZMod (2^(k+7)))*(r : ZMod (2^(k+7)))=N ∧
      ∀ t : ℤ, Gap (2^(k+7)) N ((r : ZMod (2^(k+7)))*(t : ZMod (2^(k+7)))) ↔ UnitGap k t := by
  obtain ⟨r,hr⟩ := normalizing_unit residue (k+7)
  exact ⟨r,hr,fun t => by rw [←hr,scale_iff,unit_gap]⟩

private abbrev Norm (e : ℕ) (h : ℤ) := ∃ x y : ZMod (2^e), (h : ZMod (2^e))=x^2+y^2

private theorem lattice (e : ℕ) (h : ℤ) : Norm e h ↔ ∃ a b z : ℤ, h=a^2+b^2+2^e*z := by
  constructor
  · rintro ⟨x,y,eq⟩
    obtain ⟨a,ra⟩ := ZMod.intCast_surjective x
    obtain ⟨b,rb⟩ := ZMod.intCast_surjective y
    have E : ((a^2+b^2 : ℤ) : ZMod (2^e))=h := by simp only [Int.cast_add,Int.cast_pow,ra,rb,←eq]
    obtain ⟨z,hz⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp E
    push_cast at hz
    exact ⟨a,b,z,by linarith only [hz]⟩
  · rintro ⟨a,b,z,hz⟩
    refine ⟨a,b,?_⟩
    have E := (ZMod.intCast_eq_intCast_iff_dvd_sub (a^2+b^2) h (2^e)).mpr
      ⟨z,by push_cast; linarith only [hz]⟩
    simpa only [Int.cast_add,Int.cast_pow] using E.symm

private theorem low_four (a : ℤ) : a^2%4=a%2 := by
  have r : a^2%4=(a%4)^2%4 := ((Int.mod_modEq a 4).symm).pow 2
  have lo : 0≤a%4 := by omega
  have hi : a%4<4 := by omega
  interval_cases w : a%4 <;> norm_num [w] at r <;> omega

private theorem halve (e : ℕ) (h : ℤ) (even : h%2=0) :
    Norm (e+1) h ↔ Norm e (h/2) := by
  rw [lattice,lattice]
  have hh : 2*(h/2)=h := by omega
  constructor
  · rintro ⟨a,b,z,eq⟩
    rw [pow_succ] at eq
    have eq' : h=a^2+b^2+2*(2^e*z) := by linear_combination eq
    have la := low_four a
    have lb := low_four b
    let A := (a+b)/2
    let B := (a-b)/2
    have aa : a=A+B := by dsimp only [A,B]; omega
    have bb : b=A-B := by dsimp only [A,B]; omega
    refine ⟨A,B,z,?_⟩
    rw [aa,bb] at eq'
    nlinarith only [hh,eq']
  · rintro ⟨a,b,z,eq⟩
    exact ⟨a+b,a-b,z,by rw [pow_succ]; linear_combination 2*eq-hh⟩

private theorem odd_norm (e : ℕ) (h : ℤ) (odd : h%2=1) : Norm (e+2) h ↔ h%4=1 := by
  constructor
  · intro ok
    obtain ⟨a,b,z,eq⟩ := (lattice _ _).mp ok
    have eq' : h=a^2+b^2+4*(2^e*z) := by rw [pow_add] at eq; linear_combination eq
    have la := low_four a
    have lb := low_four b
    omega
  · intro rem
    let a : ℤ := if h%8=1 then 0 else 2
    have r : (h-a^2)%8=1 := by dsimp [a]; split_ifs <;> norm_num <;> omega
    have eq : h-a^2=1+8*((h-a^2)/8) := by omega
    obtain ⟨u,hu⟩ := PersistentLocalSurvivors.dyadic_unit_square ((h-a^2)/8) (e+2)
    rw [←eq] at hu
    push_cast at hu
    exact ⟨u,a,by linear_combination hu⟩

/-- With at most one remaining bit every target is a sum of two squares. Otherwise
strip powers of two until an odd part is reached and test its two low bits. -/
def normTest : ℕ → ℤ → Bool
  | 0, _ => true
  | 1, _ => true
  | e+2, h => if h%2=0 then normTest (e+1) (h/2) else h%4==1

theorem normTest_iff (e : ℕ) (h : ℤ) : normTest e h=true ↔
    ∃ x y : ZMod (2^e), (h : ZMod (2^e))=x^2+y^2 := by
  induction e generalizing h with
  | zero => exact ⟨fun _ => ⟨0,0,by change (_ : ZMod 1)=_; exact Subsingleton.elim ..⟩,fun _ => rfl⟩
  | succ e ih =>
    cases e with
    | zero =>
      have low : ∀ x : ZMod 2, x=0^2+x^2 := by decide +kernel
      exact ⟨fun _ => ⟨0,h,low _⟩,fun _ => rfl⟩
    | succ e =>
      by_cases even : h%2=0
      · rw [normTest,if_pos even,ih]
        exact (halve _ _ even).symm
      · rw [normTest,if_neg even,beq_iff_eq]
        exact (odd_norm _ _ (by omega)).symm

private theorem even_trace {m : ℕ} (div : 2∣m) {N s : ℤ} (odd : N%2=1)
    (ok : AdmissibleSum (N : ZMod m) (s : ZMod m)) : s%2=0 := by
  obtain ⟨x,y,xy,plus⟩ := ok
  let f := ZMod.castHom div (ZMod 2)
  have one : (N:ZMod 2)=1 := (ZMod.intCast_eq_intCast_iff' N 1 2).mpr odd
  have prod : f x*f y=1 := by rw [←map_mul,xy,map_intCast,one]
  have zero := (show ∀ a b : ZMod 2, a*b=1 → a+b=0 by decide) _ _ prod
  have red : (s : ZMod 2)=0 := by simpa only [←map_add,plus,map_intCast] using zero
  exact (ZMod.intCast_eq_intCast_iff' s 0 2).mp (by simpa only [Int.cast_zero] using red)

private theorem sum8 {N s : ℤ} (n : N%4=3) (k : ℕ) :
    AdmissibleSum (N : ZMod (2^(k+3))) (s : ZMod _) ↔ s%8=(N+1)%8 := by
  have even (h : s%2=0) : AdmissibleSum (N : ZMod (2^(k+3))) (s : ZMod _) ↔ s%8=(N+1)%8 := by
    let v := s/2
    have eq : s=2*v := by dsimp [v]; omega
    have casts (m : ℕ) : (s : ZMod m)=2*(v : ZMod m) := by rw [eq,Int.cast_mul,Int.cast_ofNat]
    have low (b : ℤ) : s%8=b%8 ↔ (s : ZMod 8)=(b : ZMod 8) := (ZMod.intCast_eq_intCast_iff' ..).symm
    rw [low,casts,casts,Int.cast_add,Int.cast_one]
    exact three_mod_four n (by omega)
  refine ⟨fun a => (even (even_trace (dvd_pow_self 2 (by omega)) (by omega) a)).mp a,
    fun a => (even (by omega)).mpr a⟩

private theorem sum32 {N s : ℤ} (n : N%8=5) (k : ℕ) :
    AdmissibleSum (N : ZMod (2^(k+5))) (s : ZMod _) ↔ s%32=(N+1)%32 ∨ s%32=(-(N+1))%32 := by
  have even (h : s%2=0) : AdmissibleSum (N : ZMod (2^(k+5))) (s : ZMod _) ↔
      s%32=(N+1)%32 ∨ s%32=(-(N+1))%32 := by
    let v := s/2
    have eq : s=2*v := by dsimp [v]; omega
    have casts (m : ℕ) : (s : ZMod m)=2*(v : ZMod m) := by rw [eq,Int.cast_mul,Int.cast_ofNat]
    have low (b : ℤ) : s%32=b%32 ↔ (s : ZMod 32)=(b : ZMod 32) := (ZMod.intCast_eq_intCast_iff' ..).symm
    rw [low,low]
    simp only [casts,Int.cast_add,Int.cast_one,Int.cast_neg]
    exact five_mod_eight n (by omega)
  refine ⟨fun a => (even (even_trace (dvd_pow_self 2 (by omega)) (by omega) a)).mp a,
    fun a => (even (by omega)).mpr a⟩

/-- For N equal to 3 modulo 4, every multiple of eight occurs as a spacing, permanently. -/
theorem three_gap {N : ℤ} (n : N%4=3) (k : ℕ) (t : ℤ) :
    Gap (2^(k+3)) N t ↔ t%8=0 := by
  constructor
  · rintro ⟨s,a,b⟩
    obtain ⟨z,hz⟩ := ZMod.intCast_surjective s
    have l := (sum8 (s:=z) n k).mp (by simpa only [hz] using a)
    have r := (sum8 (s:=z+t) n k).mp (by simpa only [Int.cast_add,hz] using b)
    omega
  · intro ok
    exact pair_gap ((sum8 (s:=N+1) n k).mpr rfl) ((sum8 (s:=N+1+t) n k).mpr (by omega)) rfl

/-- For N equal to 5 modulo 8 there are exactly three gap residues modulo 32.
Their entire lifts persist at every higher power of two. -/
theorem five_gap {N : ℤ} (n : N%8=5) (k : ℕ) (t : ℤ) :
    Gap (2^(k+5)) N t ↔ t%32=0 ∨ t%32=(2*(N+1))%32 ∨ t%32=(-2*(N+1))%32 := by
  constructor
  · rintro ⟨s,a,b⟩
    obtain ⟨z,hz⟩ := ZMod.intCast_surjective s
    have l := (sum32 (s:=z) n k).mp (by simpa only [hz] using a)
    have r := (sum32 (s:=z+t) n k).mp (by simpa only [Int.cast_add,hz] using b)
    rcases l with l|l <;> rcases r with r|r <;> omega
  · rintro (zero|pos|neg)
    · exact pair_gap ((sum32 (s:=N+1) n k).mpr (Or.inl rfl))
        ((sum32 (s:=N+1+t) n k).mpr (Or.inl (by omega))) rfl
    · exact pair_gap ((sum32 (s:=-(N+1)) n k).mpr (Or.inr rfl))
        ((sum32 (s:=-(N+1)+t) n k).mpr (Or.inl (by omega))) rfl
    · exact pair_gap ((sum32 (s:=N+1) n k).mpr (Or.inl rfl))
        ((sum32 (s:=N+1+t) n k).mpr (Or.inr (by omega))) rfl

/-- Every odd sum is compatible with an even product at every two-adic precision. -/
theorem even_product {N s : ℤ} (even : N%2=0) (odd : s%2=1) (e : ℕ) :
    AdmissibleSum (N : ZMod (2^e)) (s : ZMod _) := by
  have low := sq_low 0 (y:=s^2) ⟨(s : R 0),by rw [Int.cast_pow,pow_two]⟩
  have par := low_four s
  obtain ⟨d,od,z,hz⟩ := LocalMidpointLanes.lift_eight
    (by omega : (8:ℤ) ∣ (s^2-4*N)-1) e
  obtain ⟨w,hw⟩ := od
  let x := (s+d)/2
  let y := s-x
  have dx : d=2*x-s := by dsimp only [x]; omega
  have eq : x*y-N=(2:ℤ)^e*(2*z) := by
    dsimp only [y]
    rw [pow_add,dx] at hz
    nlinarith only [hz]
  have prod := (ZMod.intCast_eq_intCast_iff_dvd_sub N (x*y) (2^e)).mpr ⟨2*z,by simpa using eq⟩
  exact ⟨x,y,by simpa only [Int.cast_mul] using prod.symm,by dsimp [y]; push_cast; ring⟩

private theorem scaled_stride {N t : ℤ} (residue : N%8=1) (k : ℕ) (dt : (64:ℤ)∣t) :
    Gap (2^(k+7)) N t := by
  let M := 2^(k+7)
  let v := ((N/8 : ℤ) : ZMod M)
  have eq : N=1+8*(N/8) := by omega
  have unitN : IsUnit (N : ZMod M) := by
    have cop := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬2∣1+8*v.val)).symm.pow_right (k+7)
    have push : (N : ZMod M)=1+8*v := by
      simpa only [Int.cast_add,Int.cast_one,Int.cast_mul,Int.cast_ofNat,v] using
        congrArg (fun z : ℤ => (z : ZMod M)) eq
    rw [push]
    simpa [M] using (ZMod.isUnit_iff_coprime _ _).mpr cop
  obtain ⟨r,hr⟩ := PersistentLocalSurvivors.dyadic_unit_square (N/8) (k+7)
  rw [←eq] at hr
  have unit : IsUnit r := isUnit_mul_self_iff.mp (hr ▸ unitN)
  let u := unit.unit
  have prod : (u : ZMod M)*u=N := by rw [show (u : ZMod M)=r from unit.unit_spec,←hr]
  obtain ⟨z,rfl⟩ := dt
  obtain ⟨j,hj⟩ := ZMod.intCast_surjective ((↑(u⁻¹) : ZMod M)*(z:ZMod M))
  have lift : (u : ZMod M)*((64*j : ℤ) : ZMod M)=((64*z : ℤ) : ZMod M) := by
    push_cast
    rw [hj,show (u:ZMod M)*(64*(↑(u⁻¹)*(z:ZMod M)))=64*((u*(↑(u⁻¹):ZMod M))*(z:ZMod M)) by ring]
    simp
  rw [←prod,←lift]
  apply (scale_iff u _).mpr
  exact (unit_gap k _).mpr (Or.inl ⟨4*j,by ring,by omega⟩)

/-- Sixty-four, and hence each of its integer multiples, occurs as a difference for
every product in every power of two. The two traces may use different factor pairs. -/
theorem sixtyfour (N t : ℤ) (e : ℕ) (dt : (64:ℤ)∣t) : Gap (2^e) N t := by
  apply UniversalSpacing.descends (pow_dvd_pow 2 (by omega : e≤e+7)) N t
  by_cases even : N%2=0
  · exact pair_gap (even_product (s:=1) even (by decide) (e+7))
      (even_product (s:=1+t) even (by omega) (e+7)) rfl
  by_cases three : N%4=3
  · exact (three_gap three (e+4) t).mpr (by omega)
  by_cases five : N%8=5
  · exact (five_gap five (e+2) t).mpr (Or.inl (by omega))
  exact scaled_stride (by omega) e dt

/-- At modulus 64 the unit product rules out every gap equal to 32 modulo 64. -/
theorem misses_32 {t : ℤ} (rem : t%64=32) : ¬Gap 64 1 (t : ZMod 64) := by
  have tt : (t : ZMod 64)=32 := (ZMod.intCast_eq_intCast_iff' t 32 64).mpr rem
  rw [tt]
  let P (s : ZMod 64) := s=2 ∨ s=18 ∨ s=46 ∨ s=62
  have values : ∀ x y : ZMod 64, x*y=1 → P (x+y) := by unfold P; decide +kernel
  have no : ∀ s : ZMod 64, P s → ¬P (s+32) := by unfold P; decide +kernel
  rintro ⟨s,⟨x,y,xy,plus⟩,⟨a,b,ab,shift⟩⟩
  exact no s (plus ▸ values x y xy) (shift ▸ values a b ab)

/-- Just three product residues suffice to force a universal spacing to be divisible by 64. -/
theorem sixtyfour_needed (t : ℤ) (a : Gap 64 1 t) (b : Gap 64 5 t) (c : Gap 64 59 t) : (64:ℤ)∣t := by
  have eight := (three_gap (N:=59) (by decide) 3 t).mp (by simpa only [Int.cast_ofNat] using c)
  have lanes := (five_gap (N:=5) (by decide) 1 t).mp (by simpa only [Int.cast_ofNat] using b)
  have miss : t%64≠32 := fun h => misses_32 h a
  norm_num at lanes
  omega

end PrimeFactors.TwoAdicSumSpacing
