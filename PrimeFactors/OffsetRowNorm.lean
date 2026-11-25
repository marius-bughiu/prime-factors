import PrimeFactors.OffsetLatticeBatches
import PrimeFactors.PrimePowerCount

namespace PrimeFactors.OffsetRowNorm

/-- The row discriminant in any coefficient ring, before substituting h=N−T². -/
def disc {R : Type*} [CommRing R] (N T j k : R) := (j+2*T*k)^2-4*N*k^2

theorem disc_eq_form (T h j k : ℤ) :
    disc (T^2+h) T j k = GroupedOffsetRows.form T h j k := by
  unfold disc GroupedOffsetRows.form
  ring

theorem norm_identity {R : Type*} [CommRing R] (N T a b c d w u : R) :
    let A := disc N T a b
    let B := (a+2*T*b)*(c+2*T*d)-4*N*b*d
    (A*w+B*u)^2 - A*disc N T (a*w+c*u) (b*w+d*u) =
      4*N*((a*d-b*c)*u)^2 := by
  dsimp [disc]
  ring

/-- A primitive local square can be constructed at the horizontal line
or at slope N+1−2T, whose two normalized roots are 1 and N. -/
theorem local_seed {R : Type*} [CommRing R] (N T a b c d u : R)
    (invertible : IsUnit ((a*d-b*c)*u))
    (direction : IsUnit b ∨ IsUnit (a-b*(N+1-2*T))) :
    ∃ w z : R, disc N T (a*w+c*u) (b*w+d*u) = z^2 ∧
      (IsUnit (a*w+c*u) ∨ IsUnit (b*w+d*u)) := by
  rcases direction with ⟨v,hv⟩ | ⟨v,hv⟩
  · let w := -(d*u)*(↑(v⁻¹) : R)
    have zero : b*w+d*u=0 := by
      dsimp [w]
      calc
        _ = -(d*u)*((v:R)*(↑(v⁻¹):R))+d*u := by rw [hv]; ring
        _ = 0 := by simp
    have mult : b*(a*w+c*u) = -((a*d-b*c)*u) := by linear_combination a*zero
    refine ⟨w,a*w+c*u,by simp [disc,zero],Or.inl ?_⟩
    exact (isUnit_of_mul_isUnit_right (mult ▸ invertible.neg))
  · let r := N+1-2*T
    let w := (d*r-c)*u*(↑(v⁻¹) : R)
    have line : (a-b*r)*w=(d*r-c)*u := by
      dsimp [w]
      calc
        _ = (d*r-c)*u*((v:R)*(↑(v⁻¹):R)) := by rw [hv]; dsimp [r]; ring
        _ = _ := by simp
    have jk : a*w+c*u=r*(b*w+d*u) := by linear_combination line
    have mult : (a-b*r)*(b*w+d*u)=(a*d-b*c)*u := by linear_combination b*line
    refine ⟨w,(N-1)*(b*w+d*u),?_,Or.inr (isUnit_of_mul_isUnit_right (mult ▸ invertible))⟩
    rw [jk]
    dsimp [disc,r]
    ring

private theorem unit_of_digit {p e : ℕ} [Fact p.Prime] (x : ZMod (p^(e+1)))
    (nonzero : firstPrimeDigit p e x≠0) : IsUnit x := by
  obtain ⟨v,rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast] at nonzero
  exact (ZMod.isUnit_iff_coprime _ _).mpr <| Nat.Coprime.pow_right _ <|
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr fun h =>
      nonzero ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr h)).symm

/-- No prime-power test at a prime outside det*u excludes an entire row,
even if it insists that one of the original coordinates be a unit. -/
theorem good_prime_power {p : ℕ} [Fact p.Prime] (e : ℕ) (N T a b c d u : ZMod (p^(e+1)))
    (good : firstPrimeDigit p e ((a*d-b*c)*u)≠0) :
    ∃ w z : ZMod (p^(e+1)), disc N T (a*w+c*u) (b*w+d*u)=z^2 ∧
      (IsUnit (a*w+c*u) ∨ IsUnit (b*w+d*u)) := by
  apply local_seed N T a b c d u (unit_of_digit _ good)
  by_cases db : firstPrimeDigit p e b=0
  · right
    apply unit_of_digit
    intro h
    simp [map_sub,map_mul,db] at h
    simp [map_sub,map_mul,db,h] at good
  · exact Or.inl (unit_of_digit b db)

/-- The same row has a rational point without any local tests or factor
information. The finite-field conditions merely clear its denominator. -/
theorem rational_point (N T a b c d u : ℚ) (det : a*d-b*c≠0) :
    ∃ w z : ℚ, disc N T (a*w+c*u) (b*w+d*u)=z^2 := by
  by_cases zero : u=0
  · exact ⟨0,0,by simp [disc,zero]⟩
  have unit : IsUnit ((a*d-b*c)*u) := isUnit_iff_ne_zero.mpr (mul_ne_zero det zero)
  have direction : IsUnit b ∨ IsUnit (a-b*(N+1-2*T)) := by
    by_cases hb : b=0
    · right
      rw [hb,zero_mul,sub_zero]
      apply isUnit_iff_ne_zero.mpr
      intro az
      simp [hb,az] at det
    · exact Or.inl (isUnit_iff_ne_zero.mpr hb)
  obtain ⟨w,z,square,_⟩ := local_seed N T a b c d u unit direction
  exact ⟨w,z,square⟩

/-- After dividing a lattice axis by its content, the determinant with the
actual point replaces the original coefficient u in every pivot test. -/
theorem determinant_obstruction (T h a b j k z l : ℤ)
    (axis : IsCoprime a b) (primitive : IsCoprime j k)
    (square : z^2=GroupedOffsetRows.form T h j k) (div : l∣a*k-b*j) :
    ∃ s : ℤ, s^2 ≡ GroupedOffsetRows.form T h a b [ZMOD l] := by
  obtain ⟨x,y,bez⟩ := axis
  have det : a*x-b*(-y)=1 := by linear_combination bez
  obtain ⟨hj,hk⟩ := GroupedOffsetRows.coordinates det j k
  apply OffsetLatticeBatches.pivot_at_divisor (a:=a) (b:=b) (c:= -y) (d:=x)
    (w:=x*j-(-y)*k) (u:=a*k-b*j) (z:=z) _ _ div
  · rwa [hj,hk]
  · rwa [hj,hk]

theorem scaled_coordinate (a b c d g w u : ℤ) :
    a*((g*b)*w+d*u)-b*((g*a)*w+c*u) = (a*d-b*c)*u := by ring

private theorem unit_cross {p N A B C : ℤ} (prime : Prime p) (unit : ¬p∣2*N)
    (singular : p∣A) (identity : B^2-A*C=4*N) : ¬p∣2*B := by
  have two : ¬p∣(2:ℤ) := fun h => unit (dvd_mul_of_dvd_left h _)
  intro h
  have pb := (prime.dvd_mul.mp h).resolve_left two
  have h4 : p∣4*N := identity ▸ dvd_sub (pb.trans (dvd_pow_self B two_ne_zero))
    (dvd_mul_of_dvd_left singular C)
  rw [show (4:ℤ)*N=2*(2*N) by ring] at h4
  exact (prime.dvd_mul.mp h4).elim two unit

/-- For u=p*s²*v with p not dividing v or w, if (p*s)² divides A but p
does not divide 2B, there is no square even modulo (p*s)². The old
condition on A modulo u sees zero at p^(2t+1) when s=p^t. -/
theorem singular_shell {p s A B C v w : ℤ} (prime : Prime p) (nonzero : s≠0)
    (unitB : ¬p∣2*B) (unitV : ¬p∣v) (unitW : ¬p∣w) (high : (p*s)^2∣A) :
    ∀ z : ℤ, ¬(z^2 ≡ A*w^2+2*B*w*(p*s^2*v)+C*(p*s^2*v)^2 [ZMOD (p*s)^2]) := by
  rintro z mod
  obtain ⟨a,ha⟩ := high
  obtain ⟨q,hq⟩ := Int.modEq_iff_dvd.mp mod
  have ds : s^2 ∣ z^2 := by
    refine ⟨p^2*a*w^2+2*B*w*p*v+C*p^2*s^2*v^2-p^2*q,?_⟩
    rw [ha] at hq
    linear_combination -hq
  obtain ⟨y,hy⟩ := (Int.pow_dvd_pow_iff (by decide : 2≠0)).mp ds
  have eq : y^2=p^2*a*w^2+2*B*w*p*v+C*p^2*s^2*v^2-p^2*q := by
    apply mul_left_cancel₀ (pow_ne_zero 2 nonzero)
    rw [ha,hy] at hq
    linear_combination -hq
  have dp : p∣y^2 := ⟨p*a*w^2+2*B*w*v+C*p*s^2*v^2-p*q,by rw [eq]; ring⟩
  obtain ⟨i,hi⟩ := prime.dvd_of_dvd_pow dp
  have bad : p∣(2*B*w)*v := by
    refine ⟨i^2-a*w^2-C*s^2*v^2+q,?_⟩
    apply mul_left_cancel₀ prime.ne_zero
    rw [hi] at eq
    linear_combination -eq
  rcases prime.dvd_mul.mp bad with h | h
  · rcases prime.dvd_mul.mp h with h | h
    · exact unitB h
    · exact unitW h
  · exact unitV h

/-- Apply the odd-valuation obstruction directly to a selected primitive
axis and a primitive integer point. Only the product and the normalized
determinant enter the hypotheses; the complementary basis is supplied by Bézout. -/
theorem primitive_shell {p N T a b j k s v z : ℤ} (prime : Prime p) (unit : ¬p∣2*N)
    (axis : IsCoprime a b) (point : IsCoprime j k) (nonzero : s≠0) (unitV : ¬p∣v)
    (row : a*k-b*j=p*s^2*v) (high : (p*s)^2∣disc N T a b) :
    disc N T j k≠z^2 := by
  intro hit
  obtain ⟨x,y,bez⟩ := axis
  let w := x*j-(-y)*k
  let u := a*k-b*j
  have det : a*x-b*(-y)=1 := by linear_combination bez
  obtain ⟨hj,hk⟩ := GroupedOffsetRows.coordinates det j k
  change a*w+(-y)*u=j at hj
  change b*w+x*u=k at hk
  have cop := (GroupedOffsetRows.primitive_change det w u).mp (by rwa [hj,hk])
  have pw : ¬p∣w := fun hw => prime.not_unit (cop.isUnit_of_dvd' hw
    (show p∣u by change p∣a*k-b*j; rw [row]; exact ⟨s^2*v,by ring⟩))
  let A := disc N T a b
  let B := (a+2*T*b)*(-y+2*T*x)-4*N*b*x
  let C := disc N T (-y) x
  have singular : p∣A := by
    obtain ⟨r,hr⟩ := high
    exact ⟨p*s^2*r,by dsimp [A]; rw [hr]; ring⟩
  have identity : B^2-A*C = 4*N := by
    calc B^2-A*C = 4*N*(a*x-b*(-y))^2 := by dsimp [disc,A,B,C]; ring
         _ = 4*N := by rw [det]; ring
  have no := singular_shell (C:=C) prime nonzero (unit_cross prime unit singular identity) unitV pw high z
  apply no
  have eq : A*w^2+2*B*w*u+C*u^2 = disc N T j k := by
    rw [←hj,←hk]
    dsimp only [A,B,C,disc]
    ring
  change u=p*s^2*v at row
  rw [←row,eq,hit]

/-- The row of the following example has a primitive square at every prime
power, including those above the divisors of its public product. -/
theorem local_1247 (p : ℕ) [Fact p.Prime] (e : ℕ) :
    ∃ w z : ZMod (p^(e+1)), disc 1247 35 w (2*w-1)=z^2 ∧ (IsUnit w ∨ IsUnit (2*w-1)) := by
  have h := good_prime_power (p:=p) e 1247 35 1 2 0 1 (-1) (by simp)
  simpa [sub_eq_add_neg] using h

/-- Every residue modulus is locally soluble for this row, while its two
nonnegative integer values, 53 and 52, are both nonsquares. -/
theorem no_integer_square_1247 (w z : ℤ) : disc 1247 35 w (2*w-1)≠z^2 := by
  intro hit
  have norm : (71*w-106)^2+71*z^2=4988 := by
    unfold disc at hit
    linear_combination -71*hit
  have bound : -70≤71*w-106 ∧ 71*w-106≤70 := by
    constructor <;> by_contra! bad
    · have h : 0≤-(71*w-106)-71 := by omega
      nlinarith only [norm,sq_nonneg z,mul_nonneg h (show 0≤-(71*w-106)+71 by omega)]
    · have h : 0≤(71*w-106)-71 := by omega
      nlinarith only [norm,sq_nonneg z,mul_nonneg h (show 0≤(71*w-106)+71 by omega)]
  have wlo : 1≤w := by omega
  have whi : w≤2 := by omega
  interval_cases w <;> norm_num [disc] at hit <;>
    have hz : -7≤z ∧ z≤7 := by
      constructor <;> by_contra! bad
      · nlinarith [mul_nonneg (show 0≤-z-8 by omega) (show 0≤-z+8 by omega)]
      · nlinarith [mul_nonneg (show 0≤z-8 by omega) (show 0≤z+8 by omega)]
  all_goals obtain ⟨zl,zh⟩ := hz; interval_cases z <;> norm_num at hit

end PrimeFactors.OffsetRowNorm
