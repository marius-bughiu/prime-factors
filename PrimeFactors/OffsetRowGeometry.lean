import PrimeFactors.OffsetLatticeBatches
import PrimeFactors.PrimePower

namespace PrimeFactors.OffsetRowGeometry

/-- In a finite slope class whose discriminant vanishes modulo p, every
primitive square hit lies in one index-p sublattice. R is the publicly
computed lift of the first slope r to a zero modulo p². -/
theorem forced_line {p : ℕ} [Fact p.Prime] (odd : p ≠ 2)
    {N T j k z r R : ℤ} (unit : (N : ZMod p) ≠ 0) (prim : IsCoprime j k)
    (base : j ≡ r*k [ZMOD (p:ℤ)]) (digit : R ≡ r [ZMOD (p:ℤ)])
    (root : (p:ℤ)^2 ∣ (R+2*T)^2-4*N)
    (hit : (j+2*T*k)^2-4*N*k^2=z^2) : j ≡ R*k [ZMOD (p:ℤ)^2] := by
  have line := base.trans (digit.symm.mul_right k)
  have jp : (j : ZMod p) = (R:ZMod p)*k := by
    have e := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.modEq_iff_dvd.mp line)
    push_cast at e
    exact (sub_eq_zero.mp e).symm
  have rv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    ((dvd_pow_self (p:ℤ) (by decide : 2≠0)).trans root)
  push_cast at rv
  have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have four : (4 : ZMod p) ≠ 0 := by simpa [show (4:ZMod p)=2*2 by norm_num] using mul_ne_zero two two
  have nonzero : (R:ZMod p)+2*T ≠ 0 := by
    intro bad
    simp [bad,four,unit] at rv
  have ku : (k:ZMod p) ≠ 0 := by
    intro bad
    obtain ⟨s,t,e⟩ := prim
    have ee := congrArg (fun x:ℤ => (x:ZMod p)) e
    push_cast at ee
    simp [jp,bad] at ee
  have hmod := congrArg (fun x:ℤ => (x:ZMod p)) hit
  push_cast at hmod
  rw [jp] at hmod
  have zzero : (z:ZMod p)^2=0 := by linear_combination -hmod+(k:ZMod p)^2*rv
  have zd : (p:ℤ)∣z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (pow_eq_zero zzero)
  have sumUnit : IsCoprime (p:ℤ) (j+2*T*k+(R+2*T)*k) := by
    apply (Nat.prime_iff_prime_int.mp Fact.out).coprime_iff_not_dvd.mpr
    intro bad
    have ez := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr bad
    push_cast at ez
    rw [jp] at ez
    apply (mul_ne_zero (mul_ne_zero two nonzero) ku)
    linear_combination ez
  apply Int.modEq_iff_dvd.mpr
  apply sumUnit.pow_left.dvd_of_dvd_mul_right
  obtain ⟨v,hv⟩ := root
  obtain ⟨w,hw⟩ := zd
  exact ⟨k^2*v-w^2,by rw [hw] at hit; linear_combination k^2*hv-hit⟩

/-- The algorithm makes one Newton digit from the first discriminant
quotient. Its test only needs a modular inverse of 2*(r+2T). -/
theorem lifted_root {p r T N i q v : ℤ} (first : (r+2*T)^2-4*N=p*q)
    (digit : q+2*(r+2*T)*i=p*v) :
    p^2 ∣ (r+p*i+2*T)^2-4*N := by
  exact ⟨v+i^2,by linear_combination first+p*digit⟩

/-- The second digit is selected from N,T,r before the unknown search
coordinates are given. All primitive hits in the parent belong to this
one lifted line. -/
theorem select_line {p : ℕ} [Fact p.Prime] (odd : p ≠ 2) {N T r : ℤ}
    (unit : (N:ZMod p) ≠ 0) (baseRoot : (p:ℤ) ∣ (r+2*T)^2-4*N) :
    ∃ R : ℤ, R ≡ r [ZMOD (p:ℤ)] ∧ (p:ℤ)^2 ∣ (R+2*T)^2-4*N ∧
      ∀ j k z : ℤ, IsCoprime j k → j ≡ r*k [ZMOD (p:ℤ)] →
        (j+2*T*k)^2-4*N*k^2=z^2 → j ≡ R*k [ZMOD (p:ℤ)^2] := by
  obtain ⟨q,hq⟩ := baseRoot
  obtain ⟨i,hi⟩ := ZMod.intCast_surjective (-(q:ZMod p)/(2*((r+2*T:ℤ):ZMod p)))
  let R := r + (p:ℤ)*i
  have digit : R ≡ r [ZMOD (p:ℤ)] := Int.modEq_iff_dvd.mpr ⟨-i,by dsimp [R];ring⟩
  have hs := (admissibleSum_singular_digit_iff odd N (r+2*T) q i unit hq).mpr hi
  have first : (p:ℤ)∣(r+2*T+(p:ℤ)*i)^2-4*N := ⟨q+2*(r+2*T)*i+p*i^2,by linear_combination hq⟩
  have root := (admissibleSum_prime_sq_iff_of_singular odd N _ first).mp hs
  have lifted : (p:ℤ)^2∣(R+2*T)^2-4*N := by
    simpa only [show R+2*T=r+2*T+(p:ℤ)*i by dsimp [R];ring] using root
  exact ⟨R,digit,lifted,fun _ _ _ prim base hit => forced_line odd unit prim base digit lifted hit⟩

/-- The homogeneous discriminant on the row w*x+u*y has this
determinant identity, with M=det(x,y) and N=T²+h. -/
theorem row_gram (T h a b c d : ℝ) :
    (a*c+2*T*(a*d+b*c)-4*h*b*d)^2 -
      (a^2+4*b*(T*a-h*b))*(c^2+4*d*(T*c-h*d)) =
      4*(T^2+h)*(a*d-b*c)^2 := by ring

/-- At three consecutive positions, the second difference of the real
square roots cannot be small if the row determinant and its index are large. -/
theorem root_difference {A B C N M u w l z r : ℝ}
    (gram : B^2-A*C=4*N*M^2)
    (left : l^2=A*(w-1)^2+2*B*(w-1)*u+C*u^2)
    (middle : z^2=A*w^2+2*B*w*u+C*u^2)
    (right : r^2=A*(w+1)^2+2*B*(w+1)*u+C*u^2) :
    (2*z-l-r)*(2*z+l+r)*(4*z^2-(l-r)^2)=64*N*(M*u)^2 := by
  calc
    _ = (4*z^2-l^2-r^2)^2-4*l^2*r^2 := by ring
    _ = _ := by rw [left,middle,right]; linear_combination 16*u^2*gram

/-- If all three roots fit between two parallel affine lines of vertical
separation E, their midpoint deviation is ≤2E. The Gram identity gives
a necessary lower bound on E, independently of the candidate slope. -/
theorem strip_width {N M u l z r L slope E U : ℝ} (ep : 0≤E)
    (lp : 0≤l) (zp : 0≤z) (rp : 0≤r)
    (lu : l≤U) (zu : z≤U) (ru : r≤U)
    (left : L-slope≤l ∧ l≤L-slope+E) (mid : L≤z ∧ z≤L+E)
    (right : L+slope≤r ∧ r≤L+slope+E)
    (identity : (2*z-l-r)*(2*z+l+r)*(4*z^2-(l-r)^2)=64*N*(M*u)^2) :
    2*N*(M*u)^2≤E*U^3 := by
  have up := lp.trans lu
  have first : |2*z-l-r|≤2*E := abs_le.mpr ⟨by linarith [left.2,right.2,mid.1],
    by linarith [left.1,right.1,mid.2]⟩
  have second : |2*z+l+r|≤4*U := by rw [abs_of_nonneg (by positivity)];linarith
  have delta : |l-r|≤U := abs_le.mpr ⟨by linarith,by linarith⟩
  have delta2 := pow_le_pow_left₀ (abs_nonneg _) delta 2
  rw [sq_abs] at delta2
  have z2 := pow_le_pow_left₀ zp zu 2
  have third : |4*z^2-(l-r)^2|≤4*U^2 := abs_le.mpr
    ⟨by nlinarith only [delta2,sq_nonneg z,sq_nonneg U],by nlinarith only [z2,sq_nonneg (l-r)]⟩
  have raw := mul_le_mul (mul_le_mul first second (abs_nonneg _) (by positivity))
    third (abs_nonneg _) (by positivity)
  rw [←abs_mul,←abs_mul,identity] at raw
  nlinarith only [le_abs_self (64*N*(M*u)^2),raw]

end PrimeFactors.OffsetRowGeometry
