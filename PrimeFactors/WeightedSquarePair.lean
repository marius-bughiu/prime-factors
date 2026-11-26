import PrimeFactors.MaskedRelations

/-! Compare the positive excesses over two differently weighted multiples of
the input. A square product gives a congruence of squares. The interval below
excludes both trivial signs without assuming that the input is semiprime. -/

namespace PrimeFactors.WeightedSquarePair

private theorem no_multiple {n x k : ℕ} (lo : k*n < x) (hi : x < (k+1)*n) : ¬ n ∣ x := by
  rintro ⟨t,rfl⟩
  rw [mul_comm n t] at lo hi
  have := Nat.lt_of_mul_lt_mul_right lo
  have := Nat.lt_of_mul_lt_mul_right hi
  omega

/-- The residue of the ordinary difference gcd agrees with its integer value.
The two signs are excluded by enclosing both integers in one gap between
multiples of n. -/
theorem split_between {n a b d e z i j k : ℕ} [NeZero n]
    (first : a^2=i*n+d) (second : b^2=j*n+e) (square : z^2=d*e)
    (lo : k*n+z<a*b) (hi : a*b+z<(k+1)*n) :
    1<(a*b-z).gcd n ∧ (a*b-z).gcd n<n := by
  have nonneg : z≤a*b := by omega
  have left : ¬n∣a*b-z := no_multiple (k:=k) (by omega) (by omega)
  have right : ¬n∣a*b+z := no_multiple (k:=k) (by omega) hi
  have castEq (x w h : ℕ) (eq : x^2=h*n+w) : (x:ZMod n)^2=w := by
    simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,
      mul_zero,zero_add] using congrArg (fun m : ℕ => (m:ZMod n)) eq
  have same : ((a*b:ℕ):ZMod n)^2=(z:ZMod n)^2 := by
    rw [Nat.cast_mul,mul_pow,castEq _ _ _ first,castEq _ _ _ second,← Nat.cast_mul,
      ← square,Nat.cast_pow]
  have split := maskedRelations_split same (by
    intro eq
    apply left
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd,Nat.cast_sub nonneg,eq,sub_self]) (by
    intro eq
    apply right
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd,Nat.cast_add,eq,neg_add_cancel])
  rw [← Nat.cast_sub nonneg,ZMod.val_natCast,← Nat.gcd_rec n (a*b-z),Nat.gcd_comm n] at split
  exact split

/-- When both positive excesses are at most a tenth of the input, every
square match at multipliers 4 and 8 gives a proper divisor. -/
theorem split_small_excess {n a b d e z : ℕ} [NeZero n]
    (first : a^2=4*n+d) (second : b^2=8*n+e) (square : z^2=d*e)
    (smallD : 10*d≤n) (smallE : 10*e≤n) :
    1<(a*b-z).gcd n ∧ (a*b-z).gcd n<n := by
  have positive := NeZero.pos n
  have np := Nat.pow_pos positive (n:=2)
  have smallZ : 10*z≤n := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    calc (10*z)^2 = (10*d)*(10*e) := by rw [mul_pow,square]; ring
         _ ≤ n*n := Nat.mul_le_mul smallD smallE
         _ = _ := by ring
  have highA : 10*a^2≤41*n := by omega
  have highB : 10*b^2≤81*n := by omega
  have high := Nat.mul_le_mul highA highB
  have low := Nat.mul_le_mul (show 4*n≤a^2 by omega) (show 8*n≤b^2 by omega)
  have upper : 10*(a*b)<59*n := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    nlinarith only [high,np]
  have lower : 51*n<10*(a*b) := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    nlinarith only [low,np]
  apply split_between (k:=5) first second square <;> omega

/-- An explicit family of positive excesses with the same square class. The
parameterization arranges the two weights to differ by squares 8² and 3².
Finding *prime* p and q whose two labels are first in their respective rows
is an additional constraint on the construction. -/
theorem prescribed_ratio {p q a b d e : ℕ}
    (labelA : 3*a+7*q=17*p) (labelB : 8*b=17*p+7*q)
    (excessA : a^2=4*(p*q)+d) (excessB : b^2=8*(p*q)+e) :
    ∃ h, d=64*h ∧ e=9*h ∧ (24*h)^2=d*e := by
  have diff : 9*d = 64*e := by
    have s := congrArg (fun t : ℕ => t^2) labelA
    have t := congrArg (fun t : ℕ => t^2) labelB
    have elim := congrArg (fun t : ℕ => t*(14*q)) labelA
    dsimp only at s t elim
    nlinarith only [s,t,elim,excessA,excessB]
  have div : 64∣d := (show Nat.Coprime 64 9 by decide).dvd_of_dvd_mul_left
    (diff ▸ dvd_mul_right 64 e)
  obtain ⟨h,hd⟩ := div
  have he : e=9*h := by omega
  exact ⟨h,hd,he,by rw [hd,he]; ring⟩

/-- An actual nonsquare on each individual row can still produce two primes. -/
theorem worked_pair :
    1506^2=4*559697+29248 ∧ 2117^2=8*559697+4113 ∧
    171^2<29248 ∧ 29248<172^2 ∧ 64^2<4113 ∧ 4113<65^2 ∧
    10968^2=29248*4113 ∧ Nat.gcd (1506*2117-10968) 559697=887 ∧
    631*887=559697 ∧ Nat.Prime 631 ∧ Nat.Prime 887 := by
  norm_num

end PrimeFactors.WeightedSquarePair
