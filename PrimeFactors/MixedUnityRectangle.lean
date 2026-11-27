import PrimeFactors.RectangularRootWindows

/-! A single rectangular point on a positive difference-of-squares row
splits the product. Mixed roots of unity give such rows in a narrow box. -/
namespace PrimeFactors.MixedUnityRectangle

/-- CRT gives opposite local signs at any two coprime moduli above two.
This is an existence argument; constructing the CRT root uses the moduli. -/
theorem mixed_exists {p q : ℕ} (cp : p.Coprime q) (lp : 2<p) (lq : 2<q) :
    ∃ r : ZMod (p*q), r^2=1 ∧ r≠1 ∧ r≠-1 := by
  have separate {k : ℕ} (large : 2<k) : (1 : ZMod k) ≠ -1 := by
    intro h
    have z : ((2 : ℕ) : ZMod k) = 0 := by push_cast; linear_combination h
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<2) large
      ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp z)
  let e := ZMod.chineseRemainder cp
  refine ⟨e.symm (1,-1),e.injective ?_,?_,?_⟩
  · rw [map_pow,e.apply_symm_apply,map_one]
    exact Prod.ext (by simp) (by simp)
  · intro h
    have e' := congrArg e h
    rw [e.apply_symm_apply,map_one] at e'
    exact separate lq (congrArg Prod.snd e').symm
  · intro h
    have e' := congrArg e h
    rw [e.apply_symm_apply,map_neg,map_one] at e'
    exact separate lp (congrArg Prod.fst e')

private theorem gcd_split {N a b : ℕ} (ap : 0<a) (bp : 0<b)
    (al : a<N) (bl : b<N) (div : N∣a*b) :
    1<a.gcd N ∧ a.gcd N<N ∧ a.gcd N∣N := by
  refine ⟨?_,(Nat.le_of_dvd ap (Nat.gcd_dvd_left ..)).trans_lt al,Nat.gcd_dvd_right ..⟩
  have gp := Nat.gcd_pos_of_pos_left N ap
  by_contra! h
  have cop : a.Coprime N := by change a.gcd N=1; omega
  exact (Nat.not_dvd_of_pos_of_lt bp bl) (cop.symm.dvd_of_dvd_mul_left div)

/-- Any strictly positive row yields a proper gcd at both linear factors.
The check of gcd(y,N) can be omitted, even for composite products with
more than two prime factors. -/
theorem row_split {N k x y : ℕ} (kp : 0<k) (upper : y+x<N)
    (row : y^2=x^2+k*N) :
    1<(y-x).gcd N ∧ (y-x).gcd N<N ∧ (y-x).gcd N∣N ∧
    1<(y+x).gcd N ∧ (y+x).gcd N<N ∧ (y+x).gcd N∣N := by
  have prod := Nat.mul_pos kp (show 0<N by omega)
  have xy : x<y := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  have eq : (y-x)*(y+x)=k*N := by
    obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le xy.le
    simp only [Nat.add_sub_cancel_left]
    nlinarith only [row]
  have div : N∣(y-x)*(y+x) := ⟨k,eq.trans (Nat.mul_comm ..)⟩
  have a := gcd_split (a:=y-x) (b:=y+x) (by omega) (by omega) (by omega) upper div
  have b := gcd_split (a:=y+x) (b:=y-x) (by omega) (by omega) upper (by omega)
    (by rwa [Nat.mul_comm])
  exact ⟨a.1,a.2.1,a.2.2,b⟩

/-- For a mixed root the zero row is impossible with a unit denominator.
If the numerator square is smaller than N, the only remaining multiples
of N in y²−x² are strictly positive. -/
theorem positive_row {N y H : ℕ} {x : ℤ} {r : ZMod N} (np : 0<N)
    (short : H^2<N) (xh : x.natAbs≤H) (unit : IsUnit (y : ZMod N))
    (root : r^2=1) (plus : r≠1) (minus : r≠-1) (ratio : (x : ZMod N)=r*y) :
    ∃ k : ℕ, 0<k ∧ y^2=x.natAbs^2+k*N := by
  have neq : x^2 ≠ (y:ℤ)^2 := by
    intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with s|s
    · apply plus <| unit.mul_left_inj.mp ?_
      simpa only [←ratio,one_mul,Int.cast_natCast] using congrArg (fun i:ℤ => (i:ZMod N)) s
    · apply minus <| unit.mul_left_inj.mp ?_
      simpa only [←ratio,neg_one_mul,Int.cast_neg,Int.cast_natCast] using congrArg (fun i:ℤ => (i:ZMod N)) s
  have dv : (N:ℤ)∣(y:ℤ)^2-x^2 := by
    rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ratio,mul_pow,root,one_mul,sub_self]
  obtain ⟨m,hm⟩ := dv
  have small : x^2<(N:ℤ) := by
    have e : (x.natAbs:ℤ)^2<N := by exact_mod_cast (Nat.pow_le_pow_left xh 2).trans_lt short
    simpa only [Int.natCast_natAbs,sq_abs] using e
  have mp : 0<m := by
    rcases lt_trichotomy m 0 with neg|zero|pos
    · have hn : m≤-1 := by omega
      have mul := mul_le_mul_of_nonneg_left hn (show 0≤(N:ℤ) by positivity)
      nlinarith only [hm,mul,small,sq_nonneg (y:ℤ)]
    · exfalso
      apply neq
      rw [zero,mul_zero,sub_eq_zero] at hm
      exact hm.symm
    · exact pos
  refine ⟨m.natAbs,Int.natAbs_pos.mpr mp.ne',?_⟩
  exact_mod_cast (show (y:ℤ)^2=(x.natAbs:ℤ)^2+(m.natAbs:ℤ)*N by
    simp only [Int.natCast_natAbs,sq_abs,abs_of_pos mp]
    linear_combination hm)

/-- The rectangular mixed-root witness supplies a positive row and a
proper factor when the small numerator bound is below every prime divisor.
The ratio only witnesses existence. A product-only row scan uses x,y,k. -/
theorem cover {N B : ℕ} [NeZero N] (bp : 0<B) (upper : N/(B+1)+B<N)
    (short : (N/(B+1))^2<N) (large : ∀ l : ℕ, l.Prime → l∣N → N/(B+1)<l)
    (r : ZMod N) (root : r^2=1) (plus : r≠1) (minus : r≠-1) :
    ∃ (k y : ℕ) (x : ℤ), 0<k ∧ 0<y ∧ y≤B ∧ x.natAbs≤N/(B+1) ∧
      x.natAbs.Coprime y ∧ y.Coprime N ∧ (x:ZMod N)=r*y ∧
      y^2=x.natAbs^2+k*N ∧ 1<(y-x.natAbs).gcd N ∧ (y-x.natAbs).gcd N<N ∧
      (y-x.natAbs).gcd N∣N := by
  have unit : IsUnit r := isUnit_of_mul_eq_one r r (by simpa [pow_two] using root)
  obtain ⟨v,u,vp,vb,ub,eq⟩ := RectangularRootWindows.rectangle (NeZero.pos N) bp r
  have vn := RectangularRootWindows.coprime_denominator vp vb (by omega : B<N) ub large unit eq
  obtain ⟨y,x,yp,yb,xh,prim,yn,ratio⟩ := RectangularRootWindows.primitive vp vb ub vn eq
  obtain ⟨k,kp,h⟩ := positive_row (NeZero.pos N) short xh
    ((ZMod.isUnit_iff_coprime y N).mpr yn) root plus minus ratio
  obtain ⟨low,high,dv,_⟩ := row_split kp (by omega : y+x.natAbs<N) h
  exact ⟨k,y,x,kp,yp,yb,xh,prim,yn,ratio,h,low,high,dv⟩

/-- For distinct odd primes, it suffices for the numerator cutoff to be
below both primes. The row and both coordinates are searched from pq alone. -/
theorem semiprime {p q B : ℕ} (pp : p.Prime) (pq : q.Prime) (ne : p≠q)
    (lp : 2<p) (lq : 2<q) (bp : 0<B) (upper : (p*q)/(B+1)+B<p*q)
    (hp : (p*q)/(B+1)<p) (hq : (p*q)/(B+1)<q) :
    ∃ k x y : ℕ, 0<k ∧ 0<y ∧ y≤B ∧ x≤(p*q)/(B+1) ∧ x.Coprime y ∧
      y^2=x^2+k*(p*q) ∧ 1<(y-x).gcd (p*q) ∧ (y-x).gcd (p*q)<p*q ∧
      (y-x).gcd (p*q)∣p*q := by
  letI : NeZero (p*q) := ⟨(Nat.mul_pos pp.pos pq.pos).ne'⟩
  have large (l : ℕ) (pr : l.Prime) (dvd : l∣p*q) : (p*q)/(B+1)<l := by
    rcases pr.dvd_mul.mp dvd with dv|dv
    · rwa [(Nat.prime_dvd_prime_iff_eq pr pp).mp dv]
    · rwa [(Nat.prime_dvd_prime_iff_eq pr pq).mp dv]
  have short : ((p*q)/(B+1))^2<p*q := by rw [pow_two]; exact Nat.mul_lt_mul_of_lt_of_lt hp hq
  obtain ⟨r,rr,pos,neg⟩ := mixed_exists ((Nat.coprime_primes pp pq).mpr ne) lp lq
  obtain ⟨k,y,x,kp,yp,yb,xh,prim,_,_,row,spl⟩ := cover bp upper short large r rr pos neg
  exact ⟨k,x.natAbs,y,kp,yp,yb,xh,prim,row,spl⟩

/-- A self-generated example whose successful multiplier exceeds one. -/
theorem example_3071 :
    3071=37*83 ∧ Nat.Prime 37 ∧ Nat.Prime 83 ∧ 3071/181=16 ∧
    2406%37=1 ∧ 2406%83=82 ∧ (2406 : ZMod 3071)^2=1 ∧
    (9 : ZMod 3071)=2406*157 ∧ 157^2=9^2+8*3071 ∧
    Nat.gcd (157-9) 3071=37 ∧ Nat.gcd (157+9) 3071=83 := by decide +kernel

end PrimeFactors.MixedUnityRectangle
