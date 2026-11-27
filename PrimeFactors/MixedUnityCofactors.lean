import PrimeFactors.MixedUnityRectangle
import PrimeFactors.RectangularMultiplierCount

/-! Arithmetic filters on the multiplier of a primitive difference of squares
inside a narrow rectangle. All y±x factors discussed below lie below pq. -/
namespace PrimeFactors.MixedUnityCofactors

/-- The two bounded linear factors, in either orientation. -/
def Located (t p q a b x y : ℕ) : Prop :=
  (t*(p*a)=y-x ∧ t*(q*b)=y+x) ∨ (t*(q*b)=y-x ∧ t*(p*a)=y+x)

private theorem place {p q A B : ℕ} (pp : p.Prime) (pq : q.Prime) (ne : p≠q)
    (ap : 0<A) (bp : 0<B) (al : A<p*q) (bl : B<p*q) (dv : p*q∣A*B) :
    (p∣A ∧ q∣B) ∨ (q∣A ∧ p∣B) := by
  have cop := (Nat.coprime_primes pp pq).mpr ne
  have ps := pp.dvd_mul.mp ((dvd_mul_right p q).trans dv)
  have qs := pq.dvd_mul.mp ((dvd_mul_left q p).trans dv)
  rcases ps with pa|pb <;> rcases qs with qa|qb
  · exact (Nat.not_dvd_of_pos_of_lt ap al (cop.mul_dvd_of_dvd_of_dvd pa qa)).elim
  · exact Or.inl ⟨pa,qb⟩
  · exact Or.inr ⟨qa,pb⟩
  · exact (Nat.not_dvd_of_pos_of_lt bp bl (cop.mul_dvd_of_dvd_of_dvd pb qb)).elim

private theorem odd_mul_mod {p : ℕ} (po : Odd p) (a : ℕ) : (p*a)%2=a%2 := by
  rw [Nat.mul_mod,Nat.odd_iff.mp po,one_mul,Nat.mod_mod]

private theorem cofactor_coprime {p q t a b x y : ℕ} (xy : x≤y)
    (prim : x.Coprime y) (whereAt : Located t p q a b x y)
    (par : a%2=1 ∨ b%2=1) : a.Coprime b := by
  apply Nat.coprime_of_dvd
  intro l prime la lb
  have two : l≠2 := by
    rintro rfl
    rw [Nat.dvd_iff_mod_eq_zero] at la lb
    omega
  have lm : ∀ z, l∣2*z → l∣z := fun z h =>
    (prime.dvd_mul.mp h).resolve_left (fun h => two ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp h))
  have a' : l∣t*(p*a) := (la.trans (dvd_mul_left a p)).trans (dvd_mul_left ..)
  have b' : l∣t*(q*b) := (lb.trans (dvd_mul_left b q)).trans (dvd_mul_left ..)
  have both : l∣y-x ∧ l∣y+x := by
    rcases whereAt with ⟨u,v⟩|⟨u,v⟩
    · exact ⟨u ▸ a',v ▸ b'⟩
    · exact ⟨u ▸ b',v ▸ a'⟩
  have ly := lm y (show l∣2*y from (show y-x+(y+x)=2*y by omega) ▸ Nat.dvd_add both.1 both.2)
  have lx := lm x (show l∣2*x from (show y+x-(y-x)=2*x by omega) ▸ Nat.dvd_sub both.2 both.1)
  have bad := Nat.dvd_gcd lx ly
  rw [prim.gcd_eq_one,Nat.dvd_one] at bad
  exact prime.ne_one bad

/-- Every primitive positive row has an odd multiplier factored into two
odd coprime cofactors, or four times a product of opposite-parity coprime
cofactors. Each cofactor attaches to one of the two distinct primes. -/
theorem decompose {p q k x y : ℕ} (pp : p.Prime) (pq : q.Prime) (ne : p≠q)
    (po : Odd p) (qo : Odd q) (kp : 0<k) (upper : y+x<p*q) (prim : x.Coprime y)
    (row : y^2=x^2+k*(p*q)) :
    ∃ a b t : ℕ, 0<a ∧ 0<b ∧ Located t p q a b x y ∧ a.Coprime b ∧
      ((t=1 ∧ k=a*b ∧ x%2≠y%2 ∧ Odd a ∧ Odd b) ∨
       (t=2 ∧ k=4*(a*b) ∧ Odd x ∧ Odd y ∧ a%2≠b%2)) := by
  have np := Nat.mul_pos pp.pos pq.pos
  have kpN := Nat.mul_pos kp np
  have xy : x<y := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  have eq : (y-x)*(y+x)=k*(p*q) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le xy.le
    simp only [Nat.add_sub_cancel_left]
    nlinarith only [row]
  have posA : 0<y-x := by omega
  have posB : 0<y+x := by omega
  obtain ⟨c,d,w⟩ : ∃ c d, Located 1 p q c d x y := by
    have h := place pp pq ne posA posB (by omega) upper ⟨k,eq.trans (Nat.mul_comm ..)⟩
    rcases h with ⟨⟨c,hc⟩,⟨d,hd⟩⟩|⟨⟨d,hd⟩,⟨c,hc⟩⟩
    · exact ⟨c,d,Or.inl ⟨by simpa using hc.symm,by simpa using hd.symm⟩⟩
    · exact ⟨c,d,Or.inr ⟨by simpa using hd.symm,by simpa using hc.symm⟩⟩
  have loc : (p*c=y-x ∧ q*d=y+x) ∨ (q*d=y-x ∧ p*c=y+x) := by simpa [Located] using w
  have mul : k=c*d := by
    apply Nat.mul_right_cancel np
    rw [←eq]
    rcases loc with ⟨u,v⟩|⟨u,v⟩ <;> rw [←u,←v] <;> ring
  have cd : 0<c ∧ 0<d := by
    exact ⟨Nat.pos_of_ne_zero (fun h => by simp [mul,h] at kp),
      Nat.pos_of_ne_zero (fun h => by simp [mul,h] at kp)⟩
  have sum : p*c+q*d=2*y := by rcases loc with ⟨u,v⟩|⟨u,v⟩ <;> omega
  have parity : (p*c)%2=(y+x)%2 ∧ (q*d)%2=(y+x)%2 := by
    rcases loc with ⟨u,v⟩|⟨u,v⟩ <;> omega
  rw [odd_mul_mod po,odd_mul_mod qo] at parity
  by_cases opposite : x%2≠y%2
  · have oddC : c%2=1 := by omega
    have oddD : d%2=1 := by omega
    exact ⟨c,d,1,cd.1,cd.2,w,cofactor_coprime xy.le prim w (Or.inl oddC),
      Or.inl ⟨rfl,mul,opposite,Nat.odd_iff.mpr oddC,Nat.odd_iff.mpr oddD⟩⟩
  · have same : x%2=y%2 := not_not.mp opposite
    have yodd : y%2=1 := by
      by_cases even : y%2=0
      · have two : 2∣x.gcd y := Nat.dvd_gcd (Nat.dvd_iff_mod_eq_zero.mpr (same.trans even))
          (Nat.dvd_iff_mod_eq_zero.mpr even)
        rw [prim.gcd_eq_one] at two
        omega
      · omega
    have xodd : x%2=1 := by omega
    obtain ⟨a,ha⟩ : 2∣c := by omega
    obtain ⟨b,hb⟩ : 2∣d := by omega
    have at2 : Located 2 p q a b x y := by
      simpa only [Located,one_mul,ha,hb,mul_left_comm p 2,mul_left_comm q 2] using w
    have halves : p*a+q*b=y := by
      rw [ha,hb] at sum
      nlinarith only [sum]
    have bits := congrArg (·%2) halves
    change (p*a+q*b)%2=y%2 at bits
    rw [Nat.add_mod,odd_mul_mod po,odd_mul_mod qo,yodd] at bits
    have different : a%2≠b%2 := by omega
    have cop := cofactor_coprime xy.le prim at2 (show a%2=1 ∨ b%2=1 by omega)
    exact ⟨a,b,2,by omega,by omega,at2,cop,Or.inr ⟨rfl,by rw [mul,ha,hb]; ring,
      Nat.odd_iff.mpr xodd,Nat.odd_iff.mpr yodd,different⟩⟩

private theorem ratio_one {p q a b t U V A B c d : ℕ}
    (scale : 0<t*p) (rates : q*d≤p*c) (upper : t*(p*a)≤U) (lower : V≤t*(q*b))
    (geometry : U*A≤V*B) : a*d*A≤b*c*B := by
  apply Nat.le_of_mul_le_mul_left (c:=t*p) _ scale
  calc
    (t*p)*(a*d*A) = (t*(p*a)*A)*d := by ring
    _ ≤ (U*A)*d := by gcongr
    _ ≤ (V*B)*d := by gcongr
    _ ≤ (t*(q*b)*B)*d := by gcongr
    _ = (t*b*B)*(q*d) := by ring
    _ ≤ (t*b*B)*(p*c) := by gcongr
    _ = (t*p)*(b*c*B) := by ring

/-- Integer version of max(a,b)/min(a,b) ≤ (c/d)·(S+H)/(S−H).
The input prime ratio need only satisfy q/p≤c/d. This bound then tests a
possible pair using only public bounds and the small cofactor candidates. -/
theorem ratio {p q a b t x y S H c d : ℕ} (pp : 0<p) (pq : p≤q) (tp : 0<t)
    (rates : q*d≤p*c) (xh : x≤H) (hs : H<S) (sy : S≤y)
    (loc : Located t p q a b x y) :
    max a b*d*(S-H) ≤ min a b*c*(S+H) := by
  have yx : x≤y := by omega
  have geom : (y+x)*(S-H)≤(y-x)*(S+H) := by
    have g := Nat.mul_le_mul xh sy
    have bound : (S-H)+H=S := by omega
    have low : (y-x)+x=y := by omega
    nlinarith only [g,bound,low,congrArg (·*y) bound,congrArg (·*x) bound,
      congrArg (·*S) low,congrArg (·*H) low]
  have ls : y-x≤t*(p*a) ∧ t*(p*a)≤y+x ∧ y-x≤t*(q*b) ∧ t*(q*b)≤y+x := by
    rcases loc with ⟨l,r⟩|⟨l,r⟩ <;> omega
  have fwd := ratio_one (Nat.mul_pos tp pp) rates ls.2.1 ls.2.2.1 geom
  have rev : p*d≤q*c := (Nat.mul_le_mul_right d pq).trans (rates.trans (Nat.mul_le_mul_right c pq))
  have back := ratio_one (Nat.mul_pos tp (pp.trans_le pq)) rev ls.2.2.2 ls.1 geom
  rcases le_total a b with ab|ba
  · simpa only [max_eq_right ab,min_eq_left ab] using back
  · simpa only [max_eq_left ba,min_eq_right ba] using fwd

/-- Product-only constraint on a row multiplier. List each candidate
cofactor pair just once, with the smaller cofactor first. -/
def Admissible (k c d S H : ℕ) : Prop :=
  ∃ a b : ℕ, 0<a ∧ a≤b ∧ a.Coprime b ∧ b*d*(S-H)≤a*c*(S+H) ∧
    ((k=a*b ∧ Odd a ∧ Odd b) ∨ (k=4*(a*b) ∧ a%2≠b%2))

/-- Discarding a multiplier failing Admissible preserves every primitive
solution in the given rectangle for the allowed factor range. -/
theorem necessary {p q k x y S H c d : ℕ} (pp : p.Prime) (pq : q.Prime)
    (ne : p≠q) (ord : p≤q) (po : Odd p) (qo : Odd q)
    (kp : 0<k) (upper : y+x<p*q) (prim : x.Coprime y) (row : y^2=x^2+k*(p*q))
    (rates : q*d≤p*c) (xh : x≤H) (hs : H<S) (sy : S≤y) :
    Admissible k c d S H := by
  obtain ⟨a,b,t,ap,bp,loc,cop,par⟩ := decompose pp pq ne po qo kp upper prim row
  have tp : 0<t := by rcases par with ⟨h,_⟩|⟨h,_⟩ <;> omega
  have geo := ratio pp.pos ord tp rates xh hs sy loc
  have pat : (k=a*b ∧ Odd a ∧ Odd b) ∨ (k=4*(a*b) ∧ a%2≠b%2) := by
    rcases par with ⟨_,h,_,pa,pb⟩|⟨_,h,_,_,h2⟩
    · exact Or.inl ⟨h,pa,pb⟩
    · exact Or.inr ⟨h,h2⟩
  rcases le_total a b with ab|ba
  · exact ⟨a,b,ap,ab,cop,by simpa [min_eq_left ab,max_eq_right ab] using geo,pat⟩
  · refine ⟨b,a,bp,ba,cop.symm,by simpa [min_eq_right ba,max_eq_left ba] using geo,?_⟩
    rw [Nat.mul_comm b a]
    rcases pat with ⟨h,ao,bo⟩|⟨h,unequal⟩
    · exact Or.inl ⟨h,bo,ao⟩
    · exact Or.inr ⟨h,Ne.symm unequal⟩

/-- Round the rational geometry bound up to a public integer ratio. The
finite union of weight products therefore contains every admitted k≤K. -/
theorem mem_allowed {k K c d S H scale excess : ℕ} (admit : Admissible k c d S H)
    (cap : k≤K) (sc : 0<scale) (den : 0<d*(S-H))
    (rounded : scale*(c*(S+H))≤(scale+excess)*(d*(S-H))) :
    k ∈ RectangularMultiplierCount.allowed K scale excess := by
  obtain ⟨a,b,ap,ab,_,geo,pat⟩ := admit
  have ratio : scale*b≤(scale+excess)*a := by
    apply Nat.le_of_mul_le_mul_left (c:=d*(S-H)) _ den
    calc
      d*(S-H)*(scale*b) = scale*(b*d*(S-H)) := by ring
      _ ≤ scale*(a*c*(S+H)) := Nat.mul_le_mul_left scale geo
      _ = a*(scale*(c*(S+H))) := by ring
      _ ≤ a*((scale+excess)*(d*(S-H))) := Nat.mul_le_mul_left a rounded
      _ = d*(S-H)*((scale+excess)*a) := by ring
  rcases pat with ⟨rfl,ao,bo⟩|⟨rfl,diff⟩
  · exact RectangularMultiplierCount.odd_mem sc ab (Nat.odd_iff.mp ao) (Nat.odd_iff.mp bo) cap ratio
  · simpa only [Nat.mul_assoc] using RectangularMultiplierCount.even_mem sc ap ab diff
      (by simpa only [Nat.mul_assoc] using cap) ratio

/-- From the public upper bound U for both primes and rectangle x≤H,y≤Y,
the scanner chooses S=floor(sqrt N), uses q/p≤U²/N, and needs only the
distinct eligible multipliers ≤floor(Y²/N). All the parameters of that
finite list can be evaluated without either factor. -/
theorem public_rows {p q k x y H Y U scale excess : ℕ} (pp : p.Prime) (pq : q.Prime)
    (ne : p≠q) (ord : p≤q) (po : Odd p) (qo : Odd q) (qu : q≤U) (kp : 0<k)
    (upper : Y+H<p*q) (xh : x≤H) (yb : y≤Y) (short : H<(p*q).sqrt)
    (prim : x.Coprime y) (row : y^2=x^2+k*(p*q)) (sc : 0<scale)
    (rounded : scale*(U^2*((p*q).sqrt+H))≤(scale+excess)*((p*q)*((p*q).sqrt-H))) :
    k ∈ RectangularMultiplierCount.allowed (Y^2/(p*q)) scale excess := by
  have np := Nat.mul_pos pp.pos pq.pos
  have rates : q*(p*q)≤p*U^2 := by
    calc q*(p*q) = p*q^2 := by ring
         _ ≤ p*U^2 := Nat.mul_le_mul_left p (Nat.pow_le_pow_left qu 2)
  have sy : (p*q).sqrt≤y := by
    have kn := Nat.le_mul_of_pos_left (p*q) kp
    have low : p*q≤y^2 := by omega
    exact (Nat.sqrt_le_sqrt low).trans_eq (Nat.sqrt_eq' y)
  have ad := necessary pp pq ne ord po qo kp (by omega) prim row rates xh short sy
  have cap : k≤Y^2/(p*q) := (Nat.le_div_iff_mul_le np).mpr
    ((show k*(p*q)≤y^2 by omega).trans (Nat.pow_le_pow_left yb 2))
  exact mem_allowed ad cap sc (Nat.mul_pos np (by omega)) rounded

/-- Every product in the stated balanced range has a splitting row in the
publicly generated finite multiplier set. Its construction remains a search
through that set and the denominator interval on each retained row. -/
theorem searched_split {p q Y U scale excess : ℕ} (pp : p.Prime) (pq : q.Prime)
    (lt : p<q) (lp : 2<p) (qu : q≤U) (yp : 0<Y)
    (upper : Y+(p*q)/(Y+1)<p*q) (primeBound : (p*q)/(Y+1)<p)
    (short : (p*q)/(Y+1)<(p*q).sqrt) (sc : 0<scale)
    (rounded : scale*(U^2*((p*q).sqrt+(p*q)/(Y+1)))≤
      (scale+excess)*((p*q)*((p*q).sqrt-(p*q)/(Y+1)))) :
    ∃ k ∈ RectangularMultiplierCount.allowed (Y^2/(p*q)) scale excess,
      ∃ x y : ℕ, 0<k ∧ 0<y ∧ y≤Y ∧ x≤(p*q)/(Y+1) ∧ x.Coprime y ∧
        y^2=x^2+k*(p*q) ∧ 1<(y-x).gcd (p*q) ∧ (y-x).gcd (p*q)<p*q ∧
        (y-x).gcd (p*q)∣p*q := by
  obtain ⟨k,x,y,kp,yp',yb,xh,prim,row,g⟩ := MixedUnityRectangle.semiprime
    pp pq lt.ne lp (lp.trans lt) yp (by omega) primeBound (primeBound.trans lt)
  have mem := public_rows pp pq lt.ne lt.le (pp.odd_of_ne_two (by omega))
    (pq.odd_of_ne_two (by omega)) qu kp upper xh yb short prim row sc rounded
  exact ⟨k,mem,x,y,kp,yp',yb,xh,prim,row,g⟩

/-- Both parity cases occur on small products. -/
theorem examples :
    Nat.Prime 37 ∧ Nat.Prime 61 ∧ Nat.Prime 83 ∧
    184^2=1^2+15*(37*61) ∧ Located 1 37 61 5 3 1 184 ∧
    157^2=9^2+8*(37*83) ∧ Located 2 37 83 2 1 9 157 := by
  unfold Located
  decide +kernel

/-- Passing the multiplier gate does not promise a point. At N=3071 the
eligible first row misses the complete x≤16, y≤180 rectangle. -/
theorem first_admissible_but_empty : Admissible 1 83 37 55 16 ∧
    ∀ x : Fin 17, ∀ y : Fin 181, y.val^2≠x.val^2+3071 := by
  constructor
  · refine ⟨1,1,by decide,by decide,by decide,by decide,Or.inl ?_⟩
    decide
  · decide +kernel

end PrimeFactors.MixedUnityCofactors
