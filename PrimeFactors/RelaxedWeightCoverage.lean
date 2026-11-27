import PrimeFactors.WeightWindowOverlap

/-! Even a proposed smaller divisor P coprime to N has a weight window
after increasing both public rectangle dimensions by one. The construction
uses the coprime integers P² and N, including when N/P is nonintegral. -/
namespace PrimeFactors.RelaxedWeightCoverage

/-- The signed numerator of the lifted rational coordinates is <P(H+1). -/
private theorem scaled_cutoff {N P B z : ℕ} (pp : 0<P)
    (bound : z≤(P^2*N)/(P*(B+1)+1)) : z<P*(N/(B+1)+1) := by
  have h := (Nat.le_div_iff_mul_le (by omega : 0<P*(B+1)+1)).mp bound
  have cancel : z*(B+1)≤P*N := by
    apply Nat.le_of_mul_le_mul_left (c:=P) _ pp
    nlinarith only [h,Nat.zero_le z]
  have nr := Nat.lt_mul_div_succ N (by omega : 0<B+1)
  have bigger := Nat.mul_lt_mul_of_pos_left nr pp
  apply Nat.lt_of_mul_lt_mul_right (a:=B+1)
  nlinarith only [cancel,bigger]

/-- At the candidate P, write Q=N/P. Scaled weights a,b give midpoint
(aP+bQ)/2 in (0,B+1] and gap |aP−bQ|/2 < floor(N/(B+1))+1. The statement
clears the real denominator 2P. Its hypotheses do not include P dividing N. -/
theorem relaxed {N P B : ℕ} (np : 0<N) (pp : 0<P) (po : Odd P) (no : Odd N)
    (cop : P.Coprime N) :
    ∃ a b : ℤ, Even (a-b) ∧
      |a*(P:ℤ)^2-b*N|<2*(P:ℤ)*(N/(B+1)+1:ℕ) ∧
      0<a*(P:ℤ)^2+b*N ∧ a*(P:ℤ)^2+b*N≤2*(P:ℤ)*(B+1) := by
  have cp := cop.pow_left 2
  let e := ZMod.chineseRemainder cp
  let r := e.symm (1,-1)
  have re : e r=(1,-1) := e.apply_symm_apply _
  obtain ⟨y,x,yp,yb,xb,eq⟩ := RectangularRootWindows.rectangle
    (Nat.mul_pos (Nat.pow_pos pp) np) (Nat.mul_pos pp (by omega : 0<B+1)) r
  have lift := congrArg e eq
  rw [map_intCast,map_mul,map_natCast,re] at lift
  have localP : (x:ZMod (P^2))=y := by simpa using congrArg Prod.fst lift
  have localN : (x:ZMod N)= -y := by simpa using congrArg Prod.snd lift
  have pl : ((P^2:ℕ):ℤ)∣(y:ℤ)-x := by
    rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [localP,sub_self]
  have nr : (N:ℤ)∣(y:ℤ)+x := by
    rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [localN,add_neg_cancel]
  obtain ⟨a,ha⟩ := pl
  obtain ⟨b,hb⟩ := nr
  push_cast at ha
  have gap : a*(P:ℤ)^2-b*N= -2*x := by linear_combination hb-ha
  have mid : a*(P:ℤ)^2+b*N=2*y := by linear_combination -ha-hb
  have pr : Even (a-b) := by
    obtain ⟨i,pi⟩ := po
    obtain ⟨j,nj⟩ := no
    rw [pi,nj] at mid
    push_cast at mid
    refine ⟨(y:ℤ)-b-a*(2*(i:ℤ)^2+2*i)-b*j,?_⟩
    linear_combination mid
  have hsmall : |x|<(P:ℤ)*(N/(B+1)+1:ℕ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast scaled_cutoff pp xb
  have upper : (y:ℤ)≤(P:ℤ)*(B+1) := by exact_mod_cast yb
  have low : 0<(y:ℤ) := by exact_mod_cast yp
  refine ⟨a,b,pr,?_,?_,?_⟩
  · rw [gap,abs_mul,show |(-2:ℤ)|=2 by decide]
    linarith only [hsmall]
  · rw [mid]; positivity
  · rw [mid]
    linarith

private theorem positive_weights {a b m n T : ℤ} (mp : 0<m) (mn : m≤n)
    (short : T≤m) (par : Even (a-b)) (sum : 0<a*m+b*n) (gap : |a*m-b*n|<2*T) :
    0<a ∧ 0<b := by
  obtain ⟨i,hi⟩ := par
  have lo := (abs_lt.mp gap).1
  have hi' := (abs_lt.mp gap).2
  constructor
  · by_contra! an
    have bp : 0<b := by
      by_contra! bn
      linarith [mul_nonpos_of_nonpos_of_nonneg an mp.le,
        mul_nonpos_of_nonpos_of_nonneg bn (mp.le.trans mn)]
    have sep : 2≤b-a := by omega
    have z := mul_le_mul_of_nonneg_right sep mp.le
    have w := mul_le_mul_of_nonneg_left mn bp.le
    nlinarith only [z,w,lo,short]
  · by_contra! bn
    have ap : 0<a := by
      by_contra! an
      linarith [mul_nonpos_of_nonpos_of_nonneg an mp.le,
        mul_nonpos_of_nonpos_of_nonneg bn (mp.le.trans mn)]
    have sep : 2≤a-b := by omega
    have z := mul_le_mul_of_nonneg_right sep mp.le
    have w := mul_le_mul_of_nonpos_left mn bn
    nlinarith only [z,w,hi',short]

/-- Every odd coprime candidate P in the smaller-factor range has positive
matching-parity weights in the rectangle enlarged by one on each axis. -/
theorem positive_relaxed {N P B : ℕ} (np : 0<N) (pp : 0<P) (po : Odd P) (no : Odd N)
    (cop : P.Coprime N) (order : P^2≤N) (large : N/(B+1)+1≤P) :
    ∃ a b : ℤ, 0<a ∧ 0<b ∧ Even (a-b) ∧
      |a*(P:ℤ)^2-b*N|<2*(P:ℤ)*(N/(B+1)+1:ℕ) ∧
      0<a*(P:ℤ)^2+b*N ∧ a*(P:ℤ)^2+b*N≤2*(P:ℤ)*(B+1) := by
  obtain ⟨a,b,par,gap,mid,bound⟩ := relaxed np pp po no cop
  have mpos : 0<(P:ℤ)^2 := by exact_mod_cast Nat.pow_pos pp
  have sm : P*(N/(B+1)+1)≤P^2 := by rw [pow_two]; exact Nat.mul_le_mul_left P large
  have tighter : |a*(P:ℤ)^2-b*N|<2*((P:ℤ)*(N/(B+1)+1:ℕ)) := by rwa [←mul_assoc]
  have pos := positive_weights mpos (by exact_mod_cast order) (by exact_mod_cast sm) par mid tighter
  exact ⟨a,b,pos.1,pos.2,par,gap,mid,bound⟩

/-- A positive matching-parity pair is a positive integer multiple of
one of the two canonical coprime weight pairs used by the row generator. -/
theorem normalize {a b : ℕ} (ap : 0<a) (bp : 0<b) (par : a%2=b%2) :
    ∃ g t c d : ℕ, 0<g ∧ 0<c ∧ 0<d ∧ c.Coprime d ∧
      a=g*(t*c) ∧ b=g*(t*d) ∧
      ((t=1 ∧ Odd c ∧ Odd d) ∨ (t=2 ∧ c%2≠d%2)) := by
  let G := a.gcd b
  let c := a/G
  let d := b/G
  have gp : 0<G := Nat.gcd_pos_of_pos_left b ap
  have ac : a=G*c := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have bd : b=G*d := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  have cp : c.Coprime d := Nat.coprime_div_gcd_div_gcd gp
  have posc : 0<c := Nat.pos_of_ne_zero (fun h => by rw [ac,h,mul_zero] at ap; omega)
  have posd : 0<d := Nat.pos_of_ne_zero (fun h => by rw [bd,h,mul_zero] at bp; omega)
  by_cases same : c%2=d%2
  · have co : c%2=1 := by
      by_cases even : c%2=0
      · have tw := Nat.dvd_gcd (Nat.dvd_iff_mod_eq_zero.mpr even)
          (Nat.dvd_iff_mod_eq_zero.mpr (same.symm.trans even))
        rw [cp.gcd_eq_one] at tw
        omega
      · omega
    exact ⟨G,1,c,d,gp,posc,posd,cp,by simpa using ac,by simpa using bd,
      Or.inl ⟨rfl,Nat.odd_iff.mpr co,Nat.odd_iff.mpr (same.symm.trans co)⟩⟩
  · have gEven : 2∣G := by
      by_cases even : G%2=0
      · exact Nat.dvd_iff_mod_eq_zero.mpr even
      · have go : G%2=1 := by omega
        rw [ac,bd,Nat.mul_mod,Nat.mul_mod G d,go,one_mul,one_mul,Nat.mod_mod,Nat.mod_mod] at par
        exact (same par).elim
    obtain ⟨g,eq⟩ := gEven
    exact ⟨g,2,c,d,by omega,posc,posd,cp,by rw [ac,eq]; ring,by rw [bd,eq]; ring,
      Or.inr ⟨rfl,same⟩⟩

/-- The positive rational window for every odd coprime candidate can be
realized in the same two reduced parity families as the factoring search. -/
theorem canonical {N P B : ℕ} (np : 0<N) (pp : 0<P) (po : Odd P) (no : Odd N)
    (cop : P.Coprime N) (order : P^2≤N) (large : N/(B+1)+1≤P) :
    ∃ c d t : ℕ, 0<c ∧ 0<d ∧ c.Coprime d ∧
      ((t=1 ∧ Odd c ∧ Odd d) ∨ (t=2 ∧ c%2≠d%2)) ∧
      |((t*c:ℕ):ℤ)*(P:ℤ)^2-(t*d:ℕ)*N|<2*(P:ℤ)*(N/(B+1)+1:ℕ) ∧
      ((t*c:ℕ):ℤ)*(P:ℤ)^2+(t*d:ℕ)*N≤2*(P:ℤ)*(B+1) := by
  obtain ⟨a,b,ap,bp,par,gap,_,mid⟩ := positive_relaxed np pp po no cop order large
  lift a to ℕ using ap.le
  lift b to ℕ using bp.le
  have same : a%2=b%2 := by obtain ⟨i,h⟩ := par; omega
  obtain ⟨g,t,c,d,gp,cp,dp,cd,ac,bd,types⟩ :=
    normalize (by exact_mod_cast ap : 0<a) (by exact_mod_cast bp : 0<b) same
  let X : ℤ := ((t*c:ℕ):ℤ)*(P:ℤ)^2-(t*d:ℕ)*N
  let Y : ℤ := ((t*c:ℕ):ℤ)*(P:ℤ)^2+(t*d:ℕ)*N
  have eg : (a:ℤ)*(P:ℤ)^2-b*N=(g:ℤ)*X := by rw [ac,bd]; dsimp [X]; push_cast; ring
  have ey : (a:ℤ)*(P:ℤ)^2+b*N=(g:ℤ)*Y := by rw [ac,bd]; dsimp [Y]; push_cast; ring
  have pos : 1≤(g:ℤ) := by exact_mod_cast gp
  have yn : 0≤Y := by dsimp [Y]; positivity
  have xle := mul_le_mul_of_nonneg_right pos (abs_nonneg X)
  have yle := mul_le_mul_of_nonneg_right pos yn
  rw [eg,abs_mul,abs_of_nonneg (by positivity : 0≤(g:ℤ))] at gap
  rw [ey] at mid
  rw [one_mul] at xle yle
  exact ⟨c,d,t,cp,dp,cd,types,xle.trans_lt gap,yle.trans mid⟩

/-- On this 8-bit-prime example the exact bounds do exclude the prime
candidate 167. Enlarging H from 33 to 34 admits weights (1,1). -/
theorem exact_miss :
    38957=163*239 ∧ Nat.Prime 163 ∧ Nat.Prime 239 ∧ Nat.Prime 167 ∧
    38957/(1145+1)=33 ∧
    ¬∃ a b : ℤ, 0<a ∧ 0<b ∧ Even (a-b) ∧
      |a*167^2-b*38957|≤2*167*33 ∧ a*167^2+b*38957≤2*167*1145 := by
  refine ⟨by decide,by norm_num,by norm_num,by norm_num,by decide,?_⟩
  rintro ⟨a,b,ap,bp,par,gap,mid⟩
  have bounds : a<14 ∧ b<10 := by norm_num at mid; constructor <;> linarith only [mid,ap,bp]
  lift a to ℕ using ap.le
  lift b to ℕ using bp.le
  have exclude : ∀ u : Fin 14, ∀ v : Fin 10, ¬(0<(u.val:ℤ) ∧ 0<(v.val:ℤ) ∧
      Even ((u.val:ℤ)-v.val) ∧ |(u.val:ℤ)*167^2-v.val*38957|≤2*167*33 ∧
      (u.val:ℤ)*167^2+v.val*38957≤2*167*1145) := by decide +kernel
  exact exclude ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨ap,bp,par,gap,mid⟩

theorem enlarged_hit :
    |(167:ℤ)^2-38957| < 2*167*34 ∧ (167:ℤ)^2+38957≤2*167*1146 := by decide

end PrimeFactors.RelaxedWeightCoverage
