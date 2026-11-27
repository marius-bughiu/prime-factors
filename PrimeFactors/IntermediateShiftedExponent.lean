import PrimeFactors.IntermediateTotientObstruction

/-! For an exponent dividing a nearby positive shift of the product, every upper intermediate
fraction that beats direct multiples has a prescribed parent and determines the shift of the
factor sum. The converse constructs the actual row of the Euclidean walk. -/
namespace PrimeFactors.IntermediateShiftedExponent

open UpperConvergentDeficit IntermediateTotientObstruction

private theorem advance {i t u v : ℕ} {x y : Row} (vp : 0<v) :
    rowAt (i+1) t u v x y = rowAt i t v (u%v) y (step x y (u/v)) := by
  cases v with
  | zero => omega
  | succ _ => rfl

private theorem select {t u v : ℕ} {x y : Row} (vp : 0<v) (tp : 0<t) (fits : t≤u/v) :
    rowAt 0 t u v x y = some (step x y t) := by
  cases v with
  | zero => omega
  | succ _ => simp [rowAt,tp,fits]

/-- The first two reciprocal denominators are d−1 and d. The next upper block contains
the specified row at its genuine positive index a−1. -/
theorem shifted_row {N E d k a : ℕ} (kp : 0<k) (small : 2*k<E) (dp : 2≤d)
    (shift : N+k=d*E) (ap : 2≤a) (cap : a*k≤E) :
    rowAt 3 (a-1) E N ⟨0,1⟩ ⟨1,0⟩ = some ⟨a,a*d-1⟩ := by
  have ep : 0<E := by omega
  have en : E<N := by
    have twice := Nat.mul_le_mul_right E dp
    omega
  let r := E-k
  have er : r+k=E := Nat.sub_add_cancel (by omega)
  have kr : k<r := by dsimp only [r]; omega
  have dr : d-1+1=d := by omega
  have first : N/E=d-1 ∧ N%E=r := (Nat.div_mod_unique ep).mpr ⟨by
    nlinarith only [shift,er,congrArg (fun z => z*E) dr],by omega⟩
  have rp : 0<r := by omega
  have second : E/r=1 ∧ E%r=k := (Nat.div_mod_unique rp).mpr ⟨by omega,kr⟩
  have ar : a-1+1=a := by omega
  have fits : a-1≤r/k := (Nat.le_div_iff_mul_le kp).mpr (by
    nlinarith only [cap,er,congrArg (fun z => z*k) ar])
  rw [advance (i:=2) (ep.trans en),Nat.mod_eq_of_lt en,Nat.div_eq_of_lt en,
      advance (i:=1) ep,first.1,first.2,advance (i:=0) rp,second.1,second.2,
      select kp (by omega) fits]
  apply congrArg some
  simp only [step,Nat.zero_mul,Nat.add_zero,Nat.zero_add,Nat.one_mul,Nat.mul_one]
  congr 1
  · omega
  · have eq : (d-1)+(a-1)*(1+(d-1))+1=a*d := by
      have add : 1+(d-1)=d := by omega
      rw [add]
      nlinarith only [dr,congrArg (fun z => z*d) ar]
    omega

/-- If D+k divides E and E divides N+k then E/F occurs, for F=N−D and E≤N.
This reverse implication needs no upper bound on the positive shift k. -/
theorem of_sum_divisor {N E F k : ℕ} (ep : 0<E) (en : E≤N) (fp : 0<F) (fn : F<N)
    (kp : 0<k) (shift : E∣N+k) (candidate : (N-F+k)∣E) : Hit N E F := by
  let D := N-F
  let g := D+k
  have nf : F+D=N := by dsimp only [D]; omega
  have Dp : 0<D := Nat.sub_pos_of_lt fn
  have gp : 0<g := by dsimp only [g]; omega
  obtain ⟨d,hd⟩ := shift
  obtain ⟨a,ha⟩ := candidate
  change E=g*a at ha
  have ap : 0<a := by
    apply Nat.pos_of_ne_zero
    intro az
    simp [az] at ha
    omega
  have ds : N+k=d*E := by simpa only [Nat.mul_comm] using hd
  have dp : 2≤d := by
    by_contra! bad
    have h := Nat.mul_le_mul_right E (show d≤1 by omega)
    omega
  have fg : F+g=d*E := by dsimp [g]; omega
  by_cases ao : a=1
  · rw [ao,Nat.mul_one] at ha
    apply reciprocal ep fp fn
    have dvd : E∣F+g := fg ▸ dvd_mul_left E d
    exact (Nat.dvd_add_left (show E∣g from ha ▸ dvd_rfl)).mp dvd
  have two : 2≤a := by omega
  have small : 2*k<E := by
    have hk : k<g := by dsimp only [g]; omega
    have h := Nat.mul_le_mul_left g two
    nlinarith only [h,ha,hk]
  have cap : a*k≤E := by
    have h := Nat.mul_le_mul_left a (show k≤g by dsimp only [g]; omega)
    simpa only [ha,Nat.mul_comm] using h
  have row := shifted_row kp small dp ds two cap
  have big : 2≤a*d := (Nat.le_mul_of_pos_right a (by omega)).trans' two
  have eq : (a*d-1)+1=a*d := by omega
  refine ⟨3,a-1,⟨a,a*d-1⟩,row,by dsimp; omega,?_⟩
  dsimp only
  nlinarith only [congrArg (fun z => E*z) eq,congrArg (fun z => a*z) fg,ha]

/-- On a positive shift no larger than the deficit, a hit beyond direct multiples forces
gcd(E,F)=D+k. The strict lower bound on the gcd precludes every proper divisor of D+k. -/
theorem forced_gcd {N E F k : ℕ} (ep : 0<E) (fn : F<N) (small : k≤N-F)
    (shift : E∣N+k) (hit : Hit N E F) (extra : ¬E∣F) : E.gcd F=N-F+k := by
  have larger := (dichotomy ep fn hit).resolve_left extra
  have left := (Nat.gcd_dvd_left E F).trans shift
  have dvd := Nat.dvd_sub left (Nat.gcd_dvd_right E F)
  rw [show N+k-F=N-F+k by omega] at dvd
  exact (Nat.eq_of_dvd_of_lt_two_mul (by omega) dvd (by omega)).symm

/-- An exact test for all intermediate rows, with arbitrary prime factors permitted in E.
For N=p*q, the second branch tests the single shifted sum p+q−1+k among the divisors of E. -/
theorem positive_iff {N E F k : ℕ} (ep : 0<E) (en : E≤N) (fp : 0<F) (fn : F<N)
    (kp : 0<k) (small : k≤N-F) (shift : E∣N+k) :
    Hit N E F ↔ E∣F ∨ (N-F+k)∣E := by
  constructor
  · intro hit
    by_cases multiple : E∣F
    · exact Or.inl multiple
    · exact Or.inr (forced_gcd ep fn small shift hit multiple ▸ Nat.gcd_dvd_left E F)
  · rintro (dvd|dvd)
    · exact reciprocal ep fp fn dvd
    · exact of_sum_divisor ep en fp fn kp shift dvd

/-- Each individual exponent hits precisely when it and the shifted deficit are
comparable by divisibility. Both quantities divide the same public integer N+k. -/
theorem comparable_iff {N E F k : ℕ} (ep : 0<E) (en : E≤N) (fp : 0<F) (fn : F<N)
    (kp : 0<k) (small : k≤N-F) (shift : E∣N+k) :
    Hit N E F ↔ E∣(N-F+k) ∨ (N-F+k)∣E := by
  have total : E∣F+(N-F+k) := by rwa [show F+(N-F+k)=N+k by omega]
  have eq : E∣F ↔ E∣(N-F+k) :=
    ⟨fun h => (Nat.dvd_add_right h).mp total,fun h => (Nat.dvd_add_left h).mp total⟩
  rw [positive_iff ep en fp fn kp small shift,eq]

/-- Any positive-remainder lower parent of a successful, nonreciprocal row
has numerator one, remainder k and denominator (N+k)/E. -/
theorem forced_parent {N E F k a b c d w : ℕ} (ep : 0<E) (fn : F<N) (small : k≤N-F)
    (shift : E∣N+k) (hit : Hit N E F) (extra : ¬E∣F)
    (det : a*d=b*c+1) (ratio : E*b=a*F) (low : E*d=N*c+w) (wp : 0<w) :
    c=1 ∧ w=k ∧ d=(N+k)/E := by
  have low' : E*d=(F+(N-F))*c+w := by rwa [Nat.add_sub_of_le fn.le]
  obtain ⟨e,f,g⟩ := common_divisor det ratio low'
  rw [forced_gcd ep fn small shift hit extra] at g
  have c_ne : c≠0 := by
    intro cz
    rw [cz,Nat.mul_zero,Nat.zero_add] at det
    have ao := Nat.dvd_one.mp (show a∣1 from ⟨d,det.symm⟩)
    rw [ao,one_mul] at ratio
    exact extra ⟨b,ratio.symm⟩
  have co : c=1 := by
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro high
      have h := Nat.mul_le_mul_right (N-F) high
      omega
    · exact Nat.pos_of_ne_zero c_ne
  simp only [co,one_mul] at g
  have wk : w=k := by omega
  rw [co,mul_one,wk] at low
  exact ⟨co,wk,by rw [←low,Nat.mul_div_cancel_left _ ep]⟩

/-- At nonpositive shifts of magnitude at most D, every hit is a direct multiple. -/
theorem negative_iff {N E F k : ℕ} (ep : 0<E) (fp : 0<F) (fn : F<N)
    (small : k≤N-F) (shift : E∣N-k) : Hit N E F ↔ E∣F := by
  refine ⟨?_,reciprocal ep fp fn⟩
  intro hit
  by_cases equal : k=N-F
  · rwa [show N-k=F by omega] at shift
  by_contra extra
  have larger := (dichotomy ep fn hit).resolve_left extra
  have dvd := Nat.dvd_sub ((Nat.gcd_dvd_left E F).trans shift) (Nat.gcd_dvd_right E F)
  have ub := Nat.le_of_dvd (show 0<N-k-F by omega) dvd
  omega

/-- The upper bound on k in comparability matters, even for the totient of a
product of distinct odd primes. For N=7·11, E=40 and k=43, row 2/3 hits. -/
theorem oversized_shift :
    40∣77+43 ∧ Hit 77 40 60 ∧ ¬(40∣(77-60+43) ∨ (77-60+43)∣40) :=
  ⟨by decide,⟨3,1,⟨2,3⟩,by decide,by decide,by decide⟩,by decide⟩

end PrimeFactors.IntermediateShiftedExponent
