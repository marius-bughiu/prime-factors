import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PrimeFactors.DedekindLaneRanking

/-- The rational part of classical Dedekind reciprocity, normalized by 12. -/
noncomputable def mainTerm (r n : ℚ) := n/r + r/n + 1/(r*n) - 3

/-- Euclidean evaluation of 12s(a,n) for coprime positive inputs. At a zero
remainder we set the value to zero, which includes the modulus-one base case. -/
noncomputable def score (a n : ℕ) : ℚ :=
  if _hn : n=0 then 0 else
    if a%n=0 then 0 else mainTerm (a%n) n - score n (a%n)
termination_by n
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hn)

private theorem caps {r n : ℚ} (r1 : 1≤r) (rn : r≤n) :
    -1 ≤ mainTerm r n ∧ mainTerm r n ≤ n-r := by
  have pr : 0<r := by linarith
  have pn : 0<n := by linarith
  have h₁ : n/r ≤ n-r+1 := (div_le_iff₀ pr).mpr (by
    nlinarith [mul_nonneg (sub_nonneg.mpr r1) (sub_nonneg.mpr rn)])
  have h₂ : r/n ≤ 1 := (div_le_iff₀ pn).mpr (by linarith)
  have h₃ : 1/(r*n) ≤ 1 := (div_le_iff₀ (mul_pos pr pn)).mpr (by
    nlinarith [mul_nonneg (sub_nonneg.mpr r1) pn.le])
  unfold mainTerm
  constructor
  · apply (mul_le_mul_iff_of_pos_right (mul_pos pr pn)).mp
    field_simp
    nlinarith [sq_nonneg (n-r)]
  · linarith

theorem abs_score (a n : ℕ) (hn : 0<n) : |score a n| ≤ (n:ℚ)-1 := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rw [score, dif_neg hn.ne']
    split
    · simp only [abs_zero]
      have : (1:ℚ)≤n := by exact_mod_cast hn
      linarith
    · rename_i h
      have hr := Nat.pos_of_ne_zero h
      have small := Nat.mod_lt a hn
      have c := caps (r := ((a%n:ℕ):ℚ)) (n := (n:ℚ)) (by exact_mod_cast hr)
        (by exact_mod_cast small.le)
      have hprev := abs_le.mp (ih _ small n hr)
      have range : (a%n:ℕ)+1≤n := small
      have cast : ((a%n:ℕ):ℚ)+1≤n := by exact_mod_cast range
      exact abs_le.mpr ⟨by linarith [c.1,hprev.2],by linarith [c.2,hprev.1]⟩

private theorem at_small {a n : ℕ} (ha : 0<a) (an : a<n) :
    score a n = mainTerm a n - score n a := by
  rw [score, dif_neg (ha.trans an).ne', Nat.mod_eq_of_lt an, if_neg ha.ne']

theorem positive {a n : ℕ} (ha : 0<a) (wide : a*(a+2)≤n) : 0<score a n := by
  have an : a<n := by nlinarith [Nat.mul_pos ha ha]
  have ar : 0<(a:ℚ) := by exact_mod_cast ha
  have nr : 0<(n:ℚ) := by exact_mod_cast ha.trans an
  have lead : (a:ℚ)+2≤n/a := (le_div_iff₀ ar).mpr (by
    rw [mul_comm]
    exact_mod_cast wide)
  have correction := (abs_le.mp (abs_score n a ha)).2
  rw [at_small ha an]
  unfold mainTerm
  linarith [show (0:ℚ)<(a:ℚ)/n by positivity,show (0:ℚ)≤1/((a:ℚ)*n) by positivity]

/-- Compare two exact scores using the numerator gap and the product size. -/
theorem ranking {a b B n : ℕ} (ha : 0<a) (lt : a<b) (top : b≤B) (room : B<n)
    (gap : 2*B^3 ≤ (b-a)*n) : score b n < score a n := by
  have hb := ha.trans lt
  have an := lt.trans_le top |>.trans room
  have bn := top.trans_lt room
  have ar : 0<(a:ℚ) := by exact_mod_cast ha
  have br : 0<(b:ℚ) := by exact_mod_cast hb
  have nr : 0<(n:ℚ) := by exact_mod_cast hb.trans bn
  have tr : (b:ℚ)≤B := by exact_mod_cast top
  have lr : (a:ℚ)<b := by exact_mod_cast lt
  have bnr : (b:ℚ)≤n := by exact_mod_cast bn.le
  have Bpos : 0≤(B:ℚ) := by positivity
  have cap : (2:ℚ)*B^3 ≤ (b-a:ℚ)*n := by
    have cast : ((2*B^3:ℕ):ℚ) ≤ (((b-a)*n:ℕ):ℚ) := by exact_mod_cast gap
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_sub lt.le] using cast
  have ab : (a:ℚ)*b ≤ (B:ℚ)*B := mul_le_mul (lr.le.trans tr) tr br.le Bpos
  have main : 2*(B:ℚ) ≤ (n:ℚ)/a-n/b := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos ar br)).mp
    calc 2*(B:ℚ)*(a*b) ≤ 2*B*(B*B) := mul_le_mul_of_nonneg_left ab (by positivity)
      _ = 2*B^3 := by ring
      _ ≤ (b-a)*n := cap
      _ = (n/a-n/b)*(a*b) := by field_simp; ring
  have bdiv : (b:ℚ)/n≤1 := (div_le_iff₀ nr).mpr (by linarith)
  have binv : 1/((b:ℚ)*n)≤1 := (div_le_iff₀ (mul_pos br nr)).mpr (by
    have : (1:ℚ)≤(b:ℚ)*n := by exact_mod_cast Nat.mul_pos hb (hb.trans bn)
    linarith)
  have positive : 0≤(a:ℚ)/n + 1/((a:ℚ)*n) := by positivity
  have ascore := (abs_le.mp (abs_score n a ha)).2
  have bscore := (abs_le.mp (abs_score n b hb)).1
  rw [at_small ha an, at_small hb bn]
  unfold mainTerm
  linarith

set_option exponentiation.threshold 4096 in
theorem every_2048_score {a b n : ℕ} (hn : 2^2047≤n) (ha : 0<a)
    (lt : a<b) (top : b≤2^682) : score b n < score a n := by
  have c : (2:ℕ)*(2^682)^3 = 2^2047 := by decide +kernel
  apply ranking ha lt top ((by decide +kernel : (2:ℕ)^682<2^2047).trans_le hn)
  rw [c]
  calc 2^2047 ≤ n := hn
       _ = 1*n := (one_mul _).symm
       _ ≤ (b-a)*n := Nat.mul_le_mul_right n (by omega)

theorem ranking_odd {a b B n : ℕ} (ha : 0<a) (ab : a<b) (oa : Odd a) (ob : Odd b)
    (cap : b≤B) (bn : B<n) (cube : B^3≤n) : score b n < score a n := by
  obtain ⟨u,hu⟩ := oa
  obtain ⟨v,hv⟩ := ob
  exact ranking ha ab cap bn (Nat.mul_le_mul (show 2≤b-a by omega) cube)

private theorem periodic {a b n : ℕ} (same : a%n=b%n) : score a n=score b n := by
  rw [score.eq_def a n, score.eq_def b n, same]

/-- Reciprocity gives the integral numerator and its inverse congruence in
one induction: if d=n*S(a,n), then a*d≡a²+1 modulo n. -/
theorem numerator (a n : ℕ) (hn : 0<n) (cop : a.Coprime n) :
    ∃ d z : ℤ, (n:ℚ)*score a n=d ∧ (a:ℤ)*d=(a:ℤ)^2+1+z*n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases trivial : a%n=0
    · obtain rfl := cop.symm.eq_one_of_dvd (Nat.dvd_of_mod_eq_zero trivial)
      refine ⟨0,-((a:ℤ)^2+1),?_,by ring⟩
      rw [score.eq_def a 1]
      simp [Nat.mod_one]
    let r := a%n
    have nz : r≠0 := trivial
    have small : r<n := Nat.mod_lt a hn
    have next : n.Coprime r := by
      change n.gcd (a%n)=1
      rw [Nat.gcd_comm,← Nat.gcd_rec n a]
      exact cop.symm
    obtain ⟨v,z,sv,vz⟩ := ih r small n (Nat.pos_of_ne_zero nz) next
    let d : ℤ := r-3*(n:ℤ)-z
    refine ⟨d,(n-3*(r:ℤ)-v)+((a/n:ℕ):ℤ)*(d-a-r),?_,?_⟩
    · have rq : (r:ℚ)≠0 := by exact_mod_cast nz
      have nq : (n:ℚ)≠0 := by exact_mod_cast hn.ne'
      have vq : (n:ℚ)*v=(n:ℚ)^2+1+(z:ℚ)*r := by exact_mod_cast vz
      have e : (r:ℚ)*(n*mainTerm r n)=(n:ℚ)^2+r^2+1-3*r*n := by
        field_simp [mainTerm]
        ring
      rw [score.eq_def a n,dif_neg hn.ne',if_neg trivial]
      change (n:ℚ)*(mainTerm r n-score n r)=(d:ℚ)
      apply mul_left_cancel₀ rq
      calc (r:ℚ)*(n*(mainTerm r n-score n r)) =
              r*(n*mainTerm r n)-n*(r*score n r) := by ring
        _ = r*(d:ℚ) := by rw [e,sv,vq]; simp [d]; ring
    · have decomp : (a:ℤ)=(r:ℤ)+n*((a/n:ℕ):ℤ) := by exact_mod_cast (Nat.mod_add_div a n).symm
      have changeBase : (a:ℤ)*d-a^2-((r:ℤ)*d-r^2) =
          n*((a/n:ℕ):ℤ)*(d-a-r) := by
        rw [show (n:ℤ)*((a/n:ℕ):ℤ)=a-r by linarith [decomp]]
        ring
      dsimp [d] at changeBase ⊢
      nlinarith only [changeBase,vz]

/-- When a²+1<n the fractional remainder in a*S(a,n) lies strictly below 1. -/
theorem integer_part {a n : ℕ} (ha : 0<a) (small : a^2+1<n) (cop : a.Coprime n) :
    ∃ d : ℤ, (a:ℚ)*score n a=d ∧ ⌊score a n⌋=((n:ℤ)-3*a-d)/a := by
  obtain ⟨d,_,id,_⟩ := numerator n a ha cop.symm
  refine ⟨d,id,?_⟩
  have an : a<n := by nlinarith [Nat.mul_le_mul_left a ha]
  have hn := ha.trans an
  have aq : (0:ℚ)<a := by exact_mod_cast ha
  have nq : (0:ℚ)<n := by exact_mod_cast hn
  have eps : ((a:ℚ)^2+1)/n<1 := (div_lt_iff₀ nq).mpr (by
    simpa only [one_mul] using (show (a:ℚ)^2+1<n by exact_mod_cast small))
  let k : ℤ := n-3*a-d
  have scale : (a:ℚ)*score a n=(k:ℚ)+((a:ℚ)^2+1)/n := by
    rw [at_small ha an,mul_sub,id]
    simp [k,mainTerm]
    field_simp; ring
  have ai : (0:ℤ)<a := by exact_mod_cast ha
  have lo : ((k/(a:ℤ):ℤ):ℚ)*a≤k := by exact_mod_cast Int.ediv_mul_le k ai.ne'
  have hi : (k:ℚ)+1≤(((k/(a:ℤ):ℤ):ℚ)+1)*a := by
    exact_mod_cast (show k+1≤(k/(a:ℤ)+1)*a by have := Int.lt_ediv_add_one_mul_self k ai; omega)
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (mul_le_mul_iff_of_pos_right aq).mp
    linarith [show (0:ℚ)≤((a:ℚ)^2+1)/n by positivity]
  · apply (mul_lt_mul_iff_of_pos_right aq).mp
    linarith

/-- The floor of the full Dedekind sum modulo P needs only n modulo aP. -/
theorem floor_period {a n m P : ℕ} (ha : 0<a) (sn : a^2+1<n) (sm : a^2+1<m)
    (cn : a.Coprime n) (cm : a.Coprime m) (same : n ≡ m [MOD a*P]) :
    ⌊score a n⌋ ≡ ⌊score a m⌋ [ZMOD (P:ℤ)] := by
  obtain ⟨d,vd,fn⟩ := integer_part ha sn cn
  obtain ⟨f,vf,fm⟩ := integer_part ha sm cm
  have eq := periodic (same.of_dvd (dvd_mul_right a P))
  rw [← eq] at vf
  have df : d=f := by exact_mod_cast vd.symm.trans vf
  subst f
  obtain ⟨z,hz⟩ := same.dvd
  push_cast at hz
  rw [fn,fm,Int.modEq_iff_dvd]
  refine ⟨z,?_⟩
  have expand : (m:ℤ)-3*a-d = ((n:ℤ)-3*a-d) + ((P:ℤ)*z)*a := by
    calc _ = (n:ℤ)-3*a-d+(m-n) := by ring
         _ = _ := by rw [hz]; ring
  rw [expand, Int.add_mul_ediv_right _ _ (by exact_mod_cast ha.ne')]
  ring

private theorem numerator_identity {a n : ℕ} {d g : ℤ} (ha : 0<a) (an : a<n)
    (large : (n:ℚ)*score a n=d) (small : (a:ℚ)*score n a=g) :
    (a:ℤ)*d = (n:ℤ)^2+a^2+1-3*a*n-n*g := by
  have aq : (a:ℚ)≠0 := by exact_mod_cast ha.ne'
  have nq : (n:ℚ)≠0 := by exact_mod_cast (ha.trans an).ne'
  have h : (a:ℚ)*d = (n:ℚ)^2+a^2+1-3*a*n-n*g := by
    rw [← large,← small,at_small ha an]
    field_simp [mainTerm]
    ring
  exact_mod_cast h

/-- The integral numerator n*S(a,n) modulo P depends only on n modulo
aP for every n>a. -/
theorem numerator_period {a n m P : ℕ} (ha : 0<a) (an : a<n) (am : a<m)
    (cn : a.Coprime n) (cm : a.Coprime m) (same : n ≡ m [MOD a*P]) :
    ∃ d f : ℤ, (n:ℚ)*score a n=d ∧ (m:ℚ)*score a m=f ∧ d ≡ f [ZMOD (P:ℤ)] := by
  obtain ⟨d,_,dn,_⟩ := numerator a n (ha.trans an) cn
  obtain ⟨f,_,fm,_⟩ := numerator a m (ha.trans am) cm
  obtain ⟨g,_,gn,_⟩ := numerator n a ha cn.symm
  have eq := periodic (same.of_dvd (dvd_mul_right a P))
  have qn := numerator_identity ha an dn gn
  have qm := numerator_identity ha am fm (eq ▸ gn)
  refine ⟨d,f,dn,fm,Int.modEq_iff_dvd.mpr ?_⟩
  obtain ⟨k,hk⟩ := same.dvd
  push_cast at hk
  refine ⟨k*(m+n-3*(a:ℤ)-g),?_⟩
  apply mul_left_cancel₀ (show (a:ℤ)≠0 by exact_mod_cast ha.ne')
  calc (a:ℤ)*(f-d) = (m-n)*(m+n-3*(a:ℤ)-g) := by rw [mul_sub,qm,qn]; ring
       _ = _ := by rw [hk]; ring

private theorem plus_one {a n : ℕ} (h : 1<a) (r : n%a=1) :
    score n a=(a:ℚ)-3+2/a := by
  rw [periodic (r.trans (Nat.mod_eq_of_lt h).symm), at_small zero_lt_one h, score.eq_def a 1]
  simp [mainTerm, Nat.mod_one]
  ring

private theorem minus_one {a n : ℕ} (h : 1<a) (r : n%(a+1)=a) :
    score n (a+1)=-((a+1:ℚ)-3+2/(a+1)) := by
  rw [periodic (r.trans (Nat.mod_eq_of_lt (Nat.lt_succ_self a)).symm),
    at_small (by omega : 0<a) (Nat.lt_succ_self a)]
  have ha : (a+1)%a=1 := by simp [Nat.add_mod, Nat.mod_eq_of_lt h]
  rw [plus_one h ha]
  simp only [mainTerm,Nat.cast_add,Nat.cast_one]
  have ap : 0<(a:ℚ) := by exact_mod_cast (show 0<a by omega)
  field_simp
  ring

/-- Consecutive odd candidates reverse just beyond the cubic guarantee.
With a=k+7, b=a+2 and N=a*b*(a-6)+a+1, the score gap is less than -8. -/
theorem reversed_family (k : ℕ) :
    let a := k+7
    let b := k+9
    let n := a*b*(k+1)+(k+8)
    score a n - score b n < -8 := by
  let a := k+7
  let b := k+9
  let n := a*b*(k+1)+(k+8)
  change score a n - score b n < -8
  have ba : b=(k+8)+1 := rfl
  have ra : n%a=1 := by
    rw [show n=1+(b*(k+1)+1)*a by dsimp [a,b,n]; ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show 1<a by dsimp [a]; omega)]
  have rb : n%b=k+8 := by
    rw [show n=(k+8)+(a*(k+1))*b by dsimp [n]; ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show k+8<b by dsimp [b]; omega)]
  have wh : b<n := by
    dsimp [n]
    have v := Nat.mul_le_mul (show 1≤a by dsimp [a]; omega) (le_refl b)
    have w := Nat.mul_le_mul_left (a*b) (show 1≤k+1 by omega)
    omega
  have ar : (0:ℚ)<a := by dsimp [a]; positivity
  have br : (0:ℚ)<b := by dsimp [b]; positivity
  have nr : (0:ℚ)<n := by exact_mod_cast ((show 0<b by dsimp [b]; omega).trans wh)
  rw [at_small (by dsimp [a]; omega) ((show a<b by dsimp [a,b]; omega).trans wh),
    at_small (by dsimp [b]; omega) wh, plus_one (by dsimp [a]; omega) ra]
  have min := minus_one (by omega : 1<k+8) (ba ▸ rb)
  have bc : (k:ℚ)+8+1=b := by dsimp [b]; push_cast; ring
  push_cast at min
  rw [bc] at min
  rw [← ba] at min
  rw [min]
  have diff : mainTerm a n-((a:ℚ)-3+2/a) -
        (mainTerm b n - -((b:ℚ)-3+2/b)) =
      -8-1/a-1/b-2/n*(1-1/(a*b)) := by
    unfold mainTerm
    field_simp
    dsimp [n,a,b]
    push_cast
    ring
  rw [diff]
  have big : 1≤(a:ℚ)*b := by
    exact_mod_cast Nat.mul_pos (show 0<a by dsimp [a]; omega) (show 0<b by dsimp [b]; omega)
  have inv : 1/((a:ℚ)*b)≤1 := (div_le_iff₀ (mul_pos ar br)).mpr (by linarith)
  have nn := mul_nonneg (by positivity : 0≤(2:ℚ)/n) (sub_nonneg.mpr inv)
  linarith [show 0<(1:ℚ)/a by positivity,show 0<(1:ℚ)/b by positivity]

/-- Witness at the requested equal-width shape using 15-bit primes and a
30-bit product, with the odd comparison window close to the cube root. -/
theorem balanced_reversal :
    Nat.Prime 21727 ∧ Nat.Prime 24793 ∧ 21727*24793=538677511 ∧
    score 815 538677511 - score 817 538677511 < -8 := by
  refine ⟨by norm_num,by norm_num,by decide,?_⟩
  exact reversed_family 808

end PrimeFactors.DedekindLaneRanking
