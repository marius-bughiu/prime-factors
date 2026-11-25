import PrimeFactors.ThreeUnitFactorialWindows
import PrimeFactors.BinomialDivisorScale
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Determinant budgets for full-rank, recursively rounded 3-unit windows. -/

namespace PrimeFactors.RecursiveUnitScale

open ThreeUnitFactorialWindows FeasibleDivisorCover Finset

set_option exponentiation.threshold 16384
set_option maxRecDepth 8192

/-- On going from i to i+1, both components of the lcm divide this multiple of the old lcm. -/
theorem denominator_step (i : ℕ) : denominator (i+1)≤3*(i+1)*denominator i := by
  apply Nat.le_of_dvd (Nat.mul_pos (by positivity) (denominator_pos _))
  apply Nat.lcm_dvd
  · rw [Nat.factorial_succ]
    simpa only [Nat.mul_assoc] using
      dvd_mul_of_dvd_right (Nat.mul_dvd_mul_left (i+1) (Nat.dvd_lcm_left ..)) 3
  · rcases (show (i+1)/2=i/2 ∨ ((i+1)/2=i/2+1 ∧ i+1=2*(i/2+1)) by omega) with same|⟨next,form⟩
    · have eq : quadraticDen (i+1)=quadraticDen i := by simp only [quadraticDen,same]
      rw [eq]
      exact dvd_mul_of_dvd_right (Nat.dvd_lcm_right ..) _
    · have eq : quadraticDen (i+1)=3*(i/2+1)*quadraticDen i := by
        rw [quadraticDen,quadraticDen,next,Nat.factorial_succ,pow_succ]
        ring
      rw [eq,form]
      exact (Nat.mul_dvd_mul_left _ (Nat.dvd_lcm_right ..)).trans
        (show 3*(i/2+1)*denominator i ∣ 3*(2*(i/2+1))*denominator i from ⟨2, by ring⟩)

private lemma digit_sum (a n : ℕ) (hn : n<3^a) : ((3:ℕ).digits n).sum ≤ 2*a := by
  induction a generalizing n with
  | zero =>
    have hn0 : n=0 := by simpa using hn
    subst n
    simp
  | succ a ih =>
    by_cases nz : n=0
    · simp [nz]
    have bound : n/3<3^a := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [pow_succ] using hn)
    have d := ih _ bound
    rw [Nat.digits_of_two_le_of_pos (by decide : 2≤3) (Nat.pos_of_ne_zero nz),List.sum_cons]
    omega

private def bonus (i : ℕ) := i/4-10

private lemma extra {i : ℕ} (hi : i<dimension) : 3^(bonus i)*i.factorial≤denominator i := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let v := padicValNat 3
  have upper := sub_one_mul_padicValNat_factorial (p:=3) i
  have lower := sub_one_mul_padicValNat_factorial (p:=3) (i/2)
  have ds := digit_sum 9 (i/2) (by dsimp only [dimension] at hi; norm_num; omega)
  have vbound : bonus i + v i.factorial ≤ i/2 + v (i/2).factorial := by
    dsimp only [v,bonus]
    norm_num only at upper lower ds
    omega
  have qpos : 0<quadraticDen i := Nat.mul_pos (pow_pos (by decide) _) (Nat.factorial_pos _)
  have qv : v (quadraticDen i) ≤ v (denominator i) := by
    apply (padicValNat_dvd_iff_le (denominator_pos i).ne').mp
    exact ((padicValNat_dvd_iff_le qpos.ne').mpr (le_refl _)).trans (Nat.dvd_lcm_right ..)
  have vq : v (quadraticDen i) = i/2+v (i/2).factorial := by
    dsimp only [v,quadraticDen]
    rw [padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),padicValNat.pow _ (by decide),
      padicValNat.self (by decide),mul_one]
  obtain ⟨c,eq⟩ : i.factorial∣denominator i := Nat.dvd_lcm_left ..
  have cp : c≠0 := by intro zero; apply (denominator_pos i).ne'; simp [eq,zero]
  have vc : v (denominator i) = v i.factorial+v c := by
    rw [eq]; exact padicValNat.mul (Nat.factorial_ne_zero _) cp
  have power : 3^(bonus i)∣c := (padicValNat_dvd_iff_le cp).mpr (by change bonus i≤v c; rw [vq,vc] at qv; omega)
  rw [eq,Nat.mul_comm i.factorial]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (Nat.pos_of_ne_zero cp) power)

private lemma bonus_inequality (r : ℕ) : r*(r-1)/2 ≤ 4*(∑ i∈range r, bonus i) + r*43 := by
  calc
    _ = ∑ i∈range r,i := (sum_range_id r).symm
    _ ≤ ∑ i∈range r,(4*bonus i+43) := sum_le_sum (fun i _ => by dsimp only [bonus]; omega)
    _ = (∑ i∈range r,4*bonus i)+(∑ _∈range r,43) := sum_add_distrib
    _ = _ := congrArg₂ (·+·) (mul_sum (range r) bonus 4).symm (by simp)

private lemma bonus_finish (r : ℕ) (num : 4*75230208+r*43 ≤ r*(r-1)/2) :
    75230208≤∑ i∈range r,bonus i := by
  have h := num.trans (bonus_inequality r)
  exact (Nat.mul_le_mul_left_iff (by decide : 0<4)).mp (Nat.le_of_add_le_add_right h)

private theorem bonus_total : 75230208 ≤ ∑ i ∈ range dimension, bonus i :=
  bonus_finish dimension (by decide +kernel)

private theorem power_credit {a k b z w : ℕ} (nz : z≠0) (bit : 2^w≤a^z) (fits : k*z≤w*b) :
    2^k ≤ a^b := by
  apply (Nat.pow_le_pow_iff_left nz).mp
  calc
    (2^k)^z = 2^(k*z) := (pow_mul ..).symm
    _ ≤ 2^(w*b) := Nat.pow_le_pow_right (by decide) fits
    _ = (2^w)^b := pow_mul ..
    _ ≤ (a^z)^b := Nat.pow_le_pow_left bit _
    _ = (a^b)^z := by rw [←pow_mul,←pow_mul,Nat.mul_comm b z]

private lemma increase_power {a b e : ℕ} (num : 2^e≤3^a) (order : a≤b) : 2^e≤3^b :=
  num.trans (Nat.pow_le_pow_right (by decide) order)

private lemma product_credit {r a b : ℕ}
    (favorable : ∀ i<r, 3^(bonus i)*i.factorial ≤ denominator i)
    (unit : 2^a≤3^(∑ i∈range r,bonus i)) (factorial : 2^b≤∏ i∈range r,i.factorial) :
    2^(a+b) ≤ ∏ i∈range r, denominator i := by
  calc
    _ = 2^a*2^b := pow_add ..
    _ ≤ 3^(∑ i∈range r,bonus i) * ∏ i∈range r, i.factorial := Nat.mul_le_mul unit factorial
    _ = ∏ i∈range r, 3^(bonus i)*i.factorial := by rw [prod_mul_distrib,prod_pow_eq_pow_sum]
    _ ≤ _ := prod_le_prod' (fun _ hi => favorable _ (mem_range.mp hi))

/-- Lower bound on the product of all 24,576 denominators, checked without forming
an integer with billions of digits. -/
theorem denominator_bits : 2^3859823040 ≤ ∏ i ∈ range dimension, denominator i := by
  have fbits : 2^3740806500 ≤ (5360:ℕ)^(dimension.choose 2) := by
    apply power_credit (a:=5360) (k:=3740806500) (b:=dimension.choose 2) (z:=1024) (w:=12685)
      (by decide) (by decide +kernel)
    simp only [Nat.choose_two_right]; decide +kernel
  have bonus_bits : 2^119016540 ≤ (3:ℕ)^75230208 :=
    power_credit (a:=3) (b:=75230208) (k:=119016540) (z:=256) (w:=405)
      (by decide) (by decide +kernel) (by decide +kernel)
  rw [show 3859823040=119016540+3740806500 by decide]
  exact product_credit (r:=dimension) (a:=119016540) (b:=3740806500)
    (fun _ hi => extra hi) (increase_power (a:=75230208) (b:=∑ i∈range dimension,bonus i) (e:=119016540) bonus_bits bonus_total)
    (fbits.trans BinomialDivisorScale.factorial_budget)

private lemma volume {r u e : ℕ} {W : ℕ → ℕ}
    (credit : 2^e≤∏ i∈range r,denominator i)
    (lim : ∀ i<r, W i * denominator i≤4*(2^u)^i)
    (fits : e≤2*r+u*r.choose 2) : (∏ i∈range r, W i)≤2^(2*r+u*r.choose 2-e) := by
  apply (Nat.mul_le_mul_right_iff (pow_pos (by decide : 0<(2:ℕ)) e)).mp
  calc
    (∏ i∈range r, W i)*2^e ≤ (∏ i∈range r, W i)*(∏ i∈range r,denominator i) := Nat.mul_le_mul_left _ credit
    _ = ∏ i∈range r,(W i*denominator i) := (prod_mul_distrib ..).symm
    _ ≤ ∏ i∈range r,4*(2^u)^i := prod_le_prod' (fun _ hi => lim _ (mem_range.mp hi))
    _ = 2^(2*r+u*r.choose 2) := by
      rw [prod_mul_distrib,prod_const,card_range,prod_pow_eq_pow_sum,sum_range_id,Nat.choose_two_right,
        pow_add,pow_mul,pow_mul]
      rfl
    _ = 2^(2*r+u*r.choose 2-e)*2^e := by rw [←pow_add,Nat.sub_add_cancel fits]

private lemma collect (a b c d : ℕ) : a*((b*c)*d)=((a*b)*d)*c := by ac_rfl

private lemma transfer {n D T m r v f : ℕ} {Z : ℕ} (cn : n≤2^1024*D) (df : 2^1023≤D)
    (dt : T≤m*r) (bound : Z≤2^v) (fits : f+1024*T+v<1023*(m*r-T)) :
    2^f*(n^T*Z)<(D^m)^r := by
  have pos : 0<D := (pow_pos (by decide : 0<(2:ℕ)) _).trans_le df
  calc
    2^f*(n^T*Z) ≤ 2^f*((2^1024*D)^T*2^v) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left cn _) bound)
    _ = 2^(f+1024*T+v)*D^T := by
      rw [mul_pow,pow_add,pow_add,pow_mul]; exact collect ..
    _ < 2^(1023*(m*r-T))*D^T := Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide) fits) (pow_pos pos _)
    _ ≤ D^(m*r-T)*D^T := by rw [pow_mul]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left df _)
    _ = (D^m)^r := by rw [←pow_add,Nat.sub_add_cancel dt,pow_mul]

private abbrev rankCredit : ℕ := 3859823040
private abbrev jetPower : ℕ := 75491328
private abbrev totalDegree : ℕ := 301977600

private theorem parameters : multiplicity + multiplicity.choose 2 = jetPower ∧
    dimension.choose 2 = totalDegree ∧ jetPower ≤ multiplicity*dimension := by
  simp only [Nat.choose_two_right]; decide +kernel

private theorem rank_power : dimension^dimension≤2^(15*dimension) := by
  calc
    _ ≤ ((2:ℕ)^15)^dimension := Nat.pow_le_pow_left (by decide) _
    _ = _ := (pow_mul ..).symm

private theorem lll_overhead {r f : ℕ} (rank : r≤2^15) (room : 30*r+(r-1)*r≤4*f) :
    r^(2*r)*2^((r-1)*r)≤(2^f)^4 := by
  calc
    _ ≤ ((2:ℕ)^15)^(2*r)*2^((r-1)*r) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left rank _)
    _ = 2^(30*r+(r-1)*r) := by rw [←pow_mul,←pow_add,←Nat.mul_assoc 15 2 r]
    _ ≤ 2^(4*f) := Nat.pow_le_pow_right (by decide) room
    _ = _ := by rw [Nat.mul_comm 4 f,pow_mul]

private lemma window_volume {u : ℕ} {W : ℕ→ℕ}
    (lim : ∀ i<dimension, W i*denominator i ≤ 4*((2:ℕ)^u)^i)
    (fits : rankCredit ≤ 2*dimension+u*totalDegree) :
    (∏ i∈range dimension, W i) ≤ 2^(2*dimension+u*totalDegree-rankCredit) := by
  rw [←parameters.2.1] at fits ⊢
  exact volume (e:=3859823040) (u:=u) (r:=dimension) (W:=W) denominator_bits lim fits

/-- At rank 24,576 and multiplicity 12,287, the finite-box collision bound
holds at U=2^524 (full integer-index interval [0,4U]). -/
theorem finite_room {n D : ℕ} (floor : 2^1023≤D) (coupled : n≤2^1024*D)
    (W : ℕ→ℕ) (lim : ∀ i<dimension, W i*denominator i ≤ 4*((2:ℕ)^524)^i) :
    let m := multiplicity
    let r := dimension
    n^(m+m.choose 2)*(r^r*∏ i∈range r, W i)<(D^m)^r := by
  dsimp only
  rw [parameters.1]
  have weight := window_volume lim (by decide +kernel)
  have room := transfer (f:=15*dimension) coupled floor parameters.2.2 weight (by decide +kernel)
  calc
    _ = dimension^dimension*(n^jetPower*(∏ i∈range dimension, W i)) := Nat.mul_left_comm ..
    _ ≤ _ := Nat.mul_le_mul_right _ rank_power
    _ < _ := room

/-- At half the preceding interval length the stronger numerical sufficient LLL
bound holds. The statement bounds the determinant and the LLL loss. -/
theorem lll_room {n D : ℕ} (floor : 2^1023≤D) (coupled : n≤2^1024*D)
    (W : ℕ→ℕ) (lim : ∀ i<dimension, W i*denominator i ≤ 4*((2:ℕ)^523)^i) :
    let m := multiplicity
    let r := dimension
    r^(2*r)*2^((r-1)*r)*(n^(m+m.choose 2)*(∏ i∈range r, W i))^4<(D^m)^(4*r) := by
  dsimp only
  rw [parameters.1]
  have weight := window_volume lim (by decide +kernel)
  have room := transfer (f:=151173120) coupled floor parameters.2.2 weight (by decide +kernel)
  have factor := lll_overhead (r:=dimension) (f:=151173120) (by decide) (by decide +kernel)
  calc
    _ ≤ (2^151173120)^4*(n^jetPower*(∏ i∈range dimension, W i))^4 := Nat.mul_le_mul_right _ factor
    _ = (2^151173120*(n^jetPower*(∏ i∈range dimension, W i)))^4 := (mul_pow ..).symm
    _ < ((D^multiplicity)^dimension)^4 := Nat.pow_lt_pow_left room (by decide)
    _ = _ := by rw [←pow_mul,Nat.mul_comm dimension 4]

end PrimeFactors.RecursiveUnitScale
