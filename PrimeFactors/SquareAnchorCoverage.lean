import PrimeFactors.PrimeSumDividesSuccessor
import PrimeFactors.UniformDivisorCount
import PrimeFactors.Fermat

/-! If a divisor g of an anchor m gives the correct prime sum via
p+q = N+1-(m-g), its complementary difference is the true totient F=m-g.
Count all pairs reachable via such readouts, even with every divisor supplied. -/
namespace PrimeFactors.SquareAnchorCoverage

open Finset MixedPrefixSample
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

def predProduct (z : ℕ × ℕ) := (z.1-1)*(z.2-1)

/-- The positive readout implies m≤2F even if arbitrary anchors are allowed. -/
theorem anchor_limit {m g F : ℕ} (fp : 0<F) (eq : F+g=m) (dvd : g∣m) :
    0<g ∧ g∣F ∧ m≤2*F := by
  have gf := Nat.dvd_sub dvd (dvd_refl g)
  rw [←eq,Nat.add_sub_cancel] at gf
  have gl := Nat.le_of_dvd fp gf
  exact ⟨Nat.pos_of_dvd_of_pos gf fp,gf,by omega⟩

attribute [local irreducible] MixedPrefixSample.primes MixedPrefixSample.sample
  MixedPrefixSample.ordered MixedPrefixSample.eligible

private theorem pair_bounds {z : ℕ×ℕ} (inside : z∈eligible) :
    1<z.1 ∧ 1<z.2 ∧ predProduct z<2^2048 := by
  rw [eligible,sample,mem_filter] at inside
  obtain ⟨p,q,_⟩ := (mem_ordered.mp inside.1)
  rw [primes,mem_filter,mem_Ico] at p q
  have hi : 2*X=2^1024 := by decide +kernel
  have pp := p.2.one_lt
  have qp := q.2.one_lt
  refine ⟨pp,qp,?_⟩
  rw [show (2:ℕ)^2048=2^1024*2^1024 by decide +kernel]
  exact Nat.mul_lt_mul_of_lt_of_le (by omega : z.1-1<2^1024)
    (by omega : z.2-1≤2^1024) (by positivity)

/-- A list of possible totients has at most the sum of their divisor counts
in ordered prime pairs. This includes the cost of collisions at the same F. -/
theorem count_with_values (pairs : Finset (ℕ×ℕ)) (values : Finset ℕ)
    (valid : ∀ z∈pairs, 1<z.1 ∧ 1<z.2 ∧ predProduct z<2^2048 ∧ predProduct z∈values) :
    pairs.card ≤ values.card*2^240 := by
  classical
  let ds (F : ℕ) := if F<2^2048 then F.divisors else ∅
  let box := values.biUnion fun F => (ds F).image (fun a => (F,a))
  let code (z : ℕ×ℕ) := (predProduct z,z.1-1)
  have enc : pairs.card≤box.card := by
    apply card_le_card_of_injOn code
    · intro z h
      obtain ⟨pp,qp,cap,mem⟩ := valid z h
      have pos : 0<predProduct z := Nat.mul_pos (by omega) (by omega)
      refine mem_biUnion.mpr ⟨predProduct z,mem,mem_image.mpr ⟨z.1-1,?_,rfl⟩⟩
      simp only [ds,if_pos cap,Nat.mem_divisors]
      exact ⟨dvd_mul_right ..,pos.ne'⟩
    · intro x hx y hy eq
      obtain ⟨px,qx,_⟩ := valid x hx
      obtain ⟨py,qy,_⟩ := valid y hy
      have p : x.1-1=y.1-1 := congrArg Prod.snd eq
      have f : (x.1-1)*(x.2-1)=(y.1-1)*(y.2-1) := congrArg Prod.fst eq
      rw [←p] at f
      have q := Nat.eq_of_mul_eq_mul_left (by omega : 0<x.1-1) f
      exact Prod.ext (by omega) (by omega)
  refine enc.trans (card_biUnion_le.trans ?_)
  calc
    _ ≤ ∑ _F∈values, 2^240 := sum_le_sum fun F _ => card_image_le.trans (by
      dsimp only [ds]
      split_ifs with small
      · by_cases pos : F=0
        · simp [pos]
        · exact (UniformDivisorCount.below_2049 (Nat.pos_of_ne_zero pos)
            (small.trans (by decide +kernel))).le
      · simp)
    _ = _ := by simp

theorem pair_capacity (values : Finset ℕ) :
    (eligible.filter (fun z => predProduct z∈values)).card ≤ values.card*2^240 := by
  apply count_with_values
  intro z hz
  obtain ⟨inside,mem⟩ := mem_filter.mp hz
  obtain ⟨p,q,cap⟩ := pair_bounds inside
  exact ⟨p,q,cap,mem⟩

/-- Predecessor products represented by the divisors of bounded anchors. -/
noncomputable def valuesAt (m : ℕ) := m.divisors.image (fun g => m-g)

theorem menu_capacity (anchors : Finset ℕ) (size : ∀ m∈anchors, m<2^2049) :
    (eligible.filter (fun z => predProduct z∈anchors.biUnion valuesAt)).card ≤
      anchors.card*2^480 := by
  have count : (anchors.biUnion valuesAt).card≤anchors.card*2^240 := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _m∈anchors, 2^240 := sum_le_sum fun m hm => card_image_le.trans (by
        by_cases hz : m=0
        · simp [hz]
        · exact (UniformDivisorCount.below_2049 (Nat.pos_of_ne_zero hz) (size m hm)).le)
      _ = _ := by simp
  exact (pair_capacity _).trans ((Nat.mul_le_mul_right _ count).trans_eq (by
    rw [Nat.mul_assoc,←pow_add]))

/-- For all positive divisors of all anchors in a public dictionary. Even an
input-dependent selector cannot cover more pairs than this union. -/
theorem menu_frequency (anchors : Finset ℕ) (size : ∀ m∈anchors, m<2^2049)
    (nonempty : anchors.Nonempty) :
    2^1541*(eligible.filter (fun z => predProduct z∈anchors.biUnion valuesAt)).card <
      anchors.card*eligible.card := by
  have scale : 21000000*(2^1541*2^480)≤2^2046 := by decide +kernel
  have cnt := Nat.mul_le_mul_left (21000000*2^1541) (menu_capacity anchors size)
  have final := Nat.mul_lt_mul_of_pos_left
    (scale.trans_lt ChebyshevPrimeSample.eligible_count) (card_pos.mpr nonempty)
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  calc
    _ ≤ (21000000*2^1541)*(anchors.card*2^480) := by simpa only [mul_assoc] using cnt
    _ = anchors.card*(21000000*(2^1541*2^480)) := by ac_rfl
    _ < anchors.card*(21000000*eligible.card) := final
    _ = _ := by ac_rfl

/-- Write each divisor of r² as t*a² where r=t*a*b. Reducing g/r
to lowest terms makes the positive triple unique, though only existence is used. -/
theorem square_parameters {g r : ℕ} (rp : 0<r) (dvd : g∣r^2) :
    ∃ a b t : ℕ, 0<a ∧ 0<b ∧ 0<t ∧ a.Coprime b ∧ r=t*(a*b) ∧ g=t*a^2 := by
  let h := g.gcd r
  let a := g/h
  let b := r/h
  have hp : 0<h := Nat.gcd_pos_of_pos_right _ rp
  have ga : h*a=g := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have rb : h*b=r := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have gp := Nat.pos_of_dvd_of_pos dvd (pow_pos rp 2)
  have ap : 0<a := Nat.pos_of_mul_pos_left (ga ▸ gp)
  have bp : 0<b := Nat.pos_of_mul_pos_left (rb ▸ rp)
  have cop : a.Coprime b := Nat.coprime_div_gcd_div_gcd hp
  have cancel : a∣b^2*h := by
    apply (Nat.mul_dvd_mul_iff_left hp).mp
    rw [ga,show h*(b^2*h)=(h*b)^2 by ring,rb]
    exact dvd
  obtain ⟨t,ht⟩ := (cop.pow_right 2).dvd_of_dvd_mul_left cancel
  refine ⟨a,b,t,ap,bp,?_,cop,?_,?_⟩
  · exact Nat.pos_of_mul_pos_left (ht ▸ hp)
  · rw [←rb,ht]; ring
  · rw [←ga,ht]; ring

noncomputable def squareValues (U : ℕ) := (Icc 1 U).biUnion fun a => (Icc 1 U).biUnion fun b =>
  (Icc 1 (U/(a*b))).image fun t => (t*(a*b))^2-t*a^2

theorem mem_squareValues {r g U : ℕ} (rp : 0<r) (bound : r≤U) (dvd : g∣r^2) :
    r^2-g ∈ squareValues U := by
  obtain ⟨a,b,t,ap,bp,tp,_,eq,ge⟩ := square_parameters rp dvd
  have ab := Nat.le_mul_of_pos_left (a*b) tp
  rw [←eq] at ab
  have aU := (Nat.le_mul_of_pos_right a bp).trans (ab.trans bound)
  have bU := (Nat.le_mul_of_pos_left b ap).trans (ab.trans bound)
  have tU := (Nat.le_div_iff_mul_le (Nat.mul_pos ap bp)).mpr (eq ▸ bound)
  exact mem_biUnion.mpr ⟨a,mem_Icc.mpr ⟨ap,aU⟩, mem_biUnion.mpr ⟨b,mem_Icc.mpr ⟨bp,bU⟩,
    mem_image.mpr ⟨t,mem_Icc.mpr ⟨tp,tU⟩,by rw [eq,ge]⟩⟩⟩

/-- The total number of predecessor products read off every square with root
at most U is at most U times the square of the U-th harmonic number. -/
theorem square_count (U : ℕ) : ((squareValues U).card:ℚ) ≤ U*(harmonic U)^2 := by
  let I := Icc 1 U
  have count : (squareValues U).card≤∑ a∈I, ∑ b∈I, U/(a*b) := by
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro a ha
    apply card_biUnion_le.trans
    exact sum_le_sum fun b _ => card_image_le.trans (by simp)
  calc
    _ ≤ ∑ a∈I, ∑ b∈I, ((U/(a*b):ℕ):ℚ) := by exact_mod_cast count
    _ ≤ ∑ a∈I, ∑ b∈I, (U:ℚ)/((a:ℚ)*b) := by
      apply sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
      simpa only [Nat.cast_mul] using (Nat.cast_div_le (α:=ℚ) (m:=U) (n:=a*b))
    _ = _ := by simp [I,harmonic_eq_sum_Icc,div_eq_mul_inv,mul_sum,sum_mul,pow_two,mul_assoc]

/-- Success includes every square, above or below N, at every distance. -/
def readable (z : ℕ×ℕ) : Prop := ∃ r g : ℕ, g∣r^2 ∧ predProduct z+g=r^2

open Classical in
noncomputable def squarePairs := eligible.filter readable

attribute [local irreducible] squareValues squarePairs

theorem all_squares_frequency : 2^738*squarePairs.card<eligible.card := by
  classical
  let U : ℕ := 3*2^1023
  have subset : squarePairs ⊆ eligible.filter (fun z => predProduct z∈squareValues U) := by
    intro z h
    rw [squarePairs,mem_filter] at h
    obtain ⟨hz,r,g,hg,eq⟩ := h
    obtain ⟨p,q,cap⟩ := pair_bounds hz
    have fp : 0<predProduct z := Nat.mul_pos (by omega) (by omega)
    have bound := (anchor_limit fp eq hg).2.2
    have cmp : 2*2^2048≤U^2 := by decide +kernel
    have size : r≤U := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      (bound.trans ((Nat.mul_le_mul_left _ cap.le).trans cmp))
    have rp : 0<r := Nat.pos_of_ne_zero (fun hr => by subst r; simp only [zero_pow (by decide : 2≠0),Nat.add_eq_zero_iff] at eq; exact fp.ne' eq.1)
    have mem := mem_squareValues rp size hg
    rw [←eq,Nat.add_sub_cancel] at mem
    exact mem_filter.mpr ⟨hz,mem⟩
  have hq : harmonic U≤(712:ℚ) := by
    have h := harmonic_le_one_add_log U
    have up : (U:ℝ)≤(2:ℝ)^1025 := by exact_mod_cast (by decide +kernel : U≤2^1025)
    have lg := Real.log_le_log (by exact_mod_cast (by decide +kernel : 0<U)) up
    rw [Real.log_pow] at lg
    change Real.log (U:ℝ)≤1025*Real.log 2 at lg
    exact_mod_cast (show (harmonic U:ℝ)≤712 by linarith only [h,lg,Real.log_two_lt_d9])
  have hpos : 0≤harmonic U := by rw [harmonic_eq_sum_Icc]; positivity
  have c : (squareValues U).card≤U*712^2 := by
    have sq := pow_le_pow_left₀ hpos hq 2
    exact_mod_cast (square_count U).trans (mul_le_mul_of_nonneg_left sq (Nat.cast_nonneg U))
  have population := (card_le_card subset).trans ((pair_capacity _).trans (Nat.mul_le_mul_right _ c))
  have numeric : (21000000*2^738)*(U*712^2*2^240)≤2^2046 := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using ((Nat.mul_le_mul_left _ population).trans numeric).trans_lt
    ChebyshevPrimeSample.eligible_count

/-- The reduced fraction a/b generates a square divisor whenever ab divides r.
Here the product r*a/b is represented exactly by t*a² with r=t*a*b. -/
theorem parameter_divides (a b t : ℕ) : t*a^2∣(t*(a*b))^2 := by
  exact ⟨t*b^2,by ring⟩

/-- For a specified reduced slope, checking the single small modulus ab is
both necessary and sufficient for the exact square-divisor condition. -/
theorem slope_iff {a b g r : ℕ} (cop : a.Coprime b) (bp : 0<b)
    (rp : 0<r) (slope : g*b=r*a) : g∣r^2 ↔ a*b∣r := by
  have br : b∣r := cop.symm.dvd_of_dvd_mul_right (slope ▸ dvd_mul_left b g)
  obtain ⟨k,rk⟩ := br
  have kp : 0<k := Nat.pos_of_mul_pos_left (rk ▸ rp)
  have gk : g=k*a := Nat.eq_of_mul_eq_mul_right bp (by rw [slope,rk]; ring)
  constructor
  · intro hit
    have cancel : a∣b^2*k := by
      apply (Nat.mul_dvd_mul_iff_left kp).mp
      rw [←gk,show k*(b^2*k)=(b*k)^2 by ring,←rk]
      exact hit
    obtain ⟨t,kt⟩ := (cop.pow_right 2).dvd_of_dvd_mul_left cancel
    exact ⟨t,by rw [rk,kt]; ring⟩
  · rintro ⟨t,rt⟩
    have kt : k=t*a := Nat.eq_of_mul_eq_mul_left bp (by rw [←rk,rt]; ring)
    rw [gk,kt,rk,kt]
    exact ⟨t*b^2,by ring⟩

/-- With the least square above an odd product, every correct divisor readout
has slope at least 2 and strictly below 5. In particular b is bounded by
sqrt(r/2) in the coprime parameterization, before any search budget. -/
theorem nearest_slope {p q r g : ℕ} (po : Odd p) (qo : Odd q) (lt : p<q)
    (bal : q≤2*p) (root : r=ceilSqrt (p*q)) (above : p*q<r^2)
    (hit : (p-1)*(q-1)+g=r^2) :
    2*r≤g ∧ g<5*r := by
  obtain ⟨u,pu⟩ := po
  obtain ⟨v,qv⟩ := qo
  have mid : p+q=2*(u+v+1) := by omega
  have four : 4*(p*q)≤(p+q)^2 := by nlinarith [sq_nonneg ((q:ℤ)-p)]
  have av : r≤u+v+1 := by
    rw [root,ceilSqrt_le_iff]
    rw [mid] at four
    nlinarith only [four]
  have pp : 0<p := by omega
  have qp : 0<q := by omega
  have pr : p≤r := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    exact (show p^2≤p*q by rw [pow_two]; exact Nat.mul_le_mul_left p lt.le).trans above.le
  have rp : 0<r := pp.trans_le pr
  have prev : (r-1)^2<p*q := lt_of_not_ge (fun h => by
    have l := ceilSqrt_le_iff.mpr h
    omega)
  have add : (p-1)*(q-1)+(p+q)=p*q+1 := by
    rw [pu,qv]
    simp only [Nat.add_sub_cancel]
    ring
  have rr : r-1+1=r := Nat.sub_add_cancel rp
  have diff : r^2+1=(r-1)^2+2*r := calc
    r^2+1 = ((r-1)+1)^2+1 := congrArg (fun z : ℕ => z^2+1) rr.symm
    _ = (r-1)^2+2*((r-1)+1) := by ring
    _ = _ := by rw [rr]
  omega

/-- For the constructed two-linear-factor family, the least square has root
24u and three times that root is a divisor giving the correct sum. -/
theorem triple_slope_family (u : ℕ) (pos : 0<u) :
    let p := 18*u+1
    let q := 32*u-3
    let r := ceilSqrt (p*q)
    r=24*u ∧ 3*r∣r^2 ∧ (p-1)*(q-1)+3*r=r^2 ∧
    p+q=2*(r+u-1) ∧ 16*p=9*q+43 := by
  let v := u-1
  have uv : u=v+1 := by dsimp [v]; omega
  rw [uv]
  have f : 32*(v+1)-3=32*v+29 := by omega
  simp only [f]
  have high : (18*(v+1)+1)*(32*v+29)≤(24*(v+1))^2 := by nlinarith
  have low : (24*v+23)^2<(18*(v+1)+1)*(32*v+29) := by nlinarith
  have ceil : ceilSqrt ((18*(v+1)+1)*(32*v+29))=24*(v+1) := by
    have le := ceilSqrt_le_iff.mpr high
    have gt := lt_of_not_ge fun h => low.not_le (ceilSqrt_le_iff.mp h)
    omega
  rw [ceil]
  refine ⟨rfl,⟨8*(v+1),by ring⟩,?_,by omega,by omega⟩
  simp only [Nat.add_sub_cancel,show 32*v+29-1=32*v+28 by omega]
  ring

end PrimeFactors.SquareAnchorCoverage
