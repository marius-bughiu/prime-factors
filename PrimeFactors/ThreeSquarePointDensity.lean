import PrimeFactors.ThreeSquareRadiusCounts

/-! How often the coordinate gcd of an ordered, signed point on an integer
sphere gives a proper divisor of the radius. The geometric partition is
unconditional. The general rate follows from the classical total-count formula
for odd radii, stated as an explicit hypothesis. -/
namespace PrimeFactors.ThreeSquarePointDensity

open Finset ThreeSquareRadiusCounts
open private PrimeFactors.ThreeSquareRadiusCounts.signs
  PrimeFactors.ThreeSquareRadiusCounts.slice PrimeFactors.ThreeSquareRadiusCounts.euler_prime
  from PrimeFactors.ThreeSquareRadiusCounts

private abbrev content (x y z : ℕ) := (x.gcd y).gcd z

private theorem content_dvds (x y z : ℕ) :
    content x y z ∣ x ∧ content x y z ∣ y ∧ content x y z ∣ z :=
  ⟨(Nat.gcd_dvd_left ..).trans (Nat.gcd_dvd_left ..),
   (Nat.gcd_dvd_left ..).trans (Nat.gcd_dvd_right ..), Nat.gcd_dvd_right ..⟩

private theorem content_dvd {n x y z : ℕ} (eq : x^2+y^2+z^2=n^2) :
    content x y z ∣ n := by
  obtain ⟨hx,hy,hz⟩ := content_dvds x y z
  apply (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp
  rw [←eq]
  exact dvd_add (dvd_add (pow_dvd_pow_of_dvd hx 2) (pow_dvd_pow_of_dvd hy 2))
    (pow_dvd_pow_of_dvd hz 2)

private theorem magnitudes {n : ℕ} {x y z : ℤ} (eq : x^2+y^2+z^2=(n:ℤ)^2) :
    x.natAbs^2+y.natAbs^2+z.natAbs^2=n^2 := by
  exact_mod_cast (show (x.natAbs:ℤ)^2+(y.natAbs:ℤ)^2+(z.natAbs:ℤ)^2=(n:ℤ)^2 by
    simpa only [Int.natCast_natAbs, sq_abs] using eq)

/-- Coordinate gcd of a signed triple, unchanged by coordinate signs. -/
def coordinateGcd (x y z : ℤ) : ℕ := content x.natAbs y.natAbs z.natAbs

/-- Every signed integral sphere point has coordinate gcd dividing the radius. -/
theorem coordinateGcd_dvd {n : ℕ} {x y z : ℤ} (eq : x^2+y^2+z^2=(n:ℤ)^2) :
    coordinateGcd x y z ∣ n := content_dvd (magnitudes eq)

private theorem full_iff {n x y z : ℕ} (pos : 0<n) (eq : x^2+y^2+z^2=n^2) :
    content x y z=n ↔
      (x=n ∧ y=0 ∧ z=0) ∨ (x=0 ∧ y=n ∧ z=0) ∨ (x=0 ∧ y=0 ∧ z=n) := by
  constructor
  · intro h
    have one {a : ℕ} (div : n ∣ a) (le : a^2≤n^2) : a=0 ∨ a=n := by
      by_cases az : a=0
      · exact Or.inl az
      · have lo := Nat.le_of_dvd (Nat.pos_of_ne_zero az) div
        exact Or.inr (by nlinarith)
    obtain ⟨hx,hy,hz⟩ := content_dvds x y z
    rw [h] at hx hy hz
    have positive : 0<n^2 := pow_pos pos 2
    rcases one hx (by omega) with rfl | rfl <;>
      rcases one hy (by omega) with rfl | rfl <;>
      rcases one hz (by omega) with rfl | rfl <;>
      simp_all
  · rintro (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩) <;> simp [content]

private theorem proper_divisor {p q d : ℕ} (pp : p.Prime) (qp : q.Prime) (hd : d∣p*q)
    (proper : 1<d ∧ d<p*q) : d=p ∨ d=q := by
  by_cases div : p∣d
  · obtain ⟨u,rfl⟩ := div
    rcases qp.eq_one_or_self_of_dvd u (Nat.dvd_of_mul_dvd_mul_left pp.pos hd) with rfl | rfl
    · simp
    · omega
  · have cop := (pp.coprime_iff_not_dvd.mpr div).symm
    rcases qp.eq_one_or_self_of_dvd d (cop.dvd_mul_left.mp hd) with rfl | rfl <;> omega

/-- On a semiprime sphere a proper coordinate gcd is one of the two primes. -/
theorem proper_coordinateGcd {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    {x y z : ℤ} (eq : x^2+y^2+z^2=((p*q:ℕ):ℤ)^2)
    (proper : 1<coordinateGcd x y z ∧ coordinateGcd x y z<p*q) :
    coordinateGcd x y z=p ∨ coordinateGcd x y z=q := by
  exact proper_divisor pp qp (coordinateGcd_dvd eq) proper

/-- At positive radius the maximal gcd singles out the six signed coordinate axes. -/
theorem coordinateGcd_eq_iff {n : ℕ} {x y z : ℤ} (pos : 0<n)
    (eq : x^2+y^2+z^2=(n:ℤ)^2) :
    coordinateGcd x y z=n ↔
      ((x=n ∨ x=-(n:ℤ)) ∧ y=0 ∧ z=0) ∨
      (x=0 ∧ (y=n ∨ y=-(n:ℤ)) ∧ z=0) ∨
      (x=0 ∧ y=0 ∧ (z=n ∨ z=-(n:ℤ))) := by
  change content .. = n ↔ _
  rw [full_iff pos (magnitudes eq)]
  simp [Int.natAbs_eq_iff]

/-- Signed multiplicity for triples whose common coordinate divisor is strictly
between one and the radius. The finite ranges and square-root check agree with
the total and primitive representation counts. -/
noncomputable def properCount (n : ℕ) : ℕ :=
  ∑ x∈range (n+1), ∑ y∈range (n+1),
    let z := (n^2-x^2-y^2).sqrt
    if x^2+y^2+z^2=n^2 ∧ 1<content x y z ∧ content x y z<n
    then PrimeFactors.ThreeSquareRadiusCounts.signs x * PrimeFactors.ThreeSquareRadiusCounts.signs y * PrimeFactors.ThreeSquareRadiusCounts.signs z else 0

private def axisRow (n x y : ℕ) : ℕ :=
  (if x=0 then (if y=0 then 2 else 0) + (if y=n then 2 else 0) else 0) +
  (if x=n then (if y=0 then 2 else 0) else 0)

private theorem axis_sum (n : ℕ) :
    ∑ x∈range (n+1), ∑ y∈range (n+1), axisRow n x y = 6 := by
  simp [axisRow, sum_ite_irrel, sum_add_distrib, Nat.zero_lt_succ]

private theorem row_partition {n x y : ℕ} (large : 1<n) :
    let z := (n^2-x^2-y^2).sqrt
    PrimeFactors.ThreeSquareRadiusCounts.slice n x y false = PrimeFactors.ThreeSquareRadiusCounts.slice n x y true +
      (if x^2+y^2+z^2=n^2 ∧ 1<content x y z ∧ content x y z<n
       then PrimeFactors.ThreeSquareRadiusCounts.signs x * PrimeFactors.ThreeSquareRadiusCounts.signs y *
            PrimeFactors.ThreeSquareRadiusCounts.signs z else 0) + axisRow n x y := by
  have pos : 0<n := by omega
  have ne : n≠1 := by omega
  have self : (n^2).sqrt=n := by simp [pow_two,Nat.sqrt_eq]
  by_cases ax : (x=0 ∧ y=0) ∨ (x=n ∧ y=0) ∨ (x=0 ∧ y=n)
  · rcases ax with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [PrimeFactors.ThreeSquareRadiusCounts.slice, axisRow, content, PrimeFactors.ThreeSquareRadiusCounts.signs,
        self, pos.ne', Ne.symm pos.ne', ne]
  have noaxis : axisRow n x y=0 := by
    unfold axisRow
    split_ifs <;> omega
  rw [noaxis]
  simp only [PrimeFactors.ThreeSquareRadiusCounts.slice, Bool.false_eq_true, false_implies,
    and_true, true_implies, add_zero]
  generalize (n^2-x^2-y^2).sqrt=z
  by_cases eq : x^2+y^2+z^2=n^2
  · have hd := content_dvd eq
    have hu := Nat.le_of_dvd pos hd
    have nz : content x y z≠0 := fun he => pos.ne' (by simpa [he] using hd)
    have below : content x y z<n := by
      apply lt_of_le_of_ne hu
      intro h
      have := (full_iff pos eq).mp h
      tauto
    by_cases primitive : content x y z=1
    · simp only [eq, true_and, show (x.gcd y).gcd z=content x y z from rfl,
        primitive, lt_irrefl, false_and, if_false, if_true, add_zero]
    · have bigger : 1<content x y z := by omega
      simp only [eq, true_and, show (x.gcd y).gcd z=content x y z from rfl,
        primitive, if_false, bigger, below, and_self, if_true, zero_add]
  · simp [eq]

/-- The nonprimitive, nonaxial points are exactly the proper-gcd outcomes. -/
theorem partition {n : ℕ} (large : 1<n) :
    count n false = count n true + properCount n + 6 := by
  unfold count properCount
  rw [←axis_sum n]
  simp only [←sum_add_distrib]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => row_partition large

theorem properCount_eq {n : ℕ} (large : 1<n) :
    properCount n = count n false - count n true - 6 := by
  have := partition large
  omega

private def layerRow (n d : ℕ) (u : ℕ×ℕ) : ℕ :=
  let z := (n^2-u.1^2-u.2^2).sqrt
  if u.1^2+u.2^2+z^2=n^2 ∧ content u.1 u.2 z=d then
    PrimeFactors.ThreeSquareRadiusCounts.signs u.1 *
    PrimeFactors.ThreeSquareRadiusCounts.signs u.2 *
    PrimeFactors.ThreeSquareRadiusCounts.signs z else 0

/-- Number of signed, ordered sphere points with the specified coordinate gcd. -/
noncomputable def layer (n d : ℕ) : ℕ :=
  ∑ u ∈ range (n+1) ×ˢ range (n+1), layerRow n d u

private theorem layerRow_of {n d x y z : ℕ} (eq : x^2+y^2+z^2=n^2)
    (g : content x y z=d) : layerRow n d (x,y)=
      PrimeFactors.ThreeSquareRadiusCounts.signs x *
      PrimeFactors.ThreeSquareRadiusCounts.signs y *
      PrimeFactors.ThreeSquareRadiusCounts.signs z := by
  have hz : (n^2-x^2-y^2).sqrt=z := by
    rw [show n^2-x^2-y^2=z^2 by omega, pow_two, Nat.sqrt_eq]
  simp [layerRow,hz,eq,g]

private theorem layerRow_nonzero {n d x y : ℕ} (nz : layerRow n d (x,y)≠0) :
    ∃ z, x^2+y^2+z^2=n^2 ∧ content x y z=d := by
  unfold layerRow at nz
  dsimp only at nz
  split at nz
  · exact ⟨_,by assumption⟩
  · exact False.elim (nz rfl)

private theorem content_scale (b x y z : ℕ) :
    content (b*x) (b*y) (b*z)=b*content x y z := by simp [content,Nat.gcd_mul_left]

private theorem scale_row {n b x y z : ℕ} (pos : 0<b)
    (eq : x^2+y^2+z^2=n^2) (g : content x y z=1) :
    layerRow n 1 (x,y)=layerRow (b*n) b (b*x,b*y) := by
  have eq' : (b*x)^2+(b*y)^2+(b*z)^2=(b*n)^2 := by
    simpa only [mul_pow, ←mul_add] using congrArg (b^2 * ·) eq
  rw [layerRow_of eq g, layerRow_of eq' (by rw [content_scale, g, mul_one])]
  simp [PrimeFactors.ThreeSquareRadiusCounts.signs, pos.ne']

/-- Scaling all three coordinates identifies the primitive points at radius n
with exactly the gcd-b points at radius b*n, with identical sign multiplicity. -/
theorem scale (n b : ℕ) (pos : 0<b) : layer n 1=layer (b*n) b := by
  classical
  unfold layer
  apply sum_bij_ne_zero (fun u _ _ => (b*u.1,b*u.2))
  · rintro ⟨x,y⟩ hu _
    simp only [mem_product,mem_range,Nat.lt_succ_iff] at hu ⊢
    exact ⟨Nat.mul_le_mul_left b hu.1,Nat.mul_le_mul_left b hu.2⟩
  · rintro ⟨x,y⟩ _ _ ⟨x',y'⟩ _ _ he
    exact Prod.ext (Nat.mul_left_cancel pos (congrArg Prod.fst he))
      (Nat.mul_left_cancel pos (congrArg Prod.snd he))
  · rintro ⟨x,y⟩ mem nz
    obtain ⟨z,eq,g⟩ := layerRow_nonzero nz
    obtain ⟨dx,dy,dz⟩ := content_dvds x y z
    rw [g] at dx dy dz
    obtain ⟨x',rfl⟩ := dx
    obtain ⟨y',rfl⟩ := dy
    obtain ⟨z',rfl⟩ := dz
    have eq' : x'^2+y'^2+z'^2=n^2 := by
      simp only [mul_pow, ←mul_add] at eq
      exact Nat.mul_left_cancel (pow_pos pos 2) eq
    have g' : content x' y' z'=1 := by
      rw [content_scale] at g
      exact Nat.mul_left_cancel pos (by simpa using g)
    have same := scale_row pos eq' g'
    simp only [mem_product,mem_range,Nat.lt_succ_iff] at mem
    exact ⟨(x',y'), by
      simp only [mem_product,mem_range,Nat.lt_succ_iff]
      exact ⟨Nat.le_of_mul_le_mul_left mem.1 pos,Nat.le_of_mul_le_mul_left mem.2 pos⟩,
      by rwa [same],rfl⟩
  · rintro ⟨x,y⟩ _ nz
    obtain ⟨z,eq,g⟩ := layerRow_nonzero nz
    exact scale_row pos eq g

theorem layer_one (n : ℕ) : layer n 1=count n true := by
  simp [layer, Finset.sum_product, layerRow, count, PrimeFactors.ThreeSquareRadiusCounts.slice,
    content]

private theorem prime_partition {p : ℕ} (pp : p.Prime) :
    count p false = count p true+6 := by
  have hp := partition pp.one_lt
  have zero : properCount p=0 := by
    unfold properCount
    apply sum_eq_zero
    intro x _
    apply sum_eq_zero
    intro y _
    dsimp only
    split
    · rename_i yes
      rcases pp.eq_one_or_self_of_dvd _ (content_dvd yes.1) with h | h <;> omega
    · rfl
  omega

/-- At a product of two distinct primes each proper-gcd layer is a rescaled
primitive sphere at the complementary prime. -/
theorem proper_layers {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) :
    properCount (p*q)=count p true+count q true := by
  have hp := scale q p pp.pos
  have hq := scale p q qp.pos
  rw [layer_one] at hp hq
  rw [Nat.mul_comm q p] at hq
  rw [hp,hq]
  simp only [properCount, layer, sum_product, ←sum_add_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  simp only [layerRow]
  generalize ((p*q)^2-x^2-y^2).sqrt=z
  by_cases eq : x^2+y^2+z^2=(p*q)^2
  · have possible := proper_divisor pp qp (content_dvd eq)
    have pl : p<p*q := by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left qp.one_lt pp.pos
    have ql : q<p*q := by simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right pp.one_lt qp.pos
    by_cases gp : content x y z=p
    · simp [eq, gp, pp.one_lt, pl, ne]
    by_cases gq : content x y z=q
    · simp [eq, gq, qp.one_lt, ql, ne.symm]
    have impossible : ¬(1<content x y z ∧ content x y z<p*q) := fun h =>
      (possible h).elim gp gq
    simp [eq,gp,gq,impossible]
  · simp [eq]

/-- The general total-count formula suffices to derive the primitive formula
at products of distinct odd primes, by removing the two scaled layers and axes. -/
theorem gauss_of_hurwitz {p q : ℕ} (total : HurwitzFormula)
    (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (op : Odd p) (oq : Odd q) :
    GaussFormula p q := by
  have large : 1<p*q := Nat.one_lt_mul_iff.mpr ⟨pp.pos,qp.pos,Or.inl pp.one_lt⟩
  have part := partition large
  rw [proper_layers pp qp ne] at part
  have joined : (count (p*q) false : ℤ) = count (p*q) true +
      (count p true + count q true) + 6 := by exact_mod_cast part
  have ppart : (count p false : ℤ) = count p true + 6 := by exact_mod_cast prime_partition pp
  have qpart : (count q false : ℤ) = count q true + 6 := by exact_mod_cast prime_partition qp
  rw [total p op, PrimeFactors.ThreeSquareRadiusCounts.euler_prime pp] at ppart
  rw [total q oq, PrimeFactors.ThreeSquareRadiusCounts.euler_prime qp] at qpart
  rw [semiprime_total total pp qp ne op oq] at joined
  unfold GaussFormula
  linarith only [ppart,qpart,joined]

/-- Exact count after substituting the two classical representation formulas. -/
theorem proper_semiprime {p q : ℕ} (total : HurwitzFormula) (primitive : GaussFormula p q)
    (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (op : Odd p) (oq : Odd q) :
    (properCount (p*q) : ℤ)=6*((p:ℤ)+q-sign p-sign q) := by
  have large : 1<p*q := Nat.one_lt_mul_iff.mpr ⟨pp.pos,qp.pos,Or.inl pp.one_lt⟩
  have h : (count (p*q) false : ℤ)=count (p*q) true+properCount (p*q)+6 := by
    exact_mod_cast partition large
  rw [semiprime_total total pp qp ne op oq, primitive] at h
  linarith only [h]

/-- Probability under the uniform distribution on ordered, signed sphere
points, assuming the classical formulas. The bound includes all signs and axes. -/
theorem rate_lt_reciprocals {p q : ℕ} (total : HurwitzFormula)
    (primitive : GaussFormula p q) (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (op : Odd p) (oq : Odd q) :
    (properCount (p*q) : ℚ)/count (p*q) false < 1/(p:ℚ)+1/(q:ℚ) := by
  let A : ℚ := (p:ℚ)+1-(sign p:ℤ)
  let B : ℚ := (q:ℚ)+1-(sign q:ℤ)
  have leA : (p:ℚ)≤A := by simp only [A,sign]; split <;> norm_num; linarith
  have leB : (q:ℚ)≤B := by simp only [B,sign]; split <;> norm_num; linarith
  have ppos : 0<(p:ℚ) := by exact_mod_cast pp.pos
  have qpos : 0<(q:ℚ) := by exact_mod_cast qp.pos
  have pa := lt_of_lt_of_le ppos leA
  have pb := lt_of_lt_of_le qpos leB
  have c : (count (p*q) false : ℚ)=6*A*B := by
    dsimp only [A,B]
    exact_mod_cast semiprime_total total pp qp ne op oq
  have r : (properCount (p*q) : ℚ)=6*(A+B-2) := by
    have hr := proper_semiprime total primitive pp qp ne op oq
    have h : (properCount (p*q) : ℚ)=6*((p:ℚ)+q-(sign p:ℤ)-(sign q:ℤ)) := by
      exact_mod_cast hr
    rw [h]; dsimp only [A,B]; ring
  rw [c,r]
  calc
    _ = (A+B-2)/(A*B) := by field_simp; ring
    _ < (A+B)/(A*B) := (div_lt_div_iff_of_pos_right (mul_pos pa pb)).mpr (by linarith)
    _ = 1/A+1/B := by field_simp; ring
    _ ≤ _ := add_le_add (one_div_le_one_div_of_le ppos leA)
                        (one_div_le_one_div_of_le qpos leB)

/-- For distinct odd primes in increasing order, the chance of seeing a proper
gcd is less than twice the reciprocal of the smaller prime. -/
theorem rate_lt_two {p q : ℕ} (total : HurwitzFormula) (primitive : GaussFormula p q)
    (pp : p.Prime) (qp : q.Prime) (lt : p<q) (op : Odd p) (oq : Odd q) :
    (properCount (p*q) : ℚ)/count (p*q) false < 2/(p:ℚ) := by
  have h := rate_lt_reciprocals total primitive pp qp lt.ne op oq
  have bound : 1/(q:ℚ)≤1/(p:ℚ) := one_div_le_one_div_of_le
    (by exact_mod_cast pp.pos) (by exact_mod_cast lt.le)
  linarith [show 2/(p:ℚ)=1/p+1/p by ring]

/-- The smaller-prime sampling bound with just the single, all-odd-radii
Hurwitz count as an external mathematical input. -/
theorem rate_of_hurwitz {p q : ℕ} (total : HurwitzFormula) (pp : p.Prime)
    (qp : q.Prime) (lt : p<q) (op : Odd p) (oq : Odd q) :
    (properCount (p*q) : ℚ)/count (p*q) false < 2/(p:ℚ) :=
  rate_lt_two total (gauss_of_hurwitz total pp qp lt.ne op oq) pp qp lt op oq

/-- Direct checks at radius 15, independent of the classical count assumptions. -/
theorem toy : count 15 false=150 ∧ count 15 true=96 ∧ properCount 15=48 := by
  obtain ⟨total, primitive⟩ := toy_fifteen
  exact ⟨total, primitive, by rw [properCount_eq (by decide), total, primitive]⟩

end PrimeFactors.ThreeSquarePointDensity
