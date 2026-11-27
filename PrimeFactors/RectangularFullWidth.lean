import PrimeFactors.MixedUnityCofactors
import PrimeFactors.CubicForcedParameters

/-! Uniform finite D=1 multiplier count for products with exactly 2048
bits. The numerator/denominator and natural subtraction below implement
the integer ceiling used by the public weight filter. -/
namespace PrimeFactors.RectangularFullWidth

set_option exponentiation.threshold 4096

def upperPrime : ℕ := 2^1024-1
noncomputable def B (N : ℕ) := max (N/CubicForcedParameters.ceilCube N) (N.sqrt+1)
noncomputable def H (N : ℕ) := N/(B N+1)
noncomputable def K (N : ℕ) := B N^2/N
noncomputable def numerator (N : ℕ) := 1024*upperPrime^2*(N.sqrt+H N)
noncomputable def denominator (N : ℕ) := N*(N.sqrt-H N)
noncomputable def excess (N : ℕ) :=
  (numerator N+denominator N-1)/denominator N-1024

/-- Coarse powers of two suffice to absorb all rounding errors in the
rectangle and the final product-count bound. -/
theorem dimensions {N : ℕ} (lo : 2^2047≤N) (hi : N<2^2048) :
    2^682≤CubicForcedParameters.ceilCube N ∧ CubicForcedParameters.ceilCube N≤2^683 ∧
    2^1364≤B N ∧ B N≤2^1366 ∧ H N<2^683 ∧ 2^680≤K N ∧ 2^1023≤N.sqrt := by
  let T := CubicForcedParameters.ceilCube N
  have tmax : T≤2^683 := Nat.find_min' (p:=fun v : ℕ => N≤v^3) _ (by omega)
  have reached : N≤T^3 := Nat.find_spec (p:=fun v : ℕ => N≤v^3) _
  have tmin : 2^682≤T := by
    by_contra! small
    have lt := Nat.pow_le_pow_left small.le 3
    omega
  have tp : 0<T := by omega
  have smin : 2^1023≤N.sqrt := Nat.le_sqrt.mpr (by omega)
  have smax : N.sqrt<2^1024 := by
    by_contra! large
    have := Nat.pow_le_pow_left large 2
    have := Nat.sqrt_le' N
    omega
  have bmin : 2^1364≤B N := by
    apply le_trans _ (le_max_left ..)
    apply (Nat.le_div_iff_mul_le tp).mpr
    exact (Nat.mul_le_mul_left (2^1364) tmax).trans (by omega)
  have bmax : B N≤2^1366 := by
    apply max_le _ (by omega)
    by_contra! large
    change 2^1366<N/T at large
    have ob := Nat.div_mul_le_self N T
    have lim := Nat.mul_le_mul large.le tmin
    omega
  have hl : H N<T := by
    apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ (B N))).mpr
    rw [Nat.mul_comm T]
    apply (Nat.div_lt_iff_lt_mul tp).mp
    have : N/T≤B N := le_max_left ..
    omega
  have kl : 2^680≤K N := by
    apply (Nat.le_div_iff_mul_le (by omega : 0<N)).mpr
    exact (Nat.mul_le_mul_left (2^680) hi.le).trans (by
      have t := Nat.pow_le_pow_left bmin 2
      omega)
  exact ⟨tmin,tmax,bmin,bmax,hl.trans_le tmax,kl,smin⟩

private theorem ceiling {A D c : ℕ} (dp : 0<D) (cap : A≤c*D) :
    A≤((A+D-1)/D)*D ∧ (A+D-1)/D≤c := by
  have d := Nat.mod_add_div (A+D-1) D
  have m := Nat.mod_lt (A+D-1) dp
  rw [mul_comm D] at d
  constructor
  · omega
  · have : (A+D-1)/D<c+1 := (Nat.div_lt_iff_lt_mul dp).mpr (by
      rw [Nat.add_mul,one_mul]
      omega)
    omega

/-- The rounded ratio is computed from N alone, and its excess above
scale 1024 never exceeds 1025 over the whole 2048-bit interval. -/
theorem excess_bound {N : ℕ} (lo : 2^2047≤N) (hi : N<2^2048) :
    excess N≤1025 ∧ 1024*(upperPrime^2*(N.sqrt+H N))≤
      (1024+excess N)*(N*(N.sqrt-H N)) := by
  obtain ⟨_,_,_,_,hh,_,ss⟩ := dimensions lo hi
  have tiny : 4097*H N≤N.sqrt := by omega
  have hp : H N < N.sqrt := by omega
  have dp : 0<denominator N := Nat.mul_pos (by omega) (Nat.sub_pos_of_lt hp)
  have umax : upperPrime^2≤2*N := by dsimp [upperPrime]; omega
  have rSub := Nat.sub_add_cancel hp.le
  have squeeze : 2048*(N.sqrt+H N) ≤ 2049*(N.sqrt-H N) := by omega
  have cap : numerator N≤2049*denominator N := calc
    numerator N = upperPrime^2*(1024*(N.sqrt+H N)) := by unfold numerator; ring
    _ ≤ (2*N)*(1024*(N.sqrt+H N)) := Nat.mul_le_mul_right _ umax
    _ = N*(2048*(N.sqrt+H N)) := by ring
    _ ≤ N*(2049*(N.sqrt-H N)) := Nat.mul_le_mul_left _ squeeze
    _ = 2049*denominator N := by unfold denominator; ring
  obtain ⟨up,ub⟩ := ceiling dp cap
  have lim : (numerator N+denominator N-1)/denominator N≤1024+excess N := by
    unfold excess
    omega
  refine ⟨by unfold excess; omega, ?_⟩
  simpa only [numerator,denominator,mul_assoc] using
    up.trans (Nat.mul_le_mul_right (denominator N) lim)

/-- This bounds the full candidate table, including its entries above
the cap. Empty coordinate intervals can reduce the work further. -/
theorem count_at_scale {limit e : ℕ} (large : 2^680≤limit) (ex : e≤1025) :
    1000000*(RectangularMultiplierCount.allowed limit 1024 e).card ≤ 187684*limit := by
  let Q := limit.sqrt
  let L := (Q+1)/2
  let T := (limit/4).sqrt
  let C := (RectangularMultiplierCount.allowed limit 1024 e).card
  have raw : 4096*C ≤ 4096*(L+T)+2*e*L^2+e*T*(T+1) :=
    RectangularMultiplierCount.bound limit 1024 e
  have qlo : 2^340≤Q := Nat.le_sqrt.mpr (by omega)
  have qcap : Q^2≤limit := Nat.sqrt_le' _
  have ll : 2*L≤Q+1 := by dsimp [L]; omega
  have tt : 2*T≤Q := by
    apply Nat.le_sqrt.mpr
    have s : T^2≤limit/4 := Nat.sqrt_le' _
    have := (Nat.le_div_iff_mul_le (by decide : 0<4)).mp s
    nlinarith only [this]
  have oddSq := Nat.pow_le_pow_left ll 2
  have evenProd := Nat.mul_le_mul tt (Nat.add_le_add_right tt 2)
  have oddEx := Nat.mul_le_mul_right (L^2) ex
  have evenEx := Nat.mul_le_mul_right (T*(T+1)) ex
  have full : 16384*C ≤ 3075*Q^2+22534*Q+10242 := by
    nlinarith only [raw,ll,tt,oddSq,evenProd,oddEx,evenEx]
  have qmed : 2^21≤Q := by omega
  have tail : 1000000*(22534*Q+10242) ≤ 14656*Q^2 := by
    have sq := Nat.mul_le_mul_right Q qmed
    nlinarith only [sq,qmed]
  have final : 16384*(1000000*C) ≤ 16384*(187684*limit) := by
    nlinarith only [full,tail,qcap]
  exact Nat.le_of_mul_le_mul_left final (by decide)

/-- On every balanced 2048-bit product of distinct primes, the public
filter keeps a proper-gcd row and admits at most 187684 rows per million.
The remaining denominator search in each admitted row is explicit. -/
theorem full_width {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q)
    (pl : 2^1023≤p) (qu : q<2^1024) (lo : 2^2047≤p*q) (hi : p*q<2^2048) :
    let N := p*q
    let rows := RectangularMultiplierCount.allowed (K N) 1024 (excess N)
    excess N≤1025 ∧ 1000000*rows.card≤187684*K N ∧
    ∃ k ∈ rows, ∃ x y : ℕ, 0<k ∧ 0<y ∧ y≤B N ∧ x≤H N ∧ x.Coprime y ∧
      y^2=x^2+k*N ∧ 1<(y-x).gcd N ∧ (y-x).gcd N<N ∧ (y-x).gcd N∣N := by
  dsimp only
  obtain ⟨_,_,bl,bu,hu,kl,ss⟩ := dimensions lo hi
  obtain ⟨em,ratio⟩ := excess_bound lo hi
  refine ⟨em,count_at_scale kl em,?_⟩
  apply MixedUnityCofactors.searched_split pp qp lt (by omega)
    (show q≤upperPrime by dsimp [upperPrime]; omega) (by omega)
  · change B (p*q)+H (p*q)<p*q
    omega
  · change H (p*q)<p
    omega
  · change H (p*q)<(p*q).sqrt
    omega
  · decide
  · exact ratio

end PrimeFactors.RectangularFullWidth
