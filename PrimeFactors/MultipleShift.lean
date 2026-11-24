import PrimeFactors.DiscriminantPencil

namespace PrimeFactors

private theorem multiple_shift_index {p q c d r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (different : p ≠ q) (denpos : 0 < d) (root : (2*d*p+c*(p*q))*(2*d*q+c*(p*q)) = r*r) :
    ∃ j : ℕ, 0 < j ∧ (4*d^2)*(p*q) ≤ ((p*q)*j)^2 ∧ (p*q)*j ≤ d*(p+q) ∧
      (p*q)*j*(2*c+j) = 4*d^2+2*c*d*(p+q) := by
  let n := p*q
  let k := c*n
  change (2*d*p+k)*(2*d*q+k) = r*r at root
  have pd : p ∣ r*r := root ▸
    (Nat.dvd_add (dvd_mul_left _ _) ((dvd_mul_right p q).trans (dvd_mul_left n c))).trans
      (dvd_mul_right _ _)
  have qd : q ∣ r*r := root ▸
    (Nat.dvd_add (dvd_mul_left _ _) ((dvd_mul_left q p).trans (dvd_mul_left n c))).trans
      (dvd_mul_left _ _)
  have nr : n ∣ r := ((Nat.coprime_primes hp hq).mpr different).mul_dvd_of_dvd_of_dvd
    ((hp.dvd_mul.mp pd).elim id id) ((hq.dvd_mul.mp qd).elim id id)
  have kr : k < r := by
    by_contra! h
    have sq := Nat.mul_le_mul h h
    have a : k < 2*d*p+k := by have pos := Nat.mul_pos (Nat.mul_pos (by decide : 0<2) denpos) hp.pos; omega
    have b : k < 2*d*q+k := by have pos := Nat.mul_pos (Nat.mul_pos (by decide : 0<2) denpos) hq.pos; omega
    nlinarith only [sq,root,Nat.mul_lt_mul'' a b]
  have top : r ≤ k+d*(p+q) := by
    by_contra! h
    have sq := Nat.mul_lt_mul'' h h
    zify at sq root
    nlinarith only [sq,root,sq_nonneg ((d:ℤ)*p-d*q)]
  obtain ⟨j,hj⟩ := nr
  change r = n*j at hj
  change c*n < r at kr
  have jmore : c < j := by
    by_contra! bad
    have := Nat.mul_le_mul_right n bad
    rw [mul_comm n j] at hj
    omega
  obtain ⟨i,hi⟩ := Nat.exists_eq_add_of_le jmore.le
  have ipos : 0 < i := by omega
  have eqR : r = k+n*i := by rw [hj, hi, mul_add]; dsimp [k]; ring
  have small : n*i ≤ d*(p+q) := by omega
  have formula : n*i*(2*c+i) = 4*d^2+2*c*d*(p+q) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos hq.pos)
    rw [eqR] at root
    dsimp [k,n] at root ⊢
    nlinarith only [root]
  refine ⟨i, ipos, ?_, small, formula⟩
  change (4*d^2)*n ≤ (n*i)^2
  nlinarith only [congrArg (n * ·) formula, Nat.mul_le_mul_left (2*c*n) small]

/-- If the numerator is a multiple of the squarefree semiprime, a short
denominator puts the cleared root strictly between two successive multiples. -/
theorem multiple_shift_excluded {p q c d : ℕ} (hp : p.Prime) (hq : q.Prime) (different : p ≠ q)
    (denpos : 0 < d) (short : d*(p+q) < p*q) :
    ¬ IsSquare ((2*d*p+c*(p*q))*(2*d*q+c*(p*q))) := by
  rintro ⟨r,root⟩
  obtain ⟨j,jpos,_,small,_⟩ := multiple_shift_index hp hq different denpos root
  have lower := Nat.mul_le_mul_left (p*q) (show 1 ≤ j by omega)
  omega

/-- Every integer multiple of the input is an unsuccessful symmetric shift
for two distinct primes, independent of their balance. -/
theorem integer_multiple_shift_excluded {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (different : p ≠ q) (c : ℕ) : ¬ IsSquare ((2*p+c*(p*q))*(2*q+c*(p*q))) := by
  have p2 := hp.two_le
  have q2 := hq.two_le
  have short : 1*(p+q) < p*q := by
    rcases lt_or_gt_of_ne different with h | h
    · nlinarith [Nat.mul_le_mul (show 2 ≤ p by omega) (show 1 ≤ q-2 by omega),
        Nat.sub_add_cancel q2, congrArg (p * ·) (Nat.sub_add_cancel q2)]
    · nlinarith [Nat.mul_le_mul (show 2 ≤ q by omega) (show 1 ≤ p-2 by omega),
        Nat.sub_add_cancel p2, congrArg (q * ·) (Nat.sub_add_cancel p2)]
  simpa using multiple_shift_excluded (c := c) hp hq different (by decide : 0<1) short

private theorem shift_index_lt_three {p q j d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ord : p < q) (balance : q ≤ 2*p) (den : d ≤ q) (cap : (p*q)*j ≤ d*(p+q)) :
    j < 3 := by
  have strict : q < 2*p := lt_of_le_of_ne balance (by
    intro eq
    have divides : p ∣ q := ⟨2, by rw [eq, mul_comm]⟩
    exact ord.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp divides))
  have bound := Nat.mul_le_mul_right (p+q) den
  by_contra! bad
  nlinarith only [Nat.mul_le_mul_left (p*q) bad, Nat.mul_lt_mul_of_pos_left strict hq.pos, bound, cap]

/-- With denominator ceil(sqrt N), every positive rational shift cN/d fails
on distinct balanced primes. The normalized root gap lies strictly between
the consecutive integers two and three. -/
theorem ceiling_multiple_shift_excluded {p q c : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ord : p < q) (balance : q ≤ 2*p) :
    let d := ceilSqrt (p*q)
    ¬ IsSquare ((2*d*p+c*(p*q))*(2*d*q+c*(p*q))) := by
  let n := p*q
  let d := ceilSqrt n
  have npos : 0 < n := Nat.mul_pos hp.pos hq.pos
  have dceil : n ≤ d^2 := ceilSqrt_le_iff.mp le_rfl
  have dq : d ≤ q := ceilSqrt_le_iff.mpr (by dsimp [n]; nlinarith [Nat.mul_le_mul_right q ord.le])
  have dpos : 0 < d := by by_contra! h; have := Nat.eq_zero_of_le_zero h; simp_all
  have strict : n < d^2 := lt_of_le_of_ne dceil (by
    intro eq
    have dp : p ∣ d := hp.dvd_of_dvd_pow (eq ▸ (show p ∣ n from dvd_mul_right p q))
    have eqd : q ∣ d := hq.dvd_of_dvd_pow (eq ▸ (show q ∣ n from dvd_mul_left q p))
    have nd : n ∣ d := ((Nat.coprime_primes hp hq).mpr ord.ne).mul_dvd_of_dvd_of_dvd dp eqd
    have too := Nat.le_of_dvd dpos nd
    dsimp [n] at too
    nlinarith [Nat.mul_lt_mul_of_pos_right hp.one_lt hq.pos])
  change ¬ IsSquare ((2*d*p+c*n)*(2*d*q+c*n))
  rintro ⟨r,root⟩
  obtain ⟨j,_,lower,cap,_⟩ := multiple_shift_index hp hq ord.ne dpos root
  have below := shift_index_lt_three hp hq ord balance dq cap
  change 4*d^2*n ≤ (n*j)^2 at lower
  have upper := Nat.pow_le_pow_left (Nat.mul_le_mul_left n (show j ≤ 2 by omega)) 2
  nlinarith only [lower, upper, Nat.mul_lt_mul_of_pos_right strict npos]

/-- At denominator floor(sqrt N), a successful shift forces the true sum to
within eight of twice the floor. Thus four extra Fermat midpoint tests cover
all successes for odd balanced inputs, even when the numerator is arbitrary cN. -/
theorem floor_multiple_shift_near_fermat {p q c : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ord : p < q) (balance : q ≤ 2*p) (positive : 0 < c) :
    let d := (p*q).sqrt
    IsSquare ((2*d*p+c*(p*q))*(2*d*q+c*(p*q))) → p+q ≤ 2*d+8 := by
  let n := p*q
  let d := n.sqrt
  have dlow : p ≤ d := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p ord.le)
  have dpos : 0 < d := hp.pos.trans_le dlow
  have dq : d ≤ q := (Nat.sqrt_le_sqrt (Nat.mul_le_mul_right q ord.le)).trans_eq (Nat.sqrt_eq q)
  have near : n ≤ d*d+d+d := Nat.sqrt_le_add n
  change IsSquare ((2*d*p+c*n)*(2*d*q+c*n)) → p+q ≤ 2*d+8
  rintro ⟨r,root⟩
  obtain ⟨j,jpos,large,cap,eq⟩ := multiple_shift_index hp hq ord.ne dpos root
  have upper := shift_index_lt_three hp hq ord balance dq cap
  have jtwo : j = 2 := by
    by_contra! bad
    have one : j=1 := by omega
    rw [one, mul_one] at large
    have npos : 0<n := Nat.mul_pos hp.pos hq.pos
    have nle : n ≤ 2*d^2 := by
      dsimp [n]
      nlinarith only [Nat.mul_le_mul_left p balance, Nat.pow_le_pow_left dlow 2]
    change 4*d^2*n ≤ n^2 at large
    nlinarith only [large, Nat.mul_lt_mul_of_pos_right (show n < 4*d^2 by nlinarith [sq_pos_of_pos dpos]) npos]
  change n*j*(2*c+j) = 4*d^2+2*c*d*(p+q) at eq
  rw [jtwo] at eq
  by_contra! bad
  have extra := Nat.mul_lt_mul_of_pos_left bad (Nat.mul_pos positive dpos)
  have rem := Nat.mul_le_mul_left c near
  nlinarith only [eq,extra,near,rem, Nat.mul_le_mul_right d (show 1 ≤ c by omega)]

end PrimeFactors
