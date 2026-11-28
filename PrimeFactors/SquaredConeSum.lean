import PrimeFactors.PrimeSquareThreeSquareCone
import PrimeFactors.SemiprimeThreeSquareCone

/-! For two balanced primes the total number of ternary zeroes modulo
the square of their product fixes the integer sum at a specified precision. -/
namespace PrimeFactors.SquaredConeSum

open ThreeSquareCone

/-- Count all ordered triples at the squared modulus, including the origin. -/
noncomputable def count (n : ℕ) [NeZero n] := (points (ZMod (n^2)) 0).card

private theorem congr_count {a b : ℕ} [NeZero a] [NeZero b] (eq : a=b) :
    (points (ZMod a) 0).card=(points (ZMod b) 0).card := by subst b; rfl

/-- The CRT and the exact lift counts at the two prime squares give the
following product expression for the observable. Its factors are unknown. -/
theorem factored {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q)
    (op : p≠2) (oq : q≠2) :
    (count (p*q):ℤ)=(p*q:ℤ)^2*((p:ℤ)^2+p-1)*((q:ℤ)^2+q-1) := by
  have pp : p.Prime := Fact.out
  have qp : q.Prime := Fact.out
  have co := (Nat.coprime_primes pp qp).mpr ne
  have hp : 1≤p^2 := pow_pos pp.pos _
  have hq : 1≤q^2 := pow_pos qp.pos _
  unfold count
  rw [congr_count (mul_pow p q 2),SemiprimeThreeSquareCone.total_mul ((co.pow_left 2).pow_right 2),
    PrimeSquareThreeSquareCone.prime_square p op,PrimeSquareThreeSquareCone.prime_square q oq]
  push_cast [Nat.cast_sub hp,Nat.cast_sub hq]
  ring

private theorem gap_range {p q : ℤ} (large : 5≤p) (order : p≤q) (balanced : q≤2*p) :
    0<(q-p)^2+p+q-1 ∧ (q-p)^2+p+q-1<p*q := by
  have shape := mul_nonneg (sub_nonneg.mpr balanced) (show 0≤2*q-p by omega)
  have margin := mul_nonneg (show 0≤p-5 by omega) (show 0≤q-2 by omega)
  constructor <;> nlinarith [sq_nonneg (q-p)]

attribute [local irreducible] count
private theorem location {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q)
    (op : p≠2) (oq : q≠2) (large : 5≤p) (order : p≤q) (balanced : q≤2*p) :
    let n : ℤ := p*q
    let s : ℤ := p+q
    n^3*(n+s-2)<count (p*q) ∧ (count (p*q):ℤ)<n^3*(n+s-1) := by
  let n : ℤ := p*q
  let s : ℤ := p+q
  let d : ℤ := ((q:ℤ)-p)^2+s-1
  have pn : 0<n := by dsimp [n]; exact_mod_cast Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : q.Prime).pos
  have range : 0<d ∧ d<n := by
    simpa only [d,n,s,add_assoc] using gap_range (p:=(p:ℤ)) (q:=(q:ℤ))
      (by exact_mod_cast large) (by exact_mod_cast order) (by exact_mod_cast balanced)
  have low := mul_lt_mul_of_pos_left range.2 (sq_pos_of_pos pn)
  have high := mul_pos (sq_pos_of_pos pn) range.1
  change n^3*(n+s-2)<count (p*q) ∧ (count (p*q):ℤ)<n^3*(n+s-1)
  have eq : (count (p*q):ℤ)=n^3*(n+s-1)-n^2*d := by
    rw [factored ne op oq]; dsimp [n,s,d]; ring
  rw [eq]; constructor <;> nlinarith only [low,high]

/-- An exact supplied count gives the sum by one division and subtraction. -/
theorem read_sum {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q)
    (op : p≠2) (oq : q≠2) (large : 5≤p) (order : p≤q) (balanced : q≤2*p) :
    let n : ℤ := p*q
    (count (p*q):ℤ)/n^3-n+2=(p:ℤ)+q := by
  let n : ℤ := p*q
  let s : ℤ := p+q
  have pn : 0<n := by dsimp [n]; exact_mod_cast Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : q.Prime).pos
  obtain ⟨a,b⟩ := location ne op oq large order balanced
  change n^3*(n+s-2)<_ at a
  change _<n^3*(n+s-1) at b
  have div : (count (p*q):ℤ)/n^3=n+s-2 := by
    apply (Int.ediv_eq_iff_of_pos (pow_pos pn 3)).mpr
    constructor <;> nlinarith only [a,b]
  change (count (p*q):ℤ)/n^3-n+2=s
  omega

/-- An approximate count also suffices: the permitted absolute error is
half the cube of the modulus base. The proof uses the parity of the sum. -/
theorem read_estimate {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q)
    (op : p≠2) (oq : q≠2) (large : 5≤p) (order : p≤q) (balanced : q≤2*p)
    (v : ℤ) (error : 2*|v-(count (p*q):ℤ)|≤((p:ℤ)*q)^3) :
    let n : ℤ := p*q
    2*((2*v+3*n^3)/(4*n^3))-n+1=(p:ℤ)+q := by
  let n : ℤ := p*q
  let s : ℤ := p+q
  have pn : 0<n := by dsimp [n]; exact_mod_cast Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : q.Prime).pos
  have even : Even (n+s-1) := by
    obtain ⟨a,ha⟩ : Odd (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).odd_of_ne_two op
    obtain ⟨b,hb⟩ : Odd (q:ℤ) := by exact_mod_cast (Fact.out : q.Prime).odd_of_ne_two oq
    exact ⟨2*a*b+2*a+2*b+1,by dsimp [n,s]; rw [ha,hb]; ring⟩
  obtain ⟨k,hk⟩ := even
  obtain ⟨lo,hi⟩ := location ne op oq large order balanced
  change n^3*(n+s-2)<_ at lo
  change _<n^3*(n+s-1) at hi
  have low : n^3*(k+k-1)<count (p*q) := by
    rwa [show k+k-1=n+s-2 by omega]
  rw [hk] at hi
  change 2*|v-(count (p*q):ℤ)|≤n^3 at error
  have a := le_abs_self (v-(count (p*q):ℤ))
  have b := neg_le_abs (v-(count (p*q):ℤ))
  have quotient : (2*v+3*n^3)/(4*n^3)=k := by
    apply (Int.ediv_eq_iff_of_pos (show 0<4*n^3 by positivity)).mpr
    constructor <;> nlinarith only [a,b,error,low,hi]
  change 2*((2*v+3*n^3)/(4*n^3))-n+1=s
  rw [quotient]; omega

/-- The balanced controls give sums 12 and 18. The wider pair at 65
shows the error that can result from dropping the balance hypothesis. -/
theorem examples : count 35=1953875 ∧ (count 35:ℤ)/35^3-35+2=12 ∧
    count 77=42718445 ∧ (count 77:ℤ)/77^3-77+2=18 ∧
    count 65=22177025 ∧ (count 65:ℤ)/65^3-65+2=17 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have a := factored (p:=5) (q:=7) (by decide) (by decide) (by decide)
  have b := factored (p:=7) (q:=11) (by decide) (by decide) (by decide)
  have c := factored (p:=5) (q:=13) (by decide) (by decide) (by decide)
  norm_num at a b c
  norm_num [a,b,c]
  omega

end PrimeFactors.SquaredConeSum
