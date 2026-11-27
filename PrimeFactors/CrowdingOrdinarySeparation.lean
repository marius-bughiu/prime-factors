import PrimeFactors.WeightedPrimeCrowding
import PrimeFactors.OffsetSquareSplit
import PrimeFactors.Fermat

/-! Every off-diagonal weighted-prime collision in the specified pool beats
all ordinary traces in a long initial interval, even without a residue sieve. -/
namespace PrimeFactors.CrowdingOrdinarySeparation

open WeightedPrimeCrowding Finset
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

private abbrev U : ℕ := 2^1024
private abbrev H : ℕ := 2^516
private abbrev G : ℕ := 2^1014
private abbrev D : ℕ := 2^1002

/-- Even an adjacent pair of weights forces more than 2^1014 separation
between the two primes if their weighted values fall in one bucket. -/
theorem prime_gap {a b p q : ℕ} (small : a<576) (order : a<b)
    (qlo : 3*U/4≤q) (near : b*q<a*p+H) : q+G<p := by
  by_contra! close
  have left := Nat.mul_le_mul_right q (show a+1≤b from order)
  have right := Nat.mul_le_mul_left a close
  have cap := Nat.mul_le_mul_right G small.le
  rw [Nat.add_mul,Nat.one_mul] at left
  rw [Nat.mul_add] at right
  have room : 576*G+H ≤ 3*U/4 := by decide +kernel
  omega

private theorem ordinary_gap {p q : ℕ} (gap : q+G<p)
    (highP : p≤7*U/8) (highQ : q≤7*U/8) :
    ceilSqrt (4*(p*q))+D≤p+q := by
  have enough : D ≤ p+q := by
    have : D≤G := by decide +kernel
    omega
  have sd' : (q:ℤ)+(G:ℤ)<p := by exact_mod_cast gap
  have sd : (G:ℤ)≤(p:ℤ)-q := by omega
  have sq := pow_le_pow_left₀ (show 0≤(G:ℤ) by positivity) sd 2
  have pbound : (p:ℤ)≤((7*U/8:ℕ):ℤ) := by exact_mod_cast highP
  have qbound : (q:ℤ)≤((7*U/8:ℕ):ℤ) := by exact_mod_cast highQ
  have cap := mul_le_mul_of_nonneg_right (add_le_add pbound qbound) (show 0≤2*(D:ℤ) by positivity)
  have slack : (2*(D:ℤ))*(((7*U/8:ℕ):ℤ)+((7*U/8:ℕ):ℤ))≤(G:ℤ)^2 := by decide +kernel
  have test : 4*(p*q)≤(p+q-D)^2 := by
    zify
    rw [Nat.cast_sub enough,Nat.cast_add]
    nlinarith only [sq,cap,slack,sq_nonneg (D:ℤ)]
  have good := ceilSqrt_le_iff.mpr test
  omega

/-- An ordinary square for the product of two primes can only be their
sum or the trivial sum 1+N. Both labels are at least p+q. -/
theorem ordinary_square {p q t d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (sq : t^2=4*(p*q)+d^2) : t=p+q ∨ t=1+p*q := by
  obtain ⟨sum,mul⟩ := OffsetSquareSplit.root_identities (k:=1) (N:=p*q) (by simpa using sq)
  simp only [one_pow,mul_one] at mul
  let x := (t+d)/2
  let y := (t-d)/2
  change x*y=p*q at mul
  change x+y=t at sum
  have f {x y : ℕ} (px : p∣x) (prod : x*y=p*q) : x+y=p+q ∨ x+y=1+p*q := by
    obtain ⟨j,rfl⟩ := px
    have split := Nat.eq_of_mul_eq_mul_left hp.pos (Nat.mul_assoc p j y ▸ prod)
    rcases hq.eq_one_or_self_of_dvd j (split ▸ dvd_mul_right j y) with e|e
    · subst j
      simp_all
    · subst j
      have y1 : y=1 := Nat.eq_of_mul_eq_mul_left hq.pos (by simpa using split)
      right
      rw [y1,add_comm]
  have divisor : p∣x*y := mul ▸ dvd_mul_right p q
  rcases hp.dvd_mul.mp divisor with l|r
  · simpa only [sum] using f l mul
  · rw [←sum, Nat.add_comm x y]
    exact f r (Nat.mul_comm x y ▸ mul)

/-- No square at any of the first 2^1002 consecutive integer labels, counting
from ceil(2 sqrt(pq)). This also rules out every proper square at those labels. -/
theorem early_absence {a b p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ab : a≠b) (aHi : a<576) (bHi : b<576)
    (pLo : 3*U/4≤p) (pHi : p≤7*U/8) (qLo : 3*U/4≤q) (qHi : q≤7*U/8)
    (near₁ : a*p<b*q+H) (near₂ : b*q<a*p+H) :
    ceilSqrt (4*(p*q))+2^1002 ≤ p+q ∧
    ∀ i<2^1002, ∀ d : ℕ, (ceilSqrt (4*(p*q))+i)^2 ≠ 4*(p*q)+d^2 := by
  have sep : ceilSqrt (4*(p*q))+D ≤ p+q := by
    rcases lt_or_gt_of_ne ab with lt|gt
    · exact ordinary_gap (prime_gap aHi lt qLo near₂) pHi qHi
    · simpa only [Nat.mul_comm q p,Nat.add_comm q p] using ordinary_gap (prime_gap bHi gt pLo near₁) qHi pHi
  refine ⟨sep,?_⟩
  intro i small d sq
  change i<D at small
  have lo : p+q≤1+p*q := by
    have pl : (1:ℤ)≤p := by exact_mod_cast hp.pos
    have ql : (1:ℤ)≤q := by exact_mod_cast hq.pos
    zify
    nlinarith only [mul_nonneg (sub_nonneg.mpr pl) (sub_nonneg.mpr ql)]
  rcases ordinary_square hp hq sq with e|e <;> omega

private theorem bucket_gap {c h x y : ℕ} (hp : 0<h) (xl : c≤x) (yl : c≤y)
    (eq : (x-c)/h=(y-c)/h) : x<y+h := by
  have xr := Nat.mod_add_div (x-c) h
  have yr := Nat.mod_add_div (y-c) h
  have rem := Nat.mod_lt (x-c) hp
  rw [eq] at xr
  omega

/-- Every actual collision in the public menu has the separation, with no
statistical or analytic assumptions. -/
theorem collision {a b p q : ℕ} (hit : ((a,p),(b,q))∈hits) :
    ceilSqrt (4*(p*q))+2^1002 ≤ p+q ∧
    ∀ i<2^1002, ∀ d : ℕ, (ceilSqrt (4*(p*q))+i)^2 ≠ 4*(p*q)+d^2 := by
  have data : ((a,p)∈points ∧ (b,q)∈points) ∧
      bucket (a,p)=bucket (b,q) ∧ a≠b := by
    simpa only [hits,collisions,mem_filter,mem_product,and_assoc] using hit
  have info {x y : ℕ} (h : (x,y)∈points) :
      (512≤x ∧ x<576) ∧ (3*U/4≤y ∧ y≤7*U/8) ∧ y.Prime := by
    simpa [points,weights_def,pool_def,and_assoc] using h
  obtain ⟨⟨al,ah⟩,⟨pl,ph⟩,pp⟩ := info data.1.1
  obtain ⟨⟨bl,bh⟩,⟨ql,qh⟩,qp⟩ := info data.1.2
  have base : 384*U≤512*(3*U/4) := by decide +kernel
  have left := base.trans (Nat.mul_le_mul al pl)
  have right := base.trans (Nat.mul_le_mul bl ql)
  exact early_absence pp qp data.2.2 ah bh pl ph ql qh
    (bucket_gap (by decide : 0<H) left right data.2.1)
    (bucket_gap (by decide : 0<H) right left data.2.1.symm)

/-- The entire set of previously counted 2048-bit products is missed by
ordinary Fermat for this many consecutive traces. -/
theorem products_missed {n : ℕ} (hn : n∈products) :
    ∀ i<2^1002, ∀ d : ℕ, (ceilSqrt (4*n)+i)^2 ≠ 4*n+d^2 := by
  obtain ⟨⟨⟨a,p⟩,b,q⟩,hit,rfl⟩ := Finset.mem_image.mp hn
  exact (collision hit).2

/-- The standard Fermat loop tests m^2-N for m starting at ceil(sqrt N).
It misses all the first 2^1001 midpoint tests on every counted product. -/
theorem midpoints_missed {n : ℕ} (hn : n∈products) :
    ∀ i<2^1001, ∀ d : ℕ, (ceilSqrt n+i)^2 ≠ n+d^2 := by
  let c := ceilSqrt (4*n)
  let m := ceilSqrt n
  have C : 4*n≤c^2 := ceilSqrt_le_iff.mp le_rfl
  have M : n≤m^2 := ceilSqrt_le_iff.mp le_rfl
  have low : c≤2*m := ceilSqrt_le_iff.mpr (by nlinarith only [M])
  have e : c≤2*((c+1)/2) := by omega
  have high : m≤(c+1)/2 := ceilSqrt_le_iff.mpr (by
    nlinarith only [C,Nat.pow_le_pow_left e 2])
  intro i small d square
  have budget : 2*2^1001=(2:ℕ)^1002 := by decide +kernel
  let j := 2*(m+i)-c
  have jj : c+j=2*(m+i) := by dsimp only [j]; omega
  have js : j < 2^1002 := by rw [←budget]; omega
  have miss := products_missed hn j js (2*d)
  change (c+j)^2≠4*n+(2*d)^2 at miss
  rw [jj] at miss
  exact miss (by change (m+i)^2=n+d^2 at square; nlinarith only [square])

end PrimeFactors.CrowdingOrdinarySeparation
