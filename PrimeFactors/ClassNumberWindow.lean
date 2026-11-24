import PrimeFactors.Fermat
import Mathlib.GroupTheory.OrderOfElement

namespace PrimeFactors

/-- The symmetric reduced-form candidate of discriminant -pq encodes both
factors explicitly. For odd primes with pq = 3 mod 4 the sum is divisible by 4. -/
theorem balanced_symmetric_form {p q : ℕ} (ordered : p < q) (balance : q ≤ 2*p)
    (sum4 : 4 ∣ p+q) :
    let a := (p+q)/4
    let b := (q-p)/2
    b ≤ a ∧ 2*a-b=p ∧ 2*a+b=q ∧ 4*a^2=p*q+b^2 := by
  obtain ⟨s, hs⟩ := sum4
  let a := (p+q)/4
  let b := (q-p)/2
  have sum : 4*a=p+q := by dsimp [a]; omega
  have diff : 2*b+p=q := by dsimp [b]; omega
  change b ≤ a ∧ 2*a-b=p ∧ 2*a+b=q ∧ 4*a^2=p*q+b^2
  have pa : p+b=2*a := by omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [← diff]
  nlinarith only [congrArg (fun x : ℕ => x^2) pa]

/-- If an element is killed by a power of two, its last nonidentity square has
order two. Finding it needs no factorization of the odd part of a group order. -/
private theorem last_nontrivial_square {G : Type*} [Monoid G] (x : G) (nontrivial : x ≠ 1)
    {v : ℕ} (killed : x^(2^v) = 1) :
    ∃ j < v, x^(2^j) ≠ 1 ∧ (x^(2^j))^2 = 1 := by
  induction v with
  | zero => simp [nontrivial] at killed
  | succ v ih =>
    by_cases earlier : x^(2^v)=1
    · obtain ⟨j,hj,non,sq⟩ := ih earlier
      exact ⟨j,Nat.lt_succ_of_lt hj,non,sq⟩
    · exact ⟨v,Nat.lt_succ_self _,earlier,by rw [←pow_mul, ←pow_succ]; exact killed⟩

/-- A public form in a negative genus-character class works with any
annihilating exponent found in a class-number interval. The genus character is
used only as a hypothesis proving that repeated squaring will reach an involution. -/
theorem involution_of_genus_annihilator {G : Type*} [Monoid G] (χ : G →* ℤ) (g : G)
    (genus : χ g = -1) {u v : ℕ} (odd : Odd u) (ann : g^(u*2^v)=1) :
    ∃ j < v, (g^u)^(2^j) ≠ 1 ∧ ((g^u)^(2^j))^2=1 := by
  apply last_nontrivial_square
  · intro trivial
    have signs := congrArg χ trivial
    rw [map_pow, map_one, genus, odd.neg_one_pow] at signs
    norm_num at signs
  · simpa only [pow_mul] using ann

/-- In a rank-two 2-group calculation, a shared last involution can be
cancelled. The new power vanishes one squaring earlier and the new element
still lies outside the cyclic group spanned by x. -/
theorem cancel_shared_involution {G : Type*} [CommGroup G] (x z : G) (j c : ℕ)
    (same : z^(2^j) = x^(2^(j+c))) (ann : x^(2^(j+c+1)) = 1)
    (outside : z ∉ Subgroup.zpowers x) :
    (z*x^(2^c))^(2^j) = 1 ∧ z*x^(2^c) ∉ Subgroup.zpowers x := by
  constructor
  · rw [mul_pow, ←pow_mul, show 2^c*2^j=2^(j+c) by rw [←pow_add, Nat.add_comm c j],
      same, ←pow_two, ←pow_mul, ←pow_succ]
    exact ann
  · intro mem
    have hx := (Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) (2^c)
    exact outside (by simpa using (Subgroup.zpowers x).mul_mem mem ((Subgroup.zpowers x).inv_mem hx))

/-- A group order in an integer window supplies a baby-step/giant-step match;
any match in positive exponents gives an annihilator of the chosen element. -/
theorem class_window_match {G : Type*} [Group G] [Fintype G] (g : G) (L m : ℕ)
    (width : 0 < m) (start : L ≤ Fintype.card G) :
    let h := Fintype.card G
    let i := (h-L)/m
    let j := (h-L)%m
    j < m ∧ g^(L+m*i) = (g^j)⁻¹ := by
  dsimp only
  refine ⟨Nat.mod_lt _ width, ?_⟩
  have div := Nat.div_add_mod (Fintype.card G-L) m
  have hit : L+m*((Fintype.card G-L)/m)+(Fintype.card G-L)%m=Fintype.card G := by omega
  apply eq_inv_of_mul_eq_one_left
  rw [←pow_add, hit, pow_card_eq_one]

private def reducedFormCountAt (n a : ℕ) : ℕ :=
  ((List.range (a+1)).map fun b =>
    let c := (b^2+n)/(4*a)
    if 4*a*c != b^2+n || c < a || (Nat.gcd a (Nat.gcd b c)) != 1 then 0
    else if b == 0 || b == a || a == c then 1 else 2).sum

/-- For discriminant -143 the positive reduced-form leading coefficient is at
most 6. Boundary-identified signs give 10 representatives in all. -/
theorem reduced_counts_143 :
    ([1,2,3,4,5,6].map (reducedFormCountAt 143)) = [1,2,2,2,0,3] ∧
    143=11*13 ∧ 2*6-1=(11:ℕ) ∧ 2*6+1=(13:ℕ) := by decide +kernel

/-- For -391 the count is 14, so the principal genus has odd order 7.
The first split prime 2 lies in that genus. -/
theorem reduced_counts_391 :
    ((List.range 11).map (fun a => reducedFormCountAt 391 (a+1))) =
      [1,2,0,2,2,0,2,2,0,3,0] ∧ 391=17*23 ∧
      2*10-3=(17:ℕ) ∧ 2*10+3=(23:ℕ) := by decide +kernel

set_option maxRecDepth 4096 in
/-- The class representatives for -24511 number 50. Here all primes up to
the proposed Euler cutoff of 102 are smaller than either factor. -/
theorem reduced_count_24511 :
    ((List.range 90).map (fun a => reducedFormCountAt 24511 (a+1))).sum = 50 ∧
    24511=127*193 ∧ 102<(127:ℕ) := by decide +kernel

end PrimeFactors
