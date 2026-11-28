import PrimeFactors.TransposedRadixProducts

/-! Carry-free digits of a product (Ba+b)(Bb+a), and the resulting equality
of the leading and trailing bits for sufficiently wide binary blocks. -/

namespace PrimeFactors.TransposedProductDigits

open TransposedRadixProducts

set_option exponentiation.threshold 8192

/-- The two outer coefficients in the product are both ab. -/
theorem expansion (B a b : ℕ) :
    (factors B a b).1*(factors B a b).2 = B*(B*(a*b)+(a^2+b^2))+a*b := by
  simp only [factors]
  ring

private theorem outer_le_middle (a b : ℕ) : a*b≤a^2+b^2 := by
  rcases le_total a b with h|h
  · nlinarith only [Nat.mul_le_mul_right b h,Nat.zero_le (a^2)]
  · nlinarith only [Nat.mul_le_mul_left a h,Nat.zero_le (b^2)]

/-- When the middle coefficient fits, the outer one fits as well. All three
digits are then ordinary divisions and remainders of the product. -/
theorem digits {B a b N : ℕ} (prod : (factors B a b).1*(factors B a b).2=N)
    (fit : a^2+b^2<B) :
    N%B=a*b ∧ N/B%B=a^2+b^2 ∧ N/B^2=a*b := by
  have outside := (outer_le_middle a b).trans_lt fit
  have pos : 0<B := by omega
  have fit_mul : a*a+b*b<B := by simpa only [pow_two] using fit
  rw [←prod,expansion]
  simp [pow_two,←Nat.div_div_eq_div_mul, Nat.mul_add_div pos,Nat.mul_add_mod,
    Nat.mod_eq_of_lt outside,Nat.mod_eq_of_lt fit_mul,Nat.div_eq_of_lt outside,Nat.div_eq_of_lt fit_mul]

/-- The two ordinary square roots are the sum and nonnegative difference
of the blocks. -/
theorem roots {B a b N : ℕ} (prod : (factors B a b).1*(factors B a b).2=N)
    (fit : a^2+b^2<B) (ab : a≤b) :
    ((N/B%B)+2*(N%B)).sqrt=a+b ∧ ((N/B%B)-2*(N%B)).sqrt=b-a := by
  obtain ⟨outer,middle,_⟩ := digits prod fit
  rw [outer,middle,show a^2+b^2+2*(a*b)=(a+b)^2 by ring,Nat.sqrt_eq']
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ab
  rw [show a^2+(a+d)^2=2*(a*(a+d))+d^2 by ring,Nat.add_sub_cancel_left,
    Nat.sqrt_eq',Nat.add_sub_cancel_left]
  exact ⟨rfl,rfl⟩

/-- Recover the candidate blocks using the middle digit and the low digit. -/
def blocks (B N : ℕ) : ℕ×ℕ :=
  let P := N%B
  let H := N/B%B
  let sum := (H+2*P).sqrt
  let gap := (H-2*P).sqrt
  ((sum-gap)/2,(sum+gap)/2)

theorem blocks_eq {B a b N : ℕ} (prod : (factors B a b).1*(factors B a b).2=N)
    (fit : a^2+b^2<B) (ab : a≤b) : blocks B N=(a,b) := by
  obtain ⟨sum,gap⟩ := roots prod fit ab
  simp only [blocks,sum,gap]
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

/-- If both factors fit in w bits, their leading base-2^k blocks fit in the
remaining w−k bits. Lower bounds on the factors are unnecessary. -/
theorem block_width {w k a b : ℕ} (kw : k≤w)
    (pfit : (factors (2^k) a b).1<2^w) (qfit : (factors (2^k) a b).2<2^w) :
    a<2^(w-k) ∧ b<2^(w-k) := by
  change 2^k*a+b<2^w at pfit
  change 2^k*b+a<2^w at qfit
  have scale : (2:ℕ)^w=2^k*2^(w-k) := by rw [←pow_add]; congr 1; omega
  rw [scale] at pfit qfit
  exact ⟨Nat.lt_of_mul_lt_mul_left (by omega : 2^k*a<2^k*2^(w-k)),
    Nat.lt_of_mul_lt_mul_left (by omega : 2^k*b<2^k*2^(w-k))⟩

/-- At 3k≥2w+1 the product's middle coefficient cannot carry. Its outer
coefficient uses at most 2(w−k) bits. -/
theorem binary_fit {w k a b : ℕ} (kw : k≤w) (wide : 2*w+1≤3*k)
    (pfit : (factors (2^k) a b).1<2^w) (qfit : (factors (2^k) a b).2<2^w) :
    a^2+b^2<2^k ∧ a*b<2^(2*(w-k)) := by
  obtain ⟨ha,hb⟩ := block_width kw pfit qfit
  have sq : ((2:ℕ)^(w-k))^2=2^(2*(w-k)) := by rw [←pow_mul,Nat.mul_comm (w-k) 2]
  have aa := Nat.pow_lt_pow_left ha (by decide : 2≠0)
  have bb := Nat.pow_lt_pow_left hb (by decide : 2≠0)
  rw [sq] at aa bb
  have d : 2*(w-k)+1≤k := by omega
  have budget : (2:ℕ)^(2*(w-k))*2≤2^k := by
    simpa only [pow_succ] using Nat.pow_le_pow_right (by decide : 0<2) d
  exact ⟨by omega, (Nat.mul_lt_mul_of_lt_of_lt ha hb).trans_eq (by simpa only [pow_two] using sq)⟩

/-- In a 2w-bit product the first and last 2(w−k) bits both equal ab.
The displayed arithmetic also applies when the top word is zero-padded. -/
theorem binary_ends {w k a b N : ℕ} (kw : k≤w) (wide : 2*w+1≤3*k)
    (pfit : (factors (2^k) a b).1<2^w) (qfit : (factors (2^k) a b).2<2^w)
    (prod : (factors (2^k) a b).1*(factors (2^k) a b).2=N) :
    N/2^(2*k)=a*b ∧ N%2^(2*(w-k))=a*b := by
  obtain ⟨fit,narrow⟩ := binary_fit kw wide pfit qfit
  obtain ⟨low,_,high⟩ := digits prod fit
  have divides : (2:ℕ)^(2*(w-k)) ∣ 2^k := Nat.pow_dvd_pow _ (by omega)
  refine ⟨?_,?_⟩
  · simpa only [←pow_mul,Nat.mul_comm k 2] using high
  · rw [←Nat.mod_mod_of_dvd N divides,low,Nat.mod_eq_of_lt narrow]

/-- Each binary radix width from 683 through 1024 obeys the screen for two
factors below 2^1024. A 2048-bit product has exactly the indicated top bits. -/
theorem binary_1024 {k a b N : ℕ} (low : 683≤k) (hi : k≤1024)
    (pfit : (factors (2^k) a b).1<2^1024) (qfit : (factors (2^k) a b).2<2^1024)
    (prod : (factors (2^k) a b).1*(factors (2^k) a b).2=N) :
    N/2^(2*k) = N%2^(2*(1024-k)) := by
  have both := binary_ends hi (by omega) pfit qfit prod
  exact both.1.trans both.2.symm

/-- In the 26-bit product of these two 13-bit primes, the matching top and
bottom bytes are 165. Direct digit operations give the two blocks. -/
theorem hit_26 : Nat.Prime 5647 ∧ Nat.Prime 7691 ∧
    factors 512 11 15=(5647,7691) ∧ 5647*7691=43431077 ∧
    2^25≤43431077 ∧ 43431077<2^26 ∧
    43431077/512^2=165 ∧ 43431077/512%512=346 ∧ 43431077%512=165 ∧
    43431077%256=165 ∧ blocks 512 43431077=(11,15) := by
  refine ⟨by norm_num,by norm_num,?_⟩
  decide +kernel

/-- A different 26-bit product of two 13-bit primes has leading byte 165
and trailing byte 29, so the specified width cannot fit this family. -/
theorem miss_26 : Nat.Prime 5647 ∧ Nat.Prime 7699 ∧ 5647*7699=43476253 ∧
    43476253/2^18=165 ∧ 43476253%2^8=29 ∧
    ¬ ∃ a b, (factors 512 a b).1<2^13 ∧ (factors 512 a b).2<2^13 ∧
      (factors 512 a b).1*(factors 512 a b).2=43476253 := by
  refine ⟨by norm_num,by norm_num,by decide,by decide,by decide,?_⟩
  rintro ⟨a,b,ha,hb,h⟩
  have eq := binary_ends (w:=13) (k:=9) (by decide) (by decide) ha hb h
  have wrong : 43476253/2^(2*9)≠43476253%2^(2*(13-9)) := by decide +kernel
  exact wrong (eq.1.trans eq.2.symm)

end PrimeFactors.TransposedProductDigits
