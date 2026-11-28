import PrimeFactors.Certificate
import PrimeFactors.ComplementaryQuarticProducts

/-! Two synthesized positive controls for the fixed denominator choices 1, 725,
and 1517. Each branch reads only the scaled product. The coordinates below
certify the selected examples and are not an independent sampling experiment. -/
namespace PrimeFactors.ScaledQuarticControls

open RecognizingQuarticProducts ComplementaryQuarticProducts

abbrev N58 : ℕ := 194329760155033121
abbrev N37 : ℕ := 96702339781

private theorem miss_x {n : ℕ} (x y : ℕ)
    (check : (x^4≤n ∧ n<(x+1)^4) ∧ (y^4≤(n-x^4)/4 ∧ (n-x^4)/4<(y+1)^4) ∧ n-x^4≠4*y^4) :
    recognize n=none := by
  rw [recognize,fourthRoot_eq_iff.mpr check.1,fourthRoot_eq_iff.mpr check.2.1]
  simp only [check.2.2,and_false,if_false]

private theorem miss_y {n : ℕ} (y x : ℕ)
    (check : (4*y^4≤n ∧ n<4*(y+1)^4) ∧ (x^4≤n-4*y^4 ∧ n-4*y^4<(x+1)^4) ∧ n-4*y^4≠x^4) :
    recognizeY n=none := by
  rw [recognizeY,quotient_root_iff.mpr check.1,fourthRoot_eq_iff.mpr check.2.1]
  simp only [check.2.2,and_false,if_false]

private theorem read_pair {n : ℕ} {x y : Option (ℕ×ℕ)} (forward : recognize n=x)
    (reverse : recognizeY n=y) : readings n=(x,y) := congrArg₂ Prod.mk forward reverse

attribute [local irreducible] readings recognize recognizeY fourthRoot

/-- Both primes have 29 bits, and their product has 58. The gcd of the product with the denominator is one. -/
theorem data58 : ExactFactorization N58 [362037209,536767369] ∧
    2^28≤362037209 ∧ 362037209<536767369 ∧ 536767369<2^29 ∧ 536767369<2*362037209 ∧
    2^57≤N58 ∧ N58<2^58 ∧ N58.Coprime 1517 := by
  refine ⟨by norm_num [ExactFactorization,N58],?_⟩
  decide +kernel

/-- On the scaled input, y is exactly the fourth root of the quotient by four. -/
theorem coordinates58 : 1517^4*N58=189173^4+4*22521920^4 ∧ 1517^4*N58<4*(22521920+1)^4 := by
  decide +kernel

theorem unscaled58 : readings N58=(none,none) :=
  read_pair (miss_x 20995 1706 (by decide +kernel)) (miss_y 14846 2075 (by decide +kernel))

theorem miss725_58 : readings (725^4*N58)=(none,none) :=
  read_pair (miss_x 15222039 157151 (by decide +kernel)) (miss_y 10763607 222421 (by decide +kernel))

theorem hit1517_58 : readings (1517^4*N58)=(none,some (1005988469052409,1023030625741049)) :=
  read_pair (miss_x 31850804 391168 (by decide +kernel))
    ((completeY (by decide : 0<189173) (by decide : 0<22521920) coordinates58.1 coordinates58.2).trans
      (congrArg some (by decide +kernel : factors 189173 22521920=(1005988469052409,1023030625741049))))

/-- Each successful coordinate factor shares just one prime with the input. -/
theorem gcd58 : Nat.gcd N58 1005988469052409=536767369 ∧ Nat.gcd N58 1023030625741049=362037209 ∧
    1<362037209 ∧ 362037209<N58 ∧ 1<536767369 ∧ 536767369<N58 := by decide +kernel

/-- The 37-bit comparison has ratio-balanced primes of different bit widths. -/
theorem data37 : ExactFactorization N37 [229777,420853] ∧
    2^17≤229777 ∧ 229777<2^18 ∧ 2^18≤420853 ∧ 420853<2^19 ∧ 420853<2*229777 ∧
    2^36≤N37 ∧ N37<2^37 ∧ N37.Coprime 725 := by
  refine ⟨by norm_num [ExactFactorization,N37],?_⟩
  decide +kernel

theorem coordinates37 : 725^4*N37=1643^4+4*285879^4 ∧ 725^4*N37<4*(285879+1)^4 := by decide +kernel

theorem unscaled37 : readings N37=(none,none) :=
  read_pair (miss_x 557 102 (by decide +kernel)) (miss_y 394 132 (by decide +kernel))

theorem hit725_37 : readings (725^4*N37)=(none,some (162516906337,164395703125)) :=
  read_pair (miss_x 404293 15866 (by decide +kernel))
    ((completeY (by decide : 0<1643) (by decide : 0<285879) coordinates37.1 coordinates37.2).trans
      (congrArg some (by decide +kernel : factors 1643 285879=(162516906337,164395703125))))

theorem miss1517_37 : readings (1517^4*N37)=(none,none) :=
  read_pair (miss_x 845950 19847 (by decide +kernel)) (miss_y 598177 27325 (by decide +kernel))

theorem gcd37 : Nat.gcd N37 162516906337=229777 ∧ Nat.gcd N37 164395703125=420853 ∧
    1<229777 ∧ 229777<N37 ∧ 1<420853 ∧ 420853<N37 := by decide +kernel

/-- The complete outcomes for the same ordered three-denominator menu. -/
theorem menu :
    ([1,725,1517]:List ℕ).map (fun d => readings (d^4*N58)) =
      [(none,none),(none,none),(none,some (1005988469052409,1023030625741049))] ∧
    ([1,725,1517]:List ℕ).map (fun d => readings (d^4*N37)) =
      [(none,none),(none,some (162516906337,164395703125)),(none,none)] := by
  simp only [List.map_cons,List.map_nil,one_pow,one_mul,unscaled58,miss725_58,hit1517_58,
    unscaled37,hit725_37,miss1517_37,and_self]

end PrimeFactors.ScaledQuarticControls
