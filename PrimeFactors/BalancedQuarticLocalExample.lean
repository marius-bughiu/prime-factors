import PrimeFactors.RationalQuarticFactorPair
import PrimeFactors.RationalQuarticResidues

/-! A balanced semiprime passes every finite congruence for the quartic
representation, yet cannot have ordinary integer coordinates. Its supplied
rational coordinates nevertheless determine the prime factors by gcd. -/
namespace PrimeFactors.BalancedQuarticLocalExample

open RationalQuarticResidues RecognizingQuarticProducts

abbrev N : ℕ := 161064781282549
abbrev p : ℕ := 12637693
abbrev q : ℕ := 12744793

theorem data : N=p*q ∧ p.Prime ∧ q.Prime ∧ p<q ∧ q<2*p := by
  norm_num [N,p,q]

theorem widths : 2^23≤p ∧ q<2^24 ∧ 2^47≤N ∧ N<2^48 := by decide +kernel

theorem identity : 221^4*N=318065^4+4*(552963:ℕ)^4 := by decide +kernel

theorem locally (m : ℕ) (pos : 0<m) : Rep N m := by
  apply all_moduli identity _ m pos
  intro r prime dvd e
  change r∣13*17 at dvd
  rcases prime.dvd_mul.mp dvd with h|h
  · have eq := (Nat.prime_dvd_prime_iff_eq prime (by decide : Nat.Prime 13)).mp h
    subst r
    exact smooth_lift (by decide) (by decide) 1 0 (by decide +kernel) (Or.inl (by decide)) e
  · have eq := (Nat.prime_dvd_prime_iff_eq prime (by decide : Nat.Prime 17)).mp h
    subst r
    exact smooth_lift (by decide) (by decide) 6 1 (by decide +kernel) (Or.inl (by decide)) e

/-- When the two integer factors are specified, their own sum and difference
must match the quartic coordinates at every modulus. -/
private theorem prescribed (m x y a b : ℕ) (pair : factors x y=(a,b)) :
    ∃ u v : ZMod m, 2*u^2+4*v^2=((a+b:ℕ):ZMod m) ∧ (a:ZMod m)+4*u*v=(b:ZMod m) := by
  have sum := factor_sum x y
  rw [pair] at sum
  have left := congrArg Prod.fst pair
  have right := congrArg Prod.snd pair
  dsimp [factors] at left right sum
  have bound := two_mul_le_add_sq x y
  have dif : a+4*x*y=b := by nlinarith [Nat.sub_add_cancel (show 2*x*y≤x^2+2*y^2 by omega)]
  exact ⟨x,y,by exact_mod_cast congrArg (fun z : ℕ => (z:ZMod m)) sum.symm,
    by exact_mod_cast congrArg (fun z : ℕ => (z:ZMod m)) dif⟩

theorem no_integer : ¬∃ x y : ℕ, N=x^4+4*y^4 := by
  rintro ⟨x,y,repr⟩
  by_cases zero : x=0
  · subst x
    simp only [zero_pow (by decide : 4≠0),zero_add] at repr
    unfold N at repr
    omega
  by_cases yz : y=0
  · subst y
    simp only [zero_pow (by decide : 4≠0),mul_zero,add_zero] at repr
    have root : fourthRoot N=3562 := fourthRoot_eq_iff.mpr ⟨by decide +kernel,by decide +kernel⟩
    rw [repr,fourthRoot_pow] at root
    subst x
    exact (by decide +kernel : N≠3562^4) repr
  have dif : (x,y)≠(1,1) := by
    rintro eq
    have l : x=1 := congrArg Prod.fst eq
    have r : y=1 := congrArg Prod.snd eq
    subst x; subst y
    exact (by decide +kernel : N≠1^4+4*1^4) repr
  have proper := (proper_iff (Nat.pos_of_ne_zero zero) (Nat.pos_of_ne_zero yz)).mpr dif
  have prod := (factor_product x y).trans (repr.symm.trans data.1)
  obtain ⟨left,right⟩ := ordered_semiprime_pair_unique data.2.1 data.2.2.1 data.2.2.2.1.le proper.2.1.le proper.1 prod
  have forced := prescribed 11 x y p q (Prod.ext left right)
  exact (by decide +kernel : ¬∃ u v : ZMod 11,
    2*u^2+4*v^2=((p+q:ℕ):ZMod 11) ∧ (p:ZMod 11)+4*u*v=(q:ZMod 11)) forced

theorem no_signed : ¬∃ x y : ℤ, x^4+4*y^4=N := by
  intro point
  obtain ⟨x,y,eq⟩ := (integer_iff_natural N).mp point
  exact no_integer ⟨x,y,eq.symm⟩

/-- The rational coordinates are an external certificate here. -/
theorem supplied_pair : (318065:ℕ).Coprime 552963 ∧ 6*221^4≤N ∧
    Nat.gcd N (factors 318065 552963).1=p ∧ Nat.gcd N (factors 318065 552963).2=q := by
  decide +kernel

end PrimeFactors.BalancedQuarticLocalExample
