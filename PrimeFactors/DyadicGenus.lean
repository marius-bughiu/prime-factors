import PrimeFactors.AmbiguousTwist
import Mathlib.GroupTheory.Index
import PrimeFactors.EuclideanHeightExample

namespace PrimeFactors.DyadicGenus

/-- The odd coefficient of the ramified form [2,2,c] reveals its sign under
the character of discriminant -4, from N alone. -/
theorem public_character (N : ℕ) (h : N % 8 = 5) :
    (N+1)/2 % 4 = 3 ∧ 2*((N+1)/2) = N+1 := by omega

/-- The same sign is positive for N = 1 mod 8, where the normalization
argument no longer applies. Both dyadic forms have a public odd represented
integer with fixed residue at 2. -/
theorem same_residue_character (N : ℕ) (h : N % 8 = 1) :
    (N+1)/2 % 4 = 1 ∧ (N+2) % 8 = 3 := by omega

/-- Every odd unit modulo eight is its own inverse. If the product is one,
the two hidden factors have the same residue. -/
theorem same_residue {p q : ℕ} (one : p*q % 8 = 1) : p%8=q%8 := by
  rw [Nat.mul_mod] at one
  have hp := Nat.mod_lt p (by decide : 0 < 8)
  have hq := Nat.mod_lt q (by decide : 0 < 8)
  have table : ∀ a b : Fin 8, a.val*b.val % 8 = 1 → a = b := by decide
  exact congrArg Fin.val (table ⟨_, hp⟩ ⟨_, hq⟩ one)

/-- A nonidentity involution in the image of squaring gives an extra factor
two beyond the number of elements already killed by squaring. -/
theorem double_genus_of_square_involution {G : Type*} [CommGroup G]
    {x w : G} (square : w^2=x) (non : x ≠ 1) (inv : x^2=1) :
    Nat.card (powMonoidHom (α := G) 2).ker * 2 ∣ Nat.card G := by
  let f := powMonoidHom (α := G) 2
  let s : f.range := ⟨x, ⟨w,square⟩⟩
  have ord : orderOf s = 2 := orderOf_eq_prime
    (Subtype.ext inv) (fun eq => non (congrArg Subtype.val eq))
  have div := orderOf_dvd_natCard s
  rw [ord] at div
  have size := f.ker.card_mul_index
  rw [Subgroup.index_ker] at size
  rw [←size]
  exact Nat.mul_dvd_mul_left _ div

/-- Among two real signs and their product, at least one is positive. -/
theorem positive_among_three {G : Type*} [Group G] (χ : G →* ℤ) (u v : G) :
    χ u = 1 ∨ χ v = 1 ∨ χ (u*v) = 1 := by
  rcases Int.isUnit_iff.mp ((Group.isUnit u).map χ) with a | a
  · exact Or.inl a
  rcases Int.isUnit_iff.mp ((Group.isUnit v).map χ) with b | b
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (by rw [map_mul, a, b]; decide))

/-- On two independent public involutions, if just one real character is
still unknown, one of the three possible products is a square. The known
two-torsion of size eight then forces the class-number divisor sixteen. -/
theorem sixteen_of_public_pair {G : Type*} [CommGroup G] (χ : G →* ℤ) {u v : G}
    (eight : Nat.card (powMonoidHom (α := G) 2).ker = 8)
    (hu : u ≠ 1) (hv : v ≠ 1) (different : u ≠ v) (su : u^2=1) (sv : v^2=1)
    (principal : ∀ x, (x=u ∨ x=v ∨ x=u*v) → χ x=1 → ∃ w : G, w^2=x) :
    16 ∣ Nat.card G := by
  have finish (x : G) (inSet : x=u ∨ x=v ∨ x=u*v) (one : χ x=1) (non : x≠1) (inv : x^2=1) :
      16 ∣ Nat.card G := by
    obtain ⟨w, hw⟩ := principal x inSet one
    simpa only [eight] using double_genus_of_square_involution hw non inv
  rcases positive_among_three χ u v with x | y | z
  · exact finish u (Or.inl rfl) x hu su
  · exact finish v (Or.inr (Or.inl rfl)) y hv sv
  · refine finish (u*v) (Or.inr (Or.inr rfl)) z ?_ ?_
    · intro eq
      apply different
      calc
        u = u*(v*v) := by rw [←sq, sv, mul_one]
        _ = v := by rw [←mul_assoc, eq, one_mul]
    · rw [mul_pow, su, sv, one_mul]

/-- Equal genus signs on distinct ambiguous classes give a nonidentity
square involution when the principal genus is the subgroup of squares. -/
theorem eight_of_equal_genus {G A : Type*} [CommGroup G] [Group A] (χ : G →* A)
    (principal : ∀ x, χ x = 1 → ∃ w : G, w^2=x)
    (four : Nat.card (powMonoidHom (α := G) 2).ker = 4)
    {s t : G} (different : s ≠ t) (hs : s^2=1) (ht : t^2=1) (signs : χ s=χ t) :
    8 ∣ Nat.card G := by
  obtain ⟨w, hw⟩ := principal (s/t) (by rw [map_div, signs, div_self'])
  have d := double_genus_of_square_involution hw (div_ne_one_of_ne different)
    (by rw [div_pow, hs, ht, div_one])
  simpa only [four] using d

/-- Squaring before the class-number window removes the public involution
regardless of which of the two representatives has positive sign. -/
theorem normalized_square {G : Type*} [CommGroup G] (χ : G →* ℤ) {T : G}
    (inv : T^2=1) (g : G) : (AmbiguousTwist.normalize χ T g)^2=g^2 := by
  unfold AmbiguousTwist.normalize
  split <;> simp_all [mul_pow]

/-- Canonical reduced forms, enumerating nonnegative middle coefficients
and counting both signs exactly off the boundary. -/
noncomputable def reducedCountThrough (Q maxA : ℕ) : ℕ :=
  ((List.range maxA).map fun i =>
    let a := i+1
    ((List.range (a+1)).map fun b =>
      let c := (b*b+Q)/(4*a)
      if 4*a*c != b*b+Q || c<a || Nat.gcd a (Nat.gcd b c) != 1 then 0
      else if b==0 || b==a || a==c then 1 else 2).sum).sum

/-- The enumeration agrees on the first two products through modulus 256,
and selects opposite discriminants for the extra divisor. -/
theorem opposite_branches :
    209%256 = 2257%256 ∧ reducedCountThrough (4*209) 16=20 ∧ reducedCountThrough (8*209) 23=8 ∧
    reducedCountThrough (4*2257) 54=24 ∧ reducedCountThrough (8*2257) 77=92 := by decide +kernel

/-- This computes the upper endpoint of a genus-divided window from the
discriminant magnitude and known divisor of the class number. -/
private def windowTop (Q divisor : ℕ) :=
  ((Q-1).sqrt+1)*(Q.log2+3)/3/divisor

private def tableLength (Q divisor : ℕ) :=
  ((windowTop Q divisor)-1).sqrt+1

private theorem ceil_sqrt_eq {n a : ℕ} (lower : (a-1)^2 < n) (upper : n ≤ a^2) :
    (n-1).sqrt+1 = a := by
  have lo : a-1 ≤ (n-1).sqrt := Nat.le_sqrt'.mpr (by omega)
  have hi : (n-1).sqrt < a := Nat.sqrt_lt'.mpr (by omega)
  omega

private theorem checkedLog {n k : ℕ} (pos : n ≠ 0)
    (bounds : 2^k ≤ n ∧ n < 2^(k+1)) : n.log2=k := by
  have low := (Nat.le_log2 pos).mpr bounds.1
  have high := (Nat.log2_lt pos).mpr bounds.2
  omega

private theorem certifyLength (Q divisor a b lg : ℕ)
    (size : (a-1)^2 < Q ∧ Q ≤ a^2)
    (bits : 2^lg ≤ Q ∧ Q < 2^(lg+1))
    (table : (b-1)^2 < a*(lg+3)/3/divisor ∧ a*(lg+3)/3/divisor ≤ b^2) :
    tableLength Q divisor = b := by
  unfold tableLength windowTop
  rw [ceil_sqrt_eq size.1 size.2, checkedLog (by omega) bits]
  exact ceil_sqrt_eq table.1 table.2

set_option exponentiation.threshold 4096 in
/-- The input satisfies the two dyadic twist tests and the conservative
table's length drops by between 3.2% and 3.3%. The square roots are checked
by bounding the input between consecutive squares. -/
theorem full_size_window :
    let N := EuclideanHeightExample.modulus
    let old := tableLength (4*N) 4
    let new := tableLength (56*N) 16
    N%8=1 ∧ N%7=1 ∧ old.log2+1=517 ∧ new.log2+1=516 ∧
      967*old < 1000*new ∧ 1000*new < 968*old := by
  let b4 : ℕ :=
    214902223805037835407114992638732963637735947592538852655748076481572490315420291097045772861674744886367429169013828687942427396689361027255647995960049260
  let b56 : ℕ :=
    207998478308688106460441818371784403215949272329560702499459955028692219902705013994912244749567431113764782105178442983822800860940789168674636649540499511
  dsimp only
  rw [certifyLength (4*EuclideanHeightExample.modulus) 4
    270075823370471172539650060271098650782753831933597272358639954154419986900023521886088362615536953055795637435351919646880615106044371307907625212959861347578783586375530282566149441260866241026834381879296406989063497151609370317039875224466571605726029312917602102470016115053325769991836901677876153809229
    b4 2049 (by decide +kernel) (by decide +kernel) (by decide +kernel),
    certifyLength (56*EuclideanHeightExample.modulus) 16
    1010531199503177733985076272768472990619151850117861792041918520012799459303325097346661028173782045167073734014905455111061254060832804134236424427054783699912609923635560573599831864865341360582517269321121414130883807765765614141714342550492345403751062009325112132508375425682251795687194763633512943175237
    b56 2052 (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rw [checkedLog (n:=b4) (k:=516) (by decide +kernel) (by decide +kernel),
    checkedLog (n:=b56) (k:=515) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- A genuine semiprime satisfying the -56N hypotheses has class number
48, so the guaranteed divisor cannot be raised to 32 on this entire family. -/
theorem sharp_divisor :
    1073%8=1 ∧ 1073%7=2 ∧ 3^2%7=2 ∧ 3*142^2>56*1073 ∧
    reducedCountThrough (56*1073) 141 = 48 ∧
    ExactFactorization 1073 [29,37] := by
  exact ⟨by decide, by decide, by decide, by decide, by decide +kernel, by norm_num [ExactFactorization]⟩

theorem factors : ExactFactorization 209 [11,19] ∧ ExactFactorization 2257 [37,61] ∧
    ExactFactorization 77 [7,11] := by norm_num [ExactFactorization]

/-- The lift of the middle coefficient of the split prime form at 3 gives
the symmetric form [9,4,9] of discriminant -308 and hence a factor of 77. -/
theorem worked_form :
    (2:ℤ)^2-4*2*39 = -4*77 ∧ (2:ℤ)^2-4*3*26 = -4*77 ∧
    (2:ℤ)^2-4*6*13 = -4*77 ∧ (-4:ℤ)%6 = 2 ∧ (-4:ℤ)^2-4*9*9 = -4*77 ∧
    (9:ℕ)-4/2=7 ∧ (9:ℕ)+4/2=11 := by norm_num

end PrimeFactors.DyadicGenus
