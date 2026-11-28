import PrimeFactors.ToySumIsolation
import PrimeFactors.Isolation
import PrimeFactors.PrimePower

/-! Compare the positions of the first exact square in two traversals of the
same small factor-sum window. Both use modulo 4 and modulo 25. The second
visits the sums with vanishing discriminant modulo 5 first, breaking ties in
ascending order. The finite populations impose no product-width condition. -/

namespace PrimeFactors.ToyResidueOrderCost

set_option maxRecDepth 16384

private def squareResidues : List ℕ := [0,1,4,6,9,11,14,16,19,21,24]

noncomputable def squareUnit (n : ℕ) : Bool := (n%25 != 0) && squareResidues.contains (n%25)

private noncomputable def residueTest (r s : ℕ) : Bool := squareResidues.contains ((s*s+100-4*r)%25)

theorem residue_test : ∀ r s : Fin 25, residueTest r.val s.val = true ↔
    AdmissibleSum (r.val : ZMod 25) (s.val : ZMod 25) := by
  have two : IsUnit (2 : ZMod 25) := (ZMod.isUnit_iff_coprime 2 25).mpr (by decide)
  simp only [admissibleSum_iff_isSquare_of_two_unit two, isSquare_iff_exists_sq]
  decide +kernel

theorem square_unit_test : ∀ r : Fin 25, squareUnit r.val = true ↔
    r.val.Coprime 25 ∧ ∃ x : Fin 25, x.val*x.val%25 = r.val := by decide +kernel

noncomputable def ascending (n A : ℕ) : List ℕ :=
  (ToySumIsolation.menu n A).filter fun s => residueTest (n%25) (s%25)

def singular (n s : ℕ) : Bool := s*s%5 == 4*n%5

noncomputable def prioritized (n : ℕ) (sums : List ℕ) : List ℕ :=
  sums.filter (singular n) ++ sums.filter (fun s => !singular n s)

theorem same_sums (n : ℕ) (sums : List ℕ) : (prioritized n sums).Perm sums :=
  List.filter_append_perm _ _

/-- For every candidate, equality to the known sum is an exact retrospective
measure of where a product-only discriminant test first succeeds. -/
theorem square_iff {p q A s : ℕ} (size : 2 ≤ A) (lo : A ≤ p) (order : p ≤ q)
    (pp : p.Prime) (qp : q.Prime) (mem : s ∈ ascending (p*q) A) :
    IsSquare (s^2 - 4*(p*q)) ↔ s=p+q := by
  obtain ⟨lower,upper,_⟩ := ToySumIsolation.mem_menu.mp (List.mem_filter.mp mem).1
  constructor
  · apply semiprime_sum_of_square_discriminant pp qp order (ceilSqrt_le_iff.mp lower)
    have half := Nat.div_le_div_left (a:=p*q) size (by decide)
    have twice := Nat.mul_le_mul pp.two_le (lo.trans order)
    have bound := upper.trans (min_le_left (A+p*q/A) ((2*A-1)+p*q/(2*A-1)))
    omega
  · rintro rfl
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le order
    refine ⟨d,Nat.sub_eq_of_eq_add ?_⟩
    ring

structure Counts where
  earlier : ℕ
  tied : ℕ
  later : ℕ
  ascendingTests : ℕ
  prioritizedTests : ℕ
  missing : ℕ
  deriving DecidableEq

private def Counts.add (a b : Counts) : Counts :=
  ⟨a.earlier+b.earlier, a.tied+b.tied, a.later+b.later,
    a.ascendingTests+b.ascendingTests, a.prioritizedTests+b.prioritizedTests, a.missing+b.missing⟩

private def zero : Counts := ⟨0,0,0,0,0,0⟩

/-- Rank includes the successful test. A missing true sum is recorded
separately and can never be mistaken for a successful last-position test. -/
noncomputable def score (A p q : ℕ) : Counts :=
  let sums := ascending (p*q) A
  let first := sums.idxOf (p+q)
  let next := (prioritized (p*q) sums).idxOf (p+q)
  if first < sums.length then
    ⟨if next<first then 1 else 0, if next=first then 1 else 0, if first<next then 1 else 0,
      first+1,next+1,0⟩
  else ⟨0,0,0,0,0,1⟩

/-- Both population predicates depend only on the product remainder. -/
noncomputable def census (A : ℕ) (keep : ℕ → Bool) : Counts :=
  let primes := ToySumIsolation.primes A
  (primes.map fun p =>
    (((primes.filter fun q => p<q && keep (p*q)).map fun q => score A p q).foldl Counts.add zero)
  ).foldl Counts.add zero

theorem nine_square : census 256 squareUnit = ⟨70,319,52,603,579,0⟩ := by
  rw [census,ToySumIsolation.catalog_nine]
  decide +kernel

theorem nine_one : census 256 (fun n => n%25 == 1) = ⟨7,35,2,59,55,0⟩ := by
  rw [census,ToySumIsolation.catalog_nine]
  decide +kernel

private theorem catalog_ten : ToySumIsolation.primes 512 =
    [521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,
      643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,
      773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,
      919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021] := by
  let trial (n : ℕ) := (List.range 32).all fun d => d<2 || n%d != 0
  trans (List.range' 512 512).filter trial
  · apply List.filter_congr
    intro n hn
    obtain ⟨i,hi,rfl⟩ := List.mem_range'.mp hn
    apply Bool.eq_iff_iff.mpr
    simp only [trial,decide_eq_true_eq,List.all_eq_true,List.mem_range,Bool.or_eq_true,bne_iff_ne]
    constructor
    · intro prime d small
      by_cases trivial : d<2
      · exact Or.inl trivial
      · exact Or.inr (Nat.dvd_iff_mod_eq_zero.not.mp
          ((Nat.prime_def_lt'.mp prime).2 d (by omega) (by omega)))
    · intro test
      apply Nat.prime_def_le_sqrt.mpr
      refine ⟨by omega,?_⟩
      intro d low high
      have cap : (512+1*i).sqrt < 32 := Nat.sqrt_lt'.mpr (by omega)
      exact Nat.dvd_iff_mod_eq_zero.not.mpr ((test d (high.trans_lt cap)).resolve_left (by omega))
  · decide +kernel

/-- The fixed remainder 1 is a negative comparison at ten bits. -/
theorem ten_one : census 512 (fun n => n%25 == 1) = ⟨21,91,24,242,259,0⟩ := by
  rw [census,catalog_ten]
  decide +kernel

end PrimeFactors.ToyResidueOrderCost
