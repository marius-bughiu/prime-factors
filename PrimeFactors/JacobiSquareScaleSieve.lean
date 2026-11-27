import PrimeFactors.JacobiPeriodSquareClass
import PrimeFactors.FactorSum
import Mathlib.Data.Nat.Count

/-! A finite square-divisibility sieve for the first successful scale in
the balanced predecessor-square search. -/
namespace PrimeFactors.JacobiSquareScaleSieve

/-- Trial division by the first three prime squares; a retained scale may
still have a larger square divisor. -/
def Keep (t : ℕ) : Prop := t%4≠0 ∧ t%9≠0 ∧ t%25≠0

noncomputable instance (t : ℕ) : Decidable (Keep t) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem keeps_squarefree {t : ℕ} (free : Squarefree t) : Keep t := by
  have h := Nat.squarefree_iff_prime_squarefree.mp free
  refine ⟨?_,?_,?_⟩
  · exact fun e => h 2 (by decide) (Nat.dvd_of_mod_eq_zero e)
  · exact fun e => h 3 (by decide) (Nat.dvd_of_mod_eq_zero e)
  · exact fun e => h 5 (by decide) (Nat.dvd_of_mod_eq_zero e)

/-- Unfiltered and filtered searches have the same first successful scale
on every balanced pair. Primality is unnecessary for the stated sum test. -/
theorem same_first {p q : ℕ} (hp : 1<p) (order : p≤q) (bal : q≤2*p) :
    ∃ c : ℕ, Squarefree c ∧
      IsLeast {t : ℕ | 0<t ∧ predecessorSquareSum (p*q) t=p+q} c ∧
      IsLeast {t : ℕ | 0<t ∧ Keep t ∧ predecessorSquareSum (p*q) t=p+q} c := by
  let R := JacobiPeriodCount.residualProduct p q
  have pg : 0<p-1 := by omega
  have qg : 0<q-1 := by omega
  have gp := Nat.gcd_pos_of_pos_left (q-1) pg
  have pos : 0<R := Nat.mul_pos (Nat.div_pos (Nat.gcd_le_left _ pg) gp)
    (Nat.div_pos (Nat.gcd_le_right _ qg) gp)
  obtain ⟨c,z,_,_,eq,free⟩ := Nat.sq_mul_squarefree_of_pos pos
  have first := JacobiPeriodSquareClass.first_scale hp order bal free
    (eq.symm.trans (Nat.mul_comm _ _) : R=c*z^2)
  refine ⟨c,free,first,⟨first.1.1,keeps_squarefree free,first.1.2⟩,?_⟩
  rintro t ⟨positive,_,hit⟩
  exact first.2 ⟨positive,hit⟩

/-- On a semiprime the quadratic decoder's nontrivial ordered product check
can succeed only at the true factor sum. -/
theorem checked_pair_iff {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p≤q) (t : ℕ) :
    (∃ x y, 1<x ∧ x≤y ∧ x*y=p*q ∧ x+y=predecessorSquareSum (p*q) t) ↔
      predecessorSquareSum (p*q) t=p+q := by
  constructor
  · rintro ⟨x,y,hx,hxy,prod,sum⟩
    obtain ⟨rfl,rfl⟩ := ordered_semiprime_pair_unique pp qp ord hxy hx prod
    exact sum.symm
  · intro sum
    exact ⟨p,q,pp.one_lt,ord,rfl,sum.symm⟩

/-- A supplied cap yields a successful scale in one search exactly when it
does in the other, even if the cap itself gets skipped. -/
theorem capped_iff {p q : ℕ} (hp : 1<p) (order : p≤q) (bal : q≤2*p) (B : ℕ) :
    (∃ t, t≤B ∧ 0<t ∧ predecessorSquareSum (p*q) t=p+q) ↔
    ∃ t, t≤B ∧ 0<t ∧ Keep t ∧ predecessorSquareSum (p*q) t=p+q := by
  obtain ⟨c,_,plain,sieved⟩ := same_first hp order bal
  constructor
  · rintro ⟨t,bounded,positive,hit⟩
    exact ⟨c,(plain.2 ⟨positive,hit⟩).trans bounded,sieved.1⟩
  · rintro ⟨t,bounded,positive,_,hit⟩
    exact ⟨t,bounded,positive,hit⟩

/-- Number of expensive evaluations through B inclusive, when the search
reaches B; zero-based k indexes the positive scale k+1. -/
noncomputable def evaluations (B : ℕ) := Nat.count (fun k => Keep (k+1)) B

theorem periodic (k : ℕ) : Keep (900+k) ↔ Keep k := by simp [Keep,Nat.add_mod]

set_option maxRecDepth 4096 in
theorem full_block : evaluations 900 = 576 := by decide +kernel

private theorem step (n : ℕ) : evaluations (900+n) = 576+evaluations n := by
  unfold evaluations
  rw [Nat.count_add]
  change evaluations 900 + _ = _
  rw [full_block]
  congr 1
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  ext k
  simp only [Finset.mem_filter,Nat.add_assoc,periodic]

/-- Every full block of 900 costs 576 scale evaluations, and the last
partial block costs exactly the number retained in the corresponding prefix. -/
theorem cap_count (B : ℕ) :
    evaluations B = 576*(B/900) + evaluations (B%900) := by
  have blocks (k r : ℕ) : evaluations (900*k+r)=576*k+evaluations r := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ,Nat.mul_succ,show 900*k+900+r=900+(900*k+r) by omega,step,ih]
      omega
  simpa only [Nat.div_add_mod] using blocks (B/900) (B%900)

/-- The boundary control fails through 1,154 and first succeeds at 1,155,
where the two prime factors of 4,757 can be certified. -/
theorem control_4757 :
    ExactFactorization 4757 [67,71] ∧
    IsLeast {t : ℕ | 0<t ∧ predecessorSquareSum 4757 t=138} 1155 := by
  refine ⟨by norm_num [ExactFactorization],?_⟩
  exact JacobiPeriodSquareClass.first_scale (p:=67) (q:=71) (c:=1155) (z:=1)
    (by decide) (by decide) (by decide) (by
      change Squarefree (3*(5*(7*11)) : ℕ)
      simp only [Nat.squarefree_mul_iff]
      exact ⟨by decide,(Nat.prime_iff.mp (by decide)).squarefree,by decide,
        (Nat.prime_iff.mp (by decide)).squarefree,by decide,
        (Nat.prime_iff.mp (by decide)).squarefree,(Nat.prime_iff.mp (by decide)).squarefree⟩)
    (by decide +kernel)

end PrimeFactors.JacobiSquareScaleSieve
