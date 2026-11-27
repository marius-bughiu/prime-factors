import PrimeFactors.JacobiPeriodSquareClass
import PrimeFactors.FactorSum

/-! A supplied complete set of prime divisors of a positive guess t gives a
finite menu of squarefree scales. The cardinality counts scales after that
set is known; acquiring a complete prime divisor list is a separate task. -/
namespace PrimeFactors.JacobiPeriodPrimeSupport

open Finset JacobiPeriodCount JacobiPeriodProbe JacobiMomentPeriod

/-- Completeness includes both soundness and coverage of every prime divisor. -/
def CompleteSupport (t : ℕ) (F : Finset ℕ) : Prop :=
  ∀ l : ℕ, l ∈ F ↔ l.Prime ∧ l ∣ t

/-- Distinct products of subsets, including 1 from the empty subset. -/
noncomputable def scales (F : Finset ℕ) : Finset ℕ := F.powerset.image (fun S => ∏ l ∈ S, l)

private theorem squarefree_product (S : Finset ℕ) (primes : ∀ l ∈ S, Nat.Prime l) :
    Squarefree (∏ l ∈ S, l) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert l S fresh ih =>
    have lp := primes l (mem_insert_self ..)
    have rest : ∀ k ∈ S, Nat.Prime k := fun k hk => primes k (mem_insert_of_mem hk)
    have cop : l.Coprime (∏ k ∈ S, k) := Nat.coprime_prod_right_iff.mpr fun k hk =>
      (Nat.coprime_primes lp (rest k hk)).mpr (fun eq => fresh (eq ▸ hk))
    rw [prod_insert fresh]
    exact (Nat.squarefree_mul cop).mpr ⟨lp.squarefree,ih rest⟩

/-- The menu has exactly one entry per subset of F. -/
theorem scales_card {t : ℕ} {F : Finset ℕ} (support : CompleteSupport t F) :
    (scales F).card=2^F.card := by
  rw [scales,←card_powerset]
  apply card_image_iff.mpr
  intro S hS T hT same
  have first := Nat.primeFactors_prod (s:=S) (fun l hl => ((support l).mp ((mem_powerset.mp hS) hl)).1)
  have last := Nat.primeFactors_prod (s:=T) (fun l hl => ((support l).mp ((mem_powerset.mp hT) hl)).1)
  exact first.symm.trans ((congrArg Nat.primeFactors same).trans last)

/-- Exactly the squarefree divisors occur. -/
theorem mem_scales_iff {t d : ℕ} {F : Finset ℕ} (support : CompleteSupport t F) :
    d ∈ scales F ↔ Squarefree d ∧ d ∣ t := by
  constructor
  · intro h
    obtain ⟨S,hS,rfl⟩ := mem_image.mp h
    have each (l : ℕ) (hl : l ∈ S) := (support l).mp ((mem_powerset.mp hS) hl)
    exact ⟨squarefree_product S (fun l hl => (each l hl).1),
      prod_primes_dvd t (fun l hl => (each l hl).1.prime) (fun l hl => (each l hl).2)⟩
  · rintro ⟨free,dt⟩
    apply mem_image.mpr
    refine ⟨d.primeFactors,mem_powerset.mpr ?_,Nat.prod_primeFactors_of_squarefree free⟩
    intro l hl
    exact (support l).mpr ⟨Nat.prime_of_mem_primeFactors hl,(Nat.dvd_of_mem_primeFactors hl).trans dt⟩

theorem scales_at_one {F : Finset ℕ} (support : CompleteSupport 1 F) : scales F={1} := by
  ext d
  rw [mem_scales_iff support,mem_singleton,Nat.dvd_one]
  exact ⟨And.right,fun eq => ⟨eq ▸ squarefree_one,eq⟩⟩

/-- Within a squarefree menu, the true-sum scale is uniquely the squarefree
part c of the residual product. -/
theorem menu_hit_iff {p q c z t d : ℕ} {F : Finset ℕ} (hp : 1 < p)
    (le : p ≤ q) (bal : q ≤ 2*p) (free : Squarefree c) (period : residualProduct p q=c*z^2)
    (support : CompleteSupport t F) (member : d ∈ scales F) :
    predecessorSquareSum (p*q) d=p+q ↔ d=c := by
  have sf := ((mem_scales_iff support).mp member).1
  constructor
  · intro hit
    obtain ⟨w,_,eq⟩ := (JacobiPeriodSquareClass.successful_scales hp le bal free period
      (Nat.pos_of_ne_zero sf.ne_zero)).mp hit
    have dv : w*w ∣ d := ⟨c,by rw [eq,pow_two]; ring⟩
    have unit := Nat.isUnit_iff.mp (sf w dv)
    simpa [unit] using eq
  · rintro rfl
    exact (JacobiPeriodSquareClass.first_scale hp le bal free period).1.2

/-- A true sum occurs in the menu iff c divides t. A valid period is sufficient
since c divides R, but the menu can also recover the factors for an invalid guess. -/
theorem exists_hit_iff {p q c z t : ℕ} {F : Finset ℕ} (hp : 1 < p)
    (le : p ≤ q) (bal : q ≤ 2*p) (free : Squarefree c) (period : residualProduct p q=c*z^2)
    (support : CompleteSupport t F) :
    (∃ d ∈ scales F, predecessorSquareSum (p*q) d=p+q) ↔ c ∣ t := by
  constructor
  · rintro ⟨d,mem,hit⟩
    obtain rfl := (menu_hit_iff hp le bal free period support mem).mp hit
    exact ((mem_scales_iff support).mp mem).2
  · intro div
    exact ⟨c,(mem_scales_iff support).mpr ⟨free,div⟩,(JacobiPeriodSquareClass.first_scale hp le bal free period).1.2⟩

/-- Substituting any verified, nontrivial sorted pair gives an exact period test. -/
theorem check_pair {p q x y t : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 7 ≤ p) (lt : p < q)
    (proper : 1 < x) (ordered : x ≤ y) (product : x*y=p*q) :
    AllOffsets (completeEven (p*q)) ((p*q-1)/2) t ↔ residualProduct x y ∣ t := by
  have pp : p.Prime := Fact.out
  have qp : q.Prime := Fact.out
  obtain ⟨rfl,rfl⟩ := ordered_semiprime_pair_unique pp qp lt.le ordered proper product
  exact canonical_period ((Nat.coprime_primes pp qp).mpr lt.ne) hp (hp.trans lt.le) t

/-- Enumeration followed by an exact product and divisibility check characterizes
period validity, with all quantities in the check derived from N,t and a menu scale. -/
theorem period_iff_checked {p q t : ℕ} [Fact p.Prime] [Fact q.Prime] {F : Finset ℕ}
    (hp : 7 ≤ p) (lt : p < q) (bal : q ≤ 2*p) (support : CompleteSupport t F) :
    AllOffsets (completeEven (p*q)) ((p*q-1)/2) t ↔
      ∃ d ∈ scales F, let n := p*q
        let pair := recoverFromSigma n (n+predecessorSquareSum n d+1)
        1 < pair.1 ∧ pair.1 ≤ pair.2 ∧ pair.1*pair.2=n ∧ residualProduct pair.1 pair.2 ∣ t := by
  have pp : p.Prime := Fact.out
  have qp : q.Prime := Fact.out
  have cop := (Nat.coprime_primes pp qp).mpr lt.ne
  constructor
  · intro works
    have div := (canonical_period cop hp (hp.trans lt.le) t).mp works
    obtain ⟨c,z,free,_,form,_,_⟩ := JacobiPeriodSquareClass.two_minima cop hp lt.le bal
    have cR : c ∣ residualProduct p q := ⟨_,form⟩
    obtain ⟨d,mem,sum⟩ := (exists_hit_iff pp.one_lt lt.le bal free form support).mpr (cR.trans div)
    refine ⟨d,mem,?_⟩
    dsimp only
    rw [sum,←sigma_semiprime pp qp lt.ne,recoverFromSigma_correct pp qp lt]
    exact ⟨pp.one_lt,lt.le,rfl,div⟩
  · rintro ⟨d,_,args⟩
    exact (check_pair hp lt args.1 args.2.1 args.2.2.1).mpr args.2.2.2

/-- The prime support of the false guess 3 nevertheless includes the scale
that recovers the prime pair 13,17. The final divisibility check rejects 3. -/
theorem control_221 :
    3 ∈ scales {3} ∧ recoverFromSigma 221 (221+predecessorSquareSum 221 3+1)=(13,17) ∧
      ¬ residualProduct 13 17 ∣ 3 := by decide +kernel

end PrimeFactors.JacobiPeriodPrimeSupport
