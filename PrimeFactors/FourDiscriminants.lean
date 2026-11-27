import PrimeFactors.JacobiSeparation
import PrimeFactors.ReducedSmoothReadout
import PrimeFactors.CharacterDivisorColumn

/-! Cover the four local quadratic character pairs with a public anchor of
negative Jacobi symbol and a list containing one nonresidue at each prime. -/
namespace PrimeFactors.FourDiscriminants
open Finset

/-- Only the anchor and the public list of primes are needed to build the menu. -/
noncomputable def menu (a : ℤ) (primes : Finset ℤ) : Finset ℤ :=
  {1,a} ∪ primes ∪ primes.image (a*·)

private theorem four (a b x y s t : ℤ) (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1)
    (hx : x=1 ∨ x= -1) (hy : y=1 ∨ y= -1) (anchor : a*b= -1)
    (other : (a=1 → x= -1) ∧ (b=1 → y= -1))
    (hs : s=1 ∨ s= -1) (ht : t=1 ∨ t= -1) :
    (s=1 ∧ t=1) ∨ (s=a ∧ t=b) ∨ (s=x ∧ t=y) ∨ (s=a*x ∧ t=b*y) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num at *

/-- The two hidden nonresidues may be different members of the same public
list. The algorithm never has to identify which of them works. -/
theorem covers {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (a : ℤ) (primes : Finset ℤ) (ja : jacobiSym a (p*q)= -1)
    (ap : (a : ZMod p) ≠ 0) (aq : (a : ZMod q) ≠ 0)
    (both : ∀ z ∈ primes, (z : ZMod p) ≠ 0 ∧ (z : ZMod q) ≠ 0)
    (np : ∃ z ∈ primes, legendreSym p z= -1) (nq : ∃ z ∈ primes, legendreSym q z= -1)
    (s t : ℤ) (hs : s=1 ∨ s= -1) (ht : t=1 ∨ t= -1) :
    ∃ d ∈ menu a primes, legendreSym p d=s ∧ legendreSym q d=t := by
  have product : legendreSym p a * legendreSym q a= -1 := by
    simpa only [jacobiSym.mul_right' a hp.out.ne_zero hq.out.ne_zero,
      ← jacobiSym.legendreSym.to_jacobiSym] using ja
  obtain ⟨z,mem,op⟩ : ∃ z ∈ primes, (legendreSym p a=1 → legendreSym p z= -1) ∧
      (legendreSym q a=1 → legendreSym q z= -1) := by
    by_cases h : legendreSym p a=1
    · obtain ⟨z,hz,hn⟩ := np
      refine ⟨z,hz,fun _ => hn,fun hq => ?_⟩
      norm_num [h,hq] at product
    · obtain ⟨z,hz,hn⟩ := nq
      exact ⟨z,hz,fun hp => (h hp).elim,fun _ => hn⟩
  have cover := four _ _ _ _ _ _ (legendreSym.eq_one_or_neg_one p ap)
    (legendreSym.eq_one_or_neg_one q aq) (legendreSym.eq_one_or_neg_one p (both z mem).1)
    (legendreSym.eq_one_or_neg_one q (both z mem).2) product op hs ht
  rcases cover with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨1,by simp [menu],by simp,by simp⟩
  · exact ⟨a,by simp [menu],rfl,rfl⟩
  · exact ⟨z,by simp [menu,mem],rfl,rfl⟩
  · exact ⟨a*z,by simp [menu,Finset.mem_image_of_mem _ mem],legendreSym.mul ..,legendreSym.mul ..⟩

theorem size_bound (a : ℤ) (primes : Finset ℤ) : (menu a primes).card ≤ 2+2*primes.card := by
  unfold menu
  have h₁ := card_union_le ({1,a} ∪ primes) (primes.image (a*·))
  have h₂ := card_union_le ({1,a} : Finset ℤ) primes
  have h₃ := card_image_le (s := primes) (f := (a*·))
  have h₄ : ({1,a} : Finset ℤ).card ≤ 2 := by
    simpa using card_insert_le 1 ({a} : Finset ℤ)
  omega

noncomputable def primeList (bound : ℕ) : Finset ℤ :=
  ((range (bound+1)).filter Nat.Prime).image (fun b : ℕ => (b : ℤ))

private theorem mem_primeList {B b : ℕ} (hb : b.Prime) (le : b≤B) :
    (b:ℤ) ∈ primeList B :=
  mem_image.mpr ⟨b,mem_filter.mpr ⟨mem_range.mpr (by omega),hb⟩,rfl⟩

/-- Assemble the finite number-theory inputs to the deterministic guarantee.
The first analytic premise supplies the anchor. The remaining two give a
bounded prime nonresidue at each possible hidden prime. -/
theorem bounded_cover {p q A B : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (odd : q≠2) (anchor : SmallPrimeOutside (p*q) A)
    (bp : B<p) (bq : B<q)
    (np : ∃ b : ℕ, b.Prime ∧ b≤B ∧ legendreSym p b= -1)
    (nq : ∃ b : ℕ, b.Prime ∧ b≤B ∧ legendreSym q b= -1) :
    ∃ a : ℕ, a.Prime ∧ a≤A ∧ jacobiSym a (p*q)= -1 ∧
      ∀ s t : ℤ, (s=1 ∨ s= -1) → (t=1 ∨ t= -1) →
      ∃ d ∈ menu a (primeList B), legendreSym p d=s ∧ legendreSym q d=t := by
  obtain ⟨a,pa,le,ja⟩ := CharacterDivisorColumn.bounded_prime hp.out hq.out diff odd anchor
  have prod : legendreSym p a * legendreSym q a= -1 := by
    simpa only [jacobiSym.mul_right' (a:ℤ) hp.out.ne_zero hq.out.ne_zero,
      ← jacobiSym.legendreSym.to_jacobiSym] using ja
  have nzp : ((a:ℤ) : ZMod p)≠0 := by
    intro h
    rw [(legendreSym.eq_zero_iff p a).mpr h,zero_mul] at prod
    omega
  have nzq : ((a:ℤ) : ZMod q)≠0 := by
    intro h
    rw [(legendreSym.eq_zero_iff q a).mpr h,mul_zero] at prod
    omega
  refine ⟨a,pa,le,ja,covers _ _ ja nzp nzq ?_ ?_ ?_⟩
  · intro z hz
    obtain ⟨b,mem,rfl⟩ := mem_image.mp hz
    obtain ⟨small,pr⟩ := mem_filter.mp mem
    have h := mem_range.mp small
    simp only [Int.cast_natCast,Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact ⟨Nat.not_dvd_of_pos_of_lt pr.pos (by omega),Nat.not_dvd_of_pos_of_lt pr.pos (by omega)⟩
  · obtain ⟨b,prime,small,neg⟩ := np
    exact ⟨b,mem_primeList prime small,neg⟩
  · obtain ⟨b,prime,small,neg⟩ := nq
    exact ⟨b,mem_primeList prime small,neg⟩

/-- The trace of the ratio of two conjugates has the chosen discriminant up
to a square. The public denominator is checked for invertibility first. -/
theorem trace_discriminant {K : Type*} [Field K] (d t : K) (unit : t^2-d≠0) :
    (2*(t^2+d)/(t^2-d))^2-4 = d*(4*t/(t^2-d))^2 := by
  field_simp
  ring

/-- For an accepted norm-one base, covering either reduced signed order
separates the coordinates. The prime-power schedule is computed from the
public bound and cap while the signs enter only in the guarantee. -/
theorem signed_readout {p q : ℕ} (hp : 1<p) (hq : 1<q) (s t : Bool)
    {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
    (x : G) (y : H) (hx : x^signedTorusOrder p s=1) (hy : y^signedTorusOrder q t=1)
    (bound cap : ℕ) :
    let e := signedTorusOrder (p*q) (s==t)
    let g := (signedTorusOrder p s).gcd (signedTorusOrder q t)
    let powers := ReducedSmoothReadout.schedule bound cap
    (x^e,y^e)≠1 →
    (signedTorusOrder p s/g ∣ powers.prod ∨ signedTorusOrder q t/g ∣ powers.prod) →
    ReducedSmoothReadout.separated (ReducedSmoothReadout.readout (x^e,y^e) powers) := by
  intro e g powers accepted covered
  apply ReducedSmoothReadout.readout_separates powers (ReducedSmoothReadout.schedule_powers bound cap) _ _
    (signedTorus_coprime hp hq s t x y hx hy) accepted
  rcases covered with left | right
  · exact Or.inl ((signedTorus_residual (by omega) (by omega) s t x hx).trans left)
  · have reduced := signedTorus_residual (by omega : 0<q) (by omega : 0<p) t s y hy
    rw [Nat.mul_comm q p,Bool.beq_comm (a:=t) (b:=s),Nat.gcd_comm (signedTorusOrder q t)] at reduced
    exact Or.inr (reduced.trans right)

end PrimeFactors.FourDiscriminants
