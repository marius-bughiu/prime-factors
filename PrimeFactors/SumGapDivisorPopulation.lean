import PrimeFactors.SquareDivisorClueWindow
import PrimeFactors.AntitoneSumPopulation

/-! How often fixed divisors of a prime half-sum and half-gap can accompany
a short gap. The counting arguments apply to any natural-number partners. -/
namespace PrimeFactors.SumGapDivisorPopulation

open Finset MixedPrefixSample
open scoped Classical
open private PrimeFactors.AntitoneSumPopulation.smaller from PrimeFactors.AntitoneSumPopulation

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes

/-- The scaled half-gap lies in [a,a+L*u), and the half-sum is a multiple
of u. The defining equations avoid truncated subtraction or division. -/
def Admits (u v a L p q : ℕ) : Prop :=
  ∃ e c : ℕ, a≤e ∧ e<a+L*u ∧ p+v*e=u*c ∧ q=p+2*v*e

/-- At fixed p, the divisibility condition singles out one gap residue. -/
theorem same_residue {u v p e f c d : ℕ} (cop : u.Coprime v)
    (he : p+v*e=u*c) (hf : p+v*f=u*d) : e ≡ f [MOD u] := by
  have left : p+v*e ≡ 0 [MOD u] := Nat.modEq_zero_iff_dvd.mpr ⟨c,he⟩
  have right : p+v*f ≡ 0 [MOD u] := Nat.modEq_zero_iff_dvd.mpr ⟨d,hf⟩
  exact Nat.ModEq.cancel_left_of_coprime cop (Nat.ModEq.add_left_cancel' p (left.trans right.symm))

/-- At most one partner can satisfy the short-gap conditions at fixed p. -/
theorem single_partner {u v p q r : ℕ} (cop : u.Coprime v)
    (hq : Admits u v 0 1 p q) (hr : Admits u v 0 1 p r) : q=r := by
  obtain ⟨e,c,_,es,ec,qe⟩ := hq
  obtain ⟨f,d,_,fs,fd,rf⟩ := hr
  simp only [one_mul,zero_add] at es fs
  have ef := (same_residue cop ec fd).eq_of_lt_of_lt es fs
  simp [qe,rf,ef]

/-- Every shifted window containing L full gap periods allows at most L
distinct partners. No primality or oddness is needed for this bound. -/
theorem partners (Q : Finset ℕ) {u v a L p : ℕ} (up : 0<u) (cop : u.Coprime v)
    (ok : ∀ q ∈ Q, Admits u v a L p q) : Q.card≤L := by
  obtain empty|nonempty := Q.eq_empty_or_nonempty
  · simp [empty]
  obtain ⟨r,hr⟩ := nonempty
  obtain ⟨f,d,_,_,fd,_⟩ := ok r hr
  let lane := (Ioc a (a+L*u)).filter fun m => m ≡ f+1 [MOD u]
  have subset : Q⊆lane.image (fun k => p+2*v*(k-1)) := by
    intro q hq
    obtain ⟨e,c,lo,hi,ec,qe⟩ := ok q hq
    refine mem_image.mpr ⟨e+1,mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,
      (same_residue cop ec fd).add_right 1⟩,?_⟩
    simpa using qe.symm
  exact (card_le_card subset).trans ((card_image_le).trans_eq
    (SquareDivisorClueWindow.full_periods a L (f+1) up))

/-- Convert the original half-sum and half-gap conditions for odd entries
into the division-free short-window certificate. -/
theorem short_of_divisors {u v p q : ℕ} (vp : 0<v) (po : Odd p) (qo : Odd q) (pq : p≤q)
    (sum_div : u∣(p+q)/2) (gap_div : v∣(q-p)/2) (short : (q-p)/2<u*v) :
    Admits u v 0 1 p q := by
  obtain ⟨e,ve⟩ := gap_div
  obtain ⟨c,uc⟩ := sum_div
  have eu : e<u := by
    rw [ve,Nat.mul_comm u v] at short
    exact (Nat.mul_lt_mul_left vp).mp short
  obtain ⟨i,ip⟩ := po
  obtain ⟨j,jq⟩ := qo
  refine ⟨e,c,Nat.zero_le _,by simpa using eu,by omega,?_⟩
  rw [Nat.mul_assoc]
  omega

/-- The short-window certificate is exactly the two divisibility conditions
and strict half-gap bound on a sorted pair of odd integers. -/
theorem short_iff {u v p q : ℕ} (vp : 0<v) (po : Odd p) (qo : Odd q) (pq : p≤q) :
    Admits u v 0 1 p q ↔ u∣(p+q)/2 ∧ v∣(q-p)/2 ∧ (q-p)/2<u*v := by
  constructor
  · rintro ⟨e,c,_,eu,eq,rfl⟩
    simp only [zero_add,one_mul] at eu
    rw [Nat.mul_assoc]
    have total : (p+(p+2*(v*e)))/2=u*c := by omega
    have diff : (p+2*(v*e)-p)/2=v*e := by omega
    exact ⟨⟨c,total⟩,⟨e,diff⟩,by rw [diff,Nat.mul_comm u v]; exact Nat.mul_lt_mul_of_pos_left eu vp⟩
  · rintro ⟨hs,hg,lt⟩
    exact short_of_divisors vp po qo pq hs hg lt

/-- Eligible full-width prime pairs, each included once in increasing order. -/
noncomputable def hits (u v a L : ℕ) : Finset (ℕ×ℕ) :=
  eligible.filter fun z => Admits u v a L z.1 z.2

private theorem mem_hits {u v a L : ℕ} {z : ℕ×ℕ} :
    z∈hits u v a L ↔ z∈eligible ∧ Admits u v a L z.1 z.2 := mem_filter

attribute [local irreducible] hits

private theorem count_on (A : Finset (ℕ×ℕ)) (P : Finset ℕ) (u v a L : ℕ)
    (up : 0<u) (cop : u.Coprime v) (small : ∀ z∈A, z.1∈P)
    (good : ∀ z∈A, Admits u v a L z.1 z.2) : A.card≤L*P.card := by
  apply card_le_mul_card_image_of_maps_to (f:=Prod.fst) small
  intro p _
  let row := A.filter fun z => z.1=p
  let Q := row.image Prod.snd
  have inject : row.card=Q.card := (card_image_of_injOn (s:=row) (f:=Prod.snd) (by
    intro x hx y hy eq
    exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) eq)).symm
  change row.card ≤ L
  rw [inject]
  apply partners Q (p:=p) (a:=a) up cop
  intro q hq
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
  obtain ⟨mem,eq⟩ := mem_filter.mp hz
  simpa only [eq] using good z mem

theorem count (u v a L : ℕ) (up : 0<u) (cop : u.Coprime v) :
    (hits u v a L).card ≤ L*primes.card :=
  count_on (hits u v a L) primes u v a L up cop
    (fun z hz => PrimeFactors.AntitoneSumPopulation.smaller (z:=z) (mem_hits.mp hz).1)
    (fun _ hz => (mem_hits.mp hz).2)

/-- Uniform frequency among the full eligible population for any fixed
coprime u,v and any shifted window of L positive periods. -/
theorem fraction (u v a L : ℕ) (up : 0<u) (cop : u.Coprime v) (lp : 0<L) :
    2^1007*(hits u v a L).card < L*eligible.card := by
  have cap : 41056*2^1007≤X := by decide +kernel
  have per := count u v a L up cop
  have norm := Nat.mul_lt_mul_of_pos_left SquareRootPhasePopulation.marginal lp
  apply Nat.lt_of_mul_lt_mul_left (a:=41056)
  calc
    41056*(2^1007*(hits u v a L).card) ≤ X*(L*primes.card) := by
      rw [←Nat.mul_assoc]
      exact Nat.mul_le_mul cap per
    _ = L*(X*primes.card) := by ac_rfl
    _ < L*(41056*eligible.card) := norm
    _ = _ := by ac_rfl

theorem short_fraction (u v : ℕ) (up : 0<u) (cop : u.Coprime v) :
    2^1007*(hits u v 0 1).card < eligible.card := by
  exact (fraction u v 0 1 up cop (by decide)).trans_le (Nat.one_mul eligible.card).le

end PrimeFactors.SumGapDivisorPopulation
