import PrimeFactors.FloorShiftDistinctSums
import PrimeFactors.CeilingShiftDistances
import PrimeFactors.FiniteBinCollisionPopulation

/-! An unconditional lower bound on genuine lower-center recoveries. We
count separated prime pairs, so the counted successes extend well beyond
the start of ordinary Fermat search. -/
namespace PrimeFactors.FloorShiftRecoveryPopulation

open Finset MixedPrefixSample FloorSquareShift FloorShiftDyadicCenters
open private PrimeFactors.FloorSquareShift.floor_bounds from PrimeFactors.FloorSquareShift
open CeilingShiftDistances FiniteBinCollisionPopulation
open private PrimeFactors.FiniteBinCollisionPopulation.collision_bound
  PrimeFactors.FiniteBinCollisionPopulation.band_price PrimeFactors.FiniteBinCollisionPopulation.eligible_incidence
  from PrimeFactors.FiniteBinCollisionPopulation
open private PrimeFactors.FirstSumMenuPopulation.collision_count from PrimeFactors.FirstSumMenuPopulation
open private PrimeFactors.MonotoneClosePrimeLower.prime_ratio from PrimeFactors.MonotoneClosePrimeLower
open private PrimeFactors.GaussianGateAggregateCost.info from PrimeFactors.GaussianGateAggregateCost
open private PrimeFactors.SeparatedMonotonePopulation.prime_first from PrimeFactors.SeparatedMonotonePopulation
open scoped Classical
attribute [local irreducible] eligible primes upperPrimes upperBand
set_option exponentiation.threshold 8192

private abbrev modulus : ℕ := 2^513
private abbrev offset : ℕ := 2^1022

/-- A common low residue guarantees an exact reading in exponent row
1023, for all eligible pairs satisfying this congruence. -/
theorem exact_row {p q : ℕ} (ok : (p,q)∈eligible) (same : p ≡ q [MOD modulus]) :
    ∃ s, s≤(p*q).sqrt ∧ twoPart (p*q-s^2)=2^1023 ∧ proposed (p*q) s=p+q := by
  obtain ⟨lo,lt,hi,odd,_⟩ := PrimeFactors.GaussianGateAggregateCost.info ok
  obtain ⟨h,divides⟩ := (Nat.modEq_iff_dvd' lt.le).mp same
  let d := 2^512*h
  let M := p+d
  let s := M-offset
  have qEq : q=p+2*d := by dsimp [d]; change q-p=2^513*h at divides; omega
  have dBound : d<offset := by unfold offset; omega
  have back : s+offset=M := Nat.sub_add_cancel (by dsimp [M,offset]; omega)
  have mid : p+q=2*M := by dsimp [M]; omega
  have sp : s≤p := by dsimp [M] at back; omega
  have floor : s≤(p*q).sqrt := Nat.le_sqrt'.mpr (by
    simpa only [pow_two] using Nat.mul_le_mul sp (sp.trans lt.le))
  have sq := (Nat.pow_le_pow_left floor 2).trans (Nat.sqrt_le' (p*q))
  let R := p*q-s^2
  have remEq : R+s^2=p*q := Nat.sub_add_cancel sq
  have diff : M^2=p*q+d^2 := by dsimp [M]; rw [qEq]; ring
  have identity : R+(2*offset)*(2*2^1020+2*h^2)=(2*offset)*M := by
    have sqeq : d^2=4*offset*h^2 := by dsimp [d]; rw [mul_pow]; congr 1
    have ex : s^2+2*offset*M=M^2+offset^2 := by rw [←back]; ring
    rw [sqeq] at diff
    nlinarith only [remEq,diff,ex]
  let t := 2*2^1020+2*h^2
  have fits : t≤M := Nat.le_of_mul_le_mul_left
    (by change (2*offset)*(2*2^1020+2*h^2)≤(2*offset)*M; omega) (by positivity : 0<2*offset)
  have split : R=(M-t)*(2*offset) := by
    rw [Nat.sub_mul,Nat.mul_comm M,Nat.mul_comm t]; change R=(2*offset)*M-(2*offset)*(2*2^1020+2*h^2)
    omega
  have oddFactor : Odd (M-t) := by
    obtain ⟨k,pk⟩ := odd
    have parity : M%2=1 := by dsimp [M,d]; omega
    have tEven : t%2=0 := by dsimp [t]; omega
    exact Nat.odd_iff.mpr (by omega)
  have part : twoPart R=2^1023 := by
    rw [split,show 2*offset=2^1023 by decide +kernel,twoPart_odd_mul _ oddFactor]
  exact ⟨s,floor,part,by change 2*s+twoPart R=p+q; rw [part,mid]; unfold offset at back; omega⟩

private noncomputable def aligned : Finset (ℕ×ℕ) := eligible.filter fun z => z.1 ≡ z.2 [MOD modulus]
private noncomputable def close : Finset (ℕ×ℕ) := aligned.filter fun z => z.2-z.1<2^1000
noncomputable def separated : Finset (ℕ×ℕ) := aligned \ close

private theorem matching_lower : eligible.card < (12*modulus)*aligned.card := by
  let key (p : ℕ) := p%modulus
  have bounded (p : ℕ) (_ : p∈upperBand) : key p<modulus := Nat.mod_lt _ (by decide +kernel)
  have coll := PrimeFactors.FirstSumMenuPopulation.collision_count upperBand key modulus bounded
  have count := PrimeFactors.FiniteBinCollisionPopulation.collision_bound _ aligned upperBand key rfl
    (fun p hp q hq lt eqn => mem_filter.mpr ⟨band_pair_eligible hp hq lt,eqn⟩)
  have sub := card_le_card upper_subset
  have many : 1000*modulus≤upperPrimes.card := by
    have h := ChebyshevPrimeSample.prime_count
    change 11*X<35500*(upperPrimes.card-1) at h
    have room : 35500*(1000*modulus)≤11*X := by decide +kernel
    omega
  exact PrimeFactors.FiniteBinCollisionPopulation.band_price
    (coll.trans (Nat.mul_le_mul_left _ count)) (many.trans sub)
    (PrimeFactors.MonotoneClosePrimeLower.prime_ratio.trans_le (Nat.mul_le_mul_left _ sub))
    PrimeFactors.FiniteBinCollisionPopulation.eligible_incidence

private theorem gap_quotients (A : Finset (ℕ×ℕ)) (P : Finset ℕ) (b c : ℕ)
    (data : ∀ z∈A,z.1∈P ∧ z.2=z.1+b*((z.2-z.1)/b) ∧ (z.2-z.1)/b<c) :
    A.card ≤ P.card*c := by
  let cover := (P ×ˢ range c).image fun t => (t.1,t.1+b*t.2)
  have sub : A⊆cover := by
    rintro ⟨p,q⟩ h
    obtain ⟨pm,form,small⟩ := data _ h
    exact mem_image.mpr ⟨(p,(q-p)/b),mem_product.mpr ⟨pm,mem_range.mpr small⟩,Prod.ext rfl form.symm⟩
  exact (card_le_card sub).trans (card_image_le.trans_eq (by simp only [card_product,card_range]))

private theorem close_cap : close.card ≤ primes.card*2^487 := by
  apply gap_quotients close primes modulus (2^487)
  rintro ⟨p,q⟩ h
  obtain ⟨hm,near⟩ := mem_filter.mp h
  obtain ⟨ok,same⟩ := mem_filter.mp hm
  have lt := (PrimeFactors.GaussianGateAggregateCost.info ok).2.1
  have div := (Nat.modEq_iff_dvd' lt.le).mp same
  have id := Nat.mul_div_cancel' div
  change 2^513*((q-p)/2^513)=q-p at id
  change q-p<2^1000 at near
  dsimp only [modulus,Prod.fst,Prod.snd]
  exact ⟨PrimeFactors.SeparatedMonotonePopulation.prime_first ok,by omega,by omega⟩

private theorem prices {p e n a s : ℕ} (marg : 2^1023*p<41056*e)
    (cap : n≤p*2^487) (all : e<(12*2^513)*a) (part : a≤n+s) : e<2^517*s := by
  have step := Nat.mul_le_mul_left (2^536) cap
  have id : (2^536)*(p*2^487)=(2^1023)*p := by
    calc
      _ = (2^536*2^487)*p := by ac_rfl
      _ = _ := by rw [show (2:ℕ)^536*2^487=2^1023 by decide +kernel]
  rw [id] at step
  omega

private theorem close_or_separated : aligned.card≤close.card+separated.card := by
  have cover : aligned⊆close ∪ separated := by
    intro z hz
    by_cases near : z∈close
    · exact mem_union_left _ near
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hz,near⟩)
  exact (card_le_card cover).trans (card_union_le close separated)

private theorem marginal_bound : 2^1023*primes.card<41056*eligible.card := by
  rw [show (2:ℕ)^1023=X from rfl]
  exact SquareRootPhasePopulation.marginal

private theorem aligned_bound : eligible.card<(12*2^513)*aligned.card := by
  rw [show (2:ℕ)^513=modulus from rfl]
  exact matching_lower

/-- Strictly more than one in 2^517 eligible pairs has a gap of at least
2^1000 and an exact reading at the stated row. -/
theorem lower : eligible.card < 2^517*separated.card := by
  exact prices (p:=primes.card) (e:=eligible.card) (n:=close.card) (a:=aligned.card)
    (s:=separated.card) marginal_bound close_cap aligned_bound close_or_separated

theorem separated_hit {p q : ℕ} (h : (p,q)∈separated) :
    2^1000≤q-p ∧ ∃ s, s≤(p*q).sqrt ∧ twoPart (p*q-s^2)=2^1023 ∧ proposed (p*q) s=p+q := by
  obtain ⟨hit,miss⟩ := mem_sdiff.mp h
  obtain ⟨ok,same⟩ := mem_filter.mp hit
  exact ⟨le_of_not_gt (fun small => miss (mem_filter.mpr ⟨hit,small⟩)),exact_row ok same⟩

/-- The ordinary consecutive Fermat scan includes at least this many
positions strictly before the true midpoint on every counted success. -/
theorem fermat_before {p q : ℕ} (member : (p,q)∈separated) :
    2^973 ≤ (Ico (ceilSqrt (p*q)) ((p+q)/2)).card := by
  have gap := (separated_hit member).1
  have ok : (p,q)∈eligible := (mem_filter.mp (mem_sdiff.mp member).1).1
  obtain ⟨pl,ord,qh,op,oq⟩ := PrimeFactors.GaussianGateAggregateCost.info ok
  let M := (p+q)/2
  let d := (q-p)/2
  have double : 2*M=p+q := by obtain ⟨a,pa⟩ := op; obtain ⟨b,qb⟩ := oq; dsimp [M]; omega
  have diff : p+2*d=q := by obtain ⟨a,pa⟩ := op; obtain ⟨b,qb⟩ := oq; dsimp [d]; omega
  have identity : M^2=p*q+d^2 := by
    have mid : M=p+d := by omega
    rw [mid,←diff]; ring
  have low : 2^999≤d := by omega
  have upper : M≤2^1024 := by omega
  have room : 2*(2^1024*2^973:ℕ)=(2^999)^2 := by decide +kernel
  have cost : 2*(M*2^973)≤d^2 := calc
    _ ≤ 2*(2^1024*2^973) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ upper)
    _ = (2^999)^2 := room
    _ ≤ d^2 := Nat.pow_le_pow_left low 2
  let start := M-2^973
  have back : start+2^973=M := Nat.sub_add_cancel (by omega)
  have expand : start^2+2*(M*2^973)=M^2+(2^973)^2 := by rw [←back]; ring
  have first : ceilSqrt (p*q)≤start := ceilSqrt_le_iff.mpr (by omega)
  rw [Nat.card_Ico]
  change 2^973 ≤ M-ceilSqrt (p*q)
  omega


/-- Row 1023 takes only the product and its public width. On each member
of the separated family its at most two proposed sums contain the true sum. -/
theorem public_row {p q : ℕ} (member : (p,q)∈separated) :
    p+q∈FloorShiftDistinctSums.rowSums (p*q) 1024 1023 ∧
    (FloorShiftDistinctSums.rowSums (p*q) 1024 1023).card≤2 := by
  have ok : (p,q)∈eligible := (mem_filter.mp (mem_sdiff.mp member).1).1
  obtain ⟨_,lt,hi,op,oq⟩ := PrimeFactors.GaussianGateAggregateCost.info ok
  obtain ⟨_,s,floor,part,hit⟩ := separated_hit member
  rw [FloorShiftDyadicCenters.proposed,part] at hit
  have low := (PrimeFactors.FloorSquareShift.floor_bounds lt).2.2
  constructor
  · apply mem_image.mpr
    refine ⟨s,(FloorShiftCenterCompression.mem_row (op.mul oq) (Nat.sqrt_le' _)
      (by decide : 1≤1023) (by decide : 1023≤1024)).mpr ?_,hit⟩
    exact ⟨floor,hit.symm ▸ low,by rw [hit]; omega,
      (FloorShiftCenterCompression.part_iff _ (by decide : 1≤1023)).mp part⟩
  · exact card_image_le.trans (FloorShiftCenterCompression.card_row ..)

end PrimeFactors.FloorShiftRecoveryPopulation
