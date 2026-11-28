import PrimeFactors.WideResiduePrimeSupply
import PrimeFactors.ProductPrefixFactorBand
import PrimeFactors.ResiduePairMultiplicity
import PrimeFactors.LocalSumMenu
import PrimeFactors.Certificate

/-! What the leading product word and one product remainder can exclude.
The prime counts use the published Dirichlet-GRH endpoint estimates as
explicit hypotheses. Products vary while both observations stay fixed. -/
namespace PrimeFactors.ObservedPrefixSumResidues

open ProductPrefixFactorBand (A B W)
open WideResiduePrimeSupply (BandEndpoints inBand)
open AdmissibleSumRealization (TwoRepresentatives Realized)
open ResiduePairMultiplicity (ManyRepresentatives)

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- A full 2,048-bit product with the supplied prefix bin, product remainder
and sum remainder. The two distinct primes each have exactly 1,024 bits. -/
def Fits {m : ℕ} (K h : ℕ) (r s : ZMod m) : Prop :=
  ∃ p q : ℕ, 2^1023 ≤ p ∧ p<q ∧ q<B ∧ p.Prime ∧ q.Prime ∧
    K≤p*q ∧ p*q<K+2^(2048-h) ∧ ((p*q : ℕ) : ZMod m)=r ∧ ((p+q : ℕ) : ZMod m)=s

def Endpoints (m K h : ℕ) : Prop :=
  ∀ a<m, a.Coprime m → ∃ c : ℝ, BandEndpoints m a (A K) (W h) c

private theorem width_covers {h : ℕ} (cap : h≤485) :
    2^(485-h)*2^537 = W h := by
  unfold W
  rw [←pow_add]
  congr 1
  omega

private theorem population {K h m : ℕ} (hpos : 1≤h) (cap : h≤485)
    (bottom : 2^2047≤K) (top : K+2^(2048-h)≤B^2)
    (lo : 3≤m) (hi : m≤2^(485-h)) (endpoints : Endpoints m K h) :
    ManyRepresentatives m (A K+1) (A K+W h+1) (2^526) := by
  obtain ⟨floorA,ceilA⟩ := ProductPrefixFactorBand.factor_window hpos cap bottom top
  have mA : m≤A K := hi.trans ((Nat.pow_le_pow_right (by decide : 0<2)
    (show 485-h≤1023 by omega)).trans floorA)
  have mW : m*2^537≤W h := (Nat.mul_le_mul_right _ hi).trans_eq (width_covers cap)
  have phi : 0<m.totient := Nat.totient_pos.mpr (by omega)
  have w : (m.totient : ℝ)*(2:ℝ)^537 ≤ W h := by
    exact_mod_cast (Nat.mul_le_mul_right (2^537) (Nat.totient_le m)).trans mW
  have frac : (2:ℝ)^537/710 ≤ (W h:ℝ)/(710*(m.totient:ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left w (by norm_num : (0:ℝ)≤710)]
  intro a ha cop
  obtain ⟨c,hc⟩ := endpoints a ha cop
  have left := WideResiduePrimeSupply.band_lower lo mA floorA ceilA.le (c:=c) hc
  have margin : (2:ℝ)^526 + 26400*2^512 < 2^537/710 := by norm_num
  have size : (2:ℝ)^526 < ((inBand m a (A K) (W h)).card:ℝ) := by linarith only [margin,frac,left]
  have same : inBand m a (A K) (W h) =
      ResiduePairMultiplicity.primes m (A K+1) (A K+W h+1) a := by
    ext p
    rw [WideResiduePrimeSupply.mem_band, ResiduePairMultiplicity.mem_primes]
    constructor
    · rintro ⟨prime, residue, lower, upper⟩
      exact ⟨by omega, by omega, prime, residue⟩
    · rintro ⟨lower, upper, prime, residue⟩
      exact ⟨prime, residue, by omega, by omega⟩
  rw [same] at size
  exact_mod_cast size.le

/-- Across products with these observations, a sum residue occurs exactly
when it is locally admissible at the observed modulus. -/
theorem fits_iff {K h m : ℕ} (hpos : 1≤h) (cap : h≤485)
    (bottom : 2^2047≤K) (top : K+2^(2048-h)≤B^2)
    (lo : 3≤m) (hi : m≤2^(485-h)) (endpoints : Endpoints m K h)
    (r s : ZMod m) (unit : IsUnit r) : Fits K h r s ↔ AdmissibleSum r s := by
  letI : NeZero m := ⟨by omega⟩
  constructor
  · rintro ⟨p,q,_,_,_,_,_,_,_,hr,hs⟩
    exact ⟨p,q,by simpa only [Nat.cast_mul] using hr,by simpa only [Nat.cast_add] using hs⟩
  · intro pass
    have supply := population hpos cap bottom top lo hi endpoints
    have two := ResiduePairMultiplicity.two_of_many supply (by decide +kernel)
    obtain ⟨p,q,pl,pq,qu,pp,qp,hr,hs⟩ := (AdmissibleSumRealization.iff_realized two r s unit).mp pass
    obtain ⟨floorA,ceilA⟩ := ProductPrefixFactorBand.factor_window hpos cap bottom top
    have between := ProductPrefixFactorBand.product_window hpos cap bottom top
      (p:=p) (q:=q) (by omega) (by omega) (by omega) (by omega)
    exact ⟨p,q,by omega,pq,by omega,pp,qp,between.1.le,between.2,hr,hs⟩

/-- Even after fixing the leading 232 bits, every odd 250-bit remainder
admits at least this many distinct values of the *true* sum modulo 2^250
across compatible products. -/
theorem observed_232_250 {K n : ℕ} (bottom : 2^2047≤K) (top : K+2^(2048-232)≤B^2)
    (odd : ¬2∣n) (endpoints : Endpoints (2^250) K 232) :
    2^244 ≤ Nat.card {s : ZMod (2^250) // Fits K 232 (n : ZMod (2^250)) s} := by
  have unit : IsUnit (n : ZMod (2^250)) := (ZMod.isUnit_iff_coprime _ _).mpr
    ((Nat.prime_two.coprime_iff_not_dvd.mpr odd).symm.pow_right _)
  have eq : (fun s : ZMod (2^250) => Fits K 232 (n : ZMod (2^250)) s) = AdmissibleSum (n : ZMod (2^250)) := by
    funext s
    exact propext (fits_iff (by decide) (by decide) bottom top (by decide +kernel)
      (by decide +kernel) endpoints n s unit)
  change 2^244 ≤ Nat.card (Subtype (fun s : ZMod (2^250) => Fits K 232 (n : ZMod (2^250)) s))
  rw [eq]
  change 2^244 ≤ LocalSumMenu.count n (2^250)
  have cnt := LocalSumMenu.dyadic_density (n:=n) odd 250
  exact (Nat.mul_le_mul_left_iff (by decide : 0 < 64)).mp
    ((show 64*2^244 = (2:ℕ)^250 by decide +kernel).le.trans cnt)

/-- The bounded products counted here share the complete leading word when
the bin is aligned. Unique prime factorization keeps distinct products separate. -/
theorem many_products {K h m : ℕ} (hpos : 1≤h) (cap : h≤485)
    (bottom : 2^2047≤K) (top : K+2^(2048-h)≤B^2)
    (lo : 3≤m) (hi : m≤2^(485-h)) (endpoints : Endpoints m K h)
    (r s : ZMod m) (unit : IsUnit r) (pass : AdmissibleSum r s) :
    let values := ResiduePairMultiplicity.products (A K+1) (A K+W h+1) r s
    2^1050 ≤ values.card ∧ ∀ N∈values, K<N ∧ N<K+2^(2048-h) := by
  letI : NeZero m := ⟨by omega⟩
  dsimp only
  have supply := population hpos cap bottom top lo hi endpoints
  have count := ResiduePairMultiplicity.multiplicity supply unit pass
  refine ⟨(show 2^1050=(2:ℕ)^526/2*(2^526-2^526/2) by decide +kernel).le.trans count,?_⟩
  intro N hN
  obtain ⟨p,q,pl,pq,qu,_,_,rfl,_,_⟩ := ResiduePairMultiplicity.mem_products.mp hN
  exact ProductPrefixFactorBand.product_window hpos cap bottom top
    (p:=p) (q:=q) (by omega) (by omega) (by omega) (by omega)

/-- A short list chosen from these observations misses a true sum residue
shared by at least 2^1050 compatible integer products. -/
theorem missed_by_list {K n : ℕ} (bottom : 2^2047≤K) (top : K+2^(2048-232)≤B^2)
    (odd : ¬2∣n) (endpoints : Endpoints (2^250) K 232)
    (guesses : Finset (ZMod (2^250))) (short : guesses.card < 2^244) :
    ∃ s ∉ guesses, Fits K 232 (n : ZMod (2^250)) s ∧
      2^1050 ≤ (ResiduePairMultiplicity.products (A K+1) (A K+W 232+1) (n : ZMod (2^250)) s).card := by
  classical
  have missing : ∃ s : ZMod (2^250), Fits K 232 (n : ZMod (2^250)) s ∧ s∉guesses := by
    by_contra! all
    let f (x : {s : ZMod (2^250) // Fits K 232 (n : ZMod (2^250)) s}) : guesses := ⟨x.val,all _ x.property⟩
    have upper := Nat.card_le_card_of_injective f (fun _ _ h =>
      Subtype.ext (congrArg (fun g : guesses => g.val) h))
    have size : Nat.card guesses = guesses.card := by simp [Nat.card_eq_fintype_card]
    rw [size] at upper
    exact (not_le_of_gt short) ((observed_232_250 bottom top odd endpoints).trans upper)
  obtain ⟨s,fit,out⟩ := missing
  have unit : IsUnit (n : ZMod (2^250)) := (ZMod.isUnit_iff_coprime _ _).mpr
    ((Nat.prime_two.coprime_iff_not_dvd.mpr odd).symm.pow_right _)
  have pass := (fits_iff (by decide) (by decide) bottom top (by decide +kernel)
    (by decide +kernel) endpoints n s unit).mp fit
  exact ⟨s,out,fit,(many_products (by decide) (by decide) bottom top (by decide +kernel)
    (by decide +kernel) endpoints n s unit pass).1⟩

/-- Three 24-bit products with the same leading twelve bits and trailing
eight bits have different true factor sums even modulo 256. -/
theorem small_observations :
    ExactFactorization 12518833 [3229,3877] ∧ ExactFactorization 12519601 [3251,3851] ∧
    ExactFactorization 12520369 [3329,3761] ∧
    (∀ N ∈ ([12518833,12519601,12520369] : List ℕ), 2^23≤N ∧ N<2^24 ∧ N/4096=3056 ∧ N%256=177) ∧
    [(3229+3877)%256,(3251+3851)%256,(3329+3761)%256] = ([194,190,178] : List ℕ) := by
  simp only [ExactFactorization,List.prod_cons,List.prod_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq]
  norm_num

end PrimeFactors.ObservedPrefixSumResidues
