import PrimeFactors.GaussianSquareMenu
import PrimeFactors.CyclotomicGaussianPrecision

/-! A single product-only test looks for a two-squares representation with
one coordinate equal to the floor square root. It has a small co-coordinate,
so the fixed-coordinate population bound applies uniformly at full width. -/
namespace PrimeFactors.GaussianSquareRemainder

open Finset MixedPrefixSample CyclotomicGaussianReading GaussianSquareMenu
open private PrimeFactors.SmallNormSquarePopulation.pair_data from PrimeFactors.SmallNormSquarePopulation
open scoped Classical
set_option exponentiation.threshold 8192
attribute [local irreducible] sample eligible

def remainder (N : ℕ) := N-N.sqrt^2

def Passes (N : ℕ) : Prop := (remainder N).sqrt^2=remainder N

theorem representation {N : ℕ} (hit : Passes N) : N=N.sqrt^2+(remainder N).sqrt^2 := by
  rw [show (remainder N).sqrt^2=remainder N from hit]
  unfold remainder
  have h := Nat.sqrt_le' N
  omega

theorem negative {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (op : Odd p) (oq : Odd q) (hit : Passes (p*q)) : reading (p*q) = -2*Complex.I :=
  (negative_iff_two_squares pp qp ord op oq).mpr ⟨_,_,representation hit⟩

/-- The ordinary true Fermat midpoint occupies one residue modulo eight,
or one modulo sixteen when the public product has remainder five modulo eight. -/
theorem midpoint {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (op : Odd p) (oq : Odd q) (hit : Passes (p*q)) :
    (p+q)/2 ≡ (p*q+1)/2 [MOD 8] ∧
    ((p*q)%8=5 → (p+q)/2 ≡ (p*q+1)/2 [MOD 16]) := by
  have sign := negative pp qp ord op oq hit
  have eight := CyclotomicGaussianPrecision.negative_mod_sixteen pp qp ord op oq sign
  change (p+q)%16=(p*q+1)%16 at eight
  constructor
  · change ((p+q)/2)%8=((p*q+1)/2)%8
    omega
  · intro five
    have more := CyclotomicGaussianPrecision.negative_mod_thirtytwo pp qp ord op oq five sign
    change (p+q)%32=(p*q+1)%32 at more
    change ((p+q)/2)%16=((p*q+1)/2)%16
    omega

/-- The next square is at distance 2 floor(√N)+1, independently of whether
the test succeeds. -/
theorem coordinate_bound {N : ℕ} (high : N<2^2048) : (remainder N).sqrt < 2^513 := by
  have r : N.sqrt<2^1024 := Nat.sqrt_lt'.mpr (by
    simpa only [←pow_mul,show 1024*2=2048 by decide] using high)
  have gap := Nat.sqrt_le_add N
  have room : 2*(2^1024:ℕ)<(2^513)^2 := by decide +kernel
  have low := Nat.sqrt_le' N
  apply Nat.sqrt_lt'.mpr
  unfold remainder
  rw [←sq] at gap
  omega

/-- The fraction of all eligible pairs passing this single public square
test is strictly below 2⁻⁴⁸⁷. -/
theorem frequency : 2^487*(sample Passes).card<eligible.card := by
  let A := range (2^513)
  have sub : sample Passes ⊆ sample (HasCoordinate A) := by
    intro z hz
    obtain ⟨_,_,_,_,_,high,hit⟩ := PrimeFactors.SmallNormSquarePopulation.pair_data hz
    have form := representation hit
    simp only [sample,mem_filter,mem_ordered] at hz ⊢
    obtain ⟨⟨p,q,ne,wide,_⟩,ord⟩ := hz
    have entry : HasCoordinate A (z.1*z.2) :=
      ⟨_,mem_range.mpr (coordinate_bound high),_,form.trans (Nat.add_comm _ _)⟩
    exact ⟨⟨p,q,ne,wide,entry⟩,ord⟩
  have count := menu_count A (fun a ha => (mem_range.mp ha).le)
  have ac : A.card=2^513 := card_range _
  rw [ac] at count
  have scaled := Nat.mul_le_mul_left (21000000*2^487) ((card_le_card sub).trans count)
  have num : 21000000*2^487*((2:ℕ)^513*(75*2^1015))≤2^2046 := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using (scaled.trans num).trans_lt ChebyshevPrimeSample.eligible_count

/-- A true gate hit and an exact first ordinary Fermat hit. -/
theorem positive_control : 521*1009=525689 ∧ Nat.Prime 521 ∧ Nat.Prime 1009 ∧
    (525689:ℕ).sqrt=725 ∧ remainder 525689=64 ∧ Passes 525689 ∧
    765^2=525689+244^2 ∧ 765-726+1=40 ∧ (765-727)/2+1=20 ∧
    (765-729)/4+1=10 ∧ (765-733)/8+1=5 := by
  have r : (525689:ℕ).sqrt=725 := (Nat.eq_sqrt'.mpr (by decide)).symm
  have d : remainder 525689=64 := by rw [remainder,r]; decide
  refine ⟨by decide,by norm_num,by norm_num,r,d,?_,by decide,by decide,by decide,by decide,by decide⟩
  unfold Passes
  rw [d,show (64:ℕ).sqrt=8 from (Nat.eq_sqrt'.mpr (by decide)).symm]
  decide

/-- The available representation at 8249 does not use the floor square root. -/
theorem miss_control : 8249=32^2+85^2 ∧ (8249:ℕ).sqrt=90 ∧ remainder 8249=149 ∧
    ¬Passes 8249 := by
  have r : (8249:ℕ).sqrt=90 := (Nat.eq_sqrt'.mpr (by decide)).symm
  have d : remainder 8249=149 := by rw [remainder,r]; decide
  refine ⟨by decide,r,d,?_⟩
  unfold Passes
  rw [d,show (149:ℕ).sqrt=12 from (Nat.eq_sqrt'.mpr (by decide)).symm]
  decide

end PrimeFactors.GaussianSquareRemainder
