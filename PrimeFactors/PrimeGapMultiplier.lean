import PrimeFactors.InteriorBatchPopulation
import Mathlib.Data.Complex.ExponentialBounds

/-! Center a one-sided prime gap estimate on the ratio 3/2. The analytic
input is Theorem 5 of Carneiro, Milinovich and Soundararajan, as a premise. -/
namespace PrimeFactors.PrimeGapMultiplier
open Real Finset InteriorBatchPopulation

set_option exponentiation.threshold 8192

/-- The published one-sided interval estimate under the Riemann hypothesis. -/
def PrimeInInterval : Prop := ∀ x : ℝ, 4 ≤ x →
  ∃ q : ℕ, q.Prime ∧ x ≤ q ∧ (q:ℝ) ≤ x+(22/25)*sqrt x*log x

/-- Center the interval before applying the gap estimate. This bounds the
excess of the weighted trace quadratically in the logarithm of the center. -/
theorem centered (gap : PrimeInInterval) {y : ℝ} (large : 16 ≤ y)
    (slow : 100*log y ≤ sqrt y) :
    ∃ q : ℕ, q.Prime ∧ |(q:ℝ)-y| ≤ (11/25)*sqrt y*log y ∧
      2*(sqrt q-sqrt y)^2 ≤ (8/81)*(log y)^2 := by
  let w := (11/25)*sqrt y*log y
  let x := y-w
  have yp : 0 < y := by linarith
  have lpos : 0 ≤ log y := log_nonneg (by linarith)
  have sy := sq_sqrt yp.le
  have wp : 0 ≤ w := by dsimp [w]; positivity
  have small : w ≤ y/100 := by
    dsimp [w]
    nlinarith only [sy,mul_le_mul_of_nonneg_left slow (sqrt_nonneg y),
      mul_nonneg (sqrt_nonneg y) lpos]
  have x4 : 4 ≤ x := by dsimp [x]; linarith
  have xy : x ≤ y := by dsimp [x]; linarith
  obtain ⟨q,pr,lower,upper⟩ := gap x x4
  have monotone := mul_le_mul (sqrt_le_sqrt xy) (log_le_log (by linarith) xy)
    (log_nonneg (by linarith : 1 ≤ x)) (sqrt_nonneg y)
  have close : |(q:ℝ)-y| ≤ w := by
    apply abs_le.mpr
    dsimp [x,w] at lower upper ⊢
    dsimp [x,w] at monotone
    constructor <;> linarith only [lower,upper,monotone]
  have qp : 0 ≤ (q:ℝ) := Nat.cast_nonneg q
  have rootlow : (99/100)*sqrt y ≤ sqrt q := by
    apply (le_sqrt (by positivity) qp).mpr
    dsimp [x] at lower
    nlinarith only [small,lower,sy,yp.le]
  have identity : |sqrt q-sqrt y| * (sqrt q+sqrt y) = |(q:ℝ)-y| := by
    rw [←abs_of_nonneg (add_nonneg (sqrt_nonneg (q:ℝ)) (sqrt_nonneg y)), ←abs_mul]
    congr 1
    nlinarith only [sq_sqrt qp,sy]
  have bound : |sqrt q-sqrt y| ≤ (2/9)*log y := by
    by_contra! bad
    have h := mul_lt_mul_of_pos_right bad (show 0 < sqrt (q:ℝ)+sqrt y by positivity)
    have k := mul_le_mul_of_nonneg_left rootlow lpos
    dsimp [w] at close
    nlinarith only [h,k,identity,close,mul_nonneg (sqrt_nonneg y) lpos]
  refine ⟨q,pr,close,?_⟩
  have h := pow_le_pow_left₀ (abs_nonneg _) bound 2
  rw [sq_abs] at h
  nlinarith only [h]

private theorem nat_radius {p q v : ℕ}
    (low : -(v:ℝ) ≤ (q:ℝ)-3*p/2) (high : (q:ℝ)-3*p/2 ≤ v) :
    3*p≤2*q+2*v ∧ 2*q≤3*p+2*v := by
  constructor
  · have h : 3*(p:ℝ) ≤ 2*(q:ℝ)+2*(v:ℝ) := by linarith
    exact_mod_cast h
  · have h : 2*(q:ℝ) ≤ 3*(p:ℝ)+2*(v:ℝ) := by linarith
    exact_mod_cast h

/-- Each smaller prime in the specified 1024-bit range has at least one
larger partner for which a product-only search in 8299 blocks of two labels
returns a prime factor. A block uses residues 1 and 5 modulo 6. -/
theorem partner (gap : PrimeInInterval) {p : ℕ} (hp : p ∈ interior) :
    ∃ q ∈ neighbors p, q.Prime ∧ p<q ∧ q<U ∧ bin p q ∧
      let n := p*q
      let f := ⌈2*sqrt (6*(n:ℝ))⌉₊
      ∃ j < 8299, ∃ a∈({1,5}:Finset ℕ),
        let S := 6*(f/6+j)+a
        let d := (S^2-24*n).sqrt
        f ≤ S ∧ S^2=24*n+d^2 ∧ (n.gcd ((S+d)/2)=p ∨ n.gcd ((S+d)/2)=q) := by
  have info := hp
  rw [InteriorBatchPopulation.interior,firstPrimes] at info
  obtain ⟨ir,pp⟩ := mem_filter.mp info
  obtain ⟨pl,pu⟩ := mem_Icc.mp ir
  have pbound : 2^1023≤p := le_trans (by decide +kernel) pl
  have upper : 3*p≤2*U := le_trans (Nat.mul_le_mul_left _ pu) (by decide +kernel)
  let y := 3*(p:ℝ)/2
  have yl : (2:ℝ)^1023≤y := by
    have h : (2:ℝ)^1023≤p := by exact_mod_cast pbound
    dsimp [y]; linarith only [h, show (0:ℝ) ≤ p by positivity]
  have yu : y≤(2:ℝ)^1024 := by
    have h : 3*(p:ℝ)≤2*(2:ℝ)^1024 := by exact_mod_cast upper
    dsimp [y]; linarith only [h]
  have yl16 : 16≤y := le_trans (by norm_num) yl
  have y0 : 0<y := by linarith
  have lg : log y ≤ 710 := by
    have l := log_le_log y0 yu
    rw [log_pow] at l
    norm_num only [Nat.cast_ofNat] at l
    linarith only [l,log_two_lt_d9]
  have l0 : 0 ≤ log y := log_nonneg (by linarith)
  have sy : sqrt y ≤ (2:ℝ)^512 := sqrt_le_iff.mpr ⟨by positivity,by convert yu using 1; norm_num⟩
  have ylroot : 71000 ≤ sqrt y := (le_sqrt (by norm_num) y0.le).mpr (le_trans (by norm_num) yl)
  obtain ⟨q,qp,close,height⟩ := centered gap yl16 (by linarith)
  have radius : (11/25)*sqrt y*log y ≤ V := by
    have h := mul_le_mul sy lg l0 (show (0:ℝ)≤2^512 by positivity)
    norm_num [V] at h ⊢
    linarith only [h]
  obtain ⟨neg,pos⟩ := abs_le.mp (close.trans radius)
  obtain ⟨left,right⟩ := nat_radius (p:=p) (q:=q) (v:=V) neg pos
  have hq : q ∈ neighbors p := by
    rw [neighbors]
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,qp⟩
  obtain ⟨bn,_,pq,qu,_,_⟩ := interior_split hp hq
  refine ⟨q,hq,qp,pq,qu,bn,?_⟩
  let S := 3*p+2*q
  let n := p*q
  let f := ⌈2*sqrt (6*(n:ℝ))⌉₊
  have root : sqrt (6*(n:ℝ)) = 2*sqrt y*sqrt (q:ℝ) := by
    apply (sq_eq_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt (by positivity),mul_pow,mul_pow,sq_sqrt (Nat.cast_nonneg q),sq_sqrt y0.le]
    dsimp [n,y]; push_cast; ring
  have delta : (S:ℝ)-2*sqrt (6*(n:ℝ))=2*(sqrt q-sqrt y)^2 := by
    rw [root]
    have sy2 := sq_sqrt y0.le
    dsimp [S,y] at sy2 ⊢
    push_cast
    nlinarith only [sq_sqrt (Nat.cast_nonneg q),sy2]
  have fl : f ≤ S := Nat.ceil_le.mpr (by linarith only [delta,sq_nonneg (sqrt q-sqrt y)])
  have top : S < f+49788 := by
    have h := pow_le_pow_left₀ l0 lg 2
    have hf : 2*sqrt (6*(n:ℝ))≤f := Nat.le_ceil _
    exact_mod_cast (show (S:ℝ)<(f:ℝ)+49788 by linarith only [height,h,hf,delta])
  have oddp := pp.odd_of_ne_two (by omega)
  obtain ⟨k,hk⟩ := oddp
  have qmod : ¬3∣q := fun d => ((Nat.dvd_prime qp).mp d).elim (by decide) (by omega)
  have rem : S%6=1 ∨ S%6=5 := by dsimp [S]; omega
  have express : 6*(f/6+(S/6-f/6))+S%6=S := by omega
  refine ⟨S/6-f/6,by omega,S%6,by simpa using rem,?_⟩
  change f ≤ 6*(f/6+(S/6-f/6))+S%6 ∧ _
  rw [express]
  have sq := multiplier_sum_square p q 3 2
  change S^2=24*n+(3*p).dist (2*q)^2 at sq
  have cop (l : ℕ) (pr : l.Prime) (large : 6<l) : Nat.Coprime 6 l :=
    (pr.coprime_iff_not_dvd.mpr (fun d => (not_le_of_gt large) (Nat.le_of_dvd (by decide) d))).symm
  have cn : Nat.Coprime 6 n := Nat.Coprime.mul_right (cop p pp (by omega)) (cop q qp (by omega))
  refine ⟨fl,?_,?_⟩
  · rw [sq,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  · exact WeightedTracePrefix.shared_gcd rfl (a:=3) (b:=2) (by decide) cn rfl

end PrimeFactors.PrimeGapMultiplier
