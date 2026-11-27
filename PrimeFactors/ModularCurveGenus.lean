import PrimeFactors.CyclotomicRadixLift
import PrimeFactors.DivisorSum

/-! # Reading a factor sum from the genus at level four times the product

For distinct odd primes, the classical genus formula at level `4*p*q` has index
`6*(p+1)*(q+1)`, twelve cusps and zero elliptic points of orders two and three.
`LevelFourData` is the resulting numerical premise; this file does not construct a
modular curve. The genus formula is in Csirik–Wetherell–Zieve, *On the genera of
X₀(N)*, §2. The square and triangular counting laws are separate explicit premises.
-/
namespace PrimeFactors.ModularCurveGenus

open CyclotomicRadixLift (weight stride)

/-- The equation `g=1+index/12−cusps/2` with the level-four semiprime data,
written over naturals without truncated divisions or subtractions. -/
def LevelFourData (p q g : ℕ) : Prop := 12*g+60=6*(p+1)*(q+1)

/-- The supplied genus determines both the factor sum and the divisor sum. -/
theorem readout {p q g : ℕ} (pp : p.Prime) (qp : q.Prime) (distinct : p≠q)
    (data : LevelFourData p q g) :
    2*g+9=p*q+(p+q) ∧ 2*g+10=ArithmeticFunction.sigma 1 (p*q) := by
  unfold LevelFourData at data
  rw [sigma_semiprime pp qp distinct]
  constructor <;> linarith

/-- The exact readout uses the project's integer square-root decoder. -/
theorem recover {p q g : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (data : LevelFourData p q g) : recoverFromSigma (p*q) (2*g+10) = (p,q) := by
  rw [(readout pp qp order.ne data).2]
  exact recoverFromSigma_correct pp qp order

/-- Ordered additive representations, weighted by the choices for one coordinate.
The caller uses terms with `j≤term j`, making `0..n` an inclusive bound. -/
noncomputable def representations (term choices : ℕ→ℕ) : ℕ→ℕ→ℕ
  | 0, n => if n=0 then 1 else 0
  | k+1, n => ∑ j ∈ Finset.range (n+1),
      if term j≤n then choices j*representations term choices k (n-term j) else 0

/-- Signed square representations distinguish both signs of a positive coordinate. -/
noncomputable def squares (n : ℕ) :=
  representations (fun j => j^2) (fun j => if j=0 then 1 else 2) 4 n

def triangle (j : ℕ) := j*(j+1)/2

/-- Four triangular summands correspond to four positive odd square coordinates,
with order preserved. This change of variables uses no representation theorem. -/
noncomputable def triangularEquiv (k : ℕ) :
    {x : Fin 4 → ℕ // ∑ i, triangle (x i)=k} ≃
      {v : Fin 4 → ℕ // (∀ i, Odd (v i)) ∧ ∑ i, (v i)^2=8*k+4} := by
  have term (j : ℕ) : (2*j+1)^2=8*triangle j+1 := by
    have half := Nat.div_mul_cancel j.even_mul_succ_self.two_dvd
    unfold triangle
    nlinarith only [half]
  have sum (x : Fin 4 → ℕ) : (∑ i, (2*x i+1)^2)=8*(∑ i, triangle (x i))+4 := by
    simp_rw [term]
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    simp
  have inv (j : ℕ) (odd : Odd j) : 2*(j/2)+1=j := by obtain ⟨z,h⟩ := odd; omega
  refine ⟨fun x => ⟨fun i => 2*x.val i+1, fun i => ⟨x.val i,rfl⟩, by rw [sum,x.property]⟩,
    fun v => ⟨fun i => v.val i/2, ?_⟩, ?_, ?_⟩
  · have e := sum (fun i => v.val i/2)
    simp only at e
    simp_rw [inv _ (v.property.1 _)] at e
    rw [v.property.2] at e
    change (∑ i, triangle (v.val i/2))=k
    omega
  · intro x
    apply Subtype.ext
    funext i
    change (2*x.val i+1)/2=x.val i
    omega
  · intro v
    apply Subtype.ext
    funext i
    exact inv _ (v.property.1 i)

/-- Ordered triangular representations include zero, with nonnegative coordinates. -/
noncomputable def triangles (k : ℕ) :=
  representations triangle (fun _ => 1) 4 k

/-- Jacobi's four-square identity at odd N and the four-triangular-number identity
at `(N−1)/2` give the same divisor sum. The two counting theorems are hypotheses. -/
theorem representation_readouts {p q g : ℕ} (pp : p.Prime) (qp : q.Prime) (distinct : p≠q)
    (data : LevelFourData p q g)
    (jacobi : squares (p*q)=8*ArithmeticFunction.sigma 1 (p*q))
    (triangular : triangles ((p*q-1)/2)=ArithmeticFunction.sigma 1 (p*q)) :
    squares (p*q)=16*g+80 ∧ triangles ((p*q-1)/2)=2*g+10 := by
  have sum := (readout pp qp distinct data).2
  omega

/-- The public residue of the genus. The modulus is 2, 4, 6 or 12. -/
theorem residue {p q g : ℕ} (po : Odd p) (qo : Odd q) (data : LevelFourData p q g) :
    (g:ℤ) ≡ (p*q:ℕ)-4 [ZMOD (weight (p*q):ℤ)] := by
  obtain ⟨t,eq⟩ := CyclotomicRadixLift.divides po qo
  have positiveP := po.pos
  have positiveQ := qo.pos
  have product : (p-1)*(q-1)+p+q=p*q+1 := by
    rcases Nat.exists_eq_succ_of_ne_zero positiveP.ne' with ⟨x,rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero positiveQ.ne' with ⟨y,rfl⟩
    simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one]
    ring
  have mass : weight (p*q)*t+4+g=p*q := by
    unfold stride at eq
    unfold LevelFourData at data
    nlinarith only [eq,product,data]
  apply Int.modEq_iff_dvd.mpr
  refine ⟨t,?_⟩
  have cast := congrArg (fun n : ℕ => (n:ℤ)) mass
  push_cast at cast ⊢
  linarith

/-- The last genus in the public congruence class at or below the supplied
integer endpoint. Negative endpoints use Euclidean remainders. -/
def atOrBelow (n : ℕ) (upper : ℤ) : ℤ := upper-(upper-((n:ℤ)-4))%(weight n:ℤ)

theorem interval {n g : ℕ} {upper : ℤ} (congruent : (g:ℤ) ≡ (n:ℤ)-4 [ZMOD (weight n:ℤ)])
    (contains : (g:ℤ)≤upper) (short : upper<(g:ℤ)+(weight n:ℤ)) : atOrBelow n upper=g := by
  have same := (Int.ModEq.refl upper).sub congruent
  change (upper-(g:ℤ))%(weight n:ℤ)=(upper-((n:ℤ)-4))%(weight n:ℤ) at same
  rw [Int.emod_eq_of_lt (by omega) (by omega)] at same
  unfold atOrBelow
  omega

/-- A wider interval still gives an explicit list. The number of positions to test is at most
one plus the width divided by the public genus spacing, rounded down. -/
theorem window {n g : ℕ} {lower upper : ℤ}
    (congruent : (g:ℤ) ≡ (n:ℤ)-4 [ZMOD (weight n:ℤ)]) (lo : lower≤g) (hi : (g:ℤ)≤upper) :
    ∃ j : ℤ, 0≤j ∧ j≤(upper-lower)/(weight n:ℤ) ∧ atOrBelow n upper=g+j*(weight n:ℤ) := by
  let w : ℤ := weight n
  have wp : 0<w := by
    dsimp [w]
    rcases CyclotomicRadixLift.weights n with h|h|h|h <;> omega
  refine ⟨(upper-(g:ℤ))/w, Int.ediv_nonneg (by omega) wp.le,
    Int.ediv_le_ediv wp (by omega), ?_⟩
  have same := (Int.ModEq.refl upper).sub congruent
  change (upper-(g:ℤ))%w=(upper-((n:ℤ)-4))%w at same
  change upper-(upper-((n:ℤ)-4))%w=g+(upper-(g:ℤ))/w*w
  rw [←same,Int.mul_comm _ w]
  linarith only [Int.emod_add_ediv (upper-(g:ℤ)) w]

/-- Rounding a real observation inside the strict half-spacing radius needs only
one floor and one integer remainder. -/
noncomputable def nearest (n : ℕ) (observed : ℝ) : ℤ :=
  atOrBelow n ⌊observed+(weight n:ℝ)/2⌋

theorem approximate {p q g : ℕ} (po : Odd p) (qo : Odd q) (data : LevelFourData p q g)
    {observed : ℝ} (precision : 2*|observed-g|<(weight (p*q):ℝ)) : nearest (p*q) observed=g := by
  let n := p*q
  change 2*|observed-g|<(weight n:ℝ) at precision
  have bot := neg_abs_le (observed-(g:ℝ))
  have top := le_abs_self (observed-(g:ℝ))
  apply interval (residue po qo data)
  · apply Int.le_floor.mpr
    push_cast
    linarith
  · apply Int.floor_lt.mpr
    push_cast
    linarith

/-- Two consecutive integers in the public genus class are equally far from
their midpoint. This shows the limit of rounding from the congruence alone. -/
theorem endpoint_tie (n : ℕ) (z : ℤ) (hz : z ≡ (n:ℤ)-4 [ZMOD (weight n:ℤ)]) :
    let w := weight n
    let mid : ℝ := z+(w:ℝ)/2
    z≠z+(w:ℤ) ∧ z+(w:ℤ) ≡ (n:ℤ)-4 [ZMOD (w:ℤ)] ∧
      2*|mid-z|=(w:ℝ) ∧ 2*|mid-(z+(w:ℤ):ℤ)|=(w:ℝ) := by
  dsimp only
  have pos : 0<weight n := by rcases CyclotomicRadixLift.weights n with h|h|h|h <;> omega
  have congruent : z+(weight n:ℤ) ≡ z [ZMOD (weight n:ℤ)] := by
    change (z+(weight n:ℤ))%(weight n:ℤ)=z%(weight n:ℤ)
    simp
  refine ⟨by omega,congruent.trans hz,?_,?_⟩
  · rw [abs_of_nonneg (by linarith [show (0:ℝ)≤weight n by positivity] :
      0≤(z:ℝ)+(weight n:ℝ)/2-(z:ℝ))]
    ring
  · push_cast
    rw [abs_of_nonpos (by linarith [show (0:ℝ)≤weight n by positivity] :
      (z:ℝ)+(weight n:ℝ)/2-((z:ℝ)+(weight n:ℝ))≤0)]
    ring

/-- For a 2048-bit product even the largest half-spacing is less than the genus
scaled by `2⁻²⁰⁴³`. This prices the relative error of this rounding rule. -/
theorem full_size {p q g : ℕ} (large : 2^2047≤p*q) (factors : 9≤p+q)
    (data : LevelFourData p q g) : 2^2043*weight (p*q)<2*g := by
  have w : weight (p*q)≤12 := by rcases CyclotomicRadixLift.weights (p*q) with h|h|h|h <;> omega
  have mass : p*q≤2*g := by unfold LevelFourData at data; nlinarith only [data,factors]
  exact (Nat.mul_le_mul_left _ w).trans_lt ((by decide +kernel : (2:ℕ)^2043*12<2^2047).trans_le (large.trans mass))

/-- Independent bounded counts on 15. -/
example : squares 15=192 ∧ triangles 7=24 ∧ LevelFourData 3 5 7 := by
  unfold LevelFourData
  decide +kernel

/-- On level 2108 the supplied genus 283 gives the pair. Even a reading of 288 rounds
to 283: the upper endpoint after the half-spacing adjustment is 294. -/
example : weight 527=12 ∧ atOrBelow 527 294=283 ∧ recoverFromSigma 527 (2*283+10)=(17,31) := by
  decide +kernel

end PrimeFactors.ModularCurveGenus
