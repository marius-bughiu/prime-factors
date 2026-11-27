import PrimeFactors.ResidueCount
import PrimeFactors.CyclotomicDigitPeriod
import PrimeFactors.CyclotomicRadixLift
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Counts of locally admissible sums on one specified progression. The two
published analytic inputs below are hypotheses, not library axioms. -/
namespace PrimeFactors.ShortDiscriminantWindow
set_option exponentiation.threshold 4096
open Finset
variable {p : ℕ} [Fact p.Prime]

/-- Weil's prime-modulus complete Kloosterman bound, with unnormalized sums
and the standard additive character. See <https://doi.org/10.1073/pnas.34.5.204>. -/
def Weil (p : ℕ) [Fact p.Prime] : Prop := ∀ (u v : ZMod p), u≠0 → v≠0 →
    ‖∑ x ∈ univ.erase (0:ZMod p), ZMod.stdAddChar (u*x+v/x)‖ ≤ 2*Real.sqrt p

/-- Theorem 1.1 of Fouvry, Kowalski, Michel, Raju, Rivat and Soundararajan.
The frequency sums below omit the normalizing factor 1/√p, which is included
in their upper bound. The interval can start at any point of the residue ring.
See <https://arxiv.org/html/1508.00512#S1.Thm1>. -/
def ShortSums (p : ℕ) [Fact p.Prime] : Prop := ∀ (f : ZMod p → ℂ) (c : ℝ),
    (∀ z, ‖f z‖≤c) → (∀ k : ZMod p, ‖∑ z : ZMod p, ZMod.stdAddChar (z*k)*f z‖≤c*Real.sqrt p) →
    ∀ (a : ZMod p) (L : ℕ), Real.sqrt p<L → L≤p →
      ‖∑ j ∈ range L, f (a+j)‖ ≤ c*Real.sqrt p*Real.log (4*Real.exp 8*L/Real.sqrt p)

/-- A weighted version of the two-preimage count, with branch points retained. -/
theorem trace_sum (n : ZMod p) (nz : n≠0) (φ : ZMod p → ℂ) :
    2*(∑ s ∈ factorSumResidues p n, φ s) =
      (∑ x ∈ univ.erase (0:ZMod p), φ (x+n/x)) +
      ∑ x ∈ squareRootsMod p n, φ (x+n/x) := by
  classical
  let D : Finset (ZMod p) := univ.erase 0
  let f (x : ZMod p) := x+n/x
  let R := squareRootsMod p n
  let A := factorSumResidues p n
  have maps : Set.MapsTo f D A := fun x hx => mem_image_of_mem _ hx
  have mapsR : Set.MapsTo f R A := fun x hx => maps (mem_filter.mp hx).1
  change 2*(∑ s ∈ A, φ s) = (∑ x ∈ D, φ (f x)) + ∑ x ∈ R, φ (f x)
  rw [mul_sum, ←sum_fiberwise_of_maps_to' maps φ, ←sum_fiberwise_of_maps_to' mapsR φ,
    ←sum_add_distrib]
  apply sum_congr rfl
  intro s hs
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hs
  have xp := (mem_erase.mp hx).1
  let y := n/x
  have yp : y≠0 := div_ne_zero nz xp
  have prod : x*y=n := mul_div_cancel₀ n xp
  have fiber : D.filter (fun z => f z=f x) = {x,y} := factorSum_fiber p nz xp
  have rf : R.filter (fun z => f z=f x) = ({x,y}:Finset _).filter (fun z => z^2=n) := by
    rw [←fiber]
    ext i
    simp [R,squareRootsMod,D,and_left_comm,and_comm]
  change 2*φ (f x) = (∑ _i ∈ D.filter (fun z => f z=f x), φ (f x)) +
    ∑ _i ∈ R.filter (fun z => f z=f x), φ (f x)
  simp only [fiber,rf,sum_const,nsmul_eq_mul]
  have sx : x^2=n ↔ x=y := by rw [←prod,pow_two,mul_right_inj' xp]
  have sy : y^2=n ↔ x=y := by rw [←prod,pow_two,mul_left_inj' yp,eq_comm]
  by_cases eq : x=y
  · simp [←eq,sx.mpr eq,filter_singleton,two_mul]
  · simp [filter_insert,filter_singleton,eq,sx,sy,card_pair eq]

private noncomputable def sign (n s : ZMod p) : ℂ :=
  if s∈factorSumResidues p n then 1 else -1

private theorem roots_le (odd : p≠2) (n : ZMod p) (nz : n≠0) : (squareRootsMod p n).card≤2 := by
  by_cases sq : IsSquare n
  · exact (card_squareRootsMod_of_square p odd n nz sq).le
  · rw [card_squareRootsMod_of_nonsquare p n sq]; decide

private theorem signed_sum (n : ZMod p) (φ : ZMod p → ℂ) :
    ∑ s : ZMod p, φ s * sign n s =
      2*(∑ s ∈ factorSumResidues p n, φ s) - ∑ s : ZMod p, φ s := by
  classical
  have term (s : ZMod p) : φ s * sign n s =
      2*(if s∈factorSumResidues p n then φ s else 0)-φ s := by
    unfold sign
    split_ifs <;> ring
  simp only [term,sum_sub_distrib,←mul_sum]
  rw [←sum_filter]
  simp

private theorem coefficients (w : Weil p) (odd : p≠2) (n : ZMod p) (nz : n≠0) (k : ZMod p) :
    ‖∑ s : ZMod p, ZMod.stdAddChar (s*k)*sign n s‖≤2*Real.sqrt p+2 := by
  classical
  let φ (s : ZMod p) := ZMod.stdAddChar (s*k)
  rw [signed_sum n φ,trace_sum n nz φ]
  have roots : ‖∑ x∈squareRootsMod p n, φ (x+n/x)‖≤2 := by
    calc
      _ ≤ ∑ x∈squareRootsMod p n, ‖φ (x+n/x)‖ := norm_sum_le ..
      _ = ((squareRootsMod p n).card:ℝ) := by simp [φ,ZMod.stdAddChar_apply]
      _ ≤ _ := by exact_mod_cast roots_le odd n nz
  by_cases kz : k=0
  · subst k
    simp only [φ,mul_zero,AddChar.map_zero_eq_one,sum_const,nsmul_eq_mul,mul_one,
      card_erase_of_mem (mem_univ (0:ZMod p)),card_univ,ZMod.card]
    have pp : 1≤p := (Fact.out : p.Prime).one_le
    have rr := roots_le odd n nz
    rw [Nat.cast_sub pp,Nat.cast_one]
    have r : ((p:ℂ)-1+(squareRootsMod p n).card-p) = ((squareRootsMod p n).card:ℂ)-1 := by ring
    rw [r,←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs]
    have br : (squareRootsMod p n).card≤(2:ℝ) := by exact_mod_cast rr
    have nn : (0:ℝ)≤(squareRootsMod p n).card := by positivity
    exact (abs_le.mpr ⟨by linarith,by linarith⟩ : |((squareRootsMod p n).card:ℝ)-1|≤1).trans
      (by linarith [Real.sqrt_nonneg (p:ℝ)])
  · have vanish : ∑ s : ZMod p, φ s = 0 := by
      dsimp [φ]
      rw [AddChar.sum_mulShift k (ZMod.isPrimitive_stdAddChar p)]
      simp [kz]
    rw [vanish,sub_zero]
    apply (norm_add_le ..).trans
    apply add_le_add _ roots
    have term (x : ZMod p) : (x+n/x)*k=k*x+(k*n)/x := by
      simp only [div_eq_mul_inv]
      ring
    simpa only [φ,term] using w k (k*n) kz (mul_ne_zero kz nz)

/-- Count of positions at which two residues with product n have the indicated sum. -/
noncomputable def count (n a b : ZMod p) (L : ℕ) : ℕ :=
  ((range L).filter fun j : ℕ => a+b*(j:ZMod p)∈factorSumResidues p n).card

private theorem interval (n a b : ZMod p) (L : ℕ) :
    ∑ j∈range L, sign n (a+b*(j:ZMod p)) = (2:ℂ)*(count n a b L)-(L:ℂ) := by
  classical
  have one (j : ℕ) : sign n (a+b*(j:ZMod p)) =
      2*(if a+b*(j:ZMod p)∈factorSumResidues p n then (1:ℂ) else 0)-1 := by
    unfold sign
    split_ifs <;> norm_num
  simp only [one,sum_sub_distrib,←mul_sum,←sum_filter,sum_const,card_range,
    nsmul_eq_mul,mul_one,count]

/-- Uniform two-sided count on an actual affine progression, including zero
discriminants. A passing position means precisely an admissible local factor
sum by mem_factorSumResidues_iff. -/
theorem progression (w : Weil p) (short : ShortSums p) (odd : p≠2) (n a b : ZMod p)
    (nz : n≠0) (unit : b≠0) (L : ℕ) (start : Real.sqrt p<L) (finish : L≤p) :
    |2*(count n a b L:ℝ)-L| ≤ (2*Real.sqrt p+2)*Real.log (4*Real.exp 8*L/Real.sqrt p) := by
  let g (z : ZMod p) := sign n (b*z)
  let u := Units.mk0 b unit
  have root : 0<Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  let c : ℝ := 2+2/Real.sqrt p
  have scale : c*Real.sqrt p=2*Real.sqrt p+2 := by dsimp [c]; field_simp
  have point (z : ZMod p) : ‖g z‖≤c := by
    have eq : ‖g z‖=1 := by simp only [g,sign]; split_ifs <;> simp
    rw [eq]
    dsimp [c]
    linarith [div_nonneg (by norm_num : (0:ℝ)≤2) root.le]
  have freq (k : ZMod p) : ‖∑ z : ZMod p, ZMod.stdAddChar (z*k)*g z‖≤c*Real.sqrt p := by
    rw [scale]
    have reindex : ∑ z : ZMod p, ZMod.stdAddChar (z*k)*g z =
        ∑ z : ZMod p, ZMod.stdAddChar (z*(b⁻¹*k))*sign n z := by
      apply Fintype.sum_equiv u.mulLeft
      intro z
      have eq : (b*z)*(b⁻¹*k)=z*k := by field_simp; ring
      change _ = ZMod.stdAddChar ((b*z)*(b⁻¹*k))*sign n (b*z)
      rw [eq]
    rw [reindex]
    exact coefficients w odd n nz _
  have est := short g c point freq (a/b) L start finish
  have line (j : ℕ) : g (a/b+j)=sign n (a+b*j) := by
    dsimp [g]; rw [mul_add,mul_div_cancel₀ _ unit]
  simp only [line,scale,interval] at est
  have cast : (2:ℂ)*(count n a b L)-(L:ℂ)=((2*(count n a b L:ℝ)-L:ℝ):ℂ) := by push_cast; rfl
  rw [cast,Complex.norm_real,Real.norm_eq_abs] at est
  exact est

/-- At a 1024-bit sieve prime, every lane of 2^521 positions passing the
width hypotheses has between 7/16 and 9/16 of its positions locally admissible.
The estimate applies uniformly in n, start and invertible step. -/
theorem width1024 (w : Weil p) (short : ShortSums p) (lo : 2^1023≤p) (hi : p<2^1024)
    (n a b : ZMod p) (nz : n≠0) (unit : b≠0) :
    7*2^521 ≤ 16*count n a b (2^521) ∧ 16*count n a b (2^521) ≤ 9*2^521 := by
  have posl : 0<Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  have low : (2:ℝ)^511 ≤ Real.sqrt p := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (show (2^511)^2 ≤ p from (by decide +kernel : (2^511)^2≤2^1023).trans lo)
  have high : Real.sqrt p ≤ (2:ℝ)^512 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    exact_mod_cast (show p ≤ (2^512)^2 from hi.le.trans (by decide +kernel : 2^1024 ≤ (2^512)^2))
  have Lp : 2^521≤p := (by decide +kernel : 2^521≤2^1023).trans lo
  have start : Real.sqrt p < ((2^521:ℕ):ℝ) := by
    apply high.trans_lt
    norm_num
  have odd : p≠2 := by rintro rfl; norm_num at lo
  have h := progression w short odd n a b nz unit (2^521) start Lp
  simp only [Nat.cast_pow,Nat.cast_ofNat] at h
  have arg : 4*Real.exp 8*(2:ℝ)^521/Real.sqrt p ≤ Real.exp 8*2^12 := by
    apply (div_le_iff₀ posl).mpr
    calc
      _ = Real.exp 8*2^12*2^511 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left low (by positivity)
  have logb : Real.log (4*Real.exp 8*(2:ℝ)^521/Real.sqrt p) ≤ 20 := by
    have bound := Real.log_le_log (by positivity) arg
    rw [Real.log_mul (Real.exp_ne_zero _) (by positivity),Real.log_exp,Real.log_pow] at bound
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have size : 2*Real.sqrt p+2 ≤ 3*(2:ℝ)^512 := by
    linarith [show (2:ℝ)≤2^512 by norm_num]
  have err := h.trans ((mul_le_mul_of_nonneg_left logb (by positivity)).trans
    (mul_le_mul_of_nonneg_right size (by norm_num : (0:ℝ)≤20)))
  obtain ⟨left,right⟩ := abs_le.mp err
  constructor
  · have cl : (7:ℝ)*2^521 ≤ 16*(count n a b (2^521):ℝ) := by linarith
    exact_mod_cast cl
  · have cu : 16*(count n a b (2^521):ℝ) ≤ (9:ℝ)*2^521 := by linarith
    exact_mod_cast cu

open GroupedNormExamples

/-- The first sum in the public W=12 class on the published separated input. -/
def sampleStart : ℕ := 287034011279285791907950584662114789010292222711979613908259944036028247013666088595681992599742501361847056829677468886496212179698799978296685117987456603296967449288422491187189241820471687907727346854275608679273562931301322488913236103839819581082428507125847153103599137713468205260758446146359140548622

/-- The chosen lane starts at the first admissible-width sum in its stride
and all 2^521 sites fit both independent odd-factor endpoint bounds. -/
theorem sample_window :
    CyclotomicRadixLift.stride separatedN=12 ∧
    sampleStart%12=(separatedN+1)%12 ∧ (sampleStart-12)^2<4*separatedN ∧
    4*separatedN≤sampleStart^2 ∧
    (sampleStart+12*(2^521-1))*(2^1023+1)≤(2^1023+1)^2+separatedN ∧
    (sampleStart+12*(2^521-1))*(2^1024-1)≤(2^1024-1)^2+separatedN := by decide +kernel

local instance : Fact adjacentSmall.Prime := ⟨CyclotomicDigitPeriod.grouped_examples.1.2.1⟩

/-- Neither prime factor of the separated input enters the lane or the test.
The independently certified sieve prime is taken from the adjacent input. -/
theorem sample_count (w : Weil adjacentSmall) (short : ShortSums adjacentSmall) :
    let survivors := @count adjacentSmall _ separatedN sampleStart 12 (2^521)
    7*2^521≤16*survivors ∧ 16*survivors≤9*2^521 :=
  width1024 w short (by decide +kernel) (by decide +kernel) _ _ _
    (by decide +kernel) (by decide +kernel)

end PrimeFactors.ShortDiscriminantWindow
