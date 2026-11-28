import PrimeFactors.CubicPlantedPrimality
import PrimeFactors.ComplementaryQuarticProducts
import PrimeFactors.QuarticFermatDistance
import PrimeFactors.Certificate
import Mathlib.Tactic.ReduceModChar

/-! A constructed 2,048-bit quartic product whose first ordinary Fermat hit
occurs more than 2^719 midpoints after the start. The same construction puts
both factors in a known residue class, giving a second one-candidate reading. -/
namespace PrimeFactors.FullWidthQuarticLaterMidpoint

set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

abbrev F : ℕ := 2^360
abbrev s : ℕ := 5*(2^149+48628)
abbrev x : ℕ := 1+F
abbrev y : ℕ := F*s
abbrev midpoint : ℕ := x^2+2*y^2
abbrev gap : ℕ := 2*x*y
abbrev p : ℕ := midpoint-gap
abbrev q : ℕ := midpoint+gap
abbrev N : ℕ := x^4+4*y^4

/-- A prime divisor must be one modulo F. A proper split would therefore
give two positive integers with the prescribed sum and product. -/
private theorem binary {n low high : ℕ} (z : ZMod n) (size : 1<n)
    (shape : n=1+F*(low+F*high)) (small : low<F) (height : high+1<F)
    (separate : high+1<low ∨ low^2<4*high) (half : z^(2^359) = -1)
    (cop : Nat.Coprime ((-1 - 1 : ZMod n).val) n) : n.Prime := by
  apply CubicPlantedPrimality.prime_of_order (F:=F) z size (by decide +kernel) shape small height
  · intro a b ap bp sum prod
    rcases separate with large | smallDisc
    · obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ap.ne'
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero bp.ne'
      nlinarith [Nat.zero_le (i*j)]
    · have h : 4*(a*b)≤(a+b)^2 := by nlinarith [two_mul_le_add_sq a b]
      rw [sum,prod] at h
      omega
  · simpa using (Covers.cons 360 Nat.prime_two covers_one)
  · rw [show F=2^359*2 by decide +kernel,pow_mul,half]
    ring
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    rw [show F/2=2^359 by decide +kernel,half]
    exact cop

/-- The binary-order witness is the projection of base 13. -/
theorem p_prime : Nat.Prime p := by
  let z : ZMod p := 33210822852495091089221767300879032249191995132999313744408189218086892382918750651744537151896354722993278813470024281846656522635670997893543261418262597210256937811873775113188780204835060322537685665403197703025077285527467357296741113300192648773226779830212652297595056594503829891283708078616797704245
  apply binary (low:=F+2-2*s) (high:=2*s^2-2*s) z
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · left
    decide +kernel
  · unfold z p midpoint gap x y s F
    reduce_mod_char
  · decide +kernel

/-- The binary-order witness is the projection of base 7. -/
theorem q_prime : Nat.Prime q := by
  let z : ZMod q := 117822344913071070522284192620071843732185058214944667021526473298228270820581089990160501715354990512963878044292575108100635068136286059414699469506334041921250684844024779885431501888558552081249337607454493684044048251342805011350878334101246624903691891454735503533331828211432341639029670905278074491014
  apply binary (low:=2+2*s) (high:=1+2*s^2+2*s) z
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · right
    decide +kernel
  · unfold z q midpoint gap x y s F
    reduce_mod_char
  · decide +kernel

theorem data : ExactFactorization N [p,q] ∧ 2^1023≤p ∧ p<q ∧ q<2^1024 ∧
    2^2047≤N ∧ N<2^2048 := by
  refine ⟨⟨by decide +kernel,?_⟩,by decide +kernel⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.elim (fun eq => eq ▸ p_prime) (fun eq => eq ▸ q_prime)

attribute [local irreducible] ComplementaryQuarticProducts.recognizeY ceilSqrt

/-- Reading the public fourth root of N/4 recovers both certified primes. -/
theorem quartic : ComplementaryQuarticProducts.recognizeY N=some (p,q) :=
  ComplementaryQuarticProducts.completeY (x:=x) (y:=y)
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel)

private theorem ceil_of_bounds {n a : ℕ} (hi : n≤a^2) (lo : (a-1)^2<n) :
    ceilSqrt n=a := by
  have top := ceilSqrt_le_iff.mpr hi
  have bottom : ¬ceilSqrt n≤a-1 := fun h => (not_le_of_gt lo) (ceilSqrt_le_iff.mp h)
  omega

abbrev start : ℕ := 140444776161118430291351968030392557313923591951728515931028010218673660334177894369437248448606679840096303516765302509680885855806294169394084716151414405930513084501861737575268808546958583816383303232919049257613130076951513777098547474502139045969015518960171783324942121734922213766519454043771160619146

theorem ceil_value : ceilSqrt N=start :=
  ceil_of_bounds (by decide +kernel) (by decide +kernel)

/-- Both ends of the stated distance interval are strict. -/
theorem distance : 2^719<midpoint-ceilSqrt N ∧ midpoint-ceilSqrt N<2^720 := by
  rw [ceil_value]
  decide +kernel

private theorem rank_at {a b c lo hi : ℕ}
    (hs : ceilSqrt (a^4+4*b^4)=c)
    (bracket : lo<a^2+2*b^2-c+1 ∧ a^2+2*b^2-c+1<hi) :
    lo<QuarticFermatDistance.rank a b ∧ QuarticFermatDistance.rank a b<hi := by
  simpa only [QuarticFermatDistance.rank,hs] using bracket

theorem inclusive_rank : 2^719<QuarticFermatDistance.rank x y ∧
    QuarticFermatDistance.rank x y<2^720 := by
  exact rank_at (a:=x) (b:=y) (c:=start) ceil_value (by decide +kernel)

/-- Every ordinary midpoint below the displayed midpoint fails its square test. -/
theorem no_earlier {m : ℕ} (from_start : ceilSqrt N≤m) (early : m<midpoint) :
    ¬IsSquare (m^2-N) := QuarticFermatDistance.first (x:=x) (y:=y) p_prime q_prime from_start early

theorem midpoint_hit : midpoint^2=N+gap^2 := QuarticFermatDistance.midpoint_hit x y

/-- The constructed factor classes also determine a stronger midpoint congruence. -/
theorem residues : p%(2*F)=1 ∧ q%(2*F)=1 ∧
    midpoint%(2*F^2)=((N+1)/2)%(2*F^2) := by decide +kernel

/-- The exponent of two dividing N−1 is 362. Within this construction,
the product thus identifies the exponent defining F. -/
theorem product_residue : (N-1)%(8*F)=4*F := by decide +kernel

/-- With the known family parameter F the first midpoint in the supplied
residue class already succeeds on this fixture. -/
theorem residue_first : ceilSqrt N + (((N+1)/2-ceilSqrt N)%(2*F^2))=midpoint := by
  rw [ceil_value]
  decide +kernel

end PrimeFactors.FullWidthQuarticLaterMidpoint
