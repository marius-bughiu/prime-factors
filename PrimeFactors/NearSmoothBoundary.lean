import PrimeFactors.SmoothCenterSpacing
import PrimeFactors.ChebyshevQuarticScale
import PrimeFactors.Fermat

/-! Extending the finite smooth-sum dictionary to include centers outside
the half-open interval of possible sums. The only additional center at the
specified tolerance forces recovery at the first Fermat midpoint. -/

namespace PrimeFactors.NearSmoothBoundary

open SmoothSumSelector SmoothCenterSpacing

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem margins : ∀ b : Fin 647,
    fastCenter b + 2*2^1014 < 2^1025 ∧
    (fastCenter b = 2^1024 ∨ 2^1025+2^1014 < 2*fastCenter b) := by decide +kernel

/-- Every smooth center within the indicated tolerance of this half-open
octave occurs in the standard dictionary or is the right endpoint. -/
theorem dictionary {s c a b E : ℕ} (form : c=2^a*3^b)
    (lo : 2^1024≤s) (hi : s<2^1025) (cap : E≤2^1014)
    (nearLo : c≤s+E) (nearHi : s≤c+E) :
    b<647 ∧ (candidate b=c ∨ c=2^1025) := by
  have oddPart : 3^b≤c := by rw [form]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have hb : b<647 := by
    by_contra! h
    have h₁ := Nat.pow_le_pow_right (by decide : 0<3) h
    have h₂ : (2:ℕ)^1025+2^1014<3^647 := by decide +kernel
    omega
  have h := margins ⟨b,hb⟩
  change fastCenter b + 2*2^1014 < 2^1025 ∧
    (fastCenter b = 2^1024 ∨ 2^1025+2^1014 < 2*fastCenter b) at h
  rw [fast_correct hb] at h
  refine ⟨hb,?_⟩
  by_cases low : c<2^1024
  · have twice : 2*c=2^(a+1)*3^b := by rw [form,pow_succ']; ac_rfl
    have here := (contains (s:=2*c) (by omega) (by omega) twice).2
    omega
  by_cases high : c<2^1025
  · exact Or.inl (contains (by omega) high form).2
  by_cases edge : c=2^1025
  · exact Or.inr edge
  cases a with
  | zero =>
    simp only [pow_zero,one_mul] at form
    have small := Nat.pow_le_pow_right (by decide : 0<3) (by omega : b≤646)
    have bound : (3:ℕ)^646 < 2^1024 := by decide +kernel
    omega
  | succ a =>
    let d := 2^a*3^b
    have twice : c=2*d := by simpa only [d,pow_succ',Nat.mul_assoc] using form
    have here := (contains (s:=d) (by omega) (by omega) (a:=a) (b:=b) rfl).2
    rcases h.2 with first|afterFirst <;> omega

/-- One square test at the least integer midpoint whose square reaches n. -/
def firstPair (n : ℕ) : Option (ℕ × ℕ) :=
  let t := ceilSqrt n
  let delta := t^2-n
  let d := delta.sqrt
  if d^2=delta ∧ 1<t-d then some (t-d,t+d) else none

/-- A gap of at most 2^512 between odd factors of this size guarantees
that one Fermat test returns both factors. Primality is unnecessary. -/
theorem first_of_small_gap {p q : ℕ} (op : Odd p) (oq : Odd q) (lo : 2^1023≤p)
    (order : p≤q) (gap : q-p≤2^512) :
    firstPair (p*q)=some (p,q) ∧ fermatWindowMiss (p*q) 1=false := by
  let d := (q-p)/2
  have eq : q=p+2*d := by obtain ⟨i,hi⟩ := op; obtain ⟨j,hj⟩ := oq; dsimp [d]; omega
  let t := p+d
  have sq : t^2=p*q+d^2 := by dsimp [t]; rw [eq]; ring
  have small : d^2≤(2^511)^2 := Nat.pow_le_pow_left (by omega) 2
  have budget : (2^511:ℕ)^2<2^1023 := by decide +kernel
  have hp : p≤t := by dsimp [t]; omega
  have ht : 0<t := by omega
  have pred : t-1+1=t := by omega
  have squarePred := congrArg (fun z : ℕ => z^2) pred
  have prev : (t-1)^2 < p*q := by
    dsimp only at squarePred
    nlinarith only [squarePred, pred, sq, small.trans_lt budget, lo, hp]
  have high : ceilSqrt (p*q)≤t := ceilSqrt_le_iff.mpr (by omega)
  have midpoint : ceilSqrt (p*q)=t := by
    by_contra ne
    have le : ceilSqrt (p*q)≤t-1 := by omega
    exact (not_le_of_gt prev) (ceilSqrt_le_iff.mp le)
  have delta : t^2-p*q=d^2 := by omega
  have left : t-d=p := by dsimp [t]; omega
  have right : t+d=q := by dsimp [t]; omega
  have proper : 1<p := by omega
  constructor
  · simp only [firstPair,midpoint,delta,Nat.sqrt_eq',left,right,proper,and_self,if_true]
  · rw [fermatWindowMiss,show List.range 1=[0] from rfl]
    simp [midpoint,delta,Nat.sqrt_eq']

/-- Only the extra upper center is possible outside the 647 standard
centers, and identifying this case requires just one ordinary product-only
Fermat test. The two inequalities express absolute distance at most E. -/
theorem classify {p q c a b E : ℕ} (form : c=2^a*3^b) (op : Odd p) (oq : Odd q)
    (lo : 2^1023≤p) (order : p≤q) (hi : q<2^1024) (cap : E≤2^437)
    (nearLo : c≤p+q+E) (nearHi : p+q≤c+E) :
    b<647 ∧ (candidate b=c ∨ (c=2^1025 ∧ q-p≤E ∧ firstPair (p*q)=some (p,q) ∧
      fermatWindowMiss (p*q) 1=false)) := by
  obtain ⟨hb,h⟩ := dictionary form (by omega) (by omega) (by omega) nearLo nearHi
  refine ⟨hb,h.elim Or.inl fun edge => Or.inr ?_⟩
  have gap : q-p≤E := by omega
  exact ⟨edge,gap,first_of_small_gap op oq lo order (by omega)⟩

/-- Both factors must exceed the public lower limit B−E when their sum
is within E of twice their strict upper limit B. -/
theorem excludes_upper {p q B E n : ℕ} (prod : p*q=n) (order : p≤q) (hi : q<B)
    (check : n<(B-E)^2) : p+q+E<2*B := by
  by_contra! h
  have left : B-E≤p := by omega
  have small := Nat.mul_le_mul left (left.trans order)
  rw [←Nat.pow_two,prod] at small
  omega

/-- On the published fresh and crossed products even the extra upper
center at tolerance 2^437 is impossible, hence also at 2^400. The
products and the bit cap alone establish this. -/
theorem controls {p q E : ℕ}
    (prod : p*q=ChebyshevQuarticScale.fresh ∨ p*q=ChebyshevQuarticScale.crossed)
    (order : p≤q) (hi : q<2^1024) (cap : E≤2^437) : p+q+E<2^1025 := by
  have bound : p+q+2^437<2*(2^1024) := by
    rcases prod with eq|eq
    · exact excludes_upper eq order hi (by decide +kernel)
    · exact excludes_upper eq order hi (by decide +kernel)
  omega

end PrimeFactors.NearSmoothBoundary
