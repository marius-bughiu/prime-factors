import PrimeFactors.FareyParentNecessary
import PrimeFactors.SmoothConvergentPopulation

/-! A hit beyond the initial reciprocal guesses on the upper intermediate
fractions forces a common divisor larger than the unknown prime sum minus one. -/
namespace PrimeFactors.IntermediateTotientObstruction
open UpperConvergentDeficit

/-- The t-th positive step inside the i-th Euclidean quotient block.
The endpoint is the ordinary convergent. An invalid index produces no row. -/
def rowAt : ℕ → ℕ → ℕ → ℕ → Row → Row → Option Row
  | _, _, _, 0, _, _ => none
  | 0, t, u, v+1, x, y =>
    if 0<t ∧ t≤u/(v+1) then some (step x y t) else none
  | i+1, t, u, v+1, x, y =>
    rowAt i t (v+1) (u%(v+1)) y (step x y (u/(v+1)))

/-- An actual output of the intermediate scan agrees with E/F. -/
def Hit (N E F : ℕ) : Prop := ∃ i t z,
  rowAt i t E N ⟨0,1⟩ ⟨1,0⟩ = some z ∧ 0<z.b ∧ E*z.b=z.a*F

private theorem parent {i t u v E N : ℕ} {x y z : Row}
    (adj : FareyParentNecessary.Adjacent N E u v x y)
    (found : rowAt i t u v x y = some z) (above : E*z.b<N*z.a) :
    ∃ c d w : ℕ, 0<w ∧ z.a*d=z.b*c+1 ∧ E*d=N*c+w := by
  induction i generalizing u v x y with
  | zero =>
    cases v with
    | zero => simp [rowAt] at found
    | succ v =>
      simp only [rowAt] at found
      split at found
      next h =>
        have eq := Option.some.inj found
        subst z
        rcases adj with ⟨lo,hi,det⟩ | ⟨hi,lo,det⟩
        · have bound := (Nat.le_div_iff_mul_le (Nat.succ_pos v)).mp h.2
          dsimp [step] at above
          nlinarith only [lo,congrArg (fun m : ℕ => t*m) hi,bound,above]
        · refine ⟨y.a,y.b,v+1,Nat.succ_pos v,?_,lo⟩
          dsimp [step]
          nlinarith only [det]
      next => contradiction
  | succ i ih =>
    cases v with
    | zero => simp [rowAt] at found
    | succ v => exact ih (FareyParentNecessary.advance adj) found

/-- The positive lower-parent remainder w and its numerator c determine
the common divisor exactly. The reduction also covers the initial parent 0/1. -/
theorem common_divisor {a b c d E F D w : ℕ}
    (det : a*d=b*c+1) (ratio : E*b=a*F) (low : E*d=(F+D)*c+w) :
    E=a*(w+c*D) ∧ F=b*(w+c*D) ∧ E.gcd F=w+c*D := by
  have e : E=a*(w+c*D) := by
    nlinarith only [congrArg (fun n : ℕ => E*n) det,
      congrArg (fun n : ℕ => c*n) ratio,congrArg (fun n : ℕ => a*n) low]
  have f : F=b*(w+c*D) := by
    nlinarith only [congrArg (fun n : ℕ => F*n) det,
      congrArg (fun n : ℕ => d*n) ratio,congrArg (fun n : ℕ => b*n) low]
  have cop := Nat.coprime_of_mul_modEq_one d (FareyParentNecessary.parent_mod det)
  refine ⟨e,f,?_⟩
  rw [e,f,Nat.gcd_mul_right,cop.gcd_eq_one]
  simp

/-- Every hit either tests a multiple of E directly or its hidden common
divisor exceeds the deficit. The claim includes every positive intermediate step. -/
theorem dichotomy {N E F : ℕ} (ep : 0<E) (fn : F<N) (hit : Hit N E F) :
    E ∣ F ∨ N-F<E.gcd F := by
  obtain ⟨i,t,z,row,bp,ratio⟩ := hit
  have ap : 0<z.a := by
    have h := Nat.mul_pos ep bp
    rw [ratio] at h
    exact Nat.pos_of_mul_pos_right h
  have above : E*z.b<N*z.a := by rw [ratio,Nat.mul_comm N]; exact Nat.mul_lt_mul_of_pos_left fn ap
  obtain ⟨c,d,w,wp,det,low⟩ := parent (Or.inl (by simp)) row above
  have low' : E*d=(F+(N-F))*c+w := by rwa [Nat.add_sub_of_le fn.le]
  obtain ⟨e,f,g⟩ := common_divisor det ratio low'
  by_cases cz : c=0
  · left
    rw [cz,Nat.mul_zero,Nat.zero_add] at det
    have ao : z.a=1 := Nat.dvd_one.mp ⟨d,det.symm⟩
    simp only [cz,zero_mul,add_zero,ao,one_mul] at e f
    exact ⟨z.b,by rw [e,f,Nat.mul_comm]⟩
  · right
    have h := Nat.le_mul_of_pos_left (N-F) (Nat.pos_of_ne_zero cz)
    omega

/-- Every multiple F=E*b strictly below N occurs in the initial block as 1/b. -/
theorem reciprocal {N E F : ℕ} (ep : 0<E) (fp : 0<F) (fn : F<N) (dvd : E ∣ F) : Hit N E F := by
  obtain ⟨b,fb⟩ := dvd
  have en := (Nat.le_of_dvd fp (show E ∣ F from ⟨b,fb⟩)).trans_lt fn
  have bp : 0<b := by by_contra! h; simp [Nat.eq_zero_of_le_zero h,fb] at fp
  have fits : b≤N/E := (Nat.le_div_iff_mul_le ep).mpr (by simpa [fb,Nat.mul_comm] using fn.le)
  refine ⟨1,b,⟨1,b⟩,?_,bp,by simp [fb]⟩
  cases E with
  | zero => contradiction
  | succ e =>
    cases N with
    | zero => omega
    | succ n =>
      simp [rowAt,step,Nat.div_eq_of_lt en,Nat.mod_eq_of_lt en,bp,fits]

/-- For exponents no larger than the deficit this characterizes every success. -/
theorem small_iff {N E F : ℕ} (ep : 0<E) (fp : 0<F) (fn : F<N) (small : E≤N-F) :
    Hit N E F ↔ E ∣ F := by
  refine ⟨fun h => (dichotomy ep fn h).resolve_right ?_,reciprocal ep fp fn⟩
  exact Nat.not_lt_of_ge ((Nat.gcd_le_left F ep).trans small)

open Finset MixedPrefixSample

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible sample ordered primes SmoothTotientTail.exceptional

private theorem gap {z : ℕ × ℕ} (he : z ∈ eligible) :
    let F := (z.1-1)*(z.2-1)
    0<F ∧ F<z.1*z.2 ∧ 2^1024 ≤ z.1*z.2-F := by
  rw [eligible,sample,mem_filter] at he
  obtain ⟨ord,pq⟩ := he
  obtain ⟨pm,qm,_,_,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp ord
  rw [primes,mem_filter] at pm qm
  have pl := (mem_Ico.mp pm.1).1
  have ql := (mem_Ico.mp qm.1).1
  change 2^1023 ≤ z.1 at pl
  change 2^1023 ≤ z.2 at ql
  have sum := PowerImageWidth.offset (show 0<z.1 by omega) (show 0<z.2 by omega)
  dsimp only
  exact ⟨Nat.mul_pos (by omega) (by omega),by omega,by omega⟩

/-- Outside the counted exceptional set the entire smooth intermediate scan
is equivalent to checking multiples of E, for *every* smooth exponent at once. -/
theorem ordinary_multiples {z : ℕ × ℕ} (he : z∈eligible)
    (outside : z∉SmoothTotientTail.exceptional 1501 (2^1024))
    {E : ℕ} (smooth : E∈Nat.smoothNumbers 1501) :
    Hit (z.1*z.2) E ((z.1-1)*(z.2-1)) ↔ E ∣ (z.1-1)*(z.2-1) := by
  obtain ⟨fp,fn,band⟩ := gap he
  have ep := Nat.pos_of_ne_zero smooth.1
  refine ⟨fun h => (dichotomy ep fn h).resolve_right ?_,reciprocal ep fp fn⟩
  exact fun big => outside (SmoothTotientTail.of_gcd he smooth (band.trans big.le))

/-- Count all products where smooth intermediate guesses can improve on
checking multiples, or where some smooth exponent at least 2^1024 hits at all. -/
noncomputable def exceptionalWins : Finset (ℕ × ℕ) := by
  classical
  exact eligible.filter fun z => ∃ E ∈ Nat.smoothNumbers 1501,
    Hit (z.1*z.2) E ((z.1-1)*(z.2-1)) ∧
      (¬ E ∣ (z.1-1)*(z.2-1) ∨ 2^1024≤E)

theorem rare : 2^553*exceptionalWins.card < eligible.card := by
  classical
  have sub : exceptionalWins ⊆ SmoothTotientTail.exceptional 1501 (2^1024) := by
    intro z h
    obtain ⟨he,E,smooth,hit,extra⟩ := mem_filter.mp h
    by_contra outside
    have dvd := (ordinary_multiples he outside smooth).mp hit
    have large := extra.resolve_left (not_not_intro dvd)
    exact outside (SmoothTotientTail.mem_exceptional.mpr ⟨he,E,smooth,dvd,large⟩)
  exact (Nat.mul_le_mul_left _ (card_le_card sub)).trans_lt
    (SmoothTotientTail.rare553 SmoothTotientEuler.euler_1500)

/-- The public size filter used by the prefix-LCM experiments chooses only
exponents covered by the large-exponent clause throughout the full-size range. -/
theorem scaled {N E : ℕ} (width : 2^2047≤N) (fits : 4*N≤(E+1)^2) : 2^1024≤E := by
  by_contra! small
  have low := Nat.mul_le_mul_left 4 width
  have cap := Nat.pow_le_pow_left (show E+1≤2^1024 by omega) 2
  have strict : ((2:ℕ)^1024)^2<4*2^2047 := by decide +kernel
  omega

end PrimeFactors.IntermediateTotientObstruction
