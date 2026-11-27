import PrimeFactors.IntermediateShiftedExponent
import PrimeFactors.UniformDivisorCount
import PrimeFactors.PowerImageWidth

/-! Count the shifts that can improve upon direct multiples of an exponent, even if
an arbitrary divisor of the shifted product can be chosen as the exponent. -/
namespace PrimeFactors.IntermediateShiftCount

open IntermediateTotientObstruction (Hit)
open IntermediateShiftedExponent (forced_gcd of_sum_divisor)

set_option exponentiation.threshold 4096

def Extra (N F k : ℕ) : Prop :=
  ∃ E : ℕ, 0<E ∧ E≤N ∧ E∣N+k ∧ Hit N E F ∧ ¬E∣F

/-- A nontrivial factorization of (N+k)/g produces a new hit with E=g*a, whenever
g is the shifted deficit. The proper factor a prevents E from dividing F. -/
theorem realize {N F k g a d : ℕ} (fp : 0<F) (fn : F<N) (kp : 0<k) (kn : k≤N)
    (geq : g=N-F+k) (aa : 2≤a) (dd : 2≤d) (factor : F+g=g*a*d) :
    0<g*a ∧ g*a≤N ∧ g*a∣N+k ∧ Hit N (g*a) F ∧ ¬g*a∣F := by
  have gp : 0<g := by omega
  have ep : 0<g*a := Nat.mul_pos gp (by omega)
  have sum : F+g=N+k := by omega
  have twice := Nat.mul_le_mul_left (g*a) dd
  have en : g*a≤N := by omega
  have shift : g*a∣N+k := ⟨d,sum ▸ factor⟩
  have gd : N-F+k∣g*a := geq ▸ dvd_mul_right g a
  refine ⟨ep,en,shift,of_sum_divisor ep en fp fn kp shift gd,?_⟩
  intro direct
  have both : g*a∣F+g := sum ▸ shift
  have only := (Nat.dvd_add_right direct).mp both
  have bound := Nat.le_of_dvd gp only
  have larger := Nat.mul_le_mul_left g aa
  omega

/-- This exact criterion eliminates the existential choice of exponent. In addition to
g dividing the totient, F/g+1 must itself have two factors at least two. -/
theorem exact_criterion {N F k : ℕ} (fp : 0<F) (fn : F<N) (kp : 0<k) (small : k≤N-F) :
    let g := N-F+k
    Extra N F k ↔ g∣F ∧ ∃ a d : ℕ, 2≤a ∧ 2≤d ∧ F/g+1=a*d := by
  let g := N-F+k
  have gp : 0<g := by dsimp [g]; omega
  have sum : F+g=N+k := by dsimp [g]; omega
  change Extra N F k ↔ g∣F ∧ ∃ a d : ℕ, 2≤a ∧ 2≤d ∧ F/g+1=a*d
  constructor
  · rintro ⟨E,ep,en,shift,hit,extra⟩
    have eq : E.gcd F=g := forced_gcd ep fn small shift hit extra
    have gf : g∣F := eq ▸ Nat.gcd_dvd_right E F
    have ge : g∣E := eq ▸ Nat.gcd_dvd_left E F
    obtain ⟨a,ha⟩ := ge
    obtain ⟨d,hd⟩ := shift
    have aa : 2≤a := by
      by_contra! h
      interval_cases a <;> simp_all
    have dd : 2≤d := by
      by_contra! h
      interval_cases d <;> simp_all
      omega
    refine ⟨gf,a,d,aa,dd,?_⟩
    obtain ⟨b,hb⟩ := gf
    have left : g*(b+1)=g*(a*d) := by
      calc
        _ = F+g := by rw [hb]; ring
        _ = N+k := sum
        _ = _ := by rw [hd,ha]; ring
    have smallEq := Nat.eq_of_mul_eq_mul_left gp left
    simpa only [hb,Nat.mul_div_cancel_left _ gp] using smallEq
  · rintro ⟨gf,a,d,aa,dd,eq⟩
    have quotient := Nat.div_mul_cancel gf
    have factor : F+g=g*a*d := by
      nlinarith only [quotient,congrArg (fun t => t*g) eq]
    exact ⟨g*a,realize fp fn kp (by omega) rfl aa dd factor⟩

noncomputable def shifts (N F K : ℕ) : Finset ℕ := by
  classical exact (Finset.Icc 1 K).filter (Extra N F)

/-- Each successful k has its own divisor N−F+k of F, independently of how many
different exponents can be selected at that particular shift. -/
theorem card_le {N F K : ℕ} (fp : 0<F) (fn : F<N) (cap : K≤N-F) :
    (shifts N F K).card≤F.divisors.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun k => N-F+k)
  · intro k hk
    rw [shifts,Finset.mem_filter,Finset.mem_Icc] at hk
    exact Nat.mem_divisors.mpr ⟨((exact_criterion fp fn hk.1.1 (hk.1.2.trans cap)).mp hk.2).1,fp.ne'⟩
  · intro i _ j _ eq
    exact Nat.add_left_cancel eq

/-- The number of successful positive shifts is below 2^240, and their fraction in
the complete range of 2^1024 choices is strictly less than 2^-784. -/
theorem full_size {p q : ℕ} (pp : 1<p) (qp : 1<q) (lo : 2^2047≤p*q) (hi : p*q<2^2048) :
    let S := shifts (p*q) ((p-1)*(q-1)) (2^1024)
    S.card<2^240 ∧ 2^784*S.card<(Finset.Icc 1 (2^1024)).card := by
  let N := p*q
  let F := (p-1)*(q-1)
  have fp : 0<F := Nat.mul_pos (by omega) (by omega)
  have eq : N=F+(p+q-1) := PowerImageWidth.offset pp.le qp.le
  have fn : F<N := by omega
  have enough : 2^1024≤N-F := by
    by_contra! short
    have a := Nat.pow_le_pow_left (show p+q≤2^1024 by omega) 2
    have b := Nat.mul_le_mul_left 4 lo
    have ag : 4*(p*q)≤(p+q)^2 := by
      exact_mod_cast (show (4:ℤ)*(p*q)≤(p+q)^2 by nlinarith only [sq_nonneg ((p:ℤ)-q)])
    omega
  have fin : F<2^2049 := by change N<2^2048 at hi; omega
  have count := (card_le fp fn enough).trans_lt (UniformDivisorCount.below_2049 fp fin)
  refine ⟨count,?_⟩
  rw [Nat.card_Icc]
  exact (Nat.mul_lt_mul_of_pos_left count (by decide : 0<(2:ℕ)^784)).trans_eq (by decide +kernel)

/-- A constructed shift from the factor gap. For p≡3 mod 4, p≥7 and q>p+1, the
publicly computable exponent (N+k)/2 is a new hit if k is already supplied. -/
theorem gap_construction {p q : ℕ} (big : 7≤p) (residue : p%4=3) (sep : p+1<q) :
    let N := p*q
    let F := (p-1)*(q-1)
    let k := q-p-1
    let E := (N+k)/2
    0<k ∧ k≤N-F ∧ 0<E ∧ E≤N ∧ E∣N+k ∧ Hit N E F ∧ ¬E∣F := by
  let N := p*q
  let F := (p-1)*(q-1)
  let k := q-p-1
  let a := (p+1)/4
  let g := 2*(q-1)
  have af : 4*a=p+1 := by dsimp [a]; omega
  have aa : 2≤a := by omega
  have fp : 0<F := Nat.mul_pos (by omega) (by omega)
  have eq : N=F+(p+q-1) := PowerImageWidth.offset (by omega) (by omega)
  have fn : F<N := by omega
  have kp : 0<k := by dsimp [k]; omega
  have small : k≤N-F := by dsimp [k]; omega
  have geq : g=N-F+k := by dsimp only [g,k]; omega
  have factor : F+g=g*a*2 := by
    dsimp only [F,g]
    have pred : p-1+2=p+1 := by omega
    nlinarith only [congrArg (fun t => t*(q-1)) af,congrArg (fun t => t*(q-1)) pred]
  have direct : (N+k)/2=g*a := by
    have tmp : F+g=N+k := by omega
    omega
  change 0<k ∧ k≤N-F ∧ _
  exact ⟨kp,small,direct.symm ▸ realize fp fn kp (by omega) geq aa (by decide : 2≤2) factor⟩

/-- The same supplied shift directly reconstructs both factors with one square root. -/
theorem gap_readout {p q k : ℕ} (sep : p<q) (clue : k=q-p-1) :
    let S := (4*(p*q)+(k+1)^2).sqrt
    (S-(k+1))/2=p ∧ (S+(k+1))/2=q := by
  have gap : k+1+p=q := by omega
  have square : 4*(p*q)+(k+1)^2=(p+q)^2 := by rw [←gap]; ring
  rw [square,Nat.sqrt_eq']
  omega

/-- At 209=11·19, the first shift has 30∣180 but F/30+1=7 is prime, so no
choice of exponent can add a hit. Shift seven succeeds with (209+7)/2=108. -/
theorem example209 : (209-180+1)∣180 ∧ ¬Extra 209 180 1 ∧ Extra 209 180 7 := by
  refine ⟨by decide,?_,⟨108,?_⟩⟩
  · intro extra
    obtain ⟨_,a,d,aa,dd,eq⟩ := (exact_criterion (by decide) (by decide) (by decide) (by decide)).mp extra
    change 7=a*d at eq
    have bd := Nat.mul_le_mul_left a dd
    have cap : a≤3 := by omega
    interval_cases a <;> omega
  · exact (gap_construction (p:=11) (q:=19) (by decide) (by decide) (by decide)).2.2

end PrimeFactors.IntermediateShiftCount
