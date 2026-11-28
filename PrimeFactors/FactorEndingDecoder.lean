import PrimeFactors.ObservableSeparationDepth
import PrimeFactors.LocalMidpointLanes

/-! Recover low factor remainders from the product and a supplied true
sum remainder. Each step strips a power of four or lifts one odd root by
one binary digit, with no enumeration of possible factor suffixes. -/
namespace PrimeFactors.FactorEndingDecoder

open LocalMidpointLanes (hasRoot)
open private PrimeFactors.LocalMidpointLanes.odd_square from PrimeFactors.LocalMidpointLanes

/-- Canonical lift starting at one modulo eight. The quotient supplies the
correction. Reducing after each step keeps the intermediate root bounded. -/
def unitRoot (D : ℤ) : ℕ → ℤ
  | 0 => 1
  | i+1 =>
    let x := unitRoot D i
    (x + 4*2^i*((D-x^2)/(2:ℤ)^(i+3))) % (2:ℤ)^(i+4)

private theorem unit_spec {D : ℤ} (base : (8:ℤ) ∣ D-1) (i : ℕ) :
    Odd (unitRoot D i) ∧ (2:ℤ)^(i+3) ∣ D-(unitRoot D i)^2 := by
  induction i with
  | zero => exact ⟨by exact (by decide : Odd (1:ℤ)),by simpa [unitRoot] using base⟩
  | succ i ih =>
    let x := unitRoot D i
    obtain ⟨⟨v,hv⟩,z,hz⟩ := ih
    change x=2*v+1 at hv
    change D-x^2=2^(i+3)*z at hz
    let y := x+4*2^i*z
    have yo : Odd y := ⟨v+2*2^i*z,by dsimp [y]; linarith only [hv]⟩
    have corr : unitRoot D (i+1)=y%(2:ℤ)^(i+4) := by
      change (x+4*2^i*((D-x^2)/(2:ℤ)^(i+3)))%_ = _
      rw [hz,Int.mul_ediv_cancel_left _ (by positivity)]
    have congr := Int.mod_modEq y ((2:ℤ)^(i+4))
    have low := congr.of_dvd (dvd_pow_self (2:ℤ) (by omega : i+4≠0))
    rw [corr]
    constructor
    · exact Int.odd_iff.mpr ((show (y%((2:ℤ)^(i+4)))%2=y%2 from low).trans (Int.odd_iff.mp yo))
    · have dy : (2:ℤ)^(i+4) ∣ D-y^2 := by
        refine ⟨-v*z-2^i*z^2,?_⟩
        dsimp [y]
        rw [pow_add] at hz ⊢
        rw [hv] at hz ⊢
        linear_combination hz
      exact Int.modEq_iff_dvd.mp ((congr.pow 2).trans (Int.modEq_iff_dvd.mpr dy))

/-- One square root if the congruence is soluble. Inputs where it is
insoluble can be recognized by squaring the returned value. -/
def root : ℕ → ℤ → ℤ
  | 0, _ => 0
  | 1, D => D%2
  | e+2, D => if D%4=0 then 2*root e (D/4) else unitRoot D (e-1)

theorem root_spec (e : ℕ) (D : ℤ) (possible : hasRoot e D) :
    (2:ℤ)^e ∣ D-(root e D)^2 := by
  match e with
  | 0 => simp [root]
  | 1 =>
    change (2:ℤ) ∣ D-(D%2)^2
    apply Int.modEq_iff_dvd.mp
    change (D%2)^2%2=D%2
    rw [pow_two,Int.mul_emod]
    have l := Int.emod_nonneg D (by decide : (2:ℤ)≠0)
    have u := Int.emod_lt_of_pos D (by decide : (0:ℤ)<2)
    interval_cases D%2 <;> decide
  | e+2 =>
    obtain ⟨x,dx⟩ := possible
    rw [root]
    split_ifs with four
    · have divD : (4:ℤ) ∣ D := Int.dvd_of_emod_eq_zero four
      have dX := (pow_dvd_pow (2:ℤ) (by omega : 2≤e+2)).trans dx
      change (4:ℤ) ∣ D-x^2 at dX
      have twice : Even x := by
        rcases Int.even_or_odd x with even|⟨z,hz⟩
        · exact even
        · obtain ⟨d,hd⟩ := divD
          obtain ⟨c,hc⟩ := dX
          rw [hz,hd] at hc
          have bad : 4*(d-z^2-z-c)=1 := by linear_combination hc
          omega
      obtain ⟨r,hr⟩ := twice
      have D4 : D=4*(D/4) := by omega
      obtain ⟨c,hc⟩ := dx
      have half : D/4-r^2=(2:ℤ)^e*c := by
        rw [hr,pow_add] at hc
        apply mul_left_cancel₀ (by decide : (4:ℤ)≠0)
        linear_combination hc-D4
      obtain ⟨u,hu⟩ := root_spec e (D/4) ⟨r,⟨c,half⟩⟩
      refine ⟨u,?_⟩
      rw [pow_add]
      linear_combination D4+4*hu
    · have odd : Odd x := by
        rcases Int.even_or_odd x with ⟨v,hv⟩|o
        · obtain ⟨c,hc⟩ := dx
          rw [hv,pow_add] at hc
          have deq : D=4*(v^2+2^e*c) := by linear_combination hc
          simp [deq] at four
        · exact o
      have base := PrimeFactors.LocalMidpointLanes.odd_square odd
      cases e with
      | zero =>
        change (4:ℤ) ∣ D-1
        convert dvd_add dx ((by decide : (4:ℤ) ∣ 8).trans base) using 1
        ring
      | succ e =>
        have three := (pow_dvd_pow (2:ℤ) (by omega : 3≤e+1+2)).trans dx
        have good : (8:ℤ) ∣ D-1 := by convert dvd_add three base using 1; ring
        simpa only [Nat.add_one_sub_one,Nat.add_assoc] using (unit_spec good e).2

/-- Two candidate endings, obtained by adding and subtracting one modular
square root from the midpoint of the supplied sum. -/
def endings (N s : ℤ) (k e : ℕ) : ℤ × ℤ :=
  let h := s/2
  let d := root e ((h^2-N)%(2:ℤ)^e)
  ((h+d)%(2:ℤ)^k,(h-d)%(2:ℤ)^k)

/-- At any sufficient precision the two output residues are exactly the
two factor endings, in either order. The computation reads only N and s. -/
theorem endings_correct {p q s : ℤ} {k e : ℕ} (hp : Odd p) (hq : Odd q)
    (he : 1≤e) (room : k≤e) (sum : s ≡ p+q [ZMOD (2:ℤ)^e])
    (det : FactorPairSeparationDepth.Determines p q k e) :
    endings (p*q) s k e=(p%(2:ℤ)^k,q%(2:ℤ)^k) ∨
      endings (p*q) s k e=(q%(2:ℤ)^k,p%(2:ℤ)^k) := by
  let h := s/2
  let M : ℤ := 2^e
  let D := h^2-p*q
  let d := root e (D%M)
  have even_sum : s=2*h := by
    have low := sum.of_dvd (dvd_pow_self (2:ℤ) (by omega : e≠0))
    change s%2=(p+q)%2 at low
    obtain ⟨v,hv⟩ := hp
    obtain ⟨w,hw⟩ := hq
    dsimp [h]
    omega
  have root0 : (h-p)^2 ≡ D [ZMOD M] := by
    apply Int.modEq_iff_dvd.mpr
    have ds := Int.modEq_iff_dvd.mp sum.symm
    convert dvd_mul_of_dvd_right ds p using 1
    dsimp [D]
    linear_combination -p*even_sum
  have root1 := root_spec e (D%M) ⟨h-p,Int.modEq_iff_dvd.mp
    (root0.trans (Int.mod_modEq D M).symm)⟩
  have rootD : M ∣ D-d^2 := Int.modEq_iff_dvd.mp
    ((Int.modEq_iff_dvd.mpr root1).trans (Int.mod_modEq D M))
  have prod : (h+d)*(h-d) ≡ p*q [ZMOD M] := by
    apply Int.modEq_iff_dvd.mpr
    convert dvd_neg.mpr rootD using 1
    dsimp [D]
    ring
  have total : (h+d)+(h-d) ≡ p+q [ZMOD M] := by
    rwa [show (h+d)+(h-d)=s by linarith only [even_sum]]
  have low := total.of_dvd (pow_dvd_pow (2:ℤ) room)
  have possible := (FactorPairSeparationDepth.candidate_iff p q (h+d) e).mp ⟨h-d,total,prod⟩
  rcases det (h+d) possible with left|right
  · have a := (Int.modEq_iff_dvd.mpr left).symm
    have b : h-d ≡ q [ZMOD (2:ℤ)^k] := by simpa only [add_sub_cancel_left] using low.sub a
    exact Or.inl (Prod.ext a b)
  · have a := (Int.modEq_iff_dvd.mpr right).symm
    have b : h-d ≡ p [ZMOD (2:ℤ)^k] := by simpa only [add_sub_cancel_left,add_sub_cancel_right] using low.sub a
    exact Or.inr (Prod.ext a b)

/-- With a genuine sum clue, return the endings as soon as their order-free
pair is determined by the modular observations. -/
def readEndings (N s : ℤ) (k e : ℕ) : Option (ℤ × ℤ) :=
  if ObservableSeparationDepth.ready N s k e then some (endings N s k e) else none

theorem reads_iff {p q s : ℤ} {k e : ℕ} (hk : 3≤k) (he : 2≤e)
    (hp : Odd p) (hq : Odd q) (distinct : p≠q) (sum : s ≡ p+q [ZMOD (2:ℤ)^e]) :
    (readEndings (p*q) s k e).isSome = true ↔ FactorPairSeparationDepth.Determines p q k e := by
  simpa [readEndings,Bool.apply_cond] using ObservableSeparationDepth.ready_iff hk he hp hq distinct sum

end PrimeFactors.FactorEndingDecoder
