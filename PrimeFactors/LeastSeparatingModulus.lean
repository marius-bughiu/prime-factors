import PrimeFactors.DivisorResidueCover
import PrimeFactors.PrimePower
import PrimeFactors.PersistentLocalSurvivors
import Mathlib.Data.Nat.Factorization.Induction

/-! Smallest moduli that can assign the two hidden factors opposite labels
using only their residue product. -/
namespace PrimeFactors.LeastSeparatingModulus

open DivisorResidueCover

/-- Basic square tests for an invertible residue. -/
def Basic (d : ℕ) : Prop := d = 4 ∨ d = 8 ∨ (d.Prime ∧ d ≠ 2)

private theorem project {n a b : ℕ} (h : a ∣ b) (s : IsSquare (n : ZMod b)) :
    IsSquare (n : ZMod a) := by
  simpa using s.map (ZMod.castHom h (ZMod a))

private theorem square_at_two_power {n e : ℕ} (pos : 0 < e) (cop : n.Coprime (2^e))
    (checks : ∀ d, d ∣ 2^e → Basic d → IsSquare (n : ZMod d)) :
    IsSquare (n : ZMod (2^e)) := by
  match e with
  | 0 => omega
  | 1 =>
    have all : ∀ x : ZMod 2, x*x=x := by decide
    exact ⟨n,(all _).symm⟩
  | 2 => exact checks 4 (by decide) (Or.inl rfl)
  | k+3 =>
    have divides : 8 ∣ 2^(k+3) := pow_dvd_pow 2 (by omega : 3 ≤ k+3)
    obtain ⟨x,hx⟩ := checks 8 divides (Or.inr (Or.inl rfl))
    have unit : IsUnit (n : ZMod 8) :=
      (ZMod.isUnit_iff_coprime ..).mpr (Nat.Coprime.of_dvd_right divides cop)
    have unitx : IsUnit x := by rw [hx] at unit; exact isUnit_of_mul_isUnit_left unit
    obtain ⟨u, rfl⟩ := unitx
    have all : ∀ z : (ZMod 8)ˣ, (z : ZMod 8)*(z : ZMod 8)=1 := by decide +kernel
    rw [all] at hx
    have one : n ≡ 1 [MOD 8] := (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using hx)
    change n % 8 = 1 % 8 at one
    have eq : (n : ℤ) = 1 + 8*((n/8:ℕ):ℤ) := by omega
    have lifted := PersistentLocalSurvivors.dyadic_unit_square (n/8:ℕ) (k+3)
    rw [← eq] at lifted
    simpa using lifted

/-- Every composite obstruction descends to 4, 8 or a single odd prime divisor.
This statement includes repeated factors of the tested modulus. -/
theorem square_iff {n W : ℕ} (pos : 0 < W) (cop : n.Coprime W) :
    IsSquare (n : ZMod W) ↔ ∀ d, d ∣ W → Basic d → IsSquare (n : ZMod d) := by
  refine ⟨fun s _ h _ => project h s, ?_⟩
  induction W using Nat.recOnPosPrimePosCoprime with
  | hp p e prime epos =>
    intro checks
    by_cases two : p=2
    · subst p; exact square_at_two_power epos cop checks
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero epos.ne'
      letI : Fact p.Prime := ⟨prime⟩
      have div := dvd_pow_self p (Nat.succ_ne_zero k)
      have regular : (n : ZMod p) ≠ 0 := by
        intro eq
        exact (prime.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_right div cop).symm)
          ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp eq)
      exact_mod_cast (isSquare_primePow_iff_of_unit two (n:ℤ) (by exact_mod_cast regular) k).mpr
        (by exact_mod_cast checks p div (Or.inr (Or.inr ⟨prime,two⟩)))
  | h0 => omega
  | h1 => exact fun _ => ⟨0,Subsingleton.elim ..⟩
  | h a b ha hb coprime ia ib =>
    intro checks
    have both := Nat.coprime_mul_iff_right.mp cop
    obtain ⟨x,hx⟩ := ia (by omega) both.1 (fun d hd => checks d (hd.trans (dvd_mul_right ..)))
    obtain ⟨y,hy⟩ := ib (by omega) both.2 (fun d hd => checks d (hd.trans (dvd_mul_left ..)))
    let f := ZMod.chineseRemainder coprime
    refine ⟨f.symm (x,y), f.injective ?_⟩
    rw [map_natCast,map_mul,f.apply_symm_apply]
    exact Prod.ext hx hy

theorem has_selector_iff {n W : ℕ} [NeZero W] (cop : n.Coprime W) :
    (∃ A, Separates (ZMod.unitOfCoprime n cop) A) ↔ ¬ IsSquare (n : ZMod W) := by
  rw [separates_iff]
  constructor
  · intro empty ⟨x,eq⟩
    have unit := (ZMod.isUnit_iff_coprime ..).mpr cop
    rw [eq] at unit
    obtain ⟨u,rfl⟩ := isUnit_of_mul_isUnit_left unit
    have h : u ∈ roots (ZMod.unitOfCoprime n cop) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Units.ext (by simpa [pow_two] using eq.symm)⟩
    simp [empty] at h
  · intro no
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x,hx⟩
    have eq := congrArg Units.val (Finset.mem_filter.mp hx).2
    exact no ⟨x,by simpa [pow_two] using eq.symm⟩

/-- A working period that includes a prescribed wheel always contains a
working period of the form lcm(wheel, d) with d a basic obstruction. -/
theorem reduce_period {n W wheel : ℕ} [NeZero W] (cop : n.Coprime W) (base : wheel ∣ W)
    (hit : ∃ A, Separates (ZMod.unitOfCoprime n cop) A) :
    ∃ d, Basic d ∧ d ∣ W ∧ ¬ IsSquare (n : ZMod d) ∧
      wheel.lcm d ∣ W ∧ ¬ IsSquare (n : ZMod (wheel.lcm d)) := by
  have bad := (has_selector_iff cop).mp hit
  rw [square_iff (Nat.pos_of_ne_zero (NeZero.ne W)) cop] at bad
  push_neg at bad
  obtain ⟨d,hd,b,ns⟩ := bad
  exact ⟨d,b,hd,ns,Nat.lcm_dvd base hd,fun s => ns (project (Nat.dvd_lcm_right ..) s)⟩

end PrimeFactors.LeastSeparatingModulus
