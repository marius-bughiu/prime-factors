import Mathlib.Algebra.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! One gcd suffices to detect any proper gcd in a chain of nested exponents.
Modular equality to one identifies the last index at which to take the gcd. -/

namespace PrimeFactors.LastPowerGCD

def reading (n : ℕ) (a : ℤ) (e : ℕ) : ℕ := Int.gcd (a^e-1) n

def proper (n g : ℕ) : Prop := 1<g ∧ g<n

theorem divides (n : ℕ) (a : ℤ) {e f : ℕ} (ef : e ∣ f) :
    reading n a e ∣ reading n a f := by
  obtain ⟨k,rfl⟩ := ef
  exact Int.gcd_dvd_gcd_of_dvd_left _ (pow_one_sub_dvd_pow_mul_sub_one a e k)

theorem dvd_input (n : ℕ) (a : ℤ) (e : ℕ) : reading n a e ∣ n :=
  Int.natCast_dvd_natCast.mp Int.gcd_dvd_right

theorem whole_iff (n : ℕ) (a : ℤ) (e : ℕ) :
    reading n a e = n ↔ (a : ZMod n)^e=1 := by
  have eq : (a : ZMod n)^e=1 ↔ (n : ℤ) ∣ a^e-1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_pow, Int.cast_one, sub_eq_zero]
  rw [eq]
  constructor
  · intro h
    rw [← h]
    exact Int.gcd_dvd_left
  · intro h
    exact Nat.dvd_antisymm (dvd_input ..) (Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd h (dvd_refl _)))

private theorem stays_whole {n : ℕ} (a : ℤ) {e f : ℕ} (ef : e ∣ f) (h : reading n a e=n) :
    reading n a f=n := by
  have dv := divides n a ef
  rw [h] at dv
  exact Nat.dvd_antisymm (dvd_input ..) dv

/-- The power at k differs from one. Stop there at the horizon or when the
next power is one. Equality at the next power needs no gcd to check. -/
theorem selected {n : ℕ} (npos : 0<n) (a : ℤ) (e : ℕ → ℕ)
    (nested : ∀ i j, i≤j → e i ∣ e j) {k H : ℕ} (within : k≤H)
    (active : (a : ZMod n)^(e k)≠1) (last : k=H ∨ (a : ZMod n)^(e (k+1))=1) :
    (∃ i ≤ H, proper n (reading n a (e i))) ↔ proper n (reading n a (e k)) := by
  constructor
  · rintro ⟨i,ih,large,small⟩
    have ik : i≤k := by
      by_contra! later
      rcases last with rfl|next
      · omega
      · have full := stays_whole a (nested _ _ later) ((whole_iff ..).mpr next)
        omega
    have pos : 0<reading n a (e k) := Nat.pos_of_dvd_of_pos (dvd_input ..) npos
    exact ⟨large.trans_le (Nat.le_of_dvd pos (divides n a (nested _ _ ik))),
      lt_of_le_of_ne (Nat.le_of_dvd npos (dvd_input ..)) (fun h => active ((whole_iff ..).mp h))⟩
  · exact fun h => ⟨k,within,h⟩

theorem empty_of_first_one {n : ℕ} (a : ℤ) (e : ℕ → ℕ) (chain : ∀ i, e 0 ∣ e i)
    (first : (a : ZMod n)^(e 0)=1) (i : ℕ) : ¬ proper n (reading n a (e i)) := by
  rw [stays_whole a (chain i) ((whole_iff ..).mpr first)]
  exact fun h => (Nat.lt_irrefl n) h.2

/-- The two chains computed in the experiment begin at e₀ and double the
exponent using one modular squaring at a time. -/
theorem doubling (initial i j : ℕ) (ij : i≤j) : initial*2^i ∣ initial*2^j :=
  Nat.mul_dvd_mul_left _ (pow_dvd_pow _ ij)

end PrimeFactors.LastPowerGCD
