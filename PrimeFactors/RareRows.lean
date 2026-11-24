import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- A square-root class modulo a squarefree integer is determined by the
choice of sign of a single fixed root at each prime. This includes modulus
one, the prime two, and targets that have no roots. -/
theorem rareRows_square_roots (r c : ℕ) (sq : Squarefree r) :
    ((Finset.range r).filter (fun x => x^2 ≡ c [MOD r])).card ≤ 2^r.primeFactors.card := by
  classical
  let S := (Finset.range r).filter (fun x => x^2 ≡ c [MOD r])
  change S.card ≤ _
  rcases S.eq_empty_or_nonempty with h | ⟨z,hz⟩
  · simp [h]
  have props {x : ℕ} (hx : x ∈ S) : x < r ∧ x^2 ≡ c [MOD r] :=
    ⟨Finset.mem_range.mp (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
  let tag (x : ℕ) := r.primeFactors.filter (fun l => x ≡ z [MOD l])
  have inj : Set.InjOn tag (S : Set ℕ) := by
    intro x hx y hy he
    have localEq (l : ℕ) (hl : l ∈ r.primeFactors) : x ≡ y [MOD l] := by
      letI : Fact l.Prime := ⟨Nat.prime_of_mem_primeFactors hl⟩
      have sign {n : ℕ} (hn : n ∈ S) : (n : ZMod l) = z ∨ (n : ZMod l) = -z := by
        apply sq_eq_sq_iff_eq_or_eq_neg.mp
        have h := ((props hn).2.trans (props hz).2.symm).of_dvd
          (Nat.dvd_of_mem_primeFactors hl)
        simpa using (ZMod.natCast_eq_natCast_iff _ _ l).mpr h
      have same : x ≡ z [MOD l] ↔ y ≡ z [MOD l] := by
        have e : l ∈ tag x ↔ l ∈ tag y := by rw [he]
        simpa [tag,hl] using e
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      by_cases pos : x ≡ z [MOD l]
      · exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr pos).trans
          ((ZMod.natCast_eq_natCast_iff _ _ _).mpr (same.mp pos)).symm
      · have nx : (x : ZMod l) ≠ z := fun eq => pos ((ZMod.natCast_eq_natCast_iff _ _ _).mp eq)
        have ny : (y : ZMod l) ≠ z := fun eq => pos (same.mpr ((ZMod.natCast_eq_natCast_iff _ _ _).mp eq))
        exact ((sign hx).resolve_left nx).trans ((sign hy).resolve_left ny).symm
    have globalEq : x ≡ y [MOD r] := by
      apply Nat.modEq_iff_dvd.mpr
      rw [← Nat.prod_primeFactors_of_squarefree sq, Nat.cast_prod]
      apply Finset.prod_dvd_of_coprime
      · intro l hl k hk ne
        exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hl)
          (Nat.prime_of_mem_primeFactors hk)).mpr ne).isCoprime
      · exact fun l hl => Nat.modEq_iff_dvd.mp (localEq l hl)
    exact globalEq.eq_of_lt_of_lt (props hx).1 (props hy).1
  have bound := Finset.card_le_card_of_injOn (t := r.primeFactors.powerset) tag
    (fun x _ => Finset.mem_powerset.mpr (Finset.filter_subset ..)) inj
  simpa using bound

/-- At most d representatives below dr lift each allowed low residue.
The proof uses the quotient and remainder as the two coordinates. -/
theorem rareRows_lift_count (d r : ℕ) (hr : 0 < r) (roots : Finset ℕ) :
    ((Finset.range (d*r)).filter fun x => x % r ∈ roots).card ≤ d*roots.card := by
  let S := (Finset.range (d*r)).filter fun x => x % r ∈ roots
  let key (x : ℕ) := (x/r,x%r)
  have into : ∀ x ∈ S, key x ∈ (Finset.range d) ×ˢ roots := by
    intro x hx
    obtain ⟨small,member⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hr).mpr (Finset.mem_range.mp small)),member⟩
  have inj : Set.InjOn key (S : Set ℕ) := by
    intro x _ y _ eq
    have h := Nat.div_add_mod x r
    rw [show x/r = y/r from congrArg Prod.fst eq,
      show x%r = y%r from congrArg Prod.snd eq, Nat.div_add_mod] at h
    exact h.symm
  simpa [S] using Finset.card_le_card_of_injOn key into inj

/-- All distinct residue rows handled by a fixed common divisor d can be
charged to one of the normalized weights, a square root modulo r, and one
of d lifts. Several weights may have the same target. -/
theorem rareRows_weight_count {ι : Type*} (rows : Finset ℕ) (weights : Finset ι)
    (target : ι → ℕ) (d r : ℕ) (sq : Squarefree r)
    (cover : ∀ x ∈ rows, x < d*r ∧ ∃ w ∈ weights, x^2 ≡ target w [MOD r]) :
    rows.card ≤ weights.card * (d*2^r.primeFactors.card) := by
  classical
  let roots (w : ι) := (Finset.range r).filter fun z => z^2 ≡ target w [MOD r]
  let lifted (w : ι) := (Finset.range (d*r)).filter fun x => x%r ∈ roots w
  have pos := Nat.pos_of_ne_zero sq.ne_zero
  have subset : rows ⊆ weights.biUnion lifted := by
    intro x hx
    obtain ⟨small,w,hw,hit⟩ := cover x hx
    refine Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr small,?_⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ pos),?_⟩
    exact ((Nat.mod_modEq x r).pow 2).trans hit
  calc
    _ ≤ (weights.biUnion lifted).card := Finset.card_le_card subset
    _ ≤ ∑ w ∈ weights, (lifted w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ weights, d*2^r.primeFactors.card := Finset.sum_le_sum fun w _ =>
      (rareRows_lift_count d r pos (roots w)).trans
        (Nat.mul_le_mul_left _ (rareRows_square_roots r (target w) sq))
    _ = _ := by simp

/-- Charging all nonzero signed normalized pairs in a square costs at most
8A²/d². This still holds if d is so large that the square contains only zero. -/
theorem rareRows_signed_box (weights : Finset (ℤ × ℤ)) (A d : ℕ)
    (nz : (0,0) ∉ weights)
    (bounded : ∀ w ∈ weights, w.1.natAbs*d ≤ A ∧ w.2.natAbs*d ≤ A) :
    weights.card*d^2 ≤ 8*A^2 := by
  rcases Nat.eq_zero_or_pos d with rfl | pos
  · simp
  let B := A/d
  let side := Finset.Icc (-(B : ℤ)) B
  have mem {z : ℤ} (b : z.natAbs*d ≤ A) : z ∈ side := by
    have ub : (z.natAbs : ℤ) ≤ B := by exact_mod_cast (Nat.le_div_iff_mul_le pos).mpr b
    rw [Int.natCast_natAbs] at ub
    exact Finset.mem_Icc.mpr (abs_le.mp ub)
  have subset : insert (0,0) weights ⊆ side ×ˢ side := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_product.mpr ⟨mem (by simp),mem (by simp)⟩
    · exact Finset.mem_product.mpr ⟨mem (bounded w hw).1,mem (bounded w hw).2⟩
  have card : side.card = 2*B+1 := by dsimp [side]; rw [Int.card_Icc]; omega
  have plus := Finset.card_le_card subset
  rw [Finset.card_insert_of_not_mem nz, Finset.card_product, card] at plus
  have size : weights.card ≤ 8*B^2 := by
    by_cases h : B=0
    · rw [h] at plus ⊢; norm_num at plus ⊢; exact plus
    · have hB : 1 ≤ B := by omega
      nlinarith [Nat.mul_le_mul_right B hB]
  calc
    _ ≤ (8*B^2)*d^2 := Nat.mul_le_mul_right _ size
    _ = 8*(B*d)^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.div_mul_le_self A d) 2)

/-- Moving the common divisor into the weight budget and summing yields a
single inverse power of the cutoff, even for overlapping sets of rows. -/
theorem rareRows_divisor_total (divisors : Finset ℕ) (rows : ℕ → Finset ℕ)
    (weightCount : ℕ → ℕ) (cutoff m C P : ℕ)
    (many : divisors.card ≤ P) (large : ∀ d ∈ divisors, cutoff ≤ d)
    (budget : ∀ d ∈ divisors, weightCount d*d^2 ≤ C*m)
    (fibers : ∀ d ∈ divisors, (rows d).card ≤ weightCount d*(d*P)) :
    (divisors.biUnion rows).card*cutoff ≤ P^2*C*m := by
  calc
    _ ≤ (∑ d ∈ divisors, (rows d).card)*cutoff :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ d ∈ divisors, (rows d).card*cutoff := Finset.sum_mul ..
    _ ≤ ∑ _d ∈ divisors, C*m*P := Finset.sum_le_sum fun d hd => calc
      _ ≤ (weightCount d*(d*P))*d := Nat.mul_le_mul (fibers d hd) (large d hd)
      _ = weightCount d*d^2*P := by ring
      _ ≤ C*m*P := Nat.mul_le_mul_right _ (budget d hd)
    _ = divisors.card*(C*m*P) := by simp
    _ ≤ P*(C*m*P) := Nat.mul_le_mul_right _ many
    _ = P^2*C*m := by ring

end PrimeFactors
