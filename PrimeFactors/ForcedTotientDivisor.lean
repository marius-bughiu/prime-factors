import PrimeFactors.CyclotomicRadixLift
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! The gcd of all prime-predecessor products compatible with one public unit
residue class is exactly 4, 8, 12, or 24, even when the class is taken modulo
an arbitrarily large fixed multiple of 12. Prime widths here are unbounded. -/
namespace PrimeFactors.ForcedTotientDivisor

open CyclotomicRadixLift (stride weight bonus)

/-- A common divisor on every sufficiently large, distinct prime pair lifting a given class. -/
def Forces (n T B d : ℕ) : Prop := ∀ p q : ℕ, p.Prime → q.Prime → B<p → p<q →
    p*q ≡ n [MOD T] → d∣(p-1)*(q-1)

private theorem same_stride {n r T : ℕ} (h : n ≡ r [MOD T]) (twelve : 12∣T) :
    stride n=stride r := by
  have f : n%4=r%4 := h.of_dvd ((by decide : 4∣12).trans twelve)
  have t : n%3=r%3 := h.of_dvd ((by decide : 3∣12).trans twelve)
  simp only [stride,weight,bonus,f,t]

private theorem reduced {L m : ℕ} (div : m∣L) {p : ℕ} {u : (ZMod L)ˣ}
    (h : (p:ZMod L)=u) : (p:ZMod m) = ZMod.unitsMap div u := by
  simpa only [map_natCast,ZMod.unitsMap_val,ZMod.castHom_apply] using
    congrArg (ZMod.castHom div (ZMod m)) h

/-- Lift any desired unit at m to two primes in the prescribed product class.
Dirichlet supplies the primes above any lower bound; their sizes need not match. -/
private theorem local_tests {n T d : ℕ} {P : ℕ → ℕ → Prop} (tp : 0<T) (dp : 0<d)
    (nc : n.Coprime T)
    (realize : ∀ a b : (ZMod (d*T))ˣ, ∃ p q : ℕ, P p q ∧ 1≤p ∧ 1≤q ∧
      (p:ZMod (d*T))=a ∧ (q:ZMod (d*T))=b)
    (force : ∀ p q, P p q → p*q ≡ n [MOD T] → d∣(p-1)*(q-1)) :
    ∃ v : ℕ, v ≡ n [MOD T] ∧ ∀ m, m∣d → ∀ u : (ZMod m)ˣ,
      ((u:ZMod m)-1)*((v:ZMod m)-u)=0 := by
  let L := d*T
  letI : NeZero L := ⟨(Nat.mul_pos dp tp).ne'⟩
  have tl : T∣L := dvd_mul_left ..
  obtain ⟨w,hw⟩ := ZMod.unitsMap_surjective tl (ZMod.unitOfCoprime n nc)
  let v := (w:ZMod L).val
  have lift : (v:ZMod L)=w := ZMod.natCast_zmod_val ..
  have nv : (v:ZMod T)=n := by
    rw [reduced tl lift,hw,ZMod.coe_unitOfCoprime]
  have congr := (ZMod.natCast_eq_natCast_iff ..).mp nv
  refine ⟨v,congr,?_⟩
  intro m md u
  have ml : m∣L := md.trans (dvd_mul_right ..)
  obtain ⟨a,ha⟩ := ZMod.unitsMap_surjective ml u
  let b := w/a
  obtain ⟨p,q,accepted,pp,qp,pa,qb⟩ := realize a b
  have prod : ((p*q:ℕ):ZMod L)=v := by
    rw [Nat.cast_mul,pa,qb,lift]
    change (↑(a*(w/a)) : ZMod L) = ↑w
    rw [mul_comm a,div_mul_cancel]
  have prodN := (ZMod.natCast_eq_natCast_iff ..).mp prod
  have coef := md.trans (force p q accepted ((prodN.of_dvd tl).trans congr))
  have zero := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr coef
  rw [Nat.cast_mul,Nat.cast_sub pp,Nat.cast_sub qp,Nat.cast_one] at zero
  have redprod := (ZMod.natCast_eq_natCast_iff ..).mpr (prodN.of_dvd ml)
  rw [Nat.cast_mul] at redprod
  have pu : (p:ZMod m)=u := (reduced ml pa).trans (congrArg (fun z : (ZMod m)ˣ => (z:ZMod m)) ha)
  calc
    _ = (p:ZMod m)*((p-1)*(q-1)) := by rw [←pu,←redprod]; ring
    _ = 0 := by rw [zero,mul_zero]

/-- Three unit tests suffice: -1 at any modulus, 3 at a power of 2, and
2 at an odd prime power. They bound the two parts by 8 and 3. -/
private theorem maximal {n d : ℕ}
    (tests : ∀ m, m∣d → ∀ u : (ZMod m)ˣ, ((u:ZMod m)-1)*((n:ZMod m)-u)=0) :
    d∣stride n := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k prime pk
  let m := p^k
  have neg : (m:ℤ)∣2*((n:ℤ)+1) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast
    have h := tests m pk (-1)
    simp only [Units.val_neg,Units.val_one] at h
    linear_combination -h
  have test {a : ℕ} (cop : a.Coprime m) :
      (m:ℤ)∣((a:ℤ)-1)*((n:ℤ)-a) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast
    simpa only [ZMod.coe_unitOfCoprime] using tests m pk (ZMod.unitOfCoprime a cop)
  change m∣stride n
  by_cases two : p=2
  · have cop : Nat.Coprime 3 m := by
      simpa only [m,two] using ((by decide : Nat.Coprime 3 2).pow_right k)
    have t : (m:ℤ)∣2*((n:ℤ)-3) := by simpa using test cop
    have eight : (m:ℤ)∣8 := by
      convert Int.dvd_sub neg t using 1
      ring
    have small : m∣8 := by exact_mod_cast eight
    by_cases key : n%4=3
    · exact small.trans (by simp [stride,weight,bonus,key]; split_ifs <;> decide)
    · have four : m∣4 := by
        obtain ⟨j,hj⟩ := neg
        have size := Nat.le_of_dvd (by decide) small
        interval_cases m <;> norm_num at small hj ⊢
        omega
      exact four.trans (by simp [stride,weight,bonus,key]; split_ifs <;> decide)
  · have cop : Nat.Coprime 2 m :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr (fun h => two ((Nat.prime_dvd_prime_iff_eq Nat.prime_two prime).mp h).symm)).pow_right k
    have t : (m:ℤ)∣(n:ℤ)-2 := by simpa using test cop
    have six : (m:ℤ)∣6 := by
      convert Int.dvd_sub neg (dvd_mul_of_dvd_right t 2) using 1
      ring
    have small : m∣3 := cop.symm.dvd_of_dvd_mul_left (by exact_mod_cast six : m∣2*3)
    by_cases key : n%3=2
    · exact small.trans (by simp [stride,weight,bonus,key]; split_ifs <;> decide)
    · obtain ⟨j,hj⟩ := t
      have size := Nat.le_of_dvd (by decide) small
      have one : m=1 := by
        interval_cases m <;> norm_num at small hj ⊢
        omega
      simp [one]

/-- This finite implication also applies to a size-restricted set of pairs
provided every two unit classes can be realized in that set at the indicated
modulus. In particular it states exactly what a prime-interval estimate must
supply to extend the optimality result to two factors of specified widths. -/
theorem bound_of_realization {n T d : ℕ} {P : ℕ → ℕ → Prop}
    (tp : 0<T) (dp : 0<d) (nc : n.Coprime T) (twelve : 12∣T)
    (realize : ∀ a b : (ZMod (d*T))ˣ, ∃ p q : ℕ, P p q ∧ 1≤p ∧ 1≤q ∧
      (p:ZMod (d*T))=a ∧ (q:ZMod (d*T))=b)
    (force : ∀ p q, P p q → p*q ≡ n [MOD T] → d∣(p-1)*(q-1)) :
    d∣stride n := by
  obtain ⟨v,cong,tests⟩ := local_tests tp dp nc realize force
  rw [←same_stride cong twelve]
  exact maximal tests

/-- For any prescribed lower bound at least two and any fixed positive multiple
of twelve, the largest universally guaranteed divisor is exactly the public stride. -/
theorem forces_iff {n T B d : ℕ} (tp : 0<T) (twelve : 12∣T) (nc : n.Coprime T)
    (bp : 2≤B) (dp : 0<d) : Forces n T B d ↔ d∣stride n := by
  constructor
  · intro force
    let P (p q : ℕ) := p.Prime ∧ q.Prime ∧ B<p ∧ p<q
    apply bound_of_realization (P:=P) tp dp nc twelve
    · letI : NeZero (d*T) := ⟨(Nat.mul_pos dp tp).ne'⟩
      intro a b
      obtain ⟨p,pb,pp,pa⟩ := Nat.forall_exists_prime_gt_and_eq_mod a.isUnit B
      obtain ⟨q,pq,qp,qb⟩ := Nat.forall_exists_prime_gt_and_eq_mod b.isUnit p
      exact ⟨p,q,⟨pp,qp,pb,pq⟩,pp.one_le,qp.one_le,pa,qb⟩
    · rintro p q ⟨pp,qp,pb,pq⟩
      exact force p q pp qp pb pq
  · intro good p q pp qp pb pq cong
    rw [←same_stride cong twelve] at good
    exact good.trans (CyclotomicRadixLift.divides (pp.odd_of_ne_two (by omega)) (qp.odd_of_ne_two (by omega)))

end PrimeFactors.ForcedTotientDivisor
