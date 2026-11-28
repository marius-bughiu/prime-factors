import PrimeFactors.CircleMarkAutocorrelation
import PrimeFactors.QuarticSlopeBit

/-! Shifted intersections of the two mark sets for negative-Jacobi targets. -/
namespace PrimeFactors.CircleMarkCrossTargets
open Finset CircleBranchCount CircleMarkAutocorrelation
open scoped Classical
open private PrimeFactors.QuarticSlopeBit.square_crt from PrimeFactors.QuarticSlopeBit

noncomputable def cut {R : Type*} [Add R] (A B : Finset R) (h : R) : Finset R :=
  A.filter fun x => x+h∈B

/-- Number of starting coordinates x marked for a and ending coordinates x+h
marked for b. A and B need not occupy classes at the same hidden prime. -/
noncomputable def cross (n : ℕ) [NeZero n] (a b h : ℤ) : ℕ :=
  (cut (marked n a) (marked n b) (h : ZMod n)).card

@[simp] theorem cut_univ {R : Type*} [AddGroup R] [Fintype R]
    (A : Finset R) (h : R) : cut A univ h=A := by classical simp [cut]

@[simp] theorem univ_cut {R : Type*} [AddGroup R] [Fintype R]
    (B : Finset R) (h : R) : (cut univ B h).card=B.card := by
  classical
  have eqn : (cut univ B h).map (Equiv.addRight h).toEmbedding=B := by
    ext x
    simp [cut,mem_map_equiv]
  simpa using congrArg Finset.card eqn

theorem mark_right {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    {a : ℤ} (np : legendreSym p a= -1) (x : ZMod (p*q)) :
    x∈marked (p*q) a ↔ (ZMod.chineseRemainder cop x).2^2=(a : ZMod q) := by
  let e := ZMod.chineseRemainder cop
  have miss : (e x).1^2≠(a : ZMod p) := fun h =>
    (legendreSym.eq_neg_one_iff p).mp np ((isSquare_iff_exists_sq _).mpr ⟨_,h.symm⟩)
  simp only [marked,mem_filter,mem_univ,true_and]
  rw [←isUnit_map_iff e,map_sub,map_intCast,map_pow,Prod.isUnit_iff]
  change ¬(IsUnit ((a : ZMod p)-(e x).1^2) ∧ IsUnit ((a : ZMod q)-(e x).2^2)) ↔ _
  change (¬(IsUnit ((a : ZMod p)-(e x).1^2) ∧ IsUnit ((a : ZMod q)-(e x).2^2))) ↔ (e x).2^2=(a : ZMod q)
  simp only [isUnit_iff_ne_zero,ne_eq,sub_eq_zero,Ne.symm miss,not_false_eq_true,true_and,not_not]
  exact eq_comm

/-- The component at the prime where the target is a nonsquare is unrestricted. -/
noncomputable def side (r : ℕ) [Fact r.Prime] (a : ℤ) : Finset (ZMod r) :=
  if legendreSym r a=1 then roots r a else univ

private theorem sides {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    {a : ℤ} (neg : jacobiSym a (p*q)= -1) (x : ZMod (p*q)) :
    x∈marked (p*q) a ↔ (ZMod.chineseRemainder cop x).1∈side p a ∧
      (ZMod.chineseRemainder cop x).2∈side q a := by
  rcases opposite neg with h|h
  · simpa [side,roots,h.1,h.2] using mark_left cop h.2 x
  · simpa [side,roots,h.1,h.2] using mark_right cop h.1 x

theorem factor_count {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    {a b : ℤ} (na : jacobiSym a (p*q)= -1) (nb : jacobiSym b (p*q)= -1) (h : ℤ) :
    cross (p*q) a b h=(cut (side p a) (side p b) (h : ZMod p)).card*
      (cut (side q a) (side q b) (h : ZMod q)).card := by
  let e := ZMod.chineseRemainder cop
  have eqn : (cut (marked (p*q) a) (marked (p*q) b) (h : ZMod (p*q))).map e.toEquiv.toEmbedding=
      cut (side p a) (side p b) (h : ZMod p) ×ˢ cut (side q a) (side q b) (h : ZMod q) := by
    ext z
    obtain ⟨x,rfl⟩ := e.surjective z
    simp only [mem_map_equiv,Equiv.symm_apply_apply,cut,mem_filter,mem_product,
      sides cop na,sides cop nb,map_add,map_intCast]
    change ((e (e.symm (e x))).1∈side p a ∧ (e (e.symm (e x))).2∈side q a) ∧
      ((e (e.symm (e x))).1+(h : ZMod p)∈side p b ∧ (e (e.symm (e x))).2+(h : ZMod q)∈side q b) ↔ _
    rw [e.apply_symm_apply]
    exact and_and_and_comm
  simpa only [cross,card_map,card_product] using congrArg Finset.card eqn

private theorem root_pair {p : ℕ} [Fact p.Prime] (odd : p≠2) {a : ℤ}
    (s : legendreSym p a=1) : (roots p a).card=2 := by
  have eqn := roots_count odd a
  rw [s] at eqn
  omega

private theorem not_four {p : ℕ} [hp : Fact p.Prime] (odd : p≠2) : ¬ p∣4 := by
  intro dv
  have two : p∣2 := hp.out.dvd_of_dvd_pow (show p∣2^2 from dv)
  exact odd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp two)

private theorem nz_of_sign {p : ℕ} [Fact p.Prime] {a : ℤ} (h : legendreSym p a≠0) :
    (a : ZMod p)≠0 := fun z => h ((legendreSym.eq_zero_iff p a).mpr z)

/-- For two negative-Jacobi units, their product is a square exactly when
their local signs agree at either chosen prime. -/
theorem square_product_iff {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) {a b : ℤ} (na : jacobiSym a (p*q)= -1) (nb : jacobiSym b (p*q)= -1) :
    IsSquare ((a*b : ℤ) : ZMod (p*q)) ↔ legendreSym p a=legendreSym p b := by
  rw [PrimeFactors.QuarticSlopeBit.square_crt ((Nat.coprime_primes hp.out hq.out).mpr diff)]
  have nz {r : ℕ} [Fact r.Prime] (x : legendreSym r a≠0) (y : legendreSym r b≠0) :
      ((a*b : ℤ) : ZMod r)≠0 := by push_cast; exact mul_ne_zero (nz_of_sign x) (nz_of_sign y)
  rcases opposite na with A|A <;> rcases opposite nb with B|B
  all_goals
    rw [←legendreSym.eq_one_iff p (nz (by rw [A.1]; decide) (by rw [B.1]; decide)),
      ←legendreSym.eq_one_iff q (nz (by rw [A.2]; decide) (by rw [B.2]; decide)),
      legendreSym.mul,legendreSym.mul,A.1,A.2,B.1,B.2]
    decide

/-- For any lag the count is four precisely when the product of the targets
is a quadratic nonresidue modulo N. -/
theorem four_iff {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a b : ℤ}
    (na : jacobiSym a (p*q)= -1) (nb : jacobiSym b (p*q)= -1) (h : ℤ) :
    cross (p*q) a b h=4 ↔ ¬IsSquare ((a*b : ℤ) : ZMod (p*q)) := by
  have total := factor_count ((Nat.coprime_primes hp.out hq.out).mpr diff) na nb h
  rw [square_product_iff diff na nb]
  rcases opposite na with A|A <;> rcases opposite nb with B|B
  all_goals
    simp [side,A.1,A.2,B.1,B.2] at total
    rw [A.1,B.1]
    norm_num
  · intro eqn
    exact not_four oq (eqn ▸ total ▸ dvd_mul_left ..)
  · rw [total,root_pair op A.1,root_pair oq B.2]
  · rw [total,root_pair op B.1,root_pair oq A.2]
  · intro eqn
    exact not_four op (eqn ▸ total ▸ dvd_mul_right ..)

theorem diagonal (n : ℕ) [NeZero n] (a h : ℤ) :
    cross n a a h=overlap n a h := by
  unfold cross cut overlap
  congr 1
  ext x
  simp only [mem_filter]

private theorem square_twist {R : Type*} [CommRing R] (u : Rˣ) (z : R) :
    IsSquare ((u:R)*((u:R)*z)) ↔ IsSquare z := by
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨(↑u⁻¹:R)*y,?_⟩
    calc
      z = ((↑u⁻¹:R)*(u:R))^2*z := by simp
      _ = (↑u⁻¹:R)^2*((u:R)*((u:R)*z)) := by ring
      _ = _ := by rw [hy]; ring
  · rintro ⟨y,hy⟩
    exact ⟨(u:R)*y,by rw [hy]; ring⟩

/-- A single anchor of negative Jacobi sign turns an arbitrary Jacobi-positive
input into two targets. Their intersection has four starts precisely when
the given input is a nonsquare, for any chosen lag. -/
theorem test_square {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a z : ℤ}
    (na : jacobiSym a (p*q)= -1) (pos : jacobiSym z (p*q)=1) (h : ℤ) :
    cross (p*q) a (a*z) h=4 ↔ ¬IsSquare (z : ZMod (p*q)) := by
  have nb : jacobiSym (a*z) (p*q)= -1 := by rw [jacobiSym.mul_left,na,pos,mul_one]
  have cop := (Nat.coprime_primes hp.out hq.out).mpr diff
  have unit : IsUnit (a : ZMod (p*q)) := by
    rw [←isUnit_map_iff (ZMod.chineseRemainder cop),map_intCast,Prod.isUnit_iff]
    rcases opposite na with A|A <;>
      exact ⟨(nz_of_sign (by rw [A.1]; decide)).isUnit,(nz_of_sign (by rw [A.2]; decide)).isUnit⟩
  obtain ⟨u,hu⟩ := unit
  rw [four_iff diff op oq na nb,Int.cast_mul,Int.cast_mul,←hu,square_twist]

/-- All four orientations use one hidden bit per target. Flags for one
anchor and two targets determine the flag between the two targets. -/
theorem triangle {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a b c : ℤ}
    (na : jacobiSym a (p*q)= -1) (nb : jacobiSym b (p*q)= -1)
    (nc : jacobiSym c (p*q)= -1) (i j k : ℤ) :
    cross (p*q) b c k=4 ↔ ¬(cross (p*q) a b i=4 ↔ cross (p*q) a c j=4) := by
  rw [four_iff diff op oq nb nc,four_iff diff op oq na nb,four_iff diff op oq na nc,
    square_product_iff diff nb nc,square_product_iff diff na nb,square_product_iff diff na nc]
  rcases opposite na with A|A <;> rcases opposite nb with B|B <;> rcases opposite nc with C|C <;>
    rw [A.1,B.1,C.1] <;> decide

end PrimeFactors.CircleMarkCrossTargets
