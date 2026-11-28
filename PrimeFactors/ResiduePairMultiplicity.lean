import PrimeFactors.AdmissibleSumRealization

/-! Count distinct integer products realizing one specified product residue
and one specified sum residue, given prime supplies in the factor interval.
The two local factor residues can coincide. -/

namespace PrimeFactors.ResiduePairMultiplicity

open Finset AdmissibleSumRealization

noncomputable def primes (m L H a : ℕ) : Finset ℕ :=
  (Ico L H).filter fun p => p.Prime ∧ p%m=a

theorem mem_primes {m L H a p : ℕ} : p ∈ primes m L H a ↔
    L ≤ p ∧ p < H ∧ p.Prime ∧ p%m=a := by
  simp only [primes,mem_filter,mem_Ico,and_assoc]

def ManyRepresentatives (m L H M : ℕ) : Prop :=
  ∀ a < m, a.Coprime m → M ≤ (primes m L H a).card

theorem two_of_many {m L H M : ℕ} (supply : ManyRepresentatives m L H M) (size : 2 ≤ M) :
    TwoRepresentatives m L H := by
  intro a ha cop
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by omega : 1<M) (supply a ha cop))
  obtain ⟨pl,ph,P,pa⟩ := mem_primes.mp hp
  obtain ⟨ql,qh,Q,qa⟩ := mem_primes.mp hq
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact ⟨p,q,pl,lt,qh,P,Q,pa,qa⟩
  · exact ⟨q,p,ql,gt,ph,Q,P,qa,pa⟩

/-- Distinct integers rather than ordered factorizations. -/
noncomputable def products {m : ℕ} (L H : ℕ) (r s : ZMod m) : Finset ℕ := by
  classical
  exact (range (H^2)).filter fun N => ∃ p q : ℕ, L ≤ p ∧ p < q ∧ q < H ∧
    p.Prime ∧ q.Prime ∧ N=p*q ∧ ((p*q : ℕ) : ZMod m)=r ∧ ((p+q : ℕ) : ZMod m)=s

theorem mem_products {m L H N : ℕ} {r s : ZMod m} :
    N ∈ products L H r s ↔ ∃ p q : ℕ, L ≤ p ∧ p < q ∧ q < H ∧ p.Prime ∧ q.Prime ∧
      N=p*q ∧ ((p*q : ℕ) : ZMod m)=r ∧ ((p+q : ℕ) : ZMod m)=s := by
  classical
  simp only [products,mem_filter,mem_range]
  apply and_iff_right_of_imp
  rintro ⟨p,q,_,lt,hi,_,_,rfl,_,_⟩
  simpa only [pow_two] using Nat.mul_lt_mul_of_lt_of_lt (lt.trans hi) hi

private theorem member {m L H p q : ℕ} {x y : ZMod m}
    (pl : L≤p) (ph : p<H) (ql : L≤q) (qh : q<H) (P : p.Prime) (Q : q.Prime)
    (px : (p : ZMod m)=x) (qy : (q : ZMod m)=y) (ne : p ≠ q) :
    p*q ∈ products L H (x*y) (x+y) := by
  subst x y
  apply mem_products.mpr
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact ⟨p,q,pl,lt,qh,P,Q,rfl,Nat.cast_mul ..,Nat.cast_add ..⟩
  · exact ⟨q,p,ql,gt,ph,Q,P,mul_comm ..,by rw [Nat.mul_comm,Nat.cast_mul],
      by rw [Nat.add_comm,Nat.cast_add]⟩

/-- Choose half the required supply in the first local class and remove
those primes from the second class. The remaining disjoint prime sets give
different integer products, even if the two residue roots were equal. -/
theorem multiplicity {m L H M : ℕ} [NeZero m] (supply : ManyRepresentatives m L H M)
    {r s : ZMod m} (unit : IsUnit r) (pass : AdmissibleSum r s) :
    (M/2)*(M-M/2) ≤ (products L H r s).card := by
  classical
  obtain ⟨x,y,rfl,rfl⟩ := pass
  obtain ⟨ux,uy⟩ := (Commute.all x y).isUnit_mul_iff.mp unit
  have available (z : ZMod m) (u : IsUnit z) : M ≤ (primes m L H z.val).card :=
    supply z.val z.val_lt ((ZMod.isUnit_iff_coprime _ _).mp
      (by simpa only [ZMod.natCast_zmod_val] using u))
  obtain ⟨A,sub,sz⟩ := exists_subset_card_eq ((Nat.div_le_self M 2).trans (available x ux))
  let B := primes m L H y.val \ A
  have infoA {p} (h : p ∈ A) := mem_primes.mp (sub h)
  have infoB {q} (h : q ∈ B) := mem_primes.mp (mem_sdiff.mp h).1
  have ne {p q} (hp : p ∈ A) (hq : q ∈ B) : p ≠ q := by
    rintro rfl
    exact (mem_sdiff.mp hq).2 hp
  let f (v : ℕ × ℕ) := v.1*v.2
  have inj : Set.InjOn f (↑(A ×ˢ B) : Set (ℕ × ℕ)) := by
    rintro ⟨p,q⟩ hpq ⟨u,v⟩ huv eq
    obtain ⟨pa,qb⟩ := mem_product.mp hpq
    obtain ⟨ua,vb⟩ := mem_product.mp huv
    change p*q=u*v at eq
    have P := (infoA pa).2.2.1
    have U := (infoA ua).2.2.1
    have V := (infoB vb).2.2.1
    have div : p ∣ u*v := eq ▸ dvd_mul_right p q
    have pu : p=u := (P.dvd_mul.mp div).elim ((Nat.prime_dvd_prime_iff_eq P U).mp)
      (fun d => False.elim (ne pa vb ((Nat.prime_dvd_prime_iff_eq P V).mp d)))
    subst u
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left P.pos eq)
  have into : (A ×ˢ B).image f ⊆ products L H (x*y) (x+y) := by
    intro z hz
    obtain ⟨⟨p,q⟩,hpq,rfl⟩ := mem_image.mp hz
    obtain ⟨pa,qb⟩ := mem_product.mp hpq
    obtain ⟨pl,ph,P,px⟩ := infoA pa
    obtain ⟨ql,qh,Q,qy⟩ := infoB qb
    exact member pl ph ql qh P Q (ZMod.val_injective m (by simpa only [ZMod.val_natCast] using px))
      (ZMod.val_injective m (by simpa only [ZMod.val_natCast] using qy)) (ne pa qb)
  have remaining : M-M/2 ≤ B.card := by
    have loss : (primes m L H y.val).card ≤ B.card + A.card := card_le_card_sdiff_add_card
    have enough := available y uy
    omega
  calc
    _ ≤ A.card*B.card := by rw [sz]; exact Nat.mul_le_mul_left _ remaining
    _ = _ := (card_product A B).symm.trans (card_image_of_injOn inj).symm
    _ ≤ _ := card_le_card into

end PrimeFactors.ResiduePairMultiplicity
