import PrimeFactors.QuarticLocalSumBits
import PrimeFactors.QuarticSlopeBit
import PrimeFactors.ReciprocalSumCharacter

/-! A supplied square-existence answer for −3 determines the sign of
the actual prime sum modulo nine when the product is one modulo three. -/
namespace PrimeFactors.TernarySumSign

open private PrimeFactors.ReciprocalSumCharacter.reciprocity from PrimeFactors.ReciprocalSumCharacter
open private PrimeFactors.QuarticSlopeBit.square_crt from PrimeFactors.QuarticSlopeBit

def Bit (n : ℕ) : Prop := IsSquare ((-3:ℤ):ZMod n)

private theorem reduce_symbol {n : ℕ} (odd : Odd n) :
    jacobiSym ((n:ℤ)%3) 3=jacobiSym (-3) n := by
  have qr := PrimeFactors.ReciprocalSumCharacter.reciprocity (d:=3) (by decide) odd
  change jacobiSym (n:ℤ) 3=jacobiSym (-3) n at qr
  rw [jacobiSym.mod_left (n:ℤ) 3] at qr
  exact qr

/-- On the branch where the bit is informative, its public Jacobi symbol is always one. -/
theorem public_symbol {n : ℕ} (odd : Odd n) (gate : n%3=1) : jacobiSym (-3) n=1 := by
  rw [←reduce_symbol odd,show (n:ℤ)%3=1 by exact_mod_cast gate,jacobiSym.one_left]

/-- Quadratic reciprocity identifies the local criterion away from 2 and 3. -/
theorem prime_bit {p : ℕ} (pp : p.Prime) (odd : Odd p) (other : p≠3) :
    Bit p ↔ p%3=1 := by
  letI : Fact p.Prime := ⟨pp⟩
  have nonzero : p%3≠0 := by
    intro h
    exact other ((Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp (Nat.dvd_of_mod_eq_zero h)).symm
  have qr := reduce_symbol odd
  by_cases yes : p%3=1
  · have cast : (p:ℤ)%3=1 := by exact_mod_cast yes
    rw [cast,jacobiSym.one_left] at qr
    exact iff_of_true (ZMod.isSquare_of_jacobiSym_eq_one qr.symm) yes
  · have cast : (p:ℤ)%3=2 := by exact_mod_cast (show p%3=2 by omega)
    rw [cast,show jacobiSym 2 3= -1 by norm_num] at qr
    exact iff_of_false (ZMod.nonsquare_of_jacobiSym_eq_neg_one qr.symm) yes

/-- Both factors must belong to the positive local class. -/
theorem bit_iff {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (po : Odd p) (qo : Odd q) (p3 : p≠3) (q3 : q≠3) :
    Bit (p*q) ↔ p%3=1 ∧ q%3=1 := by
  exact (PrimeFactors.QuarticSlopeBit.square_crt ((Nat.coprime_primes pp qp).mpr ne) (-3)).trans
    (and_congr (prime_bit pp po p3) (prime_bit qp qo q3))

private theorem residue9 (p q : ℕ) (gate : (p*q)%3=1) :
    ((p%3=1 ∧ q%3=1) ↔ (p+q)%9=(p*q+1)%9) ∧
    (¬(p%3=1 ∧ q%3=1) ↔ ((p+q)%9+(p*q+1)%9)%9=0) := by
  have table : ∀ a b : Fin 9, (a.val*b.val)%3=1 →
      ((a.val%3=1 ∧ b.val%3=1) ↔ (a.val+b.val)%9=(a.val*b.val+1)%9) ∧
      (¬(a.val%3=1 ∧ b.val%3=1) ↔ ((a.val+b.val)%9+(a.val*b.val+1)%9)%9=0) := by decide +kernel
  have product := (Nat.mod_modEq p 9).mul (Nat.mod_modEq q 9)
  have total : (p%9+q%9)%9=(p+q)%9 := (Nat.mod_modEq p 9).add (Nat.mod_modEq q 9)
  have next : ((p%9)*(q%9)+1)%9=(p*q+1)%9 := product.add_right 1
  have three : (p%9*(q%9))%3=(p*q)%3 := product.of_dvd (by decide)
  have row := table ⟨p%9,Nat.mod_lt _ (by decide)⟩ ⟨q%9,Nat.mod_lt _ (by decide)⟩ (three.trans gate)
  simpa only [Nat.mod_mod_of_dvd _ (by decide : 3∣9),total,next] using row

/-- The supplied bit selects between two distinct residue classes of the sum.
The second equivalence writes the negative sign without natural subtraction. -/
theorem sign9 {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (po : Odd p) (qo : Odd q) (gate : (p*q)%3=1) :
    (Bit (p*q) ↔ (p+q)%9=(p*q+1)%9) ∧
    (¬Bit (p*q) ↔ ((p+q:ℕ):ℤ)%9=(-((p*q+1:ℕ):ℤ))%9) := by
  have notthree (h : 3∣p*q) := (show (p*q)%3≠0 by omega) (Nat.mod_eq_zero_of_dvd h)
  have p3 : p≠3 := fun h => notthree (h ▸ dvd_mul_right p q)
  have q3 : q≠3 := fun h => notthree (h ▸ dvd_mul_left q p)
  rw [bit_iff pp qp ne po qo p3 q3]
  obtain ⟨plus,minus⟩ := residue9 p q gate
  refine ⟨plus,minus.trans ?_⟩
  have a : (((p+q)%9:ℕ):ℤ)=((p+q:ℕ):ℤ)%9 := by exact_mod_cast Int.natCast_mod (p+q) 9
  have b : (((p*q+1)%9:ℕ):ℤ)=((p*q+1:ℕ):ℤ)%9 := by exact_mod_cast Int.natCast_mod (p*q+1) 9
  omega

/-- Both modular factors are in the specified class modulo three. -/
def At27 (r n s : ℤ) : Prop := ∃ a b : ℤ, a%3=r ∧ b%3=r ∧
  a*b ≡ n [ZMOD 27] ∧ a+b ≡ s [ZMOD 27]

/-- After choosing the positive sign, two classes occur modulo 27.
The second depends on the product modulo nine. -/
def Menu (n s : ℤ) : Prop :=
  s%27=(n+1)%27 ∨ s%27=(n+(if n%9=1 then 10 else -8))%27

private theorem table27 : ∀ a b : Fin 27, (a.val:ℤ)%3=1 → (b.val:ℤ)%3=1 →
    Menu (a.val*b.val) (a.val+b.val) := by
  unfold Menu
  decide +kernel

theorem positive27 {n s : ℤ} (gate : n%3=1) : At27 1 n s ↔ Menu n s := by
  constructor
  · rintro ⟨a,b,ha,hb,ab,total⟩
    let u (z : ℤ) : Fin 27 := ⟨(z%27).toNat,by omega⟩
    have val (z : ℤ) : ((u z).val:ℤ)=z%27 := Int.toNat_of_nonneg (by omega)
    have row := table27 (u a) (u b) (by rw [val]; omega) (by rw [val]; omega)
    unfold Menu at row ⊢
    simp only [val] at row
    have prod := (((Int.mod_modEq a 27).mul (Int.mod_modEq b 27)).trans ab)
    have sum := (((Int.mod_modEq a 27).add (Int.mod_modEq b 27)).trans total)
    have nine := prod.of_dvd (show (9:ℤ)∣27 by decide)
    change (a%27*(b%27))%9=n%9 at nine
    rw [nine] at row
    change (a%27+b%27)%27=s%27 at sum
    rw [sum] at row
    exact row.imp (fun h => Eq.trans h (prod.add_right 1))
      (fun h => Eq.trans h (prod.add_right _))
  · rintro (first|second)
    · exact ⟨1,n,by decide,gate,by simp,by change (1+n)%27=s%27; omega⟩
    · by_cases four : n%9=4
      · refine ⟨7,4*n,by decide,by omega,?_,?_⟩
        · change (7*(4*n))%27=n%27
          omega
        · change (7+4*n)%27=s%27
          simp only [if_neg (show n%9≠1 by omega)] at second
          omega
      · refine ⟨4,7*n,by decide,by omega,?_,?_⟩
        · change (4*(7*n))%27=n%27
          omega
        · change (4+7*n)%27=s%27
          split_ifs at second <;> omega

/-- Negating both factors implements the negative sign, preserving product. -/
theorem negative27 {n s : ℤ} (gate : n%3=1) : At27 2 n s ↔ Menu n (-s) := by
  rw [←positive27 gate]
  constructor <;> rintro ⟨a,b,ac,bc,prod,total⟩
  · exact ⟨-a,-b,by omega,by omega,by simpa using prod,
      by simpa only [neg_add_rev,add_comm] using total.neg⟩
  · exact ⟨-a,-b,by omega,by omega,by simpa using prod,
      by simpa only [neg_add_rev,add_comm,neg_neg] using total.neg⟩

theorem distinct_classes (n : ℤ) :
    (n+1)%27≠(n+(if n%9=1 then 10 else -8))%27 := by split_ifs <;> omega

/-- The actual sum lies in the positive or negative two-class menu
according to the supplied bit. -/
theorem sum27 {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (po : Odd p) (qo : Odd q) (gate : (p*q)%3=1) :
    (Bit (p*q) → Menu ((p:ℤ)*q) (p+q)) ∧ (¬Bit (p*q) → Menu ((p:ℤ)*q) (-(p+q))) := by
  have classTable : ∀ a b : Fin 3, (a.val*b.val)%3=1 →
      (a.val=1 ∧ b.val=1) ∨ (a.val=2 ∧ b.val=2) := by decide +kernel
  have prod : (p%3*(q%3))%3=(p*q)%3 := (Nat.mod_modEq p 3).mul (Nat.mod_modEq q 3)
  have splitClass := classTable ⟨p%3,Nat.mod_lt _ (by decide)⟩ ⟨q%3,Nat.mod_lt _ (by decide)⟩ (prod.trans gate)
  have notthree (h : 3∣p*q) := (show (p*q)%3≠0 by omega) (Nat.mod_eq_zero_of_dvd h)
  have criterion := bit_iff pp qp ne po qo (fun h => notthree (h ▸ dvd_mul_right p q))
    (fun h => notthree (h ▸ dvd_mul_left q p))
  have good : ((p:ℤ)*q)%3=1 := by exact_mod_cast gate
  constructor
  · intro yes
    obtain ⟨a,b⟩ := criterion.mp yes
    exact (positive27 good).mp ⟨p,q,by exact_mod_cast a,by exact_mod_cast b,Int.ModEq.refl _,Int.ModEq.refl _⟩
  · intro no
    obtain ⟨a,b⟩ := splitClass.resolve_left (fun h => no (criterion.mpr h))
    exact (negative27 good).mp ⟨p,q,by exact_mod_cast a,by exact_mod_cast b,Int.ModEq.refl _,Int.ModEq.refl _⟩

/-- The four examples are chosen 20-bit products in the same residue
class modulo 432. They realize every combination of the two answers. -/
theorem independent_examples :
    ∀ row∈([(563,983,false,false),(601,877,true,true),
      (641,1013,true,false),(739,919,false,true)] : List (ℕ×ℕ×Bool×Bool)),
    match row with
    | (p,q,x,y) =>
      p.Prime ∧ q.Prime ∧ (2^9≤p ∧ p<q ∧ q<2^10 ∧ 2^19≤p*q ∧ p*q<2^20 ∧
      (p*q)%432=37) ∧ (QuarticLocalClassification.Tests (p*q) ↔ x=true) ∧
      (Bit (p*q) ↔ y=true) := by
  have check (p q : ℕ) (x y : Bool) (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
      (po : Odd p) (qo : Odd q) (p3 : p≠3) (q3 : q≠3)
      (bounds : 2^9≤p ∧ p<q ∧ q<2^10 ∧ 2^19≤p*q ∧ p*q<2^20 ∧ (p*q)%432=37)
      (xval : (p%4=1 ∧ q%4=1 ∧ ((p*q)%16=1 ∨ (p*q)%16=5)) ↔ x=true)
      (yval : (p%3=1 ∧ q%3=1) ↔ y=true) :=
    And.intro pp (And.intro qp (And.intro bounds (And.intro
      ((QuarticLocalClassification.semiprime pp qp po qo).trans xval)
      ((bit_iff pp qp ne po qo p3 q3).trans yval))))
  intro row h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl <;> apply check <;> decide +kernel

end PrimeFactors.TernarySumSign
