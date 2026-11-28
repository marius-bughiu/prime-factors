import PrimeFactors.TransposedRadixProducts

/-! Recovering the product of two exchanged blocks from a quotient and one
ordinary remainder. The argument works in every radix, for any digit parities. -/
namespace PrimeFactors.TransposedBlockQuotient

open TransposedRadixProducts (factors)

/-- Largest nonnegative representative of N modulo B up to the coarse quotient
when that quotient is at least N modulo B. -/
def digitProduct (B N : ℕ) : ℕ :=
  N%B+B*((N/(B+1)^2-N%B)/B)

def digitGapSquare (B N : ℕ) : ℕ :=
  (N-(B+1)^2*digitProduct B N)/B

def readDigits (B N : ℕ) : ℕ×ℕ :=
  let d₂ := digitGapSquare B N
  let d := d₂.sqrt
  let s := (d₂+4*digitProduct B N).sqrt
  ((s-d)/2,(s+d)/2)

/-- Completing the coefficient of ab at (B+1)² leaves the nonnegative
correction B(b−a)², including when the base-B product has carries. -/
theorem identity {B a b : ℕ} (ab : a≤b) :
    (factors B a b).1*(factors B a b).2=(B+1)^2*(a*b)+B*(b-a)^2 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ab
  simp only [factors,Nat.add_sub_cancel_left]
  ring

private theorem product_mod (B a b : ℕ) :
    ((factors B a b).1*(factors B a b).2)%B=(a*b)%B := by
  simp only [factors,Nat.mul_mod,Nat.mul_add_mod_self_left,Nat.mod_mod]
  rw [Nat.mul_comm (b%B%B)]

private theorem recover_residue {P B T : ℕ} (pos : 0<B) (lo : P≤T) (hi : T<P+B) :
    P%B+B*((T-P%B)/B)=P := by
  let K := T-P
  have tk : T=P+K := by dsimp [K]; omega
  have kb : K<B := by dsimp [K]; omega
  have parts := Nat.mod_add_div P B
  have minus : T-P%B=B*(P/B)+K := by omega
  rw [minus,Nat.mul_add_div pos,Nat.div_eq_of_lt kb,Nat.add_zero]
  exact parts

theorem digit_product {B a b N : ℕ} (ab : a≤b) (top : b<B)
    (given : (factors B a b).1*(factors B a b).2=N) : digitProduct B N=a*b := by
  have pos : 0<B := by omega
  have m : 0<(B+1)^2 := by positivity
  have diff : b-a<B+1 := by omega
  have fine : B*(b-a)^2<B*(B+1)^2 := Nat.mul_lt_mul_of_pos_left
    (Nat.pow_lt_pow_left diff (by decide : 2≠0)) pos
  have eqn := given.symm.trans (identity ab)
  have quo : N/(B+1)^2=a*b+B*(b-a)^2/(B+1)^2 := by
    rw [eqn,Nat.mul_add_div m]
  have err := (Nat.div_lt_iff_lt_mul m).mpr fine
  have suffix : N%B=(a*b)%B := given ▸ product_mod B a b
  have bounds : a*b≤N/(B+1)^2 ∧ N/(B+1)^2<a*b+B := by
    rw [quo]
    exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left err _⟩
  unfold digitProduct
  rw [suffix]
  exact recover_residue pos bounds.1 bounds.2

theorem gap_square {B a b N : ℕ} (ab : a≤b) (top : b<B)
    (given : (factors B a b).1*(factors B a b).2=N) : digitGapSquare B N=(b-a)^2 := by
  have pos : 0<B := by omega
  rw [digitGapSquare,digit_product ab top given,←given,identity ab,
    Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ pos]

theorem read_digits {B a b N : ℕ} (ab : a≤b) (top : b<B)
    (given : (factors B a b).1*(factors B a b).2=N) : readDigits B N=(a,b) := by
  rw [readDigits,gap_square ab top given,digit_product ab top given]
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ab
  simp only [Nat.add_sub_cancel_left,Nat.sqrt_eq']
  rw [show d^2+4*(a*(a+d))=(a+(a+d))^2 by ring,Nat.sqrt_eq']
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

/-- Reassemble both words and check the exact product. This also rejects
rounded square roots or truncated subtraction on unrelated inputs. -/
def recognize (B N : ℕ) : Option (ℕ×ℕ) :=
  let digits := readDigits B N
  let pq := factors B digits.1 digits.2
  if 0<digits.1 ∧ digits.1<digits.2 ∧ digits.2<B ∧ pq.1*pq.2=N then some pq else none

theorem complete {B N a b : ℕ} (pos : 0<a) (ab : a<b) (top : b<B)
    (given : (factors B a b).1*(factors B a b).2=N) :
    recognize B N=some (factors B a b) := by
  simp only [recognize,read_digits ab.le top given,pos,ab,top,given,and_self,if_true]

theorem recognizes_iff {B N p q : ℕ} :
    recognize B N=some (p,q) ↔
      ∃ a b, 0<a ∧ a<b ∧ b<B ∧ factors B a b=(p,q) ∧ p*q=N := by
  constructor
  · intro hit
    unfold recognize at hit
    dsimp only at hit
    split at hit
    · rename_i h
      have eq := Option.some.inj hit
      exact ⟨_,_,h.1,h.2.1,h.2.2.1,eq,(congrArg (fun z : ℕ×ℕ => z.1*z.2) eq).symm.trans h.2.2.2⟩
    · contradiction
  · rintro ⟨a,b,pos,ab,top,pair,given⟩
    rw [←pair]
    apply complete pos ab top
    rw [pair]
    exact given

/-- An odd radix with genuine carries. The quotient exceeds the true
digit product by five. The remainder singles out 510 and the factors follow. -/
theorem odd_radix_example :
    527479/(31+1)^2=515 ∧ 527479%31=14 ∧ digitProduct 31 527479=510 ∧
    digitGapSquare 31 527479=169 ∧ readDigits 31 527479=(17,30) ∧
    factors 31 17 30=(557,947) ∧ 557*947=527479 ∧ Nat.Prime 557 ∧ Nat.Prime 947 := by
  refine ⟨by decide,by decide,?_,?_,?_,by decide,by decide,by norm_num,by norm_num⟩
  · exact digit_product (a:=17) (b:=30) (by decide) (by decide) (by decide)
  · exact gap_square (a:=17) (b:=30) (by decide) (by decide) (by decide)
  · exact read_digits (by decide) (by decide) (by decide)

end PrimeFactors.TransposedBlockQuotient
