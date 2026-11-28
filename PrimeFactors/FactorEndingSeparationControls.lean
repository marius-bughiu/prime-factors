import PrimeFactors.Certificate
import PrimeFactors.FactorEndingSeparation

/-! Three pairs of selected 20-bit products. The products in each pair
agree modulo 4096 and their sums agree until the last distinguishing
bit. Only the product remainder and the supplied sum remainder enter
the assertion that determines both five-bit factor endings. -/
namespace PrimeFactors.FactorEndingSeparationControls

open FactorEndingSeparation

/-- Independent primality and multiplication receipts for all six inputs. -/
theorem certificates :
    ExactFactorization 545339 [619,881] ∧ ExactFactorization 578107 [673,859] ∧
    ExactFactorization 539477 [643,839] ∧ ExactFactorization 584533 [659,887] ∧
    ExactFactorization 601049 [619,971] ∧ ExactFactorization 842713 [827,1019] := by
  norm_num [ExactFactorization]

def Reading (p q productSuffix sum depth sumSuffix first second : ℕ) : Prop :=
  2^9≤p ∧ p<q ∧ q<2^10 ∧ 2^19≤p*q ∧ p*q<2^20 ∧
  (p*q)%4096=productSuffix ∧ p+q=sum ∧ sum%2^depth=sumSuffix ∧
  p%32=first ∧ q%32=second

theorem readings :
    Reading 619 881 571 1500 6 28 11 17 ∧ Reading 673 859 571 1532 6 60 1 27 ∧
    Reading 643 839 2901 1482 7 74 3 7 ∧ Reading 659 887 2901 1546 7 10 19 23 ∧
    Reading 619 971 3033 1590 9 54 11 11 ∧ Reading 827 1019 3033 1846 9 310 27 27 := by
  unfold Reading
  decide +kernel

/-- At the preceding precisions the true sums of the matched products
have the same remainders 28, 10 and 54, respectively. -/
theorem shared_before :
    1500%(2:ℕ)^5=28 ∧ 1532%(2:ℕ)^5=28 ∧
    1482%(2:ℕ)^6=10 ∧ 1546%(2:ℕ)^6=10 ∧
    1590%(2:ℕ)^8=54 ∧ 1846%(2:ℕ)^8=54 := by decide +kernel

private theorem different {r e : ℕ} (p q c d : ℤ)
    (left : p*q ≡ (r:ℤ) [ZMOD (2:ℤ)^e]) (right : c*d ≡ (r:ℤ) [ZMOD (2:ℤ)^e])
    (same : p+q ≡ c+d [ZMOD (2:ℤ)^e])
    (distinct : ¬(p ≡ c [ZMOD 32] ∨ p ≡ d [ZMOD 32])) : ¬Separates r 5 e :=
  fun h => distinct (h p q c d left right same)

/-- Failure of the lower precision is witnessed by the actual prime pairs. -/
theorem ambiguous :
    ¬Separates 571 5 5 ∧ ¬Separates 2901 5 6 ∧ ¬Separates 3033 5 8 := by
  refine ⟨different 619 881 673 859 ?_ ?_ ?_ ?_,
    different 643 839 659 887 ?_ ?_ ?_ ?_,different 619 971 827 1019 ?_ ?_ ?_ ?_⟩ <;> decide +kernel

/-- Every modular pair consistent with the observations has these two
factor endings, in either order. -/
def Determines (r e : ℕ) (s i j : ℤ) : Prop :=
  ∀ x y : ℤ, x*y ≡ (r:ℤ) [ZMOD (2:ℤ)^e] → x+y ≡ s [ZMOD (2:ℤ)^e] →
    (x ≡ i [ZMOD 32] ∧ y ≡ j [ZMOD 32]) ∨ (x ≡ j [ZMOD 32] ∧ y ≡ i [ZMOD 32])

private theorem determine {r e : ℕ} {s i j : ℤ} (p q : ℤ)
    (sharp : depth r 5=e) (enough : 5≤e)
    (prod : p*q ≡ (r:ℤ) [ZMOD (2:ℤ)^e]) (sum : p+q ≡ s [ZMOD (2:ℤ)^e])
    (first : p ≡ i [ZMOD 32]) (second : q ≡ j [ZMOD 32]) : Determines r e s i j := by
  intro x y xy obs
  have sep := sharp ▸ (at_depth_all (N:=r) (by decide : 4≤5))
  rcases same_or_swapped sep enough xy prod (obs.trans sum.symm) with h|h
  · exact Or.inl ⟨h.1.trans first,h.2.trans second⟩
  · exact Or.inr ⟨h.1.trans second,h.2.trans first⟩

theorem determinations :
    Determines 571 6 28 11 17 ∧ Determines 571 6 60 1 27 ∧
    Determines 2901 7 74 3 7 ∧ Determines 2901 7 10 19 23 ∧
    Determines 3033 9 54 11 11 ∧ Determines 3033 9 310 27 27 := by
  refine ⟨determine 619 881 ?_ ?_ ?_ ?_ ?_ ?_,determine 673 859 ?_ ?_ ?_ ?_ ?_ ?_,
    determine 643 839 ?_ ?_ ?_ ?_ ?_ ?_,determine 659 887 ?_ ?_ ?_ ?_ ?_ ?_,
    determine 619 971 ?_ ?_ ?_ ?_ ?_ ?_,determine 827 1019 ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> decide +kernel

end PrimeFactors.FactorEndingSeparationControls
