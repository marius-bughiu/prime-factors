import PrimeFactors.BinomialDivisorWindow
import PrimeFactors.HigherWindowCertificate
import Mathlib.LinearAlgebra.Lagrange

namespace PrimeFactors.BinomialWindowCertificate

open Polynomial Finset

/-- Compare the two supplied rows on k+1 distinct small integer arguments. -/
def sampleChecks {k : ℕ} (v w : Fin (k+1) → ℤ) : Prop :=
  ∀ x : Fin (k+1), (k.factorial:ℤ)*(∑ i, v i*(x.val.choose i.val:ℤ)) =
    ∑ i, w i*(x.val:ℤ)^i.val

theorem same_polynomial {k : ℕ} {v w : Fin (k+1) → ℤ} (samples : sampleChecks v w) :
    BinomialDivisorWindow.cleared k v=ofFn (k+1) w := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (v:=fun i : Fin (k+1) => (i.val:ℤ)) univ
  · intro a _ b _ eq
    change (a.val:ℤ)=(b.val:ℤ) at eq
    exact Fin.ext (by exact_mod_cast eq)
  · rw [card_univ,Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (BinomialDivisorWindow.degree_bound k v))
  · rw [card_univ,Fintype.card_fin]
    exact ofFn_degree_lt w
  · intro i _
    rw [BinomialDivisorWindow.eval_cleared,HigherDivisorWindow.eval_coeff]
    exact samples i

/-- Recursion runs on the small degree even when the span has hundreds of bits. -/
noncomputable def height {k : ℕ} (v : Fin (k+1) → ℤ) (H : ℕ) : ℤ :=
  ∑ i, |v i| * (Nat.fast_choose H i.val:ℤ)

/-- An integral binomial row, its independent ordinary evaluation table, and a
modular absence of roots exclude every natural divisor in the whole closed interval. -/
theorem excludes {k n first span depth modulus : ℕ} {v w : Fin (k+1) → ℤ} {t h : ℤ}
    (hn : n%2=1) (oddFirst : first%2=1) (anchor : (n:ℤ)∣(first:ℤ)+2*t)
    (gcd : n.Coprime k.factorial) (samples : sampleChecks v w)
    (jets : HigherWindowCertificate.jetChecks w n depth t) (measured : height v span=h)
    (small : h<(first:ℤ)^depth) (hm : 0<modulus)
    (miss : HigherWindowCertificate.rootChecks w modulus)
    (d : ℕ) (lo : first≤d) (hi : d≤first+2*span) : ¬ d∣n := by
  intro hd
  have odd := Nat.odd_iff.mpr hn
  have unit : IsCoprime (2:ℤ) (n:ℤ) := (Nat.coprime_two_left.mpr odd).isCoprime
  obtain ⟨q,hq⟩ := hd
  have dz : (d:ℤ)∣(n:ℤ) := by exact_mod_cast (show d∣n from ⟨q,hq⟩)
  obtain ⟨a,ha⟩ := (Nat.odd_mul.mp (hq ▸ odd)).1
  let x := (d-first)/2
  have pos : (d:ℤ)=(first:ℤ)+2*(x:ℤ) := by dsimp only [x]; omega
  have near : x≤span := by dsimp only [x]; omega
  have convert := same_polynomial samples
  have translated : HigherDivisorWindow.Jets depth n t (BinomialDivisorWindow.cleared k v) := by
    intro j
    rw [convert,HigherDivisorWindow.jet_coeff]
    exact jets j
  have bound : (∑ i, |v i| * (span.choose i.val:ℤ)) < (first:ℤ)^depth := by
    simpa only [height,← Nat.choose_eq_fast_choose] using (measured.trans_lt small)
  apply HigherWindowCertificate.no_integer_root hm miss (x:ℤ)
  rw [← convert]
  exact BinomialDivisorWindow.vanishes translated bound dz
    (QuarticDivisorWindow.progression_offset unit anchor dz pos) (by exact_mod_cast lo)
    (gcd.isCoprime.of_isCoprime_of_dvd_left dz) near

end PrimeFactors.BinomialWindowCertificate
