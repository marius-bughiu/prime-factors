import PrimeFactors.ComplementaryQuarticPopulation
import PrimeFactors.RationalQuarticFactorPair
import PrimeFactors.ScaledQuarticControls

/-! Executable fourth-root tests on a scaled input. The only arguments to
the search are the product and the list of denominators. -/
namespace PrimeFactors.ScaledQuarticReadings

open ComplementaryQuarticProducts (choices readings)
open MixedPrefixSample (eligible)
open private PrimeFactors.QuarticPrimePopulation.eligible_bounds from PrimeFactors.QuarticPrimePopulation
set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

/-- Return the two gcds in increasing order only after verifying both their
nontriviality and their product. This check also handles inputs with more
than two prime factors. -/
def project (n : ℕ) (ab : ℕ×ℕ) : Option (ℕ×ℕ) :=
  let a := n.gcd ab.1
  let b := n.gcd ab.2
  if 1<a ∧ 1<b ∧ a*b=n then some (min a b,max a b) else none

def one (n d : ℕ) : Option (ℕ×ℕ) :=
  let raw := readings (d^4*n)
  (raw.1.bind (project n)).orElse (fun _ => raw.2.bind (project n))

def run (n : ℕ) (denominators : List ℕ) : Option (ℕ×ℕ) :=
  denominators.findSome? (one n)

theorem project_sound {n : ℕ} {ab pair : ℕ×ℕ} (hit : project n ab=some pair) :
    1<pair.1 ∧ pair.1≤pair.2 ∧ pair.1*pair.2=n := by
  dsimp only [project] at hit
  split at hit
  · rename_i ok
    obtain rfl := Option.some.inj hit
    rcases le_total (n.gcd ab.1) (n.gcd ab.2) with h|h
    · simpa [min_eq_left h,max_eq_right h] using And.intro ok.1 (And.intro h ok.2.2)
    · simpa [min_eq_right h,max_eq_left h,Nat.mul_comm] using And.intro ok.2.1 (And.intro h ok.2.2)
  · contradiction

private theorem on_raw {p q d : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q) (size : 6*d^4≤p*q)
    {ab : ℕ×ℕ} (inside : ab∈choices (d^4*(p*q))) : project (p*q) ab=some (p,q) := by
  obtain ⟨x,y,_,yp,repr,_,rfl⟩ := ComplementaryQuarticProducts.mem_choices.mp inside
  rcases RationalQuarticFactorPair.split pp qp ord.ne yp repr size with h|h
  · simp [project,h.1,h.2,pp.one_lt,qp.one_lt,min_eq_left ord.le,max_eq_right ord.le]
  · simp [project,h.1,h.2,pp.one_lt,qp.one_lt,min_eq_right ord.le,max_eq_left ord.le,Nat.mul_comm q p]

private theorem normalize {n d : ℕ} (v : ℕ×ℕ)
    (all : ∀ ab∈choices (d^4*n),project n ab=some v) :
    one n d=if (choices (d^4*n)).Nonempty then some v else none := by
  classical
  cases l : RecognizingQuarticProducts.recognize (d^4*n) with
  | some ab =>
    have hit := all ab (Finset.mem_union_left _ (Option.mem_toFinset.mpr l))
    have present : (choices (d^4*n)).Nonempty := ⟨ab,Finset.mem_union_left _ (Option.mem_toFinset.mpr l)⟩
    simp [one,readings,l,hit,present]
  | none =>
    cases r : ComplementaryQuarticProducts.recognizeY (d^4*n) with
    | some ab =>
      have hit := all ab (Finset.mem_union_right _ (Option.mem_toFinset.mpr r))
      have present : (choices (d^4*n)).Nonempty := ⟨ab,Finset.mem_union_right _ (Option.mem_toFinset.mpr r)⟩
      simp [one,readings,l,r,hit,present]
    | none => simp [one,readings,choices,l,r]

theorem one_eq {v : ℕ×ℕ} (hv : v∈eligible) (d : ℕ) (fit : d≤2048) :
    one (v.1*v.2) d=if (choices (d^4*(v.1*v.2))).Nonempty then some v else none := by
  obtain ⟨_,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp hv
  have size := (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left fit 4)).trans
    ((by decide +kernel : 6*2048^4≤2^2047).trans (PrimeFactors.QuarticPrimePopulation.eligible_bounds hv).1)
  exact normalize v (fun _ h => on_raw pp qp ord size h)

theorem run_eq {v : ℕ×ℕ} (hv : v∈eligible) (D : List ℕ) (fit : ∀ d∈D,d≤2048) :
    run (v.1*v.2) D=if ∃ d∈D,(choices (d^4*(v.1*v.2))).Nonempty then some v else none := by
  classical
  induction D with
  | nil => simp [run]
  | cons d D ih =>
    have tail := ih (fun e he => fit e (List.mem_cons_of_mem _ he))
    have head := one_eq hv d (fit d (List.mem_cons_self ..))
    unfold run at tail ⊢
    by_cases yes : (choices (d^4*(v.1*v.2))).Nonempty <;> simp [head,yes,tail]

private theorem projected (n a b p q : ℕ) (ga : n.gcd a=p) (gb : n.gcd b=q)
    (pp : 1<p) (qp : 1<q) (prod : p*q=n) : project n (a,b)=some (min p q,max p q) := by
  simp [project,ga,gb,pp,qp,prod]

private theorem miss {n d : ℕ} (h : readings (d^4*n)=(none,none)) : one n d=none := by rw [one,h]; rfl
private theorem hit {n d : ℕ} {ab pq : ℕ×ℕ} (h : readings (d^4*n)=(none,some ab))
    (pair : project n ab=some pq) : one n d=some pq := by rw [one,h]; exact pair

private theorem at_second {n d e : ℕ} {pq : ℕ×ℕ} (a : one n 1=none) (b : one n d=some pq) :
    run n [1,d,e]=some pq := by simp [run,a,b]
private theorem at_third {n d e : ℕ} {pq : ℕ×ℕ} (a : one n 1=none) (b : one n d=none) (c : one n e=some pq) :
    run n [1,d,e]=some pq := by simp [run,a,b,c]

open ScaledQuarticControls

theorem example58 : run N58 [1,725,1517]=some (362037209,536767369) :=
  at_third (miss (by simpa only [one_pow,one_mul] using unscaled58)) (miss miss725_58)
    (hit hit1517_58 ((projected _ _ _ _ _ gcd58.1 gcd58.2.1 (by decide) (by decide)
      (by decide +kernel)).trans (by decide +kernel)))

theorem example37 : run N37 [1,725,1517]=some (229777,420853) :=
  at_second (miss (by simpa only [one_pow,one_mul] using unscaled37))
    (hit hit725_37 ((projected _ _ _ _ _ gcd37.1 gcd37.2.1 (by decide) (by decide)
      (by decide +kernel)).trans (by decide +kernel)))

end PrimeFactors.ScaledQuarticReadings
