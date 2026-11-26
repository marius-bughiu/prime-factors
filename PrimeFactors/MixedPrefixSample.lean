import PrimeFactors.MixedPrefixPopulation

/-! The uniform finite sample for mixed leading- and trailing-bit predictions.
A single count of primes in the explicit upper interval supplies the denominator. -/

namespace PrimeFactors.MixedPrefixSample

open Finset MixedPrefixPopulation LowBitsCarryMenu

set_option exponentiation.threshold 8192

def X : ℕ := 2^1023

/-- All 1024-bit primes, and the subset at least 283X/200. -/
noncomputable def primes : Finset ℕ := (Ico X (2*X)).filter Nat.Prime
noncomputable def upperPrimes : Finset ℕ := primes.filter fun p => 283*X≤200*p

private theorem mem_primes {p : ℕ} : p∈primes ↔ (X≤p ∧ p<2*X) ∧ p.Prime := by simp [primes]
private theorem mem_upper {p : ℕ} : p∈upperPrimes ↔ p∈primes ∧ 283*X≤200*p := by simp [upperPrimes]

attribute [local irreducible] primes upperPrimes

/-- Both orderings of each eligible pair whose product satisfies E. -/
noncomputable def ordered (E : ℕ → Prop) : Finset (ℕ×ℕ) := by
  classical exact primes.offDiag.filter fun z => 2*X^2≤z.1*z.2 ∧ E (z.1*z.2)

/-- Each unordered pair is represented exactly once, with the smaller prime first. -/
noncomputable def sample (E : ℕ → Prop) : Finset (ℕ×ℕ) :=
  (ordered E).filter fun z => z.1<z.2

noncomputable def eligible := sample (fun _ => True)

def success (menu : ℕ → ℕ → Finset ℤ) (n : ℕ) : Prop :=
  ∃ k∈menu (headWord 640 n) (n%2^1023), ∃ a f, PredictedTraceCarries.probe n (2^704) a k=some f

noncomputable def successful (menu : ℕ → ℕ → Finset ℤ) := sample (success menu)

theorem mem_ordered {E : ℕ → Prop} {z : ℕ×ℕ} : z∈ordered E ↔
    z.1∈primes ∧ z.2∈primes ∧ z.1≠z.2 ∧ 2*X^2≤z.1*z.2 ∧ E (z.1*z.2) := by
  classical simp only [ordered,mem_filter,mem_offDiag,and_assoc]

private theorem mem_sample {E : ℕ → Prop} {z : ℕ×ℕ} : z∈sample E ↔ z∈ordered E ∧ z.1<z.2 := mem_filter
attribute [local irreducible] ordered

/-- Exactly two ordered draws correspond to every sorted pair, both in the
denominator and after imposing any event on the public product. -/
theorem two_orders (E : ℕ → Prop) : (ordered E).card=2*(sample E).card := by
  classical
  let V := ordered E
  let lt (z : ℕ×ℕ) := z.1<z.2
  have flip {z : ℕ×ℕ} (h : z∈V) : z.swap∈V := by
    obtain ⟨hp,hq,ne,size,event⟩ := mem_ordered.mp h
    exact mem_ordered.mpr ⟨hq,hp,ne.symm,by simpa [mul_comm] using size,by simpa [mul_comm] using event⟩
  have eq : (V.filter lt).card=(V.filter fun z => ¬lt z).card := by
    apply card_nbij' Prod.swap Prod.swap
    · intro z hz; obtain ⟨mem,h⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨flip mem,by dsimp [lt] at *; omega⟩
    · intro z hz; obtain ⟨mem,h⟩ := mem_filter.mp hz
      have ne := (mem_ordered.mp mem).2.2.1
      exact mem_filter.mpr ⟨flip mem,by dsimp [lt] at *; omega⟩
    · intro _ _; rfl
    · intro _ _; rfl
  have total := filter_card_add_filter_neg_card_eq_card (s:=V) lt
  change V.card=2*(V.filter lt).card
  omega

theorem successful_subset (menu : ℕ → ℕ → Finset ℤ) : successful menu⊆eligible := by
  intro z hz
  obtain ⟨inV,lt⟩ := mem_sample.mp hz
  obtain ⟨hp,hq,ne,sz,_⟩ := mem_ordered.mp inV
  exact mem_sample.mpr ⟨mem_ordered.mpr ⟨hp,hq,ne,sz,trivial⟩,lt⟩

private theorem product_lower {x p q : ℕ} (hp : 283*x≤200*p) (hq : 283*x≤200*q) :
    2*x^2≤p*q := by
  have h := Nat.mul_le_mul hp hq
  nlinarith only [h,Nat.zero_le (x*x)]

/-- Each pair of different primes in the upper interval qualifies. The
diagonal subtraction and division by the two orderings are exact. -/
theorem upper_pairs : upperPrimes.card*(upperPrimes.card-1)≤2*eligible.card := by
  have sub : upperPrimes.offDiag⊆ordered (fun _ => True) := by
    intro z hz
    obtain ⟨p,q,ne⟩ := mem_offDiag.mp hz
    obtain ⟨pm,bp⟩ := mem_upper.mp p
    obtain ⟨qm,bq⟩ := mem_upper.mp q
    exact mem_ordered.mpr ⟨pm,qm,ne,product_lower bp bq,trivial⟩
  have bound := card_le_card sub
  rw [offDiag_card,two_orders,←eligible] at bound
  rwa [Nat.mul_sub_left_distrib,Nat.mul_one]

/-- The only prime-count input. Rosser–Schoenfeld, Corollary 1, bounds the
number M of primes in [283X/200,2X) by M−1 > 0.22X/log X, and log X < 710. -/
def PrimeCountInput : Prop := 11*X<35500*(upperPrimes.card-1)

private theorem normalize {x m t : ℕ} (count : 11*x<35500*(m-1)) (pairs : m*(m-1)≤2*t) :
    x*x<21000000*t := by
  have sq := Nat.mul_self_lt_mul_self count
  have le := (Nat.mul_le_mul_right (m-1) (Nat.sub_le m 1)).trans pairs
  nlinarith only [sq,le,Nat.zero_le t]

theorem denominator (count : PrimeCountInput) : 2^2046<21000000*eligible.card := by
  have h := normalize count upper_pairs
  rwa [show (2:ℕ)^2046=X*X by decide +kernel]

/-- The 640-bit head-word theorem applied to the successful and eligible
finite samples, with the explicit prime count as its only population premise. -/
theorem probability {J : ℕ} (menu : ℕ → ℕ → Finset ℤ) (jp : 0<J) (count : PrimeCountInput)
    (slots : ∀ H∈Ico (2^640) (2^640+2^640), ∀ c<2^1023, Odd c → (menu H c).card≤J)
    (cap : ∀ H∈Ico (2^640) (2^640+2^640), ∀ c<2^1023, Odd c → ∀ k∈menu H c,
      (output c (2^704) k).natAbs<2^1406) :
    2^72*(successful menu).card<J*eligible.card := by
  apply at_640_bits menu jp (denominator count) slots cap
  intro z hz
  obtain ⟨pm,qm,ne,sz,w⟩ := mem_ordered.mp (mem_sample.mp hz).1
  obtain ⟨⟨pl,ph⟩,pp⟩ := mem_primes.mp pm
  obtain ⟨⟨ql,qh⟩,qp⟩ := mem_primes.mp qm
  have pr := Nat.mul_lt_mul_of_lt_of_le ph qh.le (by omega : 0<2*X)
  refine ⟨pp,qp,ne,pl,?_,ql,?_,?_,?_,w⟩
  · exact (show 2*X=(2:ℕ)^1024 by decide +kernel) ▸ ph
  · exact (show 2*X=(2:ℕ)^1024 by decide +kernel) ▸ qh
  · exact (show 2*X^2=(2:ℕ)^2047 by decide +kernel) ▸ sz
  · exact (show 2*X*(2*X)=(2:ℕ)^2048 by decide +kernel) ▸ pr

end PrimeFactors.MixedPrefixSample
