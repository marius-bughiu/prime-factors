import PrimeFactors.SquareDivisorClueWindow
import PrimeFactors.FourNeighborScaleFrequency

/-! Count sums in the basic balanced interval that satisfy four labeled
square-divisibility congruences. The equal signs constrain the sum and the
mixed signs constrain its discriminant. These are necessary local tests. -/
namespace PrimeFactors.FourSquareDivisorClues

open Finset FourNeighborScaleFrequency
set_option exponentiation.threshold 4096

/-- The equal signs use the true sum residue; the mixed signs use the true
squared-gap residue. The interval in the filter ensures 4n < x². -/
noncomputable def survivors (n s g : ℕ) (r : Bool → Bool → ℕ) : Finset ℕ :=
  (Ioc (4*n).sqrt (9*n/2).sqrt).filter fun x => Even x ∧ x ≡ s [MOD 4] ∧
    x ≡ s [MOD (r false false)^2] ∧ x ≡ s [MOD (r true true)^2] ∧
    x^2-4*n ≡ g^2 [MOD (r false true)^2] ∧ x^2-4*n ≡ g^2 [MOD (r true false)^2]

theorem mem_survivors {n s g x : ℕ} {r : Bool → Bool → ℕ} : x∈survivors n s g r ↔
    OppositeSquareScaleBands.InSumWindow n x ∧ Even x ∧ x ≡ s [MOD 4] ∧
    x ≡ s [MOD (r false false)^2] ∧ x ≡ s [MOD (r true true)^2] ∧
    x^2-4*n ≡ g^2 [MOD (r false true)^2] ∧ x^2-4*n ≡ g^2 [MOD (r true false)^2] := by
  simp only [survivors,mem_filter,mem_Ioc,Nat.sqrt_lt',Nat.le_sqrt',Nat.le_div_iff_mul_le
    (by decide : 0<2),OppositeSquareScaleBands.InSumWindow,mul_comm (x^2) 2]

/-- All right-hand sides of the four tests can be computed from the product
alone once the four labeled divisors are supplied. -/
theorem mem_survivors_public {p q x : ℕ} (hp : Odd p) (hq : Odd q) (order : p≤q)
    (r : Bool → Bool → ℕ) (given : ∀ a b, (r a b)^2 ∣ neighbor a p*neighbor b q) :
    x ∈ survivors (p*q) (p+q) (q-p) r ↔
    OppositeSquareScaleBands.InSumWindow (p*q) x ∧ Even x ∧ x ≡ p*q+1 [MOD 4] ∧
    x ≡ p*q+1 [MOD (r false false)^2] ∧ (r true true)^2 ∣ x+(p*q+1) ∧
    x^2-4*(p*q) ≡ (p*q-1)^2 [MOD (r false true)^2] ∧
    x^2-4*(p*q) ≡ (p*q-1)^2 [MOD (r true false)^2] := by
  have pp : 1≤p := hp.pos
  have qp : 1≤q := hq.pos
  have id₁ : p*q+1 = (p+q)+(p-1)*(q-1) := by
    obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le pp
    obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le qp
    rw [ha,hb]; simp; ring
  have id₂ : (p+q)+(p*q+1)=(p+1)*(q+1) := by ring
  have id₃ : (p*q-1)^2=(q-p)^2+((p-1)*(q+1))*((p+1)*(q-1)) := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le order
    obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le pp
    rw [hd,Nat.add_sub_cancel_left,ha]
    simp only [Nat.add_sub_cancel_left, Nat.add_assoc]
    rw [show (1+a)*(1+(a+d))-1=a+(a+d)+a*(a+d) by
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_add,Nat.mul_one]; omega]
    ring
  have shifted {m u v w : ℕ} (eqn : v=u+w) (hw : m ∣ w) : u ≡ v [MOD m] := by
    rw [eqn]
    simpa using hw.zero_modEq_nat.add_left u
  have h4 := shifted id₁ (SquareDivisorClueWindow.four_dvd_neighbors false false hp hq)
  have hmm := shifted id₁ (given false false)
  have hpp : (p+q)+(p*q+1) ≡ 0 [MOD (r true true)^2] := by
    rw [id₂]; exact (given true true).modEq_zero_nat
  have hpq := shifted id₃ (dvd_mul_of_dvd_left (given false true) _)
  have hqp := shifted id₃ (dvd_mul_of_dvd_right (given true false) _)
  have add_test : (x ≡ p+q [MOD (r true true)^2]) ↔ (r true true)^2 ∣ x+(p*q+1) :=
    ⟨fun h => Nat.modEq_zero_iff_dvd.mp ((h.add_right _).trans hpp),
     fun h => Nat.ModEq.add_right_cancel' _ (h.modEq_zero_nat.trans hpp.symm)⟩
  have replace {m a b z : ℕ} (h : a ≡ b [MOD m]) : (z ≡ a [MOD m]) ↔ (z ≡ b [MOD m]) :=
    ⟨fun hz => hz.trans h,fun hz => hz.trans h.symm⟩
  rw [mem_survivors,add_test,replace h4,replace hmm,replace hpq,replace hqp]

/-- Four even lifted square roots Y supply a common modulus at most their
squared product divided by 64. A full period contributes one candidate. -/
theorem count_from_lifts {n s g k C : ℕ} {r Y : Bool → Bool → ℕ}
    (full : 2^2047≤n) (even : Even s) (disc : g^2+4*n=s^2)
    (positive : ∀ a b, 0<Y a b) (lift : ∀ a b, r a b ∣ Y a b)
    (four : ∀ a b, 4∣(Y a b)^2) (small : ∀ a b, Y a b<2^k)
    (budget : C*(2^k)^8 ≤ 64*2^1020) : C ≤ (survivors n s g r).card := by
  have pack (a b : Bool) : ∃ u : ℕ, 0<u ∧ (Y a b)^2=4*u := by
    obtain ⟨u,eq⟩ := four a b
    have pos := pow_pos (positive a b) 2
    exact ⟨u,by omega,eq⟩
  obtain ⟨a,ap,ea⟩ := pack false false
  obtain ⟨b,bp,eb⟩ := pack true true
  obtain ⟨c,cp,ec⟩ := pack false true
  obtain ⟨d,dp,ed⟩ := pack true false
  let M := 4*a*b*c*d
  have mp : 0<M := by dsimp only [M]; positivity
  have m4 : 4∣M := ⟨a*b*c*d,by dsimp only [M]; ring⟩
  have covers (i j : Bool) : (r i j)^2 ∣ M := by
    apply (pow_dvd_pow_of_dvd (lift i j) 2).trans
    cases i <;> cases j
    · exact ⟨b*c*d,by rw [ea]; dsimp only [M]; ring⟩
    · exact ⟨a*b*d,by rw [ec]; dsimp only [M]; ring⟩
    · exact ⟨a*b*c,by rw [ed]; dsimp only [M]; ring⟩
    · exact ⟨a*c*d,by rw [eb]; dsimp only [M]; ring⟩
  have sq (i j : Bool) := Nat.pow_le_pow_left (small i j).le 2
  have sz : 64*M ≤ (2^k)^8 := calc
    _ = (Y false false)^2*(Y true true)^2*((Y false true)^2*(Y true false)^2) := by
      rw [ea,eb,ec,ed]; dsimp only [M]; ring
    _ ≤ _ := (Nat.mul_le_mul (Nat.mul_le_mul (sq false false) (sq true true))
      (Nat.mul_le_mul (sq false true) (sq true false))).trans_eq (by ring)
  have width : C*M ≤ 2^1020 := by
    apply Nat.le_of_mul_le_mul_left (c:=64) _ (by decide)
    rw [show 64*(C*M)=C*(64*M) by ring]
    exact (Nat.mul_le_mul_left C sz).trans budget
  rw [←SquareDivisorClueWindow.full_periods (4*n).sqrt C s mp]
  apply card_le_card
  intro x hx
  obtain ⟨inside,same⟩ := mem_filter.mp hx
  obtain ⟨lo,hi⟩ := mem_Ioc.mp inside
  have window := SquareDivisorClueWindow.sum_slab full lo (hi.trans (Nat.add_le_add_left width _))
  have h4 := same.of_dvd m4
  have h2 := h4.of_dvd (by decide : 2∣4)
  change x%2=s%2 at h2
  have discriminant : x^2-4*n ≡ g^2 [MOD M] := by
    apply Nat.ModEq.add_right_cancel' (4*n)
    rw [Nat.sub_add_cancel window.1.le,disc]
    exact same.pow 2
  exact mem_survivors.mpr ⟨window,Nat.even_iff.mpr (h2.trans (Nat.even_iff.mp even)),h4,
    same.of_dvd (covers false false),same.of_dvd (covers true true),
    discriminant.of_dvd (covers false true),discriminant.of_dvd (covers true false)⟩

/-- Each root may be any supplied positive square-divisor root, including the
largest one at its sign. The conclusion counts the listed congruences. -/
theorem count_of_divisors {p q k C : ℕ} (r : Bool → Bool → ℕ)
    (full : 2^2047≤p*q) (le : p≤q) (hp : Odd p) (hq : Odd q)
    (positive : ∀ a b, 0<r a b) (given : ∀ a b, (r a b)^2 ∣ neighbor a p * neighbor b q)
    (small : ∀ a b y, y^2∣neighbor a p * neighbor b q → y<2^k)
    (budget : C*(2^k)^8 ≤ 64*2^1020) : C ≤ (survivors (p*q) (p+q) (q-p) r).card := by
  have liftable (a b : Bool) := SquareDivisorClueWindow.even_lift (positive a b)
    (SquareDivisorClueWindow.four_dvd_neighbors a b hp hq) (given a b)
  choose Y Ypos lift four div using liftable
  have disc : (q-p)^2+4*(p*q)=(p+q)^2 := by
    obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le le
    rw [Nat.add_sub_cancel_left]
    ring
  exact count_from_lifts full (hp.add_odd hq) disc Ypos lift four
    (fun a b => small a b (Y a b) (div a b)) budget

/-- All four congruences leave at least 2^514 sums at the 64-bit root cutoff. -/
theorem count_64 {p q : ℕ} (r : Bool → Bool → ℕ)
    (full : 2^2047≤p*q) (le : p≤q) (hp : Odd p) (hq : Odd q)
    (positive : ∀ a b, 0<r a b) (given : ∀ a b, (r a b)^2 ∣ neighbor a p * neighbor b q)
    (small : ∀ a b y, y^2∣neighbor a p * neighbor b q → y<2^64) :
    2^514 ≤ (survivors (p*q) (p+q) (q-p) r).card :=
  count_of_divisors r full le hp hq positive given small (by decide +kernel)

/-- All four congruences leave at least 2^258 sums at the 96-bit root cutoff. -/
theorem count_96 {p q : ℕ} (r : Bool → Bool → ℕ)
    (full : 2^2047≤p*q) (le : p≤q) (hp : Odd p) (hq : Odd q)
    (positive : ∀ a b, 0<r a b) (given : ∀ a b, (r a b)^2 ∣ neighbor a p * neighbor b q)
    (small : ∀ a b y, y^2∣neighbor a p * neighbor b q → y<2^96) :
    2^258 ≤ (survivors (p*q) (p+q) (q-p) r).card :=
  count_of_divisors r full le hp hq positive given small (by decide +kernel)

end PrimeFactors.FourSquareDivisorClues
