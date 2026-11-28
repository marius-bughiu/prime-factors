import PrimeFactors.CircleMarkParityLanes
import PrimeFactors.FactorClueWidthProfile
import PrimeFactors.SingularDyadicClueSuffixes

/-! Progressions for removing the full two-part of a circle remainder when
the target is one modulo eight. Only two classes modulo the chosen final
power require any further valuation calculation. -/
namespace PrimeFactors.CircleMarkDyadicLanes

open Finset
open scoped Classical
open private PrimeFactors.CircleMarkParityLanes.square_mod from PrimeFactors.CircleMarkParityLanes

private theorem square_period {j : ℕ} (pos : 0<j) (x : ℕ) :
    (x%2^j)^2 ≡ x^2 [MOD 2^(j+1)] := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  let r := x%2^(i+1)
  let z := x/2^(i+1)
  have rep : x=r+2^(i+1)*z := (Nat.mod_add_div ..).symm
  have eq : x^2=r^2+2^(i+1+1)*(r*z+2^i*z^2) := by
    conv_lhs => rw [rep]
    simp only [pow_succ (2:ℕ)]
    ring
  have zero := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right (2^(i+1+1)) (r*z+2^i*z^2))
  change r^2 ≡ x^2 [MOD 2^(i+1+1)]
  rw [eq]
  simpa only [add_zero] using (zero.add_left (r^2)).symm

private theorem flip {j a b : ℕ} : a ≡ b+2^j [MOD 2^(j+1)] ↔ b ≡ a+2^j [MOD 2^(j+1)] := by
  have invol (u : ℕ) : u+2^j+2^j ≡ u [MOD 2^(j+1)] := by
    rw [show u+2^j+2^j=u+2^(j+1) by rw [pow_succ]; omega]
    simp [Nat.ModEq]
  exact ⟨fun h => (invol b).symm.trans (h.add_right _).symm,
         fun h => (invol a).symm.trans (h.add_right _).symm⟩

/-- A single lookup at precision j selects precisely the positive remainders
having valuation j, even though this classification uses their next bit. -/
theorem resolved_iff {j a x : ℕ} (pos : 0<j) (above : a<x^2) :
    x%2^j∈TwoMaximalClueSuffixes.menu j a ↔ (x^2-a).factorization 2=j := by
  rw [TwoMaximalClueSuffixes.mem_menu,and_iff_right (Nat.mod_lt _ (by positivity))]
  have same := (square_period pos x).add_right (2^j)
  have eq : a ≡ (x%2^j)^2+2^j [MOD 2^(j+1)] ↔ FactorClueWidthProfile.GapAt a (x^2) j :=
    (Iff.intro (fun h => h.trans same) (fun h => h.trans same.symm)).trans flip
  rw [eq,FactorClueWidthProfile.gap_iff above.le]
  have nz : x^2-a≠0 := by omega
  constructor
  · rintro ⟨u,odd,form⟩
    have nd : ¬2∣u := by have h := Nat.odd_iff.mp odd; omega
    rw [form,Nat.factorization_mul (by positivity) odd.pos.ne',Finsupp.add_apply,
      Nat.prime_two.factorization_pow,Nat.factorization_eq_zero_of_not_dvd nd]
    simp
  · intro val
    refine ⟨ordCompl[2] (x^2-a),Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two nz),?_⟩
    rw [←val]
    exact (Nat.ordProj_mul_ordCompl_eq_self _ _).symm

/-- The surviving classes at depth K have at least K+1 factors of two. -/
theorem unresolved_iff {K a x : ℕ} (pos : 0<K) (above : a<x^2) :
    x%2^K∈SingularDyadicClueSuffixes.menu K a ↔ K+1≤(x^2-a).factorization 2 := by
  rw [SingularDyadicClueSuffixes.mem_menu,and_iff_right (Nat.mod_lt _ (by positivity))]
  have same := square_period pos x
  exact (Iff.intro (fun h => h.symm.trans same) (fun h => same.trans h.symm)).trans
    ((Nat.modEq_iff_dvd' above.le).trans (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)))

/-- Index zero is even, indices three through K are exact, and index K+1
collects the two unresolved congruence classes. -/
def Lane (K a x i : ℕ) : Prop :=
  (i=0 ∧ x%2=0) ∨
  (3 ≤ i ∧ i ≤ K ∧ x % 2^i ∈ TwoMaximalClueSuffixes.menu i a) ∨
  (i=K+1 ∧ x%2^K∈SingularDyadicClueSuffixes.menu K a)

private theorem parity {a x : ℕ} (gate : a%8=1) (above : a<x^2) :
    (x%2=0 → (x^2-a).factorization 2=0) ∧ (x%2≠0 → 3≤(x^2-a).factorization 2) := by
  have sq := PrimeFactors.CircleMarkParityLanes.square_mod x
  have eq : x^2-a+a=x^2 := by omega
  have add := congrArg (fun n : ℕ => n%8) eq
  change (x^2-a+a)%8=x^2%8 at add
  rw [Nat.add_mod] at add
  constructor
  · intro even
    exact Nat.factorization_eq_zero_of_not_dvd (by
      have := sq.1 even
      intro dv
      have d := Nat.dvd_iff_mod_eq_zero.mp dv
      omega)
  · intro odd
    apply (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : x^2-a≠0)).mp
    apply (Nat.modEq_iff_dvd' above.le).mp
    exact gate.trans (sq.2 odd).symm

/-- This single index characterizes a disjoint cover of all coordinates
with positive remainder and makes the stopping depth explicit. -/
theorem lane_iff {K a x i : ℕ} (depth : 3≤K) (gate : a%8=1) (above : a<x^2) :
    Lane K a x i ↔ i=min (K+1) ((x^2-a).factorization 2) := by
  have low := parity gate above
  unfold Lane
  rw [unresolved_iff (by omega) above]
  by_cases ie : 3 ≤ i
  · rw [resolved_iff (by omega) above]
    omega
  · omega

theorem unique_lane {K a x : ℕ} (depth : 3≤K) (gate : a%8=1) (above : a<x^2) :
    ∃! i, Lane K a x i := by
  simp only [lane_iff depth gate above]
  exact ⟨_,rfl,fun _ h => h⟩

/-- For all resolved lanes the quotient at the lane's power of two is exactly
the full odd part checked by the reduced cofactor-band condition. -/
theorem odd_part {K a x i : ℕ} (depth : 3≤K) (gate : a%8=1) (above : a<x^2)
    (lane : Lane K a x i) (resolved : i≤K) :
    ordCompl[2] (x^2-a)=(x^2-a)/2^i := by
  have val := (lane_iff depth gate above).mp lane
  change (x^2-a)/2^((x^2-a).factorization 2)=(x^2-a)/2^i
  rw [show (x^2-a).factorization 2=i by omega]

/-- Count progressions with their depths attached. There is one even
progression, exactly two for each resolved odd valuation, and two final
ones that need a further divisibility check. -/
theorem indexed_count {K a : ℕ} (depth : 3≤K) (gate : a%8=1) :
    (∀ j∈Icc 3 K, (TwoMaximalClueSuffixes.menu j a).card=2) ∧
    (∑ j∈Icc 3 K,(TwoMaximalClueSuffixes.menu j a).card)=2*(K-2) ∧
    (SingularDyadicClueSuffixes.menu K a).card=2 := by
  have ao : Odd a := Nat.odd_iff.mpr (by omega)
  have each : ∀ j∈Icc 3 K, (TwoMaximalClueSuffixes.menu j a).card=2 := fun j hj => by
    simp [TwoMaximalClueSuffixes.card_menu (mem_Icc.mp hj).1 ao,gate]
  refine ⟨each,?_,by simp [SingularDyadicClueSuffixes.card_menu depth ao,gate]⟩
  rw [sum_congr rfl each]
  simp [Nat.card_Icc]
  omega

/-- Under uniform sampling of all K-bit coordinates, exactly two outcomes
per 2^K need further bits; the denominator includes even coordinates. -/
theorem unresolved_count {K a : ℕ} (depth : 3≤K) (gate : a%8=1) :
    ((range (2^K)).filter fun x => x%2^K∈SingularDyadicClueSuffixes.menu K a).card=2 := by
  have same : ((range (2^K)).filter fun x => x%2^K∈SingularDyadicClueSuffixes.menu K a)=
      SingularDyadicClueSuffixes.menu K a := by
    ext x
    simp only [mem_filter,mem_range]
    exact ⟨fun h => (Nat.mod_eq_of_lt h.1) ▸ h.2,fun h => by
      have room := (SingularDyadicClueSuffixes.mem_menu.mp h).1
      exact ⟨room,(Nat.mod_eq_of_lt room).symm ▸ h⟩⟩
  rw [same]
  exact (indexed_count depth gate).2.2

/-- To obtain the next two exact lanes and two unresolved lanes, test just
the four children of the preceding unresolved residues. Their union is exact
including when the representatives have nonpositive integer remainders. -/
theorem next_children {K a : ℕ} (depth : 3≤K) (gate : a%8=1) :
    SingularDyadicClueSuffixes.menu (K+1) a ∪ TwoMaximalClueSuffixes.menu (K+1) a =
      (SingularDyadicClueSuffixes.menu K a).biUnion (fun r => {r,r+2^K}) := by
  have next := indexed_count (K:=K+1) (by omega) gate
  have leftCard : (SingularDyadicClueSuffixes.menu (K+1) a ∪ TwoMaximalClueSuffixes.menu (K+1) a).card=4 := by
    rw [card_union_of_disjoint (SingularDyadicClueSuffixes.disjoint_maximal ..),next.2.2,
      next.1 (K+1) (mem_Icc.mpr ⟨by omega,le_rfl⟩)]
  apply eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    have child : x<2^(K+1) ∧ x^2 ≡ a [MOD 2^(K+1)] := by
      rcases mem_union.mp hx with deep|exactLane
      · obtain ⟨room,eq⟩ := SingularDyadicClueSuffixes.mem_menu.mp deep
        exact ⟨room,eq.of_dvd (pow_dvd_pow 2 (by omega))⟩
      · obtain ⟨room,eq⟩ := TwoMaximalClueSuffixes.mem_menu.mp exactLane
        have r := eq.of_dvd (pow_dvd_pow 2 (by omega : K+1≤K+1+1))
        have cancel : x^2+2^(K+1) ≡ x^2 [MOD 2^(K+1)] := by simp [Nat.ModEq]
        exact ⟨room,(r.trans cancel).symm⟩
    have parent : x%2^K ∈ SingularDyadicClueSuffixes.menu K a :=
      SingularDyadicClueSuffixes.mem_menu.mpr ⟨Nat.mod_lt _ (by positivity),
        (square_period (by omega) x).trans child.2⟩
    refine mem_biUnion.mpr ⟨x%2^K,parent,?_⟩
    have half : x/2^K<2 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      (by simpa only [pow_succ,Nat.mul_comm 2] using child.1)
    have rep := Nat.mod_add_div x (2^K)
    simp only [mem_insert,mem_singleton]
    have cases (z : ℕ) (hz : z<2) : z=0 ∨ z=1 := by omega
    rcases cases _ half with h|h
    · exact Or.inl (by simpa [h] using rep.symm)
    · exact Or.inr (by simpa [h] using rep.symm)
  · have upper := card_biUnion_le_card_mul (SingularDyadicClueSuffixes.menu K a)
        (fun r => {r,r+2^K}) 2 (fun _ _ => card_le_two)
    simpa only [(indexed_count depth gate).2.2,leftCard] using upper

/-- At target 17 the final two resolved lanes differ from the two progressions
needing another bit. -/
theorem seventeen :
    (∑ j∈Icc 3 8,(TwoMaximalClueSuffixes.menu j 17).card)=12 ∧
    TwoMaximalClueSuffixes.menu 8 17={105,151} ∧
    SingularDyadicClueSuffixes.menu 8 17={23,233} ∧
    ((range 256).filter fun x => x%256∈SingularDyadicClueSuffixes.menu 8 17).card=2 := by
  refine ⟨(indexed_count (K:=8) (a:=17) (by decide) (by decide)).2.1,?_,?_,
    unresolved_count (K:=8) (a:=17) (by decide) (by decide)⟩ <;> decide +kernel

end PrimeFactors.CircleMarkDyadicLanes
