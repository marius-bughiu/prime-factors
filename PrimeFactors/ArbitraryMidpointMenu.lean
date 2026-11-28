import PrimeFactors.PersistentLocalSurvivors

/-! Persistent local square tests for any finite choice of prime bases.
The chosen primes need not form an initial segment. -/
namespace PrimeFactors.ArbitraryMidpointMenu

open Finset
open PersistentLocalSurvivors (laneMod minLanes full_period_product)
open private PrimeFactors.PersistentLocalSurvivors.local_lanes
  PrimeFactors.PersistentLocalSurvivors.laneMod_pow from PrimeFactors.PersistentLocalSurvivors

/-- Adjoin the dyadic and triadic tests to the supplied set. -/
noncomputable def bases (S : Finset ℕ) := insert 2 (insert 3 S)

noncomputable def period (S : Finset ℕ) := 3456*∏ p∈S,p
noncomputable def lanes (S : Finset ℕ) := 8*∏ p∈S,((p-3)/2)

def Passes (S : Finset ℕ) (N h : ℕ) : Prop := ∀ p∈bases S, ∀ e : ℕ,
  IsSquare (((h:ℤ)^2-N : ℤ) : ZMod (p^e))

abbrev survivors (S : Finset ℕ) (start W N : ℕ) := {k : Fin W // Passes S N (start+k.val)}

/-- The basic CRT count for any finite set of primes, including the empty set. -/
theorem prime_set_interval (T : Finset ℕ) (start W N : ℕ) (prime : ∀ p∈T,p.Prime)
    (unit : ∀ p∈T, ¬p∣N) :
    W/(∏ p∈T,laneMod p)*(∏ p∈T,minLanes p) ≤ Nat.card {k : Fin W // ∀ p∈T, ∀ e : ℕ,
        IsSquare ((((start+k.val : ℕ):ℤ)^2-N : ℤ) : ZMod (p^e))} := by
  classical
  let I := {p // p∈T}
  choose A count good using fun i : I => PrimeFactors.PersistentLocalSurvivors.local_lanes
    (prime i.val i.property) N (unit i.val i.property)
  have cop : Pairwise (fun i j : I => (laneMod i.val).Coprime (laneMod j.val)) := by
    intro i j ne
    obtain ⟨a,ha⟩ := PrimeFactors.PersistentLocalSurvivors.laneMod_pow i.val
    obtain ⟨b,hb⟩ := PrimeFactors.PersistentLocalSurvivors.laneMod_pow j.val
    rw [ha,hb]
    exact (((Nat.coprime_primes (prime _ i.property) (prime _ j.property)).mpr
      (fun eq => ne (Subtype.ext eq))).pow_left a).pow_right b
  have pos (i : I) : 0<laneMod i.val := by
    obtain ⟨e,h⟩ := PrimeFactors.PersistentLocalSurvivors.laneMod_pow i.val
    rw [h]; exact pow_pos (prime _ i.property).pos _
  have full := full_period_product (fun i : I => laneMod i.val) pos cop A start W
  rw [←Finset.prod_subtype T (by simp) laneMod] at full
  have tally : (∏ i : I,minLanes i.val) = ∏ p∈T,minLanes p := (Finset.prod_subtype _ (by simp) _).symm
  rw [←tally]
  refine (Nat.mul_le_mul_left _ (Finset.prod_le_prod' (fun i _ => count i))).trans (full.trans ?_)
  apply Nat.card_le_card_of_injective (fun k => ⟨k.val,fun p mem e => good ⟨p,mem⟩ _ (k.property ⟨p,mem⟩) e⟩)
  intro x y eq
  exact Subtype.ext (Subtype.mk.inj eq)

private theorem period_and_lanes (S : Finset ℕ) (large : ∀ p∈S, 5≤p) :
    (∏ p∈bases S,laneMod p)=period S ∧ (∏ p∈bases S,minLanes p)=lanes S := by
  have no_two : 2∉S := fun h => (by decide : ¬5≤2) (large _ h)
  have no_three : 3∉S := fun h => (by decide : ¬5≤3) (large _ h)
  have fresh : 2∉insert 3 S := by simp [no_two]
  have mod_prod : (∏ p∈S,laneMod p)=∏ p∈S,p := by
    apply prod_congr rfl
    intro p hp
    have bound := large p hp
    simp [laneMod,show p≠2 by omega,show p≠3 by omega]
  have count_prod : (∏ p∈S,minLanes p)=∏ p∈S,((p-3)/2) := by
    apply prod_congr rfl
    intro p hp
    have bound := large p hp
    simp [minLanes,show p≠2 by omega,show p≠3 by omega]
  simp only [bases,prod_insert fresh,prod_insert no_three,mod_prod,count_prod,period,lanes]
  change 128*(27*_)=3456*_ ∧ 4*(2*_)=8*_
  constructor <;> ring

/-- Counts distinct offsets which pass every power of every chosen prime,
with special lanes at two and three contributing a factor of eight. -/
theorem interval (S : Finset ℕ) (start W N : ℕ) (prime : ∀ p∈S,p.Prime)
    (large : ∀ p∈S, 5≤p) (unit : ∀ p∈bases S, ¬p∣N) :
    W/period S*lanes S ≤ Nat.card (survivors S start W N) := by
  have primes (p : ℕ) (mem : p∈bases S) : p.Prime := by
    rcases mem_insert.mp mem with rfl|rest
    · exact Nat.prime_two
    rcases mem_insert.mp rest with rfl|hp
    · exact Nat.prime_three
    · exact prime p hp
  have h := prime_set_interval (bases S) start W N primes unit
  rw [(period_and_lanes S large).1,(period_and_lanes S large).2] at h
  exact h

private theorem half_covered {W P A C : ℕ} (pos : 0<P) (one : P≤W) (h : W/P*A≤C) :
    W*A≤2*P*C := by
  have at_least : 1≤W/P := (Nat.le_div_iff_mul_le pos).mpr (by simpa using one)
  have cover : P≤P*(W/P) := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left P at_least
  have rem : W%P < P*(W/P) := (Nat.mod_lt W pos).trans_le cover
  have split := Nat.div_add_mod W P
  have twice : W≤2*(P*(W/P)) := by omega
  calc
    W*A ≤ (2*(P*(W/P)))*A := Nat.mul_le_mul_right _ twice
    _ = 2*P*(W/P*A) := by ring
    _ ≤ 2*P*C := Nat.mul_le_mul_left _ h

/-- If the window contains a complete joint period, at least half its length
can be charged at the full-period survivor density. -/
theorem half_interval_mul (S : Finset ℕ) (start W N : ℕ) (prime : ∀ p∈S,p.Prime)
    (large : ∀ p∈S, 5≤p) (unit : ∀ p∈bases S, ¬p∣N) (wide : period S≤W) :
    W*lanes S≤2*period S*Nat.card (survivors S start W N) :=
  half_covered (Nat.mul_pos (by decide) (Finset.prod_pos (fun p hp => (prime p hp).pos))) wide
    (interval S start W N prime large unit)

theorem half_interval (S : Finset ℕ) (start W N : ℕ) (prime : ∀ p∈S,p.Prime)
    (large : ∀ p∈S, 5≤p) (unit : ∀ p∈bases S, ¬p∣N) (wide : period S≤W) :
    (W:ℚ)*lanes S/(2*period S) ≤ (Nat.card (survivors S start W N):ℚ) := by
  have pos : 0<period S := Nat.mul_pos (by decide) (Finset.prod_pos (fun p hp => (prime p hp).pos))
  apply (div_le_iff₀ (mul_pos (by norm_num) (by exact_mod_cast pos))).mpr
  rw [mul_comm (Nat.card (survivors S start W N):ℚ)]
  exact_mod_cast half_interval_mul S start W N prime large unit wide

private theorem odd_density {p : ℕ} (prime : p.Prime) (large : 5≤p) :
    (((p-3)/2:ℕ):ℚ)/p=((p:ℚ)-3)/(2*p) := by
  obtain ⟨k,hk⟩ := prime.odd_of_ne_two (by omega)
  have exact_half : (p-3)/2*2+3=p := by omega
  have rational : (((p-3)/2:ℕ):ℚ)*2+3=p := by exact_mod_cast exact_half
  rw [div_mul_eq_div_div]
  congr 1
  linarith only [rational]

/-- The certified lanes per period, expressed as a product of odd-prime densities. -/
theorem density_eq (S : Finset ℕ) (prime : ∀ p∈S,p.Prime) (large : ∀ p∈S, 5≤p) :
    (lanes S:ℚ)/period S=(1/432:ℚ)*(∏ p∈S,((p:ℚ)-3)/(2*p)) := by
  have prod_eq : (∏ p∈S,((p:ℚ)-3)/(2*p))=
      (∏ p∈S,(((p-3)/2:ℕ):ℚ))/(∏ p∈S,(p:ℚ)) := by
    rw [←Finset.prod_div_distrib]
    exact prod_congr rfl (fun p hp => (odd_density (prime p hp) (large p hp)).symm)
  have pos : 0<∏ p∈S,(p:ℚ) := prod_pos (fun p hp => by exact_mod_cast (prime p hp).pos)
  rw [prod_eq,lanes,period]
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_prod]
  field_simp [pos.ne']
  ring

/-- Half the analytic density bounds the complete-period certificate itself. -/
theorem certificate_half_density (S : Finset ℕ) (W : ℕ) (prime : ∀ p∈S,p.Prime)
    (large : ∀ p∈S, 5≤p) (wide : period S≤W) :
    (W:ℚ)/864*(∏ p∈S,((p:ℚ)-3)/(2*p)) ≤ ((W/period S*lanes S:ℕ):ℚ) := by
  have pos : 0<period S := Nat.mul_pos (by decide) (Finset.prod_pos (fun p hp => (prime p hp).pos))
  have floor := half_covered pos wide (le_refl (W/period S*lanes S))
  calc
    _ = (W:ℚ)/2*((lanes S:ℚ)/period S) := by rw [density_eq S prime large]; ring
    _ = (W:ℚ)*lanes S/(2*period S) := by rw [div_mul_eq_div_div]; ring
    _ ≤ _ := by
      apply (div_le_iff₀ (mul_pos (by norm_num) (by exact_mod_cast pos))).mpr
      rw [mul_comm (((W/period S*lanes S:ℕ):ℚ))]
      exact_mod_cast floor

/-- The same lower bound applies directly to the number of actual survivors. -/
theorem half_density (S : Finset ℕ) (start W N : ℕ) (prime : ∀ p∈S,p.Prime)
    (large : ∀ p∈S, 5≤p) (unit : ∀ p∈bases S, ¬p∣N) (wide : period S≤W) :
    (W:ℚ)/864*(∏ p∈S,((p:ℚ)-3)/(2*p)) ≤ (Nat.card (survivors S start W N):ℚ) :=
  (certificate_half_density S W prime large wide).trans (by exact_mod_cast interval S start W N prime large unit)

end PrimeFactors.ArbitraryMidpointMenu
