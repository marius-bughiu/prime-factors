import PrimeFactors.TwoMaximalClueSuffixes
import PrimeFactors.DyadicClueFullSumClass

/-! Public dyadic factor suffixes that contain a square root of the product
at every prescribed finite precision. -/
namespace PrimeFactors.SingularDyadicClueSuffixes

open Finset
open private PrimeFactors.TwoMaximalClueSuffixes.root_signs from PrimeFactors.TwoMaximalClueSuffixes

/-- Shifting the argument of the maximal-gain congruence by half a period
cancels its offset and gives precisely the singular suffixes. -/
noncomputable def menu (k N : ℕ) : Finset ℕ := TwoMaximalClueSuffixes.menu k (N+2^k)

theorem mem_menu {k N a : ℕ} : a∈menu k N ↔ a<2^k ∧ a^2 ≡ N [MOD 2^(k+1)] := by
  rw [menu,TwoMaximalClueSuffixes.mem_menu]
  exact and_congr_right fun _ => ⟨fun h => (Nat.ModEq.add_right_cancel' _ h).symm,
    fun h => h.symm.add_right _⟩

private theorem mem_int {k N a : ℕ} : a∈menu k N ↔ a<2^k ∧
    (a:ℤ)^2 ≡ (N:ℤ) [ZMOD (2:ℤ)^(k+1)] := by
  rw [mem_menu,←Int.natCast_modEq_iff]
  push_cast
  rfl

private theorem shifted_gate {k : ℕ} (hk : 3≤k) (N : ℕ) : (N+2^k)%8=N%8 := by
  have add := (Nat.modEq_zero_iff_dvd.mpr (show 8∣(2:ℕ)^k from pow_dvd_pow 2 hk)).add_left N
  simpa only [Nat.add_zero] using add

theorem opposite_pair {k N : ℕ} (hk : 3≤k) (gate : N%8=1) :
    ∃ a b : ℕ, a≠b ∧ (a:ℤ)+b ≡ 0 [ZMOD (2:ℤ)^k] ∧ menu k N={a,b} :=
  TwoMaximalClueSuffixes.opposite_pair hk ((shifted_gate hk N).trans gate)

theorem card_menu {k N : ℕ} (hk : 3≤k) (odd : Odd N) :
    (menu k N).card = if N%8=1 then 2 else 0 := by
  have even : Even ((2:ℕ)^k) := (by decide : Even (2:ℕ)).pow_of_ne_zero (by omega)
  rw [menu,TwoMaximalClueSuffixes.card_menu hk (odd.add_even even),shifted_gate hk]

/-- The two pairs at a product congruent to one modulo eight share no suffix. -/
theorem disjoint_maximal (k N : ℕ) : Disjoint (menu k N) (TwoMaximalClueSuffixes.menu k N) := by
  apply disjoint_left.mpr
  intro a singular maximal
  have both := (mem_menu.mp singular).2.trans (TwoMaximalClueSuffixes.mem_menu.mp maximal).2
  have impossible : 0 ≡ (2:ℕ)^k [MOD 2^(k+1)] :=
    Nat.ModEq.add_left_cancel' (a^2) (by simpa only [Nat.add_zero] using both)
  have := (Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ))).mp (Nat.modEq_zero_iff_dvd.mp impossible.symm)
  omega

/-- Every valid suffix contains an odd square root at each requested
precision. The witness can be chosen separately for each e. -/
theorem lift {k N a : ℕ} (hk : 3≤k) (odd : Odd N) (hit : a∈menu k N) (e : ℕ) :
    ∃ r : ℤ, Odd r ∧ r ≡ (a:ℤ) [ZMOD (2:ℤ)^k] ∧ r^2 ≡ (N:ℤ) [ZMOD (2:ℤ)^e] := by
  have gate : N%8=1 := by
    have nonempty := card_pos.mpr ⟨a,hit⟩
    rw [card_menu hk odd] at nonempty
    split_ifs at nonempty with gate
    · exact gate
    · omega
  have base := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr (show 1 ≡ N [MOD 8] from gate.symm))
  obtain ⟨r,ro,deep⟩ := LocalMidpointLanes.lift_eight (D:=N) base (e+k)
  have root (j : ℕ) (le : j≤e+k+3) : r^2 ≡ (N:ℤ) [ZMOD (2:ℤ)^j] :=
    Int.modEq_iff_dvd.mpr ((pow_dvd_pow _ le).trans deep)
  have matchSq := (mem_int.mp hit).2.trans (root (k+1) (by omega)).symm
  rcases (PrimeFactors.TwoMaximalClueSuffixes.root_signs (by omega) a r ro).mp matchSq with same|opposite
  · exact ⟨r,ro,same.symm,root e (by omega)⟩
  · exact ⟨-r,ro.neg,opposite.symm,by simpa only [neg_sq] using root e (by omega)⟩

/-- Conversely, roots at all finite precisions with the given suffix imply
membership. The public test thus suffices to select the square-root branch. -/
theorem lift_iff {k N a : ℕ} (hk : 3≤k) (odd : Odd N) (room : a<2^k) :
    a∈menu k N ↔ ∀ e : ℕ, ∃ r : ℤ, Odd r ∧ r ≡ (a:ℤ) [ZMOD (2:ℤ)^k] ∧
      r^2 ≡ (N:ℤ) [ZMOD (2:ℤ)^e] := by
  refine ⟨fun h => lift hk odd h,?_⟩
  intro all
  obtain ⟨r,ro,same,sq⟩ := all (k+1)
  exact mem_int.mpr ⟨room,((PrimeFactors.TwoMaximalClueSuffixes.root_signs (by omega) a r ro).mpr
    (Or.inl same.symm)).trans sq⟩

/-- For an actual odd factor the singular case is equivalent to agreement
with its partner through all k+1 low bits. -/
theorem true_suffix {k p q : ℕ} (hk : 1≤k) (odd : Odd p) :
    p%2^k ∈ menu k (p*q) ↔ p ≡ q [MOD 2^(k+1)] := by
  have cl : ((p%2^k:ℕ):ℤ) ≡ (p:ℤ) [ZMOD (2:ℤ)^k] := by
    exact_mod_cast Int.natCast_modEq_iff.mpr (Nat.mod_modEq p (2^k))
  have sqz := (PrimeFactors.TwoMaximalClueSuffixes.root_signs hk ((p%2^k:ℕ):ℤ) p
    (by exact_mod_cast odd)).mpr (Or.inl cl)
  have sq : (p%2^k)^2 ≡ p^2 [MOD 2^(k+1)] := Int.natCast_modEq_iff.mp (by exact_mod_cast sqz)
  rw [mem_menu,and_iff_right (Nat.mod_lt p (by positivity))]
  constructor
  · intro test
    exact Nat.ModEq.cancel_left_of_coprime (odd.coprime_two_right.pow_right _).symm
      (by simpa only [pow_two] using sq.symm.trans test)
  · intro eq
    exact sq.trans (by simpa only [pow_two] using eq.mul_left p)

/-- Every canonical suffix outside the singular menu has finite discriminant
valuation at most k. -/
theorem regular_valuation {k N a : ℕ} (room : a<2^k) (miss : a∉menu k N) :
    ∃ t ≤ k, ∃ g : ℤ, Odd g ∧ (a:ℤ)^2-N=2^t*g := by
  let D : ℤ := (a:ℤ)^2-N
  have excluded : ¬(2:ℤ)^(k+1)∣D := by
    intro div
    apply miss
    exact mem_int.mpr ⟨room,(Int.modEq_iff_dvd.mpr div).symm⟩
  have nz : D.natAbs≠0 := fun zero => excluded (Int.natAbs_eq_zero.mp zero ▸ dvd_zero _)
  obtain ⟨t,u,odd,absEq⟩ := Nat.exists_eq_two_pow_mul_odd nz
  have zEq : (D.natAbs:ℤ)=(2:ℤ)^t*u := by exact_mod_cast absEq
  rw [Int.natCast_natAbs] at zEq
  have signed : ∃ g : ℤ, Odd g ∧ D=2^t*g := by
    have zo : Odd (u:ℤ) := by exact_mod_cast odd
    by_cases pos : 0≤D
    · exact ⟨u,zo,by simpa only [abs_of_nonneg pos] using zEq⟩
    · rw [abs_of_neg (lt_of_not_ge pos)] at zEq
      exact ⟨-u,zo.neg,by linarith only [zEq]⟩
  obtain ⟨g,go,eq⟩ := signed
  have limit : t≤k := by
    by_contra! large
    exact excluded ((pow_dvd_pow (2:ℤ) large).trans ⟨g,eq⟩)
  exact ⟨t,limit,g,go,eq⟩

/-- Outside the two singular suffixes, the full all-precisions criterion
for a sum is the single congruence coming from the regular valuation. -/
theorem regular_branch {k N a : ℕ} (hk : 0<k) (ao : Odd a) (room : a<2^k)
    (miss : a∉menu k N) : ∃ t ≤ k, ∀ s : ℤ, DyadicClueFullSumClass.Possible k N a s ↔
      (a:ℤ)*s ≡ (a:ℤ)^2+N [ZMOD (2:ℤ)^((if t=k then k+1 else k)+t)] := by
  obtain ⟨t,le,g,odd,disc⟩ := regular_valuation room miss
  exact ⟨t,le,fun _ => DyadicClueFullSumClass.full_class hk le (by exact_mod_cast ao) odd disc⟩

/-- In the two existing seven-bit prime examples, the supplied suffix 7
falls in opposite branches despite both products being one modulo eight. -/
theorem controls : menu 3 (71*79)={3,5} ∧ 71%8∉menu 3 (71*79) ∧
    menu 3 (71*103)={1,7} ∧ 71%8∈menu 3 (71*103) := by decide +kernel

end PrimeFactors.SingularDyadicClueSuffixes
