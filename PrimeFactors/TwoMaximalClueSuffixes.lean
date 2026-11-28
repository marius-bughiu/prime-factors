import PrimeFactors.DyadicFactorClueGain
import PrimeFactors.FactorClueSumGap
import PrimeFactors.HighLowSumPopulation
import PrimeFactors.LocalMidpointLanes

/-! Inverting the maximum-precision criterion: at a fixed odd product,
which public factor suffixes would force a sum modulo 2^(2k+1)? -/
namespace PrimeFactors.TwoMaximalClueSuffixes

open Finset FactorClueSumPrecision
open private PrimeFactors.DyadicFactorClueGain.cap_pow from PrimeFactors.DyadicFactorClueGain
open private PrimeFactors.LocalMidpointLanes.odd_square from PrimeFactors.LocalMidpointLanes

/-- All length-k suffixes solving the congruence given by the public product. -/
noncomputable def menu (k N : ℕ) : Finset ℕ :=
  (range (2^k)).filter (fun a => N ≡ a^2+2^k [MOD 2^(k+1)])

theorem mem_menu {k N a : ℕ} : a∈menu k N ↔ a<2^k ∧ N ≡ a^2+2^k [MOD 2^(k+1)] := by
  simp only [menu,mem_filter,mem_range]

/-- Integer subtraction avoids truncation when N is smaller than 2^k. -/
theorem mem_square {k N a : ℕ} : a∈menu k N ↔ a<2^k ∧
    (a:ℤ)^2 ≡ (N:ℤ)-2^k [ZMOD (2:ℤ)^(k+1)] := by
  rw [mem_menu,←Int.natCast_modEq_iff]
  push_cast
  rw [Int.modEq_iff_dvd,Int.modEq_iff_dvd,
    show (N:ℤ)-2^k-a^2 = -(a^2+2^k-N) by ring,Int.dvd_neg]

private theorem unit_of_mem {k N a : ℕ} (pos : 0<k) (odd : Odd N) (h : a∈menu k N) :
    Odd a := by
  have dv : 2∣(2:ℕ)^k := dvd_pow_self _ pos.ne'
  have eq := (mem_menu.mp h).2.of_dvd (dvd_pow_self 2 (Nat.succ_ne_zero k))
  change N%2=(a^2+2^k)%2 at eq
  rw [Nat.odd_iff.mp odd,Nat.add_mod,Nat.mod_eq_zero_of_dvd dv,add_zero,Nat.pow_mod] at eq
  apply Nat.odd_iff.mpr
  by_contra! bad
  have zero : a%2=0 := by omega
  simp [zero] at eq

private theorem max_iff {k N a : ℕ} (pos : 0<k) (odd : Odd a) :
    greatest N a (2^k)=2^(2*k+1) ↔ N ≡ a^2+2^k [MOD 2^(k+1)] := by
  have cap : greatest N a (2^k)∣2^(k+(k+1)) := by
    rw [←PrimeFactors.DyadicFactorClueGain.cap_pow pos]
    exact Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..)
  have iff : greatest N a (2^k)=2^(k+(k+1)) ↔ 2^(k+(k+1))∣greatest N a (2^k) :=
    ⟨fun eq => eq ▸ dvd_rfl,fun dv => Nat.dvd_antisymm cap dv⟩
  rw [show 2*k+1=k+(k+1) by omega,iff,DyadicFactorClueGain.precision_iff pos]
  simp only [le_refl,true_and]
  obtain ⟨v,hv⟩ := odd
  have term : a*2^k ≡ 2^k [MOD 2^(k+1)] := by
    rw [show a*2^k=2^k+v*2^(k+1) by rw [hv,pow_succ]; ring]
    simp [Nat.ModEq]
  exact ⟨fun eq => eq.trans (term.add_left _),fun eq => eq.trans (term.add_left _).symm⟩

/-- These are exactly the odd suffixes which would produce the maximum
fixed sum modulus if supplied. -/
theorem mem_maximum {k N a : ℕ} (pos : 0<k) (odd : Odd N) : a∈menu k N ↔
    a<2^k ∧ Odd a ∧ greatest N a (2^k)=2^(2*k+1) := by
  constructor
  · intro h
    obtain ⟨lo,eq⟩ := mem_menu.mp h
    have unit := unit_of_mem pos odd h
    exact ⟨lo,unit,(max_iff pos unit).mpr eq⟩
  · rintro ⟨lo,unit,eq⟩
    exact mem_menu.mpr ⟨lo,(max_iff pos unit).mp eq⟩

private theorem root_signs {k : ℕ} (kp : 1≤k) (a r : ℤ) (odd : Odd r) :
    a^2 ≡ r^2 [ZMOD (2:ℤ)^(k+1)] ↔
      a ≡ r [ZMOD (2:ℤ)^k] ∨ a ≡ -r [ZMOD (2:ℤ)^k] := by
  have result := HighLowSumPopulation.roots_iff (p:=r) (q:=-r) (a:=a) (b:=-a)
    (g:=-r) (k:=k+1) (v:=1) (by omega) (by ring) odd.neg (by ring)
  simpa only [Nat.add_sub_cancel,mul_neg,←pow_two,Int.neg_modEq_neg,
    Int.modEq_comm (a:=r^2) (b:=a^2)] using result

private def rep (k : ℕ) (z : ℤ) : ℕ := (z%(2:ℤ)^k).toNat
private theorem rep_cast (k : ℕ) (z : ℤ) : (rep k z:ℤ)=z%(2:ℤ)^k :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))

private theorem rep_lt (k : ℕ) (z : ℤ) : rep k z<2^k := by
  have := Int.emod_lt_of_pos z (by positivity : (0:ℤ)<2^k)
  rw [←rep_cast] at this
  exact_mod_cast this

private theorem rep_class (k : ℕ) (z : ℤ) : (rep k z:ℤ) ≡ z [ZMOD (2:ℤ)^k] := by
  rw [rep_cast]
  exact Int.mod_modEq ..

private theorem eq_rep {k a : ℕ} (room : a<2^k) (z : ℤ) :
    (a:ℤ) ≡ z [ZMOD (2:ℤ)^k] ↔ a=rep k z := by
  change (a:ℤ)%(2:ℤ)^k=z%(2:ℤ)^k ↔ _
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast room),←rep_cast]
  exact Int.natCast_inj

private theorem gate_of_mem {k N a : ℕ} (hk : 3≤k) (odd : Odd N) (inside : a∈menu k N) :
    N%8=1 := by
  have unit : Odd (a:ℤ) := by exact_mod_cast unit_of_mem (by omega) odd inside
  have sq := PrimeFactors.LocalMidpointLanes.odd_square unit
  have eight : (8:ℤ)∣2^k := pow_dvd_pow 2 hk
  have level : (8:ℤ)∣2^(k+1) := pow_dvd_pow 2 (by omega : 3≤k+1)
  have near := ((mem_square.mp inside).2.of_dvd level).dvd
  have fixed : (8:ℤ)∣(N:ℤ)-1 := by
    convert dvd_add (dvd_add near eight) sq using 1
    ring
  have yes := Int.modEq_iff_dvd.mpr fixed
  exact_mod_cast (show (N:ℤ)%8=1 from Eq.symm yes)

/-- For N equal to one modulo eight the menu consists of precisely two
distinct representatives, which are additive inverses modulo 2^k. -/
theorem opposite_pair {k N : ℕ} (hk : 3≤k) (gate : N%8=1) :
    ∃ a b : ℕ, a≠b ∧ (a:ℤ)+b ≡ 0 [ZMOD (2:ℤ)^k] ∧ menu k N={a,b} := by
  have eight : (8:ℤ)∣2^k := pow_dvd_pow 2 hk
  have initial : (8:ℤ)∣(N:ℤ)-1 := Int.modEq_iff_dvd.mp
    (Int.natCast_modEq_iff.mpr (show 1 ≡ N [MOD 8] from gate.symm))
  have base : (8:ℤ)∣((N:ℤ)-2^k)-1 := by
    convert dvd_sub initial eight using 1
    ring
  obtain ⟨r,odd,deep⟩ := LocalMidpointLanes.lift_eight base k
  have root : r^2 ≡ (N:ℤ)-2^k [ZMOD (2:ℤ)^(k+1)] :=
    Int.modEq_iff_dvd.mpr ((pow_dvd_pow _ (by omega : k+1≤k+3)).trans deep)
  refine ⟨rep k r,rep k (-r),?_,?_,?_⟩
  · intro same
    have collapse := (rep_class k r).symm.trans (same ▸ rep_class k (-r))
    have four := collapse.of_dvd (show (4:ℤ)∣2^k from pow_dvd_pow 2 (by omega : 2≤k))
    change r%4=(-r)%4 at four
    obtain ⟨j,eq⟩ := odd
    omega
  · simpa only [add_neg_cancel] using (rep_class k r).add (rep_class k (-r))
  · ext a
    rw [mem_square,mem_insert,mem_singleton]
    constructor
    · rintro ⟨room,hit⟩
      exact ((root_signs (by omega) a r odd).mp (hit.trans root.symm)).imp
        (eq_rep room r).mp (eq_rep room (-r)).mp
    · rintro (rfl|rfl)
      · exact ⟨rep_lt k r,((root_signs (by omega) _ r odd).mpr (Or.inl (rep_class k r))).trans root⟩
      · exact ⟨rep_lt k (-r),((root_signs (by omega) _ r odd).mpr (Or.inr (rep_class k (-r)))).trans root⟩

/-- Exact menu size for every odd product, independent of its factors. -/
theorem card_menu {k N : ℕ} (hk : 3≤k) (odd : Odd N) :
    (menu k N).card=if N%8=1 then 2 else 0 := by
  split_ifs with good
  · obtain ⟨a,b,ne,_,eq⟩ := opposite_pair hk good
    simp [eq,ne]
  · apply card_eq_zero.mpr
    exact eq_empty_of_forall_not_mem (fun a h => good (gate_of_mem hk odd h))

/-- Reading the public menu catches the true suffix precisely on the
previously characterized half-period factor-gap event. -/
theorem true_suffix {k p q : ℕ} (kp : 0<k) (po : Odd p) (qo : Odd q) :
    p%2^k∈menu k (p*q) ↔ p ≡ q+2^k [MOD 2^(k+1)] := by
  have room := Nat.mod_lt p (by positivity : 0<2^k)
  have unit : Odd (p%2^k) := Nat.odd_iff.mpr ((Nat.mod_mod_of_dvd p
    (dvd_pow_self 2 kp.ne')).trans (Nat.odd_iff.mp po))
  rw [mem_maximum kp (po.mul qo),and_iff_right room,and_iff_right unit,
    FactorClueSumGap.dyadic_maximum kp po]

/-- Two products with the same public mod-eight gate but different
outcomes for the true suffix of the same prime 71. -/
theorem controls : menu 3 (71*79)={1,7} ∧ 71%8∈menu 3 (71*79) ∧
    menu 3 (71*103)={3,5} ∧ 71%8∉menu 3 (71*103) := by decide +kernel

end PrimeFactors.TwoMaximalClueSuffixes
