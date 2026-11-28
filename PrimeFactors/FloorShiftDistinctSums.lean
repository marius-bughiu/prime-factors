import PrimeFactors.FloorShiftCenterCompression

/-! Adjacent dyadic levels share a pair of possible midpoint residues. -/
namespace PrimeFactors.FloorShiftDistinctSums

open Finset FloorShiftCenterCompression

/-- Sums contributed by the single exponent j, using the original lower-center rule. -/
noncomputable def rowSums (N b j : ℕ) : Finset ℕ :=
  (row N N.sqrt b j (sharedRoot N b)).image (fun s => 2*s+2^j)

private theorem half {j : ℕ} (jp : 1≤j) : (2:ℕ)^j=2*2^(j-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  simp [pow_succ,mul_comm]

private theorem translate (s u d : ℤ) :
    (s ≡ u+d [ZMOD 2*d] ∨ s ≡ -(u+d) [ZMOD 2*d]) ↔
    (s+d ≡ u [ZMOD 2*d] ∨ s+d ≡ -u [ZMOD 2*d]) := by
  simp only [Int.modEq_iff_dvd]
  apply or_congr
  · constructor
    · rintro ⟨v,h⟩
      exact ⟨v-1,by linear_combination h⟩
    · rintro ⟨v,h⟩
      exact ⟨v+1,by linear_combination h⟩
  · rw [show -(u+d)-s = -u-(s+d) by ring]

/-- The midpoint uses the unshifted root at every high exponent. -/
theorem midpoint_iff {N r b s j : ℕ} (odd : Odd N) (rs : r^2≤N) (sr : s≤r)
    (lo : 3≤j) (hi : j≤b) :
    let H : ℤ := s+(2:ℤ)^(j-1)
    let u := sharedRoot N b
    (N-s^2)%2^(j+1)=2^j ↔ N%8=1 ∧ (H ≡ u [ZMOD (2:ℤ)^j] ∨ H ≡ -u [ZMOD (2:ℤ)^j]) := by
  dsimp only
  have old := residue_classes odd rs sr lo hi
  dsimp only at old
  rw [old]
  apply and_congr_right
  intro _
  have eq : (2:ℤ)^j=2*2^(j-1) := by exact_mod_cast half (by omega : 1≤j)
  rw [eq]
  exact translate ..

/-- First integer strictly above r in residue class a. -/
def first (r j : ℕ) (a : ℤ) : ℕ := r+1+((a-r-1)%(2:ℤ)^j).toNat

private theorem first_eq {r j H : ℕ} {a : ℤ} (low : r<H) (high : H≤r+2^j)
    (cls : (H:ℤ) ≡ a [ZMOD (2:ℤ)^j]) : H=first r j a := by
  have eq := (cls.sub (Int.ModEq.refl (r:ℤ))).sub (Int.ModEq.refl (1:ℤ))
  change ((H:ℤ)-r-1)%(2:ℤ)^j=(a-r-1)%(2:ℤ)^j at eq
  have upper : (H:ℤ)-r-1<(2:ℤ)^j := by
    have : (H:ℤ)≤r+(2:ℤ)^j := by exact_mod_cast high
    omega
  rw [Int.emod_eq_of_lt (by omega) upper] at eq
  unfold first
  rw [←eq]
  omega

private theorem in_pair {N b j i S : ℕ} (odd : Odd N) (lo : 3≤j) (le : j≤ i)
    (near : i≤j+1) (hi : i≤b) (member : S∈rowSums N b i) :
    let r := N.sqrt
    let u := sharedRoot N b
    S∈({2*first r j u,2*first r j (-u)} : Finset ℕ) := by
  obtain ⟨s,mem,rfl⟩ := mem_image.mp member
  obtain ⟨sr,low,_,res⟩ := (mem_row odd (Nat.sqrt_le' N) (by omega) hi).mp mem
  obtain ⟨_,left|right⟩ := (midpoint_iff odd (Nat.sqrt_le' N) sr (by omega) hi).mp res
  all_goals
    have level := half (by omega : 1≤ i)
    have bound : (2:ℕ)^(i-1)≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    have bot : N.sqrt<s+2^(i-1) := by omega
    have top : s+2^(i-1)≤N.sqrt+2^j := by omega
    have ident : 2*s+2^i=2*(s+2^(i-1)) := by omega
    simp only [mem_insert,mem_singleton,ident]
  · left
    congr 1
    apply first_eq bot top
    push_cast
    exact left.of_dvd (pow_dvd_pow 2 le)
  · right
    congr 1
    apply first_eq bot top
    push_cast
    exact right.of_dvd (pow_dvd_pow 2 le)

/-- The entire union across one pair of consecutive high levels contains at most
two distinct sums even when either level individually has two centers. -/
theorem adjacent {N b j : ℕ} (odd : Odd N) (lo : 3≤j) (hi : j+1≤b) :
    (rowSums N b j ∪ rowSums N b (j+1)).card≤2 := by
  refine (card_le_card (t:={2*first N.sqrt j (sharedRoot N b),
    2*first N.sqrt j (-(sharedRoot N b))}) ?_).trans ((card_insert_le ..).trans (by simp))
  intro S mem
  rcases mem_union.mp mem with a|a
  · exact in_pair (i:=j) odd lo le_rfl (by omega) (by omega) a
  · exact in_pair (i:=j+1) odd lo (by omega) le_rfl hi a

private theorem congr_of_rem {N s j : ℕ} (sq : s^2≤N) (res : (N-s^2)%2^(j+1)=2^j) :
    N%(2^(j+1))=((s%(2^(j+1)))^2+2^j)%(2^(j+1)) := by
  have eq := Nat.mod_add_div (N-s^2) (2^(j+1))
  rw [res] at eq
  let c := (N-s^2)/2^(j+1)
  have write : N=s^2+2^j+c*2^(j+1) := by dsimp [c]; rw [mul_comm ((N-s^2)/_)]; omega
  conv_lhs => rw [write,Nat.add_mul_mod_self_right,Nat.add_mod,Nat.pow_mod]
  exact (Nat.add_mod ..).symm

private theorem small {N b j S : ℕ} (odd : Odd N) (jp : 1≤j) (low : j≤2) (hi : j≤b)
    (mem : S∈rowSums N b j) : N%8≠1 ∧ S=(if N%4=3 then 2*N.sqrt+2
      else 2*(N.sqrt-((N.sqrt+1)%2))+4) := by
  obtain ⟨s,h,rfl⟩ := mem_image.mp mem
  obtain ⟨sr,bot,_,res⟩ := (mem_row odd (Nat.sqrt_le' N) jp hi).mp h
  have eq := congr_of_rem ((Nat.pow_le_pow_left sr 2).trans (Nat.sqrt_le' N)) res
  have npar := Nat.odd_iff.mp odd
  have n2 := Nat.mod_mod_of_dvd N (show 2∣4 by decide)
  have n4 := Nat.mod_mod_of_dvd N (show 4∣8 by decide)
  have s2 := Nat.mod_mod_of_dvd s (show 2∣8 by decide)
  rcases (show j=1 ∨ j=2 by omega) with rfl|rfl
  · norm_num at eq bot ⊢
    have bound := Nat.mod_lt s (by decide : 0<4)
    generalize hx : s%4=x at eq bound
    interval_cases x <;> norm_num at eq <;> split_ifs <;> constructor <;> omega
  · norm_num at eq bot ⊢
    have bound := Nat.mod_lt s (by decide : 0<8)
    generalize hx : s%8=x at eq bound s2
    interval_cases x <;> norm_num at eq s2 <;> split_ifs <;> constructor <;> omega

/-- At odd products outside the square-unit residue modulo eight, at most one
sum survives across every exponent. -/
theorem other {N b : ℕ} (odd : Odd N) (gate : N%8≠1) : (sums N b).card≤1 := by
  refine (card_le_card (t:={if N%4=3 then 2*N.sqrt+2
    else 2*(N.sqrt-((N.sqrt+1)%2))+4}) ?_).trans (by simp)
  intro S mem
  obtain ⟨i,ib,inside⟩ := mem_biUnion.mp mem
  have hi : i+1≤b := mem_range.mp ib
  by_cases low : i+1≤2
  · exact mem_singleton.mpr (small odd (by omega) low hi inside).2
  · obtain ⟨s,valid,_⟩ := mem_image.mp inside
    obtain ⟨sr,_,_,res⟩ := (mem_row odd (Nat.sqrt_le' N) (by omega) hi).mp valid
    exact (gate ((midpoint_iff odd (Nat.sqrt_le' N) sr (by omega) hi).mp res).1).elim

/-- At width 2m+2 the two low exponents are empty and the remaining 2m
levels group into m adjacent pairs. -/
theorem even_width (m : ℕ) {N : ℕ} (odd : Odd N) (gate : N%8=1) :
    (sums N (2*m+2)).card≤2*m := by
  let b := 2*m+2
  let pair (k : ℕ) := rowSums N b (2*k+3) ∪ rowSums N b (2*k+4)
  change (sums N b).card≤2*m
  refine (card_le_card (t:=(range m).biUnion pair) ?_).trans ?_
  · intro S mem
    obtain ⟨i,ib,inside⟩ := mem_biUnion.mp mem
    have hi : i+1≤b := mem_range.mp ib
    have ih : 3≤ i+1 := by
      by_contra! bad
      exact (small odd (by omega) (by omega : i+1≤2) hi inside).1 gate
    let k := (i-2)/2
    have smallK : k<m := by dsimp [k,b] at *; omega
    refine mem_biUnion.mpr ⟨k,mem_range.mpr smallK,mem_union.mpr ?_⟩
    have choice : i+1=2*k+3 ∨ i+1=2*k+4 := by dsimp [k]; omega
    rcases choice with eq|eq
    · left; exact eq ▸ inside
    · right; exact eq ▸ inside
  · calc
      _ ≤ (range m).card*2 := card_biUnion_le_card_mul _ _ _ (fun k hk =>
        adjacent odd (by omega) (by have := mem_range.mp hk; dsimp [b]; omega))
      _ = _ := by simp [mul_comm]

theorem full_width {N : ℕ} (odd : Odd N) : (sums N 1024).card≤1022 := by
  by_cases gate : N%8=1
  · exact even_width 511 odd gate
  · exact (other odd gate).trans (by decide)

/-- Both levels generate 862 from different centers on this nine-bit example. -/
theorem repeated_sum : rowSums 141217 9 7={862} ∧ rowSums 141217 9 8={862} := by
  simp only [rowSums,show (141217:ℕ).sqrt=375 by norm_num]
  decide +kernel

end PrimeFactors.FloorShiftDistinctSums
