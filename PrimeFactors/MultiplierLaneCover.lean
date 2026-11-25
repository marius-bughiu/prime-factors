import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors.MultiplierLaneCover
open Finset
set_option exponentiation.threshold 4096

/-- Assigning one factor 3 gives two public ways to lift the original pair. -/
theorem three_lifts (p q : ℤ) :
    (3*p)*q=3*(p*q) ∧ p*(3*q)=3*(p*q) := by constructor <;> ring

/-- Count every covered oriented residue only once, even when different
public multipliers coincide modulo the radix or induce overlapping sets. -/
theorem cover_card {G : Type*} [Group G] [DecidableEq G] (A V S : Finset G)
    (cover : ∀ s ∈ S, ∃ a ∈ A, a*s ∈ V) : S.card ≤ A.card*V.card := by
  have subset : S ⊆ A.biUnion (fun a => V.image (fun v => a⁻¹*v)) := by
    intro s hs
    obtain ⟨a,ha,hv⟩ := cover s hs
    exact mem_biUnion.mpr ⟨a,ha,mem_image.mpr ⟨a*s,hv,by simp⟩⟩
  exact (card_le_card subset).trans (card_biUnion_le_card_mul _ _ _ (fun _ _ => card_image_le))

/-- One representative for each consecutive two vertices of the folded path.
The last anchor lies on the last vertex when the vertex count is odd. -/
noncomputable def anchors (n : ℕ) : Finset ℕ :=
  (range ((n+1)/2)).image (fun t => min (2*t+1) (n-1))

theorem anchors_card (n : ℕ) : (anchors n).card ≤ (n+1)/2 :=
  (card_image_le.trans (card_range _).le)

theorem covers_vertex {n j : ℕ} (within : j<n) :
    ∃ a ∈ anchors n, a=j ∨ a=j+1 := by
  let t := j/2
  have bound : t < (n+1)/2 := by dsimp [t]; omega
  exact ⟨_,mem_image.mpr ⟨t,mem_range.mpr bound,rfl⟩,by dsimp [t]; omega⟩

/-- In exponent coordinates the signed unit group has period 2L, and factor
exchange sends i to k-i. Their quotient is covered by successive exponents
starting at ceil(k/2). This handles both parities and the fixed endpoints. -/
theorem folded_path (i k : ℤ) {L : ℕ} (pos : 0<L) :
    let start := (k+1)/2
    let count := L+1-(k%2).toNat
    ∃ j<count, i ≡ start+j [ZMOD 2*L] ∨ k-i ≡ start+j [ZMOD 2*L] := by
  let start := (k+1)/2
  let M : ℤ := 2*L
  let r := (i-start)%M
  let q := (i-start)/M
  have Mpos : 0<M := by dsimp [M]; omega
  have lr : 0≤r := Int.emod_nonneg _ Mpos.ne'
  have ur : r<M := Int.emod_lt_of_pos _ Mpos
  have eqn : r+M*q=i-start := Int.emod_add_ediv ..
  have parity : 2*start=k+k%2 := by dsimp [start]; omega
  have hpar : 0≤k%2 := Int.emod_nonneg _ (by decide)
  have bpar : k%2<2 := Int.emod_lt_of_pos _ (by decide)
  change ∃ j<L+1-(k%2).toNat, i ≡ start+j [ZMOD M] ∨ k-i ≡ start+j [ZMOD M]
  by_cases small : r ≤ (L:ℤ)-k%2
  · refine ⟨r.toNat,by omega,Or.inl (Int.modEq_iff_dvd.mpr ⟨-q,?_⟩)⟩
    rw [Int.toNat_of_nonneg lr]
    linarith only [eqn]
  · have other : 0 ≤ M-r-k%2 := by omega
    refine ⟨(M-r-k%2).toNat,by dsimp [M] at *; omega, Or.inr (Int.modEq_iff_dvd.mpr ⟨q+1,?_⟩)⟩
    rw [Int.toNat_of_nonneg other]
    linarith only [eqn,parity]

/-- The signed powers of 3 gain one bit of multiplicative period per
doubling: 3^(2^(j+1)) - 1 is 2^(j+3) times an odd integer. -/
theorem three_lift (j : ℕ) :
    ∃ a : ℕ, 3^(2^(j+1)) = 1 + 2^(j+3)*(2*a+1) := by
  induction j with
  | zero => exact ⟨0,by decide⟩
  | succ j ih =>
    obtain ⟨a,h⟩ := ih
    refine ⟨a+2*2^j*(2*a+1)^2,?_⟩
    rw [show 2^(j+1+1)=2^(j+1)*2 by ring, pow_mul, h]
    ring

private theorem lift_choice {n r M w : ℤ} (old : n ≡ r [ZMOD M])
    (odd : Odd r) (a : ℤ) (flip : w=1+M*(2*a+1)) :
    n ≡ r [ZMOD 2*M] ∨ n ≡ r*w [ZMOD 2*M] := by
  obtain ⟨q,hq⟩ := old.dvd
  rcases Int.even_or_odd q with ⟨v,hv⟩ | ⟨v,hv⟩
  · rw [hv] at hq
    exact Or.inl (Int.modEq_iff_dvd.mpr ⟨v,by linarith only [hq]⟩)
  · obtain ⟨h,hr⟩ := odd
    rw [hv,hr] at hq
    apply Or.inr
    refine Int.modEq_iff_dvd.mpr ⟨v+1+2*h*a+h+a,?_⟩
    rw [hr,flip]
    linarith only [hq]

/-- Every odd residue modulo 2^(e+3) has a signed power-of-three representative.
The proof lifts a representative by either keeping the same exponent or adding
2^(e+1), which also gives a digit-by-digit algorithm for its discrete log. -/
theorem signed_power (n : ℤ) (odd : Odd n) (e : ℕ) :
    ∃ j<2^(e+1), n ≡ (3:ℤ)^j [ZMOD 2^(e+3)] ∨ n ≡ -(3:ℤ)^j [ZMOD 2^(e+3)] := by
  induction e with
  | zero =>
    obtain ⟨v,hv⟩ := odd
    have h : n%8=1 ∨ n%8=7 ∨ n%8=3 ∨ n%8=5 := by omega
    rcases h with p|p|p|p
    · exact ⟨0,by decide,Or.inl (by simpa [Int.ModEq] using p)⟩
    · exact ⟨0,by decide,Or.inr (by simpa [Int.ModEq] using p)⟩
    · exact ⟨1,by decide,Or.inl (by simpa [Int.ModEq] using p)⟩
    · exact ⟨1,by decide,Or.inr (by simpa [Int.ModEq] using p)⟩
  | succ e ih =>
    obtain ⟨j,hj,old⟩ := ih
    obtain ⟨a,ha⟩ := three_lift e
    have flip : (3:ℤ)^(2^(e+1))=1+2^(e+3)*(2*(a:ℤ)+1) := by exact_mod_cast ha
    have lift (s : ℤ) (os : Odd s) (old : n ≡ s*3^j [ZMOD 2^(e+3)]) :
        ∃ t<2^(e+1+1), n ≡ s*3^t [ZMOD 2^(e+1+3)] := by
      have o3 : Odd (3:ℤ) := ⟨1,by decide⟩
      rcases lift_choice old (os.mul (o3.pow)) a flip with same | next
      · refine ⟨j,by rw [pow_succ]; omega,?_⟩
        rwa [show (2:ℤ)^(e+1+3)=2*2^(e+3) by ring]
      · refine ⟨j+2^(e+1),by rw [pow_succ]; omega,?_⟩
        rw [show (2:ℤ)^(e+1+3)=2*2^(e+3) by ring,pow_add (3:ℤ) j]
        simpa only [mul_assoc] using next
    rcases old with plus|minus
    · obtain ⟨t,ht,h⟩ := lift 1 (by decide) (by simpa using plus)
      exact ⟨t,ht,Or.inl (by simpa using h)⟩
    · obtain ⟨t,ht,h⟩ := lift (-1) (by decide) (by simpa using minus)
      exact ⟨t,ht,Or.inr (by simpa using h)⟩

/-- A concrete exponent ledger for a 2048-bit product. In both rows the
factor of three is inside the proved full-size LLL budget. The preceding
radix is insufficient even before including the multiplier in this estimate. -/
theorem retained_scales (m e : ℕ) (case : (m=4 ∧ e=571) ∨ (m=8 ∧ e=544)) :
    let d := 2*m+1
    let k := m*(m+1)
    d^d*2^(m*d)*3^(2*k)*2^(2049*k) < 2^(e*(2*m*d)) ∧
    2^((e-1)*(2*m*d)) ≤ d^d*2^(m*d)*2^(2049*k) := by
  rcases case with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel

/-- At degree 4096, compare exponents without constructing a billion-bit power.
Use 2^12 < 4097 < 2^13 and 2^3 < 3² < 2^4 to sandwich the scaled determinant. -/
theorem degree_4096 :
    let m : ℕ := 2048
    let d := 2*m+1
    let h := m*(m+1)
    2^12<d ∧ d<2^13 ∧ 2^3<3^2 ∧ 3^2<2^4 ∧
    512*(2*m*d) ≤ 12*d+m*d+2049*h ∧ 13*d+m*d+2049*h < 513*(2*m*d) ∧
    513*(2*m*d) ≤ 12*d+m*d+2052*h ∧ 13*d+m*d+2053*h < 514*(2*m*d) := by
  decide +kernel

end PrimeFactors.MultiplierLaneCover
