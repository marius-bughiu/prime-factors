import PrimeFactors.CompleteOffsetWork
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Data.Nat.Squarefree

namespace PrimeFactors.OffsetSquareSplit
open CompleteOffsetSearch CompleteOffsetWork

theorem root_identities {S d N k : ℕ} (square : S^2=4*k^2*N+d^2) :
    let A := (S+d)/2
    let B := (S-d)/2
    A+B=S ∧ A*B=N*k^2 := by
  intro A B
  have le : d≤S := by
    by_contra! lt
    have := Nat.pow_lt_pow_left lt (by decide : 2≠0)
    omega
  have parity (m : ℕ) : m^2%2=m%2 := by
    rw [pow_two,Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one m with h|h <;> rw [h]
  have same : S%2=d%2 := by
    rw [←parity S,←parity d,square,show 4*k^2*N=2*(2*k^2*N) by ring]
    omega
  have sum : A+B=S := by dsimp [A,B]; omega
  have diff : A=B+d := by dsimp [A,B]; omega
  refine ⟨sum,?_⟩
  rw [←sum,diff] at square
  rw [diff]
  nlinarith only [square]

/-- Coprime positive factors of a square have positive square roots whose
product is the original root. -/
theorem square_coefficients {C L k : ℕ} (kp : 0<k) (cop : C.Coprime L) (pair : C*L=k^2) :
    ∃ s v : ℕ, 0<s ∧ 0<v ∧ k=s*v ∧ C=s^2 ∧ L=v^2 := by
  obtain ⟨s,hs⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr cop.gcd_eq_one) pair
  obtain ⟨v,hv⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr cop.symm.gcd_eq_one)
    (show L*C=k^2 by rwa [Nat.mul_comm L C])
  have eq : k=s*v := (Nat.pow_left_inj (by decide : 2≠0)).mp (by rw [←pair,hs,hv,mul_pow])
  have sp : 0<s := by by_contra! zero; simp [eq,Nat.eq_zero_of_le_zero zero] at kp
  have vp : 0<v := by by_contra! zero; simp [eq,Nat.eq_zero_of_le_zero zero] at kp
  exact ⟨s,v,sp,vp,eq,hs,hv⟩

/-- Once all of N is allocated to one root, its remaining coefficient C and
the opposite root L are coprime squares. This uses just the primitive slot. -/
private theorem concentrated {N T j k C L : ℕ} (np : 0<N) (kp : 0<k)
    (primitive : j.Coprime k) (sum : N*C+L=j+2*T*k) (prod : (N*C)*L=N*k^2) :
    ∃ s v : ℕ, 0<s ∧ k=s*v ∧ C=s^2 ∧ L=v^2 := by
  have pair : C*L=k^2 := Nat.eq_of_mul_eq_mul_left np (by rwa [←Nat.mul_assoc])
  have cop : C.Coprime L := by
    apply Nat.coprime_of_dvd
    intro p prime pc pl
    have pk := prime.dvd_of_dvd_pow (show p ∣ k^2 from pair ▸ dvd_mul_of_dvd_left pc L)
    have ds : p ∣ j+2*T*k := sum ▸ dvd_add (dvd_mul_of_dvd_right pc N) pl
    have pj := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right pk (2*T))).mpr ds
    exact prime.not_dvd_one (primitive.gcd_eq_one ▸ Nat.dvd_gcd pj pk)
  obtain ⟨s,v,sp,_,eq,hs,hv⟩ := square_coefficients kp cop pair
  exact ⟨s,v,sp,eq,hs,hv⟩

/-- A trivial lower-root gcd forces a representation of the offset by
x²+h s² with s positive. No squarefreeness hypothesis is needed on N. -/
theorem trivial_representation {N T h j k d : ℕ} (digits : N=T^2+h) (np : 0<N)
    (kp : 0<k) (primitive : j.Coprime k) (square : (j+2*T*k)^2=4*k^2*N+d^2)
    (trivial : let g := N.gcd ((j+2*T*k-d)/2); g=1 ∨ g=N) :
    ∃ s v : ℕ, 0<s ∧ k=s*v ∧ (j:ℤ)=((T:ℤ)*s-v)^2+(h:ℤ)*s^2 := by
  let A := (j+2*T*k+d)/2
  let B := (j+2*T*k-d)/2
  obtain ⟨sum,prod⟩ := root_identities square
  change A+B=j+2*T*k at sum
  change A*B=N*k^2 at prod
  change N.gcd B=1 ∨ N.gcd B=N at trivial
  have finish (C L : ℕ) (hsum : N*C+L=j+2*T*k) (hprod : (N*C)*L=N*k^2) :
      ∃ s v : ℕ, 0<s ∧ k=s*v ∧ (j:ℤ)=((T:ℤ)*s-v)^2+(h:ℤ)*s^2 := by
    obtain ⟨s,v,sp,eq,hs,hv⟩ := concentrated np kp primitive hsum hprod
    refine ⟨s,v,sp,eq,?_⟩
    rw [digits,hs,hv,eq] at hsum
    zify at hsum
    nlinarith only [hsum]
  rcases trivial with one|whole
  · have da : N∣A := (show N.Coprime B from one).dvd_of_dvd_mul_right
      (show N∣A*B from prod ▸ dvd_mul_right N _)
    obtain ⟨C,eq⟩ := da
    exact finish C B (eq ▸ sum) (eq ▸ prod)
  · obtain ⟨C,eq⟩ := (show N∣B from whole ▸ Nat.gcd_dvd_right N B)
    exact finish C A (by rw [←eq, Nat.add_comm B A]; exact sum)
      (by rw [←eq,Nat.mul_comm B A]; exact prod)

/-- On a squarefree input the two integral roots are themselves coprime. -/
theorem roots_coprime {N T j k A B : ℕ} (sf : Squarefree N) (primitive : j.Coprime k)
    (sum : A+B=j+2*T*k) (prod : A*B=N*k^2) : A.Coprime B := by
  apply Nat.coprime_of_dvd
  intro p prime pa pb
  by_cases pk : p∣k
  · have ps := sum ▸ dvd_add pa pb
    have pj := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right pk (2*T))).mpr ps
    exact prime.not_dvd_one (primitive.gcd_eq_one ▸ Nat.dvd_gcd pj pk)
  · have cop := prime.coprime_iff_not_dvd.mpr pk
    have div : p^2 ∣ N*k^2 := prod ▸ (show p^2 ∣ A*B by simpa [pow_two] using mul_dvd_mul pa pb)
    have pn := ((cop.pow_left 2).pow_right 2).dvd_of_dvd_mul_right div
    exact Nat.squarefree_iff_prime_squarefree.mp sf p prime (by simpa [pow_two] using pn)

/-- Given the signed discriminant as an actual square, the guarded executable
returns exactly the lower-root gcd if it is proper. -/
theorem probe_at_square {N T j k d : ℕ} (square : (j+2*T*k)^2=4*k^2*N+d^2) :
    let g := N.gcd ((j+2*T*k-d)/2)
    probe N T j k=if 1<g ∧ g<N then some g else none := by
  dsimp only
  unfold probe
  dsimp only
  have target : 4*k^2*N≤(j+2*T*k)^2 := by omega
  have gap : (j+2*T*k)^2-4*k^2*N=d^2 := by omega
  simp only [gap,Nat.sqrt_eq',target,eq_self,true_and]

theorem failed_iff {N T j k d : ℕ} (np : 0<N) (square : (j+2*T*k)^2=4*k^2*N+d^2) :
    let g := N.gcd ((j+2*T*k-d)/2)
    probe N T j k=none ↔ g=1 ∨ g=N := by
  intro g
  rw [probe_at_square square]
  change (if 1<g ∧ g<N then some g else none)=none ↔ _
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ np
  have cap : g≤N := Nat.le_of_dvd np (Nat.gcd_dvd_left ..)
  split <;> simp_all <;> omega

/-- Every primitive square below h yields a proper divisor, for any N. -/
theorem split_of_small_square {N T h j k d : ℕ} (digits : N=T^2+h) (np : 0<N) (kp : 0<k)
    (primitive : j.Coprime k) (short : j<h) (square : (j+2*T*k)^2=4*k^2*N+d^2) :
    ∃ f, probe N T j k=some f ∧ 1<f ∧ f<N ∧ f∣N := by
  cases found : probe N T j k with
  | some f => exact ⟨f, rfl, probe_sound found⟩
  | none =>
    obtain ⟨s,v,sp,_,eq⟩ := trivial_representation digits np kp primitive square ((failed_iff np square).mp found)
    have ss : 1≤(s:ℤ)^2 := by exact_mod_cast (Nat.one_le_pow _ _ sp)
    have mul := mul_le_mul_of_nonneg_left ss (show 0≤(h:ℤ) by positivity)
    zify at short
    nlinarith only [eq,mul,short,sq_nonneg ((T:ℤ)*s-v)]

/-- The sharp search height is already strictly below h whenever h≥2. -/
theorem sharp_split {N T h j k d : ℕ} (digits : N=T^2+h) (large : 2≤h) (kp : 0<k)
    (primitive : j.Coprime k) (sharp : 3*j^2≤4*h) (square : (j+2*T*k)^2=4*k^2*N+d^2) :
    ∃ f, probe N T j k=some f ∧ 1<f ∧ f<N ∧ f∣N := by
  apply split_of_small_square digits (by omega) kp primitive _ square
  by_contra! bad
  nlinarith only [sharp,Nat.pow_le_pow_left bad 2,Nat.mul_le_mul_right h large,large]

/-- The exceptional slot exists, has square gap one, and returns no factor. -/
theorem one_exception (T : ℕ) (tp : 0<T) :
    (1,T)∈slots T 1 ∧ (1+2*T*T)^2=4*T^2*(T^2+1)+1^2 ∧ probe (T^2+1) T 1 T=none := by
  have eq : (1+2*T*T)^2=4*T^2*(T^2+1)+1^2 := by ring
  refine ⟨mem_slots.mpr ⟨⟨by decide,by decide⟩,⟨tp,by simp⟩,Nat.coprime_one_left _⟩,eq,?_⟩
  apply (failed_iff (by positivity) eq).mpr
  left
  rw [show (1+2*T*T-1)/2=T^2 by rw [show 1+2*T*T-1=2*T^2 by rw [Nat.add_sub_cancel_left]; ring];simp]
  exact (Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)).gcd_eq_one

/-- On the h=1 sharp schedule this is the unique primitive square hit with
trivial gcd. In particular every other primitive square splits the input. -/
theorem failed_iff_one_exception {T j k d : ℕ} (tp : 0<T) (jp : 0<j) (kp : 0<k)
    (primitive : j.Coprime k) (sharp : 3*j^2≤4) (square : (j+2*T*k)^2=4*k^2*(T^2+1)+d^2) :
    probe (T^2+1) T j k=none ↔ j=1 ∧ k=T ∧ d=1 := by
  constructor
  · intro fail
    have jo : j=1 := by
      by_contra! bad
      have ge : 2≤j := by omega
      nlinarith only [sharp,Nat.pow_le_pow_left ge 2]
    subst j
    obtain ⟨s,v,sp,sv,eq⟩ := trivial_representation rfl (by positivity) kp primitive square
      ((failed_iff (by positivity) square).mp fail)
    have so : s=1 := by
      by_contra! bad
      have ge : 2≤s := by omega
      have sq : (4:ℤ)≤(s:ℤ)^2 := by exact_mod_cast (Nat.pow_le_pow_left ge 2)
      push_cast at eq
      nlinarith only [sq,eq,sq_nonneg ((T:ℤ)*s-v)]
    subst s
    push_cast at eq
    simp only [one_mul,mul_one,one_pow] at eq sv
    have vt : v=T := by
      have bz : ((T:ℤ)-v)^2=0 := by linarith only [eq]
      have := pow_eq_zero bz
      omega
    subst v
    subst k
    have dd : d^2=1^2 := by nlinarith only [square]
    exact ⟨rfl,rfl,(Nat.pow_left_inj (by decide : 2≠0)).mp dd⟩
  · rintro ⟨hj,hk,_⟩
    rw [hj,hk]
    exact (one_exception T tp).2.2

end PrimeFactors.OffsetSquareSplit
