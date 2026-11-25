import PrimeFactors.OffsetProjectiveSlopes
import PrimeFactors.PersistentLocalSurvivors

namespace PrimeFactors.OffsetTraceImage

/-- Over any modular ring where both coordinates are invertible, the entire
trace and signed-gap image is the same conic scaled by k=sv. -/
theorem normalize_signed {R : Type*} [CommRing R] {s v si vi N S z : R}
    (hs : s*si=1) (hv : v*vi=1) :
    (∃ p q : R, p*q=N ∧ S=s^2*p+v^2*q ∧ z=s^2*p-v^2*q) ↔
    (∃ x y : R, x*y=N ∧ S=(s*v)*(x+y) ∧ z=(s*v)*(x-y)) := by
  constructor
  · rintro ⟨p,q,pq,tr,gap⟩
    refine ⟨s*vi*p,v*si*q,?_,?_,?_⟩
    · calc _ = (s*si)*(v*vi)*(p*q) := by ring
           _ = N := by rw [hs,hv,pq]; ring
    · linear_combination tr - s^2*p*hv - v^2*q*hs
    · linear_combination gap - s^2*p*hv + v^2*q*hs
  · rintro ⟨x,y,xy,tr,gap⟩
    refine ⟨si*v*x,vi*s*y,?_,?_,?_⟩
    · calc _ = (s*si)*(v*vi)*(x*y) := by ring
           _ = N := by rw [hs,hv,xy]; ring
    · linear_combination tr - (s*v*x)*hs - (s*v*y)*hv
    · linear_combination gap - (s*v*x)*hs + (s*v*y)*hv

/-- At a nonexceptional prime the fixed-coordinate trace filter is exactly
the existing finite projective-slope filter. -/
theorem projective_iff {ℓ : ℕ} [Fact ℓ.Prime] (odd : ℓ≠2) {s v N j T : ZMod ℓ}
    (hs : s≠0) (hv : v≠0) (hn : N≠0) :
    (∃ p q : ZMod ℓ, p*q=N ∧ j+2*T*(s*v)=s^2*p+v^2*q) ↔
    some (j/(s*v)) ∈ OffsetProjectiveSlopes.localSlopes ℓ N T := by
  rw [OffsetProjectiveSlopes.finite_mem_iff odd hn,←admissibleSum_iff_isSquare odd]
  have hk := mul_ne_zero hs hv
  constructor
  · rintro ⟨p,q,pq,tr⟩
    obtain ⟨x,y,xy,sum,_⟩ := (normalize_signed (mul_inv_cancel₀ hs) (mul_inv_cancel₀ hv)).mp
      ⟨p,q,pq,tr,(rfl : s^2*p-v^2*q=s^2*p-v^2*q)⟩
    refine ⟨x,y,xy,?_⟩
    field_simp [hk]
    linear_combination -sum
  · rintro ⟨x,y,xy,sum⟩
    have tr : j+2*T*(s*v)=(s*v)*(x+y) := by
      rw [sum]; field_simp [hk]
    obtain ⟨p,q,pq,sum',_⟩ := (normalize_signed (mul_inv_cancel₀ hs) (mul_inv_cancel₀ hv)).mpr
      ⟨x,y,xy,tr,(rfl : (s*v)*(x-y)=(s*v)*(x-y))⟩
    exact ⟨p,q,pq,sum'⟩

/-- When both coordinates and 2 are units, the signed-square test yields
a local factor label, at arbitrary composite moduli or prime powers. -/
theorem square_iff_label {m : ℕ} {s v S N : ZMod m} (two : IsUnit (2:ZMod m))
    (su : IsUnit s) (vu : IsUnit v) :
    (∃ p q : ZMod m, p*q=N ∧ S=s^2*p+v^2*q) ↔ IsSquare (S^2-4*(N*(s*v)^2)) := by
  rw [←admissibleSum_iff_isSquare_of_two_unit two]
  obtain ⟨si,hs⟩ := su.exists_right_inv
  obtain ⟨vi,hv⟩ := vu.exists_right_inv
  constructor
  · rintro ⟨p,q,pq,tr⟩
    refine ⟨s^2*p,v^2*q,?_,tr.symm⟩
    rw [←pq]; ring
  · rintro ⟨x,y,prod,sum⟩
    refine ⟨si^2*x,vi^2*y,?_,?_⟩
    · calc _ = si^2*vi^2*(x*y) := by ring
           _ = N*(s*si)^2*(v*vi)^2 := by rw [prod]; ring
           _ = N := by rw [hs,hv]; ring
    · calc S = (s*si)^2*x+(v*vi)^2*y := by rw [hs,hv]; simpa using sum.symm
           _ = _ := by ring

/-- Taking residues of the trivial factorization (1,N) gives an explicit
survivor in every unrestricted coordinate for every integer modulus and
any number of shifts by that modulus. -/
theorem unlimited (m : ℕ) (N T s v t : ℤ) :
    let j := s^2+N*v^2-2*T*(s*v)+m*t
    let S : ZMod m := ((j+2*T*(s*v) : ℤ) : ZMod m)
    S=(s:ZMod m)^2+(N:ZMod m)*(v:ZMod m)^2 ∧
    S^2-4*(N:ZMod m)*(s*v)^2=((s:ZMod m)^2-(N:ZMod m)*v^2)^2 := by
  dsimp only
  push_cast
  simp only [ZMod.natCast_self,zero_mul,add_zero,sub_add_cancel]
  exact ⟨True.intro,by ring⟩

/-- At any prime, at least (p−3)/2 first digits already certify a square
discriminant at *every* precision. The case n=0 mod p has p−1 such digits. -/
private theorem stable_digits {p : ℕ} [Fact p.Prime] (odd : p≠2) (n : ℤ) :
    ∃ A : Finset (ZMod p), (p-3)/2≤A.card ∧ ∀ x : ℤ, (x:ZMod p)∈A →
      ∀ e : ℕ, IsSquare ((x^2-n : ℤ) : ZMod (p^e)) := by
  by_cases zero : (n:ZMod p)=0
  · refine ⟨Finset.univ.erase 0,?_,?_⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,ZMod.card]
      omega
    · intro x member
      have nz := (Finset.mem_erase.mp member).1
      have reg : ((x^2-n:ℤ) : ZMod p)≠0 := by simpa [zero] using pow_ne_zero 2 nz
      intro e
      cases e with
      | zero => rw [pow_zero]; exact ⟨0,Subsingleton.elim _ _⟩
      | succ e =>
        apply (isSquare_primePow_iff_of_unit odd _ reg e).mpr
        exact ⟨(x:ZMod p),by simp [zero,pow_two]⟩
  · exact ⟨PersistentLocalSurvivors.regularLanes p (n:ZMod p),
      PersistentLocalSurvivors.regular_lane_count odd _ zero,
      fun x member => PersistentLocalSurvivors.regular_lane_lifts odd n x zero member⟩

private theorem affine_digits {p : ℕ} [Fact p.Prime] (odd : p≠2) (a d n : ℤ)
    (step : (d:ZMod p)≠0) :
    ∃ B : Finset (ZMod p), (p-3)/2≤B.card ∧ ∀ i : ℕ, (i:ZMod p)∈B →
      ∀ e : ℕ, IsSquare (((a+d*i)^2-n : ℤ) : ZMod (p^e)) := by
  obtain ⟨A,count,good⟩ := stable_digits odd n
  refine ⟨A.image (fun x => (x-a)/d),?_,?_⟩
  · rwa [Finset.card_image_of_injective _ (fun x y eq => sub_left_inj.mp ((div_left_inj' step).mp eq))]
  · intro i member
    obtain ⟨x,hx,same⟩ := Finset.mem_image.mp member
    have eq := (div_eq_iff step).mp same
    apply good
    have target : ((a+d*i : ℤ) : ZMod p)=x := by push_cast; linear_combination -eq
    rwa [target]

/-- Lower bound on every finite arithmetic progression, for any list of odd
primes and even for adaptively chosen precisions at those primes. The step
must be nonzero at each selected prime. -/
theorem interval_floor (P : Finset ℕ) (W : ℕ) (a d n : ℤ)
    (pr : ∀ p∈P, p.Prime ∧ p≠2) (step : ∀ p∈P,(d:ZMod p)≠0) :
    W/(∏ p∈P,p)*(∏ p∈P,(p-3)/2) ≤ Nat.card {i : Fin W //
      ∀ p∈P, ∀ e : ℕ, IsSquare (((a+d*i.val)^2-n : ℤ) : ZMod (p^e))} := by
  classical
  let I := {p // p∈P}
  have prime (i : I) := (pr i.val i.property).1
  have build (i : I) := @affine_digits i.val ⟨prime i⟩ (pr i.val i.property).2 a d n
    (step i.val i.property)
  choose B count good using build
  have cp : Pairwise (fun i j : I => i.val.Coprime j.val) := fun i j ne =>
    (Nat.coprime_primes (prime i) (prime j)).mpr (fun same => ne (Subtype.ext same))
  have bound := PersistentLocalSurvivors.full_period_product (fun i : I => i.val)
    (fun i => (prime i).pos) cp B 0 W
  simp only [Nat.zero_add] at bound
  have per : (∏ i : I, i.val) = ∏ p∈P,p := (Finset.prod_subtype (p:=fun i : ℕ => i∈P) P (fun _ => Iff.rfl) id).symm
  have cnt : (∏ i : I, (i.val-3)/2) = ∏ p∈P,(p-3)/2 := (Finset.prod_subtype (p:=fun i : ℕ => i∈P) P (fun _ => Iff.rfl) (fun i => (i-3)/2)).symm
  rw [per] at bound
  rw [←cnt]
  refine (Nat.mul_le_mul_left _ (Finset.prod_le_prod' (fun i _ => count i))).trans (bound.trans ?_)
  apply Nat.card_le_card_of_injective (fun i => ⟨i.val,fun p hp e =>
    good ⟨p,hp⟩ i.val.val (i.property ⟨p,hp⟩) e⟩)
  intro x y eq
  exact Subtype.ext (Subtype.mk.inj eq)

noncomputable def wheel379 : Finset ℕ := (Finset.range 380).filter (fun p => 5≤p ∧ p.Prime)

private theorem wheel_size :
    2^428+1 < (2^508/(∏ p∈wheel379,p))*(∏ p∈wheel379,(p-3)/2) := by decide +kernel

/-- For every trace interval of at least 2^508 entries on a coprime step,
even all powers of all primes from 5 to 379 leave more than 2^428 traces
after discounting one true oriented factor pair. -/
theorem long_chart {W : ℕ} (size : 2^508≤W) (a d n : ℤ)
    (step : ∀ p∈wheel379,(d:ZMod p)≠0) :
    2^428+1 < Nat.card {i : Fin W // ∀ p∈wheel379, ∀ e : ℕ,
      IsSquare (((a+d*i.val)^2-n : ℤ) : ZMod (p^e))} := by
  have pr (p : ℕ) (hp : p∈wheel379) : p.Prime ∧ p≠2 := by
    have h := (Finset.mem_filter.mp hp).2
    exact ⟨h.2,by omega⟩
  exact wheel_size.trans_le ((Nat.mul_le_mul_right _ (Nat.div_le_div_right size)).trans
    (interval_floor wheel379 W a d n pr step))

/-- The finite count underlying the additional coprimality calculation:
2^508 entries contain 1108 full periods through 373, and each full
residue track can lose the displayed union bound for prime divisors of k. -/
noncomputable def wheel373 : Finset ℕ := (Finset.range 374).filter (fun p => 5≤p ∧ p.Prime)

theorem primitive_constants :
    2^508/(∏ p∈wheel373,p)=1108 ∧
    2^428+1 < (1108-(1108/3+1)-64*(1108/374+1))*(∏ p∈wheel373,(p-3)/2) := by
  decide +kernel

/-- Count occurrences of one specified residue in a bounded interval. -/
theorem residue_count (L p r : ℕ) :
    ((Finset.range L).filter (fun i => i%p=r%p)).card≤L/p+1 := by
  let used := (Finset.range L).filter (fun i => i%p=r%p)
  have into : ∀ i∈used,i/p∈Finset.range (L/p+1) := by
    intro i hi
    have lt := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right lt.le))
  have inj : Set.InjOn (fun i => i/p) (used : Set ℕ) := by
    intro i hi j hj eq
    have residues := (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    have combine := Nat.mod_add_div i p
    change i/p=j/p at eq
    rw [residues,eq,Nat.mod_add_div] at combine
    exact combine.symm
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn (fun i => i/p) into inj

/-- In 1108 repeats of one wheel residue, removing one class modulo 3
and one class at each of at most 64 moduli above 373 leaves 546 entries. -/
theorem primitive_repeats (P : Finset ℕ) (r : ℕ → ℕ) (few : P.card≤64)
    (large : ∀ p∈P,374≤p) :
    let bad := fun p => (Finset.range 1108).filter (fun i => i%p=r p%p)
    546≤((Finset.range 1108) \ (bad 3 ∪ P.biUnion bad)).card := by
  intro bad
  have single (p : ℕ) (hp : p∈P) : (bad p).card≤3 := by
    have quot : 1108/p≤1108/374 := Nat.div_le_div_left (large p hp) (by decide)
    exact (residue_count ..).trans (by omega)
  have many : (P.biUnion bad).card≤P.card*3 := calc
    _ ≤ ∑ p∈P, (bad p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p∈P, (3:ℕ) := Finset.sum_le_sum single
    _ = _ := by simp
  have small : (bad 3).card≤370 := residue_count 1108 3 (r 3)
  have union := Finset.card_union_le (bad 3) (P.biUnion bad)
  have left := Finset.card_le_card_sdiff_add_card (s:=Finset.range 1108) (t:=bad 3 ∪ P.biUnion bad)
  rw [Finset.card_range] at left
  omega

theorem large_prime_divisors {k : ℕ} (positive : 0<k) (cap : k≤2^513) :
    (k.primeFactors.filter (fun p => 373<p)).card≤64 := by
  let P := k.primeFactors.filter (fun p => 373<p)
  have less := Finset.prod_le_prod' (s:=P) (f:=fun _ : ℕ => 256) (g:=fun p : ℕ => p)
    (fun p hp => (show 256 ≤ p by have := (Finset.mem_filter.mp hp).2; omega))
  rw [Finset.prod_const] at less
  have divides : (∏ p∈P,p) ∣ ∏ p∈k.primeFactors,p :=
    Finset.prod_dvd_prod_of_subset P k.primeFactors id (Finset.filter_subset ..)
  have upper := less.trans (Nat.le_of_dvd positive (divides.trans (Nat.prod_primeFactors_dvd k)))
  by_contra! many
  have bigger := Nat.pow_le_pow_right (by decide : 0<256) (show 65≤P.card from many)
  exact (not_le_of_gt (by decide +kernel : (2:ℕ)^513<256^65)) (bigger.trans (upper.trans cap))

end PrimeFactors.OffsetTraceImage
