import PrimeFactors.ResidueCount
import Mathlib.Data.Nat.Totient

/-! Exact simultaneous residue tests for two linear combinations of factors.
Harvey's Algorithm 4.2 searches for a modular collision from any one weight
row (https://arxiv.org/abs/2010.05450). Here both rows describe the same
factor residues. The rectangle bound counts only Cartesian blocks in which
every pair must pass this stronger local test. -/

namespace PrimeFactors.WeightedCollisionReuse

open Finset

/-- With neighboring weights the gcd of the two genuine collision exponent
differences is exactly the predecessor of the first factor, in absolute value. -/
theorem residual_gcd {a b c d e : ℤ} (p q : ℤ) (inv : e*(a*d-b*c)=1) :
    Int.gcd ((a+b*(p*q))-(a*p+b*q)) ((c+d*(p*q))-(c*p+d*q))=(p-1).natAbs := by
  let g := Int.gcd (b*q-a) (d*q-c)
  have left : (g:ℤ)∣b*q-a := Int.gcd_dvd_left
  have right : (g:ℤ)∣d*q-c := Int.gcd_dvd_right
  have det : (g:ℤ)∣a*d-b*c := by
    rw [show a*d-b*c=b*(d*q-c)-d*(b*q-a) by ring]
    exact dvd_sub (dvd_mul_of_dvd_right right _) (dvd_mul_of_dvd_right left _)
  have one : (g:ℤ)∣1 := by rw [←inv]; exact dvd_mul_of_dvd_right det _
  have gcd_one : g=1 := Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp one)
  change Int.gcd (b*q-a) (d*q-c)=1 at gcd_one
  rw [show (a+b*(p*q))-(a*p+b*q)=(p-1)*(b*q-a) by ring,
    show (c+d*(p*q))-(c*p+d*q)=(p-1)*(d*q-c) by ring,Int.gcd_mul_left,gcd_one,mul_one]

/-- With only the two residues modulo M, their common residual divisors
among the divisors of M are precisely those dividing p−1. -/
theorem modular_residuals {a b c d e p q M s t k : ℤ}
    (inv : e*(a*d-b*c)=1) (dk : k∣M)
    (hs : s ≡ a*p+b*q [ZMOD M]) (ht : t ≡ c*p+d*q [ZMOD M]) :
    (k∣a+b*(p*q)-s ∧ k∣c+d*(p*q)-t) ↔ k∣p-1 := by
  have transfer {x y A : ℤ} (hint : x ≡ y [ZMOD M]) : k∣A-x ↔ k∣A-y := by
    have diff := (Int.ModEq.refl A).sub (Int.ModEq.of_dvd dk hint)
    rw [←Int.modEq_zero_iff_dvd,←Int.modEq_zero_iff_dvd]
    exact ⟨fun h => diff.symm.trans h,fun h => diff.trans h⟩
  rw [transfer hs,transfer ht,←(Int.dvd_natAbs (a:=k) (b:=p-1)),←residual_gcd p q inv]
  exact ⟨fun h => Int.dvd_coe_gcd h.1 h.2,
    fun h => ⟨h.trans Int.gcd_dvd_left,h.trans Int.gcd_dvd_right⟩⟩

/-- A single product test on the two proposed trace residues. -/
def Compatible {R : Type*} [CommRing R] (a b c d n s t : R) : Prop :=
  (d*s-b*t)*(a*t-c*s)=(a*d-b*c)^2*n

/-- With invertible determinant the two labels and the two factor residues
determine one another over any commutative ring. -/
theorem compatible_iff {R : Type*} [CommRing R] {a b c d e n s t : R}
    (inv : e*(a*d-b*c)=1) :
    Compatible a b c d n s t ↔
    ∃ x y, x*y=n ∧ a*x+b*y=s ∧ c*x+d*y=t := by
  constructor
  · intro h
    refine ⟨e*(d*s-b*t),e*(a*t-c*s),?_,?_,?_⟩
    · calc
        _ = e^2*((d*s-b*t)*(a*t-c*s)) := by ring
        _ = (e*(a*d-b*c))^2*n := by rw [h]; ring
        _ = n := by rw [inv]; ring
    · calc
        _ = (e*(a*d-b*c))*s := by ring
        _ = s := by rw [inv,one_mul]
    · calc
        _ = (e*(a*d-b*c))*t := by ring
        _ = t := by rw [inv,one_mul]
  · rintro ⟨x,y,rfl,rfl,rfl⟩
    unfold Compatible
    ring

private def tracePair {R : Type*} [CommRing R] (a b c d n : R) (x : Rˣ) : R × R :=
  (a*x+b*(n*↑x⁻¹),c*x+d*(n*↑x⁻¹))

/-- Enumerating all exact joint labels is equivalent to enumerating the unit
residue of the first factor; no factorization of the public modulus is needed. -/
noncomputable def labels (M : ℕ) [NeZero M] (a b c d n : ZMod M) : Finset (ZMod M × ZMod M) :=
  univ.image (tracePair a b c d n)

theorem card_labels {M : ℕ} [NeZero M] {a b c d e : ZMod M} (n : ZMod M)
    (inv : e*(a*d-b*c)=1) : (labels M a b c d n).card=Nat.totient M := by
  unfold labels
  rw [card_image_of_injective,card_univ,ZMod.card_units_eq_totient]
  intro x y h
  apply Units.ext
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only [tracePair] at h₁ h₂
  calc
    (x : ZMod M) = (e*(a*d-b*c))*x := by rw [inv,one_mul]
    _ = (e*(a*d-b*c))*y := by linear_combination e*d*h₁ - e*b*h₂
    _ = (y : ZMod M) := by rw [inv,one_mul]

theorem mem_labels {M : ℕ} [NeZero M] {a b c d e n s t : ZMod M}
    (inv : e*(a*d-b*c)=1) (hn : IsUnit n) :
    (s,t)∈labels M a b c d n ↔ Compatible a b c d n s t := by
  rw [compatible_iff inv]
  constructor
  · intro mem
    obtain ⟨x,_,eq⟩ := mem_image.mp mem
    refine ⟨(x : ZMod M),n*(↑x⁻¹ : ZMod M),?_,congrArg Prod.fst eq,congrArg Prod.snd eq⟩
    rw [mul_left_comm,Units.mul_inv, mul_one]
  · rintro ⟨x,y,hxy,hs,ht⟩
    have hx : IsUnit x := isUnit_of_mul_isUnit_left (hxy ▸ hn : IsUnit (x*y))
    obtain ⟨u,rfl⟩ := hx
    have hy : n*↑u⁻¹=y := by rw [←hxy,mul_right_comm,Units.mul_inv,one_mul]
    exact mem_image.mpr ⟨u,mem_univ _,by simp only [tracePair,hy,hs,ht]⟩

/-- Knowing one feasible value of the second trace and fixing the first
trace leaves just that value and its explicit reflection in a field. -/
theorem row_options {F : Type*} [Field F] {a b c d n s t v : F}
    (ab : a*b≠0) (ht : Compatible a b c d n s t) (hv : Compatible a b c d n s v) :
    v=t ∨ v=(a*d+b*c)*s/(a*b)-t := by
  by_cases eq : v=t
  · exact Or.inl eq
  · right
    have zero : (v-t)*((a*d+b*c)*s-(a*b)*(v+t))=0 := by
      unfold Compatible at ht hv
      linear_combination hv-ht
    have rhs := sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr eq))
    apply eq_sub_iff_add_eq.mpr
    exact (eq_div_iff ab).mpr (by rw [rhs,mul_comm])

private theorem transpose {F : Type*} [CommRing F] {a b c d n s t : F}
    (h : Compatible a b c d n s t) : Compatible c d a b n t s := by
  unfold Compatible at *
  linear_combination h

/-- No feasible 2-by-2 rectangle exists at a regular prime. Its four
public conic tests have a mixed difference that factors into three units. -/
theorem no_rectangle {F : Type*} [Field F] {a b c d n x y s t : F}
    (mixed : a*d+b*c≠0) (h₁ : Compatible a b c d n x s)
    (h₂ : Compatible a b c d n x t) (h₃ : Compatible a b c d n y s)
    (h₄ : Compatible a b c d n y t) : x=y ∨ s=t := by
  have eq : (a*d+b*c)*((x-y)*(s-t))=0 := by
    unfold Compatible at *
    linear_combination h₁-h₂-h₃+h₄
  simpa only [sub_eq_zero] using mul_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left mixed)

private theorem row_size {F : Type*} [Field F] {a b c d n s : F}
    (ab : a*b≠0) (T : Finset F) (rows : ∀ t∈T, Compatible a b c d n s t) : T.card≤2 := by
  classical
  obtain empty|⟨t,mem⟩ := T.eq_empty_or_nonempty
  · simp [empty]
  · apply (card_le_card (t:= {t,(a*d+b*c)*s/(a*b)-t}) ?_).trans card_le_two
    intro v hv
    simpa only [mem_insert,mem_singleton] using row_options ab (rows _ mem) (rows _ hv)

/-- Every all-valid Cartesian batch has at most two joint labels. -/
theorem rectangle_size {F : Type*} [Field F] {a b c d n : F}
    (ab : a*b≠0) (cd : c*d≠0) (mixed : a*d+b*c≠0) (S T : Finset F)
    (valid : ∀ s∈S, ∀ t∈T, Compatible a b c d n s t) : S.card*T.card≤2 := by
  classical
  obtain empty|⟨s,hs⟩ := S.eq_empty_or_nonempty
  · simp [empty]
  obtain empty|⟨t,ht⟩ := T.eq_empty_or_nonempty
  · simp [empty]
  have s2 := row_size cd S (fun i hi => transpose (valid i hi t ht))
  have t2 := row_size ab T (valid s hs)
  by_cases one : S.card≤1
  · simpa only [one_mul] using (Nat.mul_le_mul one t2)
  · obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (by omega : 1<S.card)
    have bound : T.card≤1 := card_le_one.mpr fun i hi j hj =>
      (no_rectangle mixed (valid x hx i hi) (valid x hx j hj) (valid y hy i hi)
        (valid y hy j hj)).resolve_left ne
    simpa only [mul_one] using (Nat.mul_le_mul s2 bound)

/-- A cover by all-valid Cartesian blocks requires at least (ℓ−1)/2
blocks. The menu may depend arbitrarily on the whole public input. -/
theorem cover_lower {ℓ : ℕ} [Fact ℓ.Prime] {a b c d e n : ZMod ℓ}
    (ab : a*b≠0) (cd : c*d≠0) (mixed : a*d+b*c≠0) (inv : e*(a*d-b*c)=1)
    {ι : Type*} (menu : Finset ι) (S T : ι → Finset (ZMod ℓ))
    (valid : ∀ i∈menu, ∀ s∈S i, ∀ t∈T i, Compatible a b c d n s t)
    (cover : labels ℓ a b c d n ⊆ menu.biUnion (fun i => S i ×ˢ T i)) :
    ℓ-1≤2*menu.card := by
  calc
    ℓ-1 = (labels ℓ a b c d n).card := by rw [card_labels n inv,Nat.totient_prime Fact.out]
    _ ≤ _ := (card_le_card cover).trans card_biUnion_le
    _ ≤ ∑ _i∈menu, 2 := sum_le_sum fun i hi => by
      rw [card_product]; exact rectangle_size ab cd mixed _ _ (valid i hi)
    _ = 2*menu.card := by simp [Nat.mul_comm]

private theorem card_projections {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, DecidableEq (F i)] (S : Finset (∀ i, F i)) :
    S.card ≤ ∏ i, (S.image fun s => s i).card := by
  rw [←Fintype.card_piFinset]
  exact card_le_card fun s hs => Fintype.mem_piFinset.mpr fun _ => mem_image_of_mem _ hs

/-- In CRT coordinates distinct prime moduli can distribute the two-element
choices between the two axes. Even then, each all-valid global rectangle
contains at most two choices per prime. The weights can vary with the prime. -/
theorem product_rectangle_size {ι : Type*} [Fintype ι] {F : ι → Type*} [∀ i, Field (F i)]
    {a b c d n : ∀ i, F i} (ab : ∀ i, a i*b i≠0) (cd : ∀ i, c i*d i≠0)
    (mixed : ∀ i, a i*d i+b i*c i≠0) (S T : Finset (∀ i, F i))
    (valid : ∀ s∈S, ∀ t∈T, ∀ i, Compatible (a i) (b i) (c i) (d i) (n i) (s i) (t i)) :
    S.card*T.card ≤ 2^Fintype.card ι := by
  classical
  have upper := Nat.mul_le_mul (card_projections S) (card_projections T)
  rw [←prod_mul_distrib] at upper
  apply upper.trans
  calc
    _ ≤ ∏ _i : ι, 2 := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ =>
      rectangle_size (ab i) (cd i) (mixed i) _ _ (by
        intro u hu v hv
        obtain ⟨s,hs,rfl⟩ := mem_image.mp hu
        obtain ⟨t,ht,rfl⟩ := mem_image.mp hv
        exact valid s hs t ht i)
    _ = _ := by simp

/-- Simultaneous wheel lower bound in CRT coordinates. For distinct primes
the independent labels are precisely the residues modulo their product.
Every all-valid cover costs at least ∏(ℓ−1)/2^r Cartesian blocks. -/
theorem product_cover_lower {ι κ : Type*} [Fintype ι] [DecidableEq ι] (P : ι → ℕ)
    [∀ i, Fact (P i).Prime] {a b c d e n : ∀ i, ZMod (P i)}
    (ab : ∀ i, a i*b i≠0) (cd : ∀ i, c i*d i≠0)
    (mixed : ∀ i, a i*d i+b i*c i≠0) (inv : ∀ i, e i*(a i*d i-b i*c i)=1)
    (menu : Finset κ) (S T : κ → Finset (∀ i, ZMod (P i)))
    (valid : ∀ j∈menu, ∀ s∈S j, ∀ t∈T j, ∀ i, Compatible (a i) (b i) (c i) (d i) (n i) (s i) (t i))
    (cover : ∀ s t : (∀ i, ZMod (P i)),
      (∀ i, (s i,t i)∈labels (P i) (a i) (b i) (c i) (d i) (n i)) →
      ∃ j∈menu, s∈S j ∧ t∈T j) :
    (∏ i, (P i-1)) ≤ 2^Fintype.card ι*menu.card := by
  classical
  let L := Fintype.piFinset fun i => labels (P i) (a i) (b i) (c i) (d i) (n i)
  let split (f : ∀ i, (ZMod (P i) × ZMod (P i))) := ((fun i => (f i).1),(fun i => (f i).2))
  have inj : Function.Injective split := by
    intro x y same
    funext i
    exact Prod.ext (congrFun (congrArg Prod.fst same) i) (congrFun (congrArg Prod.snd same) i)
  have sub : L.image split ⊆ menu.biUnion (fun j => S j ×ˢ T j) := by
    intro z mem
    obtain ⟨f,hf,rfl⟩ := mem_image.mp mem
    obtain ⟨j,hj,hs,ht⟩ := cover (split f).1 (split f).2 (Fintype.mem_piFinset.mp hf)
    exact mem_biUnion.mpr ⟨j,hj,mem_product.mpr ⟨hs,ht⟩⟩
  calc
    _ = (L.image split).card := by
      rw [card_image_of_injective _ inj,Fintype.card_piFinset]
      exact prod_congr rfl fun i _ => by rw [card_labels _ (inv i),Nat.totient_prime Fact.out]
    _ ≤ _ := (card_le_card sub).trans card_biUnion_le
    _ ≤ ∑ _j∈menu, 2^Fintype.card ι := sum_le_sum fun j hj => by
      rw [card_product]; exact product_rectangle_size ab cd mixed _ _ (valid j hj)
    _ = _ := by simp [Nat.mul_comm]

/-- When the first trace is x+y and n is a nonsquare, one rectangle for
each admissible first trace attains the prime lower bound. -/
theorem sharp_nonsquare {ℓ : ℕ} [Fact ℓ.Prime] {c d e n : ZMod ℓ}
    (inv : e*(1*d-1*c)=1) (hn : n≠0) (ns : ¬IsSquare n) :
    ∃ (menu : Finset (ZMod ℓ)) (S T : ZMod ℓ → Finset (ZMod ℓ)),
      menu.card=(ℓ-1)/2 ∧ (∀ i∈menu, ∀ s∈S i, ∀ t∈T i, Compatible 1 1 c d n s t) ∧
      labels ℓ 1 1 c d n ⊆ menu.biUnion (fun i => S i ×ˢ T i) := by
  classical
  let T (s : ZMod ℓ) := univ.filter fun t => Compatible 1 1 c d n s t
  refine ⟨factorSumResidues ℓ n,fun s => {s},T,
    card_factorSumResidues_of_nonsquare ℓ n hn ns,?_,?_⟩
  · intro i _ s hs t ht
    rw [mem_singleton.mp hs]
    exact (mem_filter.mp ht).2
  · rintro ⟨s,t⟩ h
    have ok := (mem_labels inv (isUnit_iff_ne_zero.mpr hn)).mp h
    obtain ⟨x,y,prod,first,_⟩ := (compatible_iff inv).mp ok
    have smem : s∈factorSumResidues ℓ n :=
      (mem_factorSumResidues_iff ℓ hn).mpr ⟨x,y,prod,by simpa using first⟩
    exact mem_biUnion.mpr ⟨s,smem,mem_product.mpr
      ⟨mem_singleton_self _,mem_filter.mpr ⟨mem_univ _,ok⟩⟩⟩

/-- A fixed product of consecutive primes whose modulus exceeds 2^614. -/
noncomputable def wheel : Finset ℕ := (range 458).filter fun p => 5≤p ∧ p.Prime

instance (i : wheel) : Fact i.val.Prime := ⟨(mem_filter.mp i.property).2.2⟩

set_option maxRecDepth 4000 in
theorem wheel_values : wheel.card=86 ∧ 2^619<(∏ p∈wheel,p) ∧
    (∏ p∈wheel,p)<2^620 ∧ 2^86*2^531<(∏ p∈wheel,(p-1)) := by decide +kernel

set_option maxRecDepth 5000 in
/-- Even on this fixed wheel and just two adjacent weight rows, any complete
explicit cover by all-valid Cartesian rectangles requires over 2^531 blocks.
This charges neither an implicit conic test nor a table permitted false positives. -/
theorem wheel_lower {κ : Type*} (N : ℕ) (menu : Finset κ)
    (S T : κ → Finset (∀ i : wheel, ZMod i.val))
    (valid : ∀ j∈menu, ∀ s∈S j, ∀ t∈T j, ∀ i, Compatible 1 1 2 1 (N : ZMod i.val) (s i) (t i))
    (cover : ∀ s t : (∀ i : wheel, ZMod i.val), (∀ i, (s i,t i)∈labels i.val 1 1 2 1 N) →
      ∃ j∈menu, s∈S j ∧ t∈T j) : 2^531<menu.card := by
  have nz {i : wheel} {k : ℕ} (pos : 0<k) (small : k<5) : (k : ZMod i.val)≠0 :=
    fun h => (Nat.not_dvd_of_pos_of_lt pos (small.trans_le (mem_filter.mp i.property).2.1))
      ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
  have bound := product_cover_lower (fun i : wheel => i.val) (e:=fun _ => -1)
    (fun _ => by simp) (fun i => by simpa using (nz (i:=i) (k:=2) (by decide) (by decide)))
    (fun i => by convert (nz (i:=i) (k:=3) (by decide) (by decide)) using 1; norm_num)
    (fun _ => by ring) menu S T valid cover
  rw [Fintype.card_coe,wheel_values.1,Finset.prod_coe_sort wheel (fun p => p-1)] at bound
  have compared : 2^86*2^531<2^86*menu.card := wheel_values.2.2.2.trans_le bound
  exact Nat.lt_of_mul_lt_mul_left compared

local instance prime1009 : Fact (Nat.Prime 1009) := ⟨by decide +kernel⟩

set_option maxRecDepth 5000 in
/-- A bounded comparison for the adjacent weights (1,1),(2,1).
Independent marginal masks have 504² pairs. The actual relation has
1,008 labels and its exact Cartesian cover needs precisely 504 blocks. -/
theorem example_counts :
    (factorSumResidues 1009 77).card=504 ∧ (factorSumResidues 1009 154).card=504 ∧
    (labels 1009 1 1 2 1 77).card=1008 := by
  have h₁ : ¬IsSquare (77 : ZMod 1009) := by
    change ¬∃ z : ZMod 1009, 77=z*z
    decide +kernel
  have h₂ : ¬IsSquare (154 : ZMod 1009) := by
    change ¬∃ z : ZMod 1009, 154=z*z
    decide +kernel
  exact ⟨card_factorSumResidues_of_nonsquare _ _ (by decide) h₁,
    card_factorSumResidues_of_nonsquare _ _ (by decide) h₂,
    (card_labels (e:= -1) _ (by decide)).trans (Nat.totient_prime Fact.out)⟩

/-- If the mixed coefficient vanishes, four-element rectangles really can
occur, even for neighboring positive weights of determinant one. -/
example : ∀ s ∈ ({3,4} : Finset (ZMod 7)), ∀ t ∈ ({2,5} : Finset (ZMod 7)),
    Compatible 2 1 3 2 1 s t := by
  simp only [mem_insert,mem_singleton,forall_eq_or_imp,forall_eq,Compatible]
  decide +kernel

end PrimeFactors.WeightedCollisionReuse
