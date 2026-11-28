import PrimeFactors.FloorSquareShiftPopulation
import PrimeFactors.CyclotomicDiagonalPopulation

/-! Integer shifts at the first Fermat midpoint, or at an arbitrary
midpoint between it and the true one. The counts are over sorted prime
pairs of full factor and product width. -/
namespace PrimeFactors.CeilingShiftPopulation
open Finset MixedPrefixSample
open private PrimeFactors.MonotoneSumPopulation.data from PrimeFactors.MonotoneSumPopulation
open private PrimeFactors.MixedPrefixSample.mem_primes PrimeFactors.MixedPrefixSample.mem_sample from PrimeFactors.MixedPrefixSample

/-- A strictly positive magnitude for the negative shift at the specified center. -/
def Hit (p q m a : ℕ) : Prop := 0<a ∧ (p+a)*(q+a)=(m+a)^2

theorem before {p q m a : ℕ} (lt : p<q) (hit : Hit p q m a) : 2*m<p+q := by
  obtain ⟨_,eqn⟩ := hit
  have sep : (0:ℤ)<q-(p:ℤ) := sub_pos.mpr (by exact_mod_cast lt)
  have sq : (2*(m+a))^2<(p+a+(q+a))^2 := by
    zify at eqn ⊢
    nlinarith only [sq_pos_of_pos sep,eqn]
  have := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp sq
  omega

/-- Reflect a ceiling witness to a positive floor-shift witness. -/
theorem reflect {p q m a H : ℕ} (lt : p<q) (height : q≤H) (op : Odd p) (oq : Odd q)
    (center : ceilSqrt (p*q)=m) (hit : Hit p q m a) :
    q+2*a≤3*H ∧ FloorSquareShift.shift (p+2*a) (q+2*a) a := by
  have order := before lt hit
  have gap : 2*m+2≤p+q := by obtain ⟨i,hi⟩ := op; obtain ⟨j,hj⟩ := oq; omega
  have mpos : 0<m := by
    by_contra! mh
    have zero : p*q=0 := by
      have := ceilSqrt_le_iff.mp (center.trans_le mh)
      simpa using this
    have pp : 0<p := by obtain ⟨i,hi⟩ := op; omega
    exact (Nat.mul_pos pp (pp.trans lt)).ne' zero
  have low := ceilSqrt_le_iff.mp (center.le : ceilSqrt (p*q)≤m)
  have prev : (m-1)^2<p*q := lt_of_not_ge fun h =>
    (by omega : ¬ceilSqrt (p*q)≤m-1) (ceilSqrt_le_iff.mpr h)
  have cut : m^2+1<p*q+2*m := by
    zify [show 1≤m by omega] at prev ⊢
    linarith only [show ((m:ℤ)-1)^2=(m:ℤ)^2-2*m+1 by ring,prev]
  have eqn := hit.2
  have budget : a≤m := by
    have gg := Nat.mul_le_mul_right a gap
    nlinarith only [gg,eqn,cut]
  have mh : m≤H := by
    rw [←center,ceilSqrt_le_iff]
    calc p*q≤H*H := Nat.mul_le_mul (lt.le.trans height) height
         _ = H^2 := by ring
  have lower : (m+2*a)^2≤(p+2*a)*(q+2*a) := by nlinarith only [eqn,low]
  have upper : (p+2*a)*(q+2*a)<(m+2*a+1)^2 := by nlinarith only [eqn,cut]
  have root : ((p+2*a)*(q+2*a)).sqrt=m+2*a :=
    Nat.le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr upper)) (Nat.le_sqrt'.mpr lower)
  refine ⟨by omega, hit.1, by omega,?_⟩
  rw [root,show p+2*a-a=p+a by omega,show q+2*a-a=q+a by omega,show m+2*a-a=m+a by omega]
  exact eqn

attribute [local irreducible] eligible MixedPrefixSample.primes
set_option exponentiation.threshold 4096
set_option maxRecDepth 1024

noncomputable def successes : Finset (ℕ×ℕ) := by
  classical exact eligible.filter fun z => ∃ a, Hit z.1 z.2 (ceilSqrt (z.1*z.2)) a

theorem odd_factors {z : ℕ×ℕ} (h : z∈eligible) : Odd z.1 ∧ Odd z.2 := by
  rw [eligible] at h
  obtain ⟨base,lt⟩ := PrimeFactors.MixedPrefixSample.mem_sample.mp h
  obtain ⟨pm,qm,_,_,_⟩ := mem_ordered.mp base
  obtain ⟨⟨pl,_⟩,pp⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp pm
  obtain ⟨⟨ql,_⟩,qp⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp qm
  have two : 2<X := by decide +kernel
  exact ⟨pp.odd_of_ne_two (by omega),qp.odd_of_ne_two (by omega)⟩

attribute [local irreducible] successes

private theorem reflected_count (A : Finset (ℕ×ℕ))
    (witness : ∀ z∈A, z.1<z.2 ∧ z.2≤2^1024 ∧ Odd z.1 ∧ Odd z.2 ∧
      ∃ t, Hit z.1 z.2 (ceilSqrt (z.1*z.2)) t) :
    A.card≤72*2^1024*2^512+6*2^1024 := by
  classical
  let a (z : ℕ×ℕ) := if h : ∃ t, Hit z.1 z.2 (ceilSqrt (z.1*z.2)) t then h.choose else 0
  let f (z : ℕ×ℕ) : ℕ×ℕ := (z.1+2*a z,z.2+2*a z)
  have facts : ∀ z∈A, (f z).1<(f z).2 ∧ (f z).2≤3*2^1024 ∧
      FloorSquareShift.shift (f z).1 (f z).2 (a z) := by
    intro z hz
    obtain ⟨lt,hh,op,oq,ex⟩ := witness z hz
    have step : Hit z.1 z.2 (ceilSqrt (z.1*z.2)) (a z) := by
      dsimp only [a]; rw [dif_pos ex]; exact ex.choose_spec
    exact ⟨by dsimp [f]; omega,reflect lt hh op oq rfl step⟩
  have inj : Set.InjOn f (A:Set (ℕ×ℕ)) := by
    intro z hz w hw same
    obtain ⟨lt,_,hz'⟩ := facts z hz
    obtain ⟨_,_,hw'⟩ := facts w hw
    rw [←same] at hw'
    have eqn := FloorSquareShift.shift_unique lt hz' hw'
    have l := congrArg Prod.fst same
    have r := congrArg Prod.snd same
    change z.1+2*a z=w.1+2*a w at l
    change z.2+2*a z=w.2+2*a w at r
    exact Prod.ext (by omega) (by omega)
  have ext := FloorSquareShiftPopulation.finite_count (A.image f) (H:=3*2^1024)
    (by decide +kernel) (by
      intro v hv
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
      obtain ⟨lt,hi,hs⟩ := facts z hz
      exact ⟨lt,hi,a z,hs⟩)
  rw [Finset.card_image_of_injOn inj] at ext
  have rt : Real.sqrt ((3:ℝ)*2^1024)≤2*2^512 :=
    (Real.sqrt_le_left (by positivity)).mpr (by norm_num)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at ext
  have R := mul_le_mul_of_nonneg_left rt (show 0≤12*((3:ℝ)*2^1024) by positivity)
  have hn : A.card≤72*2^1024*2^512+6*2^1024 := by
    exact_mod_cast (show (A.card:ℝ)≤72*2^1024*2^512+6*2^1024 by linarith only [ext,R])
  exact hn

/-- Even with an arbitrary shift, first-center hits cover less than one in 2^479. -/
theorem full_width : 2^479*successes.card<eligible.card := by
  classical
  have hn := reflected_count successes (by
    intro z hz
    rw [successes] at hz
    obtain ⟨he,ex⟩ := Finset.mem_filter.mp hz
    obtain ⟨lt,hi⟩ := PrimeFactors.MonotoneSumPopulation.data he
    obtain ⟨op,oq⟩ := odd_factors he
    exact ⟨lt,hi.le,op,oq,ex⟩)
  have room : 21000000*(2^479*(72*2^1024*2^512+6*2^1024))≤2^2046 := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left ((Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left _ hn)).trans_lt
    (room.trans_lt ChebyshevPrimeSample.eligible_count))

/-- Whenever the last odd midpoint below the true one is strictly above
the real square root, it admits a positive magnitude. The center uses the
true sum and is not an observation obtained from the product. -/
theorem last_odd {p q M m : ℕ} (op : Odd p) (oq : Odd q) (om : Odd m)
    (mid : p+q=2*M) (last : M=m+1 ∨ M=m+2) (above : p*q<m^2) :
    ∃ a, Hit p q m a := by
  obtain ⟨x,hp⟩ := op
  obtain ⟨y,hq⟩ := oq
  obtain ⟨z,hm⟩ := om
  have normM : m^2=4*(z^2+z)+1 := by rw [hm]; ring
  have normN : p*q=4*(x*y)+2*(x+y)+1 := by rw [hp,hq]; ring
  rcases last with last|last
  · let a := (m^2-p*q)/2
    have eqn : p*q+2*a=m^2 := by dsimp [a]; omega
    refine ⟨a,by omega,?_⟩
    have hh : p+q=2*m+2 := by omega
    nlinarith only [congrArg (·*a) hh,eqn]
  · let a := (m^2-p*q)/4
    have eqn : p*q+4*a=m^2 := by dsimp [a]; omega
    refine ⟨a,by omega,?_⟩
    have hh : p+q=2*m+4 := by omega
    nlinarith only [congrArg (·*a) hh,eqn]

theorem flexible {p q M : ℕ} (op : Odd p) (oq : Odd q) (mid : p+q=2*M)
    (nonsquare : ∀ j : ℕ, p*q≠j^2) (room : ceilSqrt (p*q)+2≤M) :
    ∃ m a : ℕ, ceilSqrt (p*q)≤m ∧ m<M ∧ Odd m ∧ Hit p q m a := by
  let j := (M-2)/2
  let m := 2*j+1
  have last : M=m+1 ∨ M=m+2 := by dsimp [m,j]; omega
  have inside : ceilSqrt (p*q)≤m := by omega
  have odd : Odd m := ⟨j,rfl⟩
  obtain ⟨a,ha⟩ := last_odd op oq odd mid last ((ceilSqrt_le_iff.mp inside).lt_of_ne (nonsquare m))
  exact ⟨m,a,inside,by omega,odd,ha⟩

private theorem ceil_at {n m : ℕ} (below : m^2<n) (high : n≤(m+1)^2) :
    ceilSqrt n=m+1 := by
  have upper := ceilSqrt_le_iff.mpr high
  have lower := (ceilSqrt_le_iff.not).mpr (not_le_of_gt below)
  omega

theorem controls :
    Nat.Prime 67 ∧ Nat.Prime 73 ∧ Nat.Prime 127 ∧
    67*127=8509 ∧ ceilSqrt 8509=93 ∧ (¬∃ a, Hit 67 127 93 a) ∧
    Hit 67 127 95 129 ∧ 73*127=9271 ∧ ceilSqrt 9271=97 ∧ Hit 73 127 97 23 := by
  refine ⟨by norm_num,by norm_num,by norm_num,by decide,ceil_at (m:=92) (by decide) (by decide),?_,by norm_num [Hit],
    by decide,ceil_at (m:=96) (by decide) (by decide),by norm_num [Hit]⟩
  rintro ⟨a,_,h⟩
  have eqn : 8*a=140 := by nlinarith only [h]
  omega

/-- All eligible products except fewer than one in 2^498 have at least one
negative-shift witness somewhere between the first and true midpoints. -/
theorem flexible_population (A : Finset (ℕ×ℕ)) (sub : A⊆eligible)
    (miss : ∀ z∈A, ¬∃ m a : ℕ, ceilSqrt (z.1*z.2)≤m ∧ 2*m<z.1+z.2 ∧ Hit z.1 z.2 m a) :
    2^498*A.card<eligible.card := by
  classical
  have covered : A⊆sample (FirstSumMenuPopulation.event 2) := by
    rintro ⟨p,q⟩ h
    have ok := sub h
    obtain ⟨op,oq⟩ := odd_factors ok
    have oe : (p+q)%2=0 := by obtain ⟨x,hx⟩ := op; obtain ⟨y,hy⟩ := oq; omega
    let M := (p+q)/2
    have mid : p+q=2*M := by dsimp [M]; omega
    have lt := (PrimeFactors.MonotoneSumPopulation.data ok).1
    change p<q at lt
    have meta := ok
    rw [eligible] at meta
    obtain ⟨base,_⟩ := PrimeFactors.MixedPrefixSample.mem_sample.mp meta
    obtain ⟨pm,qm,_,_,_⟩ := mem_ordered.mp base
    have pp : Nat.Prime p := (PrimeFactors.MixedPrefixSample.mem_primes.mp pm).2
    have qp : Nat.Prime q := (PrimeFactors.MixedPrefixSample.mem_primes.mp qm).2
    have ns : ∀ j : ℕ, p*q≠j^2 := by
      intro j eqn
      have dv : p∣j^2 := eqn ▸ dvd_mul_right p q
      obtain ⟨w,rfl⟩ := pp.dvd_of_dvd_pow dv
      have same : q=p*w^2 := Nat.eq_of_mul_eq_mul_left pp.pos (by
        calc p*q = (p*w)^2 := eqn
             _ = p*(p*w^2) := by ring)
      exact lt.ne ((Nat.prime_dvd_prime_iff_eq pp qp).mp ⟨w^2,same⟩)
    have room : ¬ceilSqrt (p*q)+2≤M := by
      intro hv
      obtain ⟨m,a,lo,hi,_,hit⟩ := flexible op oq mid ns hv
      exact miss (p,q) h ⟨m,a,lo,by change 2*m<p+q; omega,hit⟩
    have first : ceilSqrt (p*q)≤M := by
      apply ceilSqrt_le_iff.mpr
      have sq : (0:ℤ)≤((p:ℤ)-q)^2 := sq_nonneg _
      zify at mid ⊢
      nlinarith only [sq,congrArg (·^2) mid]
    refine FirstSumMenuPopulation.mem_sample_iff.mpr ⟨ok,Finset.mem_image.mpr
      ⟨M-ceilSqrt (p*q),Finset.mem_range.mpr (by omega),?_⟩⟩
    change 2*(ceilSqrt (p*q)+(M-ceilSqrt (p*q)))=p+q
    omega
  have rare := CyclotomicDiagonalPopulation.menu_fraction (J:=2) (G:=2^514) (m:=2^498)
    (by decide +kernel) (by decide +kernel)
  rw [CyclotomicDiagonalPopulation.compatible_eq] at rare
  exact (Nat.mul_le_mul_left _ (card_le_card covered)).trans_lt rare

end PrimeFactors.CeilingShiftPopulation
