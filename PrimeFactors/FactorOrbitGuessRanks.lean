import PrimeFactors.FirstPowerGuessOverlap

/-! Guessing either coordinate of a uniform pair with known product in a
finite commutative group. Each label is an actual set {a,n/a}; testing
either representative succeeds for exactly those two coordinates, or one
coordinate when the set is a singleton. -/

namespace PrimeFactors.FactorOrbitGuessRanks

open Finset
open FiveSquareGuessRanks (score)
open private PrimeFactors.FiveSquareGuessRanks.overlap PrimeFactors.FiveSquareGuessRanks.rankSum
  PrimeFactors.FiveSquareGuessRanks.rank_identity PrimeFactors.FiveSquareGuessRanks.least_of_overlap
  from PrimeFactors.FiveSquareGuessRanks
open scoped Classical

variable {G : Type*} [CommGroup G] [Fintype G]

noncomputable def orbit (n a : G) : Finset G := {a,n/a}
abbrev Label (n : G) := {s : Finset G // ∃ a, orbit n a=s}
noncomputable def label (n a : G) : Label n := ⟨orbit n a,a,rfl⟩
abbrev Order (n : G) := Label n ≃ Fin (Fintype.card (Label n))

/-- Number of fixed points of the partner map, counted in the group. -/
noncomputable def fixed (n : G) := (univ.filter fun a : G => a^2=n).card

omit [Fintype G] in
private theorem involution (n a : G) : n/(n/a)=a := div_div_self' n a

omit [Fintype G] in
/-- A representative hits either coordinate precisely when it names the correct orbit. -/
theorem hit_iff (n x a : G) : label n x=label n a ↔ x=a ∨ x=n/a := by
  constructor
  · intro eq
    have own : x∈(label n x).val := mem_insert_self ..
    rw [eq] at own
    simpa [label,orbit] using own
  · rintro (rfl|rfl)
    · rfl
    · apply Subtype.ext
      change {n/a,n/(n/a)}=({a,n/a}:Finset G)
      rw [involution,pair_comm]

private theorem orbit_fiber (n : G) (s : Label n) :
    (univ.filter fun a : G => label n a=s)=s.val := by
  obtain ⟨v,⟨x,rfl⟩⟩ := s
  ext a
  change a∈(univ.filter fun y => label n y=label n x) ↔ a∈orbit n x
  simp only [mem_filter,mem_univ,true_and,hit_iff,orbit,mem_insert,mem_singleton]

/-- In the ordered-pair model each orbit has multiplicity exactly its size. -/
theorem by_orbit (n : G) (f : Label n→ℕ) :
    (∑ a : G,f (label n a))=∑ s,s.val.card*f s := by
  have grouped := sum_fiberwise_of_maps_to' (s:=univ) (fun a _ => mem_univ (label n a)) f
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,orbit_fiber] using grouped.symm

omit [Fintype G] in
private theorem sizes (n : G) (s : Label n) : s.val.card=1 ∨ s.val.card=2 := by
  obtain ⟨v,⟨x,rfl⟩⟩ := s
  exact card_pair_eq_one_or_two

omit [Fintype G] in
private theorem singleton_iff (n a : G) : (label n a).val.card=1 ↔ a^2=n := by
  have eq : a=n/a ↔ a^2=n := by rw [eq_div_iff_mul_eq',pow_two]
  by_cases h : a=n/a
  · simp only [label,orbit,←h,pair_eq_singleton,card_singleton,true_iff]
    exact eq.mp h
  · simp only [label,orbit,card_pair h,OfNat.ofNat_ne_one,false_iff]
    exact fun root => h (eq.mpr root)

theorem mass (n : G) : (∑ s : Label n,s.val.card)=Fintype.card G := by
  simpa only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] using (by_orbit n (fun _ => 1)).symm

/-- Doubled orbit count equals group size plus the number of square roots. -/
theorem count (n : G) : 2*Fintype.card (Label n)=Fintype.card G+fixed n := by
  let cost (s : Label n) := 1+(if s.val.card=1 then 1 else 0)
  have row (s : Label n) : s.val.card*cost s=2 := by
    rcases sizes n s with h|h <;> simp [cost,h]
  have term (a : G) : cost (label n a)=1+(if a^2=n then 1 else 0) := by simp only [cost,singleton_iff]
  have h := by_orbit n cost
  simp only [term,row,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] at h
  have fs : (∑ a : G, if a^2=n then 1 else 0)=fixed n := by
    rw [sum_ite, sum_const_zero,add_zero,sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,fixed]
  rw [fs] at h
  omega

theorem singleton_count (n : G) :
    (univ.filter (fun s : Label n => s.val.card=1)).card=fixed n := by
  have row (s : Label n) : s.val.card+(if s.val.card=1 then 1 else 0)=2 := by
    rcases sizes n s with h|h <;> simp [h]
  have h := sum_congr (rfl : (univ : Finset (Label n))=univ) (fun s _ => row s)
  simp only [sum_add_distrib,mass,sum_ite,sum_const_zero,add_zero,sum_const,
    card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] at h
  have total := count n
  omega

theorem double_count (n : G) :
    (univ.filter (fun s : Label n => s.val.card=2)).card=(Fintype.card G-fixed n)/2 := by
  have parts := filter_card_add_filter_neg_card_eq_card (s:=univ) (fun s : Label n => s.val.card=1)
  have eq : (univ.filter fun s : Label n => ¬s.val.card=1)=(univ.filter fun s : Label n => s.val.card=2) := by
    ext s
    simp only [mem_filter,mem_univ,true_and]
    have h := sizes n s
    omega
  rw [eq,singleton_count,card_univ] at parts
  have h := count n
  omega

/-- Inclusive rank, averaged over the uniformly chosen first coordinate. -/
noncomputable def mean (n : G) (e : Order n) : ℚ :=
  ((∑ a : G,((e (label n a)).val+1) : ℕ):ℚ)/(Fintype.card G:ℚ)

noncomputable def optimum (n : G) : ℚ :=
  (Fintype.card G:ℚ)/4+1/2+(fixed n:ℚ)^2/(4*Fintype.card G)

noncomputable def random (n : G) : ℚ := ((Fintype.card G:ℚ)+fixed n+2)/4

theorem mean_eq (n : G) (e : Order n) :
    mean n e=(score (fun s : Label n => s.val.card) e.symm:ℚ)/(Fintype.card G:ℚ) := by
  apply congrArg (fun z : ℕ => (z:ℚ)/(Fintype.card G:ℚ))
  calc
    _ = ∑ s : Label n, s.val.card*((e s).val+1) := by_orbit n (fun s => (e s).val+1)
    _ = ∑ i, (e.symm i).val.card*(i.val+1) := by
      simpa only [Equiv.apply_symm_apply] using
        (e.symm.sum_comp (fun s => s.val.card*((e s).val+1))).symm
    _ = score (fun s : Label n => s.val.card) e.symm :=
      sum_congr rfl (fun _ _ => Nat.mul_comm ..)

private theorem integer_optimum {α : Type*} [Fintype α] (w : α→ℕ) :
    ∃ k : ℕ, IsLeast (Set.range (score w)) k ∧ 2*k=(∑ a,w a)+PrimeFactors.FiveSquareGuessRanks.overlap w := by
  let e₀ := (Fintype.equivFin α).symm
  let f := fun i => OrderDual.toDual (w (e₀ i))
  let e := (Tuple.sort f).trans e₀
  have sort : Antitone (w ∘ e) := fun _ _ h => Tuple.monotone_sort f h
  have h := (PrimeFactors.FiveSquareGuessRanks.rank_identity (w ∘ e)).2 sort
  have inner (a : α) := e.sum_comp (fun b => min (w a) (w b))
  have outer := e.sum_comp (fun a => ∑ b,min (w a) (w b))
  simp only [PrimeFactors.FiveSquareGuessRanks.overlap,Function.comp_apply,inner,outer,e.sum_comp w] at h
  exact ⟨score w e,PrimeFactors.FiveSquareGuessRanks.least_of_overlap w h,h.symm⟩

/-- All orders have at least this mean; putting two-member orbits before
singletons gives an order attaining it. -/
theorem optimal (n : G) : IsLeast (Set.range (mean n)) (optimum n) := by
  let w (s : Label n) := s.val.card
  obtain ⟨k,least,twice⟩ := integer_optimum w
  have m : (∑ s,w s)=Fintype.card G := mass n
  rw [m] at twice
  have cast : (2:ℝ)*k=(Fintype.card G:ℝ)+∑ a,∑ b,min (w a:ℝ) (w b:ℝ) := by
    dsimp only [PrimeFactors.FiveSquareGuessRanks.overlap] at twice
    exact_mod_cast twice
  have cm : (∑ s,(w s:ℝ))=(Fintype.card G:ℝ) := by exact_mod_cast m
  have cc : (2:ℝ)*Fintype.card (Label n)=Fintype.card G+fixed n := by exact_mod_cast count n
  have ca : (Fintype.card (Label n):ℝ)=((Fintype.card G:ℝ)+fixed n)/2 := by linarith only [cc]
  rw [FirstPowerGuessOverlap.one_two w (sizes n),cm,ca] at cast
  have dist : (4:ℝ)*k=(Fintype.card G:ℝ)^2+2*Fintype.card G+(fixed n:ℝ)^2 := by nlinarith only [cast]
  have dist' : (4:ℚ)*k=(Fintype.card G:ℚ)^2+2*Fintype.card G+(fixed n:ℚ)^2 := by exact_mod_cast dist
  have pos : (0:ℚ)<Fintype.card G := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card G)
  have eq : (k:ℚ)/Fintype.card G=optimum n := by
    unfold optimum
    field_simp [pos.ne']
    nlinarith only [dist']
  rw [←eq]
  obtain ⟨⟨e,hit⟩,bound⟩ := least
  refine ⟨⟨e.symm,?_⟩,?_⟩
  · rw [mean_eq]
    exact congrArg (fun j : ℕ => (j:ℚ)/Fintype.card G) hit
  · rintro _ ⟨e,rfl⟩
    rw [mean_eq]
    have h := bound ⟨e.symm,rfl⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) pos.le

/-- Mean inclusive rank of a label over all bijections to the rank positions. -/
noncomputable def uniformRank {α : Type*} [Fintype α] (x : α) : ℚ :=
  ((∑ e : α ≃ Fin (Fintype.card α), ((e x).val+1) : ℕ):ℚ)/
    Fintype.card (α ≃ Fin (Fintype.card α))

private theorem uniform_mean {α : Type*} [Fintype α] (x : α) :
    uniformRank x=((Fintype.card α:ℚ)+1)/2 := by
  unfold uniformRank
  have h := PrimeSquareExpectedRank.uniform_order (A:=Fintype.card α) x
  have hr := congrArg (Nat.cast : ℕ→ℚ) h
  push_cast only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hr
  have non : Nonempty (α ≃ Fin (Fintype.card α)) := ⟨Fintype.equivFin _⟩
  have pos : (0:ℚ)<Fintype.card (α ≃ Fin (Fintype.card α)) := by
    exact_mod_cast Fintype.card_pos_iff.mpr non
  apply (div_eq_iff pos.ne').mpr
  linarith only [hr]

/-- Every fixed hidden pair has the stated average rank in a uniformly
random ordering of the actual orbits. -/
theorem random_target (n a : G) :
    uniformRank (label n a)=random n := by
  refine (uniform_mean (label n a)).trans ?_
  unfold random
  have eq : (2:ℚ)*Fintype.card (Label n)=(Fintype.card G:ℚ)+fixed n := by
    exact_mod_cast count n
  linarith only [eq]

theorem saving (n : G) : random n-optimum n =
    (fixed n:ℚ)*((Fintype.card G:ℚ)-fixed n)/(4*Fintype.card G) := by
  have hp : (0:ℚ)<Fintype.card G := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card G)
  unfold random optimum
  field_simp [hp.ne']
  ring

end PrimeFactors.FactorOrbitGuessRanks
