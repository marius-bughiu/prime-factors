import PrimeFactors.FiveWeightEstimates
import PrimeFactors.CrowdingOrdinarySeparation
import PrimeFactors.WeightedPrimeCrowding

/-! A fixed set of five nearby weights needs just ten unfiltered first
traces. Explicit prime-count estimates guarantee many distinct hits. -/
namespace PrimeFactors.FiveWeightMenu
open Finset WeightedPrimeCrowding
open WeightedCrowdingEstimates (Dusart BrunTitchmarsh)
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192

noncomputable def menu : Finset ℕ := Icc 512 516
private abbrev U : ℕ := 2^1024

theorem allowed : menu⊆weights := by
  simp only [menu,weights_def,subset_iff,mem_Icc,mem_Ico]
  omega

private theorem subtract_left {v origin span : ℕ} (bound : v<origin+span) (pos : 0<span) :
    v-origin<span := by omega

private theorem bins_cover {x : ℕ×ℕ} (mem : x∈menu ×ˢ pool) : bucket x<135*2^507 := by
  obtain ⟨w,p⟩ := mem_product.mp mem
  rw [menu,mem_Icc] at w
  rw [pool_def,mem_filter,mem_Icc] at p
  have pl : x.2<7*U/8 := by
    by_contra! h
    have eq : x.2=7*U/8 := le_antisymm p.1.2 h
    have divides : 2∣x.2 := eq ▸ (by decide +kernel : 2∣7*U/8)
    have two := (Nat.prime_dvd_prime_iff_eq Nat.prime_two p.2).mp divides
    have : 2<7*U/8 := by decide +kernel
    omega
  have upper := (Nat.mul_le_mul_right x.2 w.2).trans_lt
    (Nat.mul_lt_mul_of_pos_left pl (by decide : 0<516))
  change (x.1*x.2-384*U)/(2^516)<135*2^507
  rw [Nat.div_lt_iff_lt_mul (by decide : 0<2^516)]
  have size : 384*U+(135*2^507)*(2^516)=516*(7*U/8) := by decide +kernel
  have pos : 0<(135*2^507)*(2^516) := by decide +kernel
  exact subtract_left (lt_of_lt_of_eq upper size.symm) pos

theorem many_products (dusart : Dusart) (bt : BrunTitchmarsh) :
    2^1503 < (menuProducts menu).card := by
  have size : menu.card=5 := by rw [menu,Nat.card_Icc]
  obtain ⟨total,diagonal,en,di,split,copies⟩ :=
    menu_counts menu allowed (135*2^507) (2^512/5600+1) (fun _ hx => bins_cover hx)
      (FiveWeightEstimates.short_intervals bt)
  rw [size] at en di copies
  have pop := FiveWeightEstimates.population dusart
  apply FiveWeightEstimates.product_lower_bound (points:=5*pool.card)
    (total:=total) (diagonal:=diagonal) (hits:=(menuHits menu).card)
  · omega
  · exact en
  · exact di
  · exact split
  · omega

/-- Each counted input comes with a proper first-label gcd on this five-weight
menu and no ordinary square at the first 2^1002 consecutive traces. -/
theorem comparison {n : ℕ} (hit : n∈menuProducts menu) :
    (∃ a∈menu, ∃ b∈menu, a≠b ∧
      let s := (4*(a*b)*n-1).sqrt+1
      let g := n.gcd ((s+(s^2-4*(a*b)*n).sqrt)/2)
      s^2 = 4*(a*b)*n+((s^2-4*(a*b)*n).sqrt)^2 ∧ 1<g ∧ g<n) ∧
    ∀ i<2^1002, ∀ d : ℕ, (ceilSqrt (4*n)+i)^2≠4*n+d^2 := by
  obtain ⟨z,hz,hprod⟩ := mem_image.mp hit
  obtain ⟨hitAll,wa,wb⟩ := mem_filter.mp hz
  have full : n∈products := mem_image.mpr ⟨z,hitAll,hprod⟩
  refine ⟨?_,CrowdingOrdinarySeparation.products_missed full⟩
  rcases z with ⟨⟨a,p⟩,b,q⟩
  change p*q=n at hprod
  subst n
  have ⟨first,split⟩ := recover hitAll
  simp only [hits,collisions,points,mem_filter,mem_product] at hitAll
  obtain ⟨⟨⟨⟨_,hp⟩,_,hq⟩,_⟩,ne⟩ := hitAll
  have pp := (mem_filter.mp (show p∈(Icc (3*U/4) (7*U/8)).filter Nat.Prime by
    rwa [←pool_def])).2
  have qp := (mem_filter.mp (show q∈(Icc (3*U/4) (7*U/8)).filter Nat.Prime by
    rwa [←pool_def])).2
  refine ⟨a,wa,b,wb,ne,?_,?_⟩
  · dsimp only at first ⊢
    rw [first]
    have sqr := multiplier_sum_square p q a b
    rw [Nat.mul_assoc 4 a b] at sqr
    rw [sqr,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  dsimp only at split ⊢
  rcases split with h|h
  · rw [h]
    exact ⟨pp.one_lt,by nlinarith only [Nat.mul_le_mul_left p qp.two_le,pp.pos]⟩
  · rw [h]
    exact ⟨qp.one_lt,by nlinarith only [Nat.mul_le_mul_right q pp.two_le,qp.pos]⟩

/-- These are ten unordered public pairs of distinct weights. -/
theorem tests : ((menu ×ˢ menu).filter (fun z => z.1<z.2)).card=10 := by decide +kernel

end PrimeFactors.FiveWeightMenu
