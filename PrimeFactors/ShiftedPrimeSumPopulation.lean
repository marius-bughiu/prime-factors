import PrimeFactors.PrimeSumDividesSuccessor

/-! Count all eligible inputs covered by all divisors of N+k, for 1≤k≤64,
under the public exponent-size gate (E+1)²≥4N. -/
namespace PrimeFactors.ShiftedPrimeSumPopulation

open Finset MixedPrefixSample PrimeSumDividesSuccessor
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

noncomputable def roots (g h : ℕ) := (range g).filter fun a => g∣a*(a+h)

/-- For d=gcd(g,a), the other part g/d divides a+h. The cross products
a(b+h) and b(a+h) show that d determines h*a modulo g. Together with the
integer part of h*a/g this determines a, using at most h slots. -/
theorem root_count {g h : ℕ} (gp : 0<g) (hp : 0<h) :
    (roots g h).card≤g.divisors.card*h := by
  classical
  let code (a : ℕ) := (g.gcd a,h*a/g)
  rw [show g.divisors.card*h=(g.divisors ×ˢ range h).card by simp]
  apply card_le_card_of_injOn (t:=g.divisors ×ˢ range h) code
  · intro a ha
    obtain ⟨al,_⟩ := mem_filter.mp ha
    exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,gp.ne'⟩,
      mem_range.mpr ((Nat.div_lt_iff_lt_mul gp).mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp al) hp))⟩
  · intro a ha b hb eq
    obtain ⟨_,ar⟩ := mem_filter.mp ha
    obtain ⟨_,br⟩ := mem_filter.mp hb
    have dg : g.gcd a=g.gcd b := congrArg Prod.fst eq
    have block : h*a/g=h*b/g := congrArg Prod.snd eq
    let d := g.gcd a
    let e := g/d
    have da : d∣a := Nat.gcd_dvd_right ..
    have db : d∣b := by dsimp only [d]; rw [dg]; exact Nat.gcd_dvd_right ..
    have ea : e∣a+h := remove_common gp ar
    have eb : e∣b+h := by simpa only [e,d,dg] using remove_common gp br
    have product : d*e=g := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
    have left := Nat.mul_dvd_mul da eb
    have right := Nat.mul_dvd_mul db ea
    rw [product,show a*(b+h)=a*b+h*a by ring] at left
    rw [product,show b*(a+h)=a*b+h*b by ring] at right
    have mod := Nat.ModEq.add_left_cancel' (a*b)
      ((Nat.modEq_zero_iff_dvd.mpr left).trans (Nat.modEq_zero_iff_dvd.mpr right).symm)
    change h*a%g=h*b%g at mod
    have equal : h*a=h*b := by
      rw [←Nat.mod_add_div (h*a) g,mod,block,Nat.mod_add_div]
    exact Nat.eq_of_mul_eq_mul_left hp equal

/-- The shifted factor-sum candidate D+k for the pair z. -/
def shiftSum (z : ℕ×ℕ) (k : ℕ) := z.1+z.2-1+k

/-- For each allowed g, reductions of p−1 give just the roots priced above. -/
theorem fixed_count {pairs : Finset (ℕ×ℕ)} {G k : ℕ}
    (valid : ∀ z∈pairs, 0<z.1 ∧ 0<z.2 ∧ shiftSum z k≤G ∧ shiftSum z k∣z.1*z.2+k) :
    pairs.card≤(∑ g∈Icc 1 G, g.divisors.card)*(k+1) := by
  classical
  let code (z : ℕ×ℕ) := (shiftSum z k,z.1-1)
  let box := (Icc 1 G).biUnion fun g => (roots g (k+1)).image (fun a => (g,a))
  have small : pairs.card≤box.card := by
    apply card_le_card_of_injOn code
    · rintro ⟨p,q⟩ hz
      obtain ⟨pp,qp,cap,dv⟩ := valid _ hz
      let g := shiftSum (p,q) k
      let a := p-1
      change g∣p*q+k at dv
      change g≤G at cap
      change 0<p at pp
      change 0<q at qp
      have pa : p=a+1 := by dsimp only [a]; omega
      have ge : g=a+q+k := by dsimp only [g,shiftSum,a]; omega
      have prod : g*p=p*q+k+a*(a+(k+1)) := by rw [ge,pa]; ring
      have root := Nat.dvd_sub (dvd_mul_right g p) dv
      rw [prod,Nat.add_sub_cancel_left] at root
      have grid : a∈roots g (k+1) := mem_filter.mpr ⟨mem_range.mpr (by omega),root⟩
      exact mem_biUnion.mpr ⟨g,mem_Icc.mpr ⟨by omega,cap⟩,mem_image.mpr ⟨a,grid,rfl⟩⟩
    · rintro ⟨p,q⟩ hp ⟨r,s⟩ hq eq
      have pp := (valid _ hp).1
      have rp := (valid _ hq).1
      have e₁ : p+q-1+k=r+s-1+k := congrArg Prod.fst eq
      have e₂ : p-1=r-1 := congrArg Prod.snd eq
      dsimp only at pp rp
      exact Prod.ext (by omega) (by omega)
  calc
    _ ≤ _ := small.trans card_biUnion_le
    _ ≤ ∑ g∈Icc 1 G, g.divisors.card*(k+1) := sum_le_sum fun g hg =>
      card_image_le.trans (root_count (mem_Icc.mp hg).1 (Nat.succ_pos k))
    _ = _ := (sum_mul ..).symm

attribute [local irreducible] MixedPrefixSample.eligible MixedPrefixSample.ordered
  MixedPrefixSample.primes MixedPrefixSample.sample

private theorem sample_bounds {z : ℕ×ℕ} (hz : z∈eligible) :
    65<z.1 ∧ z.1<z.2 ∧ z.2≤2*z.1 ∧ z.2<2^1024 := by
  rw [eligible,sample,mem_filter] at hz
  obtain ⟨both,lt⟩ := hz
  obtain ⟨p,q,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp both
  rw [primes,mem_filter,mem_Ico] at p q
  have lo := p.1.1
  have hi := q.1.2
  have lower : 65<X := by decide +kernel
  have upper : 2*X=2^1024 := by decide +kernel
  omega

private abbrev G : ℕ := 2^1025+64

noncomputable def pairsAt (k : ℕ) := eligible.filter fun z => shiftSum z k∣z.1*z.2+k
noncomputable def hitPairs := (Icc 1 64).biUnion pairsAt

private theorem sum_divisors : (∑ g∈Icc 1 G, g.divisors.card)≤713*G := by
  apply total_bound
  have lg := harmonic_le_one_add_log G
  have np : (0:ℝ)<(G:ℕ) := by exact_mod_cast (by decide +kernel : 0<G)
  have le : (G:ℝ)≤(2:ℝ)^1026 := by exact_mod_cast (by decide +kernel : G≤2^1026)
  have monotone := Real.log_le_log np le
  rw [Real.log_pow] at monotone
  have r : (harmonic G:ℝ)≤713 := lg.trans (by
    change Real.log (G:ℝ)≤1026*Real.log 2 at monotone
    linarith only [monotone,Real.log_two_lt_d9])
  exact_mod_cast r

/-- Grant every divisor of every shift. The union still has the specified
finite coverage on uniformly sampled sorted 1024-bit prime pairs. -/
theorem population : 2^976*hitPairs.card<eligible.card := by
  have each {k : ℕ} (hk : k∈Icc 1 64) : (pairsAt k).card≤713*G*(k+1) := by
    apply (fixed_count (G:=G) (pairs:=pairsAt k) ?_).trans (Nat.mul_le_mul_right _ sum_divisors)
    intro z hz
    rw [pairsAt,mem_filter] at hz
    obtain ⟨p,lt,_,q⟩ := sample_bounds (z:=z) hz.1
    have lim := (mem_Icc.mp hk).2
    have two : 2^1025=2*2^1024 := by decide +kernel
    refine ⟨by omega,by omega,?_,hz.2⟩
    dsimp only [G,shiftSum]
    omega
  have union : hitPairs.card≤(713*G)*2144 := calc
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ k∈Icc 1 64, (713*G)*(k+1) := sum_le_sum fun _ hk => each hk
    _ = _ := by rw [←mul_sum]; congr 1
  have scale : (21000000*2^976)*((713*G)*2144) ≤ 2^2046 := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using ((Nat.mul_le_mul_left _ union).trans scale).trans_lt
    ChebyshevPrimeSample.eligible_count

/-- Under the public exponent-size gate, even the direct E|F branch
forces the shifted sum itself to divide N+k. -/
theorem forced_by_gate {p q E k : ℕ} (pm : 65<p) (pq : p<q) (bal : q≤2*p)
    (lo : 0<k) (hi : k≤64) (ep : 0<E) (en : E≤p*q)
    (gate : 4*(p*q)≤(E+1)^2) (shift : E∣p*q+k)
    (hit : IntermediateTotientObstruction.Hit (p*q) E ((p-1)*(q-1))) :
    p+q-1+k∣p*q+k := by
  let F := (p-1)*(q-1)
  have total : F+(p+q)=p*q+1 := by
    have a : p-1+1=p := by omega
    have b : q-1+1=q := by omega
    change (p-1)*(q-1)+(p+q)=p*q+1
    nlinarith only [congrArg (fun z => z*(q-1)) a,congrArg (fun z => p*z) b,a]
  have fn : F<p*q := by omega
  have fp : 0<F := Nat.mul_pos (by omega) (by omega)
  have floor : 2*p≤E+1 := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    calc (2*p)^2=4*(p*p) := by ring
         _ ≤ 4*(p*q) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left p pq.le)
         _ ≤ _ := gate
  have branches := (IntermediateShiftedExponent.comparable_iff ep en fp fn lo (by omega) shift).mp hit
  rw [show p*q-F+k=p+q-1+k by omega] at branches
  rcases branches with a|b
  · have eq := Nat.eq_of_dvd_of_lt_two_mul (by omega) a (by omega)
    rwa [eq]
  · exact b.trans shift

open Classical in
/-- For k=1 alone the sharper 2^-988 bound applies to all gated hits. -/
theorem one_gated_fraction :
    2^988*(eligible.filter (fun z => ∃ E : ℕ, 0<E ∧ E≤z.1*z.2 ∧
      4*(z.1*z.2)≤(E+1)^2 ∧ E∣z.1*z.2+1 ∧
      IntermediateTotientObstruction.Hit (z.1*z.2) E ((z.1-1)*(z.2-1)))).card<eligible.card := by
  classical
  apply (Nat.mul_le_mul_left _ (card_le_card (t:=hits) ?_)).trans_lt eligible_fraction
  intro z hz
  obtain ⟨inside,E,ep,en,size,dv,hit⟩ := mem_filter.mp hz
  obtain ⟨p,lt,bal,_⟩ := sample_bounds (z:=z) inside
  have cond := forced_by_gate p lt bal (by decide : 0<1) (by decide) ep en size dv hit
  rw [hits,mem_filter]
  exact ⟨inside,by simpa only [Nat.sub_add_cancel (by omega : 1≤z.1+z.2)] using cond⟩

open Classical in
/-- Fraction for the actual nonnegative intermediate panel, including all
direct and nondirect hits and all adaptive menus of permitted exponents. -/
theorem gated_fraction :
    2^976*(eligible.filter (fun z => ∃ k∈Icc 1 64, ∃ E : ℕ,
      0<E ∧ E≤z.1*z.2 ∧ 4*(z.1*z.2)≤(E+1)^2 ∧ E∣z.1*z.2+k ∧
      IntermediateTotientObstruction.Hit (z.1*z.2) E ((z.1-1)*(z.2-1)))).card<eligible.card := by
  classical
  apply (Nat.mul_le_mul_left _ (card_le_card (t:=hitPairs) ?_)).trans_lt population
  intro z hz
  obtain ⟨inside,k,hk,E,ep,en,size,dv,hit⟩ := mem_filter.mp hz
  obtain ⟨p,lt,bal,_⟩ := sample_bounds (z:=z) inside
  obtain ⟨lo,hi⟩ := mem_Icc.mp hk
  apply mem_biUnion.mpr
  refine ⟨k,hk,?_⟩
  rw [pairsAt,mem_filter]
  exact ⟨inside,forced_by_gate p lt bal lo hi ep en size dv hit⟩

end PrimeFactors.ShiftedPrimeSumPopulation
