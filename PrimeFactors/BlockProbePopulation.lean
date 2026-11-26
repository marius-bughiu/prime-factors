import PrimeFactors.BlockSubresultantProbe
import PrimeFactors.SquareRootShiftPartners
import PrimeFactors.SquareRootPhasePopulation

/-! Successful quartic block probes over the uniform full-width prime-pair population.
The menu consists of (width, additive shift from the integer square root) pairs. -/
namespace PrimeFactors.BlockProbePopulation

open Finset MixedPrefixSample BlockSubresultantProbe

set_option maxRecDepth 4096
set_option exponentiation.threshold 4096

abbrev Setting := ℤ × ℤ

/-- Integer value submitted to the gcd, including signed offsets. -/
def reading (s : Setting) (n : ℕ) : ℤ := probe s.1 ((n.sqrt : ℤ)+s.2)

def split (s : Setting) (n : ℕ) : Prop :=
  let g := Int.gcd (reading s n) n
  1 < g ∧ g < n

/-- Each eligible unordered pair appears once, including hits on either prime. -/
noncomputable def successes (menu : Finset Setting) : Finset (ℕ×ℕ) := by
  classical exact eligible.filter fun z => ∃ s ∈ menu, split s (z.1*z.2)

private theorem target : 48 < X := by decide +kernel
attribute [local irreducible] X eligible primes sample ordered

/-- A fixed first prime permits at most eight odd integer partners for the
quartic. This also counts composite partners and whole-modulus gcds. -/
theorem eight_partners {p : ℕ} (hp : p∈primes) (s : Setting) (S : Finset ℕ)
    (range : ∀ q∈S, X≤q ∧ q<2*X ∧ q%2=1)
    (hit : ∀ q∈S, (p:ℤ) ∣ reading s (p*q)) : S.card ≤ 8 := by
  classical
  rw [primes] at hp
  obtain ⟨interval, prime⟩ := mem_filter.mp hp
  obtain ⟨pl, pu⟩ := mem_Ico.mp interval
  letI : Fact p.Prime := ⟨prime⟩
  have nonzero : (48 : ZMod p) ≠ 0 := by
    intro bad
    have h := (ZMod.natCast_zmod_eq_zero_iff_dvd 48 p).mp bad
    have slim := Nat.le_of_dvd (by decide : 0<48) h
    have := target
    omega
  let F : Polynomial (ZMod p) := Polynomial.C 48 * Polynomial.X^4 -
    Polynomial.C (24*(1+(s.1 : ZMod p)^2))*Polynomial.X^2 +
    Polynomial.C (((s.1 : ZMod p)^2-1)^3)
  have degree : F.natDegree = 4 := by
    dsimp only [F]
    compute_degree!
  have nz : F ≠ 0 := by intro zero; rw [zero, Polynomial.natDegree_zero] at degree; contradiction
  have cap := SquareRootShiftPartners.polynomial pl pu S F nz (s.2 : ZMod p) range (by
    intro q hq
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hit q hq)
    unfold reading probe at h
    push_cast at h
    simpa [F] using h)
  simpa [degree] using cap

private noncomputable def partnerSet (p : ℕ) (s : Setting) : Finset ℕ :=
  (Ico X (2*X)).filter fun q => q%2=1 ∧ (p:ℤ) ∣ reading s (p*q)

private noncomputable def pairs (s : Setting) : Finset (ℕ×ℕ) :=
  primes.biUnion fun p => (partnerSet p s).image fun q => (min p q,max p q)

private theorem per_setting (s : Setting) : (pairs s).card ≤ primes.card*8 := by
  apply card_biUnion_le_card_mul
  intro p hp
  apply card_image_le.trans (eight_partners hp s _ ?_ ?_)
  · intro q hq
    obtain ⟨interval, odd, _⟩ := mem_filter.mp hq
    exact ⟨(mem_Ico.mp interval).1,(mem_Ico.mp interval).2,odd⟩
  · exact fun _ hq => (mem_filter.mp hq).2.2

/-- Any nonunit integer reading vanishes at at least one of the two primes. -/
theorem prime_dvd_reading {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (a : ℤ)
    (hit : 1 < Int.gcd a (p*q:ℕ)) : (p:ℤ) ∣ a ∨ (q:ℤ) ∣ a := by
  have gnot : Int.gcd a (p*q:ℕ) ≠ 1 := Nat.ne_of_gt hit
  obtain ⟨r, prime, rd⟩ := Nat.exists_prime_and_dvd gnot
  have left := (Int.natCast_dvd_natCast.mpr rd).trans (Int.gcd_dvd_left ..)
  have right := (Int.natCast_dvd_natCast.mpr rd).trans (Int.gcd_dvd_right ..)
  have cases := prime.dvd_mul.mp (Int.natCast_dvd_natCast.mp right)
  rcases cases with point | point
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq prime pp).mp point ▸ left)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq prime qp).mp point ▸ left)

private theorem partner_bounds {p : ℕ} (hp : p∈primes) :
    p∈Ico X (2*X) ∧ p%2=1 ∧ p.Prime := by
  rw [primes] at hp
  obtain ⟨h,pr⟩ := mem_filter.mp hp
  have b := (mem_Ico.mp h).1
  have ne : p≠2 := by have := target; omega
  obtain ⟨k,hk⟩ := pr.odd_of_ne_two ne
  exact ⟨h,by omega,pr⟩

/-- Either prime may be the one where a square-root residue occurs. -/
theorem mem_detected (R : (p : ℕ) → Finset (ZMod p)) {z : ℕ×ℕ} (mem : z∈eligible)
    (hit : ((z.1*z.2).sqrt : ZMod z.1) ∈ R z.1 ∨ ((z.1*z.2).sqrt : ZMod z.2) ∈ R z.2) :
    z∈SquareRootShiftPartners.detected R := by
  rw [eligible,sample] at mem
  obtain ⟨ord,lt⟩ := mem_filter.mp mem
  obtain ⟨pm,qm,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp ord
  obtain ⟨pi,po,_⟩ := partner_bounds pm
  obtain ⟨qi,qo,_⟩ := partner_bounds qm
  rcases hit with h|h
  · refine mem_biUnion.mpr ⟨z.1,pm,mem_image.mpr ⟨z.2,mem_filter.mpr ⟨qi,qo,h⟩,?_⟩⟩
    simp [min_eq_left lt.le,max_eq_right lt.le]
  · refine mem_biUnion.mpr ⟨z.2,qm,mem_image.mpr ⟨z.1,mem_filter.mpr ⟨pi,po,?_⟩,?_⟩⟩
    · simpa [Nat.mul_comm] using h
    · simp [min_eq_right lt.le,max_eq_left lt.le]

/-- A general cap for arbitrary local residue menus, allowing detection on either factor. -/
theorem residue_count (R : (p : ℕ) → Finset (ZMod p)) {D : ℕ}
    (cap : ∀ p∈primes, (R p).card ≤ D) :
    (SquareRootShiftPartners.detected R ∩ eligible).card ≤ primes.card*(2*D) := by
  classical
  apply (card_le_card inter_subset_left).trans
  apply card_biUnion_le_card_mul
  intro p hp
  have ib := mem_Ico.mp (partner_bounds hp).1
  apply card_image_le.trans
  apply (SquareRootShiftPartners.count ib.1 ib.2 _ (R p) ?_ ?_).trans
    (Nat.mul_le_mul_left 2 (cap p hp))
  · intro q h
    obtain ⟨interval,odd,_⟩ := mem_filter.mp h
    exact ⟨(mem_Ico.mp interval).1,(mem_Ico.mp interval).2,odd⟩
  · exact fun _ h => (mem_filter.mp h).2.2

private theorem normalize {x hits p k total : ℕ} (positive : 0<k)
    (cost : hits ≤ p*k) (base : x*p < 41056*total) :
    x*hits < (41056*k)*total := by
  calc
    _ ≤ x*(p*k) := Nat.mul_le_mul_left _ cost
    _ = (x*p)*k := (Nat.mul_assoc ..).symm
    _ < (41056*total)*k := Nat.mul_lt_mul_of_pos_right base positive
    _ = _ := by ac_rfl

private theorem two_price (d t : ℕ) : (41056*(2*d))*t = (82112*d)*t := by ring
private theorem eight_price (d t : ℕ) : (41056*(8*d))*t = (328448*d)*t := by ring

/-- Normalize the arbitrary-residue bound over the actual prime-pair population. -/
theorem residue_fraction (R : (p : ℕ) → Finset (ZMod p)) {D : ℕ} (pos : 0<D)
    (cap : ∀ p∈primes, (R p).card ≤ D) :
    X*(SquareRootShiftPartners.detected R ∩ eligible).card < (82112*D)*eligible.card := by
  rw [←two_price]
  exact normalize (Nat.mul_pos (by decide) pos) (residue_count R cap) SquareRootPhasePopulation.marginal

private theorem in_pairs {s : Setting} {z : ℕ×ℕ} (mem : z∈eligible)
    (hit : split s (z.1*z.2)) : z∈pairs s := by
  classical
  rw [eligible,sample] at mem
  obtain ⟨ord,lt⟩ := mem_filter.mp mem
  obtain ⟨pm,qm,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp ord
  obtain ⟨pi,po,pp⟩ := partner_bounds pm
  obtain ⟨qi,qo,qp⟩ := partner_bounds qm
  rcases prime_dvd_reading pp qp _ hit.1 with ph|qh
  · refine mem_biUnion.mpr ⟨z.1,pm,mem_image.mpr ⟨z.2,mem_filter.mpr ⟨qi,qo,ph⟩,?_⟩⟩
    simp [min_eq_left lt.le,max_eq_right lt.le]
  · refine mem_biUnion.mpr ⟨z.2,qm,mem_image.mpr ⟨z.1,mem_filter.mpr ⟨pi,po,?_⟩,?_⟩⟩
    · simpa [Nat.mul_comm] using qh
    · simp [min_eq_right lt.le,max_eq_left lt.le]

/-- Absolute count for any finite public menu. The union permits an arbitrary
product-dependent choice of trials *from this menu*. -/
theorem menu_count (menu : Finset Setting) :
    (successes menu).card ≤ menu.card*(primes.card*8) := by
  classical
  apply (card_le_card (t:=menu.biUnion pairs) ?_).trans
    (card_biUnion_le_card_mul _ _ _ fun s _ => per_setting s)
  intro z hz
  obtain ⟨mem,s,hs,hit⟩ := mem_filter.mp hz
  exact mem_biUnion.mpr ⟨s,hs,in_pairs mem hit⟩

/-- Exact integer upper bound on the fraction of prime pairs that a nonempty
menu can split, using the fully checked prime marginal, with no distribution
assumption about square-root residues. -/
theorem menu_fraction (menu : Finset Setting) (nonempty : menu.Nonempty) :
    X*(successes menu).card < 328448*menu.card*eligible.card := by
  rw [←eight_price]
  have h : (successes menu).card ≤ primes.card*(8*menu.card) := by
    exact (menu_count menu).trans_eq (by ac_rfl)
  exact normalize (Nat.mul_pos (by decide) nonempty.card_pos) h SquareRootPhasePopulation.marginal

/-- Each tested width/offset pair costs at most one factor of 2^-1004 in
the upper bound on success probability. -/
theorem dyadic_fraction (menu : Finset Setting) (nonempty : menu.Nonempty) :
    2^1004*(successes menu).card < menu.card*eligible.card := by
  have room : 328448*2^1004 ≤ X := by rw [X]; decide +kernel
  have h := (Nat.mul_le_mul_right (successes menu).card room).trans_lt (menu_fraction menu nonempty)
  apply Nat.lt_of_mul_lt_mul_left (a:=328448)
  simpa only [Nat.mul_assoc] using h

private theorem single_bound (s t b : ℕ) (eq : s=1) (h : b<s*t) : b<t := by
  rw [eq, Nat.one_mul] at h
  exact h

/-- The actual width-three, zero-offset setting of the benchmark. -/
theorem benchmark_quartic :
    2^1004*(successes {(3,0)}).card < eligible.card := by
  exact single_bound _ _ _ (card_singleton ((3,0) : Setting))
    (dyadic_fraction {(3,0)} (singleton_nonempty _))

private theorem half_square {p a b : ℕ} [Fact p.Prime] (ha : 2*a<p) (hb : 2*b<p)
    (same : (a : ZMod p)^2=(b:ZMod p)^2) : a=b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp same with h|h
  · have e := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
    simpa [Nat.mod_eq_of_lt (by omega : a<p),Nat.mod_eq_of_lt (by omega : b<p)] using e
  · have zero : ((a+b:ℕ):ZMod p)=0 := by rw [Nat.cast_add,h,neg_add_cancel]
    have dvd := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp zero
    have e : a+b=0 := Nat.eq_zero_of_dvd_of_lt dvd (by omega)
    omega

private theorem shape {B p q : ℕ} (bp : B≤p) (hp : p<2*B) (bq : B≤q) (hq : q<2*B) :
    let t := (p*q).sqrt
    (q<p → t<p ∧ p<2*t) ∧ (p≤q → p≤t ∧ 2*t<3*p) := by
  let t := (p*q).sqrt
  change (_ → t<_ ∧ _<2*t) ∧ (_ → _≤t ∧ 2*t<_)
  have pp : 0<p := by omega
  constructor
  · intro smaller
    have lo : q≤t := Nat.le_sqrt.mpr (Nat.mul_le_mul_right q smaller.le)
    exact ⟨Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_left smaller pp),by omega⟩
  · intro larger
    refine ⟨Nat.le_sqrt.mpr (Nat.mul_le_mul_left p larger),?_⟩
    have sq : t^2 ≤ p*q := Nat.sqrt_le' _
    have cap := Nat.mul_lt_mul_of_pos_left (by omega : q<2*p) pp
    by_contra! bad
    have ae := Nat.pow_le_pow_left bad 2
    nlinarith only [ae,sq,cap,Nat.zero_le (p*p)]

private theorem gap {p a b t j : ℕ} (sa : (p*a).sqrt=t) (sb : (p*b).sqrt=t)
    (height : 2*t+1 ≤ j*p) : b<a+j := by
  have lo := Nat.sqrt_le' (p*a)
  have hi := Nat.lt_succ_sqrt' (p*b)
  rw [sa] at lo; rw [sb] at hi
  by_contra! far
  have dist := Nat.mul_le_mul_left p far
  nlinarith only [dist,lo,hi,height]

private theorem same_side {p t u : ℕ} [Fact p.Prime]
    (h : (t<p ∧ u<p ∧ p<2*t ∧ p<2*u) ∨ (p≤t ∧ p≤u ∧ 2*t<3*p ∧ 2*u<3*p))
    (sq : (t:ZMod p)^2=(u:ZMod p)^2) : t=u := by
  rcases h with ⟨a,b,c,d⟩ | ⟨a,b,c,d⟩
  · have e : ((p-t:ℕ):ZMod p)^2=((p-u:ℕ):ZMod p)^2 := by
      rw [Nat.cast_sub a.le,Nat.cast_sub b.le, ZMod.natCast_self,zero_sub,zero_sub,
        neg_sq,neg_sq,sq]
    have h := half_square (by omega : 2*(p-t)<p) (by omega : 2*(p-u)<p) e
    omega
  · have e : ((t-p:ℕ):ZMod p)^2=((u-p:ℕ):ZMod p)^2 := by
      rw [Nat.cast_sub a,Nat.cast_sub b, ZMod.natCast_self,sub_zero,sub_zero,sq]
    have h := half_square (by omega : 2*(t-p)<p) (by omega : 2*(u-p)<p) e
    omega

/-- If the permitted squared residues of the unshifted square root form a set R,
there are at most three odd partners per member of R. A smaller partner occupies
one tag and a larger partner occupies at most two tags. -/
theorem square_partners {B p : ℕ} [Fact p.Prime] (bp : B≤p) (hp : p<2*B)
    (S : Finset ℕ) (R : Finset (ZMod p))
    (bounds : ∀ q∈S, B≤q ∧ q<2*B ∧ q%2=1)
    (hit : ∀ q∈S, ((p*q).sqrt : ZMod p)^2∈R) :
    S.card ≤ 3*R.card := by
  let tag (q : ℕ) : Fin 3 := if q<p then 0 else ⟨q/2%2+1,by omega⟩
  let key (q : ℕ) : ZMod p × Fin 3 := (((p*q).sqrt : ZMod p)^2,tag q)
  have inject : (S : Set ℕ).InjOn key := by
    intro a ha b hb equal
    obtain ⟨al,au,ao⟩ := bounds a ha
    obtain ⟨bl,bu,bo⟩ := bounds b hb
    have sr := congrArg Prod.fst equal
    have tt : (tag a).val=(tag b).val := congrArg (fun x : ZMod p×Fin 3 => x.2.val) equal
    have ash := shape bp hp al au
    have bsh := shape bp hp bl bu
    by_cases ax : a<p <;> by_cases bx : b<p
    · obtain ⟨a1,a2⟩ := ash.1 ax
      obtain ⟨b1,b2⟩ := bsh.1 bx
      have eq := same_side (Or.inl ⟨a1,b1,a2,b2⟩) sr
      have gap1 := gap rfl eq.symm (by omega : 2*(p*a).sqrt+1 ≤ 2*p)
      have gap2 := gap eq.symm rfl (by omega : 2*(p*a).sqrt+1 ≤ 2*p)
      omega
    · simp [tag,ax,bx] at tt
    · simp [tag,ax,bx] at tt
    · obtain ⟨a1,a2⟩ := ash.2 (by omega)
      obtain ⟨b1,b2⟩ := bsh.2 (by omega)
      have eq := same_side (Or.inr ⟨a1,b1,a2,b2⟩) sr
      have gap1 := gap rfl eq.symm (by omega : 2*(p*a).sqrt+1 ≤ 3*p)
      have gap2 := gap eq.symm rfl (by omega : 2*(p*a).sqrt+1 ≤ 3*p)
      simp [tag,ax,bx] at tt
      omega
  have total := card_le_card_of_injOn (t:=R ×ˢ (univ : Finset (Fin 3))) key
    (fun _ h => mem_product.mpr ⟨hit _ h,mem_univ _⟩) inject
  simpa [Nat.mul_comm] using total
/-- For zero offset the quartic is quadratic in the squared square-root residue.
An eight-partner bound therefore sharpens to six without averaging over p. -/
theorem six_partners {p : ℕ} (hp : p∈primes) (m : ℤ) (S : Finset ℕ)
    (range : ∀ q∈S, X≤q ∧ q<2*X ∧ q%2=1)
    (hit : ∀ q∈S, (p:ℤ) ∣ reading (m,0) (p*q)) : S.card ≤ 6 := by
  classical
  obtain ⟨ip,_,prime⟩ := partner_bounds hp
  obtain ⟨pl,pu⟩ := mem_Ico.mp ip
  letI : Fact p.Prime := ⟨prime⟩
  have nz48 : (48:ZMod p)≠0 := by
    intro he
    have h := Nat.le_of_dvd (by decide : 0<48) ((ZMod.natCast_zmod_eq_zero_iff_dvd 48 p).mp he)
    have := target
    omega
  let F : Polynomial (ZMod p) := Polynomial.C 48*Polynomial.X^2-
    Polynomial.C (24*(1+(m:ZMod p)^2))*Polynomial.X+Polynomial.C (((m:ZMod p)^2-1)^3)
  have d : F.natDegree=2 := by dsimp only [F]; compute_degree!
  have nzero : F≠0 := by intro eq; rw [eq,Polynomial.natDegree_zero] at d; contradiction
  have supported (q : ℕ) (hq : q∈S) : ((p*q).sqrt:ZMod p)^2∈F.roots.toFinset := by
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots nzero).mpr
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hit q hq)
    simp only [reading,probe,Int.cast_add,Int.cast_sub,Int.cast_ofNat,Int.cast_mul,
      Int.cast_pow,Int.cast_zero,Int.cast_one,Int.cast_natCast,add_zero] at h
    simpa [Polynomial.IsRoot,F,←pow_mul] using h
  have limit := square_partners pl pu S F.roots.toFinset range supported
  have dc := (Multiset.toFinset_card_le _).trans F.card_roots'
  rw [d] at dc
  omega

/-- A public width of any size and no shift can reveal a divisor on fewer
than one in 2^1005 target products. -/
theorem zero_offset_fraction (m : ℤ) :
    2^1005*(successes {(m,0)}).card < eligible.card := by
  classical
  have per : (pairs (m,0)).card ≤ primes.card*6 := by
    apply card_biUnion_le_card_mul
    intro p hp
    apply card_image_le.trans (six_partners hp m _ ?_ ?_)
    · intro q hq
      obtain ⟨interval,odd,_⟩ := mem_filter.mp hq
      exact ⟨(mem_Ico.mp interval).1,(mem_Ico.mp interval).2,odd⟩
    · exact fun _ hq => (mem_filter.mp hq).2.2
  have cover : successes {(m,0)} ⊆ pairs (m,0) := by
    intro z hz
    obtain ⟨mem,s,hs,hit⟩ := mem_filter.mp hz
    rw [mem_singleton.mp hs] at hit
    exact in_pairs mem hit
  have growth := normalize (by decide : 0<6) ((card_le_card cover).trans per)
    SquareRootPhasePopulation.marginal
  have room : (41056*6)*2^1005 ≤ X := by rw [X]; decide +kernel
  have cmp := (Nat.mul_le_mul_right (successes {(m,0)}).card room).trans_lt growth
  apply Nat.lt_of_mul_lt_mul_left (a:=41056*6)
  rwa [Nat.mul_assoc] at cmp

end PrimeFactors.BlockProbePopulation
