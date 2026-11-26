import PrimeFactors.FactorLaneAdvice
import PrimeFactors.UniformDivisorCount
import PrimeFactors.ShiftedEndpointPopulation

/-! Count carry predictions chosen from a whole low product word. A proposed
signed product fixes both displacements up to a choice of a signed divisor.
The anchor coefficients need not be nearest, positive, or bounded. -/

namespace PrimeFactors.LowBitsCarryMenu

open Finset

set_option exponentiation.threshold 65536

/-- Any translated factor pair giving the proposed residual product. -/
def Lift (D p q : ℕ) (w : ℤ) : Prop :=
  ∃ A B : ℤ, w=((p:ℤ)-A*D)*((q:ℤ)-B*D)

private def residues (D : ℕ) (w : ℤ) : Finset ℕ :=
  w.natAbs.divisors.image (fun t => t%D) ∪
    w.natAbs.divisors.image (fun t : ℕ => ((-(t:ℤ))%(D:ℤ)).toNat)

private theorem residue_count (D : ℕ) (w : ℤ) : (residues D w).card≤2*w.natAbs.divisors.card := by
  rw [two_mul]; exact (card_union_le ..).trans (Nat.add_le_add card_image_le card_image_le)

private theorem residue_mem {D p q : ℕ} {w : ℤ} (nz : w≠0) (lift : Lift D p q w) :
    p%D∈residues D w := by
  obtain ⟨A,B,h⟩ := lift
  let u := (p:ℤ)-A*D
  have dvd : u∣w := ⟨(q:ℤ)-B*D,h⟩
  have mem := Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr dvd,Int.natAbs_ne_zero.mpr nz⟩
  have same : u ≡ (p:ℤ) [ZMOD (D:ℤ)] := Int.modEq_iff_dvd.mpr ⟨A,by dsimp [u]; ring⟩
  by_cases pos : 0≤u
  · apply mem_union_left; apply mem_image.mpr; refine ⟨u.natAbs,mem,?_⟩
    exact Int.natCast_modEq_iff.mp (by simpa only [Int.natCast_natAbs,abs_of_nonneg pos] using same)
  · apply mem_union_right; apply mem_image.mpr; refine ⟨u.natAbs,mem,?_⟩
    have eq := congrArg Int.toNat same.eq
    simpa only [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge pos),neg_neg,←Int.natCast_mod,Int.toNat_natCast] using eq

/-- Each possible full low word identifies a unique partner in [Q,2Q) once
p is known. Pairs in this word with fixed w have at most two signed first
residues for every positive divisor of |w|. -/
private theorem word_count {hits : Finset (ℕ×ℕ)} {B D Q c : ℕ} {w : ℤ}
    (dp : 0<D) (nz : w≠0)
    (support : ∀ x∈hits, B*D≤x.1 ∧ x.1<2*B*D ∧ Q≤x.2 ∧ x.2<2*Q ∧ Q.Coprime x.1 ∧
      x.1*x.2%Q=c ∧ Lift D x.1 x.2 w) : hits.card ≤ (2*w.natAbs.divisors.card)*B := by
  have count := FactorLaneAdvice.one_word_bound (A:=residues D w) (codes:={c}) dp (fun n => n%Q)
    (fun x hx => ⟨(support x hx).1,(support x hx).2.1,residue_mem nz (support x hx).2.2.2.2.2.2,
      mem_singleton.mpr (support x hx).2.2.2.2.2.1⟩) (by
      intro p q r hq hr eq
      obtain ⟨_,_,lq,uq,cop,_,_⟩ := support (p,q) hq
      obtain ⟨_,_,lr,ur,_,_,_⟩ := support (p,r) hr
      have rel : q ≡ r [MOD Q] := Nat.ModEq.cancel_left_of_coprime cop eq
      have rel' : (q-Q) ≡ (r-Q) [MOD Q] := Nat.ModEq.add_right_cancel' Q (by simpa [Nat.sub_add_cancel lq,Nat.sub_add_cancel lr] using rel)
      have := rel'.eq_of_lt_of_lt (by omega) (by omega); omega)
  simpa only [card_singleton,mul_one] using count.trans (Nat.mul_le_mul_right 1 (Nat.mul_le_mul_right B (residue_count D w)))

/-- At most J public outputs per product word, and at most T positive divisors
per nonzero output. Counting the E odd words uses the whole Q=2E low word. -/
theorem menu_count {pairs : Finset (ℕ×ℕ)} {D Q B E J T : ℕ} (menu : ℕ → Finset ℤ)
    (dp : 0<D) (even : Q=2*E) (slots : ∀ c<E, (menu (2*c+1)).card≤J)
    (sizes : ∀ c<E, ∀ w∈menu (2*c+1), w≠0 ∧ w.natAbs.divisors.card≤T)
    (support : ∀ x∈pairs, B*D≤x.1 ∧ x.1<2*B*D ∧ Q≤x.2 ∧ x.2<2*Q ∧ Q.Coprime x.1 ∧
      Odd (x.1*x.2) ∧ ∃ w∈menu (x.1*x.2%Q), Lift D x.1 x.2 w) :
    pairs.card ≤ Q*(J*(T*B)) := by
  classical
  let row (c : ℕ) (w : ℤ) := pairs.filter fun x => x.1*x.2%Q=2*c+1 ∧ Lift D x.1 x.2 w
  have subset : pairs ⊆ (range E).biUnion (fun c => (menu (2*c+1)).biUnion (row c)) := by
    intro x hx; obtain ⟨_,_,_,_,_,⟨s,hs⟩,w,hw,hit⟩ := support x hx
    have Qp : 0<Q := by have := (support x hx).2.2.2.1; omega
    let r := x.1*x.2%Q
    have decomp : r+2*(E*((x.1*x.2)/Q))=2*s+1 := by
      rw [←Nat.mul_assoc,←even]; exact (Nat.mod_add_div ..).trans hs
    have hi : r<Q := Nat.mod_lt _ Qp
    have odd : r=2*(r/2)+1 := by omega
    refine mem_biUnion.mpr ⟨r/2,mem_range.mpr (by omega),mem_biUnion.mpr ⟨w,odd ▸ hw,?_⟩⟩
    exact mem_filter.mpr ⟨hx,odd,hit⟩
  have each (c : ℕ) (hc : c<E) (w : ℤ) (hw : w∈menu (2*c+1)) : (row c w).card ≤ (2*T)*B := by
    obtain ⟨nz,cost⟩ := sizes c hc w hw
    apply (word_count (Q:=Q) (c:=2*c+1) dp nz ?_).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ cost))
    intro x hx; obtain ⟨mem,eq,h⟩ := mem_filter.mp hx
    obtain ⟨pl,ph,ql,qh,unit,_,_⟩ := support x mem
    exact ⟨pl,ph,ql,qh,unit,eq,h⟩
  have total := card_biUnion_le_card_mul (range E) (fun c => (menu (2*c+1)).biUnion (row c))
    (J*((2*T)*B)) (fun c hc => (card_biUnion_le_card_mul _ _ _ (each c (mem_range.mp hc))).trans
      (Nat.mul_le_mul_right _ (slots c (mem_range.mp hc))))
  calc
    _ ≤ _ := (card_le_card subset).trans total
    _ = _ := by rw [card_range,even]; ring

/-- Predicted signed residual product for a public, possibly large carry. -/
def output (n D : ℕ) (k : ℤ) : ℤ :=
  n-(D:ℤ)*PredictedTraceCarries.nearest n D+D*k

/-- The residual can be computed from any product word whose modulus contains
D. This statement also fixes the convention at half ties. -/
theorem output_mod {D Q : ℕ} (pos : 0<D) (dvd : D∣Q) (n : ℕ) (k : ℤ) :
    output (n%Q) D k=output n D k := by
  obtain ⟨c,dc⟩ := dvd
  have eq : (n:ℤ)=(n%Q:ℕ)+(D:ℤ)*(c*(n/Q:ℕ)) := by
    exact_mod_cast (show n=n%Q+D*(c*(n/Q)) by rw [←Nat.mul_assoc,←dc,Nat.mod_add_div])
  unfold output; conv_rhs => rw [eq,PredictedTraceCarries.nearest_shift (by exact_mod_cast pos)]
  ring

/-- At every dyadic radix divisible by four the two centered odd residuals
are strictly inside the half-radix bounds: an even endpoint cannot be an
odd residual. Arbitrary anchors in `Lift` need not satisfy this cap. -/
theorem centered_size {p q m : ℤ} (mp : 0<m) (po : Odd p) (qo : Odd q) :
    |(p-4*m*PredictedTraceCarries.nearest p (4*m))*(q-4*m*PredictedTraceCarries.nearest q (4*m))| < (2*m)^2 := by
  have bound (x : ℤ) (odd : Odd x) : |x-4*m*PredictedTraceCarries.nearest x (4*m)|<2*m := by
    obtain ⟨j,hj⟩ := odd
    have cap := PredictedTraceCarries.nearest_error (n:=x) (show (0:ℤ)<4*m by omega)
    rw [mul_assoc] at cap ⊢
    rcases le_total 0 (x-4*(m*PredictedTraceCarries.nearest x (4*m))) with pos|neg
    · rw [abs_of_nonneg pos] at cap ⊢; omega
    · rw [abs_of_nonpos neg] at cap ⊢; omega
  rw [abs_mul,sq]
  exact mul_lt_mul_of_nonneg_of_pos (bound p po) (bound q qo).le (abs_nonneg _) (by omega)

/-- Every proper output, including an incidental square at arbitrary high
carry, yields an actual signed factorization of the predicted residual. -/
theorem lift_of_probe {p q D f : ℕ} {h k : ℤ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (hit : PredictedTraceCarries.probe (p*q) D h k=some f) : Lift D p q (output (p*q) D k) := by
  obtain ⟨a,b,c,t⟩ := ShiftedEndpointPopulation.probe_allocation pp qp ne hit
  unfold PredictedTraceCarries.label at t
  rw [c] at t
  refine ⟨a,b,?_⟩; unfold output; push_cast at t ⊢; linear_combination -(D:ℤ)*t

/-- Membership in the counted population. The factor pair, the high carry,
and the choice of lower carry from the entire allowed menu can vary by input. -/
def Accepted (menu : ℕ → Finset ℤ) (D p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p≠q ∧ 2^1023≤p ∧ p<2^1024 ∧ 2^1023≤q ∧ q<2^1024 ∧
    ∃ k∈menu (p*q%2^1023), ∃ h f, PredictedTraceCarries.probe (p*q) D h k=some f

private theorem nonzero_output {D r : ℕ} (pos : r%2=1) (even : Even D) (k : ℤ) :
    output r D k≠0 := by
  intro zero
  obtain ⟨j,h⟩ := even
  unfold output at zero
  have eq : (r:ℤ) = 2*((j:ℤ)*(PredictedTraceCarries.nearest r D-k)) := by
    have evenZ : (D:ℤ)=2*j := by exact_mod_cast (by omega : D=2*j)
    rw [evenZ] at zero ⊢; linarith only [zero]
  omega

/-- Generic target bound in terms of the ambient full-factor block count B.
Only the residual magnitudes on usable menu entries enter the divisor bound. -/
theorem target_count {pairs : Finset (ℕ×ℕ)} {J D B T : ℕ} (menu : ℕ → Finset ℤ)
    (dp : 0<D) (even : Even D) (blocks : B*D=2^1023)
    (slots : ∀ r<2^1023, r%2=1 → (menu r).card≤J)
    (cap : ∀ r<2^1023, r%2=1 → ∀ k∈menu r, (output r D k).natAbs.divisors.card≤T)
    (support : ∀ z∈pairs, Accepted menu D z.1 z.2) : pairs.card ≤ 2^1023*(J*(T*B)) := by
  let words (r : ℕ) := (menu r).image (output r D)
  have split : (2:ℕ)^1023=2*2^1022 := by decide +kernel
  have upper : (2:ℕ)^1024=2*2^1023 := by decide +kernel
  have wordlt {c : ℕ} (hc : c<2^1022) : 2*c+1<2^1023 := by omega
  refine menu_count words dp split (fun c hc => card_image_le.trans (slots _ (wordlt hc) (by omega))) ?_ ?_
  · intro c hc w hw; obtain ⟨k,hk,rfl⟩ := mem_image.mp hw
    exact ⟨nonzero_output (by omega) even k,cap _ (wordlt hc) (by omega) k hk⟩
  · intro z hz; obtain ⟨pp,qp,ne,pl,pu,ql,qu,k,hk,h,f,hit⟩ := support z hz
    have pl' : 2<z.1 := lt_of_lt_of_le (by decide +kernel) pl
    have ql' : 2<z.2 := lt_of_lt_of_le (by decide +kernel) ql
    have po := pp.odd_of_ne_two pl'.ne'; have qo := qp.odd_of_ne_two ql'.ne'
    have dvd : D∣2^1023 := ⟨B,by rw [←blocks,mul_comm]⟩
    refine ⟨blocks ▸ pl,?_,ql,upper ▸ qu,po.coprime_two_left.pow_left _,po.mul qo,output (z.1*z.2) D k,?_,
      lift_of_probe pp qp ne hit⟩
    · simpa only [Nat.mul_assoc,blocks,←upper] using pu
    · exact mem_image.mpr ⟨k,hk,output_mod dp dvd _ _⟩

private theorem div_704 {m : ℕ} (pos : 0<m) (small : m<2^1406) : m.divisors.card ≤ 5*2^176 := by
  apply (Nat.pow_le_pow_iff_left (by decide : 336≠0)).mp
  exact (UniformDivisorCount.below_power_two pos small).le.trans (by decide +kernel)

private theorem div_640 {m : ℕ} (pos : 0<m) (small : m<2^1278) : m.divisors.card ≤ 17*2^162 := by
  apply (Nat.pow_le_pow_iff_left (by decide : 336≠0)).mp
  exact (UniformDivisorCount.below_power_two pos small).le.trans (by decide +kernel)

/-- Convert the finite integer count using an explicit lower bound for the
number of eligible unordered prime pairs. -/
private theorem price {A J T B f pop : ℕ} (count : A≤2^1023*(J*(T*B)))
    (den : 2^2046<21000000*pop) (jp : 0<J) (budget : f*(T*B)*21000000≤2^1023) :
    f*A<J*pop := by
  have scaled : f*A*21000000 ≤ J*2^2046 := calc
    _ ≤ f*(2^1023*(J*(T*B)))*21000000 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ count)
    _ = (J*2^1023)*(f*(T*B)*21000000) := by ac_rfl
    _ ≤ (J*2^1023)*2^1023 := Nat.mul_le_mul_left _ budget
    _ = _ := by rw [Nat.mul_assoc,←pow_add]
  have strict := scaled.trans_lt (Nat.mul_lt_mul_of_pos_left den jp)
  exact Nat.lt_of_mul_lt_mul_right (by simpa only [mul_left_comm J 21000000, mul_comm 21000000,←mul_assoc] using strict)

/-- Any positive-size menu of lower carries read from up to 1,023 low bits,
at radix 2^704, even with unlimited high carry and accidental proper gcds. -/
theorem at_704 {pairs : Finset (ℕ×ℕ)} {J pop : ℕ} (menu : ℕ → Finset ℤ) (jp : 0<J)
    (den : 2^2046<21000000*pop) (slots : ∀ r<2^1023, r%2=1 → (menu r).card≤J)
    (cap : ∀ r<2^1023, r%2=1 → ∀ k∈menu r, (output r (2^704) k).natAbs<2^1406)
    (support : ∀ z∈pairs, Accepted menu (2^704) z.1 z.2) : 2^501*pairs.card<J*pop := by
  have bound := target_count (B:=2^319) menu (by decide +kernel) (by decide +kernel)
    (by decide +kernel) slots (fun r hr odd k hk => div_704
      (Int.natAbs_pos.mpr (nonzero_output odd (by decide +kernel) k)) (cap r hr odd k hk)) support
  exact price bound den jp (by decide +kernel)

/-- The analogous bound at radix 2^640. -/
theorem at_640 {pairs : Finset (ℕ×ℕ)} {J pop : ℕ} (menu : ℕ → Finset ℤ) (jp : 0<J)
    (den : 2^2046<21000000*pop) (slots : ∀ r<2^1023, r%2=1 → (menu r).card≤J)
    (cap : ∀ r<2^1023, r%2=1 → ∀ k∈menu r, (output r (2^640) k).natAbs<2^1278)
    (support : ∀ z∈pairs, Accepted menu (2^640) z.1 z.2) : 2^449*pairs.card<J*pop := by
  have bound := target_count (B:=2^383) menu (by decide +kernel) (by decide +kernel)
    (by decide +kernel) slots (fun r hr odd k hk => div_640
      (Int.natAbs_pos.mpr (nonzero_output odd (by decide +kernel) k)) (cap r hr odd k hk)) support
  exact price bound den jp (by decide +kernel)

/-- For a fixed product in the unit group the first coordinate determines
the second one, including its image in a smaller residue group. -/
private def productFiber {G H : Type*} [Group G] [Group H] (f : G →* H) (n : G) (P : G → H → Prop) :
    {z : G×G // z.1*z.2=n ∧ P z.1 (f z.2)} ≃ {x : G // P x ((f x)⁻¹*f n)} where
  toFun z := ⟨z.val.1,by simpa only [←z.property.1,map_mul,inv_mul_cancel_left] using z.property.2⟩
  invFun x := ⟨(x.val,x.val⁻¹*n),by simp [x.property]⟩
  left_inv z := by
    obtain ⟨⟨x,y⟩,eq,_⟩ := z
    apply Subtype.ext; change (x,x⁻¹*n)=(x,y); simp [←eq]
  right_inv _ := rfl

/-- Exact histogram identity on complete residue boxes: even allowing an
arbitrary predicate of all of p and just the reduced q, two refinements of
the same low product have identical counts. This covers the centered low
carry, which depends only on the two signed residues modulo D. -/
theorem histogram {G H : Type*} [Group G] [Group H] (f : G →* H) {a b : G} (same : f a=f b)
    (P : G → H → Prop) :
    Nat.card {z : G×G // z.1*z.2=a ∧ P z.1 (f z.2)} =
    Nat.card {z : G×G // z.1*z.2=b ∧ P z.1 (f z.2)} := by
  rw [Nat.card_congr (productFiber f a P),Nat.card_congr (productFiber f b P),same]

/-- In particular take all odd residues modulo the full low word Q and
reduce the second factor modulo a smaller power D dividing Q. -/
theorem word_histogram {D Q : ℕ} (dvd : D∣Q) (a b : (ZMod Q)ˣ)
    (same : ZMod.castHom dvd (ZMod D) (a:ZMod Q)=ZMod.castHom dvd (ZMod D) (b:ZMod Q))
    (P : (ZMod Q)ˣ → (ZMod D)ˣ → Prop) :
    let f := Units.map (ZMod.castHom dvd (ZMod D)).toMonoidHom
    Nat.card {z : (ZMod Q)ˣ×(ZMod Q)ˣ // z.1*z.2=a ∧ P z.1 (f z.2)} =
    Nat.card {z : (ZMod Q)ˣ×(ZMod Q)ˣ // z.1*z.2=b ∧ P z.1 (f z.2)} :=
  histogram _ (Units.ext same) P

/-- Distinct equal-width prime pairs with the same bottom five bits but
opposite decisions on whether the centered low carry vanishes at radix 16. -/
theorem different_carries :
    (41*59:ℕ)%32=(47*61:ℕ)%32 ∧ PredictedTraceCarries.lowCarry 41 59 16 3 4=2 ∧
    PredictedTraceCarries.lowCarry 47 61 16 3 4=0 ∧
    Nat.Prime 41 ∧ Nat.Prime 47 ∧ Nat.Prime 59 ∧ Nat.Prime 61 := by decide +kernel

end PrimeFactors.LowBitsCarryMenu
