import PrimeFactors.WeightedPartnerIntervals

/-! Trim weighted tests only when every allocation of the multiplier contradicts
the public smaller-factor bounds. A failed ordinary prefix tightens its upper
endpoint using its last already-computed discriminant root. -/
namespace PrimeFactors.EndpointPrunedWeights

open MarginalTraceWidth InteriorBatchPopulation

/-- Endpoint tests use only integer products and comparisons. The interval
may contain smaller primes from any compatible allocation A*B=k. -/
def possible (n k s l u : ℕ) : Prop :=
  l≤u ∧ ∃ A B : ℕ, A*B=k ∧ s.gcd 24=(A+B*(n%24)).gcd 24 ∧
    (B*n≤A*l^2 → A*l^2+B*n≤s*l) ∧
    (A*u^2≤B*n → A*u^2+B*n≤s*u) ∧
    (s*l≤A*l^2+B*n ∨ s*u≤A*u^2+B*n)

/-- On the feasible factor interval the maximum of Ap+BN/p occurs at an
endpoint. If the minimum occurs at an endpoint it gives a lower bound there. -/
theorem endpoints {p q A B l u : ℕ} (lp : 0<l) (lp' : l≤p) (pu : p≤u) :
    (B*(p*q)≤A*l^2 → A*l^2+B*(p*q)≤(A*p+B*q)*l) ∧
    (A*u^2≤B*(p*q) → A*u^2+B*(p*q)≤(A*p+B*q)*u) ∧
    ((A*p+B*q)*l≤A*l^2+B*(p*q) ∨ (A*p+B*q)*u≤A*u^2+B*(p*q)) := by
  let L : ℤ := l
  let P : ℤ := p
  let U : ℤ := u
  let a : ℤ := A
  let v : ℤ := B*q
  have lo : L≤P := by dsimp [L,P]; exact_mod_cast lp'
  have hi : P≤U := by dsimp [P,U]; exact_mod_cast pu
  have lpos : 0<L := by dsimp [L]; exact_mod_cast lp
  have upos : 0<U := lpos.trans_le (lo.trans hi)
  have nonneg : 0≤v := by dsimp [v]; positivity
  have posA : 0≤a := by dsimp [a]; positivity
  have left (cut : v≤a*L) : a*L^2+v*P≤(a*P+v)*L := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr cut)]
  have right (cut : a*U≤v) : a*U^2+v*P≤(a*P+v)*U := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr cut)]
  have left' (cut : a*L≤v) : (a*P+v)*L≤a*L^2+v*P := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr cut)]
  have right' (cut : v≤a*U) : (a*P+v)*U≤a*U^2+v*P := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr cut)]
  have rearr : B*(p*q)=(B*q)*p := by ring
  rw [rearr]
  constructor
  · intro bound
    have hb : v*P≤a*L^2 := by dsimp [v,P,a,L]; exact_mod_cast bound
    have cut : v≤a*L := (mul_le_mul_iff_of_pos_right lpos).mp (by
      nlinarith only [mul_le_mul_of_nonneg_left lo nonneg,hb])
    have rc := left cut
    dsimp [L,P,U,a,v] at rc
    exact_mod_cast rc
  constructor
  · intro bound
    have hb : a*U^2≤v*P := by dsimp [v,P,a,U]; exact_mod_cast bound
    have cut : a*U≤v := (mul_le_mul_iff_of_pos_right upos).mp (by
      nlinarith only [mul_le_mul_of_nonneg_left hi nonneg,hb])
    have rc := right cut
    dsimp [L,P,U,a,v] at rc
    exact_mod_cast rc
  · by_cases cut : a*L≤v
    · left
      have rc := left' cut
      dsimp [L,P,U,a,v] at rc
      exact_mod_cast rc
    · right
      have rc := right' ((le_of_not_ge cut).trans (mul_le_mul_of_nonneg_left (lo.trans hi) posA))
      dsimp [L,P,U,a,v] at rc
      exact_mod_cast rc

/-- A proper square may have an unintended allocation. Every such allocation
passes the endpoint and remainder necessary conditions. -/
theorem retain {p q k s l u : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (unit : p.Coprime 6) (lp : 0<l) (pl : l≤p) (pu : p≤u)
    (hit : properSquare (p*q) k s) : possible (p*q) k s l u := by
  let d := (s^2-4*k*(p*q)).sqrt
  obtain ⟨sq,lo,hi⟩ := hit
  have roots := OffsetSquareSplit.root_identities (k:=1) (N:=k*(p*q)) (d:=d) (S:=s)
    (by simpa only [d,one_pow,mul_one,mul_assoc] using sq)
  dsimp only at roots
  obtain ⟨A,B,weights,tr⟩ := ShiftedEndpointPopulation.allocation pp qp ne
    (by simpa using roots.2 : (s+d)/2*((s-d)/2)=k*(p*q)) lo hi
  have trace := tr.symm.trans roots.1
  rw [←trace]
  exact ⟨pl.trans pu,B,A,by simpa only [Nat.mul_comm A B] using weights.symm,
    sum_allowed B A unit,endpoints lp pl pu⟩

/-- A failed ordinary prefix leaves the true sum at least its last tested label. -/
theorem missed_sum {p q H : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (unit : p.Coprime 6) :
    let f := ceilSqrt (4*(p*q))
    let r := (p*q)%24
    let label := fun i => f+offset r (f%24) 1 1 i
    (∀ i<H+1, ¬properSquare (p*q) 1 (label i)) → label H≤p+q := by
  intro f r label miss
  by_contra! bad
  have lo : f≤p+q := ceilSqrt_le_iff.mpr (by zify; nlinarith only [sq_nonneg ((p:ℤ)-q)])
  have pass : (p+q).gcd 24=(1+1*r).gcd 24 := by simpa only [one_mul] using sum_allowed 1 1 unit
  obtain ⟨i,ih,eq⟩ := (admitted_iff (a:=1) (b:=1) lo pass).mp bad
  have all := WeightedPartnerIntervals.split_iff_allocations (a:=1) (b:=1) (H:=H+1) pp qp ne (by simp)
  dsimp only at all
  simp only [Nat.mul_one,Nat.one_mul] at all
  obtain ⟨j,small,hit⟩ := all.mpr ⟨1,1,by decide,i,by omega,by simpa only [Nat.one_mul] using eq⟩
  exact miss j small hit

/-- The discriminant root from the final ordinary square test supplies a
smaller-factor upper bound without another square root. -/
theorem after_miss {p q s : ℕ} (order : p≤q) (large : 4*(p*q)≤s^2) (before : s≤p+q) :
    p≤(s-(s^2-4*(p*q)).sqrt)/2 := by
  have pu : 2*p≤s := by
    apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
    nlinarith only [large,Nat.mul_le_mul_left p order]
  have sub := Nat.sub_add_cancel large
  let d := (s^2-4*(p*q)).sqrt
  have dx : d^2≤s^2-4*(p*q) := Nat.sqrt_le' _
  have dcap : d≤s-2*p := by
    apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
    zify at sub dx before ⊢
    rw [Nat.cast_sub pu,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith only [dx,sub,mul_le_mul_of_nonneg_left before (show 0≤(p:ℤ) by positivity)]
  change p≤(s-d)/2
  omega

/-- Keep every surviving historical label and replace each rejected label
by one new ordinary trace from the same already-started arm. -/
noncomputable def reassign (n l u : ℕ) (old : List (ℕ×ℕ)) (ordinary : ℕ → ℕ) : List (ℕ×ℕ) := by
  classical
  let kept := old.filter (fun z => decide (possible n z.1 z.2 l u))
  exact kept ++ (List.range (old.length-kept.length)).map (fun i => (1,ordinary i))

theorem budget (n l u : ℕ) (old : List (ℕ×ℕ)) (ordinary : ℕ → ℕ) :
    (reassign n l u old ordinary).length=old.length := by
  classical
  unfold reassign
  simp only [List.length_append,List.length_map,List.length_range]
  exact Nat.add_sub_of_le (List.length_filter_le _ _)

/-- Direct preservation of every previously successful weighted label, including
incidental multiplier allocations. The replacement rule may use any ordinary
continuation labels. -/
theorem success_inclusion {p q l u : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (unit : p.Coprime 6) (lp : 0<l) (pl : l≤p) (pu : p≤u)
    (old : List (ℕ×ℕ)) (ordinary : ℕ → ℕ) :
    ∀ z∈old, properSquare (p*q) z.1 z.2 →
      z∈reassign (p*q) l u old ordinary := by
  classical
  intro z inz hit
  apply List.mem_append_left
  exact List.mem_filter.mpr ⟨inz,decide_eq_true (retain pp qp ne unit lp pl pu hit)⟩

/-- Public equal-width lower endpoint and the public starting-ceiling upper
bound on the smaller prime. -/
theorem bit_width {p q B : ℕ} (pp : 0<p) (order : p≤q) (B0 : 2≤B)
    (low : B/2≤p) (high : q<B) :
    max (B/2) (((p*q-1)/(B-1))+1) ≤ p ∧ p ≤ (p*q).sqrt := by
  have qp : 0<q := pp.trans_le order
  have nq := Nat.mul_pos pp qp
  have bound := Nat.mul_le_mul_left p (show q≤B-1 by omega)
  have h : (p*q-1)/(B-1)<p := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  exact ⟨max_le low (by omega),Nat.le_sqrt.mpr (Nat.mul_le_mul_left p order)⟩

/-- Product-only specialization after the 16 ordinary tests have missed. -/
theorem after_sixteen {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (pq : p<q)
    (unit : p.Coprime 6) (B0 : 2≤B) (lo : B/2≤p) (hi : q<B)
    (old : List (ℕ×ℕ)) (ordinary : ℕ → ℕ) :
    let n := p*q
    let f := ceilSqrt (4*n)
    let label := fun i => f+offset (n%24) (f%24) 1 1 i
    let s := label 15
    let l := max (B/2) ((n-1)/(B-1)+1)
    let u := min n.sqrt ((s-(s^2-4*n).sqrt)/2)
    (∀ i<16, ¬properSquare n 1 (label i)) →
      ∀ z∈old, properSquare n z.1 z.2 → z∈reassign n l u old ordinary := by
  intro n f label s l u miss
  have low := bit_width pp.pos pq.le B0 lo hi
  have pos : 0<l := lt_of_lt_of_le (Nat.zero_lt_succ ((n-1)/(B-1))) (le_max_right _ _)
  have st : f≤s := Nat.le_add_right _ _
  have above := ceilSqrt_le_iff.mp st
  have no := missed_sum (H:=15) pp qp pq.ne unit miss
  have upper : p≤u := le_min low.2 (after_miss pq.le above no)
  exact success_inclusion pp qp pq.ne unit pos low.1 upper old ordinary

/-- Adjacent squares certify an entire negative prefix using supplied integer
roots, avoiding fresh root computations inside a generated Lean receipt. -/
theorem bracket_miss {n k t d : ℕ} (lo : d^2<t^2-4*k*n) (hi : t^2-4*k*n<(d+1)^2) :
    ¬properSquare n k t := by
  rintro ⟨sq,_,_⟩
  let r := (t^2-4*k*n).sqrt
  change t^2=4*k*n+r^2 at sq
  have e : t^2-4*k*n=r^2 := by omega
  by_cases h : r≤d
  · have := Nat.pow_le_pow_left h 2
    omega
  · have := Nat.pow_le_pow_left (show d+1≤r by omega) 2
    omega

end PrimeFactors.EndpointPrunedWeights
