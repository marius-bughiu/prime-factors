import PrimeFactors.WeightedCollision
import PrimeFactors.TraceFoldedRight
import PrimeFactors.RectangularFullWidth
import PrimeFactors.RectangularRowCost

/-! Swapping the two weights gives complementary collisions at the two
prime factors. Centering the exponent then makes a full-modulus trace
key whose right side depends only on the difference of the weights. -/
namespace PrimeFactors.WeightedGlobalTrace

open TraceFoldedRight

/-- N=2h+1. Only the weight sum c and proposed weighted sum s enter here. -/
def left {G : Type*} [CommGroup G] (u : G) (h c s : ℕ) := u^s / u^((h+1)*c)

/-- The other lookup key is shared by all pairs with the same difference. -/
def right {G : Type*} [CommGroup G] (u : G) (h d : ℕ) := u^(h*d)

private theorem at_first {p : ℕ} (hp : p.Prime) (q a d h : ℕ) (odd : p*q=2*h+1)
    (v : (ZMod p)ˣ) :
    left v h (a+(a+d)) (a*p+(a+d)*q)=right v h d := by
  dsimp [left,right]
  have center : a+(a+d)*(p*q)=h*d+(h+1)*(a+(a+d)) := by rw [odd]; ring
  rw [weighted_power_at_prime hp,center,pow_add,mul_div_cancel_right]

private theorem at_second {q : ℕ} (hq : q.Prime) (p a d h : ℕ) (odd : p*q=2*h+1)
    (v : (ZMod q)ˣ) :
    left v h (a+(a+d)) (a*p+(a+d)*q)*right v h d=1 := by
  have eq := weighted_power_at_prime hq p (a+d) a v
  rw [Nat.mul_comm q p,add_comm ((a+d)*q)] at eq
  dsimp [left,right]
  rw [div_mul_eq_mul_div,div_eq_one,eq,←pow_add,odd]
  congr 1
  ring

private theorem map_trace {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Rˣ) : f (trace 1 x)=trace 1 (Units.map f x) := by
  simp [trace]

private theorem map_left {G G' : Type*} [CommGroup G] [CommGroup G'] (f : G →* G')
    (u : G) (h c s : ℕ) : f (left u h c s)=left (f u) h c s := by simp [left]

private theorem map_right {G G' : Type*} [CommGroup G] [CommGroup G'] (f : G →* G')
    (u : G) (h d : ℕ) : f (right u h d)=right (f u) h d := by simp [right]

/-- Exact equality in Z/(pq), using opposite orientations at p and q. The
inputs to either key are computed from the public modulus and indices. -/
theorem global {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (cop : p.Coprime q)
    (odd : Odd (p*q)) (u : (ZMod (p*q))ˣ) (a d : ℕ) :
    trace 1 (left u ((p*q)/2) (a+(a+d)) (a*p+(a+d)*q)) =
      trace 1 (right u ((p*q)/2) d) := by
  let h := (p*q)/2
  have hn : p*q=2*h+1 := by have := Nat.odd_iff.mp odd; dsimp [h]; omega
  let e := ZMod.chineseRemainder cop
  let fp := (RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom
  let fq := (RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom
  apply e.injective
  apply Prod.ext
  · change fp (trace 1 _)=fp (trace 1 _)
    rw [map_trace,map_trace,map_left,map_right]
    rw [at_first hp q a d h hn]
  · change fq (trace 1 _)=fq (trace 1 _)
    rw [map_trace,map_trace,map_left,map_right]
    exact same_key (at_second hq p a d h hn _)

/-- Every equal key is a scalar or reciprocal match, or the ordinary
difference exposes a proper divisor. -/
theorem classify {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) (c s d : ℕ)
    (hit : trace 1 (left u (N/2) c s)=trace 1 (right u (N/2) d)) :
    let X := left u (N/2) c s
    let Y := right u (N/2) d
    X=Y ∨ X*Y=1 ∨ (1<((X:ZMod N)-(Y:ZMod N)).val.gcd N ∧ ((X:ZMod N)-(Y:ZMod N)).val.gcd N<N) :=
  TraceFoldedRight.classify _ _ _ hit

/-- If the weighted trace lies in a thin square window, its raw left-key
indices determine the weight difference as an ordinary integer. -/
theorem difference_sq {N a b s W : ℕ} (np : 0<N) (order : a≤b)
    (lo : 4*a*b*N≤s^2) (hi : s^2≤4*a*b*N+W^2) (thin : W^2<N) :
    (a+b)^2-s^2/N=(b-a)^2 := by
  have quotient : s^2/N=4*a*b := by
    apply le_antisymm
    · have := (Nat.div_lt_iff_lt_mul np).mpr (show s^2<(4*a*b+1)*N by nlinarith only [hi,thin])
      omega
    · exact (Nat.le_div_iff_mul_le np).mpr lo
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le order
  rw [quotient,Nat.add_sub_cancel_left]
  apply Nat.sub_eq_of_eq_add
  ring

/-- Deduplicating the unexponentiated left-key indices cannot merge distinct
sorted weight assignments in these windows. Hash coincidences after reducing
modulo N are a separate matter. -/
theorem unique_weights {N a b a' b' s W : ℕ} (np : 0<N)
    (o : a≤b) (o' : a'≤b') (sum : a+b=a'+b')
    (l : 4*a*b*N≤s^2) (u : s^2≤4*a*b*N+W^2)
    (l' : 4*a'*b'*N≤s^2) (u' : s^2≤4*a'*b'*N+W^2) (thin : W^2<N) :
    a=a' ∧ b=b' := by
  have x := difference_sq np o l u thin
  have y := difference_sq np o' l' u' thin
  have sq : (b-a)^2=(b'-a')^2 := by rw [←x,←y,sum]
  have eq := (Nat.pow_left_inj (by decide : 2≠0)).mp sq
  omega


/-- While the proposed traces each fit in one band, equal signed left
exponents force equal indices even before reduction modulo the base order.
The cross-added equality avoids subtraction of naturals. -/
theorem exponent_indices {M c c' s s' : ℕ} (small : s<M) (small' : s'<M)
    (eq : M*c+s'=M*c'+s) : c=c' ∧ s=s' := by
  have h := congrArg (fun z => z%M) eq
  simp only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt small'] at h
  subst s'
  exact ⟨Nat.eq_of_mul_eq_mul_left (by omega : 0<M) (Nat.add_right_cancel eq),rfl⟩

private theorem projection_square {R F : Type*} [CommRing R] [Field F] (f : R →+* F)
    (Y : Rˣ) (clear : IsUnit ((Y:R)^2-1)) : (Units.map f.toMonoidHom Y)^2≠1 := by
  intro eq
  have nonzero := clear.map f
  have sq := congrArg (fun z : Fˣ => (z:F)) eq
  change ((f (Y:R))^2:F) = 1 at sq
  rw [map_sub,map_pow,map_one,sq,sub_self] at nonzero
  exact not_isUnit_zero nonzero

/-- One public precheck per right entry excludes both trivial orientations.
For such an entry a genuine trace gives a proper gcd, including at composite
modulus without any assumption on the global order of the base. -/
theorem proper {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (cop : p.Coprime q)
    (odd : Odd (p*q)) (u : (ZMod (p*q))ˣ) (a d : ℕ)
    (clear : IsUnit (((right u ((p*q)/2) d : (ZMod (p*q))ˣ) : ZMod (p*q))^2-1)) :
    let X := left u ((p*q)/2) (a+(a+d)) (a*p+(a+d)*q)
    let Y := right u ((p*q)/2) d
    let f := ((X:ZMod (p*q))-(Y:ZMod (p*q))).val.gcd (p*q)
    1<f ∧ f<p*q := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  let fp := ZMod.castHom (dvd_mul_right p q) (ZMod p)
  let fq := ZMod.castHom (dvd_mul_left q p) (ZMod q)
  let h := (p*q)/2
  have hn : p*q=2*h+1 := by have := Nat.odd_iff.mp odd; dsimp [h]; omega
  have hit := global hp hq cop odd u a d
  rcases classify u _ _ d hit with eq|mate|factor
  · have oriented := congrArg (Units.map fq.toMonoidHom) eq
    rw [map_left,map_right] at oriented
    have other := at_second hq p a d h hn (Units.map fq.toMonoidHom u)
    have gap := projection_square fq _ clear
    rw [map_right] at gap
    rw [oriented] at other
    exact False.elim (gap (by simpa only [pow_two] using other))
  · have oriented := congrArg (Units.map fp.toMonoidHom) mate
    rw [map_mul,map_left,map_right,map_one] at oriented
    have first := at_first hp q a d h hn (Units.map fp.toMonoidHom u)
    have gap := projection_square fp _ clear
    rw [map_right] at gap
    rw [first] at oriented
    exact False.elim (gap (by simpa only [pow_two] using oriented))
  · exact factor

/-- On a primitive rectangular representation the public coordinate supplies
the weighted sum, 2y for odd weights and y for opposite-parity weights. -/
theorem located {p q t a d x y : ℕ} (hp : p.Prime) (hq : q.Prime) (cop : p.Coprime q)
    (odd : Odd (p*q)) (u : (ZMod (p*q))ˣ) (xy : x≤y) (tp : 0<t)
    (loc : MixedUnityCofactors.Located t p q a (a+d) x y) :
    trace 1 (left u ((p*q)/2) (a+(a+d)) (2*y/t))=trace 1 (right u ((p*q)/2) d) := by
  have sum : t*(a*p+(a+d)*q)=2*y := by
    rw [Nat.mul_add,Nat.mul_comm a p,Nat.mul_comm (a+d) q]
    rcases loc with ⟨l,r⟩|⟨l,r⟩ <;> rw [l,r] <;> omega
  rw [←sum,Nat.mul_div_cancel_left _ tp]
  exact global hp hq cop odd u a d

/-- Conditional-size of the shared right table, using only the public ratio
and the multiplier cutoff. Every eligible weight pair falls into it. -/
theorem gap_bound {a b R e K : ℕ} (rp : 0<R) (ord : a≤b)
    (ratio : R*b≤(R+e)*a) (cap : a*b≤K) : b-a≤e*K.sqrt/R := by
  have al : a≤K.sqrt := Nat.le_sqrt.mpr ((Nat.mul_le_mul_left a ord).trans cap)
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ord
  rw [Nat.add_sub_cancel_left]
  apply (Nat.le_div_iff_mul_le rp).mpr
  exact (show d*R≤e*a by nlinarith only [ratio]).trans (Nat.mul_le_mul_left e al)

/-- The positive rectangular chart with odd weights supplies the common
thin-window hypotheses for the proposed weighted sum 2y. -/
theorem odd_band {N a b B H y : ℕ}
    (pos : y∈RectangularRowCost.positions true N 1 B H (a*b)) :
    4*a*b*N≤(2*y)^2 ∧ (2*y)^2≤4*a*b*N+(2*H)^2 := by
  have ⟨lo,hi⟩ := (Finset.mem_filter.mp pos).2
  simp only [Bool.true_eq,if_true,one_mul] at lo hi
  constructor <;> nlinarith only [lo,hi]

/-- With opposite-parity weights the multiplier is 4ab and the proposed
weighted sum is the raw chart coordinate y. -/
theorem even_band {N a b B H y : ℕ}
    (pos : y∈RectangularRowCost.positions true N 1 B H (4*a*b)) :
    4*a*b*N≤y^2 ∧ y^2≤4*a*b*N+H^2 := by
  simpa only [Bool.true_eq,if_true,one_mul] using (Finset.mem_filter.mp pos).2

/-- The standard full-width rectangular bound fits the thin-window lemma
on both parities, even after doubling the odd chart coordinate. -/
theorem full_width_thin {N : ℕ} (lo : 2^2047≤N) (hi : N<2^2048) :
    (2*RectangularFullWidth.H N)^2<N := by
  obtain ⟨_,_,_,_,bound,_,_⟩ := RectangularFullWidth.dimensions lo hi
  have small := Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 bound.le) 2
  exact small.trans_lt ((by decide +kernel : (2*2^683:ℕ)^2<2^2047).trans_le lo)

/-- The full-width coordinate cap puts both parity charts inside one
exponent band, so the preceding injectivity result applies to all rows. -/
theorem full_width_band {N : ℕ} (lo : 2^2047≤N) (hi : N<2^2048) :
    2*RectangularFullWidth.B N < N/2+1 := by
  obtain ⟨_,_,_,bound,_,_,_⟩ := RectangularFullWidth.dimensions lo hi
  have cmp : 4*RectangularFullWidth.B N≤N :=
    (Nat.mul_le_mul_left 4 bound).trans ((by decide +kernel : 4*2^1366≤2^2047).trans lo)
  omega

private def bitPower {G : Type*} [Monoid G] (a : G) : ℕ → ℕ → G
  | 0, _ => 1
  | j+1, n =>
    let v := bitPower a j (n/2)
    if n%2=0 then v*v else v*v*a

private theorem bitPower_eq {G : Type*} [Monoid G] (a : G) (j n : ℕ) (small : n<2^j) :
    a^n=bitPower a j n := by
  induction j generalizing n with
  | zero =>
    have : n=0 := by simpa using small
    simp [this,bitPower]
  | succ j ih =>
    rw [pow_succ] at small
    have prev := ih (n/2) (by omega)
    rw [bitPower,←prev]
    split
    · exact (congrArg (fun z => a^z) (show n=n/2+n/2 by omega)).trans (pow_add ..)
    · have hh : a^(n/2+n/2+1)=a^(n/2)*a^(n/2)*a := by rw [pow_succ,pow_add]
      exact (congrArg (fun z => a^z) (show n=n/2+n/2+1 by omega)).trans hh

private def two : (ZMod 154421)ˣ := ⟨2,77211,by decide,by decide⟩

/-- A product-only key hit at public weights (3,5) and candidate 3044. -/
theorem example_18_bit :
    let X := left two (154421/2) 8 3044
    let Y := right two (154421/2) 2
    (X:ZMod 154421)=124284 ∧ (Y:ZMod 154421)=103158 ∧
      trace 1 X=124904 ∧ trace 1 Y=124904 ∧
      ((X:ZMod 154421)-(Y:ZMod 154421)).val.gcd 154421=503 ∧
      154421=503*307 ∧ Nat.Prime 503 ∧ Nat.Prime 307 := by
  let ux : (ZMod 154421)ˣ := ⟨124284,620,by decide,by decide⟩
  let uy : (ZMod 154421)ˣ := ⟨103158,21746,by decide,by decide⟩
  have hx : left two (154421/2) 8 3044=ux := by
    change two^3044/two^617688=ux
    rw [bitPower_eq two 20 3044 (by decide),bitPower_eq two 20 617688 (by decide)]
    exact Units.ext (by decide +kernel)
  have hy : right two (154421/2) 2=uy := by
    change two^154420=uy
    rw [bitPower_eq two 20 154420 (by decide)]
    exact Units.ext (by decide +kernel)
  dsimp only
  rw [hx,hy]
  decide +kernel

end PrimeFactors.WeightedGlobalTrace
