import PrimeFactors.TraceDirection
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.Int.Sqrt

namespace PrimeFactors.GaussianTraceRecovery

/-- The squared length of the primitive direction of two supplied integer readings. -/
def direction (s v : ℤ) : ℕ :=
  (s.natAbs / s.gcd v)^2 + (v.natAbs / s.gcd v)^2

/-- Any nonzero signed common scale is immaterial. -/
theorem direction_scaled {h u v : ℤ} (hn : h≠0) (prim : IsCoprime u v) :
    direction (h*u) (h*v) = u.natAbs^2+v.natAbs^2 := by
  have cop : u.natAbs.gcd v.natAbs = 1 := Int.isCoprime_iff_gcd_eq_one.mp prim
  have pos : 0<h.natAbs := Int.natAbs_pos.mpr hn
  simp only [direction, Int.gcd, Int.natAbs_mul, Nat.gcd_mul_left, cop, mul_one]
  simp [Nat.mul_div_cancel_left _ pos]

private theorem norm_nat {u v : ℤ} {p : ℕ} (norm : u^2+v^2=p) :
    u.natAbs^2+v.natAbs^2=p := by
  exact_mod_cast (show ((u.natAbs : ℤ)^2+(v.natAbs : ℤ)^2)=(p : ℤ) by
    simpa [Int.natCast_natAbs, sq_abs] using norm)

/-- From two complete quartic readings, dividing by their gcd before taking
the norm gives the selected prime. The decoder itself receives only the readings. -/
theorem prime_from_readings (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (pc : p%4=1) (qc : q%4=1) (d : ℤ)
    (left : quadraticChar (ZMod p) (d : ZMod p) = -1)
    (right : quadraticChar (ZMod q) (d : ZMod q) = 1) :
    direction (QuarticTrace.complete (p*q) 1) (QuarticTrace.complete (p*q) d) = p := by
  obtain ⟨h,u,v,ho,_,prim,norm,h1,hd⟩ := TraceDirection.direction_of_traces p q cop pc qc d left right
  obtain ⟨k,hk⟩ := ho
  have hn : h≠0 := by omega
  rw [h1,hd,direction_scaled (mul_ne_zero (by decide : (4:ℤ)≠0) hn) prim]
  exact norm_nat norm

/-- A Jacobi-negative selector can be checked without either prime. -/
theorem prime_from_jacobi (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (pc : p%4=1) (qc : q%4=1) (d : ℤ)
    (selector : jacobiSym d (p*q) = -1) :
    let out := direction (QuarticTrace.complete (p*q) 1) (QuarticTrace.complete (p*q) d)
    out=p ∨ out=q := by
  rw [jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero,
    ←jacobiSym.legendreSym.to_jacobiSym p, ←jacobiSym.legendreSym.to_jacobiSym q] at selector
  change quadraticChar (ZMod p) (d : ZMod p) * quadraticChar (ZMod q) (d : ZMod q) = -1 at selector
  have nz : (d : ZMod p)≠0 := by intro h; simp [h] at selector
  rcases quadraticChar_dichotomy nz with good | bad
  · right
    have qn : quadraticChar (ZMod q) (d : ZMod q) = -1 := by simpa [good] using selector
    letI : NeZero (q*p) := ⟨mul_ne_zero hq.out.ne_zero hp.out.ne_zero⟩
    simpa only [Nat.mul_comm q p] using prime_from_readings q p cop.symm qc pc d qn good
  · left
    have qp : quadraticChar (ZMod q) (d : ZMod q) = 1 := by rw [bad,neg_one_mul] at selector; omega
    exact prime_from_readings p q cop pc qc d bad qp

/-- Two candidate primitive norms for an oriented representation (x,y), input n
and a single supplied trace t. Spurious norms can be discarded by division of n. -/
noncomputable def fromOrientation (n : ℕ) (t x y : ℤ) : Finset ℕ :=
  let s := t/2
  let w := Int.sqrt ((n:ℤ)-(s-x)^2)
  {direction s (y+w), direction s (y-w)}

/-- The two real coordinates of the Gaussian products have sum t/2. The other
imaginary coordinate is obtained by one ordinary integer square root, up to sign. -/
theorem reflected_square {a b c d : ℤ} {n : ℕ}
    (norm : (n : ℤ)=(a^2+b^2)*(c^2+d^2)) :
    (n : ℤ) - (2*a*c-(a*c-b*d))^2 = (a*d-b*c)^2 := by rw [norm]; ring

/-- For an oriented Gaussian product, both primes are in the two-entry output.
The local coordinates, their primitivity and the factorization occur only in
the correctness hypotheses. The actual calculation uses n,t,x,y. -/
theorem from_product {a b c d : ℤ} {p q : ℕ} (an : a≠0) (cn : c≠0)
    (prim : IsCoprime a b) (prim' : IsCoprime c d)
    (pn : a^2+b^2=p) (qn : c^2+d^2=q) :
    let out := fromOrientation (p*q) (4*a*c) (a*c-b*d) (a*d+b*c)
    p∈out ∧ q∈out := by
  have nr : ((p*q : ℕ):ℤ)=(a^2+b^2)*(c^2+d^2) := by push_cast; rw [pn,qn]
  have s : 4*a*c/2=2*a*c := by rw [show 4*a*c=2*(2*a*c) by ring]; omega
  have square := reflected_square (a:=a) (b:=b) (c:=c) (d:=d) nr
  have pval : direction (2*a*c) (2*b*c) = p := by
    rw [show 2*a*c=(2*c)*a by ring,show 2*b*c=(2*c)*b by ring,
      direction_scaled (mul_ne_zero (by decide) cn) prim,norm_nat pn]
  have qval : direction (2*a*c) (2*a*d) = q := by
    rw [show 2*a*c=(2*a)*c by ring,show 2*a*d=(2*a)*d by ring,
      direction_scaled (mul_ne_zero (by decide) an) prim',norm_nat qn]
  dsimp only [fromOrientation]
  rw [s,square, sq (a*d-b*c),Int.sqrt_eq,Int.natCast_natAbs]
  rcases le_total (b*c) (a*d) with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h),
      show a*d+b*c+(a*d-b*c)=2*a*d by ring, show a*d+b*c-(a*d-b*c)=2*b*c by ring,pval,qval]
    simp
  · rw [abs_of_nonpos (sub_nonpos.mpr h),
      show a*d+b*c+ -(a*d-b*c)=2*b*c by ring, show a*d+b*c- -(a*d-b*c)=2*a*d by ring,pval,qval]
    simp

/-- For a known trace magnitude and an index j, try the possible real coordinate
|t|/4 − 4j. A genuine index supplies the imaginary coordinate by an integer
square root. Final answers from unsuccessful guesses require a divisibility check. -/
noncomputable def traceProbe (n t j : ℕ) : Finset ℕ :=
  let x := (t/4 : ℕ) - (4*j : ℤ)
  fromOrientation n t x (Int.sqrt ((n:ℤ)-x^2))

/-- A prime norm forces primitive coordinates. -/
private theorem coprime_norm {a b p : ℕ} (prime : p.Prime) (nr : a^2+b^2=p) :
    IsCoprime (a:ℤ) (b:ℤ) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  change a.gcd b=1
  have h : (a.gcd b)^2 ∣ p := by
    rw [←nr]
    exact dvd_add (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left a b) 2)
      (pow_dvd_pow_of_dvd (Nat.gcd_dvd_right a b) 2)
  have gdiv : a.gcd b ∣ p := (dvd_pow_self _ (by decide : 2≠0)).trans h
  rcases prime.eq_one_or_self_of_dvd _ gdiv with one | all
  · exact one
  · rw [all] at h
    have low := Nat.le_of_dvd prime.pos h
    nlinarith [prime.two_le]

/-- Given only the true trace magnitude t, a generic search needs at most
(⌊√n⌋−t/4)/4 positive indices. This can be useful when t is close to 4√n.
Here nonnegative coordinates suffice because only the magnitude of t is used. -/
theorem trace_only_window {p q a b c d t : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pn : a^2+b^2=p) (qn : c^2+d^2=q) (ap : 0<a) (cp : 0<c)
    (bp : 0<b) (dp : 0<d) (be : Even b) (de : Even d) (reading : t=4*a*c) :
    ∃ j, 0<j ∧ j≤((p*q).sqrt - t/4)/4 ∧
      p∈traceProbe (p*q) t j ∧ q∈traceProbe (p*q) t j := by
  obtain ⟨i,hi⟩ := be
  obtain ⟨k,hk⟩ := de
  have bd : b*d = 4*(i*k) := by rw [hi,hk]; ring
  have ac : t/4=a*c := by rw [reading,show 4*a*c=4*(a*c) by ring,Nat.mul_div_cancel_left _ (by decide)]
  have bound : a*c+b*d ≤ (p*q).sqrt := by
    apply Nat.le_sqrt'.mpr
    rw [←pn,←qn]
    have id : ((a:ℤ)*c+(b:ℤ)*d)^2 + ((a:ℤ)*d-(b:ℤ)*c)^2 =
        ((a:ℤ)^2+(b:ℤ)^2)*((c:ℤ)^2+(d:ℤ)^2) := by ring
    exact_mod_cast (show ((a:ℤ)*c+(b:ℤ)*d)^2 ≤ _ from le_of_add_le_of_nonneg_left
      (le_of_eq id) (sq_nonneg _))
  have yi : Int.sqrt (((p*q:ℕ):ℤ) - ((a:ℤ)*c-(b:ℤ)*d)^2)=(a:ℤ)*d+(b:ℤ)*c := by
    have eq : ((p*q:ℕ):ℤ) - ((a:ℤ)*c-(b:ℤ)*d)^2 =
        ((a:ℤ)*d+(b:ℤ)*c)*((a:ℤ)*d+(b:ℤ)*c) := by rw [←pn,←qn]; push_cast; ring
    rw [eq,Int.sqrt_eq,Int.natAbs_of_nonneg (by positivity)]
  refine ⟨i*k, by exact Nat.mul_pos (by omega) (by omega), ?_, ?_⟩
  · rw [ac,bd] at *
    omega
  · dsimp only [traceProbe]
    rw [ac,Nat.cast_mul,show (4:ℤ)*((i*k:ℕ):ℤ)=b*d by exact_mod_cast bd.symm,yi,reading]
    push_cast
    apply from_product (by exact_mod_cast ap.ne') (by exact_mod_cast cp.ne')
      (coprime_norm pp pn) (coprime_norm qp qn) <;> exact_mod_cast ‹_›

private theorem prime_of_norm {p : ℕ} (pp : p.Prime) {A : GaussianInt} (nr : A.norm=p) :
    Prime A := by
  have price : A.norm.natAbs = p := by simp [nr]
  apply Irreducible.prime
  refine ⟨fun unit => pp.ne_one (price.symm.trans (Zsqrtd.norm_eq_one_iff.mpr unit)),?_⟩
  intro v w factor
  have eq : p = v.norm.natAbs * w.norm.natAbs := by
    rw [←price, factor, Zsqrtd.norm_mul,Int.natAbs_mul]
  rcases (Nat.prime_iff.mp pp).irreducible.isUnit_or_isUnit eq with a | b
  · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp (Nat.isUnit_iff.mp a))
  · exact Or.inr (Zsqrtd.norm_eq_one_iff.mp (Nat.isUnit_iff.mp b))

private noncomputable def conjugates (z : GaussianInt) : Finset GaussianInt := {z,star z}

private noncomputable def phases : Finset GaussianInt :=
  {⟨1,0⟩, ⟨-1,0⟩, ⟨0,1⟩, ⟨0,-1⟩}

private theorem phase_of_norm {v : GaussianInt} (h : v.norm=1) : v ∈ phases := by
  rcases v with ⟨x,y⟩
  change x*x-(-1)*y*y=1 at h
  have x2 : x^2≤1 := by nlinarith [sq_nonneg y]
  have y2 : y^2≤1 := by nlinarith [sq_nonneg x]
  have xbounds : -1≤x ∧ x≤1 := by constructor <;> nlinarith [sq_nonneg (x-1),sq_nonneg (x+1)]
  have ybounds : -1≤y ∧ y≤1 := by constructor <;> nlinarith [sq_nonneg (y-1),sq_nonneg (y+1)]
  obtain ⟨xl,xh⟩ := xbounds
  obtain ⟨yl,yh⟩ := ybounds
  interval_cases x <;> interval_cases y <;> first | decide | norm_num at h

/-- At most eight signed orientations of a single, unordered representation. -/
noncomputable def orientations (z : GaussianInt) : Finset GaussianInt :=
  (conjugates z).biUnion (fun w => phases.image (fun u => u*w))

private theorem divides_orientation {A z : GaussianInt} (prime : Prime A)
    (div : A.norm ∣ z.norm) : ∃ w∈conjugates z, A∣w := by
  obtain ⟨k,hk⟩ := div
  have divides : A ∣ z*star z := by
    rw [←Zsqrtd.norm_eq_mul_conj,hk,Int.cast_mul,Zsqrtd.norm_eq_mul_conj]
    exact ⟨star A*k, by ring⟩
  rcases prime.dvd_mul.mp divides with h | h
  · exact ⟨z,by simp [conjugates],h⟩
  · exact ⟨star z,by simp [conjugates],h⟩

/-- Any integral representation of pq is, after one of eight signed orientations,
the product of a prescribed norm-p Gaussian integer and one of the two orientations
of a prescribed norm-q Gaussian integer. Its coordinates need not be pre-oriented. -/
theorem orient_product {p q : ℕ} (pp : p.Prime) (qp : q.Prime) {A C z : GaussianInt}
    (pn : A.norm=p) (qn : C.norm=q) (nz : z.norm=(p:ℤ)*q) :
    ∃ v∈orientations z, v=A*C ∨ v=A*star C := by
  obtain ⟨v,vm,w,vw⟩ := divides_orientation (prime_of_norm pp pn) (show A.norm∣z.norm by
    rw [pn,nz]; exact dvd_mul_right _ _)
  have vn : v.norm=(p:ℤ)*q := by
    simp only [conjugates,Finset.mem_insert,Finset.mem_singleton] at vm
    rcases vm with rfl|rfl <;> simpa only [Zsqrtd.norm_conj] using nz
  rw [vw,Zsqrtd.norm_mul,pn] at vn
  have wn : w.norm=q := mul_left_cancel₀ (Int.natCast_ne_zero.mpr pp.ne_zero) vn
  obtain ⟨w',wm,k,wk⟩ := divides_orientation (prime_of_norm qp qn) (show C.norm∣w.norm by rw [qn,wn])
  have normw : w'.norm=q := by
    simp only [conjugates,Finset.mem_insert,Finset.mem_singleton] at wm
    rcases wm with rfl|rfl <;> simpa only [Zsqrtd.norm_conj] using wn
  rw [wk,Zsqrtd.norm_mul,qn] at normw
  have kn : k.norm=1 := mul_left_cancel₀ (Int.natCast_ne_zero.mpr qp.ne_zero)
    (normw.trans (mul_one _).symm)
  have inv : k*star k=1 := by rw [←Zsqrtd.norm_eq_mul_conj,kn]; simp
  have mt (u : GaussianInt) (hu : u.norm=1) : u*v ∈ orientations z :=
    Finset.mem_biUnion.mpr ⟨v,vm,Finset.mem_image.mpr ⟨u,phase_of_norm hu,rfl⟩⟩
  simp only [conjugates,Finset.mem_insert,Finset.mem_singleton] at wm
  rcases wm with rfl | rfl
  · refine ⟨star k*v, mt _ (by simpa only [Zsqrtd.norm_conj] using kn), Or.inl ?_⟩
    rw [vw,wk]
    linear_combination A*C*inv
  · have wk' := congrArg star wk
    simp only [star_star,star_mul] at wk'
    refine ⟨k*v, mt _ kn, Or.inr ?_⟩
    rw [vw,wk']
    linear_combination A*star C*inv

/-- Four rotations and their conjugates suffice when the supplied representation
has arbitrary order/signs. Tests for proper divisibility may remove spurious norms. -/
noncomputable def fromRepresentation (n : ℕ) (t : ℤ) (z : GaussianInt) : Finset ℕ :=
  (orientations z).biUnion (fun w => fromOrientation n t w.re w.im)

/-- With a single representation of the product, the supplied trace determines
both primes up to a constant list of at most sixteen norms. No twist is required. -/
theorem from_arbitrary_rep {a b c d p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ap : 0<a) (cp : 0<c) (pn : a^2+b^2=p) (qn : c^2+d^2=q) (z : GaussianInt)
    (nz : z.norm=(p:ℤ)*q) :
    let out := fromRepresentation (p*q) (4*a*c) z
    p∈out ∧ q∈out := by
  let A : GaussianInt := ⟨a,b⟩
  let C : GaussianInt := ⟨c,d⟩
  have nn (i j : ℕ) : (⟨i,j⟩ : GaussianInt).norm=(i:ℤ)^2+(j:ℤ)^2 := by
    dsimp [Zsqrtd.norm]; ring
  obtain ⟨w,wm,forms⟩ := orient_product pp qp (A:=A) (C:=C)
    ((nn a b).trans (by exact_mod_cast pn)) ((nn c d).trans (by exact_mod_cast qn)) nz
  have as : (a:ℤ)≠0 := by exact_mod_cast ap.ne'
  have cs : (c:ℤ)≠0 := by exact_mod_cast cp.ne'
  have normp : (a:ℤ)^2+(b:ℤ)^2=p := by exact_mod_cast pn
  have normq : (c:ℤ)^2+(d:ℤ)^2=q := by exact_mod_cast qn
  have entries : p∈fromOrientation (p*q) (4*a*c) w.re w.im ∧
      q∈fromOrientation (p*q) (4*a*c) w.re w.im := by
    rcases forms with rfl | rfl
    · simpa [A,C,Zsqrtd.mul_re,Zsqrtd.mul_im,sub_eq_add_neg] using
        from_product as cs (coprime_norm pp pn) (coprime_norm qp qn) normp normq
    · simpa [A,C,Zsqrtd.mul_re,Zsqrtd.mul_im,sub_eq_add_neg] using
        from_product as cs (coprime_norm pp pn) (coprime_norm qp qn).neg_right normp
          (show (c:ℤ)^2+(-(d:ℤ))^2=q by simpa using normq)
  exact ⟨Finset.mem_biUnion.mpr ⟨w,wm,entries.1⟩,Finset.mem_biUnion.mpr ⟨w,wm,entries.2⟩⟩

private theorem not_prime_square {p : ℕ} (pp : p.Prime) (a : ℕ) : p ≠ a^2 := by
  intro eq
  have split := (Nat.prime_iff.mp pp).irreducible.isUnit_or_isUnit (by simpa only [sq] using eq)
  have one := Nat.isUnit_iff.mp (split.elim id id)
  simp [one,pp.ne_one] at eq

/-- The absolute base trace at a split prime is twice the nonzero odd
coordinate of its Gaussian representation. Its other coordinate is even. -/
private theorem local_coordinates (p : ℕ) [hp : Fact p.Prime] (pc : p%4=1) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ Even b ∧ a^2+b^2=p ∧
      (QuarticTrace.trace (1:ZMod p)).natAbs = 2*a := by
  have charp : ringChar (ZMod p)≠2 := by rw [ZMod.ringChar_zmod_n]; omega
  obtain ⟨v,vneg⟩ := quadraticChar_exists_neg_one (F:=ZMod p) charp
  have neg : quadraticChar (ZMod p) (-1)=1 := by
    apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
    exact FiniteField.isSquare_neg_one_iff.mpr (by simp [ZMod.card,pc])
  have norms := QuarticTrace.complementary_squares charp neg vneg
  rw [ZMod.card] at norms
  let x := QuarticTrace.trace (1:ZMod p)
  let y := QuarticTrace.trace v
  change x^2+y^2=4*p at norms
  have parity := QuarticTrace.base_parity p pc
  change x%4=2%4 at parity
  let k := x/4
  have xeq : x=4*k+2 := by dsimp [k]; omega
  have peq : (p:ℤ)=4*(p/4:ℕ)+1 := by exact_mod_cast (show p=4*(p/4)+1 by omega)
  have fourSq : (4:ℤ)^2∣y^2 := by
    refine ⟨(p/4:ℕ)-k*(k+1),?_⟩
    rw [xeq,peq] at norms
    nlinarith only [norms]
  have fy : 4∣y.natAbs := Nat.pow_dvd_pow_iff (by decide : 2≠0) |>.mp
    (by simpa [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr fourSq)
  obtain ⟨w,yw⟩ := fy
  let a := (2*k+1).natAbs
  have xa : x.natAbs=2*a := by rw [show x=2*(2*k+1) by omega,Int.natAbs_mul]; rfl
  have norm := norm_nat (p:=4*p) (u:=x) (v:=y) (by exact_mod_cast norms)
  rw [xa,yw] at norm
  have n : a^2+(2*w)^2=p := by nlinarith only [norm]
  have apos : 0<a := by apply Int.natAbs_pos.mpr; omega
  have bpos : 0<2*w := by
    by_contra! zero
    have z : w=0 := by omega
    exact not_prime_square hp.out a (by simpa [z] using n.symm)
  exact ⟨a,2*w,apos,bpos,⟨w,by omega⟩,n,xa⟩

/-- The supplied reading can be the single unmodified complete character sum
at the public product. This theorem charges the subsequent index search only. -/
theorem single_reading (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (pc : p%4=1) (qc : q%4=1) :
    let t := (QuarticTrace.complete (p*q) 1).natAbs
    ∃ j, 0<j ∧ j≤((p*q).sqrt-t/4)/4 ∧
      p∈traceProbe (p*q) t j ∧ q∈traceProbe (p*q) t j := by
  obtain ⟨a,b,ap,bp,be,pn,ta⟩ := local_coordinates p pc
  obtain ⟨c,d,cp,dp,de,qn,tc⟩ := local_coordinates q qc
  apply trace_only_window Fact.out Fact.out pn qn ap cp bp dp be de
  rw [QuarticTrace.complete_eq p q cop,Int.natAbs_mul]
  simp only [Int.cast_one,ta,tc]
  ring

/-- A product representation plus the base trace entails a constant-sized search
on every product of distinct split primes, in any orientation of the representation. -/
theorem single_reading_and_rep (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (pc : p%4=1) (qc : q%4=1) (z : GaussianInt)
    (nz : z.norm=(p:ℤ)*q) :
    let out := fromRepresentation (p*q) (QuarticTrace.complete (p*q) 1).natAbs z
    p∈out ∧ q∈out := by
  obtain ⟨a,b,ap,_,_,pn,ta⟩ := local_coordinates p pc
  obtain ⟨c,d,cp,_,_,qn,tc⟩ := local_coordinates q qc
  have reading : (QuarticTrace.complete (p*q) 1).natAbs=4*a*c := by
    rw [QuarticTrace.complete_eq p q cop,Int.natAbs_mul]
    simp only [Int.cast_one,ta,tc]; ring
  dsimp only
  rw [reading]
  push_cast
  exact from_arbitrary_rep Fact.out Fact.out ap cp pn qn z nz

example : 5∈traceProbe 65 12 1 ∧ 13∈traceProbe 65 12 1 ∧
    5∈fromRepresentation 65 12 ⟨4,7⟩ ∧ 13∈fromRepresentation 65 12 ⟨1,8⟩ := by decide +kernel

end PrimeFactors.GaussianTraceRecovery
