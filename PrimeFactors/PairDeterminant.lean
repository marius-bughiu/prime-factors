import PrimeFactors.SameSourcePair

namespace PrimeFactors.PairDeterminant

/-- The determinant of rows one step apart is preserved in absolute value by
one Euclidean update. Skipping the middle row multiplies it by the quotient. -/
theorem skip_one {a b c d N : ℤ} (det : a*d-b*c=N) (q : ℤ) :
    c*(b-q*d)-d*(a-q*c) = -N ∧
    a*(b-q*d)-b*(a-q*c) = -q*N := by
  rw [← det]
  constructor <;> ring

/-- The ordered cross products of a qualifying pair give a difference of two
coprime squares. Its multiplier is the determinant quotient divided by the gcd. -/
theorem normalize {U V N h z : ℕ} (vpos : 0 < V) (ordered : V < U)
    (det : U = V+h*N) (unit : U.Coprime N) (square : U*V = z^2) (short : 2*z < N) :
    let g := U.gcd V
    ∃ k u v, h=g*k ∧ U=g*u^2 ∧ V=g*v^2 ∧ u.Coprime v ∧
      0<v ∧ v<u ∧ u^2=v^2+k*N ∧ 2*g*u*v<N := by
  let g := U.gcd V
  have gp : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨u,v,hu,hv,cp⟩ := SameSourcePair.reduced_squares (lt_trans vpos ordered) square
  change U=g*u^2 at hu
  change V=g*v^2 at hv
  have vg : g ∣ V := Nat.gcd_dvd_right _ _
  have ug : g ∣ U := Nat.gcd_dvd_left _ _
  have gh : g ∣ h*N := (Nat.dvd_add_right vg).mp (det ▸ ug)
  have gn : g.Coprime N := unit.of_dvd_left ug
  obtain ⟨k,hk⟩ := gn.dvd_of_dvd_mul_right gh
  have norm : u^2=v^2+k*N := Nat.eq_of_mul_eq_mul_left gp (by
    calc
      g*u^2 = V+h*N := hu.symm.trans det
      _ = g*(v^2+k*N) := by rw [hv,hk]; ring)
  have vp : 0 < v := by by_contra! e; simp [Nat.eq_zero_of_le_zero e] at hv; omega
  have increasing : v < u := by
    by_contra! e
    have := Nat.mul_le_mul_left g (Nat.pow_le_pow_left e 2)
    omega
  have root : g*u*v=z := Nat.pow_left_injective two_ne_zero (by
    calc
      (g*u*v)^2 = (g*u^2)*(g*v^2) := by ring
      _ = z^2 := by rw [←hu,←hv,square])
  exact ⟨k,u,v,hk,hu,hv,cp,vp,increasing,norm,by simpa only [← Nat.mul_assoc] using
    (show 2*(g*u*v)<N by rwa [root])⟩

/-- Every primitive short solution supplies the two reciprocal fractions
u/v and v/u at a single residue computed from u and v. -/
theorem reciprocal {N u v k : ℕ} (vc : v.Coprime N) (uc : u.Coprime N)
    (norm : u^2=v^2+k*N) :
    ∃ r : ZMod N, IsUnit r ∧ (v : ZMod N)*r=u ∧ (u : ZMod N)*r=v ∧
      (u*v)*(v*u)=(u*v)^2 := by
  let U := ZMod.unitOfCoprime u uc
  let V := ZMod.unitOfCoprime v vc
  have a : (U : ZMod N) = u := rfl
  have b : (V : ZMod N) = v := rfl
  have squares : (U : ZMod N)^2=(V : ZMod N)^2 := by
    simpa [a,b] using congrArg (fun n : ℕ => (n : ZMod N)) norm
  refine ⟨((U*V⁻¹ : (ZMod N)ˣ) : ZMod N),(U*V⁻¹).isUnit,?_,?_,by ring⟩
  · rw [← a,← b]
    simp [mul_left_comm]
  · rw [← a,← b, Units.val_mul, ← mul_assoc, ← sq, squares, sq, mul_assoc]
    simp

/-- Exact integer endpoints for the midpoint. They can be evaluated from N,
the normalized multiplier k and the common factor g of the cross products. -/
theorem window {N g k u v : ℕ} (vp : 0 < v) (gp : 0 < g)
    (norm : u^2 = v^2+k*N) (short : 2*g*u*v < N) :
    (k*N).sqrt+1 ≤ u ∧
    u ≤ ((g*k*N + ((g*k*N)^2+N^2-1).sqrt)/(2*g)).sqrt := by
  have lower : k*N < u^2 := by rw [norm]; have := pow_pos vp 2; omega
  have cross : (g*(u^2+v^2))^2 = (g*k*N)^2 + (2*g*u*v)^2 := by
    calc
      _ = (g*k*N)^2 + 4*g^2*u^2*v^2 := by rw [norm]; ring
      _ = _ := by ring
  have strict : (g*(u^2+v^2))^2 < (g*k*N)^2+N^2 := by
    rw [cross]
    exact Nat.add_lt_add_left (Nat.pow_lt_pow_left short two_ne_zero) _
  have hi := Nat.le_sqrt'.mpr (show (g*(u^2+v^2))^2 ≤ (g*k*N)^2+N^2-1 by omega)
  have twice : 2*g*u^2 = g*k*N + g*(u^2+v^2) := by rw [norm]; ring
  refine ⟨Nat.sqrt_lt'.mpr lower,Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by omega)).mpr ?_)⟩
  calc
    u^2*(2*g) = 2*g*u^2 := Nat.mul_comm ..
    _ ≤ _ := twice.trans_le (Nat.add_le_add_left hi _)

private theorem second_midpoint {N k u v : ℕ} (norm : u^2=v^2+k*N)
    (later : (k*N).sqrt+1 < u) : 2*u ≤ v^2 := by
  have lo : (k*N).sqrt < u-1 := by omega
  have prev := Nat.sqrt_lt'.mp lo
  have one : u-1+1=u := by omega
  have alg : u^2+1 = (u-1)^2+2*u := by
    calc
      u^2+1 = (u-1+1)^2+1 := by rw [one]
      _ = (u-1)^2+2*(u-1+1) := by ring
      _ = _ := by rw [one]
  omega

/-- Above this cube-root multiplier threshold every short pair is decided
by a single midpoint test immediately above the integer square root. -/
theorem one_midpoint {N g k u v : ℕ} (vp : 0 < v) (gp : 0 < g)
    (norm : u^2=v^2+k*N) (short : 2*g*u*v<N) (threshold : N ≤ 64*g^4*k^3) :
    u = (k*N).sqrt+1 := by
  have low := (window vp gp norm short).1
  by_contra ne
  have growth := second_midpoint norm (show (k*N).sqrt+1 < u by omega)
  have small := Nat.pow_lt_pow_left short (by decide : 2 ≠ 0)
  have cube : 8*g^2*u^3 < N^2 := by
    calc
      _ = 4*g^2*u^2*(2*u) := by ring
      _ ≤ 4*g^2*u^2*v^2 := Nat.mul_le_mul_left _ growth
      _ = (2*g*u*v)^2 := by ring
      _ < _ := small
  have npos : 0 < N := by omega
  have bad : 64*g^4*k^3*N^3 < N*N^3 := by
    calc
      _ = 64*g^4*(k*N)^3 := by ring
      _ ≤ 64*g^4*(u^2)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      _ = (8*g^2*u^3)^2 := by ring
      _ < (N^2)^2 := Nat.pow_lt_pow_left cube two_ne_zero
      _ = _ := by ring
  exact (Nat.not_lt_of_ge threshold) ((Nat.mul_lt_mul_right (pow_pos npos 3)).mp bad)

/-- When one row has absolute norm at most H and its partner has twice its
norm below N, the normalized squared gap times 2*g²*k is strictly below H. -/
theorem height_gap {N g k u v H : ℕ} (norm : u^2=v^2+k*N)
    (small : 2*g^2*u^2*v^2 < N*H) : 2*g^2*k*v^2 < H := by
  have smaller : N*(2*g^2*k*v^2)<N*H := by
    calc
      _ = 2*g^2*(k*N)*v^2 := by ring
      _ ≤ 2*g^2*u^2*v^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ < _ := small
  exact lt_of_not_ge (fun bad => (not_lt_of_ge (Nat.mul_le_mul_left _ bad)) smaller)

/-- A short planted row forces the normalized Fermat midpoint to be the first
integer above the square root whenever H² ≤ 16*g⁴*k³*N. -/
theorem height_midpoint {N g k u v H : ℕ} (vp : 0 < v)
    (norm : u^2=v^2+k*N) (small : 2*g^2*u^2*v^2 < N*H)
    (threshold : H^2 ≤ 16*g^4*k^3*N) : u=(k*N).sqrt+1 := by
  have posSquare := pow_pos vp 2
  have low := Nat.sqrt_lt'.mpr (show k*N < u^2 by omega)
  by_contra ne
  have growth := second_midpoint norm (show (k*N).sqrt+1 < u by omega)
  have tooSmall : 4*g^2*k*u<H := by
    calc
      _ = 2*g^2*k*(2*u) := by ring
      _ ≤ 2*g^2*k*v^2 := Nat.mul_le_mul_left _ growth
      _ < _ := height_gap norm small
  have contradiction : 16*g^4*k^3*N < H^2 := by
    calc
      _ = 16*g^4*k^2*(k*N) := by ring
      _ ≤ 16*g^4*k^2*u^2 := Nat.mul_le_mul_left _ (by omega)
      _ = (4*g^2*k*u)^2 := by ring
      _ < _ := Nat.pow_lt_pow_left tooSmall two_ne_zero
  exact (not_lt_of_ge threshold) contradiction

/-- For every positive multiplier and gcd the uniform threshold H² ≤ 16N
suffices, and the integer gap obeys 2*k*v² < H. -/
theorem short_row {N g k u v H : ℕ} (gp : 0<g) (kp : 0<k) (vp : 0<v)
    (norm : u^2=v^2+k*N) (small : 2*g^2*u^2*v^2 < N*H) (threshold : H^2≤16*N) :
    2*k*v^2<H ∧ u=(k*N).sqrt+1 := by
  have p2 : 1 ≤ g^2 := pow_pos gp 2
  have p4 : 1 ≤ g^4*k^3 := Nat.mul_pos (pow_pos gp 4) (pow_pos kp 3)
  constructor
  · calc
      _ ≤ 2*k*v^2*g^2 := Nat.le_mul_of_pos_right _ p2
      _ = 2*g^2*k*v^2 := by ring
      _ < _ := height_gap norm small
  · apply height_midpoint vp norm small
    calc
      _ ≤ 16*N := threshold
      _ ≤ 16*N*(g^4*k^3) := Nat.le_mul_of_pos_right _ p4
      _ = _ := by ring

/-- Each prime lands on a different side of the difference of squares, so
the two unknown prime weights multiply to the normalized determinant. -/
theorem weights {p q k u v : ℕ} (hp : p.Prime) (hq : q.Prime) (distinct : p≠q)
    (vp : 0<v) (ordered : v<u) (norm : u^2=v^2+k*(p*q)) (short : 2*u*v<p*q) :
    ∃ a b, k=a*b ∧ ((u+v=a*p ∧ u-v=b*q) ∨ (u-v=a*p ∧ u+v=b*q)) := by
  let M := u+v
  let D := u-v
  have dp : 0<D := Nat.sub_pos_of_lt ordered
  have add : D+v=u := Nat.sub_add_cancel ordered.le
  have product : M*D=k*(p*q) := by
    dsimp [M]
    nlinarith only [norm, congrArg (fun x : ℕ => x^2) add, congrArg (fun x : ℕ => x*D) add,
      congrArg (fun x : ℕ => x*v) add]
  have up := lt_trans vp ordered
  have top : M<p*q := by
    have vu := Nat.le_mul_of_pos_right u vp
    have uv := Nat.le_mul_of_pos_left v up
    dsimp [M]
    nlinarith only [short,vu,uv]
  have small : D<p*q := lt_of_le_of_lt (le_trans (Nat.sub_le ..) (Nat.le_add_right ..)) top
  have noM : ¬p*q ∣ M := Nat.not_dvd_of_pos_of_lt (by dsimp [M]; omega) top
  have noD : ¬p*q ∣ D := Nat.not_dvd_of_pos_of_lt dp small
  have divides : p*q ∣ M*D := ⟨k,product.trans (Nat.mul_comm ..)⟩
  have pd := hp.dvd_mul.mp ((dvd_mul_right p q).trans divides)
  have qd := hq.dvd_mul.mp ((dvd_mul_left q p).trans divides)
  have cop := (Nat.coprime_primes hp hq).mpr distinct
  have same {a b : ℕ} (sides : M*D=(a*p)*(b*q)) : k=a*b :=
    Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hp.pos hq.pos) (by
      calc
        _ = M*D := product.symm
        _ = _ := sides
        _ = _ := by ring)
  rcases pd with pm | pd <;> rcases qd with qm | qd
  · exact False.elim (noM (cop.mul_dvd_of_dvd_of_dvd pm qm))
  · obtain ⟨a,ha⟩ := pm
    obtain ⟨b,hb⟩ := qd
    rw [Nat.mul_comm p a] at ha
    rw [Nat.mul_comm q b] at hb
    exact ⟨a,b,same (by rw [ha,hb]),Or.inl ⟨ha,hb⟩⟩
  · obtain ⟨a,ha⟩ := pd
    obtain ⟨b,hb⟩ := qm
    rw [Nat.mul_comm p a] at ha
    rw [Nat.mul_comm q b] at hb
    exact ⟨a,b,same (by rw [ha,hb,Nat.mul_comm (b*q)]),Or.inr ⟨ha,hb⟩⟩
  · exact False.elim (noD (cop.mul_dvd_of_dvd_of_dvd pd qd))

/-- This product has a short witness at multiplier 209. The ordinary midpoint
of the two primes is 51 integers above the floor of the square root. -/
theorem example_1832087 :
    19568^2=21^2+209*1832087 ∧ 2*19568*21<1832087 ∧
    1832087 ≤ 64*209^3 ∧ (209*1832087).sqrt+1=19568 ∧
    (19568+21).gcd 1832087=1031 ∧ 1031*1777=1832087 ∧
    (1031+1777)/2=(1832087 : ℕ).sqrt+51 := by
  have weighted : 19567=(209*1832087).sqrt := Nat.eq_sqrt'.mpr (by decide)
  have base : 1353=(1832087 : ℕ).sqrt := Nat.eq_sqrt'.mpr (by decide)
  rw [←weighted, ←base]
  decide

end PrimeFactors.PairDeterminant
