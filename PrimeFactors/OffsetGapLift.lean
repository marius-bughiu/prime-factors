import PrimeFactors.OffsetCoordinateGaps
import PrimeFactors.GapStride

namespace PrimeFactors.OffsetGapLift

/-- The fourth-power projector works at every divisor of the chart multiplier. -/
theorem fourth_projector {s v : ℤ} (cop : IsCoprime s v) :
    ∃ e : ℤ, v^4 ∣ e ∧ s^4 ∣ 1-e := by
  obtain ⟨a,b,e⟩ := (show IsCoprime (s^4) (v^4) from cop.pow_left.pow_right)
  exact ⟨v^4*b,⟨b,rfl⟩,⟨a,by linear_combination -e⟩⟩

/-- A projector exists at the partial moduli used by the computation. -/
theorem partial_projector {s v ds dv : ℤ} (cop : IsCoprime s v) (sd : ds ∣ s) (vd : dv ∣ v) :
    ∃ e : ℤ, v^2*dv^2 ∣ e ∧ s^2*ds^2 ∣ 1-e := by
  obtain ⟨e,ev,es⟩ := fourth_projector cop
  have divides {r d : ℤ} (part : d ∣ r) : r^2*d^2 ∣ r^4 := by
    obtain ⟨x,hx⟩ := part
    exact ⟨x^2,by rw [hx]; ring⟩
  exact ⟨e,(divides vd).trans ev,(divides sd).trans es⟩

theorem inverse_exists {S d : ℤ} (unit : IsCoprime S d) :
    ∃ U : ℤ, d^2 ∣ S*U-1 := by
  obtain ⟨u,w,eq⟩ := (show IsCoprime S (d^2) from unit.pow_right)
  exact ⟨u,-w,by linear_combination eq⟩

private theorem root_digit {p q s v ds dv S U : ℤ} (div : ds ∣ s)
    (trace : S=p*s^2+q*v^2) (inv : (ds*dv)^2 ∣ S*U-1) :
    s^2*ds^2 ∣ p*s^2-(p*q)*(s*v)^2*U := by
  obtain ⟨x,hx⟩ := div
  obtain ⟨w,hw⟩ := inv
  refine ⟨(p*x)^2*U-p*dv^2*w,?_⟩
  calc _ = (p*s^2)^2*U-p*s^2*(S*U-1) := by rw [trace]; ring
       _ = _ := by rw [hw,hx]; ring

/-- For d=ds*dv with ds|s and dv|v, an inverse of the trace modulo d²
determines the oriented gap modulo 2 k² d². This also includes even k. -/
theorem signed_lift {p q s v ds dv S U e : ℤ} (sd : ds ∣ s) (vd : dv ∣ v)
    (trace : S=p*s^2+q*v^2) (inv : (ds*dv)^2 ∣ S*U-1)
    (ev : v^2*dv^2 ∣ e) (es : s^2*ds^2 ∣ 1-e) :
    2*(s*v)^2*(ds*dv)^2 ∣ (p*s^2-q*v^2) -
      (1-2*e)*(S-2*(p*q)*(s*v)^2*U) := by
  obtain ⟨a,ha⟩ := root_digit sd trace inv
  have reversed : S=q*v^2+p*s^2 := trace.trans (add_comm _ _)
  obtain ⟨b,hb⟩ := root_digit vd reversed (show (dv*ds)^2 ∣ S*U-1 by rwa [mul_comm dv ds])
  rw [mul_comm q p,mul_comm v s] at hb
  obtain ⟨ne,hne⟩ := es
  obtain ⟨ee,hee⟩ := ev
  refine ⟨ee*a-ne*b,?_⟩
  calc _ = 2*e*(p*s^2-(p*q)*(s*v)^2*U) -
           2*(1-e)*(q*v^2-(p*q)*(s*v)^2*U) := by rw [trace]; ring
       _ = _ := by rw [ha,hb,hne,hee]; ring

/-- The inverse is affine along a residue class modulo d. One inverse at
its start suffices for all integer parameters, including negative ones. -/
theorem inverse_affine {S d U : ℤ} (inv : d^2 ∣ S*U-1) (t : ℤ) :
    d^2 ∣ (S+d*t)*(U-d*t*U^2)-1 := by
  obtain ⟨w,hw⟩ := inv
  refine ⟨(1-d*t*U)*w-t^2*U^2,?_⟩
  calc _ = (1-d*t*U)*(S*U-1)-d^2*t^2*U^2 := by ring
       _ = _ := by rw [hw]; ring

/-- The intercept and slope supplied to a linear modular-interval counter. -/
theorem signed_class {p q s v ds dv S₀ U₀ e t : ℤ} (sd : ds ∣ s) (vd : dv ∣ v)
    (trace : S₀+(ds*dv)*t=p*s^2+q*v^2) (inv : (ds*dv)^2 ∣ S₀*U₀-1)
    (ev : v^2*dv^2 ∣ e) (es : s^2*ds^2 ∣ 1-e) :
    2*(s*v)^2*(ds*dv)^2 ∣ (p*s^2-q*v^2) -
      ((1-2*e)*(S₀-2*(p*q)*(s*v)^2*U₀) +
      (1-2*e)*(ds*dv)*(1+2*(p*q)*(s*v)^2*U₀^2)*t) := by
  convert signed_lift sd vd trace (inverse_affine inv t) ev es using 1; ring

/-- For odd d the old parity class supplies an extra bit throughout the
new progression. At d=1 the combination reduces to the old class. -/
theorem combine_parity {K d z lifted old : ℤ} (odd : Odd d)
    (newClass : 2*K*d^2 ∣ z-lifted) (oldClass : 4*K ∣ z-old) :
    4*K*d^2 ∣ z-((1-d^2)*lifted+d^2*old) := by
  obtain ⟨w,hw⟩ := newClass
  obtain ⟨y,hy⟩ := oldClass
  obtain ⟨b,hb⟩ := odd
  refine ⟨-(2*b^2+2*b)*w+y,?_⟩
  calc _ = (1-d^2)*(z-lifted)+d^2*(z-old) := by ring
       _ = _ := by rw [hw,hy,hb]; ring

/-- At three consecutive unit points, an affine inverse forces a
divisibility condition on the square of the stride. -/
theorem inverse_stride {m S D u₀ u₁ u₂ : ℤ}
    (h₀ : m ∣ S*u₀-1) (h₁ : m ∣ (S+D)*u₁-1) (h₂ : m ∣ (S+2*D)*u₂-1)
    (affine : m ∣ u₂-2*u₁+u₀) : m ∣ 2*D^2 := by
  obtain ⟨a,ha⟩ := h₀
  obtain ⟨b,hb⟩ := h₁
  obtain ⟨c,hc⟩ := h₂
  obtain ⟨e,he⟩ := affine
  refine ⟨e*S*(S+D)*(S+2*D)-a*(S+D)*(S+2*D)+2*b*S*(S+2*D)-c*S*(S+D),?_⟩
  calc _ = (u₂-2*u₁+u₀)*S*(S+D)*(S+2*D) -
      (S*u₀-1)*(S+D)*(S+2*D)+2*((S+D)*u₁-1)*S*(S+2*D) -
      ((S+2*D)*u₂-1)*S*(S+D) := by ring
       _ = _ := by rw [ha,hb,hc,he]; ring

private theorem root_unit_digit {p q s v ds dv S U m : ℤ} (div : ds ∣ s)
    (trace : S=p*s^2+q*v^2) (inv : m*(ds*dv)^2 ∣ S*U-1) (sq : m ∣ p^2-1) :
    m*s^2*ds^2 ∣ p*s^2-((p*q)*(s*v)^2+s^4)*U := by
  obtain ⟨x,hx⟩ := div
  obtain ⟨w,hw⟩ := inv
  obtain ⟨c,hc⟩ := sq
  refine ⟨x^2*c*U-p*dv^2*w,?_⟩
  calc _ = s^4*(p^2-1)*U-p*s^2*(S*U-1) := by rw [trace]; ring
       _ = _ := by rw [hw,hc,hx]; ring

/-- If both factors square to one modulo m, the signed residue has m
as an additional factor in the modulus.
No invertibility at primes outside md is required. -/
theorem signed_unit_lift {p q s v ds dv S U e m : ℤ} (sd : ds ∣ s) (vd : dv ∣ v)
    (trace : S=p*s^2+q*v^2) (inv : m*(ds*dv)^2 ∣ S*U-1)
    (pp : m ∣ p^2-1) (qq : m ∣ q^2-1) (ev : v^2*dv^2 ∣ e) (es : s^2*ds^2 ∣ 1-e) :
    2*m*(s*v)^2*(ds*dv)^2 ∣ (p*s^2-q*v^2) -
      ((1-2*e)*(S-2*(p*q)*(s*v)^2*U)+2*(e*s^4-(1-e)*v^4)*U) := by
  obtain ⟨a,ha⟩ := root_unit_digit sd trace inv pp
  have reversed : S=q*v^2+p*s^2 := trace.trans (add_comm _ _)
  obtain ⟨b,hb⟩ := root_unit_digit vd reversed
    (show m*(dv*ds)^2 ∣ S*U-1 by rwa [mul_comm dv ds]) qq
  rw [mul_comm q p,mul_comm v s] at hb
  obtain ⟨ne,hne⟩ := es
  obtain ⟨ee,hee⟩ := ev
  refine ⟨ee*a-ne*b,?_⟩
  calc _ = 2*e*(p*s^2-((p*q)*(s*v)^2+s^4)*U) -
           2*(1-e)*(q*v^2-((p*q)*(s*v)^2+v^4)*U) := by rw [trace]; ring
       _ = _ := by rw [ha,hb,hne,hee]; ring

/-- Exactly the same stride condition is sufficient to extend the unique
linear interpolation of two initial inverses to every integer index. -/
theorem inverse_secant {m S D u₀ u₁ : ℤ} (h₀ : m ∣ S*u₀-1)
    (h₁ : m ∣ (S+D)*u₁-1) (stride : m ∣ 2*D^2) (i : ℤ) :
    m ∣ (S+D*i)*(u₀+(u₁-u₀)*i)-1 := by
  obtain ⟨a,ha⟩ := h₀
  obtain ⟨b,hb⟩ := h₁
  obtain ⟨w,hw⟩ := stride
  obtain ⟨l,hl⟩ := i.even_mul_pred_self.two_dvd
  have slope : u₁-u₀ = m*(b*u₀-a*u₁)-D*u₀*u₁ := by
    linear_combination u₀*hb - u₁*ha
  refine ⟨(1-i)*a+i*b+D*(b*u₀-a*u₁)*(2*l)-w*u₀*u₁*l,?_⟩
  calc _ = (1-i)*(S*u₀-1)+i*((S+D)*u₁-1)+D*(u₁-u₀)*(i*(i-1)) := by ring
       _ = m*((1-i)*a+i*b+D*(b*u₀-a*u₁)*(2*l))-(2*D^2)*u₀*u₁*l := by
         rw [ha,hb,slope,hl]; ring
       _ = _ := by rw [hw]; ring

theorem odd_square {p : ℤ} (po : Odd p) : 8 ∣ p^2-1 := by
  obtain ⟨a,ha⟩ := po
  obtain ⟨l,lh⟩ := (a+1).even_mul_pred_self.two_dvd
  refine ⟨l,?_⟩
  rw [ha]
  linear_combination 4*lh

/-- Constant precision m at d=1. When the trace squares to one modulo m,
the residue is an affine function of the trace with no inverse queries. -/
theorem self_inverse_slope {p q s v S e m : ℤ} (trace : S=p*s^2+q*v^2)
    (pp : m ∣ p^2-1) (qq : m ∣ q^2-1) (ss : m ∣ S^2-1)
    (ev : v^2 ∣ e) (es : s^2 ∣ 1-e) :
    2*m*(s*v)^2 ∣ p*s^2-q*v^2-
      ((1-2*e)*(1-2*(p*q)*(s*v)^2)+2*(e*s^4-(1-e)*v^4))*S := by
  have inv : m*(1*1)^2 ∣ S*S-1 := by simpa [pow_two] using ss
  have h := signed_unit_lift (one_dvd s) (one_dvd v) trace inv pp qq
    (by simpa using ev) (by simpa using es)
  convert h using 1 <;> ring

/-- On odd traces of an odd product the previous chart costs no extra
classes and has modulus 16 k². -/
theorem odd_trace {p q s v S e : ℤ} (trace : S=p*s^2+q*v^2)
    (po : Odd p) (qo : Odd q) (so : Odd S) (ev : v^2 ∣ e) (es : s^2 ∣ 1-e) :
    16*(s*v)^2 ∣ p*s^2-q*v^2-
      ((1-2*e)*(1-2*(p*q)*(s*v)^2)+2*(e*s^4-(1-e)*v^4))*S :=
  self_inverse_slope trace (odd_square po) (odd_square qo) (odd_square so) ev es

/-- Every integer coprime to six squares to one modulo 24. -/
theorem unit24_square {p : ℕ} (unit : p.Coprime 6) : (24:ℤ) ∣ (p:ℤ)^2-1 := by
  simpa using Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr (square_mod_twentyfour unit)).symm

/-- In the full lift m=k² the reciprocal stride is a multiple of k. -/
theorem square_stride {k D : ℕ} (kp : 0<k) (stride : k^2 ∣ 2*D^2) : k ∣ D := by
  let g := k.gcd D
  let a := k/g
  let b := D/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left D kp
  have ka : a*g=k := Nat.div_mul_cancel (Nat.gcd_dvd_left k D)
  have db : b*g=D := Nat.div_mul_cancel (Nat.gcd_dvd_right k D)
  have cop : a.Coprime b := Nat.coprime_div_gcd_div_gcd gp
  obtain ⟨w,hw⟩ := stride
  have reduced : a^2 ∣ 2*b^2 := by
    refine ⟨w,Nat.eq_of_mul_eq_mul_left (Nat.pow_pos gp (n:=2)) ?_⟩
    calc g^2*(2*b^2) = 2*(b*g)^2 := by ring
         _ = (a*g)^2*w := by rw [ka,db,hw]
         _ = _ := by ring
  have div : a^2 ∣ 2 := ((cop.pow_left 2).pow_right 2).dvd_of_dvd_mul_right reduced
  have limit := Nat.le_of_dvd (by decide : 0<2) div
  have ap : 0<a := Nat.pos_of_mul_pos_right (show 0<a*g by rwa [ka])
  have one : a=1 := by nlinarith
  rw [←ka,one,one_mul,←db]
  exact dvd_mul_left _ _

/-- The signed multiplier of a partial projector is a unit modulo d². -/
theorem projector_unit {s v ds dv e : ℤ} (ev : v^2*dv^2 ∣ e) (es : s^2*ds^2 ∣ 1-e) :
    IsCoprime (1-2*e) ((ds*dv)^2) := by
  obtain ⟨a,ha⟩ := ev
  obtain ⟨b,hb⟩ := es
  refine ⟨1-2*e, 4*v^2*s^2*a*b,?_⟩
  calc _ = (1-2*e)^2+4*(v^2*dv^2*a)*(s^2*ds^2*b) := by ring
       _ = 1 := by rw [←ha,←hb]; ring

/-- At a full second lift, affine signed residues at three consecutive
unit traces force the inverse to be affine there, provided N is a unit.
This obstruction concerns a single affine progression. -/
theorem lifted_stride {N K m C S D u₀ u₁ u₂ : ℤ} (kp : K≠0)
    (nc : IsCoprime N m) (cc : IsCoprime C m) (h₀ : m ∣ S*u₀-1)
    (h₁ : m ∣ (S+D)*u₁-1) (h₂ : m ∣ (S+2*D)*u₂-1)
    (affine : 2*K*m ∣ C*(S+2*D-2*N*K*u₂) - 2*C*(S+D-2*N*K*u₁)
      + C*(S-2*N*K*u₀)) : m ∣ 2*D^2 := by
  obtain ⟨w,hw⟩ := affine
  have cancel : (N*C)*(u₂-2*u₁+u₀) = m*(-w) := by
    apply mul_left_cancel₀ (mul_ne_zero (by decide : (2:ℤ)≠0) kp)
    linear_combination -hw
  exact inverse_stride h₀ h₁ h₂
    ((nc.mul_left cc).symm.dvd_of_dvd_mul_left ⟨-w,cancel⟩)

/-- Every proper primitive probe hit has an oriented coordinate pair for
which every divisor of k gives the signed residue above. -/
theorem chart_of_hit {p q T j k f : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (kp : 0<k) (primitive : j.Coprime k)
    (hit : CompleteOffsetSearch.probe (p*q) T j k=some f) :
    ∃ s v : ℕ, 0<s ∧ 0<v ∧ s.Coprime v ∧ k=s*v ∧
      ∀ d : ℕ, d ∣ k → ∃ ds dv : ℕ, d=ds*dv ∧ ds∣s ∧ dv∣v ∧
      ∃ e U : ℤ, v^2*(dv:ℤ)^2 ∣ e ∧ s^2*(ds:ℤ)^2 ∣ 1-e ∧
        (d:ℤ)^2 ∣ (j+2*(T:ℤ)*k)*U-1 ∧
        2*(k:ℤ)^2*(d:ℤ)^2 ∣ ((p:ℤ)*s^2-(q:ℤ)*v^2) -
        (1-2*e)*((j+2*(T:ℤ)*k)-2*((p:ℤ)*q)*k^2*U) := by
  obtain ⟨s,v,sp,vp,prim,ks,sum⟩ := OffsetSquareWitness.exists_vector_of_hit pp qp ne kp primitive hit
  refine ⟨s,v,sp,vp,prim,ks,?_⟩
  intro d div
  let ds := d.gcd s
  let dv := d.gcd v
  have split : ds*dv=d := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime prim).mpr (ks ▸ div)
  have sd := Nat.gcd_dvd_right d s
  have vd := Nat.gcd_dvd_right d v
  have cds : (ds:ℤ) ∣ (s:ℤ) := by exact_mod_cast sd
  have cdv : (dv:ℤ) ∣ (v:ℤ) := by exact_mod_cast vd
  have csv : IsCoprime (s:ℤ) v := Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using prim)
  obtain ⟨e,ev,es⟩ := partial_projector csv cds cdv
  have cjk : IsCoprime (j:ℤ) k := Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using primitive)
  obtain ⟨a,b,ab⟩ := cjk
  obtain ⟨w,kw⟩ := div
  have ck : (k:ℤ)=(d:ℤ)*w := by exact_mod_cast kw
  have unit : IsCoprime (j+2*(T:ℤ)*k) d := by
    refine ⟨a,(b-2*T*a)*w,?_⟩
    rw [ck] at ab ⊢
    linear_combination ab
  obtain ⟨U,inv⟩ := inverse_exists unit
  refine ⟨ds,dv,split.symm,sd,vd,e,U,ev,es,inv,?_⟩
  have kd : (k:ℤ)=(s:ℤ)*v := by exact_mod_cast ks
  have dd : (ds:ℤ)*dv=(d:ℤ) := by exact_mod_cast split
  have st : (j+2*(T:ℤ)*k)=(p:ℤ)*s^2+(q:ℤ)*v^2 := by exact_mod_cast sum
  have h := signed_lift cds cdv st (dd ▸ inv) ev es
  rwa [←kd,dd] at h

/-- The required last slot at 117449, at the full d=12, m=24 lift. -/
theorem example117449 :
    let p : ℤ := 257
    let q : ℤ := 457
    let s : ℤ := 4
    let v : ℤ := 3
    let k := s*v
    let S := 17+2*342*k
    let e : ℤ := 14337
    let U : ℤ := 737
    let modulus := 2*24*k^2*k^2
    let residue := (1-2*e)*(S-2*(p*q)*k^2*U)+2*(e*s^4-(1-e)*v^4)*U
    p*q=117449 ∧ S=p*s^2+q*v^2 ∧ 24*k^2 ∣ S*U-1 ∧
    v^4 ∣ e ∧ s^4 ∣ 1-e ∧ modulus=995328 ∧
    p*s^2-q*v^2=-1 ∧ residue%modulus=995327 := by decide +kernel

end PrimeFactors.OffsetGapLift
