import PrimeFactors.HyperbolicNormArc
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Group.Commute.Units

/-! A split conic modulo an odd modulus has exactly φ(h) branches. In
each smooth branch, lifting the equation to h² restricts the next
coordinates to a single affine line modulo h. -/
namespace PrimeFactors.ConicTangentLattice

section Split
variable {R : Type*} [CommRing R] {t c : R}

private theorem product_eq {u z : R} (point : z^2-t^2*u^2=c) :
    (z-t*u)*(z+t*u)=c := by linear_combination point

private theorem unit_left {u z : R} (hc : IsUnit c) (point : z^2-t^2*u^2=c) :
    IsUnit (z-t*u) := ((Commute.all _ _).isUnit_mul_iff.mp ((product_eq point).symm ▸ hc)).1

/-- The parameter is z−tu. Its companion z+tu is forced by their
product c. Units of 2 and t permit the inverse coordinate change. -/
noncomputable def splitEquiv (htwo : IsUnit (2:R)) (ht : IsUnit t) (hc : IsUnit c) :
    {q : R × R // q.2^2-t^2*q.1^2=c} ≃ Rˣ := by
  let f (q : {q : R × R // q.2^2-t^2*q.1^2=c}) := (unit_left hc q.property).unit
  apply Equiv.ofBijective f
  refine ⟨?_, ?_⟩
  · intro q r eqn
    have same : q.val.2-t*q.val.1=r.val.2-t*r.val.1 := by
      simpa only [f,IsUnit.unit_spec] using congrArg Units.val eqn
    have comp : q.val.2+t*q.val.1=r.val.2+t*r.val.1 := by
      apply (unit_left hc q.property).mul_right_inj.mp
      conv_rhs => rw [same]
      exact (product_eq q.property).trans (product_eq r.property).symm
    apply Subtype.ext
    apply Prod.ext
    · apply ht.mul_right_inj.mp
      apply htwo.mul_right_inj.mp
      linear_combination comp-same
    · apply htwo.mul_right_inj.mp
      linear_combination comp+same
  · intro v
    let half : R := ↑htwo.unit⁻¹
    let invt : R := ↑ht.unit⁻¹
    let left : R := v
    let right : R := c * ↑v⁻¹
    let u := half*invt*(right-left)
    let z := half*(left+right)
    have h2 : 2*half=1 := by simpa only [half,htwo.unit_spec] using htwo.unit.mul_inv
    have ht' : t*invt=1 := by simpa only [invt,ht.unit_spec] using ht.unit.mul_inv
    have l : z-t*u=left := by
      dsimp only [u,z]
      linear_combination left*h2 - half*(right-left)*ht'
    have r : z+t*u=right := by
      dsimp only [u,z]
      linear_combination right*h2 + half*(right-left)*ht'
    have lr : left*right=c := by
      dsimp only [left,right]
      rw [mul_left_comm,v.mul_inv,mul_one]
    have pt : z^2-t^2*u^2=c := calc
      _ = (z-t*u)*(z+t*u) := by ring
      _ = c := by rw [l,r,lr]
    refine ⟨⟨(u,z),pt⟩, Units.ext ?_⟩
    exact (IsUnit.unit_spec _).trans l

/-- The formula works for composite and prime-power moduli whenever the
split slope and normalized right hand side are units. -/
theorem split_count {h : ℕ} [NeZero h] {t c : ZMod h}
    (htwo : IsUnit (2 : ZMod h)) (ht : IsUnit t) (hc : IsUnit c) :
    Fintype.card {q : ZMod h × ZMod h // q.2^2-t^2*q.1^2=c} = Nat.totient h :=
  (Fintype.card_congr (splitEquiv htwo ht hc)).trans (ZMod.card_units_eq_totient h)

end Split

/-- Taylor expansion at the representatives (r,s) gives the single
linear congruence in the first lifted digits (i,j). The integer c is
the quotient of the base-point residual by the modulus. -/
theorem tangent {a b M h r s i j c : ℤ} (hn : h≠0)
    (atBase : b*s^2-a*r^2-M=h*c)
    (point : b*(s+h*j)^2-a*(r+h*i)^2=M) :
    c+2*b*s*j-2*a*r*i = h*(a*i^2-b*j^2) := by
  apply mul_left_cancel₀ hn
  linear_combination point - atBase

/-- For the practical chart with z a unit modulo h, a residue k for the
slope and l for the offset converts the tangent restriction exactly into
j = l+k i modulo h. The Bézout identity expresses invertibility. -/
theorem lift_graph {a b h r s i j c k l inv v w x : ℤ}
    (inverse : (2*b*s)*inv=1+h*v)
    (slope : (2*b*s)*k-2*a*r=h*w) (offset : (2*b*s)*l+c=h*x)
    (tan : h ∣ c+2*b*s*j-2*a*r*i) : h ∣ j-l-k*i := by
  obtain ⟨d,hd⟩ := tan
  refine ⟨inv*(d-x-w*i)-v*(j-l-k*i), ?_⟩
  linear_combination inv*(hd-offset-i*slope) - (j-l-k*i)*inverse

/-- Triangular basis valid also when only part of the modulus divides
the height derivative. Write h=gq and the derivative as gβ. After
choosing the first digits i₀,j₀, the two modular inverses and k determine
every lift. The physical horizontal/vertical strides are hg and hq. -/
theorem tangent_basis {α β c g q i j i₀ j₀ k u v e f w x : ℤ} (gn : g≠0)
    (ia : α*u=1+g*e) (ib : β*v=1+q*f)
    (base : c+α*i₀+g*β*j₀=g*q*w) (slope : α+β*k=q*x) :
    g*q ∣ c+α*i+g*β*j ↔
      ∃ n m : ℤ, i=i₀+g*n ∧ j=j₀+k*n+q*m := by
  constructor
  · rintro ⟨d,hd⟩
    let n := u*(q*(d-w)-β*(j-j₀))-e*(i-i₀)
    have ni : i-i₀=g*n := by
      dsimp [n]
      linear_combination u*(hd-base)-(i-i₀)*ia
    have next : α*n+β*(j-j₀)=q*(d-w) := by
      apply mul_left_cancel₀ gn
      linear_combination hd-base-α*ni
    refine ⟨n,v*(d-w-n*x)-f*(j-j₀-k*n),by linarith only [ni],?_⟩
    linear_combination v*(next-n*slope)-(j-j₀-k*n)*ib
  · rintro ⟨n,m,rfl,rfl⟩
    refine ⟨w+x*n+β*m,?_⟩
    linear_combination base+g*n*slope

/-- For h=gq, the doubled area of any triangle in this more general
triangular lattice is again a multiple of h³. -/
theorem basis_determinant {g q k i₁ i₂ j₁ j₂ : ℤ} :
    ((g*q)*g*i₁)*((g*q)*k*i₂+(g*q)*q*j₂)-
      ((g*q)*g*i₂)*((g*q)*k*i₁+(g*q)*q*j₁) =
      (g*q)^3*(i₁*j₂-i₂*j₁) := by ring

/-- With ordinary width W and class width ⌊W/g⌋, physical block starts
are at least h(W−h+1) apart. -/
theorem stride_lower {h W g : ℕ} (gp : 0<g) (gh : g≤h) (hw : h≤W) :
    h*(W-h+1) ≤ h*g*(W/g) := by
  rw [mul_assoc]
  apply Nat.mul_le_mul_left
  have hdiv := Nat.mod_add_div W g
  have hmod := Nat.mod_lt W gp
  omega

/-- A finite upper bound on blocks in all classes. It needs only their
cardinality and the smallest possible stride, without enumerating
each residue or any block of a full-size conic. -/
theorem block_count_bound {ι : Type*} (classes : Finset ι)
    (start stride blocks : ι → ℕ) {X step : ℕ} (positive : 0<step)
    (sp : ∀ v ∈ classes, 0<start v) (st : ∀ v ∈ classes, step≤stride v)
    (last : ∀ v ∈ classes, blocks v ≠ 0 →
      start v + (blocks v-1)*stride v ≤ X) :
    ∑ v ∈ classes, blocks v ≤ classes.card*((X-1)/step+1) := by
  calc
    _ ≤ ∑ _v ∈ classes, ((X-1)/step+1) := by
      apply Finset.sum_le_sum
      intro v hv
      by_cases empty : blocks v=0
      · simp [empty]
      have tail := last v hv empty
      have small := Nat.mul_le_mul_left (blocks v-1) (st v hv)
      have head := sp v hv
      have cap : (blocks v-1)*step ≤ X-1 := by omega
      have div := (Nat.le_div_iff_mul_le positive).mpr cap
      omega
    _ = _ := by simp

/-- The transformed hyperbola still has a bounded intercept strip. Here
gq=h, the physical span is g²q·w and the ratio of horizontal to height
stride is g/q. The slope-gap premise is the physical rounded-gap bound
multiplied by g. Both shear terms cancel from the slope difference. -/
theorem transformed_gap {a b u g q den w W eps gap : ℝ} (ap : 0≤a) (bp : 0<b)
    (up : 0<u) (gp : 0<g) (qp : 0<q) (wp : 0≤w) (dp : 0≤den)
    (wW : w≤W) (dW : den≤W) (ep : 0≤eps) (guard : g≤q*u)
    (radius : 8*a*(g*W)^3≤b*u) (precision : 4*a*eps*W^2 ≤ 1)
    (physical : b*u*(q*gap) ≤ 2*a*g^3*q*w+4*b*a*g*eps) :
    den*gap*w ≤ 5/4 := by
  have ww := mul_le_mul dW wW wp (wp.trans wW)
  have cube := mul_le_mul ww wW wp (mul_self_nonneg W)
  have geom : 8*a*g^3*(den*w*w) ≤ b*u := calc
    _ ≤ 8*a*g^3*(W*W*W) := mul_le_mul_of_nonneg_left cube (by positivity)
    _ = 8*a*(g*W)^3 := by ring
    _ ≤ _ := radius
  have bill : 4*a*eps*(den*w) ≤ 1 := by
    apply le_trans _ precision
    simpa only [pow_two] using mul_le_mul_of_nonneg_left ww (by positivity : 0≤4*a*eps)
  apply le_of_mul_le_mul_left _ (mul_pos (mul_pos bp up) qp)
  linarith only [mul_le_mul_of_nonneg_right physical (mul_nonneg dp wp),
    mul_le_mul_of_nonneg_right geom qp.le,
    mul_le_mul_of_nonneg_left bill (mul_nonneg bp.le gp.le),
    mul_le_mul_of_nonneg_left guard bp.le]

/-- Every triangle formed by three points in the same tangent lattice
has doubled area divisible by h³. The shear k has no effect. -/
theorem determinant {h k i₁ i₂ j₁ j₂ : ℤ} :
    (h*i₁)*(h*k*i₂+h^2*j₂)-(h*i₂)*(h*k*i₁+h^2*j₁) =
      h^3*(i₁*j₂-i₂*j₁) := by ring

/-- When the tangent is vertical modulo a prime, the coordinate stride
is h² in the horizontal direction and h in the height direction. -/
theorem vertical_determinant {h i₁ i₂ j₁ j₂ : ℤ} :
    (h^2*i₁)*(h*j₂)-(h^2*i₂)*(h*j₁) = h^3*(i₁*j₂-i₂*j₁) := by ring

end PrimeFactors.ConicTangentLattice
