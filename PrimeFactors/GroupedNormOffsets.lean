import PrimeFactors.GroupedNormFactors
import Mathlib.Data.Nat.ModEq

namespace PrimeFactors.GroupedNormOffsets

/-- The public choice at offset j and the squared difference subsequently tested. -/
def multiplier (T h j : ℕ) : ℕ := (j*T-1)/h

def discriminant (T h j k : ℕ) : ℕ := j^2+4*k*(j*T-h*k)

theorem selected {T h j k z : ℕ} (decomp : j*T=z+h*k) (pos : 0<z) (cap : z≤h) :
    multiplier T h j=k := GroupedNormFactors.top_multiplier decomp pos cap

/-- Every integer square hit has the required parity and yields m without search. -/
theorem of_square {x j k z : ℕ} (sq : x^2=j^2+4*k*z) :
    ∃ m : ℕ, x=j+2*m ∧ m*(m+j)=k*z := by
  have ge : j≤x := by nlinarith only [sq,Nat.zero_le (k*z),sq_nonneg ((j:ℤ)-(x:ℤ))]
  have parity (v : ℕ) : v^2%2=v%2 := by
    rw [pow_two,Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one v with h|h <;> rw [h]
  have eq : x%2=j%2 := by
    rw [← parity x, ← parity j, sq,show 4*k*z=2*(2*k*z) by ring]
    omega
  let m := (x-j)/2
  have hx : x=j+2*m := by dsimp [m]; omega
  exact ⟨m,hx,by rw [hx] at sq; nlinarith only [sq]⟩

/-- Dividing both j and k by the same positive factor retains selection and
divides the squared difference by its square. -/
theorem reduced {g T h j k : ℕ} (gp : 0<g) (inside : h*(g*k)<(g*j)*T)
    (cap : (g*j)*T-h*(g*k)≤h) :
    multiplier T h j=k ∧ discriminant T h (g*j) (g*k)=g^2*discriminant T h j k := by
  have orig : h*k<j*T := by
    apply Nat.lt_of_mul_lt_mul_left (a:=g)
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using inside
  have rem : (g*j)*T-h*(g*k)=g*(j*T-h*k) := by rw [Nat.mul_sub]; congr 1 <;> ring
  rw [rem] at cap
  refine ⟨selected (Nat.sub_add_cancel orig.le).symm (Nat.sub_pos_of_lt orig)
    ((Nat.le_mul_of_pos_left _ gp).trans cap), ?_⟩
  simp only [discriminant,rem]
  ring

theorem square_scale {g d : ℕ} (gp : 0<g) :
    (∃ x : ℕ, x^2=g^2*d) ↔ ∃ x : ℕ, x^2=d := by
  constructor
  · rintro ⟨x,h⟩
    obtain ⟨v,rfl⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp (show g^2 ∣ x^2 from ⟨_,h⟩)
    rw [mul_pow] at h
    exact ⟨v,Nat.eq_of_mul_eq_mul_left (pow_pos gp 2) h⟩
  · rintro ⟨x,rfl⟩
    exact ⟨g*x,by ring⟩

theorem scaled_gcd {N g k T m : ℕ} (cop : g.Coprime N) :
    N.gcd ((g*k)*T-g*m)=N.gcd (k*T-m) := by
  rw [Nat.mul_assoc,← Nat.mul_sub]
  exact Nat.Coprime.gcd_mul_left_cancel_right _ cop

/-- The same gcd allocation of k works at any positive determinant. -/
theorem witness_of_hit {T h k m j z : ℕ} (jp : 0<j) (kp : 0<k) (zp : 0<z)
    (decomp : j*T=z+h*k) (hit : m*(m+j)=k*z) :
    ∃ a b u v : ℕ, 0<a ∧ 0<b ∧ 0<u ∧ 0<v ∧ a*v=b*u+j ∧ a*b=k ∧
      u*v=z ∧ (u^2+h*a^2)*(v^2+h*b^2)=j^2*(T^2+h) := by
  let b := k.gcd m
  let a := k/b
  let u := m/b
  let v := (m+j)/a
  have bp : 0<b := Nat.gcd_pos_of_pos_left _ kp
  have ab : a*b=k := Nat.div_mul_cancel (Nat.gcd_dvd_left k m)
  have bu : b*u=m := Nat.mul_div_cancel' (Nat.gcd_dvd_right k m)
  have ap : 0<a := Nat.pos_of_mul_pos_right (ab ▸ kp : 0<a*b)
  have mp : 0<m := Nat.pos_of_mul_pos_right (hit ▸ Nat.mul_pos kp zp : 0<m*(m+j))
  have up : 0<u := Nat.pos_of_mul_pos_left (bu ▸ mp : 0<b*u)
  have cop : a.Coprime u := Nat.coprime_div_gcd_div_gcd bp
  have cancel : u*(m+j)=a*z := by
    apply Nat.eq_of_mul_eq_mul_left bp
    calc b*(u*(m+j)) = m*(m+j) := by rw [← Nat.mul_assoc,bu]
         _ = k*z := hit
         _ = b*(a*z) := by rw [← ab]; ring
  have adv : a ∣ m+j := cop.dvd_of_dvd_mul_left ⟨_,cancel⟩
  have av : a*v=m+j := Nat.mul_div_cancel' adv
  have vp : 0<v := Nat.pos_of_mul_pos_left (av ▸ (by omega) : 0<a*v)
  have uv : u*v=z := by
    apply Nat.eq_of_mul_eq_mul_left ap
    calc a*(u*v) = u*(a*v) := by ring
         _ = _ := by rw [av,cancel]
  have det : a*v=b*u+j := by rw [av,bu]
  refine ⟨a,b,u,v,ap,bp,up,vp,det,ab,uv,?_⟩
  have sq : (a*v)^2+(b*u)^2=2*(a*v)*(b*u)+j^2 := by rw [det]; ring
  have prodEq : (u^2+h*a^2)*(v^2+h*b^2)=(u*v+h*(a*b))^2+h*j^2 := by
    nlinarith only [congrArg (fun x => h*x) sq]
  rw [prodEq,ab,uv,← decomp]; ring

theorem hit_of_witness {a b u v j : ℕ} (det : a*v=b*u+j) :
    (b*u)*(b*u+j)=(a*b)*(u*v) := by rw [← det]; ring

/-- At the top multiplier, j≤h suffices to force a proper divisor by the
lower signed gcd. The condition uses only the public offset. -/
theorem gcd_split {T h k m j z : ℕ} (jp : 0<j) (jh : j≤h) (kp : 0<k) (zp : 0<z)
    (cap : z≤h) (decomp : j*T=z+h*k) (hit : m*(m+j)=k*z) :
    let N := T^2+h
    let d := N.gcd (k*T-m)
    1<d ∧ d<N ∧ d ∣ N := by
  let N := T^2+h
  let A := k*T-m
  let B := k*T+m+j
  change 1<N.gcd A ∧ N.gcd A<N ∧ N.gcd A ∣ N
  have kt : k<T := by
    by_contra! bad
    have := Nat.mul_le_mul jh bad
    omega
  have mt : m<T := by
    have bound := Nat.mul_le_mul_left k cap
    have mj : m*j ≤ m*(m+j) := Nat.mul_le_mul_left m (by omega)
    have h : m*j<j*T := by nlinarith only [decomp,zp,hit,bound,mj]
    exact Nat.lt_of_mul_lt_mul_right (by simpa only [Nat.mul_comm j T] using h)
  have ma := mt.trans_le (Nat.le_mul_of_pos_left T kp)
  have ap : 0<A := Nat.sub_pos_of_lt ma
  have bp : 0<B := by dsimp [B]; omega
  have bl : B<N := by
    have enough := Nat.mul_le_mul_right T (show k+1≤T by omega)
    dsimp [B,N]
    nlinarith only [enough,mt,jh]
  have al : A<N := (Nat.sub_le _ _).trans_lt (show k*T<N by dsimp [B] at bl; omega)
  have same : A*B=k^2*N := by
    have ea : A+m=k*T := Nat.sub_add_cancel ma.le
    dsimp [B,N]
    zify at ea hit decomp ⊢
    linear_combination ((k:ℤ)*T+m+j)*ea-hit+(k:ℤ)*decomp
  have div : N ∣ A*B := ⟨k^2,by rw [same,mul_comm]⟩
  refine ⟨?_,(Nat.le_of_dvd ap (Nat.gcd_dvd_right N A)).trans_lt al,Nat.gcd_dvd_left ..⟩
  have pos := Nat.gcd_pos_of_pos_right N ap
  by_contra! small
  have cop : N.Coprime A := show N.gcd A=1 by omega
  exact Nat.not_dvd_of_pos_of_lt bp bl (cop.dvd_of_dvd_mul_left div)

/-- The numerical square test on an explicit family whose first hit occurs at 13. -/
def familyProduct (r : ℕ) := (9*r+1)*(16*r+5)

private def shape (r j : ℕ) := j^2+4*(j-1)*(j+1+(13-j)*r)

theorem family_window (r : ℕ) (rp : 0<r) :
    (familyProduct r).sqrt=12*r+2 ∧ familyProduct r-(12*r+2)^2=13*r+1 := by
  have eq : familyProduct r=(12*r+2)^2+(13*r+1) := by unfold familyProduct; ring
  rw [eq]
  exact ⟨(Nat.eq_sqrt.mpr ⟨by nlinarith,by nlinarith⟩).symm, by omega⟩

private theorem family_lanes {r j : ℕ} (rp : 0<r) (jp : 0<j) (cap : j≤13) :
    multiplier (12*r+2) (13*r+1) j=j-1 ∧
    discriminant (12*r+2) (13*r+1) j (j-1)=shape r j := by
  let z := j+1+(13-j)*r
  have e₁ := Nat.sub_add_cancel cap
  have e₂ := Nat.sub_add_cancel (show 1≤j by omega)
  have e : j*(12*r+2)=z+(13*r+1)*(j-1) := by
    dsimp [z]
    nlinarith only [e₂,congrArg (fun t => t*r) e₁,congrArg (fun t => t*r) e₂]
  have zcap : z≤13*r+1 := by
    have := Nat.le_mul_of_pos_right j rp
    dsimp [z]; nlinarith only [this,congrArg (fun t => t*r) e₁]
  have zpos : 0<z := by dsimp [z]; omega
  have diff : j*(12*r+2)-(13*r+1)*(j-1)=z := by omega
  exact ⟨selected e zpos zcap,by simp only [discriminant,shape,diff,z]⟩

private theorem failed_residues : ∀ j ∈ List.range 13, 2≤j → ∀ x ∈ List.range 77,
    shape 58 j%77 ≠ x^2%77 := by decide +kernel

/-- Every eligible offset in 1..12 fails on this entire progression. The
first offset has no multiplier at all, so its formal zero is excluded. -/
theorem family_misses {r j : ℕ} (pr : r ≡ 58 [MOD 77]) (jp : 0<j) (small : j<13)
    (eligible : 0<multiplier (12*r+2) (13*r+1) j) :
    ¬∃ x : ℕ, x^2=discriminant (12*r+2) (13*r+1) j (multiplier (12*r+2) (13*r+1) j) := by
  have rp : 0<r := by change r%77=58%77 at pr; omega
  obtain ⟨chosen,eq⟩ := family_lanes rp jp small.le
  rw [chosen] at eligible ⊢
  rw [eq]
  rintro ⟨x,hit⟩
  have modEq : shape r j ≡ shape 58 j [MOD 77] := (Nat.ModEq.refl _).add
    (((Nat.ModEq.refl _).add (pr.mul_left (13-j))).mul_left (4*(j-1)))
  have xmod := (Nat.mod_modEq x 77).pow 2
  exact failed_residues j (List.mem_range.mpr small) (by omega) (x%77)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide))) (xmod.trans (hit ▸ modEq)).symm

/-- Offset 13 recovers the displayed factor with a single square root and gcd. -/
theorem family_hit {r : ℕ} (rp : 0<r) :
    multiplier (12*r+2) (13*r+1) 13=12 ∧
    discriminant (12*r+2) (13*r+1) 13 12=29^2 ∧
    (familyProduct r).gcd (12*(12*r+2)-8)=9*r+1 := by
  have h := family_lanes rp (by decide : 0<13) (by decide : 13≤13)
  refine ⟨h.1,h.2.trans (by simp [shape]),?_⟩
  change ((9*r+1)*(16*r+5)).gcd _=_
  have key : 12*(12*r+2)-8=(9*r+1)*16 := by omega
  rw [key,Nat.gcd_mul_left]
  have cop : (16*r+5).gcd 16=1 := by
    rw [Nat.gcd_comm,Nat.gcd_rec]
    simp
  rw [cop,mul_one]

theorem offset_13_example : familyProduct 674=65456863 ∧ 674 ≡ 58 [MOD 77] ∧
    Nat.Prime (9*674+1) ∧ Nat.Prime (16*674+5) := by
  refine ⟨by decide,by decide,?_,?_⟩ <;> norm_num1

theorem equal_width_example : familyProduct 4062=2376225323 ∧ 4062 ≡ 58 [MOD 77] ∧
    Nat.Prime (9*4062+1) ∧ Nat.Prime (16*4062+5) := by
  refine ⟨by decide,by decide,?_,?_⟩ <;> norm_num1

end PrimeFactors.GroupedNormOffsets
