import PrimeFactors.UpperConvergentAgreement

/-! The open interval between a fraction and the mediant with either neighboring parent
lies in its ordinary continued-fraction cylinder. All inputs here are nonnegative rationals. -/
namespace PrimeFactors.FareyParentSufficient

private def Neighbors (a b c d : ℕ) := a*d=b*c+1 ∨ b*c=a*d+1

private theorem peel {a b c d : ℕ} (nb : Neighbors a b c d) (hb : 1<b) (db : d≤b) :
    ∃ r h, a=(a/b)*b+r ∧ c=(a/b)*d+h ∧ 0<r ∧ r<b ∧
      h≤d ∧ h≤r ∧ Neighbors b r d h := by
  let q := a/b
  let r := a%b
  have aq : a=q*b+r := by
    simpa only [q,r,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div a b).symm
  have rb : r<b := Nat.mod_lt _ (by omega)
  have ab : q*b≤a := by omega
  have dp : 0<d := by
    apply lt_of_not_ge
    intro bad
    have dz : d=0 := by omega
    subst d
    rcases nb with n|n <;> simp only [Nat.mul_zero] at n
    · omega
    · have divides : b ∣ 1 := ⟨c,n.symm⟩
      exact (by have := Nat.dvd_one.mp divides; omega)
  have lower : q*d ≤ c := by
    apply le_of_not_gt
    intro lt
    have bound := Nat.mul_le_mul_left b (show c+1≤q*d by omega)
    have bound' := Nat.mul_le_mul_right d ab
    rcases nb with hn|hn <;> nlinarith only [hn,bound,bound',hb]
  let h := c-q*d
  have cq : c=q*d+h := by dsimp [h]; omega
  have child : Neighbors b r d h := by
    rcases nb with hn|hn
    · right
      rw [aq,cq] at hn
      nlinarith only [hn]
    · left
      rw [aq,cq] at hn
      nlinarith only [hn]
  have rp : 0<r := by
    apply lt_of_not_ge
    intro bad
    have rz : r=0 := by omega
    rcases child with n|n <;> rw [rz,Nat.zero_mul] at n
    · have divides : b ∣ 1 := ⟨h,n.symm⟩
      have := Nat.dvd_one.mp divides
      omega
    · omega
  have hle : h≤d := by
    apply le_of_not_gt
    intro lt
    have L := Nat.mul_le_mul_left b (show d+1≤h by omega)
    have R := Nat.mul_le_mul_right d (show r+1≤b by omega)
    rcases child with hn|hn <;> nlinarith only [L,R,hn,hb,dp]
  have hlr : h≤r := by
    apply le_of_not_gt
    intro lt
    have L := Nat.mul_le_mul_left b (show r+1≤h by omega)
    have R := Nat.mul_le_mul_right r db
    rcases child with hn|hn <;> nlinarith only [L,R,hn,hb]
  exact ⟨r,h,aq,cq,rp,rb,hle,hlr,child⟩

private theorem lift_digit {A B q r : ℕ} (decomp : A=q*B+r) (rp : 0<r) (rb : r<B)
    {t : ℚ} (present : ∃ i, t=((B:ℝ)/r).convergent i) :
    ∃ i, (q:ℚ)+t⁻¹=((A:ℝ)/B).convergent i := by
  have bp : (0:ℝ)<B := by exact_mod_cast rp.trans rb
  have remLo : (0:ℝ)<(r:ℝ)/B := div_pos (by exact_mod_cast rp) bp
  have remHi : (r:ℝ)/B<1 := (div_lt_one bp).mpr (by exact_mod_cast rb)
  have equality : (A:ℝ)/B=q+(r:ℝ)/B := by
    rw [decomp,Nat.cast_add,Nat.cast_mul,add_div,mul_div_cancel_right₀ _ bp.ne']
  have fl : ⌊(A:ℝ)/B⌋=(q:ℤ) := by
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_natCast]
    constructor <;> linarith
  have tail : (Int.fract ((A:ℝ)/B))⁻¹=(B:ℝ)/r := by
    rw [Int.fract,fl,Int.cast_natCast,equality,add_sub_cancel_left,inv_div]
  obtain ⟨i,hi⟩ := present
  exact ⟨i+1,by rw [Real.convergent_succ,fl,Int.cast_natCast,tail,hi]⟩

/-- In the positive unimodular bracket with endpoints a/b and c/d, the first endpoint is an
ordinary convergent whenever its mixture coefficient m strictly exceeds the other coefficient n. -/
theorem mixture {a b c d m n : ℕ} (bp : 0<b) (db : d≤b)
    (near : a*d=b*c+1 ∨ b*c=a*d+1) (np : 0<n) (closer : n<m) :
    ∃ i, (a:ℚ)/b=(((m*a+n*c:ℕ):ℝ)/(m*b+n*d:ℕ)).convergent i := by
  induction b using Nat.strong_induction_on generalizing a c d with
  | h b ih =>
    by_cases base : b=1
    · subst b
      have mp : 0<m := np.trans closer
      have mr : (0:ℝ)<m := by exact_mod_cast mp
      have nr : (0:ℝ)<n := by exact_mod_cast np
      have mn : (n:ℝ)<m := by exact_mod_cast closer
      by_cases dz : d=0
      · subst d
        have co : c=1 := by rcases near with h|h <;> simp_all
        subst c
        refine ⟨0,?_⟩
        have eq : ((m*a+n*1:ℕ):ℝ)/(m*1+n*0:ℕ)=(a:ℝ)+n/m := by
          push_cast
          field_simp
          ring
        have lo : (0:ℝ)≤n/m := by positivity
        have hi : (n:ℝ)/m<1 := (div_lt_one mr).mpr mn
        have fl : ⌊(a:ℝ)+n/m⌋=(a:ℤ) := by
          apply Int.floor_eq_iff.mpr
          simp only [Int.cast_natCast]
          constructor <;> linarith
        rw [eq,Real.convergent_zero,fl,Int.cast_natCast,Nat.cast_one,div_one]
      · have do' : d=1 := by omega
        subst d
        simp only [Nat.mul_one,Nat.one_mul] at near ⊢
        rw [Nat.cast_one,div_one]
        apply Real.exists_rat_eq_convergent
        simp only [Rat.den_natCast,Nat.cast_one,one_pow,mul_one,Rat.cast_natCast]
        have error : |((m*a+n*c:ℕ):ℝ)/(m+n:ℕ)-(a:ℝ)|=(n:ℝ)/(m+n) := by
          push_cast
          rw [div_sub' (by positivity),abs_div,abs_of_pos (by positivity : (0:ℝ)<m+n)]
          congr 1
          rcases near with hn|hn
          · rw [hn,Nat.cast_add,Nat.cast_one,show (m:ℝ)*(c+1)+n*c-(m+n)*(c+1) = -n by ring,
              abs_neg,abs_of_pos nr]
          · rw [hn,Nat.cast_add,Nat.cast_one,show (m:ℝ)*a+n*(a+1)-(m+n)*a = n by ring,
              abs_of_pos nr]
        rw [error,div_lt_div_iff₀ (by positivity) (by norm_num)]
        linarith
    · obtain ⟨r,h,aq,cq,rp,rb,hd,hr,child⟩ := peel near (by omega) db
      let q := a/b
      have lifted := lift_digit (q:=q) (A:=m*a+n*c) (B:=m*b+n*d) (r:=m*r+n*h)
        (by dsimp only [q]; calc
            m*a+n*c=m*(a/b*b+r)+n*(a/b*d+h) := congrArg₂ (fun x y : ℕ => m*x+n*y) aq cq
            _ = _ := by ring)
        (by have := Nat.mul_pos (np.trans closer) rp; omega)
        (by have lo := Nat.mul_lt_mul_of_pos_left rb (np.trans closer)
            have hi := Nat.mul_le_mul_left n hd
            omega)
        (ih r rb rp hr child)
      obtain ⟨i,hi⟩ := lifted
      refine ⟨i,Eq.trans ?_ hi⟩
      change (a:ℚ)/b = q+((b:ℚ)/r)⁻¹
      rw [inv_div]
      field_simp
      exact_mod_cast aq

/-- An upper neighbor is reached strictly beyond its mediant with the left parent.
The cross deficit is integral and can be tested without division. -/
theorem upper {E N a b c d : ℕ} (bp : 0<b) (db : d≤b)
    (det : a*d=b*c+1) (above : E*b<N*a)
    (open_interval : (N*a-E*b)*(b+d)<N) :
    ∃ i, (a:ℚ)/b=((E:ℝ)/N).convergent i := by
  let n := N*a-E*b
  have np : 0<n := Nat.sub_pos_of_lt above
  have diff : E*b+n=N*a := by dsimp [n]; omega
  have id : b*(E*d)+n*d=N+b*(N*c) := by
    nlinarith only [congrArg (fun z => z*d) diff,congrArg (fun z => N*z) det]
  have nd : n*d<N := by
    change n*(b+d)<N at open_interval
    exact (Nat.mul_le_mul_left n (by omega : d≤b+d)).trans_lt open_interval
  have larger : N*c<E*d := by
    apply lt_of_not_ge
    intro bad
    have h := Nat.mul_le_mul_left b bad
    omega
  let m := E*d-N*c
  have md : m+N*c=E*d := Nat.sub_add_cancel larger.le
  have den : m*b+n*d=N := by
    nlinarith only [congrArg (fun z => b*z) md,id]
  have num : m*a+n*c=E := by
    apply Nat.eq_of_mul_eq_mul_right bp (m:=_) (k:=_)
    change (m*a+n*c)*b=E*b
    nlinarith only [congrArg (fun z => z*a) den,congrArg (fun z => n*z) det,diff]
  have nm : n<m := by
    apply (Nat.mul_lt_mul_right bp).mp
    change n*(b+d)<N at open_interval
    nlinarith only [open_interval,den]
  have hit := mixture bp db (Or.inl det) np nm
  rwa [num,den] at hit

/-- Direct totient-ratio form. The fraction is supplied by its cross multiplication, so the
criterion also applies to any positive F<N of interest. -/
theorem sufficient {N E F a b c d : ℕ} (ep : 0<E) (fp : 0<F) (fn : F<N)
    (bp : 0<b) (db : d≤b) (eq : a*F=E*b) (det : a*d=b*c+1)
    (strict : (a*(N-F))*(b+d)<N) : ∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i := by
  have ap : 0<a := by
    have h := Nat.mul_pos ep bp
    rw [←eq] at h
    exact (Nat.pos_of_mul_pos_right h)
  have above : E*b<N*a := by
    rw [←eq,Nat.mul_comm N]
    exact Nat.mul_lt_mul_of_pos_left fn ap
  have diff : N*a-E*b=a*(N-F) := by rw [←eq,Nat.mul_comm N,Nat.mul_sub]
  obtain ⟨i,hi⟩ := upper bp db det above (diff ▸ strict)
  refine ⟨i,?_⟩
  apply Eq.trans _ hi
  exact (div_eq_div_iff (by positivity) (by positivity)).mpr (by exact_mod_cast eq.symm)

/-- The positive representative of the inverse of a modulo b. For an integer target the
left parent is the preceding integer, with denominator one. -/
noncomputable def parentDen (a b : ℕ) : ℕ := if b=1 then 1 else ((a:ZMod b)⁻¹).val

theorem parent_spec {a b : ℕ} (ap : 0<a) (bp : 0<b) (cop : a.Coprime b) :
    let d := parentDen a b
    0<d ∧ d≤b ∧ a*d=b*((a*d-1)/b)+1 := by
  by_cases bo : b=1
  · subst b
    simp [parentDen,Nat.sub_add_cancel ap]
  have big : 1<b := by omega
  letI : NeZero b := ⟨bp.ne'⟩
  let d := ((a:ZMod b)⁻¹).val
  have md : a*d % b=1 := by
    calc
      _ = 1 % b := (ZMod.natCast_eq_natCast_iff' _ _ _).mp (by
        rw [Nat.cast_mul,Nat.cast_one]
        change (a:ZMod b)*(((a:ZMod b)⁻¹).val:ℕ)=1
        rw [ZMod.natCast_zmod_val,ZMod.coe_mul_inv_eq_one a cop])
      _ = _ := Nat.mod_eq_of_lt big
  have dp : 0<d := by
    apply Nat.pos_of_ne_zero
    intro dz
    simp [dz] at md
  have db : d<b := ZMod.val_lt _
  have eq := Nat.mod_add_div (a*d) b
  rw [md] at eq
  have div : (a*d-1)/b=(a*d)/b := by
    have eq' : a*d-1=b*((a*d)/b) := by omega
    rw [eq',Nat.mul_div_cancel_left _ bp]
  simpa only [parentDen,if_neg bo] using
    (show 0<d ∧ d≤b ∧ a*d=b*((a*d-1)/b)+1 from ⟨dp,db.le,by rw [div]; omega⟩)

end PrimeFactors.FareyParentSufficient
