import PrimeFactors.GroupedNormFrequency

namespace PrimeFactors.OffsetSweepFrequency

/-- A raw square hit, including the endpoint with m=0. -/
def Hit (T h k j m : ℕ) : Prop := m*(m+j)+h*k^2=k*T*j

/-- On the eligible interval, the raw discriminant square is exactly the
additive hit relation. The parity of the square root is forced. -/
theorem discriminant_square_iff {T h k j : ℕ} (room : h*k≤T*j) :
    (∃ x : ℕ, x^2=j^2+4*k*(T*j-h*k)) ↔ ∃ m, Hit T h k j m := by
  have dec := Nat.sub_add_cancel room
  constructor
  · rintro ⟨x,eq⟩
    have small : j≤x := le_of_not_gt (fun gt =>
      (not_le_of_gt (Nat.pow_lt_pow_left gt (by decide : 2≠0))) (by omega : j^2≤x^2))
    have mod : x^2%2=j^2%2 := by
      rw [eq,show 4*k*(T*j-h*k)=2*(2*k*(T*j-h*k)) by ring,Nat.add_mul_mod_self_left]
    have parity : x%2=j%2 := by
      rw [pow_two,pow_two,Nat.mul_mod x x,Nat.mul_mod j j] at mod
      rcases (show x%2=0 ∨ x%2=1 by omega) with a|a <;>
        rcases (show j%2=0 ∨ j%2=1 by omega) with b|b <;> simp_all
    let m := (x-j)/2
    have split : x=2*m+j := by dsimp [m];omega
    refine ⟨m,?_⟩
    dsimp [Hit]
    rw [split] at eq
    nlinarith only [eq,congrArg (fun z => k*z) dec]
  · rintro ⟨m,hit⟩
    exact ⟨2*m+j,by dsimp [Hit] at hit; nlinarith only [hit,congrArg (fun z => k*z) dec]⟩

/-- Every hit has a representative with coprime multiplier and offset.
Factors of either m or m+j may repeat. -/
theorem primitive {T h k j m : ℕ} (kp : 0<k) (jp : 0<j) (hit : Hit T h k j m) :
    ∃ K J M, 0<K ∧ 0<J ∧ J≤j ∧ K.Coprime J ∧ Hit T h K J M := by
  induction j using Nat.strong_induction_on generalizing k m with
  | h j ih =>
    by_cases cop : k.Coprime j
    · exact ⟨k,j,m,kp,jp,le_rfl,cop,hit⟩
    obtain ⟨p,prime,⟨K,rfl⟩,⟨J,rfl⟩⟩ := Nat.Prime.not_coprime_iff_dvd.mp cop
    have mult : p ∣ m*(m+p*J) := by
      apply (Nat.dvd_add_iff_left (show p ∣ h*(p*K)^2 by exact ⟨h*p*K^2,by ring⟩)).mpr
      exact hit ▸ ⟨K*T*(p*J),by ring⟩
    have md : p ∣ m := (prime.dvd_mul.mp mult).elim id
      (fun d => (Nat.dvd_add_iff_left (dvd_mul_right p J)).mpr d)
    obtain ⟨M,rfl⟩ := md
    have ppos := prime.pos
    have jpos : 0<J := Nat.pos_of_mul_pos_left jp
    have kpos : 0<K := Nat.pos_of_mul_pos_left kp
    have smaller : J<p*J := by
      have := Nat.mul_le_mul_right J prime.two_le
      omega
    have reduced : Hit T h K J M := by
      apply Nat.eq_of_mul_eq_mul_left (n:=p^2) (pow_pos ppos 2)
      dsimp [Hit] at hit ⊢
      nlinarith only [hit]
    obtain ⟨k',j',m',hk,hj,le,unit,eq⟩ := ih J smaller kpos jpos reduced
    exact ⟨k',j',m',hk,hj,le.trans smaller.le,unit,eq⟩

/-- The multiplier's gcd with m determines a single residue class of roots
when the offset and multiplier are coprime. -/
private theorem root_residue {k j m : ℕ} (kp : 0<k) (unit : k.Coprime j)
    (root : k ∣ m*(m+j)) :
    let b := k.gcd m
    let a := k/b
    a.Coprime b ∧ a ∣ m+j ∧ b ∣ m ∧ a*b=k := by
  let b := k.gcd m
  let a := k/b
  let u := m/b
  have bp : 0<b := Nat.gcd_pos_of_pos_left _ kp
  have ab : a*b=k := Nat.div_mul_cancel (Nat.gcd_dvd_left k m)
  have bu : b*u=m := Nat.mul_div_cancel' (Nat.gcd_dvd_right k m)
  have au : a.Coprime u := Nat.coprime_div_gcd_div_gcd bp
  obtain ⟨v,eq⟩ := root
  have av : a ∣ m+j := au.dvd_of_dvd_mul_left (show a ∣ u*(m+j) from ⟨v,by
    apply Nat.eq_of_mul_eq_mul_left bp
    calc b*(u*(m+j)) = m*(m+j) := by rw [← mul_assoc,bu]
         _ = b*(a*v) := by rw [eq,←ab]; ring⟩)
  have ba : a.Coprime b := by
    by_contra bad
    obtain ⟨p,prime,pa,pb⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    have pm : p ∣ m := pb.trans (Nat.gcd_dvd_right k m)
    have pj : p ∣ j := (Nat.dvd_add_iff_right pm).mpr (pa.trans av)
    exact prime.not_dvd_one (unit ▸ Nat.dvd_gcd (pb.trans (Nat.gcd_dvd_left k m)) pj)
  exact ⟨ba,av,Nat.gcd_dvd_right k m,ab⟩

private theorem equal_of_div_mod {a x y : ℕ} (eq : x ≡ y [MOD a]) (div : x/a=y/a) : x=y := by
  have xr := Nat.mod_add_div x a
  rw [show x%a=y%a from eq,div,Nat.mod_add_div] at xr
  exact xr.symm

private theorem root_unique {k j m n : ℕ} (kp : 0<k) (unit : k.Coprime j)
    (r : k ∣ m*(m+j)) (s : k ∣ n*(n+j)) (g : k.gcd m=k.gcd n) (q : m/k=n/k) :
    m=n := by
  obtain ⟨cop,a1,b1,ab⟩ := root_residue kp unit r
  have t := root_residue kp unit s
  rw [←g] at t
  have aeq := Nat.ModEq.add_right_cancel' j
    ((Nat.modEq_zero_iff_dvd.mpr a1).trans (Nat.modEq_zero_iff_dvd.mpr t.2.1).symm)
  have beq := (Nat.modEq_zero_iff_dvd.mpr b1).trans (Nat.modEq_zero_iff_dvd.mpr t.2.2.1).symm
  apply equal_of_div_mod _ q
  rw [←ab]
  exact Nat.modEq_and_modEq_iff_modEq_mul cop |>.mp ⟨aeq,beq⟩

private theorem hit_remainder {T h k j m : ℕ} (kp : 0<k) (hit : Hit T h k j m) :
    ∃ v, m*(m+j)=k*v ∧ v+h*k=T*j := by
  have bound : h*k ≤ T*j := by
    apply Nat.le_of_mul_le_mul_left (c:=k) _ kp
    dsimp [Hit] at hit
    nlinarith only [hit]
  refine ⟨T*j-h*k, ?_,Nat.sub_add_cancel bound⟩
  have eq := Nat.sub_add_cancel bound
  dsimp [Hit] at hit
  nlinarith only [hit,congrArg (fun x => k*x) eq]

/-- At fixed multiplier, offset and root, either of two small quotient
labels suffices to recover the floor root and square remainder. -/
theorem fiber_unique {T S h g k j m : ℕ} (kp : 0<k) (jp : 0<j) (unit : k.Coprime j)
    (one : Hit T h k j m) (two : Hit S g k j m)
    (label : T/k=S/k ∨ h/j=g/j) : T=S ∧ h=g := by
  obtain ⟨v,vm,ve⟩ := hit_remainder kp one
  obtain ⟨z,zm,ze⟩ := hit_remainder kp two
  have same := Nat.eq_of_mul_eq_mul_left kp (vm.symm.trans zm)
  subst z
  have tmod : T*j ≡ S*j [MOD k] := by simp only [←ve,←ze,Nat.ModEq,mul_comm _ k,Nat.add_mul_mod_self_left]
  have hmod : h*k ≡ g*k [MOD j] := by
    apply Nat.ModEq.add_left_cancel' v
    rw [ve,ze]
    exact (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left j T)).trans
      (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left j S)).symm
  rcases label with t | r
  · have ts := equal_of_div_mod (Nat.ModEq.cancel_right_of_coprime unit tmod) t
    subst S
    exact ⟨rfl,Nat.eq_of_mul_eq_mul_right kp (Nat.add_left_cancel (ve.trans ze.symm))⟩
  · have hg := equal_of_div_mod (Nat.ModEq.cancel_right_of_coprime unit.symm hmod) r
    subst g
    exact ⟨Nat.eq_of_mul_eq_mul_right jp (ve.symm.trans ze),rfl⟩

private structure Witness (S J : ℕ) where
  T : ℕ
  h : ℕ
  k : ℕ
  j : ℕ
  m : ℕ
  small : T<S^2
  remainder : h≤2*T
  hp : 0<h
  kp : 0<k
  jp : 0<j
  js : j≤J
  unit : k.Coprime j
  hit : Hit T h k j m

private noncomputable def high (L k j : ℕ) := (L*j/k).sqrt
private noncomputable def coordinate (T h k j : ℕ) := if k≤j then h/j else T/k

private theorem witness_bounds {S J : ℕ} (w : Witness S J) :
    w.k < S^2*w.j ∧ w.m/w.k ≤ high (S^2) w.k w.j := by
  obtain ⟨v,eq,rep⟩ := hit_remainder w.kp w.hit
  have t := Nat.mul_lt_mul_of_pos_right w.small w.jp
  have k := Nat.le_mul_of_pos_left w.k w.hp
  have vk : v≤w.T*w.j := by omega
  refine ⟨by omega,Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le w.kp).mpr ?_)⟩
  have q := Nat.mul_div_le w.m w.k
  have z : (w.k*(w.m/w.k))^2 ≤ w.m*(w.m+w.j) :=
    (Nat.pow_le_pow_left q 2).trans (by rw [pow_two]; gcongr; omega)
  apply Nat.le_of_mul_le_mul_left (c:=w.k) _ w.kp
  calc w.k*((w.m/w.k)^2*w.k) = (w.k*(w.m/w.k))^2 := by ring
       _ ≤ w.m*(w.m+w.j) := z
       _ = w.k*v := eq
       _ ≤ w.k*(S^2*w.j) := Nat.mul_le_mul_left _ (vk.trans t.le)

private theorem sq_imp {a b : ℕ} (le : a^2≤b^2) : a≤b := by
  exact le_of_not_gt (fun gt => (not_le_of_gt (Nat.pow_lt_pow_left gt (by decide : 2≠0))) le)

/-- Per pair of dyadic bins for the factors of k, the remaining information
fits below 6 S³, independently of the permitted offset j≤S. -/
private theorem capacity {S J : ℕ} (w : Witness S J) (js : J≤S) :
    w.k*(high (S^2) w.k w.j+1)*(coordinate w.T w.h w.k w.j+1) ≤ 6*S^3 := by
  let k := w.k
  let j := w.j
  let z := high (S^2) k j
  let y := coordinate w.T w.h k j
  have jj : j≤S := w.js.trans js
  have sp : 0<S := w.jp.trans_le jj
  have bound : k ≤ S^2*j := (witness_bounds w).1.le
  have zs : z^2*k ≤ S^2*j := (Nat.mul_le_mul_right _ (Nat.sqrt_le' _)).trans (Nat.div_mul_le_self ..)
  change k*(z+1)*(y+1) ≤ _
  by_cases kj : k≤j
  · have kz : k*z≤S*j := sq_imp (calc
      (k*z)^2 = (z^2*k)*k := by ring
      _ ≤ (S^2*j)*j := Nat.mul_le_mul zs kj
      _ = _ := by ring)
    have ky : k*(z+1) ≤ 2*S*j := by
      have basic := kj.trans (Nat.le_mul_of_pos_left j sp)
      nlinarith only [basic,kz]
    have jy : j*(y+1) ≤ 3*S^2 := by
      have rem := w.remainder
      have small := w.small
      have yh : j*y ≤ w.h := by simpa [y,coordinate,kj] using Nat.mul_div_le w.h j
      have jL := jj.trans (by simpa [pow_two] using Nat.le_mul_of_pos_left S sp : S≤S^2)
      nlinarith only [rem,small,yh,jL]
    calc _ ≤ (2*S*j)*(y+1) := Nat.mul_le_mul_right _ ky
         _ = 2*S*(j*(y+1)) := by ring
         _ ≤ 2*S*(3*S^2) := Nat.mul_le_mul_left _ jy
         _ = _ := by ring
  · have jk : j≤k := by omega
    have yz : y=w.T/k := by simp [y,coordinate,kj]
    by_cases kl : k≤S^2
    · have zS : z≤S := sq_imp (Nat.le_of_mul_le_mul_right (c:=k) (zs.trans (Nat.mul_le_mul_left _ jk)) w.kp)
      have ky : k*(y+1) ≤ 2*S^2 := by
        have a := Nat.mul_div_le w.T k
        rw [yz]
        have b := w.small
        nlinarith only [a,b,kl]
      calc _ = k*(y+1)*(z+1) := by ring
           _ ≤ (2*S^2)*(2*S) := Nat.mul_le_mul ky (by omega)
           _ ≤ _ := by nlinarith
    · have zy : y=0 := yz.trans (Nat.div_eq_of_lt (w.small.trans_le (by omega)))
      have kz : k*z ≤ S^2*j := sq_imp (calc
        (k*z)^2 = (z^2*k)*k := by ring
        _ ≤ (S^2*j)*(S^2*j) := Nat.mul_le_mul zs bound
        _ = _ := by ring)
      have upper := Nat.mul_le_mul_left (S^2) jj
      rw [zy,zero_add,mul_one]
      nlinarith only [kz,bound,upper]

private noncomputable def pack (r hi lo : ℕ) := r*hi+lo
private theorem pack_lt {r hi lo : ℕ} (h : lo<r) : pack r hi lo<r*(hi+1) := by
  unfold pack
  rw [Nat.mul_succ]
  omega

private theorem unpack {r i j a b : ℕ} (ha : a<r) (hb : b<r)
    (h : pack r i a=pack r j b) : i=j ∧ a=b := by
  have pos : 0<r := by omega
  have d := congrArg (· / r) h
  have m := congrArg (· % r) h
  simpa [pack,Nat.mul_add_div pos,Nat.mul_add_mod,Nat.div_eq_of_lt ha,Nat.div_eq_of_lt hb,
    Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using And.intro d m

private noncomputable def base (a : ℕ) := 2^(Nat.log 2 a)
private theorem base_lo {a : ℕ} (ap : 0<a) : base a ≤ a := Nat.pow_log_le_self _ ap.ne'
private theorem offset_lt {a : ℕ} (ap : 0<a) : a-base a < base a := by
  have lo := base_lo ap
  have hi := Nat.lt_pow_succ_log_self (by decide : 1<2) a
  rw [pow_succ] at hi
  unfold base at *
  omega

private noncomputable def payload (S a b T h j m : ℕ) :=
  let k := a*b
  pack (base a) (pack (base b)
    (pack (high (S^2) k j+1) (coordinate T h k j) (m/k)) (b-base b)) (a-base a)

private theorem payload_lt {S J : ℕ} (w : Witness S J) {a b : ℕ} (ap : 0<a) (bp : 0<b)
    (ab : a*b=w.k) (js : J≤S) : payload S a b w.T w.h w.j w.m<6*S^3 := by
  let z := high (S^2) w.k w.j
  let y := coordinate w.T w.h w.k w.j
  have inner : pack (z+1) y (w.m/w.k)<(z+1)*(y+1) := pack_lt (Nat.lt_succ_of_le (witness_bounds w).2)
  have middle := pack_lt (hi:=pack (z+1) y (w.m/w.k)) (offset_lt bp)
  have outer := pack_lt (hi:=pack (base b) (pack (z+1) y (w.m/w.k)) (b-base b)) (offset_lt ap)
  unfold payload
  rw [ab]
  calc _ < _ := outer
       _ ≤ base a*(base b*(pack (z+1) y (w.m/w.k)+1)) := Nat.mul_le_mul_left _ middle
       _ ≤ a*(b*((z+1)*(y+1))) := Nat.mul_le_mul (base_lo ap) (Nat.mul_le_mul (base_lo bp) inner)
       _ = w.k*(z+1)*(y+1) := by rw [←ab];ring
       _ ≤ _ := capacity w js

private noncomputable def factors (k m : ℕ) : ℕ × ℕ := (k/(k.gcd m),k.gcd m)

private theorem factors_spec {k m : ℕ} (kp : 0<k) :
    let (a,b) := factors k m
    0<a ∧ 0<b ∧ a*b=k := by
  dsimp only [factors]
  have ab := Nat.div_mul_cancel (Nat.gcd_dvd_left k m)
  exact ⟨Nat.pos_of_mul_pos_right (ab ▸ kp),Nat.gcd_pos_of_pos_left _ kp,ab⟩

private abbrev Code (S J e : ℕ) := Fin J × Fin e × Fin e × Fin (6*S^3)

private noncomputable def code {S J e : ℕ} (w : Witness S J) (fit : S^2*J ≤ 2^e) (js : J≤S) : Code S J e :=
  let a := (factors w.k w.m).1
  let b := (factors w.k w.m).2
  have fs := factors_spec (m:=w.m) w.kp
  have km := (witness_bounds w).1.trans_le ((Nat.mul_le_mul_left _ w.js).trans fit)
  have ab : a*b=w.k := fs.2.2
  have pab : a*b<2^e := ab.trans_lt km
  have al := (Nat.le_mul_of_pos_right a fs.2.1).trans_lt pab
  have bl := (Nat.le_mul_of_pos_left b fs.1).trans_lt pab
  (⟨w.j-1,by have := w.js; have := w.jp;omega⟩,⟨Nat.log 2 a,Nat.log_lt_of_lt_pow fs.1.ne' al⟩,
   ⟨Nat.log 2 b,Nat.log_lt_of_lt_pow fs.2.1.ne' bl⟩,
   ⟨payload S a b w.T w.h w.j w.m,payload_lt w fs.1 fs.2.1 fs.2.2 js⟩)

private theorem payload_unique {S a b c d T h U g j m n : ℕ}
    (ap : 0<a) (bp : 0<b) (cp : 0<c) (dp : 0<d)
    (al : Nat.log 2 a=Nat.log 2 c) (bl : Nat.log 2 b=Nat.log 2 d)
    (rootOne : m/(a*b) ≤ high (S^2) (a*b) j) (rootTwo : n/(c*d) ≤ high (S^2) (c*d) j)
    (eq : payload S a b T h j m=payload S c d U g j n) :
    a=c ∧ b=d ∧ m/(a*b)=n/(c*d) ∧ coordinate T h (a*b) j=coordinate U g (c*d) j := by
  have ac : base a=base c := congrArg (2^·) al
  have bd : base b=base d := congrArg (2^·) bl
  unfold payload at eq
  rw [←ac,←bd] at eq
  have co := offset_lt cp
  have doff := offset_lt dp
  rw [←ac] at co
  rw [←bd] at doff
  obtain ⟨inner,ao⟩ := unpack (offset_lt ap) co eq
  obtain ⟨top,bo⟩ := unpack (offset_lt bp) doff inner
  have la := base_lo ap
  have lb := base_lo bp
  have lc := base_lo cp
  have ld := base_lo dp
  rw [←ac] at lc
  rw [←bd] at ld
  have : a=c := by omega
  subst c
  have : b=d := by omega
  subst d
  obtain ⟨coord,rts⟩ := unpack (Nat.lt_succ_of_le rootOne) (Nat.lt_succ_of_le rootTwo) top
  exact ⟨rfl,rfl,rts,coord⟩

private theorem recover {S J e : ℕ} (w v : Witness S J) (fit : S^2*J ≤ 2^e) (js : J≤S)
    (eq : code w fit js=code v fit js) : w.T^2+w.h=v.T^2+v.h := by
  have je := congrArg (fun c : Code S J e => c.1.val) eq
  have ae := congrArg (fun c : Code S J e => c.2.1.val) eq
  have be := congrArg (fun c : Code S J e => c.2.2.1.val) eq
  have pe := congrArg (fun c : Code S J e => c.2.2.2.val) eq
  change w.j-1=v.j-1 at je
  have j : w.j=v.j := by have := w.jp; have := v.jp;omega
  let f := factors w.k w.m
  let g := factors v.k v.m
  change Nat.log 2 f.1=Nat.log 2 g.1 at ae
  change Nat.log 2 f.2=Nat.log 2 g.2 at be
  change payload S f.1 f.2 w.T w.h w.j w.m=payload S g.1 g.2 v.T v.h v.j v.m at pe
  rw [j] at pe
  have fs := factors_spec (m:=w.m) w.kp
  have gs := factors_spec (m:=v.m) v.kp
  have fe : f.1*f.2=w.k := fs.2.2
  have ge : g.1*g.2=v.k := gs.2.2
  obtain ⟨a,b,m,y⟩ := payload_unique (a:=f.1) (b:=f.2) (c:=g.1) (d:=g.2) fs.1 fs.2.1 gs.1 gs.2.1 ae be
    (by rw [fe,←j]; exact (witness_bounds w).2) (by rw [ge];exact (witness_bounds v).2) pe
  have k : w.k=v.k := by rw [←fe,a,b,ge]
  rw [fe,ge,k] at m y
  change w.k.gcd w.m=v.k.gcd v.m at b
  rw [k] at b
  have one := w.hit
  rw [j,k] at one
  obtain ⟨r,rd,_⟩ := hit_remainder v.kp one
  obtain ⟨s,sd,_⟩ := hit_remainder v.kp v.hit
  have roots := root_unique v.kp v.unit ⟨r,rd⟩ ⟨s,sd⟩ b m
  rw [roots] at one
  have q : w.T/v.k=v.T/v.k ∨ w.h/v.j=v.h/v.j := by
    by_cases l : v.k≤v.j
    · exact Or.inr (by simpa [coordinate,l] using y)
    · exact Or.inl (by simpa [coordinate,l] using y)
  obtain ⟨t,h⟩ := fiber_unique v.kp v.jp v.unit one v.hit q
  rw [t,h]

/-- Counts inputs admitting any positive multiplier and any allowed offset,
even when a hit yields a trivial gcd or is selected using the entire input. -/
theorem all_offsets_card (ns : Finset ℕ) {S J e : ℕ} (js : J≤S) (fit : S^2*J≤2^e)
    (bounded : ∀ n∈ns, n.sqrt<S^2)
    (hits : ∀ n∈ns, ∃ k j m, 0<n-n.sqrt^2 ∧ 0<k ∧ 0<j ∧ j≤J ∧ Hit n.sqrt (n-n.sqrt^2) k j m) :
    ns.card ≤ J*e^2*(6*S^3) := by
  classical
  have covered (n : ↥ns) : ∃ w : Witness S J, w.T^2+w.h=n.val := by
    obtain ⟨k,j,m,hp,kp,jp,cap,hit⟩ := hits n.val n.property
    obtain ⟨K,I,M,Kp,Ip,Ij,unit,eq⟩ := primitive kp jp hit
    have rel := Nat.sqrt_le_add n.val
    have le := Nat.sqrt_le' n.val
    rw [←pow_two] at rel
    exact ⟨⟨n.val.sqrt,n.val-n.val.sqrt^2,K,I,M,bounded n.val n.property,by omega,hp,
      Kp,Ip,Ij.trans cap,unit,eq⟩,Nat.add_sub_of_le le⟩
  let pick (n : ↥ns) := Classical.choose (covered n)
  have val (n : ↥ns) := Classical.choose_spec (covered n)
  have inj : Function.Injective (fun n : ↥ns => code (pick n) fit js) := by
    intro n m eq
    exact Subtype.ext ((val n).symm.trans ((recover _ _ fit js eq).trans (val m)))
  have bound := Fintype.card_le_of_injective _ inj
  simpa [Code,pow_two,Nat.mul_assoc] using bound

set_option exponentiation.threshold 4096 in
/-- Entire sweep at the stated target. The last comparison uses the known
prime-count denominator for distinct, uniformly chosen 1,024-bit primes
conditioned on a 2,048-bit product. -/
theorem scale_2048 (ns : Finset ℕ) (size : ∀ n∈ns, n.sqrt<2^1024)
    (hits : ∀ n∈ns, ∃ k j m, 0<n-n.sqrt^2 ∧ 0<k ∧ 0<j ∧ j≤2^40 ∧
      Hit n.sqrt (n-n.sqrt^2) k j m) :
    ns.card<2^1599 ∧ 2^422*2*ns.card*71000^2 < 22^2*(2:ℕ)^(2*1023) := by
  have eq : ((2:ℕ)^512)^2=2^1024 := by decide +kernel
  have le := all_offsets_card ns (S:=2^512) (e:=1064) (by decide +kernel : 2^40≤(2:ℕ)^512)
    (by decide +kernel) (by simpa only [eq] using size) hits
  have one : (2:ℕ)^40*1064^2*(6*((2:ℕ)^512)^3)<2^1599 := by decide +kernel
  have two : (2:ℕ)^422*2*((2:ℕ)^40*1064^2*(6*((2:ℕ)^512)^3))*71000^2 <
      22^2*(2:ℕ)^(2*1023) := by decide +kernel
  exact ⟨le.trans_lt one,(Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ le)).trans_lt two⟩

set_option exponentiation.threshold 4096 in
/-- Even all offsets through 2^461 cover less than half of the same prime
population, regardless of the public rule for assigning work to inputs. -/
theorem half_scale_2048 (ns : Finset ℕ) (size : ∀ n∈ns, n.sqrt<2^1024)
    (hits : ∀ n∈ns, ∃ k j m, 0<n-n.sqrt^2 ∧ 0<k ∧ 0<j ∧ j≤2^461 ∧
      Hit n.sqrt (n-n.sqrt^2) k j m) :
    2*2*ns.card*71000^2 < 22^2*(2:ℕ)^(2*1023) := by
  have eq : ((2:ℕ)^512)^2=2^1024 := by decide +kernel
  have le := all_offsets_card ns (S:=2^512) (e:=1485) (by decide +kernel : 2^461≤(2:ℕ)^512)
    (by decide +kernel) (by simpa only [eq] using size) hits
  have arithmetic : 2*2*((2:ℕ)^461*1485^2*(6*((2:ℕ)^512)^3))*71000^2 <
      22^2*(2:ℕ)^(2*1023) := by decide +kernel
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ le)).trans_lt arithmetic

set_option exponentiation.threshold 4096 in
/-- Arithmetic for the sharper divisor-sum estimate proved in the note. -/
theorem paper_constants :
    let L := (2:ℕ)^1024
    let J := (2:ℕ)^40
    let V := (2:ℕ)^1576
    2000*(3*L*J^2*740+L*J*740^2)+(26000+7*79*694)*V < 2000*205*V ∧
      2^438*2*(205*V)*71000^2 < 22^2*(2:ℕ)^(2*1023) := by decide +kernel

end PrimeFactors.OffsetSweepFrequency
