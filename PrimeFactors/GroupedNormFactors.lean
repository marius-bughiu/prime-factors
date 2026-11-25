import PrimeFactors.DiscriminantPencil
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.LinearCombination
import PrimeFactors.ChebyshevQuarticScale

namespace PrimeFactors.GroupedNormFactors

/-- The same k=a*b tests every norm pair with determinant one and those
coefficients. Interchanging the two factors changes the determinant sign. -/
theorem determinant_one {a b u v : ℕ} (h : ℕ) (neighbor : a*v=b*u+1) :
    let k := a*b
    let T := u*v+h*k
    let p := u^2+h*a^2
    let q := v^2+h*b^2
    p*q=T^2+h ∧ b^2*p+a^2*q=2*k*T+1 ∧ (b*u)*(b*u+1)=k*(u*v) := by
  dsimp only
  have sq : (a*v)^2+(b*u)^2=2*(a*v)*(b*u)+1 := by rw [neighbor]; ring
  constructor
  · nlinarith only [congrArg (fun z => h*z) sq]
  constructor
  · nlinarith only [sq]
  · rw [← neighbor]; ring

/-- The first integer at or above the square root of 4k²N is 2kT+1
when the square test accepts and the offset is positive. -/
theorem first_sum {T h k m : ℕ} (hp : 0<h) (kp : 0<k) (room : h*k < T)
    (hit : m*(m+1)=k*(T-h*k)) :
    (2*k*T)^2 < 4*k^2*(T^2+h) ∧
    (2*k*T+1)^2 = 4*k^2*(T^2+h)+(2*m+1)^2 := by
  have eq := Nat.sub_add_cancel room.le
  constructor
  · nlinarith only [Nat.mul_pos hp (pow_pos kp 2)]
  · nlinarith only [hit,congrArg (fun z => k*z) eq]

/-- The cheaper direct gcd is proper throughout the open branch, even when
the weighted sum exceeds N. Both individual summands stay below N. -/
theorem gcd_split {T h k m : ℕ} (hp : 0<h) (kp : 0<k) (room : h*k<T)
    (hit : m*(m+1)=k*(T-h*k)) :
    let N := T^2+h
    let d := N.gcd (k*T-m)
    1<d ∧ d<N ∧ d ∣ N := by
  let N := T^2+h
  let A := k*T-m
  let B := k*T+m+1
  change 1<N.gcd A ∧ N.gcd A<N ∧ N.gcd A ∣ N
  have kt := (Nat.le_mul_of_pos_left k hp).trans_lt room
  have mt : m<T := by
    have bound := Nat.mul_lt_mul_of_pos_right kt (by omega : 0<T)
    have small := (Nat.mul_le_mul_left k (Nat.sub_le T (h*k))).trans_lt bound
    rw [← hit] at small
    by_contra! bad
    exact (Nat.not_lt_of_ge (Nat.mul_le_mul bad (by omega : T ≤ m+1))) small
  have ma := mt.trans_le (Nat.le_mul_of_pos_left T kp)
  have ap : 0<A := Nat.sub_pos_of_lt ma
  have bp : 0<B := by dsimp [B]; omega
  have bl : B<N := by
    have enough := Nat.mul_le_mul_right T (show k+1≤T by omega)
    dsimp [B,N]
    nlinarith only [enough,mt,hp]
  have al : A<N := (Nat.sub_le _ _).trans_lt (show k*T<N by dsimp [B] at bl; omega)
  have same : A*B=k^2*N := by
    have ea : A+m=k*T := Nat.sub_add_cancel ma.le
    have er := Nat.sub_add_cancel room.le
    dsimp [B,N]
    zify at ea hit er ⊢
    linear_combination ((k:ℤ)*T+m+1)*ea-hit-(k:ℤ)*er
  have div : N ∣ A*B := ⟨k^2,by rw [same,mul_comm]⟩
  refine ⟨?_,(Nat.le_of_dvd ap (Nat.gcd_dvd_right N A)).trans_lt al,Nat.gcd_dvd_left ..⟩
  have pos := Nat.gcd_pos_of_pos_right N ap
  by_contra! small
  have cop : N.Coprime A := show N.gcd A=1 by omega
  exact Nat.not_dvd_of_pos_of_lt bp bl (cop.dvd_of_dvd_mul_left div)

/-- Recover the correct divisor allocation of k by one gcd. -/
def fromRoot (h k m : ℕ) : ℕ × ℕ :=
  let b := k.gcd m
  let a := k/b
  let u := m/b
  let v := (m+1)/a
  (u^2+h*a^2,v^2+h*b^2)

private theorem root_coordinates {T h k m : ℕ} (kp : 0<k) (room : h*k<T)
    (hit : m*(m+1)=k*(T-h*k)) :
    let b := k.gcd m
    let a := k/b
    let u := m/b
    let v := (m+1)/a
    0<a ∧ 0<b ∧ 0<u ∧ 0<v ∧ a*v=b*u+1 ∧ a*b=k ∧ u*v+h*(a*b)=T := by
  let b := k.gcd m
  let a := k/b
  let u := m/b
  let v := (m+1)/a
  have bp : 0<b := Nat.gcd_pos_of_pos_left _ kp
  have ab : a*b=k := Nat.div_mul_cancel (Nat.gcd_dvd_left k m)
  have bu : b*u=m := Nat.mul_div_cancel' (Nat.gcd_dvd_right k m)
  have ap : 0<a := Nat.pos_of_mul_pos_right (ab ▸ kp : 0<a*b)
  have mp : 0<m := Nat.pos_of_mul_pos_right (hit ▸ Nat.mul_pos kp (Nat.sub_pos_of_lt room) : 0<m*(m+1))
  have up : 0<u := Nat.pos_of_mul_pos_left (bu ▸ mp : 0<b*u)
  have cop : a.Coprime u := Nat.coprime_div_gcd_div_gcd bp
  have cancel : u*(m+1)=a*(T-h*k) := by
    apply Nat.eq_of_mul_eq_mul_left bp
    calc b*(u*(m+1)) = m*(m+1) := by rw [← Nat.mul_assoc,bu]
         _ = k*(T-h*k) := hit
         _ = b*(a*(T-h*k)) := by rw [← ab]; ring
  have adv : a ∣ m+1 := cop.dvd_of_dvd_mul_left ⟨_,cancel⟩
  have av : a*v=m+1 := Nat.mul_div_cancel' adv
  have vp : 0<v := Nat.pos_of_mul_pos_left (av ▸ Nat.succ_pos m : 0<a*v)
  have uv : u*v=T-h*k := by
    apply Nat.eq_of_mul_eq_mul_left ap
    calc a*(u*v) = u*(a*v) := by ring
         _ = _ := by rw [av,cancel]
  have det : a*v=b*u+1 := by rw [av,bu]
  exact ⟨ap,bp,up,vp,det,ab,by rw [ab,uv,Nat.sub_add_cancel room.le]⟩

/-- A successful square test yields a positive determinant-one witness with
the same multiplier and the public center T, without primality assumptions. -/
theorem witness_of_hit {T h k m : ℕ} (kp : 0<k) (room : h*k<T)
    (hit : m*(m+1)=k*(T-h*k)) :
    ∃ a b u v : ℕ, 0<a ∧ 0<b ∧ 0<u ∧ 0<v ∧ a*v=b*u+1 ∧ a*b=k ∧ u*v+h*(a*b)=T :=
  ⟨_,_,_,_,root_coordinates kp room hit⟩

theorem fromRoot_correct {T h k m : ℕ} (hp : 0<h) (kp : 0<k) (room : h*k<T)
    (hit : m*(m+1)=k*(T-h*k)) :
    let (p,q) := fromRoot h k m
    1<p ∧ 1<q ∧ p*q=T^2+h := by
  let b := k.gcd m
  let a := k/b
  let u := m/b
  let v := (m+1)/a
  obtain ⟨ap,bp,up,vp,det,_,product⟩ := root_coordinates kp room hit
  change 0<a at ap
  change 0<b at bp
  change 0<u at up
  change 0<v at vp
  change a*v=b*u+1 at det
  change u*v+h*(a*b)=T at product
  have all := (determinant_one h det).1
  rw [product] at all
  change 1<u^2+h*a^2 ∧ 1<v^2+h*b^2 ∧ _
  exact ⟨by have := Nat.mul_pos hp (pow_pos ap 2); have := pow_pos up 2; omega,
    by have := Nat.mul_pos hp (pow_pos bp 2); have := pow_pos vp 2; omega,all⟩

/-- Input-only test. A square offset in N itself is unnecessary. -/
def probe (N k : ℕ) : Option (ℕ × ℕ) :=
  let T := N.sqrt
  let h := N-T^2
  let r := k*(T-h*k)
  let m := (1+4*r).sqrt/2
  if 0<h ∧ 0<k ∧ h*k<T ∧ m*(m+1)=r then some (fromRoot h k m) else none

theorem probe_sound {N k p q : ℕ} (found : probe N k = some (p,q)) :
    1<p ∧ 1<q ∧ p*q=N := by
  unfold probe at found
  dsimp only at found
  split at found
  next yes =>
    obtain ⟨hp,kp,room,hit⟩ := yes
    have h := fromRoot_correct hp kp room hit
    rw [Option.some.inj found] at h
    simpa only [Nat.add_sub_of_le (show N.sqrt^2 ≤ N by simpa [pow_two] using Nat.sqrt_le N)] using h
  next => contradiction

theorem probe_accepts {N k T h m : ℕ} (root : N.sqrt=T) (off : N-T^2=h)
    (hp : 0<h) (kp : 0<k) (room : h*k<T) (hit : m*(m+1)=k*(T-h*k)) :
    probe N k = some (fromRoot h k m) := by
  have discr : 1+4*(k*(T-h*k))=(2*m+1)*(2*m+1) := by rw [← hit]; ring
  simp only [probe,root,off,discr,Nat.sqrt_eq,show (2*m+1)/2=m by omega,hp,kp,room,hit,
    and_self,if_true]

/-- Largest eligible multiplier from the public digits. -/
def topProbe (N : ℕ) : Option (ℕ × ℕ) := probe N ((N.sqrt-1)/(N-N.sqrt^2))

theorem multiplier_rank {T h k z : ℕ} (decomp : T=z+h*k) (hp : 0<h) (zp : 0<z) :
    (T-1)/h=(z-1)/h+k := by
  rw [show T-1=(z-1)+h*k by omega, Nat.add_mul_div_left _ _ hp]

theorem top_multiplier {T h k z : ℕ} (decomp : T=z+h*k) (pos : 0<z) (cap : z≤h) :
    (T-1)/h=k := by
  rw [multiplier_rank decomp (by omega) pos, Nat.div_eq_of_lt (by omega : z-1<h),zero_add]

theorem topProbe_accepts {N k T h z m : ℕ} (root : N.sqrt=T) (off : N-T^2=h)
    (kp : 0<k) (decomp : T=z+h*k) (zp : 0<z) (cap : z≤h) (hit : m*(m+1)=k*z) :
    topProbe N = some (fromRoot h k m) := by
  unfold topProbe
  rw [root,off,top_multiplier decomp zp cap]
  exact probe_accepts root off (by omega) kp (by omega) (by rwa [show T-h*k=z by omega])

theorem topProbe_sound {N p q : ℕ} (hit : topProbe N=some (p,q)) :
    1<p ∧ 1<q ∧ p*q=N := probe_sound hit

private theorem floor_anchor {z h k : ℕ} (kp : 0<k) : ((z+h*k)^2+h).sqrt=z+h*k := by
  have size := Nat.le_mul_of_pos_right h kp
  apply (Nat.eq_sqrt.mpr ⟨by nlinarith,by nlinarith⟩).symm

/-- Every determinant-one pair in this family triggers its one public test. -/
theorem family_covered {a b u v h : ℕ} (hp : 0<h) (ap : 0<a) (bp : 0<b)
    (up : 0<u) (vp : 0<v) (neighbor : a*v=b*u+1) :
    ∃ pair, probe ((u^2+h*a^2)*(v^2+h*b^2)) (a*b) = some pair := by
  let T := u*v+h*(a*b)
  obtain ⟨prodEq,_,relation⟩ := determinant_one h neighbor
  change (u^2+h*a^2)*(v^2+h*b^2)=T^2+h at prodEq
  rw [prodEq]
  have root : (T^2+h).sqrt=T := floor_anchor (Nat.mul_pos ap bp)
  have off : T^2+h-T^2=h := by omega
  have room : h*(a*b)<T := by dsimp [T]; have := Nat.mul_pos up vp; omega
  have cancel : T-h*(a*b)=u*v := by dsimp [T]; omega
  exact ⟨_,probe_accepts root off hp (Nat.mul_pos ap bp) room (by rw [cancel]; exact relation)⟩

/-- If the small-coordinate product fits the offset h, then a single
input-only probe finds a proper factorization of the whole family. -/
theorem topProbe_covers {a b u v h : ℕ} (ap : 0<a) (bp : 0<b) (up : 0<u) (vp : 0<v)
    (neighbor : a*v=b*u+1) (cap : u*v≤h) :
    ∃ p q, topProbe ((u^2+h*a^2)*(v^2+h*b^2))=some (p,q) ∧
      1<p ∧ 1<q ∧ p*q=(u^2+h*a^2)*(v^2+h*b^2) := by
  let T := u*v+h*(a*b)
  obtain ⟨prodEq,_,relation⟩ := determinant_one h neighbor
  change (u^2+h*a^2)*(v^2+h*b^2)=T^2+h at prodEq
  rw [prodEq]
  have uvpos := Nat.mul_pos up vp
  have root : (T^2+h).sqrt=T := floor_anchor (Nat.mul_pos ap bp)
  have off : T^2+h-T^2=h := by omega
  have found := topProbe_accepts root off (Nat.mul_pos ap bp) (rfl : T=u*v+h*(a*b)) uvpos cap relation
  exact ⟨_,_,found,topProbe_sound found⟩

/-- A one-probe example with k=56 selected by the product alone. -/
theorem top_example : topProbe 50629=some (257,197) ∧ Nat.Prime 257 ∧ Nat.Prime 197 := by
  have found := topProbe_accepts (N:=50629) (T:=225) (h:=4) (k:=56) (z:=1) (m:=7)
    (Nat.eq_sqrt.mpr (by decide)).symm (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  exact ⟨found.trans (by decide),by norm_num1,by norm_num1⟩

/-- Two different balanced prime pairs selected from consecutive public T,
read by the same k=30030. -/
theorem examples :
    probe 656618502401 30030 = some (639941,1026061) ∧
    probe 65915335618277 30030 = some (8955293,7360489) ∧
    Nat.Prime 639941 ∧ Nat.Prime 1026061 ∧ Nat.Prime 8955293 ∧ Nat.Prime 7360489 := by
  have ex₁ := probe_accepts (N:=656618502401) (T:=810320) (h:=1) (k:=30030) (m:=153075)
    (Nat.eq_sqrt.mpr (by decide +kernel)).symm (by decide +kernel) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
  have ex₂ := probe_accepts (N:=65915335618277) (T:=8118826) (h:=1) (k:=30030) (m:=492855)
    (Nat.eq_sqrt.mpr (by decide +kernel)).symm (by decide +kernel) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
  refine ⟨ex₁.trans (by decide +kernel),ex₂.trans (by decide +kernel),?_,?_,?_,?_⟩ <;> norm_num1

/-- When the public remainder is at least half T, only k=1 could pass.
Enclosing its target between consecutive triangular products excludes it. -/
theorem large_offset {N T h c : ℕ} (root : N.sqrt=T) (off : N-T^2=h)
    (wide : T≤2*h) (gap : c*(c+1)<T-h ∧ T-h<(c+1)*(c+2)) (k : ℕ) : probe N k=none := by
  unfold probe
  dsimp only
  rw [root,off]
  split
  next accepted =>
    obtain ⟨_,kp,room,hit⟩ := accepted
    have eq : k=1 := by
      by_contra contra
      have double := Nat.mul_le_mul_left h (show 2≤k by omega)
      omega
    subst k
    simp only [mul_one,one_mul] at hit
    let m := (1+4*(T-h)).sqrt/2
    change m*(m+1)=T-h at hit
    by_cases low : m≤c
    · exact False.elim ((Nat.not_lt_of_ge (Nat.mul_le_mul low (by omega : m+1 ≤ c+1)))
        (hit ▸ gap.1 : c*(c+1)<m*(m+1)))
    · exact False.elim ((Nat.not_lt_of_ge (Nat.mul_le_mul (by omega : c+1≤m)
        (by omega : c+2≤m+1))) (hit ▸ gap.2 : m*(m+1)<(c+1)*(c+2)))
  next => rfl

/-- Both complete one-test schedules miss on the public 2,048-bit controls. -/
theorem control_misses (k : ℕ) : probe ChebyshevQuarticScale.fresh k=none ∧
    probe ChebyshevQuarticScale.crossed k=none := by
  constructor
  · let T : ℕ := 158327039176966334715448284019718823474497913662177975160442996009439310669941017429676080400185006424773254142252582891257193029659269227070095120289800339855421063931472090621260003180611046788905349147963313017385074143012442899089952314244753217806428276920663827209779196401916113023989449483782760844629
    let c : ℕ := 5500665530298769307748506461388864762558762596762720878227911826937049518150797153928179341293421276956232414513958274127629871783628975790797556089182453
    exact large_offset (T:=T) (c:=c) (Nat.eq_sqrt.mpr (by decide +kernel)).symm rfl
      (by decide +kernel) (by decide +kernel) k
  · let T : ℕ := 135037911685235586269825030135549325391376915966798636179319977077209993450011760943044181307768476527897818717675959823440307553022185653953812606479930673789391793187765141283074720630433120513417190939648203494531748575804685158519937612233285802863014656458801051235008057526662884995918450838938076904614
    let c : ℕ := 7570109277772167473801479740187059477270904345797578508571027899908137136455538293072754730715600684573623026860324589029405129510785057601779246502554417
    exact large_offset (T:=T) (c:=c) (Nat.eq_sqrt.mpr (by decide +kernel)).symm rfl
      (by decide +kernel) (by decide +kernel) k

end PrimeFactors.GroupedNormFactors
