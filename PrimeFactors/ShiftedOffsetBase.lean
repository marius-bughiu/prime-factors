import PrimeFactors.OffsetWinnerWindow
import PrimeFactors.CompleteOffsetWork

namespace PrimeFactors.ShiftedOffsetBase

open CompleteOffsetSearch ReducedOffsetMinimum

/-- Moving one integer below the floor root controls the determinant on
both sides, including at products arbitrarily close to a perfect square. -/
theorem parameters {n : ℕ} (large : 1≤n.sqrt) (nonsquare : n.sqrt^2<n) :
    let T := n.sqrt-1
    let H := n-T^2
    T^2+H=n ∧ 2*T+2≤H ∧ H≤4*T+3 := by
  intro T H
  have r : n.sqrt=T+1 := by dsimp [T]; omega
  have lt := Nat.lt_succ_sqrt' n
  rw [r] at nonsquare lt
  have below : T^2≤n := (Nat.pow_le_pow_left (Nat.le_succ T) 2).trans nonsquare.le
  have digits : T^2+H=n := Nat.add_sub_of_le below
  exact ⟨digits,by nlinarith only [digits,nonsquare],by change n<(T+1+1)^2 at lt; nlinarith only [digits,lt]⟩

/-- The public height J and global multiplier cap K are each of order sqrt T. -/
theorem schedule_size {T H : ℕ} (tpos : 6≤T) (lo : 2*T+2≤H) (hi : H≤4*T+3) :
    let J := CompleteOffsetWork.height H
    let K := T*J/H+1
    (2*T).sqrt≤J ∧ J≤(6*T).sqrt ∧ J/5+1≤K ∧ K≤J/2+1 := by
  intro J K
  have tp : 0<T := by omega
  have hp : 0<H := by omega
  have leH : 2*T≤4*H/3 := by omega
  have hiH : 4*H/3≤6*T := by omega
  have h5 : H≤5*T := by omega
  have kmin : (J/5)*H≤T*J := calc
    (J/5)*H ≤ (J/5)*(5*T) := Nat.mul_le_mul_left _ h5
    _ = T*((J/5)*5) := by ring
    _ ≤ T*J := Nat.mul_le_mul_left T (Nat.div_mul_le_self ..)
  have kmax : (T*J/H)*2≤J := by
    apply Nat.le_of_mul_le_mul_left _ tp
    calc
      T*((T*J/H)*2) = (T*J/H)*(2*T) := by ring
      _ ≤ (T*J/H)*H := Nat.mul_le_mul_left _ (by omega)
      _ ≤ T*J := Nat.div_mul_le_self ..
  exact ⟨Nat.sqrt_le_sqrt leH,Nat.sqrt_le_sqrt hiH,
    Nat.succ_le_succ ((Nat.le_div_iff_mul_le hp).mpr kmin),
    Nat.succ_le_succ ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr kmax)⟩

/-- Coupling the height to the same H used in the quotient improves on
taking the two independent worst cases. -/
theorem multiplier_square {T H : ℕ} (tp : 0<T) (lo : 2*T<H) :
    let J := CompleteOffsetWork.height H
    3*(T*J/H)^2<2*T := by
  intro J
  let m := T*J/H
  have hp : 0<H := by omega
  have sqJ : J^2*3≤4*H := (Nat.le_div_iff_mul_le (by decide : 0<3)).mp (Nat.sqrt_le' _)
  have div : m*H≤T*J := Nat.div_mul_le_self ..
  have divsq := Nat.pow_le_pow_left div 2
  have left : (3*m^2*H)*H≤(4*T^2)*H := by
    nlinarith only [divsq,Nat.mul_le_mul_left (T^2) sqJ]
  have cancel : 3*m^2*H≤4*T^2 := Nat.le_of_mul_le_mul_right left hp
  have strict : (2*T)*H>(4*T^2) := by
    have cmp := Nat.mul_lt_mul_of_pos_left lo (show 0<2*T by omega)
    nlinarith only [cmp]
  exact (Nat.mul_lt_mul_right hp).mp (cancel.trans_lt strict)

/-- A 2,048-bit product gives a global multiplier cap strictly below 2^512;
the public height is below 3·2^512. The lemma also covers smaller T≥6. -/
theorem bits2048 {T H : ℕ} (base : T<2^1024) (size : 6≤T)
    (lo : 2*T+2≤H) (hi : H≤4*T+3) :
    let J := CompleteOffsetWork.height H
    J<3*2^512 ∧ T*J/H+1<2^512 := by
  intro J
  have bounds := schedule_size size lo hi
  have m := multiplier_square (T:=T) (H:=H) (by omega) (by omega)
  change 3*(T*J/H)^2<2*T at m
  have upJ : (6*T).sqrt<3*2^512 := Nat.sqrt_lt'.mpr (by
    have limit : 6*(2:ℕ)^1024<(3*2^512)^2 := by decide +kernel
    omega)
  refine ⟨bounds.2.1.trans_lt upJ,?_⟩
  by_contra! bad
  have bigger : 2^512-1≤T*J/H := by omega
  have sq := Nat.pow_le_pow_left bigger 2
  have scale : 2*(2:ℕ)^1024<3*(2^512-1)^2 := by decide +kernel
  omega

/-- The smaller prime is paired with the larger coordinate at a minimum:
swapping two positive coordinates reverses the strict excess otherwise. -/
private theorem order_of_minimum {p T q H s v : ℤ} (pp : 0<p) (hp : 0<H)
    (det : p*q-T^2=H) (ord : p<q) (vp : 0<v) (sp : 0<s)
    (best : ∀ a b, 0<Q p T q a b → Q p T q s v ≤ Q p T q a b) : v≤s := by
  by_contra! bad
  have swap := best v s (positive pp hp det (Or.inl vp.ne'))
  have excess := mul_pos (sub_pos.mpr ord) (sub_pos.mpr (pow_lt_pow_left₀ bad sp.le (by decide : 2≠0)))
  unfold Q at swap
  nlinarith only [swap,excess]

/-- Even at the shifted root the product-only sharp schedule contains a
recoverable prime. The positive minimizing coordinates lie in v≤s≤2v. -/
theorem complete_balanced {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (balance : q≤2*p) (large : 17≤p) :
    let N := p*q
    let T := N.sqrt-1
    let H := N-T^2
    ∃ j s v : ℕ, 0<v ∧ v≤s ∧ s≤2*v ∧ s.Coprime v ∧
      j+2*T*(s*v)=p*s^2+q*v^2 ∧
      3*j^2≤4*H ∧ InSchedule T H j (s*v) ∧
      (probe N T j (s*v)=some p ∨ probe N T j (s*v)=some q) := by
  let N := p*q
  let r := N.sqrt
  let T := r-1
  let H := N-T^2
  have pr : p≤r := Nat.le_sqrt'.mpr (by simpa [pow_two] using Nat.mul_le_mul_left p ord.le)
  have rq : r≤q := Nat.mul_self_le_mul_self_iff.mp ((Nat.sqrt_le N).trans (Nat.mul_le_mul_right q ord.le))
  obtain ⟨_,nonsq,_⟩ := balanced_parameters pp qp ord balance large
  change 0<N-r^2 at nonsq
  obtain ⟨digits,lo,hi⟩ := parameters (n:=N) (by change 1≤r; omega) (by change r^2<N; omega)
  change T^2+H=p*q at digits
  change 2*T+2≤H at lo
  change H≤4*T+3 at hi
  have hp : 0<H := by omega
  have base : T≤2*p := by dsimp [T]; omega
  have cut : 4*H<3*p^2 := by
    have floor : T+1=r := by dsimp [T]; omega
    have fp : 16*p<p^2 := by simpa only [pow_two] using
      Nat.mul_lt_mul_of_pos_right (show 16<p by omega) pp.pos
    nlinarith only [hi,floor,rq,balance,fp]
  have ppZ : (0:ℤ)<p := by exact_mod_cast pp.pos
  have det : (p:ℤ)*q-(T:ℤ)^2=H := by
    have sum : (T:ℤ)^2+H=(p:ℤ)*q := by exact_mod_cast digits
    linarith only [sum]
  have hZ : (0:ℤ)<H := by exact_mod_cast hp
  obtain ⟨a,b,pos,best,cop,sharp⟩ := exists_minimum ppZ hZ det
  let z := Q p T q a b
  change 0<z at pos
  change 3*z^2≤4*(H:ℤ) at sharp
  have low : z<(p:ℤ) := by
    have limit : 4*(H:ℤ)<3*(p:ℤ)^2 := by exact_mod_cast cut
    apply lt_of_not_ge
    intro bad
    have sq := pow_le_pow_left₀ ppZ.le bad 2
    linarith only [sq,limit,sharp]
  have small : z^2≤4*(H:ℤ) := by nlinarith only [sharp,sq_nonneg z]
  obtain ⟨k,dom,found⟩ := witness_of_signed pp qp digits hp cop (rfl : z=_) pos low
    (low.trans (by exact_mod_cast ord)) small
  have hit : ∃ f, probe (p*q) T z.toNat k=some f := by
    rcases found with f|f
    · exact ⟨p,f⟩
    · exact ⟨q,f⟩
  obtain ⟨f,hit⟩ := hit
  obtain ⟨s,v,sp,vp,sv,ks,label⟩ :=
    OffsetSquareWitness.exists_vector_of_hit pp qp ord.ne dom.2.2.1 dom.2.2.2.2 hit
  subst k
  have ze : (z.toNat:ℤ)=z := Int.toNat_of_nonneg pos.le
  have zval : Q p T q s v=z := by
    have eq : (z.toNat:ℤ)+2*T*(s*v)=(p:ℤ)*s^2+(q:ℤ)*v^2 := by exact_mod_cast label
    rw [ze] at eq
    unfold Q
    nlinarith only [eq]
  have orderZ := order_of_minimum ppZ hZ det (by exact_mod_cast ord)
    (show (0:ℤ)<v by exact_mod_cast vp) (show (0:ℤ)<s by exact_mod_cast sp)
    (fun x y good => zval ▸ best x y good)
  have vs : v≤s := by exact_mod_cast orderZ
  have jsmall : z.toNat<p := by omega
  have slope := (OffsetWinnerWindow.close_to_slope pp.pos digits jsmall label).1
  have roof := Nat.mul_le_mul_right v base
  have lim : p*s<p*(2*v+1) := by nlinarith only [slope,roof]
  have su : s≤2*v := by have := (Nat.mul_lt_mul_left pp.pos).mp lim; omega
  have sharpN : 3*z.toNat^2≤4*H := by
    exact_mod_cast (show 3*(z.toNat:ℤ)^2≤4*(H:ℤ) by rwa [ze])
  exact ⟨z.toNat,s,v,vp,vs,su,sv,label,sharpN,dom,found⟩

end PrimeFactors.ShiftedOffsetBase
