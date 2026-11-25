import PrimeFactors.OffsetSweepFrequency

namespace PrimeFactors.SignedOffsetFrequency

/-- The weighted discriminant is a square, with both signs of Tj − hk allowed. -/
def SquareHit (T h k j : ℕ) : Prop :=
  ∃ d : ℕ, d^2 + 4*h*k^2 = j^2 + 4*k*T*j

/-- On the additional side of the interval the two positive root distances
sum to the offset, and their product is divisible by the multiplier. -/
theorem endpoint_decomposition {T h k j : ℕ} (kp : 0<k) (past : T*j<h*k)
    (hit : SquareHit T h k j) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ a+b=j ∧ k ∣ a*b ∧ h*k^2=k*T*j+a*b := by
  obtain ⟨d,eq⟩ := hit
  have strict := Nat.mul_lt_mul_of_pos_left past kp
  have less : d<j := by
    by_contra! bad
    nlinarith only [Nat.pow_le_pow_left bad 2,eq,strict]
  have mod : d^2%2=j^2%2 := by
    simp only [Nat.mul_assoc] at eq
    omega
  have parity : d%2=j%2 := by
    rw [pow_two,pow_two,Nat.mul_mod d d,Nat.mul_mod j j] at mod
    rcases (show d%2=0 ∨ d%2=1 by omega) with u|u <;>
      rcases (show j%2=0 ∨ j%2=1 by omega) with v|v <;> simp_all
  let a := (j-d)/2
  let b := d+a
  have ap : 0<a := by dsimp [a]; omega
  have bp : 0<b := by dsimp [b]; omega
  have sum : a+b=j := by dsimp [a,b]; omega
  have eqn : h*k^2=k*T*j+a*b := by
    rw [←sum] at eq ⊢
    dsimp [b] at eq ⊢
    nlinarith only [eq]
  have dv : k ∣ h*k^2 := ⟨h*k,by ring⟩
  have dt : k ∣ k*T*j := ⟨T*j,by ring⟩
  exact ⟨a,b,ap,bp,sum,(Nat.dvd_add_right dt).mp (eqn ▸ dv),eqn⟩

private abbrev Digit (e J : ℕ) := Fin e × Fin J

/-- Store a positive factor pair with product at most J in eJ labels.
A dyadic interval stores the first factor and the quotient in one digit. -/
private def digit {x y e J : ℕ} (xp : 0<x) (yp : 0<y)
    (size : x*y≤J) (bits : J<2^e) : Digit e J :=
  let i := Nat.log 2 x
  let b := 2^i
  have lo : b≤x := Nat.pow_log_le_self 2 xp.ne'
  have hi : x<2*b := by simpa [b,i,pow_succ,Nat.mul_comm] using
    Nat.lt_pow_succ_log_self (by decide : 1<2) x
  have bit : i<e := Nat.log_lt_of_lt_pow xp.ne'
    ((Nat.le_mul_of_pos_right x yp).trans_lt (size.trans_lt bits))
  have rem : x-b<b := by omega
  have ub : b*y≤J := (Nat.mul_le_mul_right y lo).trans size
  have succ : y-1+1=y := by omega
  have fit : b*(y-1)+(x-b)<J := by
    calc _ < b*(y-1)+b := Nat.add_lt_add_left rem _
         _ = b*y := by rw [←Nat.mul_succ,Nat.succ_eq_add_one,succ]
         _ ≤ J := ub
  (⟨i,bit⟩,⟨_,fit⟩)

private theorem digit_unique {x y u v e J : ℕ} {xp : 0<x} {yp : 0<y}
    {up : 0<u} {vp : 0<v} {xy : x*y≤J} {uv : u*v≤J} {bits : J<2^e}
    (eq : digit xp yp xy bits = digit up vp uv bits) : x=u ∧ y=v := by
  have i := congrArg (fun a : Digit e J => a.1.val) eq
  have f := congrArg (fun a : Digit e J => a.2.val) eq
  change Nat.log 2 x=Nat.log 2 u at i
  let b := 2^(Nat.log 2 x)
  have bu : b=2^(Nat.log 2 u) := congrArg (2^·) i
  change b*(y-1)+(x-b)=2^(Nat.log 2 u)*(v-1)+(u-2^(Nat.log 2 u)) at f
  rw [←bu] at f
  have xl : b≤x := Nat.pow_log_le_self _ xp.ne'
  have ul : b≤u := bu ▸ Nat.pow_log_le_self _ up.ne'
  have xh : x<2*b := by simpa [b,pow_succ,Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1<2) x
  have uh : u<2*b := by rw [bu]; simpa [pow_succ,Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1<2) u
  have r := congrArg (· % b) f
  simp only [Nat.mul_add_mod,Nat.mod_eq_of_lt (show x-b<b by omega),
    Nat.mod_eq_of_lt (show u-b<b by omega)] at r
  have same : x=u := by omega
  have bp : 0<b := by dsimp [b]; positivity
  have : y-1=v-1 := Nat.eq_of_mul_eq_mul_left bp (by simpa [same] using f)
  exact ⟨same,by omega⟩

private structure Endpoint (L J : ℕ) where
  T : ℕ
  x : ℕ
  y : ℕ
  u : ℕ
  v : ℕ
  tlim : T<L
  xp : 0<x
  yp : 0<y
  up : 0<u
  vp : 0<v
  alim : x*y≤J
  blim : u*v≤J

private def Endpoint.value {L J : ℕ} (w : Endpoint L J) : ℕ :=
  let a := w.x*w.y
  let b := w.u*w.v
  let k := w.x*w.u
  w.T^2 + (k*w.T*(a+b)+a*b)/k^2

private theorem encode_endpoint {n L J : ℕ} (size : n.sqrt<L)
    {k j : ℕ} (kp : 0<k) (cut : j≤J) (past : n.sqrt*j<(n-n.sqrt^2)*k)
    (hit : SquareHit n.sqrt (n-n.sqrt^2) k j) :
    ∃ w : Endpoint L J, w.value=n := by
  obtain ⟨a,b,ap,bp,sum,dv,eq⟩ := endpoint_decomposition kp past hit
  obtain ⟨x,u,⟨y,ay⟩,⟨v,bv⟩,ku⟩ := Nat.dvd_mul.mp dv
  subst a; subst b; subst k; subst j
  have xp : 0<x := Nat.pos_of_mul_pos_right ap
  have up : 0<u := Nat.pos_of_mul_pos_right bp
  have yp : 0<y := Nat.pos_of_mul_pos_left ap
  have vp : 0<v := Nat.pos_of_mul_pos_left bp
  refine ⟨⟨n.sqrt,x,y,u,v,size,xp,yp,up,vp,by omega,by omega⟩,?_⟩
  change n.sqrt^2+(_)/((x*u)^2)=n
  rw [←eq,Nat.mul_div_cancel _ (pow_pos kp 2),Nat.add_sub_of_le (Nat.sqrt_le' n)]

/-- Counts every input with a square past the old cutoff. The encoding
retains its floor root and two ordered divisor pairs from the offset. -/
theorem endpoint_card (ns : Finset ℕ) {L J e : ℕ} (bits : J<2^e)
    (size : ∀ n∈ns, n.sqrt<L)
    (hits : ∀ n∈ns, ∃ k j, 0<k ∧ j≤J ∧ n.sqrt*j<(n-n.sqrt^2)*k ∧
      SquareHit n.sqrt (n-n.sqrt^2) k j) :
    ns.card ≤ L*(e*J)^2 := by
  classical
  have rep (n : ↥ns) : ∃ w : Endpoint L J, w.value=n.val := by
    obtain ⟨k,j,kp,cut,past,hit⟩ := hits n.val n.property
    exact encode_endpoint (size n.val n.property) kp cut past hit
  let w (n : ↥ns) := Classical.choose (rep n)
  let code (n : ↥ns) : Fin L × Digit e J × Digit e J :=
    (⟨(w n).T,(w n).tlim⟩,digit (w n).xp (w n).yp (w n).alim bits,
     digit (w n).up (w n).vp (w n).blim bits)
  have inj : Function.Injective code := by
    intro n m eq
    have t : (w n).T=(w m).T := congrArg (fun c => c.1.val) eq
    obtain ⟨x,y⟩ := digit_unique (xp:=(w n).xp) (yp:=(w n).yp) (up:=(w m).xp)
      (vp:=(w m).yp) (xy:=(w n).alim) (uv:=(w m).alim) (bits:=bits) (congrArg (fun c => c.2.1) eq)
    obtain ⟨u,v⟩ := digit_unique (xp:=(w n).up) (yp:=(w n).vp) (up:=(w m).up)
      (vp:=(w m).vp) (xy:=(w n).blim) (uv:=(w m).blim) (bits:=bits) (congrArg (fun c => c.2.2) eq)
    apply Subtype.ext
    rw [←Classical.choose_spec (rep n),←Classical.choose_spec (rep m)]
    change (w n).value=(w m).value
    simp only [Endpoint.value,t,x,y,u,v]
  simpa [Digit,pow_two,Nat.mul_assoc] using Fintype.card_le_of_injective code inj

/-- Counts successes for every positive multiplier, with both signs of the
residual and with no coprimality or proper-gcd assumptions. -/
theorem all_multipliers_card (ns : Finset ℕ) {S J e f : ℕ} (js : J≤S)
    (fit : S^2*J≤2^e) (bits : J<2^f) (size : ∀ n∈ns, n.sqrt<S^2)
    (hits : ∀ n∈ns, ∃ k j, 0<n-n.sqrt^2 ∧ 0<k ∧ 0<j ∧ j≤J ∧
      SquareHit n.sqrt (n-n.sqrt^2) k j) :
    ns.card ≤ J*e^2*(6*S^3) + S^2*(f*J)^2 := by
  classical
  let ordinary (n : ℕ) := ∃ k j m, 0<n-n.sqrt^2 ∧ 0<k ∧ 0<j ∧ j≤J ∧
    OffsetSweepFrequency.Hit n.sqrt (n-n.sqrt^2) k j m
  let inside := ns.filter ordinary
  have sub : inside⊆ns := Finset.filter_subset ..
  have left := OffsetSweepFrequency.all_offsets_card inside js fit
    (fun n h => size n (sub h)) (fun _ h => (Finset.mem_filter.mp h).2)
  have right := endpoint_card (ns \ inside) bits (fun n h => size n (Finset.mem_sdiff.mp h).1) (by
    intro n hn
    obtain ⟨listed,absent⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨k,j,hp,kp,jp,cut,hit⟩ := hits n listed
    refine ⟨k,j,kp,cut,?_,hit⟩
    by_contra! room
    obtain ⟨d,eq⟩ := hit
    have diff := Nat.sub_add_cancel room
    have disc : d^2=j^2+4*k*(n.sqrt*j-(n-n.sqrt^2)*k) := by
      nlinarith only [eq,congrArg (fun x => 4*k*x) diff]
    obtain ⟨m,hm⟩ := (OffsetSweepFrequency.discriminant_square_iff room).mp ⟨d,disc⟩
    exact absent (Finset.mem_filter.mpr ⟨listed,k,j,m,hp,kp,jp,cut,hm⟩))
  have split := Finset.card_sdiff_add_card_eq_card sub
  omega

set_option exponentiation.threshold 4096 in
/-- With a trillion offsets, the numerator is less than 2⁻⁴²² of the
external prime-pair denominator, including the formerly omitted endpoint. -/
theorem trillion_2048 (ns : Finset ℕ) (size : ∀ n∈ns, n.sqrt<2^1024)
    (hits : ∀ n∈ns, ∃ k j, 0<n-n.sqrt^2 ∧ 0<k ∧ 0<j ∧ j≤2^40 ∧
      SquareHit n.sqrt (n-n.sqrt^2) k j) :
    2^422*2*ns.card*71000^2 < 22^2*(2:ℕ)^(2*1023) := by
  have rel : ((2:ℕ)^512)^2=2^1024 := by decide +kernel
  have bound := all_multipliers_card ns (S:=2^512) (e:=1064) (f:=41)
    (by decide +kernel : 2^40≤(2:ℕ)^512) (by decide +kernel) (by decide +kernel)
    (by simpa only [rel] using size) hits
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ bound)).trans_lt (by decide +kernel)

set_option exponentiation.threshold 4096 in
/-- Even allowing every positive multiplier and the additional endpoint,
fewer than half of the target prime pairs can succeed through 2^461 offsets. -/
theorem half_2048 (ns : Finset ℕ) (size : ∀ n∈ns, n.sqrt<2^1024)
    (hits : ∀ n∈ns, ∃ k j, 0<n-n.sqrt^2 ∧ 0<k ∧ 0<j ∧ j≤2^461 ∧
      SquareHit n.sqrt (n-n.sqrt^2) k j) :
    2*2*ns.card*71000^2 < 22^2*(2:ℕ)^(2*1023) := by
  have rel : ((2:ℕ)^512)^2=2^1024 := by decide +kernel
  have bound := all_multipliers_card ns (S:=2^512) (e:=1485) (f:=462)
    (by decide +kernel : 2^461≤(2:ℕ)^512) (by decide +kernel) (by decide +kernel)
    (by simpa only [rel] using size) hits
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ bound)).trans_lt (by decide +kernel)

set_option exponentiation.threshold 4096 in
/-- Final arithmetic when the sharper published-note divisor sum is used on
the nonnegative branch and the finite endpoint bound on the negative branch. -/
theorem divisor_sum_constants :
    let L := (2:ℕ)^1024
    let J := (2:ℕ)^473
    let old := 3*L*J^2*1040+L*J*1040^2+2^1536*J*(13+7*329)
    let extra := L*(474*J)^2
    2*2*(old+extra)*71000^2 < 22^2*(2:ℕ)^(2*1023) ∧
      2^438*2*(205*2^1576+L*(41*2^40)^2)*71000^2 < 22^2*(2:ℕ)^(2*1023) := by
  decide +kernel

end PrimeFactors.SignedOffsetFrequency
