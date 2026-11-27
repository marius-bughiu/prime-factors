import PrimeFactors.MarginalTraceCoverage

/-! Width comparison for two residue-selected weighted Fermat bands at a fixed budget.
Each schedule uses 16 common ordinary labels and 15 weighted labels across two starts. -/
namespace PrimeFactors.GeometryWeightMenu

open Real MarginalTraceWidth

structure Arm where
  a : ℕ
  b : ℕ

/-- The common arm has different test counts. The second arm changes altogether. -/
structure Plan where
  shared : Arm
  removed : Arm
  added : Arm
  previousCount : ℕ
  selectedCount : ℕ

private noncomputable def group (r : ℕ) : Fin 4 :=
  if r%12=1 then 0 else if r%12=5 then 1 else if r%12=7 then 2 else 3

noncomputable def plan (i : Fin 4) : Plan :=
  if i.val=0 then ⟨⟨7,5⟩,⟨3,2⟩,⟨13,11⟩,12,9⟩
  else if i.val=1 then ⟨⟨7,5⟩,⟨3,2⟩,⟨9,7⟩,10,8⟩
  else if i.val=2 then ⟨⟨7,5⟩,⟨3,2⟩,⟨11,7⟩,10,7⟩
  else ⟨⟨3,2⟩,⟨7,5⟩,⟨11,7⟩,8,7⟩

noncomputable def schedule (r : ℕ) := plan (group r)

private structure Bound where
  x : ℕ
  d : ℕ
  y : ℕ
  z : ℕ
  m : ℕ
  t : ℕ
  g : ℕ
  lost : ℕ
  gain : ℕ

private noncomputable def bound (i : Fin 4) : Bound :=
  if i.val=0 then ⟨216,72,12,144,10213,48295,1581,3615,6384⟩
  else if i.val=1 then ⟨96,24,18,80,6809,48295,804,4427,5599⟩
  else if i.val=2 then ⟨84,36,18,192,6369,48295,1244,4427,7462⟩
  else ⟨20,4,48,96,4666,108867,446,4815,5277⟩

private theorem ranks : ∀ r o : Fin 24, (r:ℕ).Coprime 6 →
    let P := schedule r
    let B := bound (group r)
    let off := fun (arm : Arm) (H : ℕ) => offset r o arm.a arm.b H
    B.x ≤ off P.shared P.selectedCount ∧
    off P.shared P.previousCount ≤ off P.shared P.selectedCount+B.d ∧
    off P.shared P.previousCount+1 ≤ 360 ∧
    off P.removed (15-P.previousCount)+1 ≤ B.y ∧
    B.z ≤ off P.added (15-P.selectedCount) := by decide +kernel

/-- Squared leading width divided by height, in units of the product fourth root. -/
noncomputable def scale (A : Arm) : ℝ := 4*√((A.b:ℝ)/A.a^3)

noncomputable def leading (A : Arm) (h : ℝ) : ℝ := √(scale A*h)

/-- True interval width divided by u, for N=u^4 and excess trace h. -/
noncomputable def normalized (A : Arm) (u h : ℝ) : ℝ :=
  √(scale A*h + (h/((A.a:ℝ)*u))^2)

noncomputable def root (A : Arm) : ℝ := √(√((A.a:ℝ)*A.b))

noncomputable def excess (r : Fin 24) (A : Arm) (u : ℝ) (H : ℕ) :=
  height r u (root A) A.a A.b H

noncomputable def width (r : Fin 24) (A : Arm) (u : ℝ) (H : ℕ) :=
  u*normalized A u (excess r A u H)

private theorem scale_sq (A : Arm) : (scale A)^2 = 16*A.b/(A.a:ℝ)^3 := by
  unfold scale
  rw [mul_pow,sq_sqrt (by positivity)]
  ring

private theorem leading_fourth (A : Arm) {h : ℝ} (h0 : 0≤h) :
    (leading A h)^4 = 16*A.b*h^2/(A.a:ℝ)^3 := by
  have s0 : 0≤scale A := by unfold scale; positivity
  rw [show (leading A h)^4=((leading A h)^2)^2 by ring]
  rw [leading, sq_sqrt (mul_nonneg s0 h0), mul_pow, scale_sq]
  ring

private theorem lower {A : Arm} {h v : ℝ} (h0 : 0≤h)
    (hv : v^4 ≤ 16*A.b*h^2/(A.a:ℝ)^3) : v ≤ leading A h := by
  exact le_of_pow_le_pow_left₀ (n:=4) (by decide) (sqrt_nonneg _) ((leading_fourth A h0).symm ▸ hv)

private theorem upper {A : Arm} {h v : ℝ} (h0 : 0≤h) (v0 : 0≤v)
    (hv : 16*A.b*h^2/(A.a:ℝ)^3 ≤ v^4) : leading A h ≤ v :=
  le_of_pow_le_pow_left₀ (n:=4) (by decide) v0 ((leading_fourth A h0).symm ▸ hv)

private theorem mono (A : Arm) {h k : ℝ} (hk : h≤k) : leading A h ≤ leading A k := by
  apply sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hk (by unfold scale; positivity)

private theorem approximation (A : Arm) {u h : ℝ} (a1 : 1≤(A.a:ℝ)) (big : 1000000≤u)
    (h0 : 0≤h) (boundH : h≤360) :
    leading A h ≤ normalized A u h ∧ normalized A u h ≤ leading A h+1/1000 := by
  have s0 : 0≤scale A := by unfold scale; positivity
  have L0 : 0≤leading A h := sqrt_nonneg _
  have eqL : (leading A h)^2=scale A*h := sq_sqrt (mul_nonneg s0 h0)
  have ap : 0<(A.a:ℝ) := by linarith
  have up : 0<u := by linarith
  have ax := le_mul_of_one_le_left up.le a1
  have delta : 0≤h/((A.a:ℝ)*u) := by positivity
  have cap : h/((A.a:ℝ)*u)≤1/1000 := (div_le_iff₀ (mul_pos ap up)).mpr (by linarith only [boundH,big,ax])
  refine ⟨sqrt_le_sqrt (by linarith only [sq_nonneg (h/((A.a:ℝ)*u))]),?_⟩
  apply sqrt_le_iff.mpr
  refine ⟨by linarith only [L0],?_⟩
  nlinarith only [eqL,L0,pow_le_pow_left₀ delta cap 2]

private theorem shared_loss {A : Arm} {x d h k m t g : ℝ}
    (x0 : 0≤x) (m0 : 0≤m) (g0 : 0≤g) (d0 : 0≤d) (xh : x≤h)
    (order : k≤h+d) (mlo : m≤leading A x) (tcap : scale A≤t)
    (room : t*d≤2*m*g+g^2) : leading A k ≤ leading A h+g := by
  have s0 : 0≤scale A := by unfold scale; positivity
  have H0 := mlo.trans (mono A xh)
  have HH := sq_sqrt (mul_nonneg s0 (x0.trans xh))
  change (leading A h)^2 = scale A*h at HH
  apply sqrt_le_iff.mpr
  refine ⟨by linarith only [m0,H0,g0],?_⟩
  nlinarith only [HH,room,mul_le_mul_of_nonneg_right H0 g0,
    mul_le_mul_of_nonneg_right tcap d0,mul_le_mul_of_nonneg_left order s0]

private theorem facts (g : Fin 4) :
    let P := plan g
    let B := bound g
    (B.m/1000:ℝ)^4 ≤ 16*P.shared.b*(B.x:ℝ)^2/(P.shared.a:ℝ)^3 ∧
    16*P.shared.b/(P.shared.a:ℝ)^3 ≤ (B.t/100000:ℝ)^2 ∧
    (B.t/100000:ℝ)*B.d ≤ 2*(B.m/1000:ℝ)*(B.g/1000:ℝ)+(B.g/1000:ℝ)^2 ∧
    16*P.removed.b*(B.y:ℝ)^2/(P.removed.a:ℝ)^3 ≤ (B.lost/1000:ℝ)^4 ∧
    (B.gain/1000:ℝ)^4 ≤ 16*P.added.b*(B.z:ℝ)^2/(P.added.a:ℝ)^3 ∧
    (B.lost/1000:ℝ)+(B.g/1000:ℝ)+16/1000 ≤ B.gain/1000 ∧
    1≤(P.shared.a:ℝ) ∧ 1≤(P.removed.a:ℝ) ∧ (B.y:ℝ)≤360 := by
  fin_cases g <;> norm_num [bound,plan]

private theorem phase (r : Fin 24) (unit : (r:ℕ).Coprime 6) (u : ℝ) :
    let P := schedule r
    let B := bound (group r)
    let h := excess r P.shared u P.selectedCount
    let k := excess r P.shared u P.previousCount
    let y := excess r P.removed u (15-P.previousCount)
    let z := excess r P.added u (15-P.selectedCount)
    (B.x:ℝ) ≤ h ∧ k ≤ h+B.d ∧ k≤360 ∧ y≤B.y ∧ (B.z:ℝ)≤z := by
  let P := schedule r
  let B := bound (group r)
  let s := fun (A : Arm) => 2*(root A)^2*u^2
  let o := fun (A : Arm) => (⟨⌈s A⌉₊%24,Nat.mod_lt _ (by decide)⟩ : Fin 24)
  let e := fun (A : Arm) => (⌈s A⌉₊:ℝ)-s A
  have err (A : Arm) : 0≤e A ∧ e A≤1 :=
    ⟨sub_nonneg.mpr (Nat.le_ceil _),by dsimp [e]; linarith only [Nat.ceil_lt_add_one (by dsimp [s]; positivity : 0≤s A)]⟩
  have value (A : Arm) (H : ℕ) : excess r A u H=(offset r (o A) A.a A.b H:ℝ)+e A := rfl
  obtain ⟨h,k,d,_,_⟩ := ranks r (o P.shared) unit
  have y := (ranks r (o P.removed) unit).2.2.2.1
  have z := (ranks r (o P.added) unit).2.2.2.2
  dsimp only
  rw [value,value,value,value]
  replace h := (Nat.cast_le (α:=ℝ)).mpr h
  replace k := (Nat.cast_le (α:=ℝ)).mpr k
  replace d := (Nat.cast_le (α:=ℝ)).mpr d
  replace y := (Nat.cast_le (α:=ℝ)).mpr y
  replace z := (Nat.cast_le (α:=ℝ)).mpr z
  push_cast at k d y
  dsimp only at h k d y z
  exact ⟨by linarith only [h,(err P.shared).1],by linarith only [k],
    by linarith only [d,(err P.shared).2],by linarith only [y,(err P.removed).2],
    by linarith only [z,(err P.added).1]⟩

private theorem excess_nonneg (r : Fin 24) (A : Arm) (u : ℝ) (H : ℕ) : 0 ≤ excess r A u H := by
  dsimp only [excess,height]
  exact add_nonneg (by positivity) (sub_nonneg.mpr (Nat.le_ceil _))

/-- For every possible starting phase at the actual product, the new two weighted
bands gain at least 1.4 percent of N^(1/4) in summed length over the previous two.
The common ordinary prefix cancels. -/
theorem width_gain (r : Fin 24) (unit : (r:ℕ).Coprime 6) {u : ℝ} (big : 1000000≤u) :
    let P := schedule r
    width r P.shared u P.previousCount + width r P.removed u (15-P.previousCount) +
      14/1000*u ≤ width r P.shared u P.selectedCount + width r P.added u (15-P.selectedCount) := by
  let P := schedule r
  let B := bound (group r)
  let h := excess r P.shared u P.selectedCount
  let k := excess r P.shared u P.previousCount
  let y := excess r P.removed u (15-P.previousCount)
  let z := excess r P.added u (15-P.selectedCount)
  obtain ⟨xh,kh,kcap,ycap,zlo⟩ := phase r unit u
  obtain ⟨M,T,R,L,G,margin,a1,b1,Y⟩ := facts (group r)
  have tc : scale P.shared ≤ (B.t/100000:ℝ) := le_of_sq_le_sq (by rw [scale_sq]; exact T) (by positivity)
  have loss : leading P.shared k ≤ leading P.shared h + B.g/1000 :=
    shared_loss (x:=B.x) (d:=B.d) (m:=(B.m:ℝ)/1000) (t:=(B.t:ℝ)/100000)
      (by positivity) (by positivity) (by positivity) (by positivity) xh kh (lower (by positivity) M) tc R
  have gone := (mono P.removed ycap).trans (upper (by positivity) (by positivity) L)
  have new := (lower (by positivity) G).trans (mono P.added zlo)
  have before₁ := (approximation P.shared a1 big (excess_nonneg _ _ _ _) kcap).2
  have before₂ := (approximation P.removed b1 big (excess_nonneg _ _ _ _) (ycap.trans Y)).2
  have under (A : Arm) (v : ℝ) : leading A v≤normalized A u v :=
    sqrt_le_sqrt (by linarith only [sq_nonneg (v/((A.a:ℝ)*u))])
  have gain : normalized P.shared u k + normalized P.removed u y + 14/1000 ≤
      normalized P.shared u h + normalized P.added u z := by
    linarith only [loss,gone,new,before₁,before₂,under P.shared h,under P.added z,margin]
  dsimp only [width]
  linarith only [mul_le_mul_of_nonneg_left gain (show 0≤u by linarith only [big])]

noncomputable def midpoint (A : Arm) (u h : ℝ) :=
  √((A.b:ℝ)/A.a)*u^2+h/(2*A.a)

noncomputable def low (A : Arm) (u h : ℝ) := midpoint A u h - u*normalized A u h/2

noncomputable def high (A : Arm) (u h : ℝ) := midpoint A u h + u*normalized A u h/2

theorem endpoint_width (A : Arm) (u h : ℝ) : high A u h - low A u h = u*normalized A u h := by
  unfold high low
  ring

private theorem center_eq (A : Arm) (a0 : 0<(A.a:ℝ)) :
    √((A.b:ℝ)/A.a)*(A.a:ℝ) = √((A.a:ℝ)*A.b) := by
  have eq := sq_sqrt (show 0≤(A.b:ℝ)/A.a by positivity)
  have rr := sq_sqrt (show 0≤(A.a:ℝ)*A.b by positivity)
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,eq,rr]
  field_simp [ne_of_gt a0]
  ring

/-- The endpoints are the two roots in the smaller-factor coordinate of
a*x^2 + b*N = (2*sqrt(a*b*N)+h)*x; the open interval is exactly the region
below the first omitted admissible trace. -/
theorem band_iff (A : Arm) {u h x : ℝ} (a0 : 0<(A.a:ℝ)) (up : 0<u) (h0 : 0≤h) :
    A.a*x^2 + A.b*u^4 < (2*(root A)^2*u^2+h)*x ↔ low A u h<x ∧ x<high A u h := by
  let c := √((A.b:ℝ)/A.a)
  let v := √((A.b:ℝ)/A.a^3)
  have ca : c*(A.a:ℝ)=√((A.a:ℝ)*A.b) := center_eq A a0
  have cs : c^2=(A.b:ℝ)/A.a := sq_sqrt (by positivity)
  have vs : v^2=(A.b:ℝ)/A.a^3 := sq_sqrt (by positivity)
  have va : v*(A.a:ℝ)=c := by
    apply (sq_eq_sq₀ (by dsimp [v]; positivity) (by dsimp [c]; positivity)).mp
    rw [mul_pow,vs,cs]
    field_simp [ne_of_gt a0]
    ring
  have rr : (root A)^2=√((A.a:ℝ)*A.b) := sq_sqrt (sqrt_nonneg _)
  have s0 : 0≤scale A := by unfold scale; positivity
  have eq := sq_sqrt (add_nonneg (mul_nonneg s0 h0) (sq_nonneg (h/((A.a:ℝ)*u))))
  change (normalized A u h)^2=4*v*h+(h/((A.a:ℝ)*u))^2 at eq
  have rel : (x-low A u h)*(x-high A u h)*(A.a:ℝ)=
      A.a*x^2+A.b*u^4-(2*(root A)^2*u^2+h)*x := by
    unfold low high midpoint
    change (x-(c*u^2+h/(2*A.a)-u*normalized A u h/2))*
      (x-(c*u^2+h/(2*A.a)+u*normalized A u h/2))*(A.a:ℝ)=_
    rw [rr,←ca]
    field_simp [ne_of_gt a0,ne_of_gt up] at cs eq ⊢
    linear_combination -4*A.a*eq + 16*A.a^2*u^4*cs - 16*A.a^2*h*u^2*va
  have ord : low A u h ≤ high A u h := by
    unfold low high
    linarith only [mul_nonneg up.le (show 0≤normalized A u h from sqrt_nonneg _)]
  have neg (x : ℝ) : x*(A.a:ℝ)<0 ↔ x<0 := by simpa using (mul_lt_mul_iff_of_pos_right (b:=x) (c:=0) a0)
  rw [←sub_neg,←rel,neg,mul_neg_iff]
  constructor
  · rintro (⟨a,b⟩|⟨a,b⟩)
    · exact ⟨by linarith only [a],by linarith only [b]⟩
    · linarith only [a,b,ord]
  · rintro ⟨a,b⟩
    exact Or.inl ⟨sub_pos.mpr a,sub_neg.mpr b⟩

/-- An actual factor in the primary band places its true sum among the paid
labels. Its square then yields one of the factors from a single gcd. -/
theorem factor_readout (A : Arm) {p q H : ℕ} (pp : 0<p) (qp : 0<q)
    (ap : 0<A.a) (bp : 0<A.b) (unit : p.Coprime 6) (cop : (A.a*A.b).Coprime (p*q)) :
    let u := productRoot (p*q)
    let r : Fin 24 := ⟨(p*q)%24,Nat.mod_lt _ (by decide)⟩
    let f := ⌈2*(root A)^2*u^2⌉₊
    let h := excess r A u H
    (low A u h<p ∧ (p:ℝ)<high A u h) ↔ ∃ i<H,
      let t := f + offset r (f%24) A.a A.b i
      let d := (t^2-4*(A.a*A.b)*(p*q)).sqrt
      t=A.a*p+A.b*q ∧ t^2=4*(A.a*A.b)*(p*q)+d^2 ∧
      ((p*q).gcd ((t+d)/2)=p ∨ (p*q).gcd ((t+d)/2)=q) := by
  let u := productRoot (p*q)
  let r : Fin 24 := ⟨(p*q)%24,Nat.mod_lt _ (by decide)⟩
  let f := ⌈2*(root A)^2*u^2⌉₊
  let h := excess r A u H
  have ap' : 0<(A.a:ℝ) := by exact_mod_cast ap
  have bp' : 0<(A.b:ℝ) := by exact_mod_cast bp
  have up : 0<u := by dsimp [u,productRoot]; positivity
  have jp : 0<root A := by dsimp [root]; positivity
  have js : (root A)^4=(A.a:ℝ)*A.b := by
    rw [show (root A)^4=((root A)^2)^2 by ring,
      show (root A)^2=√((A.a:ℝ)*A.b) from sq_sqrt (sqrt_nonneg _),sq_sqrt (by positivity)]
  have h0 := excess_nonneg r A u H
  have old := MarginalTraceWidth.factor_band_iff (H:=H) pp qp ap jp js unit
  dsimp only at old ⊢
  change ((root A)^2*u^2/A.a/endpoint u (root A) h < p ∧ (p:ℝ) < (root A)^2*u^2/A.a*endpoint u (root A) h) ↔ ∃ i<H, A.a*p+A.b*q=f+offset r (f%24) A.a A.b i at old
  change (low A u h < p ∧ (p:ℝ)<high A u h) ↔ _
  rw [←MarginalTraceWidth.band_iff (x:=(p:ℝ)) up jp (show 0≤h from h0) ap',js] at old
  rw [show (A.a:ℝ)*A.b*u^4/A.a=A.b*u^4 by field_simp; ring] at old
  rw [←band_iff A ap' up (show 0≤h from h0),old]
  constructor
  · rintro ⟨i,small,hit⟩
    refine ⟨i,small,hit.symm,?_, WeightedTracePrefix.shared_gcd rfl rfl cop hit.symm⟩
    rw [←hit]
    have sq := multiplier_sum_square p q A.a A.b
    rw [mul_assoc 4 A.a A.b] at sq
    rw [sq,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  · rintro ⟨i,small,hit,_,_⟩
    exact ⟨i,small,hit.symm⟩

private noncomputable def fence (A : Arm) : ℕ :=
  if A.a=3 then 816 else if A.a=7 then 845 else if A.a=9 then 881 else if A.a=11 then 797 else 919

private def Sound (A : Arm) : Prop :=
  1≤(A.a:ℝ) ∧ (A.b:ℝ)≤A.a ∧ 797≤(fence A:ℝ) ∧ (fence A:ℝ)≤919 ∧
  ((fence A:ℝ)/1000)^2 ≤ A.b/A.a ∧ (A.b:ℝ)/A.a ≤ (((fence A:ℝ)+2)/1000)^2

private theorem fences (i : Fin 4) :
    let P := plan i
    Sound P.shared ∧ Sound P.added ∧ Sound P.removed ∧
      (fence P.shared+4 ≤ fence P.removed ∨ fence P.removed+4 ≤ fence P.shared) ∧
      (fence P.shared+4 ≤ fence P.added ∨ fence P.added+4 ≤ fence P.shared) := by
  fin_cases i <;> norm_num [plan,Sound,fence]

private theorem all_heights : ∀ r o : Fin 24, (r:ℕ).Coprime 6 →
    let P := schedule r
    (offset r o P.shared.a P.shared.b P.selectedCount)+1≤360 ∧
    (offset r o P.shared.a P.shared.b P.previousCount)+1≤360 ∧
    (offset r o P.added.a P.added.b (15-P.selectedCount))+1≤360 ∧
    (offset r o P.removed.a P.removed.b (15-P.previousCount))+1≤360 := by decide +kernel

private theorem fence_band (A : Arm) (ha : Sound A) {u h : ℝ} (big : 1000000≤u)
    (h0 : 0≤h) (h1 : h≤360) :
    ((fence A:ℝ)-1)/1000*u^2 < low A u h ∧
    high A u h < ((fence A:ℝ)+3)/1000*u^2 := by
  obtain ⟨a1,b1,_,_,s,t⟩ := ha
  have ap : 0<(A.a:ℝ) := by linarith
  have up : 0<u := by linarith
  have third : (A.a:ℝ)≤(A.a:ℝ)^3 := by
    nlinarith only [mul_le_mul_of_nonneg_left (one_le_pow₀ a1 (n:=2)) ap.le]
  have cap : (A.b:ℝ)/A.a^3 ≤ 1 := (div_le_one (by positivity)).mpr (b1.trans third)
  have rs := sqrt_le_sqrt cap
  rw [sqrt_one] at rs
  have sc : scale A≤4 := by dsimp [scale]; linarith
  have L : leading A h≤38 := sqrt_le_iff.mpr ⟨by norm_num,by linarith only [mul_le_mul sc h1 h0 (by norm_num : (0:ℝ)≤4)]⟩
  have w : normalized A u h ≤39 := by linarith only [(approximation A a1 big h0 h1).2,L]
  have d0 : 0≤h/(2*(A.a:ℝ)) := by positivity
  have d1 : h/(2*(A.a:ℝ))≤180 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have cl := (le_sqrt (by positivity) (by positivity)).mpr s
  have ch := sqrt_le_iff.mpr ⟨by positivity,t⟩
  have room := mul_le_mul_of_nonneg_right big up.le
  unfold low high midpoint
  constructor
  · nlinarith only [room,d0,up,mul_le_mul_of_nonneg_right cl (sq_nonneg u),mul_le_mul_of_nonneg_left w up.le]
  · nlinarith only [room,d1,big,mul_le_mul_of_nonneg_right ch (sq_nonneg u),mul_le_mul_of_nonneg_left w up.le]

/-- Each weighted band lies inside (0.796,0.922)*sqrt(N). The two bands used
by either schedule are disjoint. The conditions use only the product. -/
theorem separated (r : Fin 24) (unit : (r:ℕ).Coprime 6) {u : ℝ} (big : 1000000≤u) :
    let P := schedule r
    let pair := fun (A : Arm) (H : ℕ) =>
      (low A u (excess r A u H), high A u (excess r A u H))
    let inside := fun (x : ℝ × ℝ) => 796/1000*u^2 < x.1 ∧ x.2 < 922/1000*u^2
    let apart := fun (x y : ℝ × ℝ) => x.2<y.1 ∨ y.2<x.1
    let a := pair P.shared P.previousCount
    let b := pair P.removed (15-P.previousCount)
    let c := pair P.shared P.selectedCount
    let d := pair P.added (15-P.selectedCount)
    inside a ∧ inside b ∧ inside c ∧ inside d ∧ apart a b ∧ apart c d := by
  let P := schedule r
  let pair := fun (A : Arm) (H : ℕ) => (low A u (excess r A u H), high A u (excess r A u H))
  let s := fun (A : Arm) => 2*(root A)^2*u^2
  let o := fun (A : Arm) => (⟨⌈s A⌉₊%24,Nat.mod_lt _ (by decide)⟩ : Fin 24)
  have bounded (A : Arm) (H : ℕ) (sound : Sound A) (cap : offset r (o A) A.a A.b H+1≤360) :
      ((fence A:ℝ)-1)/1000*u^2 < (pair A H).1 ∧ (pair A H).2<((fence A:ℝ)+3)/1000*u^2 := by
    apply fence_band A sound big (excess_nonneg _ _ _ _)
    have C := (Nat.cast_le (α:=ℝ)).mpr cap
    push_cast at C
    have err := Nat.ceil_lt_add_one (by dsimp [s]; positivity : 0≤s A)
    change (offset r (o A) A.a A.b H:ℝ)+((⌈s A⌉₊:ℝ)-s A) ≤360
    linarith only [C,err]
  obtain ⟨sa,se,sr,old,new⟩ := fences (group r)
  have a := bounded P.shared P.previousCount sa ((all_heights r (o P.shared) unit).2.1)
  have b := bounded P.removed (15-P.previousCount) sr ((all_heights r (o P.removed) unit).2.2.2)
  have c := bounded P.shared P.selectedCount sa ((all_heights r (o P.shared) unit).1)
  have d := bounded P.added (15-P.selectedCount) se ((all_heights r (o P.added) unit).2.2.1)
  have box (A : Arm) (H : ℕ) (S : Sound A)
      (W : ((fence A:ℝ)-1)/1000*u^2 < (pair A H).1 ∧ (pair A H).2 < ((fence A:ℝ)+3)/1000*u^2) :
      796/1000*u^2 < (pair A H).1 ∧ (pair A H).2 < 922/1000*u^2 := by
    exact ⟨by nlinarith only [W.1,mul_le_mul_of_nonneg_right S.2.2.1 (sq_nonneg u)],
      by nlinarith only [W.2,mul_le_mul_of_nonneg_right S.2.2.2.1 (sq_nonneg u)]⟩
  have disjoint (A B : Arm) (H K : ℕ) (sep : fence A+4≤fence B)
      (X : (pair A H).2 < ((fence A:ℝ)+3)/1000*u^2)
      (Y : ((fence B:ℝ)-1)/1000*u^2 < (pair B K).1) :
      (pair A H).2 < (pair B K).1 := by
    have e : (fence A:ℝ)+4≤fence B := by exact_mod_cast sep
    nlinarith only [X,Y,mul_le_mul_of_nonneg_right e (sq_nonneg u)]
  refine ⟨box _ _ sa a,box _ _ sr b,box _ _ sa c,box _ _ se d,?_,?_⟩
  · rcases old with X|X
    · exact Or.inl (disjoint _ _ _ _ X a.2 b.1)
    · exact Or.inr (disjoint _ _ _ _ X b.2 a.1)
  · rcases new with X|X
    · exact Or.inl (disjoint _ _ _ _ X c.2 d.1)
    · exact Or.inr (disjoint _ _ _ _ X d.2 c.1)

/-- Number of integer smaller-factor positions in an open band. -/
noncomputable def sites (r : Fin 24) (A : Arm) (u : ℝ) (H : ℕ) :=
  let h := excess r A u H
  (Finset.Ioo ⌊low A u h⌋ ⌈high A u h⌉).card

private theorem count_error {l h : ℝ} (span : l≤h) :
    let count : ℝ := (Finset.Ioo ⌊l⌋ ⌈h⌉).card
    h-l-1≤count ∧ count≤h-l+1 := by
  rw [Int.card_Ioo]
  by_cases pos : 0≤⌈h⌉-⌊l⌋-1
  · have eq : (((⌈h⌉-⌊l⌋-1).toNat:ℕ):ℝ) = ((⌈h⌉:ℤ):ℝ)-⌊l⌋-1 := by
      exact_mod_cast Int.toNat_of_nonneg pos
    dsimp only
    rw [eq]
    exact ⟨by linarith only [Int.le_ceil h,Int.floor_le l],
      by linarith only [Int.ceil_lt_add_one h,Int.lt_floor_add_one l]⟩
  · have v : (⌈h⌉-⌊l⌋-1).toNat=0 := by omega
    have w : ((⌈h⌉:ℤ):ℝ) - ⌊l⌋ -1 < 0 := by exact_mod_cast lt_of_not_ge pos
    simp only [v,Nat.cast_zero]
    exact ⟨by linarith only [w,Int.le_ceil h,Int.floor_le l],by linarith only [span]⟩

/-- Rounding the four endpoints of either schedule still leaves a strict gain. -/
theorem integer_gain (r : Fin 24) (unit : (r:ℕ).Coprime 6) {u : ℝ} (big : 1000000≤u) :
    let P := schedule r
    sites r P.shared u P.previousCount + sites r P.removed u (15-P.previousCount) <
      sites r P.shared u P.selectedCount + sites r P.added u (15-P.selectedCount) := by
  let P := schedule r
  have E (A : Arm) (H : ℕ) : width r A u H-1 ≤ sites r A u H ∧
      (sites r A u H:ℝ)≤width r A u H+1 := by
    have span : low A u (excess r A u H) ≤ high A u (excess r A u H) := by
      unfold low high
      linarith only [mul_nonneg (show 0≤u by linarith only [big])
        (show 0≤normalized A u (excess r A u H) from sqrt_nonneg _)]
    have error := count_error span
    dsimp only at error
    rw [endpoint_width] at error
    exact error
  have gap := width_gain r unit big
  have g : (sites r P.shared u P.previousCount:ℝ) + sites r P.removed u (15-P.previousCount) <
      sites r P.shared u P.selectedCount + sites r P.added u (15-P.selectedCount) := by
    linarith only [gap,big,(E P.shared P.previousCount).2,(E P.removed (15-P.previousCount)).2,
      (E P.shared P.selectedCount).1,(E P.added (15-P.selectedCount)).1]
  exact_mod_cast g

/-- At the public equal-width product bin, all four weighted bands lie above
the rounded smaller-factor lower bound and below the shared ordinary prefix.
Combine with separated and integer_gain to count newly covered positions. -/
theorem slice {n : ℕ} {B : ℝ} (large : 10000≤B) (unit : n.Coprime 6)
    (lo : 9/16*B^2 ≤ n) (hi : (n:ℝ)≤5/8*B^2) (big : 1000000≤productRoot n) :
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let u := productRoot n
    max (B/2) (⌈(n:ℝ)/(B-1)⌉:ℤ) ≤ 796/1000*u^2 ∧
    922/1000*u^2 < u^2/endpoint u 1 (height r u 1 1 1 16) := by
  let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
  let u := productRoot n
  have tt : u^2=√(n:ℝ) := sq_sqrt (sqrt_nonneg _)
  have tn : (u^2)^2=(n:ℝ) := by rw [tt,sq_sqrt (by positivity)]
  have tlo : 3/4*B≤u^2 := le_of_sq_le_sq (by linarith only [lo,tn]) (sq_nonneg _)
  have Bp : 0<B := by linarith
  have thi : u^2≤791/1000*B := le_of_sq_le_sq (by nlinarith only [hi,tn,sq_nonneg B]) (by positivity)
  have ratio : u^2/(B-1)≤792/1000 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have product := mul_le_mul_of_nonneg_left ratio (sq_nonneg u)
  rw [show u^2*(u^2/(B-1))=(u^2)^2/(B-1) by ring,tn] at product
  have ru : (r:ℕ).Coprime 6 := by
    change (n%24).gcd 6=1
    rw [Nat.gcd_comm,Nat.gcd_rec,Nat.mod_mod_of_dvd _ (by decide : 6∣24),←Nat.gcd_rec,Nat.gcd_comm]
    exact unit
  have us : 100000≤u := by linarith only [big]
  have H := actual_heights r ru u
  have ord := (MarginalTraceWidth.separated us H).1
  have nested := ordinary_span us H
  dsimp only
  refine ⟨max_le (by linarith only [large,tlo])
    (by linarith only [Int.ceil_lt_add_one ((n:ℝ)/(B-1)),product,tlo,large]),?_⟩
  linarith only [ord,nested,sq_pos_of_pos (show 0<u by linarith only [big])]

/-- Direct 2048-bit specialization. The product alone determines the arms,
their counts, and their integer positions. -/
theorem full_size {n : ℕ} (hn : n.Coprime 6)
    (lo : 9/16*(2^1024:ℝ)^2 ≤ n) (hi : (n:ℝ)≤5/8*(2^1024:ℝ)^2) :
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let u := productRoot n
    let P := schedule r
    max ((2^1024:ℝ)/2) (⌈(n:ℝ)/(2^1024-1)⌉:ℤ) ≤ 796/1000*u^2 ∧
    922/1000*u^2 < u^2/endpoint u 1 (height r u 1 1 1 16) ∧
    sites r P.shared u P.previousCount + sites r P.removed u (15-P.previousCount) <
      sites r P.shared u P.selectedCount + sites r P.added u (15-P.selectedCount) := by
  let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
  let u := productRoot n
  have tt : u^2=√(n:ℝ) := sq_sqrt (sqrt_nonneg _)
  have tn : (u^2)^2=(n:ℝ) := by rw [tt,sq_sqrt (by positivity)]
  have big : 1000000≤u := by
    apply le_of_sq_le_sq _ (sqrt_nonneg _)
    apply le_of_sq_le_sq _ (sq_nonneg u)
    rw [tn]
    exact (by norm_num : ((1000000:ℝ)^2)^2 ≤ 9/16*(2^1024:ℝ)^2).trans lo
  have ru : (r:ℕ).Coprime 6 := by
    change (n%24).gcd 6=1
    rw [Nat.gcd_comm,Nat.gcd_rec,Nat.mod_mod_of_dvd _ (by decide : 6∣24),←Nat.gcd_rec,Nat.gcd_comm]
    exact hn
  obtain ⟨l,h⟩ := slice (by norm_num : (10000:ℝ)≤2^1024) hn lo hi big
  exact ⟨l,h,integer_gain r ru big⟩

end PrimeFactors.GeometryWeightMenu
