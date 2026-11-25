import PrimeFactors.OffsetGlobalArcs
import PrimeFactors.ShiftedOffsetBase
import PrimeFactors.OffsetCoordinateGaps

namespace PrimeFactors.TargetArcSchedule
open OffsetGlobalArcs CompleteOffsetSearch

set_option exponentiation.threshold 4096
set_option maxRecDepth 10000

/-- One coordinate and one arc. Each arc is charged once per orientation,
independently of which positions on it are occupied. -/
abbrev Address (na nb : ℕ) := Σ a : Fin na,
  (Fin (2^a.val) × Fin (2^(a.val+2))) × (Unit ⊕ (Σ b : Fin nb, Fin (2^(b.val-chunkExp a.val b.val))))

theorem address_count (na nb : ℕ) : 2*Fintype.card (Address na nb) = total na nb := by
  unfold Address total
  congr 1
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun i => 2^i*2^(i+2)*(1+∑ b : Fin nb, 2^(b.val-chunkExp i b.val)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fin.sum_univ_eq_sum_range (fun b => 2^(b-chunkExp a b)), Nat.mul_add, Nat.mul_one, Finset.mul_sum]
  rw [←pow_add]
  have ex : a+(a+2)=2*a+2 := by omega
  rw [ex]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact (pow_add 2 (2*a+2) (b-chunkExp a b)).symm

/-- Sharper shifted-base caps allow 256 coordinate bins and 513 parity-index bins. -/
theorem target_count : 2*Fintype.card (Address 256 513) < 2^692 := by
  rw [address_count]
  exact (geometric_total (m:=257) (by decide) (by decide) (by decide)).trans_lt (by decide +kernel)

/-- Public first positive parity-compatible offset with nonnegative discriminant. -/
def Admissible (N T s v j : ℕ) : Prop :=
  0<j ∧ j%2=(s+v)%2 ∧ 4*N*(s*v)^2≤(2*T*(s*v)+j)^2

noncomputable instance (N T s v : ℕ) : DecidablePred (Admissible N T s v) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem exists_first (N T s v : ℕ) : ∃ j, Admissible N T s v j := by
  let P := 4*N*(s*v)^2
  let j := 2*(P+1)+(s+v)%2
  refine ⟨j,by dsimp [j]; omega,by dsimp [j]; omega,?_⟩
  apply le_trans _ (Nat.le_self_pow (by decide : 2≠0) _)
  change P≤2*T*(s*v)+j
  dsimp [j]
  omega

noncomputable def first (N T s v : ℕ) := Nat.find (exists_first N T s v)

theorem first_spec (N T s v : ℕ) : Admissible N T s v (first N T s v) :=
  Nat.find_spec (exists_first N T s v)

theorem first_min {N T s v j : ℕ} (good : Admissible N T s v j) : first N T s v≤j :=
  Nat.find_min' (exists_first N T s v) good

def vCoord {na nb : ℕ} (d : Address na nb) : ℕ := 2^d.1.val+d.2.1.1.val
def sCoord {na nb : ℕ} (d : Address na nb) : ℕ := d.2.1.2.val

def startIndex {na nb : ℕ} (d : Address na nb) : ℕ :=
  match d.2.2 with
  | .inl _ => 0
  | .inr ⟨b,c⟩ => 2^b.val+c.val*2^(chunkExp d.1.val b.val)

def width {na nb : ℕ} (d : Address na nb) : ℕ :=
  match d.2.2 with
  | .inl _ => 0
  | .inr ⟨b,_⟩ => 2^(chunkExp d.1.val b.val)-1

/-- The root at the first index of this arc determines at most one line for
each signed residue progression. A width-zero arc is a direct point test. -/
def OneLine (N T : ℕ) (d : Address 256 513) : Prop :=
  let k := sCoord d*vCoord d
  let S := 2*T*k+first N T (sCoord d) (vCoord d)+2*startIndex d
  width d=0 ∨ ∀ r β : ℤ, ∃ (q : ℕ) (p t : ℤ), 1≤q ∧ q≤2*width d ∧ ∀ x y w : ℤ,
    0≤x → x≤width d → 0≤w → w=r+β*x+((4*k^2:ℕ):ℤ)*y →
    w^2=((S:ℤ)+2*x)^2-((4*N*k^2:ℕ):ℤ) → (q:ℤ)*y-p*x=t

/-- Public tests before charging a line. They can discard the unused rectangle
coordinates and every chunk which starts past the sharp height. -/
def Active (N : ℕ) (d : Address 256 513) : Prop :=
  let T := N.sqrt-1
  let H := N-T^2
  let J := CompleteOffsetWork.height H
  let s := sCoord d
  let v := vCoord d
  v≤s ∧ s≤2*v ∧ s.Coprime v ∧ s*v≤T*J/H+1 ∧ first N T s v+2*startIndex d≤J

theorem active_one_line {N : ℕ} (lo : 2^1022≤N.sqrt-1) (hi : N.sqrt-1≤2^1024)
    (nmax : N≤2^2048) (jmax : CompleteOffsetWork.height (N-(N.sqrt-1)^2)≤2^515)
    (d : Address 256 513) (active : Active N d) : OneLine N (N.sqrt-1) d := by
  let T := N.sqrt-1
  let s := sCoord d
  let v := vCoord d
  let k := s*v
  let j₀ := first N T s v
  let A := 2*T*k+j₀
  by_cases single : width d=0
  · exact Or.inl single
  right
  intro R B
  obtain ⟨a,coords,kind⟩ := d
  cases kind with
  | inl _ => exact (single rfl).elim
  | inr sub =>
    obtain ⟨b,c⟩ := sub
    let d : Address 256 513 := ⟨a,coords,.inr ⟨b,c⟩⟩
    let I := startIndex d
    have in_bin : 2^a.val≤v := Nat.le_add_right _ _
    have ordered : v≤s := active.1
    have scale : 2^(2*a.val)≤k := by
      rw [show 2*a.val=a.val+a.val by omega,pow_add]
      exact Nat.mul_le_mul (in_bin.trans ordered) in_bin
    have height_cap : j₀+2*I≤2^515 := active.2.2.2.2.trans jmax
    have dw : width d=2^(chunkExp a.val b.val)-1 := rfl
    apply chunk_line (a:=a.val) (b:=b.val) (T:=T) (i:=I) (k:=k) (A:=A) (j:=j₀+2*I) R B lo hi nmax
      height_cap scale (by dsimp [A]; nlinarith only [Nat.zero_le (T*k),Nat.zero_le j₀])
      (first_spec N T s v).2.2 (by dsimp [A]; omega)
      (Nat.le_add_right (2^b.val) _) (Nat.pos_of_ne_zero single)
    change width d<2^(chunkExp a.val b.val)
    have := Nat.two_pow_pos (chunkExp a.val b.val)
    omega

private theorem located {N T j s v : ℕ} (good : Admissible N T s v j)
    (vp : 0<v) (small : v<2^256) (order : v≤s) (aspect : s≤2*v)
    (jc : j<3*2^512) :
    ∃ d : Address 256 513, ∃ x≤width d, sCoord d=s ∧ vCoord d=v ∧
      j=first N T s v+2*(startIndex d+x) := by
  let j₀ := first N T s v
  have good₀ := first_spec N T s v
  have low := first_min good
  let i := (j-j₀)/2
  have repr : j=j₀+2*i := by
    have par := good.2.1
    have par₀ := good₀.2.1
    dsimp [i,j₀]
    omega
  have ic : i<2^513 := by omega
  obtain ⟨a,al,vl,vr⟩ := dyadic_bin vp small
  obtain ⟨vbin,sbin,_⟩ := coordinate_bin vl vr (by omega : s≤2*v+1) order
  let coords : Fin (2^a) × Fin (2^(a+2)) := (⟨v-2^a,vbin⟩,⟨s,sbin⟩)
  have back : 2^a+(v-2^a)=v := by omega
  by_cases zero : i=0
  · let d : Address 256 513 := ⟨⟨a,al⟩,coords,.inl ()⟩
    exact ⟨d,0,Nat.zero_le _,rfl,back,by simpa [d,startIndex,zero] using repr⟩
  obtain ⟨b,bl,il,ir⟩ := dyadic_bin (Nat.pos_of_ne_zero zero) ic
  obtain ⟨c,cc,r,rc,pos⟩ := partition (a:=a) il ir
  let d : Address 256 513 := ⟨⟨a,al⟩,coords,.inr ⟨⟨b,bl⟩,⟨c,cc⟩⟩⟩
  let I := 2^b+c*2^(chunkExp a b)
  have stamp : i=I+r := pos
  have dw : width d=2^(chunkExp a b)-1 := rfl
  exact ⟨d,r,by omega,rfl,back,by change j=j₀+2*(I+r); omega⟩

/-- This integer-square-root readout computes the least offset without enumerating
its predecessors. The parity correction is either zero or one. -/
theorem first_formula {N T s v : ℕ} (np : 0<N) (kp : 0<s*v) :
    let m := max 1 (((4*N*(s*v)^2-1).sqrt+1)-(2*T*(s*v)))
    first N T s v = if m%2=(s+v)%2 then m else m+1 := by
  intro m
  let P := 4*N*(s*v)^2
  have pp : 0<P := by dsimp [P]; positivity
  have threshold (j : ℕ) : m≤j ↔ 0<j ∧ P≤(2*T*(s*v)+j)^2 := by
    change max 1 ((P-1).sqrt+1-2*T*(s*v))≤j ↔ _
    rw [max_le_iff]
    have cut := Nat.sqrt_lt' (m:=P-1) (n:=2*T*(s*v)+j)
    omega
  have ok := first_spec N T s v
  have mmin := (threshold _).mpr ⟨ok.1,ok.2.2⟩
  split
  next eq => exact Nat.le_antisymm (first_min ⟨((threshold m).mp le_rfl).1,eq,((threshold m).mp le_rfl).2⟩) mmin
  next ne =>
    obtain ⟨pos,disc⟩ := (threshold (m+1)).mp (by omega)
    have congr := ok.2.1
    exact Nat.le_antisymm (first_min ⟨pos,by omega,disc⟩) (by omega)

private theorem adm_of_label {p q T j s v : ℕ} (po : Odd p) (qo : Odd q)
    (pos : 0<j) (label : j+2*T*(s*v)=p*s^2+q*v^2) : Admissible (p*q) T s v j := by
  have mp : p%2=1 := Nat.odd_iff.mp po
  have mq : q%2=1 := Nat.odd_iff.mp qo
  have sq2 (n : ℕ) : n^2%2=n%2 := by
    rw [Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one n with h|h <;> simp [h]
  have par := congrArg (·%2) label
  dsimp only at par
  rw [Nat.add_mod,show (2*T*(s*v))%2=0 by simp [Nat.mul_assoc],Nat.add_zero,Nat.mod_mod,
    Nat.add_mod, Nat.mul_mod p, Nat.mul_mod q, mp,mq,one_mul,one_mul,
    Nat.mod_mod,Nat.mod_mod,sq2,sq2,←Nat.add_mod] at par
  refine ⟨pos,par,?_⟩
  rw [Nat.add_comm (2*T*(s*v)) j,label]
  exact_mod_cast (show (4:ℤ)*(p*q)*(s*v)^2≤(p*s^2+q*v^2)^2 by
    nlinarith only [sq_nonneg ((p:ℤ)*s^2-(q:ℤ)*v^2)])

/-- At the beginning of a chunk the projector gives the residue of the signed gap.
The intercept and slope use only the coordinates, trace and a Bézout projector. -/
def residue (s v : ℕ) (e S : ℤ) : ℤ :=
  (s:ℤ)^2-v^2+(1-2*e)*(S-s^2-v^2)

/-- The actual nonnegative square root belongs to one of exactly two orientations.
This identifies the point to which the universal line in OneLine applies. -/
def SquarePoint (N s v : ℕ) (S : ℤ) (x : ℕ) : Prop :=
  ∀ e u h : ℤ, e=(v:ℤ)^2*u → 1-e=(s:ℤ)^2*h →
    ∃ σ y z : ℤ, (σ=1 ∨ σ= -1) ∧ 0≤z ∧
      z=σ*residue s v e S+(σ*(2*(1-2*e)))*x+((4*(s*v)^2:ℕ):ℤ)*y ∧
      z^2=(S+2*x)^2-((4*N*(s*v)^2:ℕ):ℤ)

private theorem point_of_label {p q s v x : ℕ} {S : ℤ} (po : Odd p) (qo : Odd q)
    (trace : S+2*x=(p:ℤ)*s^2+(q:ℤ)*v^2) : SquarePoint (p*q) s v S x := by
  intro e u h ev es
  obtain ⟨a,ha⟩ := po
  obtain ⟨b,hb⟩ := qo
  have hp : (p:ℤ)=2*a+1 := by exact_mod_cast ha
  have hq : (q:ℤ)=2*b+1 := by exact_mod_cast hb
  have pr : (2:ℤ)∣(p:ℤ)-1 := ⟨a,by omega⟩
  have qr : (2:ℤ)∣(q:ℤ)-1 := ⟨b,by omega⟩
  obtain ⟨y,ye⟩ := OffsetCoordinateGaps.signed_gap ev es pr qr trace
  let z := (p:ℤ)*s^2-(q:ℤ)*v^2
  have sq : z^2=(S+2*x)^2-((4*(p*q)*(s*v)^2:ℕ):ℤ) := by
    rw [trace]
    dsimp [z]
    push_cast
    ring
  have matchGap : z=residue s v e S+(2*(1-2*e))*x+((4*(s*v)^2:ℕ):ℤ)*y := by
    unfold z residue
    push_cast
    linear_combination ye
  by_cases zp : 0≤z
  · exact ⟨1,y,z,Or.inl rfl,zp,by simpa using matchGap,sq⟩
  · exact ⟨-1,-y,-z,Or.inr rfl,by omega,by linear_combination -matchGap,by nlinarith only [sq]⟩

/-- A successful address has public index, offset and multiplier bounds, a
primitive coordinate pair and a directly recoverable proper divisor. -/
def Found (N f : ℕ) : Prop :=
  let T := N.sqrt-1
  let H := N-T^2
  ∃ d : Address 256 513, ∃ x≤width d,
    let s := sCoord d
    let v := vCoord d
    let k := s*v
    let j := first N T s v+2*(startIndex d+x)
    Active N d ∧ 0<v ∧ v≤s ∧ s≤2*v ∧ s.Coprime v ∧ j≤CompleteOffsetWork.height H ∧
      k≤T*CompleteOffsetWork.height H/H+1 ∧ InSchedule T H j k ∧
      OneLine N T d ∧ SquarePoint N s v (2*(T:ℤ)*k+first N T s v+2*startIndex d) x ∧
      probe N T j k=some f

private theorem ordered {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (pbits : 2^1023≤p ∧ p<2^1024) (qbits : 2^1023≤q ∧ q<2^1024) :
    (∀ d, Active (p*q) d → OneLine (p*q) ((p*q).sqrt-1) d) ∧
      ∃ f, (f=p ∨ f=q) ∧ Found (p*q) f := by
  let N := p*q
  let T := N.sqrt-1
  let H := N-T^2
  have balance : q≤2*p := by
    have : (2:ℕ)^1024=2*2^1023 := by decide +kernel
    omega
  have big : 17≤p := (show 17≤(2:ℕ)^1023 by decide +kernel).trans pbits.1
  have nmax : N<2^2048 := by
    have h := Nat.mul_lt_mul_of_lt_of_le pbits.2 qbits.2.le (show 0<(2:ℕ)^1024 by decide +kernel)
    exact h
  have pr : p≤N.sqrt := Nat.le_sqrt'.mpr (by simpa [N,pow_two] using Nat.mul_le_mul_left p ord.le)
  have tlo : 2^1022≤T := by dsimp [T]; omega
  have top : T<2^1024 := by
    have rt : N.sqrt<2^1024 := Nat.sqrt_lt'.mpr (by exact nmax)
    dsimp [T]; omega
  have off := (balanced_parameters pp qp ord balance big).2.1
  change 0<N-N.sqrt^2 at off
  obtain ⟨_,lower,upper⟩ := ShiftedOffsetBase.parameters (n:=N) (by omega) (by omega)
  have limits := ShiftedOffsetBase.bits2048 (T:=T) (H:=H) top (by omega) lower upper
  dsimp only at limits
  have fullHeight : CompleteOffsetWork.height H≤2^515 := by omega
  refine ⟨active_one_line (N:=N) tlo top.le nmax.le fullHeight,?_⟩
  obtain ⟨j,s,v,vp,order,aspect,prim,label,sharp,dom,hit⟩ := ShiftedOffsetBase.complete_balanced pp qp ord balance big
  change InSchedule T H j (s*v) at dom
  change 3*j^2≤4*H at sharp
  have smallJ : j≤CompleteOffsetWork.height H :=
    Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide : 0<3)).mpr (by omega))
  have smallK : s*v≤T*CompleteOffsetWork.height H/H+1 :=
    dom.2.2.2.1.trans (Nat.succ_le_succ (Nat.div_le_div_right (Nat.mul_le_mul_left _ smallJ)))
  have vc : v<2^256 := v_limit order (smallK.trans_lt limits.2)
  have good := adm_of_label (pp.odd_of_ne_two (by omega)) (qp.odd_of_ne_two (by omega)) dom.1 label
  obtain ⟨d,x,within,sd,vd,offset⟩ := located good vp vc order aspect (smallJ.trans_lt limits.1)
  change j=first N T s v+2*(startIndex d+x) at offset
  have finish (f : ℕ) (h : probe N T j (s*v)=some f) : Found N f := by
    refine ⟨d,x,within,?_⟩
    dsimp only
    rw [sd,vd,←offset]
    have active : Active N d := by
      dsimp only [Active]
      rw [sd,vd]
      exact ⟨order,aspect,prim,smallK,by change first N T s v+2*startIndex d≤CompleteOffsetWork.height H; omega⟩
    refine ⟨active,vp,order,aspect,prim,smallJ,smallK,dom,
      active_one_line (N:=N) tlo top.le nmax.le fullHeight d active,?_,h⟩
    apply point_of_label (pp.odd_of_ne_two (by omega)) (qp.odd_of_ne_two (by omega))
    have gap : j+2*T*(s*v)=p*s^2+q*v^2 := label
    rw [offset] at gap
    have expr : 2*T*(s*v)+first N T s v+2*startIndex d+2*x=p*s^2+q*v^2 := by
      nlinarith only [gap]
    exact_mod_cast expr
  rcases hit with h|h
  · exact ⟨p,Or.inl rfl,finish p h⟩
  · exact ⟨q,Or.inr rfl,finish q h⟩

/-- For distinct 1,024-bit primes, in either order, the public signed arc
schedule contains a factor and charges fewer than 2^692 line or singleton tests. -/
theorem covers_target {N p q : ℕ} (pair : p*q=N) (pp : p.Prime) (qp : q.Prime) (distinct : p≠q)
    (pbits : 2^1023≤p ∧ p<2^1024) (qbits : 2^1023≤q ∧ q<2^1024) :
    2*Fintype.card (Address 256 513)<2^692 ∧ (∀ d, Active N d → OneLine N (N.sqrt-1) d) ∧
      ∃ f, (f=p ∨ f=q) ∧ Found N f := by
  refine ⟨target_count,?_⟩
  rcases lt_or_gt_of_ne distinct with lt|lt
  · simpa only [pair] using ordered pp qp lt pbits qbits
  · have rev : q*p=N := (Nat.mul_comm ..).trans pair
    obtain ⟨all,f,h,found⟩ := ordered qp pp lt qbits pbits
    exact ⟨rev ▸ all,f,h.symm,rev ▸ found⟩

end PrimeFactors.TargetArcSchedule
