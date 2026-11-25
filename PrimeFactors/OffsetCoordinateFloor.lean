import PrimeFactors.OffsetWinnerWindow
import PrimeFactors.CompleteOffsetWork
import PrimeFactors.ChebyshevQuarticScale

namespace PrimeFactors.OffsetCoordinateFloor
open Finset

/-- Exactly the primitive pairs visited by the complete coordinate loop before
computing the trace interval or testing any arc. Pairs are ordered (s,v). -/
noncomputable def charts (T L K : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 K.sqrt).biUnion fun v =>
    ((Icc v (min (K/v) ((T*v+L-1)/L))).filter (fun s => s.Coprime v)).image (fun s => (s,v))

private def frame (m : ℕ) (point : ℕ × ℕ) : ℕ × ℕ :=
  ((m+1)*point.2+point.1,m*point.2+point.1)

/-- The quotient digit separates the images of neighboring unimodular
frames: the denominator b is recovered as s−v and m as (v−1)/b. -/
private theorem decode {b x : ℕ} (bp : 0<b) (xp : 0<x) (xb : x≤b) (m : ℕ) :
    (m*b+x-1)/b=m := by
  rw [Nat.add_sub_assoc xp,add_comm (m*b),Nat.add_mul_div_right _ _ bp,
    Nat.div_eq_of_lt (by omega : x-1<b),zero_add]

private theorem inject_frames {M U : ℕ} :
    Set.InjOn (fun z : ℕ × (ℕ × ℕ) => frame z.1 z.2)
      (↑(Icc 8 M ×ˢ FareyWork.primitiveOffsets U) : Set (ℕ × (ℕ × ℕ))) := by
  rintro ⟨m,x,b⟩ h₁ ⟨n,y,c⟩ h₂ same
  have left := mem_filter.mp (mem_product.mp h₁).2
  have right := mem_filter.mp (mem_product.mp h₂).2
  have bp : 0<b := (mem_Icc.mp (mem_product.mp left.1).2).1
  have xp : 0<x := (mem_Icc.mp (mem_product.mp left.1).1).1
  have yp : 0<y := (mem_Icc.mp (mem_product.mp right.1).1).1
  obtain ⟨s,v⟩ := Prod.mk.inj same
  change (m+1)*b+x=(n+1)*c+y at s
  change m*b+x=n*c+y at v
  simp only [Nat.add_mul,one_mul] at s
  have bc : b=c := by omega
  subst c
  have digit := congrArg (fun t : ℕ => (t-1)/b) v
  change (m*b+x-1)/b=(n*b+y-1)/b at digit
  rw [decode bp xp left.2.1,decode bp yp right.2.1] at digit
  subst n
  have xy : x=y := Nat.add_left_cancel v
  simp [xy]

theorem frame_mem {T L K U m : ℕ} (lp : 0<L) (wide : 9*L≤8*T) (base : 8≤m)
    (cap : ((m+2)*(m+1))*U^2≤K) {point : ℕ × ℕ}
    (inside : point∈FareyWork.primitiveOffsets U) : frame m point∈charts T L K := by
  obtain ⟨x,b⟩ := point
  obtain ⟨box,xb,primitive⟩ := mem_filter.mp inside
  obtain ⟨bp,bu⟩ := mem_Icc.mp (mem_product.mp box).2
  change 1≤b at bp
  change b≤U at bu
  change x≤b at xb
  change x.Coprime b at primitive
  let v := m*b+x
  let s := (m+1)*b+x
  have vp : 0<v := by have := Nat.mul_pos (show 0<m by omega) bp; dsimp [v]; omega
  have sv : s=b+v := by dsimp [s,v]; ring
  have vs : v≤s := by omega
  have cop : s.Coprime v := by
    rw [sv,Nat.coprime_add_self_left]
    change b.Coprime (m*b+x)
    rw [add_comm,Nat.coprime_add_mul_right_right]
    exact primitive.symm
  have ucap : x≤U := xb.trans bu
  have vcap : v≤(m+1)*U := by
    dsimp [v]; rw [Nat.add_mul,one_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left m bu) ucap
  have scap : s≤(m+2)*U := by
    rw [sv]; have a := Nat.add_le_add bu vcap; nlinarith only [a]
  have kcap : s*v≤K := calc
    s*v ≤ ((m+2)*U)*((m+1)*U) := Nat.mul_le_mul scap vcap
    _ = (m+2)*(m+1)*U^2 := by ring
    _ ≤ K := cap
  have lt : L≤T := by omega
  have broad : (m+1)*L≤m*T := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le base
    rw [hd]
    have more := Nat.mul_le_mul_left d lt
    nlinarith only [wide,more]
  have budget : L*s≤T*v := by
    have left := Nat.mul_le_mul_right b broad
    have right := Nat.mul_le_mul_right x lt
    dsimp [s,v]
    nlinarith only [left,right]
  have strict : L*(s-1)<T*v := by
    have pos : 0<s := vp.trans_le vs
    exact (Nat.mul_lt_mul_of_pos_left (Nat.sub_lt pos (by decide : 0<1)) lp).trans_le budget
  obtain ⟨svroot,prodCap,windowCap⟩ := OffsetWinnerWindow.loop_membership vp lp vs kcap strict
  exact mem_biUnion.mpr ⟨v,mem_Icc.mpr ⟨vp,svroot⟩,mem_image.mpr ⟨s,
    mem_filter.mpr ⟨mem_Icc.mpr ⟨vs,le_min prodCap windowCap⟩,cop⟩,rfl⟩⟩

/-- A family of disjoint frames inside the coordinate loop. The square
cutoff U is common to the frames and bounded using their largest digit. -/
theorem count {T L K U M : ℕ} (lp : 0<L) (wide : 9*L≤8*T)
    (cap : (M+2)*(M+1)*U^2≤K) : (M+1-8)*U^2≤8*(charts T L K).card := by
  let domain := Icc 8 M ×ˢ FareyWork.primitiveOffsets U
  have injection : domain.card≤(charts T L K).card := by
    apply card_le_card_of_injOn (fun z : ℕ × (ℕ × ℕ) => frame z.1 z.2) _ inject_frames
    rintro ⟨m,x,b⟩ inside
    obtain ⟨range,point⟩ := mem_product.mp inside
    obtain ⟨base,roof⟩ := mem_Icc.mp range
    apply frame_mem lp wide base _ point
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.add_le_add_right roof 2)
      (Nat.add_le_add_right roof 1))).trans cap
  dsimp [domain] at injection
  rw [card_product,Nat.card_Icc] at injection
  have lower := Nat.mul_le_mul_left (M+1-8) (FareyWork.primitive_count U)
  nlinarith only [lower,Nat.mul_le_mul_left 8 injection]

/-- The public lower factor bound for products of two 1,024-bit primes. -/
def lower1024 (n : ℕ) : ℕ :=
  let cap := 2^1024-1
  max (2^1023) ((n+cap-1)/cap)

noncomputable def shiftedCharts (n : ℕ) : Finset (ℕ × ℕ) :=
  let T := n.sqrt-1
  let H := n-T^2
  let K := T*CompleteOffsetWork.height H/H+1
  charts T (lower1024 n) K

private theorem control {n r j : ℕ}
    (root : r*r≤n ∧ n<(r+1)*(r+1)) (width : 9*lower1024 n≤8*(r-1))
    (height : let D := 4*(n-(r-1)^2)/3; j*j≤D ∧ D<(j+1)*(j+1))
    (roof : 156*((2:ℕ)^252)^2≤(r-1)*j/(n-(r-1)^2)+1) :
    2^503≤(shiftedCharts n).card := by
  have positive : 0<lower1024 n := (show 0<(2:ℕ)^1023 by decide +kernel).trans_le (le_max_left ..)
  have ans := count (M:=11) (U:=2^252) positive width roof
  have number : (11+1-8)*((2:ℕ)^252)^2=8*2^503 := by decide +kernel
  simp only [shiftedCharts,CompleteOffsetWork.height]
  rw [← Nat.eq_sqrt.mpr root,← Nat.eq_sqrt.mpr height]
  rw [number] at ans
  exact Nat.le_of_mul_le_mul_left ans (by decide)

/-- Lower bound for the full shifted coordinate loop on the fresh public product. -/
theorem fresh_floor : 2^503≤(shiftedCharts ChebyshevQuarticScale.fresh).card := by
  apply control (r:=158327039176966334715448284019718823474497913662177975160442996009439310669941017429676080400185006424773254142252582891257193029659269227070095120289800339855421063931472090621260003180611046788905349147963313017385074143012442899089952314244753217806428276920663827209779196401916113023989449483782760844629)
    (j:=24350873940639364334886801085192646652213503525186672085206397727635074574986121348349144341028626654802843595248922622201743210614999263828009557158942871) <;> decide +kernel

/-- Lower bound for the full shifted coordinate loop on the crossed public product. -/
theorem crossed_floor : 2^503≤(shiftedCharts ChebyshevQuarticScale.crossed).card := by
  apply control (r:=135037911685235586269825030135549325391376915966798636179319977077209993450011760943044181307768476527897818717675959823440307553022185653953812606479930673789391793187765141283074720630433120513417190939648203494531748575804685158519937612233285802863014656458801051235008057526662884995918450838938076904614)
    (j:=21534690790390421013056024285375526729526579810281161584549924242069624343778029068870474089933516289576023308315319402177062351872558724660017617861963271) <;> decide +kernel

end PrimeFactors.OffsetCoordinateFloor
