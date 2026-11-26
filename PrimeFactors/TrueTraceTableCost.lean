import PrimeFactors.TraceProgression
import PrimeFactors.Fermat
import PrimeFactors.ChebyshevQuarticScale

/-! Price of reaching the actual weighted sum in an initial segment of a
canonical trace progression. The charge counts a baby table of length m
and g consecutive giant blocks on one slope; they contain exactly m*g
labels. A modular coincidence at an earlier label is outside this model. -/

namespace PrimeFactors.TrueTraceTableCost

open TraceCoverCertificate

/-- At the least total budget (or any larger one), the two table dimensions
can differ by at most one. -/
theorem balanced_table {h M : ℕ} (bound : ceilSqrt (4*h) ≤ M) :
    ∃ m g : ℕ, m+g=M ∧ m ≤ g ∧ g ≤ m+1 ∧ h ≤ m*g := by
  have room := ceilSqrt_le_iff.mp bound
  obtain ⟨k,even|odd⟩ := Nat.even_or_odd' M
  · refine ⟨k,k,by omega,by omega,by omega,?_⟩
    rw [even, show (2*k)^2=4*(k*k) by ring] at room
    omega
  · refine ⟨k,k+1,by omega,by omega,by omega,?_⟩
    rw [odd, show (2*k+1)^2=4*(k*(k+1))+1 by ring] at room
    omega

/-- The exact total-budget threshold for covering the first h labels. -/
theorem table_budget_iff (h M : ℕ) :
    (∃ m g : ℕ, m+g ≤ M ∧ h ≤ m*g) ↔ ceilSqrt (4*h) ≤ M := by
  constructor
  · rintro ⟨m,g,total,room⟩
    have prod : 4*(m*g) ≤ (m+g)^2 := by
      nlinarith only [sq_nonneg ((m:ℤ)-g)]
    exact ceilSqrt_le_iff.mpr (((Nat.mul_le_mul_left 4 room).trans prod).trans
      (Nat.pow_le_pow_left total 2))
  · intro bound
    obtain ⟨m,g,total,_,_,room⟩ := balanced_table bound
    exact ⟨m,g,total.le,room⟩

/-- A catalogue may choose its slope with knowledge of the factors. The
smallest attained index gives the entire table-budget criterion. -/
theorem least_index_budget {α : Type*} {pool : Set α} {index : α → ℕ}
    {winner : α} (enters : winner∈pool) (best : ∀ a∈pool, index winner ≤ index a)
    (M : ℕ) :
    (∃ m g : ℕ, m+g ≤ M ∧ ∃ a∈pool, index a<m*g) ↔
      ceilSqrt (4*(index winner+1)) ≤ M := by
  rw [←table_budget_iff]
  constructor
  · rintro ⟨m,g,total,a,member,hit⟩
    exact ⟨m,g,total,(best a member).trans_lt hit⟩
  · rintro ⟨m,g,total,room⟩
    exact ⟨m,g,total,winner,enters,room⟩

/-- Some reduced catalogue row reaches the true sum, allowing every canonical
start with the verified residue, lower square and predecessor square. Both
assignments of the weights to the two factors are allowed. -/
def Reaches (K p q m g : ℕ) : Prop :=
  ∃ s : Slope, (s.a,s.b)∈catalogueCoordinates K ∧ validStart (p*q) s ∧
    ∃ j<m*g, s.start+s.step*j=s.a*p+s.b*q ∨ s.start+s.step*j=s.a*q+s.b*p

/-- T-d*i is still at or above the geometric minimum. For an attained
trace T=z+d*j, where z is the first valid label, this implies i ≤ j. -/
private theorem index_lower {T z d A i j : ℕ} (hit : z+d*j=T)
    (prev : z<d ∨ (z-d)^2<A) (under : d*i ≤ T) (square : A ≤ (T-d*i)^2) : i ≤ j := by
  by_contra! smaller
  have step := Nat.mul_le_mul_left d (show j+1 ≤ i by omega)
  rw [Nat.mul_add,Nat.mul_one] at step
  rcases prev with small | before
  · omega
  · have := Nat.pow_le_pow_left (show T-d*i ≤ z-d by omega) 2
    omega

private def lowerTest (p q i a b : ℕ) : Bool :=
  let S := a*p+b*q
  let d := weightedStride (p*q) a b
  decide (d*i ≤ S ∧ 4*a*b*(p*q) ≤ (S-d*i)^2)

private def winnerRow (p q i a b : ℕ) : Slope :=
  let d := weightedStride (p*q) a b
  ⟨a,b,a*p+b*q-d*i,d⟩

/-- Compressed exact-price certificate. Every slope checks the single proposed
minimum index. The winning row also checks its predecessor and residue. -/
private theorem reached_iff {K p q i a b : ℕ}
    (ordered : p ≤ q)
    (allRows : (catalogueCoordinates K).all (fun uv => lowerTest p q i uv.1 uv.2))
    (member : (a,b)∈catalogueCoordinates K)
    (first : validStart (p*q) (winnerRow p q i a b)) (m g : ℕ) :
    Reaches K p q m g ↔ i+1 ≤ m*g := by
  have lower {u v} (mem : (u,v)∈catalogueCoordinates K) :
      weightedStride (p*q) u v*i ≤ u*p+v*q ∧
      4*u*v*(p*q) ≤ (u*p+v*q-weightedStride (p*q) u v*i)^2 :=
    of_decide_eq_true (List.all_eq_true.mp allRows (u,v) mem)
  constructor
  · rintro ⟨s,mem,valid,j,hj,hit⟩
    obtain ⟨_,step,_,_,prev⟩ := of_decide_eq_true valid
    obtain ⟨under,square⟩ := lower mem
    rw [←step] at under square
    rcases hit with direct | swapped
    · exact (index_lower direct prev under square).trans_lt hj
    · have ab := (coordinate_mem.mp mem).2.2.1
      have compare : s.a*p+s.b*q ≤ s.a*q+s.b*p := by
        nlinarith only [mul_nonneg (show 0 ≤ (s.a:ℤ)-s.b by omega) (show 0 ≤ (q:ℤ)-p by omega)]
      have squares := Nat.pow_le_pow_left (Nat.sub_le_sub_right compare (s.step*i)) 2
      exact (index_lower swapped prev (under.trans compare) (square.trans squares)).trans_lt hj
  · intro room
    refine ⟨winnerRow p q i a b,member,first,i,room,?_⟩
    exact Or.inl (Nat.sub_add_cancel (lower member).1)

/-- The exact index, the row attaining it and the catalogue-wide lower
bound. Row indices start at zero. -/
def BestIndex (K p q i a b : ℕ) : Prop :=
  (∀ m g, Reaches K p q m g ↔ i+1 ≤ m*g) ∧
    ∃ s : Slope, s.a=a ∧ s.b=b ∧ (a,b)∈catalogueCoordinates K ∧
      validStart (p*q) s ∧ s.start+s.step*i=a*p+b*q

private theorem best_checked {K p q i a b : ℕ}
    (ordered : p ≤ q)
    (allRows : (catalogueCoordinates K).all (fun uv => lowerTest p q i uv.1 uv.2))
    (member : (a,b)∈catalogueCoordinates K)
    (first : validStart (p*q) (winnerRow p q i a b)) :
    BestIndex K p q i a b := by
  refine ⟨reached_iff ordered allRows member first,winnerRow p q i a b,rfl,rfl,member,first,?_⟩
  have room : weightedStride (p*q) a b*i ≤ a*p+b*q ∧ _ :=
    of_decide_eq_true (List.all_eq_true.mp allRows (a,b) member)
  exact Nat.sub_add_cancel room.1

/-- M is the least possible sum of the two table dimensions. -/
def ExactPrice (K p q M : ℕ) : Prop :=
  ∀ budget, (∃ m g : ℕ, m+g ≤ budget ∧ Reaches K p q m g) ↔ M ≤ budget

private theorem price_checked {K p q i a b M : ℕ}
    (proved : BestIndex K p q i a b)
    (lower : (M-1)^2<4*(i+1)) (upper : 4*(i+1) ≤ M^2) :
    ExactPrice K p q M := by
  have root : ceilSqrt (4*(i+1))=M := by
    apply le_antisymm (ceilSqrt_le_iff.mpr upper)
    by_contra! small
    have tooLow := ceilSqrt_le_iff.mp (show ceilSqrt (4*(i+1)) ≤ M-1 by omega)
    omega
  intro budget
  simp only [proved.1,table_budget_iff,root]

/-- Smaller certified factor. -/
def freshP : ℕ :=
  155437199607556058012532697390816360200993450617775861977793885503041330648186435254461734869213045968256605640509036134253515311588040219325256786085481113217401073894164916964759494475637984845596500869609803951359509506709556269999261634541514057554539876849500776006036129784966133839608344624969272353567

/-- Larger certified factor. -/
def freshQ : ℕ :=
  161270605735527305106073331997188600389811486601036205205001425727786078300416814134106878399348029233962121752237344825423608369752978864046063434777553854865105371574916603604640605082441946447462046466208739893141681020415078708986222758892913779726834240750726240518693682341337270830209012662338065799537

/-- Least attained zero-based label index. -/
def freshI : ℕ :=
  6715873643836710963682668570914205226138736807014607738664901493598451090151816152056558523882794084027388530151897145342202752810078653891247535429286046458039700767167415860011649607229714405981129986489726216380280137468647600697470618115175208564695469862420263146427415308897327729807289967727057980

/-- Least possible table-plus-block charge. -/
def freshM : ℕ :=
  163900868134817528350596985041875431332186285417741663029457559886250424123335277012951398755833263528452131986466051075815714189331974503127544763448123

/-- The attaining weights, exact label index and lower bound on every row. -/
theorem fresh_index : BestIndex 8 freshP freshQ freshI 1 1 := by
  apply best_checked
  all_goals decide +kernel

/-- Retrospective price across the complete K=8 catalogue. The minimizing
weights are (1,1). The prior independent prime certificates are
the recursive Pocklington chains in benchmarks/controls/PocklingtonControl.lean. -/
theorem fresh_price :
    freshP*freshQ=ChebyshevQuarticScale.fresh ∧
    ExactPrice 8 freshP freshQ freshM := by
  refine ⟨by decide +kernel,?_⟩
  apply price_checked fresh_index
  all_goals decide +kernel

/-- Smaller certified factor. -/
def crossedP : ℕ :=
  112441117597005507953302714561413417518796533972742569875368211967290010067619061196617791973932104346183757482183516464238353350334638255926060911354549114328226549291121357839031716121854438648697694663627230333137863905814077048887609386383765457047190918933920371080593625356668075932061615063557912657921

/-- Larger certified factor. -/
def crossedQ : ℕ :=
  162175883538133029802291489124241622288267787047767787619968522876469755952252006712021489496357385664202411123611087501740545115604806677668534291518891839981872791402271917271711941951294673034733692968395258952798139520796019241828276619087706598664711444552563048153081122472506776073806036274013471244289

/-- Least attained zero-based label index. -/
def crossedI : ℕ :=
  7380096819849871715369447423263456575968439862175354734678788249877478482282830285337227845360044853307905335879901020418109603634330507015510888343979583059560607242344254113629226015103947913804337057662249162688380874263386320652438085211665129818314335033633726249623041105872158035624648824869157696

/-- Least possible table-plus-block charge. -/
def crossedM : ℕ :=
  171814979787559521341930816278604688535110941129341746511096547550813162345936340765243654535458674832690082864160339439699243582277123199636806435737875

/-- The attaining weights, exact label index and lower bound on every row. -/
theorem crossed_index : BestIndex 8 crossedP crossedQ crossedI 7 5 := by
  apply best_checked
  all_goals decide +kernel

/-- Retrospective price across the complete K=8 catalogue. The minimizing
weights are (7,5). The prior independent prime certificates are
the published unit-quartic-crossed-2048.lean factor certificate. -/
theorem crossed_price :
    crossedP*crossedQ=ChebyshevQuarticScale.crossed ∧
    ExactPrice 8 crossedP crossedQ crossedM := by
  refine ⟨by decide +kernel,?_⟩
  apply price_checked crossed_index
  all_goals decide +kernel

end PrimeFactors.TrueTraceTableCost
