import PrimeFactors.PairDeterminant

namespace PrimeFactors.PlantedHeightExample

set_option exponentiation.threshold 2048

/-- The constructed product used by the multiplier-24 benchmark. -/
def N : ℕ := 16787391552540980919361938531147976673853202492779629718236560478981685486694034702925163156221405883839017279586592568895830216473342615436528971039351442721277112369043338858269268996285264282474579117195515386192776263410431214181076152612437518871640452479385738575063551669988691102411818573664168048605671523643905913578222780306075477304189965983833870705940866794442606239115536030880548129434790038465610562965698608796474223270304117024061404722958822579537118488781464618791936289954693808838348245126242022065622021982670975570046634287683674360698359594884668182502089078631212301788938585144511430656001

def smallerFactor : ℕ := 105790332111968785265293824204621891710913208191503497667320230349832740942537675238435003136368785077691880188693820024461046767731255566223604676753745475361514022681786531850388550074657355396259717407402691631645562749513449996124774253377717154050106182684349383285306435324691685852277536777994397286401

def largerFactor : ℕ := 158685498167953177897940736306932837566369812287255246500980345524749111413806512857652504704553177616537820283040730036691570151596883349335407015130618213042271034022679797775582825111986033094389576111104037447468344124270174994187161380066575731075159274026524074927959652987037528778416305166991595929601

def midpoint : ℕ := 634741992671812711591762945227731350265479249149020986003921382098996445655226051430610018818212710466151281132162920146766280606387533397341628060522472852169084136090719191102331300447944132377558304444416149789873376497080699976748645520266302924300637096106096299711838611948150115113665220667966383718405

private def approximateRoot (n : ℕ) : ℕ → ℕ
  | 0 => 2^1028
  | i+1 => let x := approximateRoot n i; (x+n/x)/2

/-- Each candidate root is certified by integer multiplication on both sides;
Newton updates supply compact witnesses for the 23 floor square roots. -/
private theorem checked_windows : ∀ i : Fin 23,
    let m := (i.val+1)*N
    let x := approximateRoot m 13
    x^2 ≤ m ∧ m+2^1022 ≤ (x+1)^2 := by decide +kernel

/-- The first square above each of the first 23 positive multiples is at
least 2^1022 away. -/
theorem gaps {k : ℕ} (pos : 0<k) (small : k<24) :
    k*N+2^1022 ≤ ((k*N).sqrt+1)^2 := by
  have h := checked_windows ⟨k-1,by omega⟩
  have hk : k-1+1=k := by omega
  simp only [hk] at h
  have exact_root : approximateRoot (k*N) 13 = (k*N).sqrt :=
    Nat.eq_sqrt'.mpr ⟨h.1,by omega⟩
  exact (congrArg (fun t : ℕ => k*N+2^1022 ≤ (t+1)^2) exact_root).mp h.2

/-- No two normalized switched rows with a height cap of 48 on one row
and the strict shortness bound on its partner can yield a factor. -/
theorem no_height_48 {g k u v : ℕ} (gp : 0<g) (kp : 0<k) (vp : 0<v)
    (norm : u^2=v^2+k*N) : ¬ 2*g^2*u^2*v^2<N*48 := by
  intro h
  obtain ⟨size,first⟩ := PairDeterminant.short_row gp kp vp norm h (by decide)
  have vp2 : 1 ≤ v^2 := pow_pos vp 2
  have low : 2*k ≤ 2*k*v^2 := Nat.le_mul_of_pos_right _ vp2
  have huge := gaps kp (by omega)
  rw [← first,norm] at huge
  have small : v^2 ≤ 2*k*v^2 := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- A and B are the absolute row heights. U and V are their ordered cross
products. These conditions follow from any qualifying primitive pair. -/
theorem row_height_floor {A B U V z : ℕ} (vp : 0<V) (ordered : V<U)
    (same : V ≡ U [MOD N]) (unit : U.Coprime N) (square : U*V=z^2)
    (heights : A*B=U*V) (ha : 2*A<N) (hb : 2*B<N) : 49 ≤ A ∧ 49 ≤ B := by
  obtain ⟨h,hh⟩ := (Nat.modEq_iff_dvd' ordered.le).mp same
  have det : U=V+h*N := by rw [Nat.mul_comm] at hh; omega
  have sp : (2*z)^2 < N^2 := by
    calc
      _ = (2*A)*(2*B) := by rw [mul_pow,←square,←heights]; ring
      _ ≤ N*(2*B) := Nat.mul_le_mul_right _ ha.le
      _ < N^2 := by simpa only [sq] using Nat.mul_lt_mul_of_pos_left hb (by decide : 0<N)
  have short : 2*z < N := lt_of_not_ge fun bad =>
    (Nat.not_le_of_lt sp) (Nat.pow_le_pow_left bad 2)
  obtain ⟨k,u,v,_,hU,hV,_,vpos,lt,norm,_⟩ := PairDeterminant.normalize vp ordered det unit square short
  have kp : 0 < k := by
    by_contra! bad
    have := Nat.pow_lt_pow_left lt (by decide : 2 ≠ 0)
    simp [Nat.eq_zero_of_le_zero bad] at norm
    omega
  have floor (a b : ℕ) (prod : a*b=U*V) (partner : 2*b<N) : 49 ≤ a := by
    by_contra! low
    apply no_height_48 (Nat.gcd_pos_of_pos_left V (vp.trans ordered)) kp vpos norm
    calc
      _ = 2*((U.gcd V*u^2)*(U.gcd V*v^2)) := by ring
      _ = 2*(U*V) := by rw [←hU,←hV]
      _ = (2*b)*a := by rw [←prod]; ring
      _ ≤ (2*b)*48 := Nat.mul_le_mul_left _ (by omega)
      _ < N*48 := Nat.mul_lt_mul_of_pos_right partner (by decide)
  exact ⟨floor A B heights hb,floor B A ((Nat.mul_comm ..).trans heights) ha⟩

/-- At source 49 the reduced positive rows 49/1 and 1/denominator
have signed norm product midpoint². One gcd gives the larger factor. -/
def denominator : ℕ := (24*N+1)/49

theorem witness :
    2^2047 ≤ N ∧ N < 2^2048 ∧ N=smallerFactor*largerFactor ∧
    49=7^2 ∧ Nat.Coprime 49 N ∧ 49*denominator=24*N+1 ∧
    Nat.Coprime 49 1 ∧ Nat.Coprime 1 denominator ∧ 1<denominator ∧
    (49*denominator)%N=1 ∧ 2*49<N ∧ 2*denominator<N ∧ 49≤denominator ∧
    49*denominator=midpoint^2 ∧ 2*midpoint^2<N*49 ∧
    (49*denominator-midpoint).gcd N=largerFactor ∧
    1<largerFactor ∧ largerFactor<N := by decide +kernel

end PrimeFactors.PlantedHeightExample
