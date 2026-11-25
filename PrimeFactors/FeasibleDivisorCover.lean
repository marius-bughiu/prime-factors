import PrimeFactors.HigherDivisorWindow
import PrimeFactors.ChebyshevQuarticScale

namespace PrimeFactors.FeasibleDivisorCover

open Polynomial HigherDivisorWindow

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

abbrev X : ℕ := 2^1023
abbrev Q : ℕ := 2^1024
abbrev S : ℕ := 2^507
abbrev multiplicity : ℕ := 12287
abbrev dimension : ℕ := 24576

def lower (n : ℕ) := n/Q+1
def radius (b : Bool) := if b then 15*S else 13*S
def divisorFloor (n : ℕ) (b : Bool) := if b then max (lower n) (19*2^1019) else lower n
def cut : ℕ := 19*2^1018
def start (n : ℕ) (b : Bool) := if b then max (lower n/2) cut else lower n/2
def stop (n : ℕ) (b : Bool) := if b then n.sqrt/2+1 else min (n.sqrt/2+1) cut
def count (n : ℕ) (b : Bool) :=
  (stop n b - start n b + (2*radius b-1))/(2*radius b)
def center (n : ℕ) (b : Bool) (i : ℕ) := 2*(start n b+i*(2*radius b)+radius b)+1

private theorem floor_facts (n : ℕ) (big : 2^2047≤n) :
    X≤lower n ∧ n≤Q*lower n := by
  have bound := Nat.lt_mul_div_succ n (by positivity : 0<Q)
  have xd : X*Q=2^2047 := by rw [← pow_add]
  have le : X≤n/Q := (Nat.le_div_iff_mul_le (by positivity)).mpr (xd ▸ big)
  exact ⟨le.trans (Nat.le_add_right ..),bound.le⟩

private lemma shuffle (a b c d : ℕ) : a*(b*c*d)=(a*b*d)*c := by ac_rfl

private lemma bit_room {n D W B T A C wb db : ℕ} (dc : 0<D)
    (coupled : n≤Q*D) (hi : W^256 ≤ 2^wb) (lo : 2^db ≤ D^256)
    (bits : 256*(C+1024*T) + wb*B < db*A) :
    2^C * (n^T * W^B) < D^(A+T) := by
  have h : (2^C * Q^T * W^B)^256 < (D^A)^256 := by
    calc
      _ = 2^(256*(C+1024*T))*(W^256)^B := by
        simp only [Q,mul_pow,←pow_mul,←pow_add]
        rw [Nat.mul_comm B 256]
        congr 2
        ring
      _ ≤ 2^(256*(C+1024*T))*(2^wb)^B := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hi _)
      _ = 2^(256*(C+1024*T)+wb*B) := by rw [←pow_mul,←pow_add]
      _ < 2^(db*A) := Nat.pow_lt_pow_right (by decide) bits
      _ = (2^db)^A := pow_mul ..
      _ ≤ (D^256)^A := Nat.pow_le_pow_left lo _
      _ = (D^A)^256 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
  have h' := (Nat.pow_lt_pow_iff_left (by decide : 256≠0)).mp h
  calc
    _ ≤ 2^C*((Q*D)^T*W^B) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left coupled _))
    _ = (2^C * Q^T * W^B)*D^T := by rw [mul_pow]; exact shuffle ..
    _ < D^A*D^T := Nat.mul_lt_mul_of_pos_right h' (pow_pos dc _)
    _ = _ := (pow_add ..).symm

private abbrev T := 75491328
private abbrev B := 301977600
private abbrev A := 226473984
private abbrev C := 151173120

private lemma scaled_width {w e : ℕ} (bit : w^256≤2^e) :
    (w*S)^256 ≤ 2^(507*256+e) := by
  rw [mul_pow,pow_add,pow_mul]
  exact (Nat.mul_le_mul_right _ bit).trans_eq (Nat.mul_comm ..)

private theorem uniform_height {n : ℕ} (big : 2^2047≤n) (b : Bool) :
    2^C * (n^T * (radius b)^B) < (divisorFloor n b)^(A+T) := by
  obtain ⟨xl,nl⟩ := floor_facts n big
  have Dle : lower n ≤ divisorFloor n b := by
    cases b
    · exact le_rfl
    · exact le_max_left ..
  apply bit_room (n:=n) (D:=divisorFloor n b) (W:=radius b) (C:=C) (B:=B) (T:=T) (A:=A)
    (wb:=507*256+if b then 1001 else 948) (db:=if b then 1019*256+1087 else 1023*256)
    (lt_of_lt_of_le (by positivity : 0<X) (xl.trans Dle)) (nl.trans (Nat.mul_le_mul_left _ Dle))
  · cases b
    · simpa only [radius,Bool.false_eq_true,if_false] using
        scaled_width (by decide +kernel : 13^256≤(2:ℕ)^948)
    · simpa only [radius,if_true] using scaled_width (by decide +kernel : 15^256≤(2:ℕ)^1001)
  · cases b
    · simp only [Bool.false_eq_true,if_false,divisorFloor]
      exact (pow_mul (2:ℕ) 1023 256).trans_le (Nat.pow_le_pow_left xl _)
    · simp only [if_true]
      have hD : 19*2^1019 ≤ divisorFloor n true := le_max_right ..
      calc
        (2:ℕ)^(1019*256+1087) = ((2:ℕ)^1019)^256 * 2^1087 := by rw [pow_add,pow_mul]
        _ ≤ ((2:ℕ)^1019)^256 * 19^256 := Nat.mul_le_mul_left _ (by decide +kernel)
        _ = (19*2^1019)^256 := by rw [mul_pow,Nat.mul_comm]
        _ ≤ _ := Nat.pow_le_pow_left hD _
  · cases b <;> decide +kernel

private theorem constants : multiplicity + multiplicity.choose 2 = T ∧
    dimension.choose 2=B ∧ multiplicity*dimension=A+T ∧ 15*dimension≤C ∧
    30*dimension+(dimension-1)*dimension ≤ 4*C := by
  simp only [Nat.choose_two_right]; decide +kernel

private theorem lll_factor {r H : ℕ} (dim : r≤2^15) (bound : 30*r+(r-1)*r≤4*H) :
    r^(2*r)*2^((r-1)*r)≤(2^H)^4 := by
  calc
    _ ≤ ((2:ℕ)^15)^(2*r)*2^((r-1)*r) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left dim _)
    _ = 2^(30*r+(r-1)*r) := by rw [←pow_mul,←pow_add,←Nat.mul_assoc 15 2 r]
    _ ≤ 2^(4*H) := Nat.pow_le_pow_right (by decide) bound
    _ = _ := by rw [Nat.mul_comm 4 H,pow_mul]

/-- Both the finite-pigeonhole room and the numerical sufficient bound from classical LLL
hold at these two radii, for the public lower divisor bound of the corresponding region. -/
theorem rooms {n : ℕ} (big : 2^2047≤n) (b : Bool) :
    let m := multiplicity
    let r := dimension
    let W := radius b
    let D := divisorFloor n b
    n^(m+m.choose 2)*(r^r*W^(r.choose 2)) < (D^m)^r ∧
    r^(2*r)*2^((r-1)*r)*(n^(m+m.choose 2)*W^(r.choose 2))^4 < (D^m)^(4*r) := by
  obtain ⟨ht,hb,ha,hc,h4⟩ := constants
  obtain hc' := uniform_height big b
  dsimp only
  rw [ht,hb,←pow_mul,ha]
  have hr : dimension≤2^15 := by decide
  constructor
  · have factor : dimension^dimension ≤ 2^C := by
      calc _ ≤ ((2:ℕ)^15)^dimension := Nat.pow_le_pow_left hr _
           _ = 2^(15*dimension) := (pow_mul ..).symm
           _ ≤ _ := Nat.pow_le_pow_right (by decide) hc
    calc
      _ = dimension^dimension*(n^T*(radius b)^B) := Nat.mul_left_comm ..
      _ ≤ _ := Nat.mul_le_mul_right _ factor
      _ < _ := hc'
  · have factor := lll_factor hr h4
    calc
      _ ≤ (2^C)^4*(n^T*(radius b)^B)^4 := Nat.mul_le_mul_right _ factor
      _ = _ := (mul_pow ..).symm
      _ < ((divisorFloor n b)^(A+T))^4 := Nat.pow_lt_pow_left hc' (by decide)
      _ = _ := by rw [←ha]; simp only [←pow_mul]; congr 1


private theorem tangent (u L Z : ℕ) (bound : u^2≤2*Z*L) :
    70*u ≤ 50*L+49*Z := by
  apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
  have ag : 9800*Z*L ≤ (50*L+49*Z)^2 := by
    have e : (9800:ℤ)*(Z:ℤ)*L ≤ (50*(L:ℤ)+49*Z)^2 := by
      nlinarith only [sq_nonneg (50*(L:ℤ)-49*(Z:ℤ))]
    exact_mod_cast e
  calc
    (70*u)^2 = 4900*u^2 := by ring
    _ ≤ 4900*(2*Z*L) := Nat.mul_le_mul_left _ bound
    _ = 9800*Z*L := by ring
    _ ≤ _ := ag

private theorem budget_math {s a b f g : ℕ} (big : 10000≤s)
    (all : 140*(a+b) ≤ 29*(512*s^2)+280) (early : 32*a ≤ 3*(512*s^2)+32)
    (left : 26*s*f ≤ a+26*s) (right : 30*s*g ≤ b+30*s) :
    20*(f+g)<76*s := by
  apply Nat.lt_of_mul_lt_mul_right (a:=s)
  have quad : 10000*s ≤ s^2 := by simpa [pow_two] using Nat.mul_le_mul_right s big
  nlinarith only [all,early,left,right,quad,big]

private lemma union_lengths (u l k : ℕ) :
    min u k-l + (u-max l k) = u-l := by omega

private lemma side_length (u l k : ℕ) : min u k-l ≤ k-l := by omega

private lemma integer_widths {l u z k a b : ℕ} (total : a+b=u/2+1-l/2)
    (early : a≤k-l/2) (lk : 32*k=19*z) (lo : z≤l) (bound : 70*u≤50*l+49*z) :
    140*(a+b)≤29*z+280 ∧ 32*a≤3*z+32 := by omega

/-- Fewer than (19/20)·2^509 polynomial locations over the entire feasible smaller-factor band.
The bound counts both regions, with their separate divisions rounded up. -/
theorem center_budget {n : ℕ} (big : 2^2047≤n) :
    20*(count n false+count n true)<19*2^509 := by
  let L := lower n
  let U := n.sqrt
  let a := stop n false - start n false
  let b := stop n true - start n true
  obtain ⟨xl,nl⟩ := floor_facts n big
  have qx : Q=2*X := by decide +kernel
  have upper : U^2 ≤ 2*X*L := (Nat.sqrt_le' n).trans (qx ▸ nl)
  have line := tangent U L X upper
  have total : a+b=U/2+1-L/2 := union_lengths ..
  have ac : a≤cut-L/2 := side_length ..
  have cutX : 32*cut=19*X := by decide +kernel
  have sx : X=512*S^2 := by decide +kernel
  obtain ⟨g1,g2⟩ := integer_widths total ac cutX xl line
  have lef : (26*S)*count n false ≤ a+26*S := by
    change (26*S)*((a+(2*(13*S)-1))/(2*(13*S))) ≤ a+26*S
    rw [show 2*(13*S)=26*S by rw [←Nat.mul_assoc]]
    exact (Nat.mul_div_le ..).trans (by omega)
  have rig : (30*S)*count n true ≤ b+30*S := by
    change (30*S)*((b+(2*(15*S)-1))/(2*(15*S))) ≤ b+30*S
    rw [show 2*(15*S)=30*S by rw [←Nat.mul_assoc]]
    exact (Nat.mul_div_le ..).trans (by omega)
  have endcap : 76*S=19*2^509 := by decide +kernel
  rw [←endcap]
  exact budget_math (by decide +kernel) (sx ▸ g1) (sx ▸ g2) lef rig


private theorem ceiling_covers {u b : ℕ} (pos : 0<b) : u≤b*((u+(b-1))/b) := by
  have r := Nat.div_add_mod (u+(b-1)) b
  have m := Nat.mod_lt (u+(b-1)) pos
  omega

private theorem local_address {l u j w : ℕ} (pos : 0<w) (lo : l≤j) (hi : j<u) :
    ∃ i : Fin ((u-l+(2*w-1))/(2*w)), ∃ x : ℤ,
      (2*j+1:ℕ)=(2*(l+i.val*(2*w)+w)+1:ℕ)+(2:ℤ)*x ∧ |x|≤(w:ℤ) := by
  let z := j-l
  let b := 2*w
  have bp : 0<b := by dsimp only [b]; omega
  have cap : z < ((u-l+(b-1))/b)*b := by
    rw [Nat.mul_comm]
    exact (show z<u-l by dsimp only [z]; omega).trans_le (ceiling_covers bp)
  let i : Fin ((u-l+(2*w-1))/(2*w)) := ⟨z/b,(Nat.div_lt_iff_lt_mul bp).mpr cap⟩
  let r := z%b
  have remLt : r<b := Nat.mod_lt _ bp
  have index : i.val*b+r=z := by simpa only [i,r,Nat.mul_comm] using Nat.div_add_mod z b
  have split : j=l+z := by dsimp only [z]; omega
  refine ⟨i,(r:ℤ)-w,?_,abs_le.mpr ?_⟩
  · change ((2*j+1:ℕ):ℤ)=((2*(l+i.val*b+w)+1:ℕ):ℤ)+2*((r:ℤ)-w)
    omega
  · change r<2*w at remLt
    omega

/-- The smaller factor of an odd product has an address using only its public product
and the upper bit-width bound on the larger factor. Each last block may be truncated. -/
theorem address {n d q : ℕ} (pair : n=d*q) (nd : Odd d) (ord : d≤q) (cap : q<Q) :
    ∃ b, ∃ i : Fin (count n b), ∃ x : ℤ, divisorFloor n b≤d ∧
      (d:ℤ)=center n b i.val + 2*x ∧ |x|≤(radius b:ℤ) := by
  obtain ⟨j,hj⟩ := nd
  have dpos : 0<d := by omega
  have bound : n<d*Q := pair ▸ Nat.mul_lt_mul_of_pos_left cap dpos
  have dl : lower n≤d := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul (by positivity : 0<Q)).mpr bound)
  have du : d≤n.sqrt := Nat.le_sqrt.mpr (pair ▸ Nat.mul_le_mul_left d ord)
  have low : lower n/2≤j := by omega
  have high : j<n.sqrt/2+1 := by omega
  by_cases jp : j<cut
  · have hi : j<stop n false := lt_min high jp
    obtain ⟨i,x,pos,near⟩ := local_address (l:=start n false) (w:=radius false)
      (by decide +kernel) low hi
    exact ⟨false,i,x,dl,by rw [hj]; exact pos,near⟩
  · have jlo : start n true≤j := max_le low (by omega)
    obtain ⟨i,x,pos,near⟩ := local_address (l:=start n true) (u:=stop n true) (w:=radius true)
      (by decide +kernel) jlo high
    have split : 2*cut=19*2^1019 := by decide +kernel
    have floorle : divisorFloor n true≤d := max_le dl (by omega)
    exact ⟨true,i,x,floorle,by rw [hj]; exact pos,near⟩

private theorem at_location {n : ℕ} (big : 2^2047≤n) (parity : Odd n) (b : Bool) (i : ℕ) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card<dimension ∧
      ∀ x d : ℤ, d ∣ (n:ℤ) → d=(center n b i:ℤ)+2*x →
        (divisorFloor n b:ℤ)≤d → |x|≤(radius b:ℤ) → F.eval x=0 := by
  let t := QuarticDivisorWindow.oddAnchor n (center n b i)
  have anchor : (n:ℤ) ∣ (center n b i:ℤ)+2*t := by
    obtain ⟨a,ha⟩ := parity
    refine ⟨1,?_⟩
    change ((center n b i:ℕ):ℤ)+2*((n-(center n b i:ℕ):ℤ)/2)=(n:ℤ)*1
    simp only [center,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at *
    omega
  have wpos : 0<radius b := by cases b <;> decide +kernel
  have dpos : 0<divisorFloor n b := by
    have h := (floor_facts n big).1
    cases b
    · exact lt_of_lt_of_le (by positivity : 0<X) h
    · exact lt_of_lt_of_le (by positivity : 0<X) (h.trans (le_max_left ..))
  obtain ⟨v,nz,jets,small⟩ := relation_exists (by decide : 0<dimension)
    (lt_of_lt_of_le (by positivity) big) wpos dpos (rooms big b).1 t
  refine ⟨ofFn dimension v,nz,?_,?_⟩
  · exact (Multiset.toFinset_card_le _).trans_lt ((Polynomial.card_roots' _).trans_lt
      (ofFn_natDegree_lt (by decide) v))
  · intro x d hd pos lowerD near
    have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr parity).isCoprime
    exact root_of_divisor jets hd (QuarticDivisorWindow.progression_offset unit anchor hd pos) near
      (small.trans_le (pow_le_pow_left₀ (Int.natCast_nonneg _) lowerD multiplicity))

/-- A public family of fewer than (19/20)·2^509 locations covers the actual smaller factor.
A polynomial at each address depends only on n and that address. -/
theorem feasible_cover {n : ℕ} (big : 2^2047≤n) (parity : Odd n) :
    20*(count n false+count n true)<19*2^509 ∧
    ∃ F : (b : Bool) → Fin (count n b) → ℤ[X],
      (∀ b i, F b i ≠ 0 ∧ (F b i).roots.toFinset.card<dimension) ∧
      ∀ d q : ℕ, n=d*q → Odd d → d≤q → q<Q →
        ∃ b, ∃ i : Fin (count n b), ∃ x : ℤ, (d:ℤ)=center n b i.val+2*x ∧
          |x|≤(radius b:ℤ) ∧ x∈(F b i).roots.toFinset := by
  classical
  choose F nz rank roots using at_location big parity
  refine ⟨center_budget big,fun b i => F b i.val,fun b i => ⟨nz b i.val,rank b i.val⟩,?_⟩
  intro d q h odd ord cap
  obtain ⟨b,i,x,floorle,pos,near⟩ := address h odd ord cap
  have hd : d ∣ n := ⟨q,h⟩
  exact ⟨b,i,x,pos,near,Multiset.mem_toFinset.mpr ((mem_roots (nz b i.val)).mpr
    (roots b i.val x d (by exact_mod_cast hd) pos (by exact_mod_cast floorle) near))⟩

private theorem checked_count {n t l lo hi f g : ℕ}
    (rad : t*t≤n ∧ n<(t+1)*(t+1))
    (quot : l*Q≤n ∧ n<(l+1)*Q)
    (lowerIndex : lo*2≤l+1 ∧ l+1<(lo+1)*2)
    (upperIndex : hi*2≤t ∧ t<(hi+1)*2)
    (first : let num := min (hi+1) cut - lo + (26*S-1)
             f*(26*S)≤num ∧ num<(f+1)*(26*S))
    (second : let num := hi+1 - max lo cut + (30*S-1)
              g*(30*S)≤num ∧ num<(g+1)*(30*S)) :
    count n false+count n true=f+g := by
  have loEq : lower n/2=lo := by
    unfold lower
    rw [Nat.div_eq_of_lt_le quot.1 quot.2]
    exact Nat.div_eq_of_lt_le lowerIndex.1 lowerIndex.2
  have hiEq : n.sqrt/2=hi := by
    rw [←Nat.eq_sqrt.mpr rad]
    exact Nat.div_eq_of_lt_le upperIndex.1 upperIndex.2
  have w0 : 2*radius false=26*S := by change 2*(13*S)=26*S; rw [←Nat.mul_assoc]
  have w1 : 2*radius true=30*S := by change 2*(15*S)=30*S; rw [←Nat.mul_assoc]
  unfold count start stop
  simp only [Bool.false_eq_true,if_false,if_true,loEq,hiEq,w0,w1]
  rw [Nat.div_eq_of_lt_le first.1 first.2,Nat.div_eq_of_lt_le second.1 second.2]

private theorem fresh_count :
    let n := ChebyshevQuarticScale.fresh
    2^507<count n false+count n true ∧ count n false+count n true<2^508 := by
  have actual := checked_count (n:=ChebyshevQuarticScale.fresh)
    (t:=158327039176966334715448284019718823474497913662177975160442996009439310669941017429676080400185006424773254142252582891257193029659269227070095120289800339855421063931472090621260003180611046788905349147963313017385074143012442899089952314244753217806428276920663827209779196401916113023989449483782760844629)
    (l:=139442326659741800731206430487301790676256450820417103603567638702615320945643200109597383181524743015044019105328426769239519633206851144688795662985927573575232819047009676412871504745078874473574991827930426743652954740327671233876795516686885724110733096621675345982548232996469560186366035226520570258953)
    (lo:=69721163329870900365603215243650895338128225410208551801783819351307660472821600054798691590762371507522009552664213384619759816603425572344397831492963786787616409523504838206435752372539437236787495913965213371826477370163835616938397758343442862055366548310837672991274116498234780093183017613260285129477)
    (hi:=79163519588483167357724142009859411737248956831088987580221498004719655334970508714838040200092503212386627071126291445628596514829634613535047560144900169927710531965736045310630001590305523394452674573981656508692537071506221449544976157122376608903214138460331913604889598200958056511994724741891380422314)
    (f:=0)
    (g:=751192643009184680950530026877019260304527153594350998785209176385870390875839219880305174368027897458394779395544870871325808378877367221830976002267841)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  dsimp only
  rw [actual]
  decide +kernel

private theorem crossed_count :
    let n := ChebyshevQuarticScale.crossed
    2^508<count n false+count n true ∧ count n false+count n true<2^509 := by
  have actual := checked_count (n:=ChebyshevQuarticScale.crossed)
    (t:=135037911685235586269825030135549325391376915966798636179319977077209993450011760943044181307768476527897818717675959823440307553022185653953812606479930673789391793187765141283074720630433120513417190939648203494531748575804685158519937612233285802863014656458801051235008057526662884995918450838938076904614)
    (l:=101436876175789090483045964435897644786103893442178967149904492460111067520014083441016609201472256281591821620562086772518546996293132064916631194893055874657388844565726265138885515005344734102079834473932446158364091082336121079670725742535554363273494176663082325461826717178425245329473589122976773570561)
    (lo:=50718438087894545241522982217948822393051946721089483574952246230055533760007041720508304600736128140795910810281043386259273498146566032458315597446527937328694422282863132569442757502672367051039917236966223079182045541168060539835362871267777181636747088331541162730913358589212622664736794561488386785281)
    (hi:=67518955842617793134912515067774662695688457983399318089659988538604996725005880471522090653884238263948909358837979911720153776511092826976906303239965336894695896593882570641537360315216560256708595469824101747265874287902342579259968806116642901431507328229400525617504028763331442497959225419469038452307)
    (f:=243309603770720409497217912827281916796375364895952005664402555118991515743252697384648595434866136852292099163454553868491458284582926946132690029752634)
    (g:=1125707526068625184741368803853468966006758895005888042017587183702177091089949134984582495848582303006870003537186185716607196497443470657135879265052887)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  dsimp only
  rw [actual]
  decide +kernel

/-- Order-of-magnitude receipts use only the two published products. -/
theorem control_counts :
    (let n := ChebyshevQuarticScale.fresh
     2^507<count n false+count n true ∧ count n false+count n true<2^508) ∧
    (let n := ChebyshevQuarticScale.crossed
     2^508<count n false+count n true ∧ count n false+count n true<2^509) :=
  ⟨fresh_count,crossed_count⟩

end PrimeFactors.FeasibleDivisorCover
