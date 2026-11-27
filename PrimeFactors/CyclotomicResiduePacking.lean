import PrimeFactors.CyclotomicRadixLift

/-! Use the local product modulo five and seven to distinguish four possible
factor sums left by a single externally supplied cyclotomic digit. -/
namespace PrimeFactors.CyclotomicResiduePacking

open CyclotomicRadixLift Polynomial Finset
set_option maxRecDepth 8192

def Classes (N : ℕ) : Prop :=
  (N%5=2 ∨ N%5=3) ∧ (N%7=3 ∨ N%7=5 ∨ N%7=6)

def target5 (N : ℕ) := if N%5=2 then 1 else 2
def target7 (N : ℕ) := if N%7=3 then 2 else if N%7=5 then 3 else 1

private noncomputable def mask5 (n t : ZMod 5) : Bool :=
  if n=2 then t==2 || t==3 else t==1 || t==4

private noncomputable def mask7 (n t : ZMod 7) : Bool :=
  if n=3 then t==0 || t==3 || t==4
  else if n=5 then t==0 || t==1 || t==6 else t==0 || t==2 || t==5

/-- Each test uses only the product and a proposed sum. -/
noncomputable def passes (N : ℕ) (S : ℤ) := mask5 N S && mask7 N S

private theorem true_pass {p q : ℕ} (cl : Classes (p*q)) : passes (p*q) (p+q) = true := by
  have five : ∀ a b : ZMod 5, a*b=2 ∨ a*b=3 → mask5 (a*b) (a+b)=true := by decide +kernel
  have seven : ∀ a b : ZMod 7, a*b=3 ∨ a*b=5 ∨ a*b=6 → mask7 (a*b) (a+b)=true := by decide +kernel
  have modp {k n r : ℕ} (eq : n%k=r) : (n : ZMod k) = r := by
    rw [←eq,ZMod.natCast_mod]
  have f := cl.1.imp (fun h => modp h) (fun h => modp h)
  have s := cl.2.imp (fun h => modp h) (fun h => h.imp (fun l => modp l) (fun l => modp l))
  push_cast at f s
  simpa [passes] using And.intro (five p q f) (seven p q s)

def GoodStep (N s : ℕ) := s%5=target5 N ∧ s%7=target7 N

private theorem cast_step5 {N s : ℕ} (fit : GoodStep N s) :
    (s : ZMod 5) = if (N:ZMod 5)=2 then 1 else 2 := by
  have e : ((s%5:ℕ) : ZMod 5) = (target5 N : ℕ) := congrArg (fun z : ℕ => (z:ZMod 5)) fit.1
  have iff : (N:ZMod 5)=2 ↔ N%5=2 := ZMod.natCast_eq_natCast_iff' N 2 5
  simpa only [ZMod.natCast_mod, target5, apply_ite, Nat.cast_ofNat, iff] using e

private theorem cast_step7 {N s : ℕ} (fit : GoodStep N s) :
    (s : ZMod 7) = if (N:ZMod 7)=3 then 2 else if (N:ZMod 7)=5 then 3 else 1 := by
  have e := congrArg (fun z : ℕ => (z:ZMod 7)) fit.2
  have i3 : (N:ZMod 7)=3 ↔ N%7=3 := ZMod.natCast_eq_natCast_iff' N 3 7
  have i5 : (N:ZMod 7)=5 ↔ N%7=5 := ZMod.natCast_eq_natCast_iff' N 5 7
  have h : (s:ZMod 7)=(target7 N:ℕ) := by simpa only [ZMod.natCast_mod] using e
  by_cases n3 : N%7=3
  · simpa only [target7,if_pos n3,if_pos (i3.mpr n3),Nat.cast_ofNat] using h
  · by_cases n5 : N%7=5
    · simpa only [target7,if_neg n3,if_neg (mt i3.mp n3),if_pos n5,if_pos (i5.mpr n5),
        Nat.cast_ofNat] using h
    · simpa only [target7,if_neg n3,if_neg (mt i3.mp n3),if_neg n5,if_neg (mt i5.mp n5),
        Nat.cast_one] using h

/-- At most one of four consecutive lifts survives the two residue tables. -/
theorem unique {N s : ℕ} (fit : GoodStep N s) (base : ℤ) {i j : Fin 4}
    (pi : passes N (base-s*(i:ℕ))=true) (pj : passes N (base-s*(j:ℕ))=true) : i=j := by
  have fifth : ∀ n t : ZMod 5, ∀ d : Fin 4, d.val=2 ∨ d.val=3 →
      mask5 n t = true → mask5 n (t-(if n=2 then 1 else 2)*(d.val:ZMod 5)) = false := by
    decide +kernel
  have seventh : ∀ n t : ZMod 7, mask7 n t = true →
      mask7 n (t-(if n=3 then 2 else if n=5 then 3 else 1)) = false := by decide +kernel
  wlog le : i≤j generalizing i j with ordered
  · exact (ordered pj pi (by omega)).symm
  by_contra ne
  let d : Fin 4 := ⟨j.val-i.val,by omega⟩
  have eq : j.val = i.val+d.val := by dsimp [d]; omega
  simp only [passes, Bool.and_eq_true, Int.cast_sub, Int.cast_mul, Int.cast_natCast] at pi pj
  rw [eq] at pj
  push_cast at pj
  rw [mul_add, sub_add_eq_sub_sub, mul_add, sub_add_eq_sub_sub] at pj
  rcases (show d.val=1 ∨ d.val=2 ∨ d.val=3 by dsimp [d]; omega) with one|two
  · have h := seventh N _ pi.2
    rw [← cast_step7 fit] at h
    have jtrue := pj.2
    rw [one,Nat.cast_one,mul_one,h] at jtrue
    contradiction
  · have h := fifth N _ d two pi.1
    rw [←cast_step5 fit,pj.1] at h
    contradiction

/-- A Chinese-remainder representative. The three coefficients are one in
their respective modulus (12, 5, 7) and zero in the other two. -/
def congruenceClass (N : ℕ) :=
  (385+336*target5 N*(stride N)^11+120*target7 N*(stride N)^11)%420

/-- First integer in the selected residue class at or above ceil(c/4). -/
def radix (N c : ℕ) :=
  let start := (c+3)/4
  start+(congruenceClass N+420-start%420)%420

theorem radix_spec (N c : ℕ) :
    (c+3)/4 ≤ radix N c ∧ radix N c ≤ (c+3)/4+419 ∧ 0<radix N c ∧
    (weight N).Coprime (radix N c) ∧ GoodStep N (stride N*radix N c) := by
  let M := radix N c
  have lim : (c+3)/4 ≤ M ∧ M ≤ (c+3)/4+419 := by dsimp [M,radix]; omega
  have congr : M ≡ congruenceClass N [MOD 420] := by
    dsimp [M,radix, Nat.ModEq, congruenceClass]; omega
  have spec : congruenceClass N%12=1 ∧ GoodStep N (stride N*congruenceClass N) := by
    rcases weights N with h|h|h|h <;>
      simp only [GoodStep,congruenceClass,stride,h,target5,target7] <;> split_ifs <;> decide +kernel
  have h12 : M%12=1 := Eq.trans (congr.of_dvd (by decide : 12∣420)) spec.1
  have full : (stride N*M) ≡ stride N*congruenceClass N [MOD 420] := congr.mul_left _
  have wdiv : weight N∣12 := by rcases weights N with h|h|h|h <;> rw [h] <;> decide
  have cop : Nat.Coprime 12 M := by show Nat.gcd 12 M=1; rw [Nat.gcd_rec,h12]; decide
  exact ⟨lim.1,lim.2,by change 0<M; omega,cop.coprime_dvd_left wdiv,
    Eq.trans (full.of_dvd (by decide : 5∣420)) spec.2.1,
    Eq.trans (full.of_dvd (by decide : 7∣420)) spec.2.2⟩

/-- Filter the four sums proposed by the supplied residue. This evaluates
eight fixed small-modulus masks at most. -/
noncomputable def survivors (N M H : ℕ) (v : ℤ) : Finset ℤ :=
  let first := decode N (weight N) M H v
  ((univ : Finset (Fin 4)).image fun j : Fin 4 => first - (stride N*M:ℕ)*(j:ℕ)).filter (passes N ·)

private theorem unique_survivor {N M H : ℕ} {v S : ℤ} (fit : GoodStep N (stride N*M))
    (inList : ∃ i : Fin 4, decode N (weight N) M H v-(stride N*M:ℕ)*(i:ℕ)=S)
    (ok : passes N S=true) : survivors N M H v = {S} := by
  obtain ⟨i,eq⟩ := inList
  ext z
  simp only [survivors,mem_filter,mem_image,mem_univ,true_and,mem_singleton]
  constructor
  · rintro ⟨⟨j,hj⟩,p⟩
    have same := unique fit (decode N (weight N) M H v) (i:=i) (j:=j)
      (by simpa only [eq] using ok) (by simpa only [hj] using p)
    simpa only [←same,eq] using hj.symm
  · rintro rfl
    exact ⟨⟨i,eq⟩,ok⟩

/-- Compute the remainder class of x in the width interval. Up to four
indices remain when count ≤ 4M. The selector receives the cyclotomic value. -/
private theorem in_four {p q M L H : ℕ} {v : ℤ} (hp : p.Prime) (hq : q.Prime)
    (neq : p≠q) (po : Odd p) (qo : Odd q) (mp : 0<M)
    (cop : (weight (p*q)).Coprime M)
    (lo : L≤p+q-1) (hi : p+q-1<H) (cap : choices (p*q) (stride (p*q)) L H ≤ 4*M)
    (supplied : v ≡ (cyclotomic (p*q) ℤ).eval (1+(M:ℤ)) [ZMOD (M:ℤ)^2]) :
    ∃ i : Fin 4, decode (p*q) (weight (p*q)) M H v -
      (stride (p*q)*M:ℕ)*(i:ℕ) = (p:ℤ)+q := by
  let g := weight (p*q)
  let F := (p-1)*(q-1)
  let start := bottom (p*q) (2*g) H
  have gp : 0<g := by rcases weights (p*q) with h|h|h|h <;> dsimp [g] <;> omega
  obtain ⟨x,hx⟩ := divides po qo
  change F=2*g*x at hx
  have off : p*q=F+(p+q-1) := PowerImageWidth.offset hp.pos hq.pos
  have xr := in_range (N:=p*q) (W:=2*g) (x:=x) (L:=L) (H:=H)
    (by positivity : 0<2*g) (by omega) (by omega) (by omega)
  change start≤x ∧ x<start+choices (p*q) (stride (p*q)) L H at xr
  obtain ⟨c,dig⟩ := CyclotomicSumDigit.digit_of_evaluation hp hq neq (by exact_mod_cast mp) supplied
  have fs : (p:ℤ)*q+1-(p+q)=F := by dsimp [F]; push_cast [hp.one_le,hq.one_le]; ring
  have fx : (F:ℤ)=2*(g:ℤ)*x := by exact_mod_cast hx
  have xm : (g:ℤ)*x = CyclotomicSumDigit.digit v M+M*c := by linarith only [dig,fs,fx]
  have bez := Nat.gcd_eq_gcd_ab g M
  rw [cop.gcd_eq_one,Nat.cast_one] at bez
  have rem : CyclotomicSumDigit.digit v M*g.gcdA M-(start:ℤ) ≡ (x:ℤ)-start [ZMOD (M:ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨c*g.gcdA M+(x:ℤ)*g.gcdB M,?_⟩
    nlinarith only [congrArg (fun h => (x:ℤ)*h) bez, congrArg (fun h => h*g.gcdA M) xm]
  let d : ℤ := (x:ℤ)-start
  have nonneg : 0≤d := by dsimp [d]; omega
  have upper : d<4*(M:ℤ) := by dsimp [d]; omega
  have mpi : (0:ℤ)<M := by exact_mod_cast mp
  have loD := Int.ediv_nonneg nonneg mpi.le
  have hiD := (Int.ediv_lt_iff_lt_mul mpi).mpr upper
  let i : Fin 4 := ⟨(d/M).toNat, by omega⟩
  refine ⟨i,?_⟩
  have iv : ((i:ℕ):ℤ) = d/M := Int.toNat_of_nonneg loD
  change (p*q:ℕ)+1-2*(g:ℤ)*((start:ℤ)+(CyclotomicSumDigit.digit v M*g.gcdA M-start)%(M:ℤ))
    - (((2*g)*M:ℕ):ℤ)*(i:ℕ) = _
  rw [iv,show (CyclotomicSumDigit.digit v M*g.gcdA M-start)%(M:ℤ) = d%M from rem]
  push_cast
  have split := Int.emod_add_ediv d M
  dsimp only [d] at split ⊢
  linear_combination fs + fx - 2*(g:ℤ)*split

/-- The quarter-size radix and the two product-only residue tables give the
unique correct sum for the selected input classes. -/
theorem recover {p q L H : ℕ} {v : ℤ} (hp : p.Prime) (hq : q.Prime) (neq : p≠q)
    (po : Odd p) (qo : Odd q) (cl : Classes (p*q))
    (lo : L≤p+q-1) (hi : p+q-1<H) :
    let M := radix (p*q) (choices (p*q) (stride (p*q)) L H)
    v ≡ (cyclotomic (p*q) ℤ).eval (1+(M:ℤ)) [ZMOD (M:ℤ)^2] →
      survivors (p*q) M H v = {(p:ℤ)+q} := by
  intro M supplied
  let c := choices (p*q) (stride (p*q)) L H
  have spec := radix_spec (p*q) c
  change (c+3)/4≤M ∧ _ at spec
  apply unique_survivor spec.2.2.2.2 _ (true_pass cl)
  apply in_four hp hq neq po qo spec.2.2.1 spec.2.2.2.1 lo hi _ supplied
  change c ≤ 4*M
  omega

/-- Supply just the common width interval, the qualifying product class
and the modular evaluation. The interval endpoints and radix are public. -/
theorem adaptive {p q A : ℕ} {v : ℤ} (hp : p.Prime) (hq : q.Prime) (neq : p≠q)
    (po : Odd p) (qo : Odd q) (cl : Classes (p*q)) (ap : 0<A) (even : Even A)
    (pl : A≤p) (ql : A≤q) (pu : p<2*A) (qu : q<2*A) :
    let N := p*q
    let L := ProductDeficitBand.lower N A
    let H := ProductDeficitBand.upper N A
    let M := radix N (choices N (stride N) L H)
    v ≡ (cyclotomic N ℤ).eval (1+(M:ℤ)) [ZMOD (M:ℤ)^2] →
      survivors N M H v = {(p:ℤ)+q} := by
  have band := ProductDeficitBand.contains ap even po qo pl ql pu qu
  exact recover hp hq neq po qo cl band.1 band.2

/-- The public band contains 52 unrestricted progression indices. The
older odd radix is 53. With the two masks, a residue modulo 13² suffices. -/
theorem worked_example :
    ProductDeficitBand.lower 7294033 2048 = 5401 ∧ ProductDeficitBand.upper 7294033 2048 = 5608 ∧
    choices 7294033 (stride 7294033) 5401 5608 = 52 ∧
    CyclotomicRadixLift.radix 7294033 52 = 53 ∧ radix 7294033 52 = 13 ∧
    (cyclotomic 7294033 ℤ).eval 14 % 169 = 40 ∧
    decode 7294033 (weight 7294033) 13 5608 40 = 5578 ∧
    [5578,5526,5474,5422].map (passes 7294033) = [false,false,true,false] ∧
    survivors 7294033 13 5608 40 = {5474} ∧
    Nat.Prime 2293 ∧ Nat.Prime 3181 ∧ 2293*3181=7294033 := by
  have pp : Nat.Prime 2293 := by decide +kernel
  have qp : Nat.Prime 3181 := by decide +kernel
  have e := CyclotomicSumDigit.evaluation_mod pp qp (by decide) 13
  have v : (cyclotomic 7294033 ℤ).eval 14 ≡ 40 [ZMOD 169] := e.trans (by decide)
  have count : choices 7294033 (stride 7294033) 5401 5608 = 52 := by decide +kernel
  have pick : radix 7294033 52=13 := by decide +kernel
  have result := recover (L:=5401) (H:=5608) (v:=40) pp qp (by decide)
    (by decide) (by decide) (by unfold Classes; decide +kernel) (by decide) (by decide)
  dsimp only at result
  rw [show 2293*3181=7294033 by decide,count,pick] at result
  refine ⟨?_,by decide +kernel,count,by decide +kernel,pick,v,?_,by decide +kernel,
    result v.symm,pp,qp,by decide⟩
  · have low : ceilSqrt 7294033 = 2701 := by
      have hi := (ceilSqrt_le_iff (n:=7294033) (a:=2701)).mpr (by decide)
      have lo : ¬ ceilSqrt 7294033 ≤ 2700 := by rw [ceilSqrt_le_iff]; decide
      omega
    rw [ProductDeficitBand.lower,low]
    decide
  · have bez : Nat.gcdA 2 13 = -6 := by norm_num [Nat.gcdA,Nat.xgcd,Nat.xgcdAux]
    rw [show weight 7294033=2 by decide,decode,bez]
    decide +kernel

end PrimeFactors.CyclotomicResiduePacking
