import PrimeFactors.GroupedNormExamples
import PrimeFactors.PartialOrder
import Mathlib.Tactic.ReduceModChar
import PrimeFactors.CyclotomicSumDigit
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! On distinct odd semiprimes of unbounded size, every fixed input modulus
loses information about the first cyclotomic digit at each radix M ≥ 3. -/
namespace PrimeFactors.CyclotomicDigitPeriod

open Polynomial CyclotomicSumDigit

/-- The requested digit, defined directly from the public index of Φ. -/
noncomputable def value (M N : ℕ) : ℤ :=
  digit ((cyclotomic N ℤ).eval (1+(M:ℤ))) (M:ℤ)

/-- Recover the familiar half-totient expression as a canonical residue. -/
theorem value_eq {M p q : ℕ} (mp : 0<M) (pp : p.Prime) (qp : q.Prime) (neq : p≠q) :
    value M (p*q) = ((((p:ℤ)-1)*((q:ℤ)-1))/2) % M := by
  let h := (((p:ℤ)-1)*((q:ℤ)-1))/2
  have e := evaluation_mod pp qp neq (M:ℤ)
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp e
  have eq : (cyclotomic (p*q) ℤ).eval (1+(M:ℤ)) - 1 = (M:ℤ)*(h-M*k) := by
    dsimp [h]
    linear_combination -hk
  have nz : (M:ℤ) ≠ 0 := by exact_mod_cast mp.ne'
  change (((cyclotomic (p*q) ℤ).eval (1+(M:ℤ)) - 1)/M) % M = h%M
  rw [eq,Int.mul_ediv_cancel_left _ nz,sub_eq_add_neg,← mul_neg,Int.add_mul_emod_self_left]

private theorem large_class {M T : ℕ} (mp : 0<M) (tp : 0<T) (B : ℕ) (c : ℤ)
    (unit : IsUnit (c : ZMod (2*M*T))) :
    ∃ p : ℕ, B<p ∧ p.Prime ∧ ∃ u : ℤ, (p:ℤ)=c+2*M*T*u := by
  letI : NeZero (2*M*T) := ⟨by positivity⟩
  obtain ⟨p,gt,prime,hp⟩ := Nat.forall_exists_prime_gt_and_eq_mod unit B
  obtain ⟨u,hu⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub c (p:ℤ) (2*M*T)).mp
    (by simpa only [Int.cast_natCast] using hp.symm)
  push_cast at hu
  exact ⟨p,gt,prime,u,by linarith⟩

private theorem product_mod {M T p q : ℕ} {c u v : ℤ} (sq : c^2=1)
    (a : (p:ℤ)=c+2*M*T*u) (b : (q:ℤ)=c+2*M*T*v) : p*q ≡ 1 [MOD T] := by
  apply Int.natCast_modEq_iff.mp
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(2*M*(c*u+c*v+2*M*T*u*v)),?_⟩
  push_cast
  rw [a,b]
  linear_combination -sq

private theorem sign_digit {M T p q : ℕ} (mp : 0<M) (pp : p.Prime) (qp : q.Prime)
    (neq : p ≠ q) {s u v : ℤ} (a : (p:ℤ)=1-2*s+2*M*T*u) (b : (q:ℤ)=1-2*s+2*M*T*v) :
    value M (p*q) = (2*s^2) % M := by
  rw [value_eq mp pp qp neq,a,b]
  let w : ℤ := 2*T*((M:ℤ)*T*u*v-s*u-s*v)
  have h : (1-2*s+2*(M:ℤ)*T*u-1)*(1-2*s+2*(M:ℤ)*T*v-1) =
      2*(2*s^2 + (M:ℤ)*w) := by dsimp [w]; ring
  rw [h,Int.mul_ediv_cancel_left _ (by decide : (2:ℤ) ≠ 0),Int.add_mul_emod_self_left]

/-- Above any preassigned bound, four increasing odd primes give two products
in the same input class, with distinct digits 0 and 2. Dirichlet's theorem
here gives no upper bounds or equal factor widths. -/
theorem collision {M T : ℕ} (radix : 3≤M) (tp : 0<T) (B : ℕ) :
    ∃ p q r s : ℕ, max 2 B<p ∧ p<q ∧ q<r ∧ r<s ∧
      p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
      p*q ≡ 1 [MOD T] ∧ r*s ≡ 1 [MOD T] ∧
      value M (p*q) = 0 ∧ value M (r*s) = 2 := by
  have mp : 0<M := by omega
  obtain ⟨p,bp,pp,u,pu⟩ := large_class mp tp (max 2 B) 1 (by simp)
  obtain ⟨q,pq,qp,v,qv⟩ := large_class mp tp p 1 (by simp)
  obtain ⟨r,qr,rp,w,rw'⟩ := large_class mp tp q (-1) (by simp)
  obtain ⟨s,rs,sp,x,sx⟩ := large_class mp tp r (-1) (by simp)
  refine ⟨p,q,r,s,bp,pq,qr,rs,pp,qp,rp,sp,product_mod (by norm_num) pu qv,
    product_mod (by norm_num) rw' sx,?_,?_⟩
  · have h := sign_digit mp pp qp pq.ne (s := 0) (by simpa using pu) (by simpa using qv)
    simpa using h
  · have h := sign_digit mp rp sp rs.ne (s := 1) (u := w) (v := x) (T := T)
      (by norm_num; exact rw') (by norm_num; exact sx)
    have small : (2:ℤ) % M = 2 := Int.emod_eq_of_lt (by decide) (by exact_mod_cast radix)
    simpa only [one_pow,mul_one,small] using h

/-- A lookup table may be arbitrary and can be chosen separately for each
radix, period and lower size threshold. Its sole argument is N modulo T. -/
def HasTable (M T B : ℕ) : Prop := ∃ f : ℕ → ℤ, ∀ p q : ℕ, p.Prime → q.Prime →
    max 2 B<p → p<q → f ((p*q)%T) = value M (p*q)

private theorem small_zero {M p q : ℕ} (mp : 0<M) (small : M≤2) (pp : p.Prime)
    (qp : q.Prime) (gt : 2<p) (pq : p<q) : value M (p*q) = 0 := by
  obtain ⟨a,ha⟩ := pp.odd_of_ne_two (by omega)
  obtain ⟨b,hb⟩ := qp.odd_of_ne_two (by omega)
  rw [value_eq mp pp qp pq.ne,ha,hb]
  push_cast
  rw [show (2*(a:ℤ)+1-1)*(2*(b:ℤ)+1-1) = 2*(2*((a:ℤ)*b)) by ring,
    Int.mul_ediv_cancel_left _ (by decide : (2:ℤ)≠0)]
  interval_cases M <;> simp

/-- The only positive radices admitting *any* such fixed lookup are 1 and 2. -/
theorem table_iff {M T : ℕ} (mp : 0<M) (tp : 0<T) (B : ℕ) : HasTable M T B ↔ M ≤ 2 := by
  constructor
  · rintro ⟨f,h⟩
    by_contra! big
    obtain ⟨p,q,r,s,bp,pq,qr,rs,pp,qp,rp,sp,hp,hr,d0,d2⟩ := collision big tp B
    have v0 := h p q pp qp bp pq
    have v2 := h r s rp sp ((bp.trans pq).trans qr) rs
    rw [show (p*q)%T = 1%T from hp,d0] at v0
    rw [show (r*s)%T = 1%T from hr,d2] at v2
    omega
  · exact fun small => ⟨fun _ => 0, fun _ _ pp qp b pq =>
      (small_zero mp small pp qp ((Nat.le_max_left ..).trans_lt b) pq).symm⟩

/-! The next four order certificates replay the named adjacent/separated
prime fixtures in `benchmarks/grouped-norm.json`. The values and products
are imported from `GroupedNormExamples`. -/

open GroupedNormExamples
set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

private theorem quotient_unit {p x : ℕ} {z : ZMod p} {k : ℕ} (h : z^k=x)
    (unit : (x-1).Coprime p) (xp : 0<x) (bound : x<p) : ((z^k-1).val).Coprime p := by
  have nz : NeZero p := ⟨by omega⟩
  rw [h, ← Nat.cast_one (R := ZMod p), ← Nat.cast_sub (by omega : 1≤x),
    ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  exact unit

private theorem adjacentSmall_prime : Nat.Prime adjacentSmall := by
  unfold adjacentSmall
  let z : ZMod 158000373181258234077770964034191626978142507914851163619225657267540347210995817467518121775931879431800241124273180064676343457063408956883101414070693823504425292149852583466880471538429142365222902020521966319920938610706008149046981895001303814809850640463303208882923455344832573236019666008492470173697 := 70128674509555767343479909835335999867527267973595033149022745405148316029326632270138525953953738468112945344834630651201651207093074334880174806539918013406382561898275176867565764621753486909866411190237894993217457598986917700062181347506036753397914491930566826602433989900143077577349908924424246604236
  apply prime_of_partial_order_cover z (F := 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096) (ps := [2])
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (Covers.cons 512 (by decide : Nat.Prime 2) covers_one)
  · dsimp [z]; reduce_mod_char
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl
    · apply quotient_unit (x := 158000373181258234077770964034191626978142507914851163619225657267540347210995817467518121775931879431800241124273180064676343457063408956883101414070693823504425292149852583466880471538429142365222902020521966319920938610706008149046981895001303814809850640463303208882923455344832573236019666008492470173696)
      · dsimp [z]; reduce_mod_char
      all_goals decide +kernel

private theorem adjacentLarge_prime : Nat.Prime adjacentLarge := by
  unfold adjacentLarge
  let z : ZMod 158000373181258234077770964034191626978142507914851163619225657267540347258689173262995900263708529317368319621764718510501263351255087565043667805122254151210021970047709861591475121092066466783849734509345974842360379096821292704568549807130711451240939161943750373477665673979329506153257679024570341785601 := 15744610425102701843740924552072356835034059750189245293116345315482040210635888903211101034179088772032583437271478871307200398396988291520296069981079091547936826161148046547627335016751402888530764919454254282465004158073440094196757759328156493531330713526653772907234607263944356857438297546443227341185
  apply prime_of_partial_order_cover z (F := 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096) (ps := [2])
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (Covers.cons 512 (by decide : Nat.Prime 2) covers_one)
  · dsimp [z]; reduce_mod_char
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl
    · apply quotient_unit (x := 158000373181258234077770964034191626978142507914851163619225657267540347258689173262995900263708529317368319621764718510501263351255087565043667805122254151210021970047709861591475121092066466783849734509345974842360379096821292704568549807130711451240939161943750373477665673979329506153257679024570341785600)
      · dsimp [z]; reduce_mod_char
      all_goals decide +kernel

private theorem separatedSmall_prime : Nat.Prime separatedSmall := by
  unfold separatedSmall
  let z : ZMod 119597504699702413294979410275881162087621759463324839128441643348345102922360870248200830249892708900769607012365612036040088408207833324290285465828106918214983936291303604395365634589335158079773970311578292388806190853169353511963157970374329749499233592683059467263036761205532101305870315405171113328641 := 43139878884414040978710250583927139204984703415775631612538906435733335466130837916192043784320922821957813018969341603579696773614263416675206139105073938788853244722964987131031640411494792862182751350638955554288016936620531321992974688681543993615800153278845858590106970031719830580215014295818075190642
  apply prime_of_partial_order_cover z (F := 20321208893819248729041881637905735536960913821835346213112272813140798608080219636715340733159213007592704535063892920825220728636856520075063499274846208) (ps := [2, 97])
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (Covers.cons 506 (by decide : Nat.Prime 2) (Covers.cons 1 (by decide : Nat.Prime 97) covers_one))
  · dsimp [z]; reduce_mod_char
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · apply quotient_unit (x := 119597504699702413294979410275881162087621759463324839128441643348345102922360870248200830249892708900769607012365612036040088408207833324290285465828106918214983936291303604395365634589335158079773970311578292388806190853169353511963157970374329749499233592683059467263036761205532101305870315405171113328640)
      · dsimp [z]; reduce_mod_char
      all_goals decide +kernel
    · apply quotient_unit (x := 59547722329737183296361418775329554234560468651377922793281972806653954173399693883772557780635265491820311582653729019869413131130535205721399183411219960467089556648468234153803437897749830987810176689662213175001211565676969401475057586681349050196097781783289279366088635731864735518914684991223731871787)
      · dsimp [z]; reduce_mod_char
      all_goals decide +kernel

private theorem separatedLarge_prime : Nat.Prime separatedLarge := by
  unfold separatedLarge
  let z : ZMod 172220406767571475144770350797268873406175333627187768344955966421616948208199653157409195559845500817108234097806481331897727307819279986978011070792473961726784070886629799095300576375923397854398298976457989375247360688997717929468935847268748658020017835087410950865546029120195620432456881192184565465089 := 71862621498107583225814135080765258930849435695603981519449160791777334604314169236211516895058608479301626912603145445470604112598970287933449596635834195204565088958447027854172799714769041033479628693740983745591353384794544778741317226969309173133899539649496451524754770089148462040465884889214121297581
  apply prime_of_partial_order_cover z (F := 169273575115525288382122065602348807359426993484978966393759963226987270879678530582123663014357155774586652209604386392028642770500825445573724818701811712) (ps := [2, 101])
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (Covers.cons 509 (by decide : Nat.Prime 2) (Covers.cons 1 (by decide : Nat.Prime 101) covers_one))
  · dsimp [z]; reduce_mod_char
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · apply quotient_unit (x := 172220406767571475144770350797268873406175333627187768344955966421616948208199653157409195559845500817108234097806481331897727307819279986978011070792473961726784070886629799095300576375923397854398298976457989375247360688997717929468935847268748658020017835087410950865546029120195620432456881192184565465088)
      · dsimp [z]; reduce_mod_char
      all_goals decide +kernel
    · apply quotient_unit (x := 159852168935178151668242791794913714096082206922838045837723700689832482623847247693830961334374727785805957057949681313627411034622025312723926596338328540016854550856490512325408016103284436670744468094545653937482031489550957960413755663501111694645063318225520070141560914350276918636998934415625576322417)
      · dsimp [z]; reduce_mod_char
      all_goals decide +kernel

/-- The prime pairs and products have the equal widths used in the study. -/
def FullPair (N p q : ℕ) : Prop := N=p*q ∧ p.Prime ∧ q.Prime ∧
  2^1023 ≤ p ∧ p<q ∧ q<2^1024 ∧ 2^2047 ≤ N ∧ N<2^2048

/-- For two previously published 2048-bit products, the low 506 bits are
identical. The digits at the 1020-bit radix distinguish them. -/
theorem grouped_examples :
    FullPair adjacentN adjacentSmall adjacentLarge ∧
    FullPair separatedN separatedSmall separatedLarge ∧
    adjacentN % 2^506 = 1 ∧ separatedN % 2^506 = 1 ∧
    value (2^1020) adjacentN = 0 ∧ value (2^1020) separatedN = 7 * 2^1014 := by
  have a : FullPair adjacentN adjacentSmall adjacentLarge :=
    ⟨by decide +kernel, adjacentSmall_prime, adjacentLarge_prime, by decide +kernel,
     by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
  have s : FullPair separatedN separatedSmall separatedLarge :=
    ⟨by decide +kernel, separatedSmall_prime, separatedLarge_prime, by decide +kernel,
     by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
  refine ⟨a,s,by decide +kernel,by decide +kernel,?_,?_⟩
  · rw [a.1,value_eq (by decide +kernel) adjacentSmall_prime adjacentLarge_prime
      (by decide +kernel)]
    decide +kernel
  · rw [s.1,value_eq (by decide +kernel) separatedSmall_prime separatedLarge_prime
      (by decide +kernel)]
    decide +kernel

end PrimeFactors.CyclotomicDigitPeriod
