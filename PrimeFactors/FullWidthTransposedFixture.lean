import PrimeFactors.Certificate
import PrimeFactors.FixedEndpointPartners
import PrimeFactors.PartialOrder
import PrimeFactors.TransposedBlockQuotient
import Mathlib.Tactic.ReduceModChar

/-! A 2,048-bit product constructed by transposing two 512-bit blocks.
The planted coefficient grid makes both primality certificates inexpensive.
The ordinary Fermat rank measures an ascending scan on this fixture. -/

open private PrimeFactors.FixedEndpointPartners.ordinary_miss from PrimeFactors.FixedEndpointPartners

namespace PrimeFactors.FullWidthTransposedFixture

set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

abbrev B : ℕ := 2^512
abbrev F : ℕ := 2^499
abbrev a : ℕ := 1+6048*F
abbrev b : ℕ := 1+7920*F
abbrev p : ℕ := B*a+b
abbrev q : ℕ := B*b+a
abbrev N : ℕ := 23066844963085184387347261723392618985438141061899048680312762958313515560278209934334290909233292916072067328140626290998629420137971329674155976078141556804790245110176018125297668933961624009382559417169811396112692192183067175667025438082590591882160968871298787901903425749131195696553574644681617773531500771815568086122993062200619183263152327117000230264857108801533044296786923365541363305468922707903624318857533171079291855421005317076781035351707420475247068411477803972667212424914661444538244694188428750185034736821770144107540632078718976540057554604194960729265856208873479120076463546625540164157441

/-- A certificate of order 2^(k+1) times one odd prime. Both prime-divisor
checks use the same modular power u. -/
private theorem mixed_order {n k l : ℕ} (z u : ZMod n) (hn : 1<n) (prime : l.Prime)
    (large : n≤(2^(k+1)*l)^2) (power : z^(2^k)=u) (half : u^l= -1)
    (two : Nat.Coprime ((-1-1 : ZMod n).val) n)
    (other : Nat.Coprime ((u^2-1).val) n) : n.Prime := by
  have twice : 2^(k+1)*l=(2^k*l)*2 := by rw [pow_succ]; ring
  apply prime_of_partial_order_cover z hn (Nat.mul_pos (by positivity) prime.pos) large
      (ps:=[2,l])
  · simpa only [pow_one,mul_one] using
      Covers.cons (k+1) Nat.prime_two (Covers.cons 1 prime covers_one)
  · rw [twice,pow_mul,pow_mul,power,half]
    ring
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · rw [twice,Nat.mul_div_cancel _ (by decide : 0<2),pow_mul,power,half]
      exact two
    · rw [Nat.mul_div_cancel _ prime.pos,pow_succ 2 k,pow_mul,power]
      exact other

/-- The certified order 4297·2^503 exceeds the square root of p. -/
theorem p_prime : Nat.Prime p := by
  let z : ZMod p := 64983196208459119657615029367318797431445350341291732007422490625846452409336088273670792957602209537790785451539996671988599414610963436045736983495788707511235444694792559770511113120712679103307573090714056777207293532471149274273670376662313413909229170627972654195418005183351412103447630499645524676896
  let u : ZMod p := 34069310758265029133843668442396393606869061709668815389672595346686834075516843601417478996383312239421695641853806735873646332647005948481695054238992247349049502955996698425152125794823547136730269904541119387913998901423168513175790814485838509000290152676715945219372221261803440972395838008303542894098
  apply mixed_order (k:=502) (l:=4297) z u
  · decide +kernel
  · norm_num
  · decide +kernel
  · unfold z u p B a b F
    reduce_mod_char
  · unfold u p B a b F
    reduce_mod_char
  · decide +kernel
  · decide +kernel

/-- The certified order 829·2^504 exceeds the square root of q. -/
theorem q_prime : Nat.Prime q := by
  let z : ZMod q := 126100401788243249040476927131753159374118778318295311956840702286612462884910457323908753826408744829396563838681862255452730175612336212905676655489994087304433191110597268684635908713269297667447252265195431800349042589236917794896053422051087650678567797220137218957144872740865305538284921386817860557872
  let u : ZMod q := 125990179120853177971194921701273841521739148186881202592059926370161736453445707570256806055226817132680672045254525650107468551174996496500626815369349983222977231653150338799705245709289515174558162938018934506921517572025104166570330478811894838022148424155576455593967580795943672716618528885079240837553
  apply mixed_order (k:=503) (l:=829) z u
  · decide +kernel
  · norm_num
  · decide +kernel
  · unfold z u q B a b F
    reduce_mod_char
  · unfold u q B a b F
    reduce_mod_char
  · decide +kernel
  · decide +kernel

theorem product : p*q=N := by decide +kernel

/-- Both factors and the product have the claimed full binary widths. -/
theorem data : ExactFactorization N [p,q] ∧ 2^1023≤p ∧ p<q ∧ q<2^1024 ∧
    2^2047≤N ∧ N<2^2048 := by
  refine ⟨⟨by decide +kernel,?_⟩,by decide +kernel⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.elim (fun eq => eq ▸ p_prime) (fun eq => eq ▸ q_prime)

/-- The swapped blocks each have 512 bits. -/
theorem block_width : 2^511≤a ∧ a<b ∧ b<2^512 := by decide +kernel

theorem valid : TransposedRadixProducts.Valid B a b := by
  simp only [TransposedRadixProducts.Valid,Nat.even_iff,Nat.odd_iff]
  decide +kernel

attribute [local irreducible] TransposedRadixProducts.recognize TransposedBlockQuotient.recognize ceilSqrt

/-- With the supplied radix, the public recognizer returns the two certified primes. -/
theorem recognized : TransposedRadixProducts.recognize B N=some (p,q) :=
  TransposedRadixProducts.complete valid product

/-- Here the quotient alone overshoots the block product. The low block of N
corrects the carry and the quotient-based recognizer recovers the factors. -/
theorem quotient_reading : 2^507<N/(B+1)^2-a*b ∧
    TransposedBlockQuotient.recognize B N=some (p,q) :=
  ⟨by decide +kernel,TransposedBlockQuotient.complete (a:=a) (b:=b) (by decide +kernel)
    block_width.2.1 block_width.2.2 product⟩

/-- The common planted residue gives a second way to read the factor sum if F is supplied. -/
theorem planted_sum : ((N-1)/F)%F=16384+6048+7920 ∧
    (B+1)*(2+F*(((N-1)/F)%F-16384))=p+q := by decide +kernel

abbrev midpoint : ℕ := (p+q)/2
abbrev start : ℕ := 151877730306602832072029141760295328616571758014658376748549969786763718940089501978581889816821293213122445533023885904633887208107260750411547443241593334780098080351058417622280162008096125729839600241433715225122719455668702762196849305432033638853017130397443725728693466918971530288884829231813794579236

theorem ceil_value : ceilSqrt N=start := by
  have top := ceilSqrt_le_iff.mpr (by decide +kernel : N≤start^2)
  have bottom : ¬ceilSqrt N≤start-1 := fun h =>
    (not_le_of_gt (by decide +kernel : (start-1)^2<N)) (ceilSqrt_le_iff.mp h)
  omega

/-- The first ordinary square hit has one-based rank between these powers of two. -/
theorem inclusive_rank : 2^1016<midpoint-ceilSqrt N+1 ∧ midpoint-ceilSqrt N+1<2^1017 := by
  rw [ceil_value]
  decide +kernel

theorem midpoint_hit : midpoint^2=N+((q-p)/2)^2 := by decide +kernel

theorem no_earlier {m : ℕ} (from_start : ceilSqrt N≤m) (early : m<midpoint) :
    ¬IsSquare (m^2-N) := by
  rintro ⟨d,hd⟩
  have lo := ceilSqrt_le_iff.mp from_start
  have eq : m^2=p*q+d^2 := by rw [product,pow_two d]; omega
  exact PrimeFactors.FixedEndpointPartners.ordinary_miss p_prime q_prime (by decide +kernel)
    (by decide +kernel) (by decide +kernel : p+q=2*midpoint) early ⟨d,eq⟩

end PrimeFactors.FullWidthTransposedFixture
