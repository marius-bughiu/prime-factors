import PrimeFactors.FactorSum
import PrimeFactors.ProductDeficitBand
import PrimeFactors.Certificate

/-! The first odd-prime cutoff that isolates one sum in each toy product's
width-and-product window. Zero means the modulo-four class already suffices.
The two factor widths are fixed at 8 and 9 bits in the census. -/

namespace PrimeFactors.ToySumIsolation

set_option maxRecDepth 8192

/-- The advertised factor interval is [A,2A). The product bit length is unrestricted. -/
noncomputable def primes (A : ℕ) := (List.range' A A).filter Nat.Prime

theorem catalog_eight : primes 128 = [131,137,139,149,151,157,163,167,173,179,181,191,
    193,197,199,211,223,227,229,233,239,241,251] := by decide +kernel

theorem catalog_nine : primes 256 = [257,263,269,271,277,281,283,293,307,311,313,317,
    331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,
    449,457,461,463,467,479,487,491,499,503,509] := by decide +kernel

noncomputable def pairs (A : ℕ) := (primes A).flatMap fun p =>
  ((primes A).filter (p < ·)).map fun q => (p,q)

theorem nodup_pairs (A : ℕ) : (pairs A).Nodup := by
  have uniq : (primes A).Nodup := List.Nodup.filter _ (List.nodup_range' 1)
  apply List.nodup_flatMap.mpr
  constructor
  · intro p _
    exact (uniq.filter _).map (by intro x y h; exact congrArg Prod.snd h)
  · apply uniq.imp
    intro p q ne x hx hy
    obtain ⟨r,_,eq⟩ := List.mem_map.mp hx
    obtain ⟨s,_,eq'⟩ := List.mem_map.mp hy
    exact ne (congrArg Prod.fst (eq.trans eq'.symm))

theorem mem_pairs {A p q : ℕ} :
    (p,q) ∈ pairs A ↔ A ≤ p ∧ p < 2*A ∧ p.Prime ∧ p < q ∧ q < 2*A ∧ q.Prime := by
  simp only [pairs, primes, List.mem_flatMap, List.mem_filter, List.mem_range',
    List.mem_map, decide_eq_true_eq, Prod.mk.injEq, one_mul]
  constructor
  · rintro ⟨x, ⟨⟨i,hi,rfl⟩, prime⟩, y, ⟨⟨⟨j,hj,rfl⟩,prime'⟩,lt⟩, rfl,rfl⟩
    exact ⟨by omega, by omega, prime, lt, by omega, prime'⟩
  · rintro ⟨lo,hi,prime,lt,hi',prime'⟩
    exact ⟨p, ⟨⟨p-A, by omega, by omega⟩, prime⟩, q,
      ⟨⟨⟨q-A, by omega, by omega⟩,prime'⟩,lt⟩, rfl, rfl⟩

private def bisect (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, hi => hi
  | fuel+1, lo, hi =>
    let m := (lo+hi)/2
    if m*m < n then bisect n fuel m hi else bisect n fuel lo m

/-- A tiny interval bisection gives the endpoint to the kernel. The two
squared comparisons certify the result, with an exact fallback for other inputs. -/
private def checkedRoot (n A : ℕ) : ℕ :=
  let r := bisect n 11 0 (4*A)
  if (r-1)^2 < n ∧ n ≤ r^2 then r else ceilSqrt n

private theorem checkedRoot_eq (n A : ℕ) : checkedRoot n A = ceilSqrt n := by
  dsimp only [checkedRoot]
  split_ifs with h
  · apply le_antisymm _ (ceilSqrt_le_iff.mpr h.2)
    by_contra! lt
    have := ceilSqrt_le_iff.mp (show ceilSqrt n ≤ bisect n 11 0 (4*A)-1 by omega)
    omega
  · rfl

/-- Four-spaced sums in the public inclusive interval, with both width endpoints used. -/
def menu (n A : ℕ) : List ℕ :=
  let lo := checkedRoot (4*n) A
  let hi := ProductDeficitBand.sumCap n A
  let start := lo + ((n+1)%4 + 4 - lo%4)%4
  List.range' start ((hi+4-start)/4) 4

theorem mem_menu {n A s : ℕ} : s ∈ menu n A ↔
    ceilSqrt (4*n) ≤ s ∧ s ≤ ProductDeficitBand.sumCap n A ∧ s%4 = (n+1)%4 := by
  simp only [menu, checkedRoot_eq, List.mem_range']
  constructor
  · rintro ⟨i, bound, eq⟩
    omega
  · rintro ⟨lo, hi, four⟩
    refine ⟨(s - (ceilSqrt (4*n) + ((n+1)%4+4-ceilSqrt (4*n)%4)%4))/4, ?_, ?_⟩ <;> omega

/-- Each mask marks the square residues, including zero, for a single odd prime. -/
def rows : List (ℕ × ℕ) := [(3,3),(5,19),(7,23),(11,571),(13,5659),(17,107287),
  (19,199411),(23,340831),(29,332473075),(31,303908791),(37,96068509339),(41,1870503675703)]

theorem cutoffs_complete : rows.map Prod.fst = (List.range' 3 39).filter Nat.Prime := by
  decide +kernel

private theorem masks_ok : ∀ r ∈ rows, r.1.Prime ∧ r.1 ≠ 2 ∧ ∀ d : Fin r.1,
    r.2.testBit d.val = true ↔ ∃ x : Fin r.1, (x.val*x.val)%r.1 = d.val := by
  decide +kernel

def accepts (n : ℕ) (r : ℕ × ℕ) (s : ℕ) := r.2.testBit ((s*s-4*n)%r.1)

/-- On the public interval a mask lookup is the repository's local sum predicate. -/
theorem accepts_iff {n A s : ℕ} (inside : s ∈ menu n A) {r : ℕ × ℕ} (row : r ∈ rows) :
    accepts n r s = true ↔ AdmissibleSum (n : ZMod r.1) (s : ZMod r.1) := by
  obtain ⟨prime, odd, mask⟩ := masks_ok r row
  letI : Fact r.1.Prime := ⟨prime⟩
  letI : NeZero r.1 := ⟨prime.ne_zero⟩
  have above : 4*n ≤ s*s := by simpa only [pow_two] using ceilSqrt_le_iff.mp (mem_menu.mp inside).1
  let d := s*s-4*n
  have cast : (d : ZMod r.1) = (s : ZMod r.1)^2 - 4*(n : ZMod r.1) := by
    simp [d, Nat.cast_sub above, pow_two]
  rw [admissibleSum_iff_isSquare odd, ← cast, isSquare_iff_exists_sq]
  change r.2.testBit (d%r.1) = true ↔ _
  rw [mask ⟨d%r.1, Nat.mod_lt _ prime.pos⟩]
  constructor
  · rintro ⟨x,h⟩
    refine ⟨x.val, ?_⟩
    simpa only [Nat.cast_mul, pow_two] using (ZMod.natCast_eq_natCast_iff' _ _ r.1).mpr h.symm
  · rintro ⟨x,h⟩
    refine ⟨⟨x.val, ZMod.val_lt x⟩, (ZMod.natCast_eq_natCast_iff' _ _ r.1).mp ?_⟩
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← pow_two]
    exact h.symm

/-- Test successive cutoffs until exactly one sum remains. Both the cutoff
and the sum are returned, with a separate value for an exhausted list. -/
noncomputable def firstFrom (n : ℕ) (atPrime : ℕ) (sums : List ℕ) : List (ℕ × ℕ) → Option (ℕ × ℕ)
  | [] => match sums with | [s] => some (atPrime,s) | _ => none
  | r::rest => match sums with
    | [s] => some (atPrime,s)
    | _ => firstFrom n r.1 (sums.filter (accepts n r)) rest

noncomputable def first (n A : ℕ) := firstFrom n 0 (menu n A) rows

/-- Factors supplied by the population are used only here to check the returned sum. -/
private noncomputable def checkedCutoff (A : ℕ) (pq : ℕ × ℕ) : Option ℕ := do
  let (cut,s) ← first (pq.1*pq.2) A
  if s = pq.1+pq.2 then some cut else none

private noncomputable def observations (A : ℕ) :=
  (primes A).map fun p => ((primes A).filter (p < ·)).map fun q => checkedCutoff A (p,q)

/-- Entries are failure count, then first-hit counts for 0,3,5,…,41. -/
noncomputable def histogram (A : ℕ) : List ℕ :=
  (none :: ((0::rows.map Prod.fst).map some)).map fun k =>
    ((observations A).map (List.count k)).sum

/-- Small reference traces avoid re-evaluating each product for every histogram bin.
Rows follow the smaller prime; the remaining larger primes are in ascending order.
Letters a through m index 0,3,5,…,41. Lean checks every trace against the search. -/
private def decode (data : List String) : List (List (Option ℕ)) :=
  data.map fun line => line.toList.map fun c => (0::rows.map Prod.fst)[c.toNat-'a'.toNat]?

private def eightRows := [
  "aaaaaaaaabbbbbbcccdcde","aaaaaaaaadbcbbbebfdcc","aaaaaabbbdbcdebcccec","abbccdbdbcbcccbcdbc",
  "bbbbbebcccddbebbdd","bbbbcceddcebebbcb","bccgedecedbgbbcb","dccddgccbcbccbc",
  "dddcdcdbcbicbb","ceccdcbcbcebb","cdccdcbbbbfb","ddcbbfbcdab",
  "iccbbbbaaa","cbbcbcaaa","cbbbbaaa","bbbaaaa","aaaaaa","aaaaa","aaaa","aaa","aa","a",""]

private theorem eight_checked : observations 128 = decode eightRows := by
  rw [observations, catalog_eight]
  decide +kernel

/-- Every unordered pair appears exactly once, and every reported singleton
is the true factor sum. At 8 bits the last needed prime is 23. -/
theorem eight_bits : (pairs 128).Nodup ∧ (pairs 128).length = 253 ∧
    histogram 128 = [0,60,79,61,31,14,3,3,0,2,0,0,0,0] := by
  refine ⟨nodup_pairs 128, ?_, ?_⟩
  · rw [pairs, catalog_eight, List.length_flatMap]
    decide +kernel
  · rw [histogram, eight_checked]
    decide +kernel

private def nineRows := [
  "aaaaaaaaaaabbbbbcbbbgdccdfcdefdfgdffgdedgg","aaaaaaaaaaabbbbbbbbccdfcccddceeeeddeeedfd",
  "aaaaaaaaaabcbcebbbchdecdcdccdeegdfeddcee","aaaaaaaabbbdbbccdbbcddcfdcdccdfdceeefcg",
  "aaabbbbbbbcbbdddbbfbedccedfdfceedecfdd","aabcbdbbebcdbbcdgcccdddfceecfdfdceddg",
  "abbbbbdbcbbddhccfddcddgdgcedegefcfee","bcbcbbdcdcdcchddecdfdecdeedemedddee",
  "bdecgdhdcdfddcedfcddhfeegcfdedcdde","efccdcefcdeeddfdfcgdddfcedefcdcee",
  "ddeefccifddcfddcdeeeecddjfcdchec","cgecdcdeceeddcgifececededecdded",
  "deedddfidffeddfcffecccgcccdecc","eddceffdcfghcfdehfcgcddddcdie",
  "ceeedcgeefcededcdcdeeecbiedd","ceeegddedhgddeecfdcdcbccccc",
  "gfddiifdchddgcedddcecbgcec","cegdecddggecddfcdccfbdbcd","feeciddcfcfgdcdcdibdbcbb",
  "dfcdgdcedecccfeebbcbdbb","cfgfeegcddcdecebbcbcbb","dddcedeccfcddcccbcbcc",
  "cedecfceeecebcdbhbbd","hgcdcdedcdbebbebcbb","cdchfcedbcbeebcbbb","dcccfcddbcbbbacbb",
  "cecdcdbfbcdbaaab","cgcbbcbcbbbaaab","dbcebcbddaaaaa","cbbdbbbbaaaaa","bbbbbbbaaaaa",
  "cbcbccaaaaa","bdbcaaaaaa","bbbaaaaaa","beaaaaaa","baaaaaa",
  "aaaaaa","aaaaa","aaaa","aaa","aa","a",""]

private theorem nine_checked : observations 256 = decode nineRows := by
  rw [observations, catalog_nine]
  decide +kernel

theorem nine_bits : (pairs 256).Nodup ∧ (pairs 256).length = 903 ∧
    histogram 256 = [0,118,139,192,198,131,66,35,13,9,1,0,0,1] := by
  refine ⟨nodup_pairs 256, ?_, ?_⟩
  · rw [pairs, catalog_nine, List.length_flatMap]
    decide +kernel
  · rw [histogram, nine_checked]
    decide +kernel

private theorem isolated {A cap p q : ℕ}
    (valid : ∀ line ∈ observations A, ∀ r ∈ line, r.any (· ≤ cap) = true)
    (input : (p,q) ∈ pairs A) : ∃ cut ≤ cap, first (p*q) A = some (cut,p+q) := by
  obtain ⟨x,hx,hmem⟩ := List.mem_flatMap.mp input
  obtain ⟨y,hy,eq⟩ := List.mem_map.mp hmem
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
  have ok := valid _ (List.mem_map.mpr ⟨x,hx,rfl⟩) _ (List.mem_map.mpr ⟨y,hy,rfl⟩)
  cases found : first (x*y) A with
  | none => simp [checkedCutoff, found] at ok
  | some v =>
    obtain ⟨cut,sum⟩ := v
    by_cases matchSum : sum=x+y
    · subst sum
      exact ⟨cut, by simpa [checkedCutoff, found] using ok, rfl⟩
    · simp [checkedCutoff, found, matchSum] at ok

/-- Each eligible input individually returns the true sum by the stated cutoff. -/
theorem isolated_eight {p q : ℕ} (input : (p,q) ∈ pairs 128) :
    ∃ cut ≤ 23, first (p*q) 128 = some (cut,p+q) := by
  apply isolated _ input
  rw [eight_checked]
  decide +kernel

theorem isolated_nine {p q : ℕ} (input : (p,q) ∈ pairs 256) :
    ∃ cut ≤ 41, first (p*q) 256 = some (cut,p+q) := by
  apply isolated _ input
  rw [nine_checked]
  decide +kernel

/-- Remaining sums after every odd prime up to the given cutoff. -/
noncomputable def through (n A cut : ℕ) := (rows.takeWhile (fun r => r.1 ≤ cut)).foldl
  (fun sums r => sums.filter (accepts n r)) (menu n A)

theorem hardest_eight :
    ExactFactorization 40309 [173,233] ∧
    through 40309 128 19 = [406,410] ∧ through 40309 128 23 = [406] ∧
    (410*410-4*40309)%23 = 10 := by
  refine ⟨by unfold ExactFactorization; decide +kernel, ?_⟩
  decide +kernel

theorem hardest_nine :
    ExactFactorization 136831 [293,467] ∧
    through 136831 256 37 = [748,760] ∧ through 136831 256 41 = [760] ∧
    (748*748-4*136831)%41 = 3 := by
  refine ⟨by unfold ExactFactorization; decide +kernel, ?_⟩
  decide +kernel

end PrimeFactors.ToySumIsolation
