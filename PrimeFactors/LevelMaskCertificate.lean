import Mathlib.Data.Nat.Bits
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Int.ModEq

namespace PrimeFactors.LevelMaskCertificate

/-- Duplicate a word of p bits k times by repeated doubling, producing
2^k periods. -/
def repeatWord (p bits : ℕ) : ℕ → ℕ
  | 0 => bits
  | k+1 =>
    let word := repeatWord p bits k
    word ||| (word <<< (p*2^k))

theorem repeatWord_bit {p bits i : ℕ} (k : ℕ) (inside : i < p*2^k)
    (hit : bits.testBit (i%p) = true) : (repeatWord p bits k).testBit i = true := by
  induction k generalizing i with
  | zero =>
    simp only [pow_zero, mul_one] at inside
    simpa [repeatWord, Nat.mod_eq_of_lt inside] using hit
  | succ k ih =>
    rw [repeatWord, Nat.testBit_or, Bool.or_eq_true]
    by_cases low : i < p*2^k
    · exact Or.inl (ih low hit)
    · have h := le_of_not_gt low
      right
      rw [Nat.testBit_shiftLeft]
      simp only [decide_eq_true_eq, Bool.and_eq_true]
      refine ⟨h, ih ?_ ?_⟩
      · rw [pow_succ, ← Nat.mul_assoc] at inside
        omega
      · have eq : (i-p*2^k)%p = i%p := by
          have decomp := Nat.sub_add_cancel h
          calc _ = ((i-p*2^k)+p*2^k)%p := (Nat.add_mul_mod_self_left ..).symm
               _ = _ := by rw [decomp]
        rwa [eq]

/-- Align each periodic bitmask to a signed first level and intersect it with
the full block of the requested width. -/
def block (start : ℤ) (width : ℕ) (depth : ℕ → ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 2^width-1
  | (p,bits)::rows =>
    (repeatWord p bits (depth p) >>> (start % (p:ℤ)).toNat) &&& block start width depth rows

private theorem aligned {start : ℤ} {p : ℕ} (hp : 0<p) (i : ℕ) :
    ((start % (p:ℤ)).toNat+i)%p = ((start+(i:ℤ))%p).toNat := by
  apply Int.ofNat_inj.mp
  have hn : (p:ℤ)≠0 := by exact_mod_cast hp.ne'
  simp only [Int.natCast_emod, Int.natCast_add, Int.toNat_of_nonneg (Int.emod_nonneg _ hn)]
  exact Int.emod_add_emod ..

theorem block_bit (start : ℤ) (width : ℕ) (depth : ℕ → ℕ) (i : ℕ) (rows : List (ℕ × ℕ))
    (inside : i < width)
    (room : ∀ row ∈ rows, 0 < row.1 ∧ (start % (row.1:ℤ)).toNat+width ≤ row.1*2^(depth row.1))
    (hit : ∀ row ∈ rows, row.2.testBit ((start+(i:ℤ))%row.1).toNat = true) :
    (block start width depth rows).testBit i = true := by
  induction rows with
  | nil => simpa only [block, Nat.testBit_two_pow_sub_one, decide_eq_true_eq] using inside
  | cons row rows ih =>
    obtain ⟨p,b⟩ := row
    have ⟨pos,limit⟩ := room (p,b) (by simp)
    have head := hit (p,b) (by simp)
    dsimp only [Prod.fst, Prod.snd] at pos limit head
    have tail := ih (fun t ht => room t (List.mem_cons_of_mem _ ht))
      (fun t ht => hit t (List.mem_cons_of_mem _ ht))
    rw [block, Nat.testBit_and, Bool.and_eq_true, Nat.testBit_shiftRight]
    refine ⟨repeatWord_bit (depth p) (by omega) ?_, tail⟩
    rwa [aligned pos]

/-- The nonzero-residue quartic image masks for the fresh 604-bit remainder. -/
def fresh604 : List (ℕ × ℕ) := [
  (7, 30),
  (11, 824),
  (13, 3121),
  (17, 64671),
  (19, 378805),
  (23, 4127174),
  (29, 267825367),
  (31, 1851452401),
  (37, 93948970353),
  (41, 2160116701983),
  (43, 446231019515),
  (47, 77152637667196),
  (53, 8407640174411194),
  (59, 412711730996752381),
  (61, 2066574547247952739),
  (67, 132930247016030578394),
  (71, 1613068381684172024735),
  (73, 6483093058530969006071),
  (79, 301691482026666441305967)]

private theorem fresh604_room : ∀ row ∈ fresh604, 0 < row.1 ∧
    ((-12743:ℤ) % (row.1:ℤ)).toNat+25487 ≤ row.1*2^12 := by decide +kernel

private theorem fresh604_zero : block (-12743) 25487 (fun _ => 12) fresh604 = 0 := by decide +kernel

/-- No one of the 25,487 consecutive trace levels belongs to all 19 images. -/
theorem fresh604_empty (j : ℤ) (lo : -12743 ≤ j) (hi : j ≤ 12743)
    (survives : ∀ row ∈ fresh604, row.2.testBit (j % (row.1:ℤ)).toNat = true) : False := by
  let i := (j+12743).toNat
  have offset : -12743+(i:ℤ) = j := by dsimp [i]; omega
  have cap : i < 25487 := by dsimp [i]; omega
  have bit := block_bit (-12743) 25487 (fun _ => 12) i fresh604 cap fresh604_room (by rwa [offset])
  simp [fresh604_zero] at bit

/-- Nonzero-residue images of the fresh 600-bit remainder. The first 42
auxiliary primes already exclude every position. -/
def fresh600 : List (ℕ × ℕ) := [
  (7, 45),
  (11, 766),
  (13, 6709),
  (17, 30523),
  (19, 210922),
  (23, 5306220),
  (29, 460619605),
  (31, 1724577707),
  (37, 64321349919),
  (41, 475650823787),
  (43, 8681030513136),
  (47, 33852561775935),
  (53, 6191680041281464),
  (59, 512683172251561420),
  (61, 2003024173867848682),
  (67, 89980605257467150167),
  (71, 2324117640872428576245),
  (73, 7004203923784814410239),
  (79, 202087962865061545375509),
  (83, 9645605155076566365728233),
  (89, 420172474205890751361966659),
  (97, 48142724108860960199471812071),
  (101, 586816496798743245934821309367),
  (103, 2441096849069409424043036920591),
  (107, 154306674128173911593789781307354),
  (109, 565522760369807198746779645280146),
  (113, 8838976019826518450513648516385359),
  (127, 110299797525751238460511520296237790809),
  (131, 2366653849042990053639240412919481758686),
  (137, 125203784890716855253625619751143636523727),
  (139, 644869475807183631916032097304437260590029),
  (149, 256256817189746643673559820379743383674681950),
  (151, 2553397885924886058403286756690913373405428143),
  (157, 13557965848252581307112574285373709655225583229),
  (163, 7096944105201138744926471763792949146033666637181),
  (167, 56952673157387743087689792910780104834105898354685),
  (173, 5756569358380011418637065034465259857128587483503852),
  (179, 631433469546488500418438909118316156683127248677416443),
  (181, 1414394147774547369051835608828833974942921869655728352),
  (191, 3098934538946489221826115450040245436476312295251661815550),
  (193, 10692986694236229275124768715413509488404081845493441621470),
  (197, 197186115511400667132587072825108454523709215470846729606129)]

/-- Enough doublings of each p-bit period to cover a one-megabit block
starting at any residue. -/
private def chunkDepth (p : ℕ) :=
  if p<8 then 18 else if p<16 then 17 else if p<32 then 16 else if p<64 then 15
  else if p<128 then 14 else 13

private theorem chunkRoom : ∀ row ∈ fresh600, 0 < row.1 ∧
    row.1+1048576 ≤ row.1*2^(chunkDepth row.1) := by decide +kernel

private theorem fresh600_blocks : ∀ k ∈ List.range 23,
    block (-11983988+(k:ℤ)*1048576) (min 1048576 (23967979-k*1048576))
      chunkDepth fresh600 = 0 := by decide +kernel

/-- The 23 disjoint certified blocks include every one of the 23,967,979
admissible levels of the fresh 600-bit remainder. -/
theorem fresh600_empty (j : ℤ) (lo : -11983988 ≤ j) (hi : j ≤ 11983990)
    (survives : ∀ row ∈ fresh600, row.2.testBit (j % (row.1:ℤ)).toNat = true) : False := by
  let i := (j+11983988).toNat
  let k := i/1048576
  let t := i%1048576
  let start : ℤ := -11983988+(k:ℤ)*1048576
  let size := min 1048576 (23967979-k*1048576)
  have hk : k ∈ List.range 23 := List.mem_range.mpr (by dsimp [k,i]; omega)
  have clear := fresh600_blocks k hk
  have cap : t<size := by dsimp [size,t,k,i]; omega
  have offset : start+(t:ℤ)=j := by dsimp [start,k,t,i]; omega
  have room (row) (hr : row ∈ fresh600) : 0<row.1 ∧
      (start % (row.1:ℤ)).toNat+size ≤ row.1*2^(chunkDepth row.1) := by
    obtain ⟨hp,full⟩ := chunkRoom row hr
    have h := Int.emod_lt_of_pos start (by exact_mod_cast hp : 0<(row.1:ℤ))
    have sz : size ≤ 1048576 := min_le_left ..
    exact ⟨hp,by omega⟩
  have bit := block_bit start size chunkDepth t fresh600 cap room (by rwa [offset])
  change block start size chunkDepth fresh600=0 at clear
  simp [clear] at bit

end PrimeFactors.LevelMaskCertificate
