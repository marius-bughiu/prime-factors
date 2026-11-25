"""Lean certificates for successful approximate sums and entire excluded families."""

from scripts.factor import verify_file


def check_recovery(proof, p, q, work):
    """Tie the discovered primes to the public center, measured offset and tolerance."""
    b = work['winning_exponent']
    center = int(work['winning_center'])
    delta = int(work['sum_error'])
    tolerance = int(work['tolerance'])
    if not 0 < abs(delta) <= min(tolerance, 2**437) or not 0 <= b < 647:
        raise ValueError("expected a nonzero near-center hit within the proved spacing")
    source = 'import PrimeFactors.SmoothCenterSpacing\n' + proof.read_text()
    theorem = 'PrimeFactors.Generated.nearSumRecovery'
    source += f"""
theorem {theorem} :
    (({p}+{q} : ℤ) - (PrimeFactors.SmoothSumSelector.candidate {b} : ℕ) = ({delta}) ∧
      |({delta} : ℤ)| ≤ {tolerance}) ∧
    (∀ j<647, {p}+{q} ≠ PrimeFactors.SmoothSumSelector.candidate j) := by
  have c : PrimeFactors.SmoothSumSelector.candidate {b} = {center} := by
    rw [←PrimeFactors.SmoothCenterSpacing.fast_correct (by decide : {b}<647)]
    decide +kernel
  constructor
  · rw [c]
    decide +kernel
  · apply PrimeFactors.SmoothCenterSpacing.nearby_not_exact (b := {b}) (by decide)
    all_goals rw [c]; decide +kernel
#print axioms {theorem}
"""
    proof.write_text(source)
    verify_file(proof, theorem)


def covers_public_menu(n, tolerance, witnesses):
    """Check that the available witnesses cover the public Lean menu in order."""
    smallest = max(2**1023, (n-1)//(2**1024-1) + 1)
    expected = []
    for b in range(647):
        odd = 3**b
        center = odd << (1025 - odd.bit_length())
        if (4*n <= (center+tolerance)**2
                and smallest*max(0, center-tolerance) <= smallest**2+n):
            expected.append(b)
    return ([b for b, _ in witnesses] == expected
            and all(w['rootless_modulus'] for _, w in witnesses))


def _all_centers_exclusion(n, tolerance):
    return f"""
theorem noNearSmoothCenter {{p q : ℕ}} (pair : p*q={n}) (ordered : p≤q)
    (lo : 2^1023≤p) (hi : q<2^1024) (a b : ℕ) :
    ¬(2^a*3^b≤p+q+{tolerance} ∧ p+q≤2^a*3^b+{tolerance}) := by
  rintro ⟨below,above⟩
  obtain ⟨hb,center|edge⟩ := NearSmoothBoundary.dictionary (a:=a) (b:=b) rfl
    (by omega) (by omega) (by decide +kernel) below above
  · rw [←center] at below above
    exact noNearSmoothSum pair ordered lo hi ⟨b,hb,above,below⟩
  · have excluded := NearSmoothBoundary.excludes_upper (E:=allowance) pair ordered hi (by decide +kernel)
    change p+q+{tolerance}<2^1025 at excluded
    exact (Nat.not_le_of_gt excluded) (edge ▸ below)
#print axioms noNearSmoothCenter
"""


def check_absence(n, tolerance, witnesses, proof, chebyshev_cuts):
    """Replay a public menu and every polynomial excluding a viable interval."""
    if tolerance % 2 or tolerance < 0:
        raise ValueError("expected an even sum tolerance")
    source = [f"""import PrimeFactors.NearSmoothBoundary
import PrimeFactors.NearSmoothExclusion
import PrimeFactors.QuarticIntervalExtension

set_option exponentiation.threshold 16384
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace PrimeFactors.Generated
private abbrev input : ℕ := {n}
private abbrev allowance : ℕ := {tolerance}
"""]
    indices = []
    for b, w in witnesses:
        if not w['excluded'] or w['degree'] != 4 or w['depth'] != 2 or not w['rootless_modulus']:
            raise ValueError("expected a certified rootless quartic")
        indices.append(b)
        low, high = w['lower'], w['upper']
        coefficients = ', '.join(map(str, w['coefficients']))
        cuts, _ = chebyshev_cuts(w)
        source.append(f"""
private theorem band{b} : ∃ l u, NearSmoothExclusion.Covers input
    (SmoothSumSelector.candidate {b}) allowance l u ∧ ∀ d, l≤d → d≤u → ¬d∣input := by
  refine ⟨{low},{high},?_,?_⟩
  · rw [←SmoothCenterSpacing.fast_correct (by decide : {b}<647)]
    decide +kernel
  · intro d lo hi
    apply QuarticIntervalExtension.odd_interval_excludes
      (v := ![{coefficients}]) (c := {w['center']}) (cuts := [{', '.join(map(str, cuts))}])
      (l := (-{w['radius']})) (u := {w['radius']}) (t := ({w['anchor']}))
      (m := {w['rootless_modulus']}) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
    all_goals first | (unfold QuarticDivisorWindow.jets; decide +kernel) | decide +kernel
""")
    if indices != sorted(set(indices)):
        raise ValueError("expected one ordered certificate per exponent")
    theorem = 'PrimeFactors.Generated.noNearSmoothSum'
    source.append(f"""
theorem noNearSmoothSum {{p q : ℕ}} (pair : p*q={n}) (ordered : p≤q)
    (lo : 2^1023≤p) (hi : q<2^1024) :
    ¬NearSmoothSumPopulation.Near (p+q) {tolerance//2} := by
  apply NearSmoothExclusion.excludes (n := input) ?_ pair ordered lo hi
  intro b mem
  change b ∈ NearSmoothExclusion.viable input allowance at mem
  have menu : NearSmoothExclusion.viable input allowance = [{', '.join(map(str, indices))}] := by
    decide +kernel
  rw [menu] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
""")
    if len(indices) == 1:
        source.append(f"  subst b\n  exact band{indices[0]}\n")
    elif indices:
        patterns = ' | '.join('rfl' for _ in indices)
        cases = '\n'.join(f'  · exact band{b}' for b in indices)
        source.append(f"  rcases mem with {patterns}\n{cases}\n")
    else:
        source.append("  contradiction\n")
    source.append("#print axioms noNearSmoothSum\n")
    if tolerance <= 2**437 and n < (2**1024 - tolerance)**2:
        source.append(_all_centers_exclusion(n, tolerance))
        theorem = 'PrimeFactors.Generated.noNearSmoothCenter'
    source.append("end PrimeFactors.Generated\n")
    proof.write_text(''.join(source))
    verify_file(proof, theorem)
