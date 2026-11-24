import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

namespace PrimeFactors

/-- The ascending 233-modulus schedule for the central-third CRT decoder. -/
def phaseSchedule233 : List ℕ :=
  [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
    41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
    283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359,
    367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
    439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
    509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593,
    599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
    751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
    829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911,
    919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
    1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
    1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163,
    1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249,
    1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321,
    1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439,
    1447, 1451, 1453, 1459, 1471]

/-- The descending 89-modulus schedule under the 53-fractional-bit cap. -/
def phaseSchedule89 : List ℕ :=
  [
    8388593, 8388587, 8388581, 8388571, 8388547, 8388539, 8388473, 8388461, 8388451,
    8388449, 8388439, 8388427, 8388421, 8388409, 8388377, 8388371, 8388319, 8388301,
    8388287, 8388283, 8388277, 8388239, 8388209, 8388187, 8388113, 8388109, 8388091,
    8388071, 8388059, 8388019, 8388013, 8387999, 8387993, 8387959, 8387957, 8387947,
    8387933, 8387921, 8387917, 8387891, 8387879, 8387867, 8387861, 8387857, 8387839,
    8387831, 8387809, 8387807, 8387741, 8387737, 8387723, 8387707, 8387671, 8387611,
    8387609, 8387591, 8387581, 8387563, 8387557, 8387543, 8387539, 8387513, 8387507,
    8387501, 8387473, 8387471, 8387447, 8387437, 8387413, 8387377, 8387371, 8387369,
    8387339, 8387311, 8387297, 8387251, 8387243, 8387231, 8387221, 8387219, 8387191,
    8387173, 8387167, 8387153, 8387149, 8387147, 8387131, 8387129, 8387117]

/-- The least exponent B satisfying 128*m² ≤ 2^B. -/
def phasePrecision (m : ℕ) := Nat.clog 2 (128*m^2)

private def phase233Bits : List ℕ :=
    List.replicate 1 9 ++
    List.replicate 1 11 ++
    List.replicate 1 12 ++
    List.replicate 1 13 ++
    List.replicate 1 14 ++
    List.replicate 1 15 ++
    List.replicate 2 16 ++
    List.replicate 3 17 ++
    List.replicate 3 18 ++
    List.replicate 4 19 ++
    List.replicate 6 20 ++
    List.replicate 7 21 ++
    List.replicate 11 22 ++
    List.replicate 12 23 ++
    List.replicate 18 24 ++
    List.replicate 25 25 ++
    List.replicate 31 26 ++
    List.replicate 44 27 ++
    List.replicate 57 28 ++
    List.replicate 4 29

private def phaseBitsCheck : List ℕ → List ℕ → Bool
  | [], [] => true
  | m :: ms, b :: bs =>
    decide (2^(b-1) < 128*m^2 ∧ 128*m^2 ≤ 2^b) && phaseBitsCheck ms bs
  | _, _ => false

private theorem phaseBitsCheck_sound (ms bs : List ℕ) (h : phaseBitsCheck ms bs = true) :
    ms.map phasePrecision = bs := by
  induction ms generalizing bs with
  | nil => cases bs <;> simp_all [phaseBitsCheck]
  | cons m ms ih =>
    cases bs with
    | nil => simp [phaseBitsCheck] at h
    | cons b bs =>
      simp only [phaseBitsCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      have lower := (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mp h.1.1
      have upper := (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp h.1.2
      simp [phasePrecision, show Nat.clog 2 (128*m^2) = b by omega, ih bs h.2]

/-- One gcd per modulus certifies pairwise coprimality of the list. -/
private def phaseProductCheck : List ℕ → ℕ × Bool
  | [] => (1, true)
  | m :: ms =>
    let (p, ok) := phaseProductCheck ms
    (m*p, ok && (m.gcd p == 1))

private theorem phaseProductCheck_spec (ms : List ℕ) :
    (phaseProductCheck ms).1 = ms.prod ∧
      ((phaseProductCheck ms).2 = true ↔ ms.Pairwise Nat.Coprime) := by
  induction ms with
  | nil => simp [phaseProductCheck]
  | cons m ms ih =>
    simp [phaseProductCheck, ih, Nat.Coprime, List.pairwise_cons, and_comm,
      ← Nat.coprime_list_prod_right_iff]

set_option maxRecDepth 8192 in
/-- This checks the actual schedule; the preceding list ends below the
lower end of the 2048-bit range. -/
theorem phaseSchedule233_checked :
    phaseSchedule233.length = 233 ∧ phaseSchedule233.Pairwise Nat.Coprime ∧
    phaseSchedule233.getLast? = some 1471 ∧
    phaseSchedule233.all (fun m => 1 < m && m ≤ 1471) = true ∧
    9*phaseSchedule233.dropLast.prod < 2^2047 ∧
    2^2048 < 9*phaseSchedule233.prod ∧
    (phaseSchedule233.map phasePrecision).sum = 5835 := by
  rw [phaseBitsCheck_sound phaseSchedule233 phase233Bits (by decide +kernel),
    ← (phaseProductCheck_spec phaseSchedule233).2]
  decide +kernel

set_option maxRecDepth 8192 in
/-- Each modulus at this cap fits 53 fractional bits, and the CRT product
covers every 2048-bit input. -/
theorem phaseSchedule89_checked :
    phaseSchedule89.length = 89 ∧ phaseSchedule89.Pairwise Nat.Coprime ∧
    phaseSchedule89.all (fun m => 1 < m && m ≤ 2^23) = true ∧
    2^2048 < 9*phaseSchedule89.prod ∧
    phaseSchedule89.map phasePrecision = List.replicate 89 53 ∧
    (phaseSchedule89.map phasePrecision).sum = 4717 := by
  rw [phaseBitsCheck_sound phaseSchedule89 (List.replicate 89 53) (by decide +kernel),
    ← (phaseProductCheck_spec phaseSchedule89).2]
  decide +kernel

/-- The 53-bit cap corresponds exactly to the modulus cap used below. -/
theorem phasePrecision_le_53 (m : ℕ) : phasePrecision m ≤ 53 ↔ m ≤ 2^23 := by
  rw [phasePrecision, ← Nat.le_pow_iff_clog_le (by decide : 1 < 2),
    show (2:ℕ)^53 = 128*(2^23)^2 by decide +kernel,
    Nat.mul_le_mul_left_iff (by decide : 0 < 128)]
  exact pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)

/-- Under the cap m ≤ 2^23, even the largest possible product of 88
moduli falls short of the 2048-bit central-third cutoff. -/
theorem phaseSchedule88_short (ms : List ℕ) (size : ms.length ≤ 88)
    (cap : ∀ m ∈ ms, phasePrecision m ≤ 53) : 9*ms.prod < 2^2047 := by
  have bound (t : List ℕ) (h : ∀ m ∈ t, m ≤ 2^23) : t.prod ≤ (2^23)^t.length := by
    induction t with
    | nil => simp
    | cons m t ih =>
      rw [List.prod_cons, List.length_cons, pow_succ']
      exact Nat.mul_le_mul (h m (List.mem_cons_self ..))
        (ih (fun k hk => h k (List.mem_cons_of_mem _ hk)))
  have power : (2^23:ℕ)^ms.length ≤ (2^23)^88 :=
    Nat.pow_le_pow_right (by decide) size
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 9 ((bound ms (fun m hm => (phasePrecision_le_53 m).mp (cap m hm))).trans power)) (by decide +kernel)

end PrimeFactors
