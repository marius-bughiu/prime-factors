import PrimeFactors.PartialOrder
import PrimeFactors.Certificate
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-! The public rotation modulus 2^1024−1 is the product of the Fermat numbers
F₀ through F₉. The factor list follows [Keller's Fermat tables](https://homes.cerias.purdue.edu/~ssw/fdub.html).
For the historical certificates see [Brent (1982)](https://maths-people.anu.edu.au/~brent/pub/pub066.html)
and [Brent, §9](https://maths-people.anu.edu.au/brent/pd/rpb161tr.pdf#page=20).

Each order certificate below gives the residue, the covered order and its prime
factor powers. Lean checks that the square of the order covers the input and
that the order survives reduction at every possible prime divisor. The middle
entries can be independently reproduced by factoring the fixed predecessors,
retaining the largest prime powers until their product F reaches the square
root, then using the first base whose projection to order F passes the checks.
The final list and its distinctness are verified separately. -/

namespace PrimeFactors.BinaryRotationModulus

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-- One factored order and its reductions at the prime divisors. -/
private theorem certify {n F : ℕ} {ps : List ℕ} (z : ZMod n) (cover : Covers F ps)
    (size : 1<n ∧ 0<F ∧ n≤F^2) (full : z^F=1)
    (unit : ∀ p∈ps, Nat.Coprime ((z^(F/p)-1).val) n) : n.Prime :=
  prime_of_partial_order_cover z size.1 size.2.1 size.2.2 cover full unit

private theorem quotient {n e : ℕ} {z : ZMod n} (v : ZMod n) (power : z^e=v)
    (unit : Nat.Coprime (v-1).val n) : Nat.Coprime ((z^e-1).val) n := power ▸ unit

def M : ℕ := 2^1024-1

private theorem prime_3 : Nat.Prime 3 := by norm_num

private theorem prime_5 : Nat.Prime 5 := by norm_num

private theorem prime_17 : Nat.Prime 17 := by norm_num

private theorem prime_257 : Nat.Prime 257 := by norm_num

private theorem prime_2 : Nat.Prime 2 := by norm_num

private theorem prime_65537 : Nat.Prime 65537 := by
  refine certify (F:=65536) (3 : ZMod 65537)
    (Covers.cons 16 prime_2 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=32768) 65536 (by reduce_mod_char) (by decide +kernel)

private theorem prime_641 : Nat.Prime 641 := by norm_num

private theorem prime_727 : Nat.Prime 727 := by norm_num

private theorem prime_17449 : Nat.Prime 17449 := by
  refine certify (F:=727) (8727 : ZMod 17449)
    (Covers.cons 1 prime_727 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 8727 (by reduce_mod_char) (by decide +kernel)

private theorem prime_6700417 : Nat.Prime 6700417 := by
  refine certify (F:=17449) (5846540 : ZMod 6700417)
    (Covers.cons 1 prime_17449 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 5846540 (by reduce_mod_char) (by decide +kernel)

private theorem prime_274177 : Nat.Prime 274177 := by
  refine certify (F:=4352) (192008 : ZMod 274177)
    (Covers.cons 8 prime_2 (Covers.cons 1 prime_17 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=2176) 274176 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=256) 216812 (by reduce_mod_char) (by decide +kernel)

private theorem prime_373 : Nat.Prime 373 := by norm_num

private theorem prime_347 : Nat.Prime 347 := by norm_num

private theorem prime_16657 : Nat.Prime 16657 := by
  refine certify (F:=347) (6944 : ZMod 16657)
    (Covers.cons 1 prime_347 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 6944 (by reduce_mod_char) (by decide +kernel)

private theorem prime_166571 : Nat.Prime 166571 := by
  refine certify (F:=16657) (1024 : ZMod 166571)
    (Covers.cons 1 prime_16657 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 1024 (by reduce_mod_char) (by decide +kernel)

private theorem prime_2998279 : Nat.Prime 2998279 := by
  refine certify (F:=166571) (262144 : ZMod 2998279)
    (Covers.cons 1 prime_166571 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 262144 (by reduce_mod_char) (by decide +kernel)

private theorem prime_67280421310721 : Nat.Prime 67280421310721 := by
  refine certify (F:=1118358067) (61081809823082 : ZMod 67280421310721)
    (Covers.cons 1 prime_2998279 (Covers.cons 1 prime_373 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=373) 61150258807256 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=2998279) 65541179653181 (by reduce_mod_char) (by decide +kernel)

private theorem prime_823 : Nat.Prime 823 := by norm_num

private theorem prime_52673 : Nat.Prime 52673 := by
  refine certify (F:=823) (36491 : ZMod 52673)
    (Covers.cons 1 prime_823 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 36491 (by reduce_mod_char) (by decide +kernel)

private theorem prime_1896229 : Nat.Prime 1896229 := by
  refine certify (F:=52673) (137776 : ZMod 1896229)
    (Covers.cons 1 prime_52673 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 137776 (by reduce_mod_char) (by decide +kernel)

private theorem prime_18533742247 : Nat.Prime 18533742247 := by
  refine certify (F:=1896229) (3936126951 : ZMod 18533742247)
    (Covers.cons 1 prime_1896229 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 3936126951 (by reduce_mod_char) (by decide +kernel)

private theorem prime_116503103764643 : Nat.Prime 116503103764643 := by
  refine certify (F:=18533742247) (65489195555553 : ZMod 116503103764643)
    (Covers.cons 1 prime_18533742247 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 65489195555553 (by reduce_mod_char) (by decide +kernel)

private theorem prime_59649589127497217 : Nat.Prime 59649589127497217 := by
  refine certify (F:=116503103764643) (20416608684428934 : ZMod 59649589127497217)
    (Covers.cons 1 prime_116503103764643 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 20416608684428934 (by reduce_mod_char) (by decide +kernel)

private theorem prime_139 : Nat.Prime 139 := by norm_num

private theorem prime_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_6939437 : Nat.Prime 6939437 := by
  refine certify (F:=247837) (4736850 : ZMod 6939437)
    (Covers.cons 1 prime_1783 (Covers.cons 1 prime_139 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=139) 1814079 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=1783) 4771566 (by reduce_mod_char) (by decide +kernel)

private theorem prime_55515497 : Nat.Prime 55515497 := by
  refine certify (F:=6939437) (256 : ZMod 55515497)
    (Covers.cons 1 prime_6939437 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 256 (by reduce_mod_char) (by decide +kernel)

private theorem prime_733803839347 : Nat.Prime 733803839347 := by
  refine certify (F:=55515497) (232562832822 : ZMod 733803839347)
    (Covers.cons 1 prime_55515497 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 232562832822 (by reduce_mod_char) (by decide +kernel)

private theorem prime_5704689200685129054721 : Nat.Prime 5704689200685129054721 := by
  refine certify (F:=733803839347) (2500924644267550558592 : ZMod 5704689200685129054721)
    (Covers.cons 1 prime_733803839347 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 2500924644267550558592 (by reduce_mod_char) (by decide +kernel)

private theorem prime_719 : Nat.Prime 719 := by norm_num

private theorem prime_2791 : Nat.Prime 2791 := by norm_num

private theorem prime_16747 : Nat.Prime 16747 := by
  refine certify (F:=2791) (64 : ZMod 16747)
    (Covers.cons 1 prime_2791 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 64 (by reduce_mod_char) (by decide +kernel)

private theorem prime_3853149761 : Nat.Prime 3853149761 := by
  refine certify (F:=12041093) (2917551232 : ZMod 3853149761)
    (Covers.cons 1 prime_16747 (Covers.cons 1 prime_719 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=719) 2744262437 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=16747) 1872278538 (by reduce_mod_char) (by decide +kernel)

private theorem prime_1238926361552897 : Nat.Prime 1238926361552897 := by
  refine certify (F:=3853149761) (437771075092802 : ZMod 1238926361552897)
    (Covers.cons 1 prime_3853149761 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 437771075092802 (by reduce_mod_char) (by decide +kernel)

private theorem prime_199 : Nat.Prime 199 := by norm_num

private theorem prime_100297 : Nat.Prime 100297 := by
  refine certify (F:=1791) (88141 : ZMod 100297)
    (Covers.cons 1 prime_199 (Covers.cons 2 prime_3 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=9) 23578 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=597) 62984 (by reduce_mod_char) (by decide +kernel)

private theorem prime_1604753 : Nat.Prime 1604753 := by
  refine certify (F:=100297) (65536 : ZMod 1604753)
    (Covers.cons 1 prime_100297 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 65536 (by reduce_mod_char) (by decide +kernel)

private theorem prime_41723579 : Nat.Prime 41723579 := by
  refine certify (F:=1604753) (25385285 : ZMod 41723579)
    (Covers.cons 1 prime_1604753 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 25385285 (by reduce_mod_char) (by decide +kernel)

private theorem prime_83447159 : Nat.Prime 83447159 := by
  refine certify (F:=41723579) (4 : ZMod 83447159)
    (Covers.cons 1 prime_41723579 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 4 (by reduce_mod_char) (by decide +kernel)

private theorem prime_25353082741699 : Nat.Prime 25353082741699 := by
  refine certify (F:=83447159) (18800649653813 : ZMod 25353082741699)
    (Covers.cons 1 prime_83447159 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 18800649653813 (by reduce_mod_char) (by decide +kernel)

private theorem prime_283 : Nat.Prime 283 := by norm_num

private theorem prime_29 : Nat.Prime 29 := by norm_num

private theorem prime_10948139 : Nat.Prime 10948139 := by
  refine certify (F:=238003) (7732585 : ZMod 10948139)
    (Covers.cons 2 prime_29 (Covers.cons 1 prime_283 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=8207) 7332951 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=841) 1301661 (by reduce_mod_char) (by decide +kernel)

private theorem prime_6130957841 : Nat.Prime 6130957841 := by
  refine certify (F:=10948139) (343502090 : ZMod 6130957841)
    (Covers.cons 1 prime_10948139 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 343502090 (by reduce_mod_char) (by decide +kernel)

private theorem prime_220714482277 : Nat.Prime 220714482277 := by
  refine certify (F:=6130957841) (68719476736 : ZMod 220714482277)
    (Covers.cons 1 prime_6130957841 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 68719476736 (by reduce_mod_char) (by decide +kernel)

private theorem prime_9243081088796207 : Nat.Prime 9243081088796207 := by
  refine certify (F:=220714482277) (2272902133103912 : ZMod 9243081088796207)
    (Covers.cons 1 prime_220714482277 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 2272902133103912 (by reduce_mod_char) (by decide +kernel)

private theorem prime_1057372046781162536274034354686893329625329 : Nat.Prime 1057372046781162536274034354686893329625329 := by
  refine certify (F:=234340599632483517839031935693) (385966367165596330213889389661767251544343 : ZMod 1057372046781162536274034354686893329625329)
    (Covers.cons 1 prime_9243081088796207 (Covers.cons 1 prime_25353082741699 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=25353082741699) 573712587599096543013594005640127396496092 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=9243081088796207) 301242753211723968424895194594146065584167 (by reduce_mod_char) (by decide +kernel)

private theorem prime_93461639715357977769163558199606896584051237541638188580280321 : Nat.Prime 93461639715357977769163558199606896584051237541638188580280321 := by
  refine certify (F:=1057372046781162536274034354686893329625329) (73220400250843860425616746354045941528994042253571182689917396 : ZMod 93461639715357977769163558199606896584051237541638188580280321)
    (Covers.cons 1 prime_1057372046781162536274034354686893329625329 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 73220400250843860425616746354045941528994042253571182689917396 (by reduce_mod_char) (by decide +kernel)

private theorem prime_2424833 : Nat.Prime 2424833 := by
  refine certify (F:=65536) (1305063 : ZMod 2424833)
    (Covers.cons 16 prime_2 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=32768) 2424832 (by reduce_mod_char) (by decide +kernel)

private theorem prime_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_11443 : Nat.Prime 11443 := by
  refine certify (F:=1907) (64 : ZMod 11443)
    (Covers.cons 1 prime_1907 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 64 (by reduce_mod_char) (by decide +kernel)

private theorem prime_68659 : Nat.Prime 68659 := by
  refine certify (F:=11443) (64 : ZMod 68659)
    (Covers.cons 1 prime_11443 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 64 (by reduce_mod_char) (by decide +kernel)

private theorem prime_45177623 : Nat.Prime 45177623 := by
  refine certify (F:=68659) (15881135 : ZMod 45177623)
    (Covers.cons 1 prime_68659 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 15881135 (by reduce_mod_char) (by decide +kernel)

private theorem prime_1084262953 : Nat.Prime 1084262953 := by
  refine certify (F:=45177623) (16777216 : ZMod 1084262953)
    (Covers.cons 1 prime_45177623 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 16777216 (by reduce_mod_char) (by decide +kernel)

private theorem prime_1143290228161321 : Nat.Prime 1143290228161321 := by
  refine certify (F:=1084262953) (45495412912970 : ZMod 1143290228161321)
    (Covers.cons 1 prime_1084262953 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 45495412912970 (by reduce_mod_char) (by decide +kernel)

private theorem prime_269 : Nat.Prime 269 := by norm_num

private theorem prime_11299 : Nat.Prime 11299 := by
  refine certify (F:=269) (606 : ZMod 11299)
    (Covers.cons 1 prime_269 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 606 (by reduce_mod_char) (by decide +kernel)

private theorem prime_3943 : Nat.Prime 3943 := by norm_num

private theorem prime_212923 : Nat.Prime 212923 := by
  refine certify (F:=3943) (73513 : ZMod 212923)
    (Covers.cons 1 prime_3943 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 73513 (by reduce_mod_char) (by decide +kernel)

private theorem prime_72174509311 : Nat.Prime 72174509311 := by
  refine certify (F:=2405816977) (1073741824 : ZMod 72174509311)
    (Covers.cons 1 prime_212923 (Covers.cons 1 prime_11299 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=11299) 19101642900 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=212923) 62649006666 (by reduce_mod_char) (by decide +kernel)

private theorem prime_514601075709020317 : Nat.Prime 514601075709020317 := by
  refine certify (F:=72174509311) (203824399746341302 : ZMod 514601075709020317)
    (Covers.cons 1 prime_72174509311 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 203824399746341302 (by reduce_mod_char) (by decide +kernel)

private theorem prime_43226490359557706629 : Nat.Prime 43226490359557706629 := by
  refine certify (F:=514601075709020317) (39340190982021487041 : ZMod 43226490359557706629)
    (Covers.cons 1 prime_514601075709020317 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 39340190982021487041 (by reduce_mod_char) (by decide +kernel)

private theorem prime_7455602825647884208337395736200454918783366342657 : Nat.Prime 7455602825647884208337395736200454918783366342657 := by
  refine certify (F:=49420424025791873042320730203096909) (6331598026120786648784919510222086574536103153039 : ZMod 7455602825647884208337395736200454918783366342657)
    (Covers.cons 1 prime_43226490359557706629 (Covers.cons 1 prime_1143290228161321 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=1143290228161321) 7144772527399820084901356947992160934279684350065 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=43226490359557706629) 6546000188509825874669636031994195250534297142415 (by reduce_mod_char) (by decide +kernel)

private theorem prime_101 : Nat.Prime 101 := by norm_num

private theorem prime_433 : Nat.Prime 433 := by norm_num

private theorem prime_9446329 : Nat.Prime 9446329 := by
  refine certify (F:=43733) (7936823 : ZMod 9446329)
    (Covers.cons 1 prime_433 (Covers.cons 1 prime_101 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=101) 7111433 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=433) 5072492 (by reduce_mod_char) (by decide +kernel)

private theorem prime_37785317 : Nat.Prime 37785317 := by
  refine certify (F:=9446329) (16 : ZMod 37785317)
    (Covers.cons 1 prime_9446329 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 16 (by reduce_mod_char) (by decide +kernel)

private theorem prime_7871739519977 : Nat.Prime 7871739519977 := by
  refine certify (F:=37785317) (1633761705180 : ZMod 7871739519977)
    (Covers.cons 1 prime_37785317 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 1633761705180 (by reduce_mod_char) (by decide +kernel)

private theorem prime_1392542208042011209 : Nat.Prime 1392542208042011209 := by
  refine certify (F:=7871739519977) (951655564034972117 : ZMod 1392542208042011209)
    (Covers.cons 1 prime_7871739519977 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 951655564034972117 (by reduce_mod_char) (by decide +kernel)

private theorem prime_487 : Nat.Prime 487 := by norm_num

private theorem prime_15661 : Nat.Prime 15661 := by
  refine certify (F:=783) (14950 : ZMod 15661)
    (Covers.cons 1 prime_29 (Covers.cons 3 prime_3 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=27) 11486 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=261) 6823 (by reduce_mod_char) (by decide +kernel)

private theorem prime_41856465617 : Nat.Prime 41856465617 := by
  refine certify (F:=7626907) (37479346036 : ZMod 41856465617)
    (Covers.cons 1 prime_15661 (Covers.cons 1 prime_487 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=487) 38288135669 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=15661) 400776787 (by reduce_mod_char) (by decide +kernel)

private theorem prime_47967509597083 : Nat.Prime 47967509597083 := by
  refine certify (F:=41856465617) (37923999670096 : ZMod 47967509597083)
    (Covers.cons 1 prime_41856465617 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 37923999670096 (by reduce_mod_char) (by decide +kernel)

private theorem prime_53531740710344629 : Nat.Prime 53531740710344629 := by
  refine certify (F:=47967509597083) (14063722605752058 : ZMod 53531740710344629)
    (Covers.cons 1 prime_47967509597083 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 14063722605752058 (by reduce_mod_char) (by decide +kernel)

private theorem prime_3088888502468305782559 : Nat.Prime 3088888502468305782559 := by
  refine certify (F:=53531740710344629) (1478901973627932007425 : ZMod 3088888502468305782559)
    (Covers.cons 1 prime_53531740710344629 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 1478901973627932007425 (by reduce_mod_char) (by decide +kernel)

private theorem prime_16975143302271505426897585653131126520182328037821729720833840187223 : Nat.Prime 16975143302271505426897585653131126520182328037821729720833840187223 := by
  refine certify (F:=4301407615622795924918770760378994703831) (11268000143499845792905808461318926786894485104105430979787576898578 : ZMod 16975143302271505426897585653131126520182328037821729720833840187223)
    (Covers.cons 1 prime_3088888502468305782559 (Covers.cons 1 prime_1392542208042011209 covers_one)) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,?_,List.forall_mem_nil _⟩
  · exact quotient (e:=1392542208042011209) 3276498169597161570801715356627499667546764450842991441239538379501 (by reduce_mod_char) (by decide +kernel)
  · exact quotient (e:=3088888502468305782559) 1519672782548057419281459549502878061355479361352684061692807406114 (by reduce_mod_char) (by decide +kernel)

private theorem prime_741640062627530801524787141901937474059940781097519023905821316144415759504705008092818711693940737 : Nat.Prime 741640062627530801524787141901937474059940781097519023905821316144415759504705008092818711693940737 := by
  refine certify (F:=16975143302271505426897585653131126520182328037821729720833840187223) (264059416234626707409047724092590155375992082268564158330468466363582375279315660706394127416487670 : ZMod 741640062627530801524787141901937474059940781097519023905821316144415759504705008092818711693940737)
    (Covers.cons 1 prime_16975143302271505426897585653131126520182328037821729720833840187223 covers_one) (by decide +kernel) (by reduce_mod_char) ?_
  simp only [List.forall_mem_cons]
  refine ⟨?_,List.forall_mem_nil _⟩
  exact quotient (e:=1) 264059416234626707409047724092590155375992082268564158330468466363582375279315660706394127416487670 (by reduce_mod_char) (by decide +kernel)

/-- The first five entries are F₀ through F₄. Each subsequent line gives the
factors of one of F₅ through F₉ in order. -/
def factors : List ℕ := [
  3, 5, 17, 257, 65537,
  641, 6700417,
  274177, 67280421310721,
  59649589127497217, 5704689200685129054721,
  1238926361552897, 93461639715357977769163558199606896584051237541638188580280321,
  2424833, 7455602825647884208337395736200454918783366342657, 741640062627530801524787141901937474059940781097519023905821316144415759504705008092818711693940737]

theorem exactFactors : ExactFactorization M factors := by
  refine ⟨by decide +kernel,?_⟩
  intro p hp
  simp only [factors,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_3
  · exact prime_5
  · exact prime_17
  · exact prime_257
  · exact prime_65537
  · exact prime_641
  · exact prime_6700417
  · exact prime_274177
  · exact prime_67280421310721
  · exact prime_59649589127497217
  · exact prime_5704689200685129054721
  · exact prime_1238926361552897
  · exact prime_93461639715357977769163558199606896584051237541638188580280321
  · exact prime_2424833
  · exact prime_7455602825647884208337395736200454918783366342657
  · exact prime_741640062627530801524787141901937474059940781097519023905821316144415759504705008092818711693940737

theorem distinct : factors.Nodup := by decide +kernel

theorem size : factors.length=16 := rfl

private theorem nonzero : M≠0 := by decide +kernel

attribute [local irreducible] M factors

theorem squarefree : Squarefree M :=
  (Nat.squarefree_iff_nodup_primeFactorsList nonzero).mpr
    (exactFactors.perm_primeFactorsList.nodup_iff.mp distinct)

theorem primeFactors : M.primeFactors=factors.toFinset := by
  ext p
  change p∈M.primeFactorsList.toFinset ↔ p∈factors.toFinset
  simpa only [List.mem_toFinset] using (exactFactors.perm_primeFactorsList.mem_iff (a:=p)).symm

theorem card : M.primeFactors.card=16 := by
  rw [primeFactors,List.toFinset_card_of_nodup distinct,size]

theorem prime_divisors (p : ℕ) : p.Prime ∧ p∣M ↔ p∈factors := by
  constructor
  · intro h
    have hit : p∈M.primeFactors := Nat.mem_primeFactors.mpr ⟨h.1,h.2,nonzero⟩
    rw [primeFactors] at hit
    exact List.mem_toFinset.mp hit
  · intro h
    have hit : p∈M.primeFactors := primeFactors.symm ▸ List.mem_toFinset.mpr h
    exact ⟨(Nat.mem_primeFactors.mp hit).1,(Nat.mem_primeFactors.mp hit).2.1⟩

/-- Every listed prime occurs once. All other numbers have multiplicity zero. -/
theorem exponents (p : ℕ) : M.factorization p=if p∈factors then 1 else 0 := by
  rw [←Nat.primeFactorsList_count_eq,←exactFactors.perm_primeFactorsList.count_eq p]
  split_ifs with member
  · exact List.count_eq_one_of_mem distinct member
  · exact List.count_eq_zero_of_not_mem member

/-- Every divisor is exactly a product of a subset of the sixteen listed primes. -/
theorem divisors (d : ℕ) : d∣M ↔ ∃ s⊆factors.toFinset, s.prod id=d := by
  constructor
  · intro dvd
    refine ⟨d.primeFactors,?_,Nat.prod_primeFactors_of_squarefree (squarefree.squarefree_of_dvd dvd)⟩
    rw [←primeFactors]
    intro p hp
    obtain ⟨prime,h,_⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨prime,h.trans dvd,nonzero⟩
  · rintro ⟨s,sub,rfl⟩
    rw [←primeFactors] at sub
    simpa only [id_eq,Nat.prod_primeFactors_of_squarefree squarefree] using
      Finset.prod_dvd_prod_of_subset s M.primeFactors id sub

theorem divisor_count : M.divisors.card=65536 := calc
  _ = M.primeFactors.prod (M.factorization · + 1) := Nat.card_divisors nonzero
  _ = M.primeFactors.prod (fun _ => 2) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [primeFactors] at hp
    rw [exponents,if_pos (List.mem_toFinset.mp hp)]
  _ = _ := by rw [Finset.prod_const,card]; decide

end PrimeFactors.BinaryRotationModulus
