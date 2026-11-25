# Using the small primes that cannot divide a factor

For any product of two 1,024-bit primes, guess the last **614 binary digits** of one factor. The product and that guess determine a single list of at most **four signed integers** to check. If the guess matches either the factor or its negative, the matching integer is in the list. The preceding bound needed 615 digits. This doubles the number of former remainder classes one equation can check. We still have no practical way to choose the right guess for an arbitrary pair. [Factor recovery theorem](../PrimeFactors/UnitQuarticRecovery.lean) · [Earlier factorial guarantee](difference-lanes.md)

## Which values must the polynomial cover?

Write $N=xy$, choose a radix $R$ coprime to $N$, and suppose $x\equiv u\bmod R$. We can discard $u$ unless it is a unit modulo $R$. The eliminant $F$ has degree at most $d=2t$ and satisfies $F(x)=x^t P(x,y)$, where $P$ is the trace. For every prime $\ell\nmid N$, both factors are units modulo $\ell$. When $\ell\nmid R$, this excludes one residue of $k$ in $x=u+Rk$. When $\ell\mid R$, the whole remainder class already consists of units.

Let $e_\ell=v_\ell(R)$. At a prime dividing $R$, take the usual local nodes $x_i=u+Ri$. The least valuation of the product of $j$ differences from the first $j$ nodes, over the entire class, is $\alpha_{\ell,j}=e_\ell j+v_\ell(j!)$. At a prime dividing neither $R$ nor $N$, take the increasing positive units

$$a_i=1+i+\lfloor i/(\ell-1)\rfloor,\qquad
  \alpha_{\ell,j}=w_\ell(j)=\sum_{a\ge1}
  \left\lfloor\frac{j}{(\ell-1)\ell^{a-1}}\right\rfloor.$$

At modulus $\ell^a$, the units in this sequence form a repeating cycle of length $\varphi(\ell^a)$. Every allowed class appears at least $\lfloor j/\varphi(\ell^a)\rfloor$ times among the first $j$ nodes. The class of the next node attains that minimum at **each** precision. Summing the counts proves the displayed valuation. This is an explicit local ordering in Bhargava’s theory of integer-valued polynomials. [Bhargava, *P-orderings and polynomial functions*](https://doi.org/10.1515/crll.1997.490.101)

Choose $L_\ell=\alpha_{\ell,d}$ and $M=\prod_\ell\ell^{L_\ell}$, using the primes dividing $R$ and the primes $\ell\le d+1$ with $\ell\nmid NR$. Larger primes off the stride have $w_\ell(j)=0$ throughout this degree. For every $i$ construct one integer $x_i=u+Rk_i$ by CRT. At primes dividing $R$, impose $k_i\equiv i\bmod{\ell^{L_\ell}}$. At other primes in $M$, impose $u+Rk_i\equiv a_i\bmod{\ell^{L_\ell}}$. All these moduli are pairwise coprime across primes. The resulting Newton polynomials $E_j(X)=\prod_{i<j}(X-x_i)$ form a monic triangular basis over the integers.

Writing $F=\sum b_j E_j$, coverage of every $x=u+Rk$ coprime to $M$ is equivalent to the independent congruences

$$\prod_{\ell\mid M}\ell^{L_\ell-\alpha_{\ell,j}}\mid b_j,\qquad 0\le j\le d.$$

For sufficiency, each term has the required divisibility locally. For necessity, evaluate in order at $x_0,\ldots,x_d$. At $x_j$ the later terms vanish, and each earlier term is already divisible everywhere on the allowed set. The diagonal has valuation $\alpha_{\ell,j}$ truncated at $L_\ell$. Thus these $d+1$ evaluations also verify any computed relation on that set. Lean proves this grid test for general nodes given the diagonal gcd minima. The cycle count and CRT construction supply those hypotheses on paper. An implementation can construct its lattice row by row from the CRT nodes, using the usual unit triangular Newton transform. The existing monomial factors involving $N$ are units modulo $M$. Cancelling $x^t$ therefore still gives $P(x,y)=0$ when $|P|<M$. [General factor extraction](../PrimeFactors/PowerFactorLanes.lean) · [Finite grid implication](../PrimeFactors/UnitNewtonLanes.lean)

For a small check, take $M=45$. The first four simultaneous unit nodes at 3 and 5 may be taken as $1,2,13,14$. Their product of differences at $x$,
$F(x)=(x-1)(x-2)(x-13)(x-14)$, vanishes modulo 45 at every class coprime to 15. At $x=3$ it gives 220, and at the next node $x=16$ it gives $45\cdot28$. Lean checks every residue in this example. [Checked modulus example](../PrimeFactors/UnitNewtonLanes.lean)

## Why 614 bits suffice in degree four

Take $R=2^{614}$, $M=360R^4$, $B=\lfloor\sqrt{2N}\rfloor$, $s=\lfloor\sqrt{N/8}\rfloor$, and put $D=x-y$. For odd balanced factors the five quantities $1,D,x,D^2-2s^2,xD$ have absolute values bounded by the widths $W=(1,2s,B,2s^2,2Bs)$. For each coefficient vector, encode the four Newton residues separately at each of the three primes. Their moduli are $(8R^4,8R^3,4R^2,4R)$ at 2, $(9,9,3,3)$ at 3, and $(5,5,5,5)$ at 5. Together there are $466560000R^{10}$ possible labels. Equal labels imply that the corresponding quartics agree modulo $M$ at every $x$ in the lane coprime to 30. [Local congruences and label count](../PrimeFactors/QuarticUnitLabels.lean)

In coordinate $i$ use the integers from zero through $\lfloor(M-1)/(5W_i)\rfloor$. The number of choices is at least $M/(5W_i)$. When $5^5\prod_iW_i<M^5/(466560000R^{10})$, two different box points must have the same label. Their difference has weighted absolute sum at most $M-1$. Here the right side of the comparison equals $12960R^{10}$, and

$$\prod_iW_i=8B^2s^4\le2^{6142}=4R^{10}.$$

The remaining strict inequality is **$3125<3240$**. Consequently the trace difference is both divisible by $M$ and strictly smaller than $M$ in absolute value, so it vanishes. The transformation of the five coefficients preserves nonzero differences, yielding a nonzero polynomial of degree at most four. Its integer roots supply the single list for both signs. Lean proves existence of the nonzero coefficient vector, its strict weighted bound, the congruence on the entire allowed lane and coverage of the factors by those roots. This existence argument uses a finite box collision. The implementation seeks a short relation with lattice reduction and checks that relation directly. The theorem covers $8\le N<2^{2048}$ with $\gcd(N,30)=1$ and all factor pairs whose ratio is between $1/2$ and 2. A shared prime with 30 is detectable directly from the product. [Finite box proof](../PrimeFactors/UnitQuarticBox.lean) · [Factor recovery and both signs](../PrimeFactors/UnitQuarticRecovery.lean)

## Checking a single full-size remainder

We ran one signed quartic at $u=1$, $R=2^{614}$ on each of the two existing 2,048-bit comparison inputs. The crossed control yielded its two primes in 2.25 seconds, with one lattice reduction, 1,679 swaps, 2,709 size reductions and 3,260 root-search nodes. Lean separately checked the prime certificate in 6.50 seconds. The fresh comparison yielded no candidate in 2.39 seconds, with one reduction, 1,870 swaps, 2,964 size reductions and 806 root-search nodes. Its full product remained unresolved. Each equation passed five dyadic grid tests, six unit evaluations modulo 9 and four modulo 5. Each run visited one of $2^{611}+1$ signed groups. The remainder was originally chosen after inspecting the crossed factors and frozen before drawing the fresh product. At four smaller products the implementation also matched direct enumeration on every odd remainder. [Probe and parameters](../experiments/unit_quartic_probe.py) · [Full-size receipts](../research/unit-quartic-probe.json) · [Small comparisons](../tests/test_unit_quartic_probe.py)

## How much the determinant changes

Put $m=d+1$, $J_d=\prod_{j=0}^d j!$. Assume $N$ has no prime divisor through $d+1$, as is automatic on a product of two 1,024-bit primes at the degrees below. The previous margin $M^m/[\mathbb Z^m:\Lambda]$ was $R^{tm}J_d$. The new maximal margin equals $R^{tm}J_d G$, where

$$ G=\prod_{\substack{\ell\le d+1\\\ell\ \mathrm{prime},\,\ell\nmid R}}
  \ell^{E_\ell},\qquad
 E_\ell=\sum_{j=0}^d\big(w_\ell(j)-v_\ell(j!)\big). $$

This compares the margins obtained after allowing each construction its own sufficient modulus. At a *fixed* modulus the correct exponents are truncated at its local precisions. If a small prime divides $N$, take the gcd or omit that prime from the modulus and factorial contributions. At a fixed degree and fixed support of $R$ the continuous radix threshold improves by $\log_2(G)/(tm)$ bits.

Each table entry is the least integer $e$ certified by the corresponding determinant inequality when $R=2^e$. The degrees 6 and 8 each save one dyadic radix bit with the ordinary weights. The unit condition and Dickson weights together give a further bit at degrees 4, 6, 16, 1,024 and 4,096 relative to Dickson weights alone. None of these full-size table lengths has been traversed.

| Maximum degree | 2 | 4 | 6 | 8 | 16 | 64 | 1,024 | 4,096 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Ordinary weights, full factorial | 684 | 615 | 586 | 569 | 541 | 517 | 506 | 504 |
| Ordinary weights, unit condition | 684 | 615 | 585 | 568 | 541 | 517 | 505 | 503 |
| Dickson weights, full factorial | 684 | 615 | 585 | 568 | 541 | 516 | 505 | 503 |
| Dickson weights, unit condition | 684 | **614** | **584** | 568 | **540** | 516 | **504** | **502** |
| Continuous gain from units, in radix bits | 0.5283 | 0.5492 | 0.6216 | 0.6472 | 0.6371 | 0.7377 | 0.7671 | 0.7693 |

For degree four the extra factor is $3^2\cdot5=45$. Degree six gives $3^5\cdot5\cdot7=8505$, and degree eight gives $3^{10}\cdot5^2\cdot7=10333575$. Lean verifies those integers and both neighboring exponent comparisons for the quartic Dickson result. For the other entries, compare $2^{2etm}(J_dG)^2$ strictly against $m^m2^{tm+W}$, once at $e$ and once at $e-1$. Here $W=2049t(t+1)$ for ordinary weights, and $W=4t-2+2049t+2045t^2$ for Dickson weights. The arithmetic check used integer lower and upper bounds for each base-two logarithm. For any positive integer $v$, the bit length of $v^{256}$ minus one bounds $256\log_2 v$ from below, with less than one unit of error. To accumulate a local exponent, use $\sum_{j=0}^d\lfloor j/h\rfloor=hq(q-1)/2+(r+1)q$ with $d=hq+r$. [Dickson norm bound](../PrimeFactors/GapPolynomialScale.lean) · [Lean finite checks](../PrimeFactors/UnitNewtonLanes.lean)

## Putting a prime in the stride

There is a tradeoff when comparing radices with different sets of prime divisors. Leaving $\ell$ out of $R$ improves the continuous radix threshold by the factor $\ell^{E_\ell/(tm)}$. Including $\ell$ multiplies the fraction of residues that are units by $1-1/\ell$. At every degree,

$$\ell^{E_\ell/(tm)}\le\frac{\ell}{\ell-1}.$$

To see this, shift the increasing unit sequence by $s$ positions for each $s=0,\ldots,\ell-2$. Form the product of all pair distances among $a_s,\ldots,a_{s+d}$ and divide by $J_d$. Each quotient is a positive integer. It is the determinant of the matrix with entries $\binom{a_{s+i}}j$, by the leading coefficients of the binomial polynomials and the Vandermonde formula. Its $\ell$-adic valuation is $E_\ell$, because every shift still cycles through the unit residues at each precision. For any pair $i<j$ the mean distance over the shifts is $(j-i)\ell/(\ell-1)$. The geometric mean is at most this arithmetic mean. Multiplying over all $tm$ pairs proves the inequality. For odd $\ell$ some adjacent distances are 1 and some are 2, making the inequality strict. For $\ell=2$ every distance doubles and equality holds.

Thus, in the **continuous count of oriented unit remainders**, dropping a stride prime solely for this extra polynomial divisibility cannot pay back the lost totient density. Integer rounding, other prime divisors of an actual radix, sign and swap orbits, and the running cost of a lattice reduction also affect a concrete comparison. The repository's standard large smooth quartic radices already contain every prime through 5. In that setting the extra determinant factor is exactly one. [Smooth radix construction](../experiments/midpoint_weights.py)
