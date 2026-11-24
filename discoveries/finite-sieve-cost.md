# How much does the wide sieve remove at 2048 bits?

The wide-modulus parameter rule chooses $m=293\#$ for every 2048-bit input. It has 62 prime factors, of which the 55 from 19 through 293 form the selected set $S$. With the allowance of 33 failed local tests obtained from the original content cutoff, the sieve discards only **0.000000883812%** of a full period. A different rule, sending rows with over 15 degenerate primes to the dense search, certifies a smaller ordinary table that retains **71.0624%**. Even a dense search with chunked rows still has a record budget of order $2^{413}$ at this parameter choice. These are counts and upper bounds. No 2048-bit factorization or wall-time measurement was performed. [Parameter theorem](../PrimeFactors/WideScale.lean) · [Wide-modulus search](wide-modulus-sieve.md) · [Integer calculation](../experiments/sieve_forecast.py)

## A floor on the work even if the modulus is retuned

For the explicit one-interval implementation, **every choice of sieve modulus and selected odd primes** on a 2048-bit product either scans at least $2^{400}$ residue positions or constructs more than $2^{400}$ baby entries once it reaches the main sieve. The powered-order setup can sometimes split a product before that point. The bound concerns the current enumeration, including its public trace width and shared table. Implicit representations or other factor searches can have different costs. [Lean finite bounds including the rounded trace width](../PrimeFactors/SieveBudget.lean)

If $m\ge 2^{400}$ the outer residue scan already incurs this cost. Otherwise $m$ contains at most 61 distinct odd primes, because the product of the first 62 exceeds $2^{400}$. At a selected prime $\ell$ even the ordinary two-sign union has density at least $(3\ell-1)/(4\ell)$. Allowing failures enlarges it. These lower bounds increase with $\ell$ and are at most one. The smallest product over at most 61 primes is attained at the first 61 odd primes. Its exact rational value exceeds $2^{-27}$.

Write $W=2R+1$ with the code's actual integer radius. Squaring its defining bound gives $W^2m^3\ge144N$, with the floor and ceiling conventions included. If $W\le 2^{427}$ and $m<2^{400}$, this would give $144\cdot2^{2047}\le2^{2054}$, which is false. The padded exponent interval has $W+M-1$ entries before sieving, containing $\lceil W/M\rceil$ full periods. It therefore emits at least $W$ times the full-period density, which exceeds $2^{400}$. This lower bound still holds if a large-order base and all the CRT membership information are supplied without charge.

The exact asymptotic parameter rule also fixes the modulus at this bit width. Lean proves directly from $2^{2047}\le N<2^{2048}$ that the eligible largest primorial is $293\#$ and its number of unit rows exceeds $2^{396}$. This separates the actual 2048-bit expense from the asymptotic coefficient improvement. [Exact cutoff and unit count](../PrimeFactors/WideScale.lean)

## The full period, exactly

Put $M=\prod_{\ell\in S}\ell$. Completing the quadratic and translating its image leaves a forbidden set of $f_\ell=(\ell-\chi_\ell(-1))/4$ residues, where $\chi_\ell$ is the Legendre symbol. The CRT identifies the coefficient of $z^j$ in
$$
 F(z)=\prod_{\ell\in S}\bigl((\ell-f_\ell)+f_\ell z\bigr)
$$
with the exact number of residues failing exactly $j$ tests. Summing coefficients through $h$ gives the full-period survivor count $A_h$. The recurrence multiplies the current coefficient array by a linear factor at each prime. [Stănică, Propositions 3.5–3.6](https://arxiv.org/html/2611.06580v1#S3)

For $h=33$ the integers are

```text
M    = 4003407882323861397930281543736271681707686800792449199563889758271709282008384433743029435105269934681633521063171
A_33 = 4003407846941268763112933953438017777345300023425472133871979739197294277799402771116120174280940471303820659422499
```

Their difference divided by $M$ is $8.83811834188596\times10^{-9}$. The original cutoff $D_0=\exp(55\sqrt{\log\log N})$ has binary logarithm about $213.77$ throughout this input width. The products of the smallest 33 and 34 selected primes have binary logarithms $207.666$ and $215.150$, explaining the 33. Independently, the implementation’s coefficient height has logarithm $200.8314$ or less. It allows only 32 failed positions. The shortest-vector bound below reduces this to 31. The counts measure the CRT test at the stated allowance and do not estimate how many actual rows attain it.

For consistent finite upper bounds, use $s=2^{1024}$, $H=2\lfloor\sqrt m\rfloor+2$, $R=\lfloor3sH/m^2\rfloor+2$ and $W=2R+1$. The true unshifted index is one of $W$ consecutive integers. These outward roundings give $\log_2 m=399.662611$, $\log_2 M=380.701031$ and $\log_2 W=428.091046$, rounded here. The translated table has $W-1+M$ possible indices, so at most $A_h\lceil(W-1+M)/M\rceil$ ordinary baby entries. End effects prevent replacing that upper bound by the exact period density times the span. [Finite search conventions](../experiments/wide_modulus.py)

## A shorter public cutoff

Let $d=\gcd(a,b,m)$ for the chosen nonzero shortest vector. When $m>4$ its coordinates are nonzero, since a zero coordinate would force a nonzero multiple of $m$ in the other. Choose the sign so that $a>0$. With $H\le4\sqrt m$, each $d$ allows at most $2(H/d)^2$ ordered signed weight pairs after division by $d$. For $r=m/d$, each pair has at most $2^{\omega(r)}$ roots modulo $r$ and each root has at most $d$ lifts to modulus $m$. Consequently the number $G$ of rows with $d\ge D$ satisfies $G\le32m\,3^{\omega(m)}/D$. This deliberately simple bound makes the following choice sufficient:
$$
 D_{\rm crit}=\left\lceil128\,3^{\omega(m)}\max(1,W/m)\right\rceil .
$$
It gives $G\le m$ and $GW\le m^2$, enough to fit the exceptional branch in $O(m)$ records. In the asymptotic parameters $\omega(m)=O(t)$ and $\log(W/m)=O(t)$. Thus $\log D_{\rm crit}=O(t)$, still allowing only $o(t)$ failed selected primes because their minimum logarithm grows. At 2048 bits $\log_2D_{\rm crit}=133.696110$ to the stated precision. The ordinary allowance is 22 and retains $99.5268\%$.

## Count exceptional rows by their failed primes

Instead of a content cutoff, designate a row exceptional exactly when more than $h$ selected primes divide $d$. For this counting argument use the smaller height $A=\lfloor\sqrt{7m/6}\rfloor$. A Gauss-reduced basis with shortest vector $w$ has second vector at least as long as $w$ and an angle of at least $60$ degrees and at most $120$ degrees. Its determinant $m$ is at least $\sqrt3\,\|w\|^2/2$. Both coordinates of $w$ are therefore at most $A$ in absolute value. Keep the original conservative $H$ for the actual trace window above. [Harvey–Hittmeir, Lemma 3.1](https://arxiv.org/pdf/2105.11105#page=4)

Write $(u,v)=(a/d,b/d)$, $U=\lfloor A/d\rfloor$. There are $U$ positive possibilities for $u$ and $2U$ nonzero signed possibilities for $v$. For genuine rows both are units modulo $r$, and $v\sigma^2=uN\bmod r$. Define $g_2=1$ and $g_\ell=2$ at odd primes, extending multiplicatively to squarefree integers. There are at most $g(r)$ roots modulo $r$. Each root has exactly $\varphi(d)$ unit lifts since $d$ and $r$ are coprime. Thus a first row bound is
$$
 G_h\le2A^2\sum_{d\mid m,\,\omega_S(d)>h}g(m/d)\frac{\varphi(d)}{d^2},
 \qquad \omega_S(d)=|\{\ell\in S:\ell\mid d\}|.
$$
Obtain this sum as the coefficient tail above $h$ of the product of $g_\ell+(\ell-1)z/\ell^2$, using $z=1$ at unselected primes. This computation gives a rigorous upper bound even though it counts unattained vectors and content values. Its first successful allowance for $G_h\le m$ and $G_hW\le m^2$ is 18.

Averaging roots over a known divisor reduces that allowance to **15**. Fix $K\mid m$. For each $d$ take $k=\gcd(K,r)$. For each unit $\sigma\bmod k$ and each $u$, the congruence fixes $v\bmod k$. There are at most $2U/k+1$ choices for $v$ in $[-U,U]$. The remaining modulus $r/k$ costs at most $g(r/k)$ roots whenever the genuine unit conditions hold. After including the lifts, the contribution for $d$ is at most
$$
 \varphi(d)g(r/k)\varphi(k)\left(\frac{2A^2}{d^2k}+\frac{A}{d}\right).
$$
This remains an upper bound when $k>U$. The two terms again give Euler products with a factor $z$ precisely at each selected prime dividing $d$. The following table gives the constant and marked coefficients for each term before multiplication by $2A^2$ and $A$ respectively.

| Term | Prime in $K$, outside $d$ | Prime outside $K$ and $d$ | Prime in $d$ |
|---|---:|---:|---:|
| First | $(\ell-1)/\ell$ | $g_\ell$ | $(\ell-1)/\ell^2$ |
| Second | $\ell-1$ | $g_\ell$ | $(\ell-1)/\ell$ |

The program tests every initial primorial $K$, the first root bound and the unconditional cap $\varphi(m)$. The table reports the smallest of these bounds $\bar G$, rounded logarithms, and exact CRT fractions rounded to percentages. These are the best bounds among the listed choices of $K$. Global optimality over all divisors $K$ is open.

| Allowance $h$ | Ordinary fraction retained | $\log_2\bar G$ | $\bar GW\le m^2$ |
|---:|---:|---:|---|
| 0 | 0.0000130090% | 396.304 | No |
| 14 | 59.8849% | 375.271 | No |
| 15 | 71.0624% | 369.897 | Yes |
| 18 | 92.6013% | 352.757 | Yes |
| 22 | 99.5268% | 326.772 | Yes |

At $h=15$ the minimizing tested prefix is $K=83\#$ and $\log_2(m^2/W)=371.234176$. The ordinary table still has up to $2^{427.599}$ entries. A fixed public exceptional chunk width $B=\min(W,\lceil\sqrt{\bar GW}\rceil)$ gives an exceptional budget of $B+\bar G\lceil W/B\rceil$ records for $\bar G>0$. At $h=15$ this is below $2^{400}$. Scanning the ordinary rows costs up to $\varphi(m)$ additional giant records, plus the outer modulus scan. The row bound controls which allowances suffice for the asymptotic proof. It need not minimize finite work. For example, putting all $\varphi(m)$ rows in one dense chunked search gives a budget of $2^{413.1973}$ records to the displayed logarithmic precision. This is an upper bound for that competing schedule and excludes setup costs. Actual timings and the best implementation strategy at 2048 bits remain unknown.

The calculation uses just the primes through 293, integer coefficients of degree at most 55, and integer square roots. Four regression tests check small periods, every small-lattice row on two products, explicit divisor sums and the 2048-bit integer thresholds. [Forecast](../experiments/sieve_forecast.py) · [Tests](../tests/test_sieve_forecast.py)

```sh
python3 experiments/sieve_forecast.py --h 14 --h 15 --h 18 --h 22 --h 33
python3 -m unittest discover -s tests -p test_sieve_forecast.py
```
