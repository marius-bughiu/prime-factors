# Testing powers large enough for the product

One guess recovered 2,731 and 3,917 from their product 10,697,327. Trying every guess from the same rule on our two 2,048-bit inputs recovered neither pair. A stopping rule saved over 83% of the continued-fraction steps on both inputs. It still left about 15,800 steps on each. [Recorded products and counts](../research/scaled-power-menu.json)

## Where the guesses come from

Write the product as $N=pq$. Knowing $F=(p-1)(q-1)$ would give us the sum $p+q=N+1-F$. For a chosen positive integer $E$, an approximation to $E/N$ occasionally equals $E/F$ exactly. We try the successive continued-fraction approximations $a/b$ to $E/N$. When $Eb/a$ is an integer strictly between zero and $N$, it proposes a value of $F$. The resulting sum $s=N+1-F$ must give a nonnegative square $s^2-4N=(p-q)^2$. [Why a good exponent works](when-one-power-needs-at-most-one-square-test.md)

The guesses here are $E=\operatorname{lcm}(1,2,\ldots,j)$, the smallest multiple of all the integers through $j$. We keep each distinct $E\le N$ satisfying $(E+1)^2\ge4N$. Below this size, the remainder $N\bmod E$ is already too small to admit the true sum. Each retained $E$ receives the stronger test $(N\bmod E+1)^2\ge4N$ before we generate any fractions.

If both primes have $k$ bits, then $2^k\le p+q-1<2^{k+1}$. At a fraction $a/b$ with $a>0$ the implied value of $p+q-1$ is $(Na-Eb)/a$. Once this value lies strictly between zero and $2^k$, every later approximation on this side is closer to $E/N$ and gives a smaller value. Approximations on the other side give a negative value. We stop even if the current proposed totient is nonintegral. We also exhaust the full list independently to compare the counts and the returned factors. [Lean stopping rule](../PrimeFactors/UpperConvergentDeficit.lean)

For 10,697,327 the guess at $j=13$ is $E=360{,}360$. The fourth approximation is $3/89$, giving $F=10{,}690{,}680$ and $s=6{,}648$. The discriminant is $1{,}406{,}596=1{,}186^2$. Halving $6{,}648\pm1{,}186$ gives the two factors. On this same guess, $\gcd(2^E-1,N)$ already gives 2,731. Fermat search reaches the factors on its 54th midpoint. [Checked fixture](../benchmarks/scaled-power-menu.json)

## What happened on independent small examples?

Before running the search we fixed the seed, four widths and sixteen pairs per width. Each side of each pair comes from a separate SHAKE-256 label. The generator reuses the same seed and sample indices across widths, taking different numbers of output bits. We take the first sixteen distinct unordered pairs of different primes at each width. The search receives just the product and common width. The modular comparison takes one gcd for **every** eligible exponent, including exponents rejected by the remainder test. The Fermat comparison tests consecutive midpoints from the ceiling of the square root until success or 1,024 trials. These are different operations with different costs.

| Bits per prime | Products | Continued-fraction splits | Base-two gcd splits | Fermat splits | Product–exponent pairs tested | Fraction visits, stopped / full | Discriminant square roots |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 12 | 16 | 1 | 1 | 16 | 50 | 214 / 595 | 5 |
| 20 | 16 | 0 | 0 | 4 | 80 | 484 / 1,655 | 3 |
| 28 | 16 | 0 | 0 | 0 | 112 | 766 / 2,914 | 0 |
| 36 | 16 | 0 | 0 | 0 | 117 | 964 / 3,973 | 2 |

The single continued-fraction success occurred at two prefix exponents on the same product. All twenty products recovered by any of the three methods have Lean certificates for both primality and multiplication. The sample is small and gives no general success-rate estimate. [Generator and certificate builder](../experiments/scaled_power_menu.py)

## What did the two 2,048-bit runs cost?

Both controls have 106 eligible exponents, first introduced at indices between 709 and 1,429. Every one passed the remainder check. For the modular comparison we start at $2\bmod N$ and update the running residue by the quotient of successive distinct exponents. This costs 254 modular powering updates per control, including the steps below the eligibility threshold. Across the eligible exponents all 106 gcds were 1 on each control. Fermat used all 1,024 candidate square roots on each, in addition to one initial integer square root for its starting midpoint.

| Continued-fraction work | Fresh 2,048-bit product | Crossed 2,048-bit product |
|---|---:|---:|
| Fractions visited before stopping | 15,754 | 15,794 |
| Fractions in the full lists | 94,345 | 94,644 |
| Integer totient guesses before stopping | 579 | 553 |
| Integer totient guesses in the full lists | 589 | 569 |
| Guesses inside the advertised width band | 2 | 1 |
| Nonnegative discriminants reaching a square root | 0 | 0 |
| Factors recovered | 0 | 0 |

All three width-compatible guesses gave a sum smaller than $2\sqrt N$, so each failed before the square root. The stopping rule shortened the calculation on both inputs. Finding a way to choose a successful exponent for unrelated 1,024-bit primes remains open. Run `python3 -m experiments.scaled_power_menu --check --verify` to regenerate the panel, compare every stored count and check the successful factorizations. [Full results](../research/scaled-power-menu.json) · [Native comparison cases](../benchmarks/scaled-power-menu.json)
