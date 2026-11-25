# Two full-size successes and the frequency of the pattern

One square test recovered both primes of two constructed 2,048-bit products. In one case the product itself supplied a 484-bit multiplier. In the other, one prime is about 44% larger than the other. Both prime pairs were constructed to fit the rule. On the earlier fresh and crossed comparison products, even trying every eligible multiplier finds neither prime by this rule. For two uniformly chosen distinct 1,024-bit primes conditioned on a 2,048-bit product, fewer than one pair in $2^{465}$ can pass any of these tests. [Derivation of the test](grouped-norm-factors.md) · [Full-size Lean outputs](../PrimeFactors/GroupedNormExamples.lean) · [Counting proof](../PrimeFactors/GroupedNormFrequency.lean)

A sharper count gives fewer than one in $2^{481}$ eligible prime pairs. It also constructs many odd inputs that do admit a balanced split, with the primality of the two resulting factors left open. [Sharp order of the count](grouped-norm-density.md)

## What the search receives

Given only $N$, compute $T=\lfloor\sqrt N\rfloor$, the offset $h=N-T^2$, and the largest eligible multiplier $k=\lfloor(T-1)/h\rfloor$ when $h>0$. Test whether $1+4k(T-hk)$ is a square. If it is, its square root determines both factors. For example, 50,629 gives $T=225$, $h=4$, and $k=56$. The square test gives $225=15^2$ and the factor formula returns $257\times197$. For a square input or an empty multiplier interval the probe returns no result. The command below runs the Lean function directly. The benchmark separately checks the primality and product of the factors it returns. [Factor formula and proof](../PrimeFactors/GroupedNormFactors.lean) · [Public inputs and expected outcomes](../benchmarks/grouped-norm.json)

```sh
lake env lean --run experiments/GroupedNormProbe.lean 50629
```

| 2,048-bit product | Eligible multipliers | Chosen multiplier | Result |
| --- | ---: | --- | --- |
| Adjacent coefficients | 484-bit count | Largest | Both primes |
| Separated primes | 30 | 30 | Both primes |
| Earlier fresh comparison | 1 | 1 | No hit |
| Earlier crossed comparison | 1 | 1 | No hit |

On the first constructed input, ordinary Fermat search would advance $2^{539}-1$ times from its first midpoint to the prime midpoint. On the second it would advance more than $2^{1017}$ times. These counts compare consecutive unweighted Fermat midpoints. They do not measure the cost of other factoring methods. [Checked first-test outputs](../PrimeFactors/GroupedNormExamples.lean)

## How the two successful examples were constructed

Both use $N=(u^2+h a^2)(v^2+h b^2)$ with $av-bu=1$ and $uv\le h$. Then $T=uv+hab$ and its quotient selects $k=ab$ on the first test. Finding primes during construction was separate from running the search. The sizes of the powers of two below give the existing partial-order certificate generator enough known factors of each prime's predecessor.

* For the first, take $h=2^{540}$, $u=v=1$, $b=15\cdot2^{238}+39{,}054$, and $a=b+1$. Starting at offset zero, 39,054 was the first offset for which the two candidates passed the prime-certificate generator. The multiplier is $a b$.
* For the separated pair, take $a=6$, $b=5$, $D=2^{506}$, $u=1+6D$ and $v=1+5D$. Start with the least $h\ge27\cdot2^{1014}$ divisible by $D$ with $u^2+36h\equiv1\pmod{101}$ and $v^2+25h\equiv1\pmod{103}$. Try successive values spaced by $101\cdot103D$. At offset 87,553 both candidates passed the certificate generator. The method receives none of these parameters at discovery time. [Certificate generator](../scripts/factor.py) · [Lean decoder](../experiments/GroupedNormProbe.lean)

## Counting all possible successes

An accepted positive multiplier with $hk<T$ gives positive integers $a,b,u,v$ satisfying $av-bu=1$ and $T=uv+hab$. This converse covers a successful multiplier however it was chosen. Here is an encoding of any such witness with $T<2^{1024}$. It also bounds how many different products can succeed.

1. Store the two indices $i=\lfloor\log_2 a\rfloor$ and $j=\lfloor\log_2 b\rfloor$. Each needs ten bits since $ab\le T<2^{1024}$. Set $A=2^i$ and $B=2^j$.
2. Store $((h-1)A+a-A)B+b-B$. This number is strictly below $hAB\le hab\le T$, so it takes at most 1,024 bits. Division and remainder by the known bases recover $a,b,h$.
3. Store $z=\lfloor u/a\rfloor$. Both $u$ and $v$ are at least $z$ by $av=bu+1$. Thus $z^2\le uv<2^{1024}$ and 512 bits suffice. If $(u',v')$ also satisfies the determinant equation with these $a,b$, then $u'-u=a(vu'-v'u)$. Equal quotients and equal remainders modulo $a$ force $u'=u$, and then $v'=v$.

These 1,556 bits determine $T$ and $N=T^2+h$. A product occurring through several witnesses still contributes only one distinct input. Lean proves the bound for every finite set of successful products and every even root-width bound. With $X=2^{1023}$, the population of eligible **unordered** pairs of distinct primes exceeds $(0.22X/710)^2/2$. Unique prime factorization makes their products distinct. Dividing $2^{1556}$ by the population bound gives the stated fraction. The prime-count inequality uses Rosser and Schoenfeld on paper. Lean checks the finite encoding, the implication from the executable test, and the final integer comparison. [Population derivation](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Rosser and Schoenfeld, Corollary 1](https://doi.org/10.1215/ijm/1255631807) · [Lean counting theorems](../PrimeFactors/GroupedNormFrequency.lean)

The expense of testing the whole family depends on $h$. For each fixed floor root $T<2^L$, the $2T$ nonsquare inputs with that root have offsets $1$ through $2T$. The total number of eligible multipliers over them is at most $LT$. In a block $2^i\le h<2^{i+1}$ there are at most $2^i$ offsets and each costs at most $\lfloor T/2^i\rfloor$ tests. Larger offsets contribute zero. Thus the mean for uniform offsets at fixed $T$ is at most $L/2$, including at most 512 tests for $L=1024$. A single input with $h=1$ can still have $T-1$ multipliers. The benchmark tests only the largest. [Dyadic sum bound](../PrimeFactors/GroupedNormFrequency.lean)

## Changing which square we start from

Completing the square in a successful test gives $(2hk-T)^2+h(2m+1)^2=N$. Searching for another point on this ellipse leads back to the existing norm-representation problem. Starting instead from an upper square, $N=T^2-H$, gives a hyperbola. Its known point $(T,1)$ can be multiplied by an integral Pell unit $r+t\sqrt H$. If the new point has coordinates $T+2Hk$ and $2m+1$, then

$$2H(kT-m)=N(r-1).$$

When $N$ is coprime to $2H$, this makes the candidate $kT-m$ a multiple of $N$, so its gcd returns the whole input. This includes every power of every integral Pell unit starting from that point. A different orbit would require another means of finding it. [Lean identity and divisibility](../PrimeFactors/GroupedNormFrequency.lean) · [Previous norm searches](searching-norm-directions.md)
