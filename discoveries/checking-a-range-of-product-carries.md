# Checking a whole range of guesses at once

On a specially constructed 2,048-bit number, two square tests and one greatest-common-divisor calculation found both primes. One quantity we were trying to guess was wrong by a **354-bit number** if we guessed zero. We found the right value without trying each guess separately. An older search in the project also recovered these primes. On two earlier numbers of the same size, the new search found neither pair. [Checked full-size example](https://marius-bughiu.github.io/prime-factors/#carry-interval-constructed-2048) · [Construction and comparison](../research/carry-interval-example.json)

## Why two tests can cover so much

In the rounded-digit search, each guess for the lower carry changes a proposed sum by exactly one. Fix the base and the upper carry. For all the lower guesses together, the product of two unknown integers is now known exactly and their sum lies in a known interval. The smaller integer must therefore lie between two bounds we can calculate with square roots. [The original rounded-digit calculation](factoring-from-two-rounded-digits.md)

Over a sufficiently short interval, that integer and its partner have a *second* weighted sum that can take at most two integer values. We calculate the weights by continued fractions. We try both values, check any resulting divisors, then take a greatest common divisor with the original input. The public inequality deciding whether this works can fail. A failed inequality leaves the whole interval unresolved. Lean verifies the rule even when the two intermediate integers are even or composite. [Exact interval and coverage proof](../PrimeFactors/CarryInterval.lean) · [Divisor-window proof](../PrimeFactors/ArbitraryDivisorWindow.lean) · [Hiary's short-interval factorization method](https://arxiv.org/abs/1408.2608)

On the 2,048-bit constructed example the base was $2^{1016}$, the upper correction was zero, and the lower correction was allowed to vary from $-2^{357}$ to $2^{357}$. Those are $2^{358}+1$ possible guesses. It took three square roots to set up the interval, four continued-fraction steps to choose the weights, two square tests and one gcd. The independent certificate checks both 1,024-bit primes and their product. A 417-bit constructed example took the same work with a smaller range. The searches were given the products and the stated settings. Both examples were designed for these settings. [Benchmark inputs, budgets and outputs](../benchmarks/carry-interval.json)

The original input also has an easier route. The known coefficient 47,177 factors as $13\times19\times191$. Of its eight divisors, only 247 could divide the smaller intermediate root and leave a candidate in the interval for the smaller original prime. Applying the earlier divisor-window search there found a prime after fourteen continued-fraction steps and one square test. The new method can work without factoring the coefficient. This comparison does not establish a speed advantage on the example. [Construction and measured alternatives](../research/carry-interval-example.json)

## What happened on the earlier products?

At base $2^{1021}$, with upper correction zero, Lean proved that every lower correction through $\pm2^{256}$ misses on each of the two older 2,048-bit products. At base $2^{704}$, the same public test leaves this entire range unresolved on the first product. Both outcomes leave the primes unknown. [Checked empty interval](https://marius-bughiu.github.io/prime-factors/#carry-interval-fresh-1021) · [Benchmark fixtures and exact settings](../benchmarks/carry-interval.json)

We also ran every base $2^{513},\ldots,2^{1024}$ with all nine upper corrections from $-4$ through $4$, keeping the same lower-carry range of $\pm2^{256}$. The first product had 472 covered intervals and 4,136 unresolved. The second had 473 covered and 4,135 unresolved. Neither run found a factor. The 929 and 930 square tests respectively exclude the three square roots used to form a nonempty sum interval. These aggregate counts were measured by integer arithmetic. The downloadable Lean exclusions above cover the two specified individual intervals. [Search implementation](../experiments/carry_interval.py)

<details>
<summary>Reproduce the counts for all 4,608 intervals on each product</summary>

Run this Python code from the repository root.

~~~python
from collections import Counter
import json
from pathlib import Path
from experiments.carry_interval import search

cases = json.loads(Path("benchmarks/radix-carries.json").read_text())
for case in cases:
    if case["id"] in {"radix-carry-fresh-2048", "radix-carry-crossed-2048"}:
        counts = Counter()
        for exponent in range(513, 1025):
            for high in range(-4, 5):
                run = search(int(case["n"]), exponent, high, 2**256)
                counts["covered" if run["covered"] else "unresolved"] += 1
                counts["squares"] += run["work"]["square_tests"]
                counts["hits"] += len(run["hits"])
        print(case["id"], counts)
~~~

</details>

## Could covering all those intervals solve ordinary inputs?

For two distinct random 1,024-bit primes conditioned on a 2,048-bit product, Lean bounds the reach of the *entire family*. It allows every one of the 512 tested bases, **any upper correction** chosen after reading the product, and every lower correction in the range. The estimates still apply if checking every guess becomes free.

| Allowed lower correction | Fraction of target pairs that could give a factor |
|---|---:|
| Up to $\pm2^{256}$, used on the older products | Less than $1/2^{214}$ |
| Up to $\pm2^{357}$, used on the successful 2,048-bit example | Less than $1/2^{113}$ |
| Up to $\pm2^{400}$ | Less than $1/2^{69}$ |

To see the constraint, measure each hidden prime's distance from its nearest multiple of the chosen base $D$. If a guess succeeds anywhere with lower correction at most $K$ in magnitude, the product of those distances is at most $(K+\tfrac12)D$. Counting pairs of distances in ranges whose sizes double gives the three bounds. The counting argument includes accidental square matches. The explicit numerical premise, at least $2^{2021}$ eligible prime pairs, follows from published unconditional prime counts. A way to predict much larger corrections from the whole product, or to select a base outside this family, would need its own analysis. [Nearest-distance theorem](../PrimeFactors/CenteredCarryDistances.lean) · [Three checked bounds](../PrimeFactors/CarryRemainderPairs.lean) · [Population denominator](factoring-from-two-rounded-digits.md#how-many-ordinary-products-could-it-reach)
