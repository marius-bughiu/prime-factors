# When does the fourth-root formula beat consecutive Fermat tests?

We constructed a 2,048-bit input on which two integer fourth roots give both 1,024-bit primes. Testing every consecutive Fermat midpoint would take **more than $2^{719}$ tests** before the first success. There is a second inexpensive way to factor this particular number. Its construction leaves a recognizable remainder, and checking the first midpoint with that remainder also succeeds. [Exact input, primes, widths and all three search results](../PrimeFactors/FullWidthQuarticLaterMidpoint.lean)

## How the input was selected

Set $F=2^{360}$, $x=F+1$, $s=5(2^{149}+48628)$ and $y=Fs$. The input is $N=x^4+4y^4$. We chose this family so that the two predicted factors could be certified as primes, and searched successive coefficients until both were prime. The reported coefficient was the 48,629th candidate. A search given just $N$ reads $y$ as the integer fourth root of $\lfloor N/4\rfloor$, then $x$ as the fourth root of the remainder. The outputs are $m-2xy$ and $m+2xy$, where $m=x^2+2y^2$. Both are prime and multiply to $N$. [Prime certificates and executable fourth-root result](../PrimeFactors/FullWidthQuarticLaterMidpoint.lean)

## Two ways to choose a midpoint

Ordinary Fermat starts at $c=\lceil\sqrt N\rceil$ and tests every integer from there. Lean proves that $m^2-N=(2xy)^2$ and that **every** midpoint from $c$ through $m-1$ fails. The inclusive test count $m-c+1$ lies strictly between $2^{719}$ and $2^{720}$. The proof uses the two primes and integer bounds on $\sqrt N$. It does not require running that many tests. [Rank and proof excluding earlier squares](../PrimeFactors/FullWidthQuarticLaterMidpoint.lean)

Now use another feature of the same input. Both primes are $1\bmod 2F$. Therefore $(p-1)(q-1)$ is divisible by $4F^2$, giving $m\equiv(N+1)/2\pmod{2F^2}$. The public $N-1$ has exactly 362 factors of two, which identifies $F$ as $2^{362-2}$ under the construction rule. The first integer at or above $c$ with the indicated remainder is already $m$. The two comparisons show exactly which work the fourth-root result avoids. [Checked public remainder and first selected midpoint](../PrimeFactors/FullWidthQuarticLaterMidpoint.lean)

## A smaller example and a general rule

With $x=3$ and $y=40$, the product is $10{,}240{,}081$. The first eight ordinary tests, starting at 3,201, fail. The ninth gives $3209^2-10{,}240{,}081=240^2$, hence $2{,}969\times3{,}449$. Both factors have 12 bits. More generally, for positive $x,y$ the displayed factor pair occurs on the first ordinary test exactly when $x=1$, and its inclusive rank is exactly $x^2$ if and only if $x^2\le2y$. With prime outputs this is the first successful test. [General criterion, counterexample beyond the threshold and small examples](../PrimeFactors/QuarticMidpointRank.lean)

The examples establish different costs on an exceptionally rare family. A uniformly chosen eligible prime product has a chance below $2^{-1128}$ of satisfying either unscaled recognition interval. [Population theorem](reading-the-other-fourth-power.md) · [Decimal inputs and outputs](../benchmarks/quartic-readings.json)

Replay this example with `python3 -m experiments.quartic_readings --case quartic-later-midpoint-2048`. Omitting the case name also checks the two smaller scaled successes, the first-midpoint example and an existing 2,048-bit comparison on which all six readings miss. The replay reports the unresolved product in that last case. [Replay implementation](../experiments/quartic_readings.py)
