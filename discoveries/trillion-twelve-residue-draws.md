# What a trillion random draws can find

Suppose someone hands us a product of two distinct 1024-bit primes. If we try the twelve-residue search with a trillion independent, uniformly random integers from zero through one less than the product, the chance it finds a prime is **less than one in $2^{939}$**. This holds for every such pair of primes. The randomness is in our choices of integers. [Lean proof](../PrimeFactors/TwelvePracticalBudget.lean)

The experiment gives twelve remainders the same label modulo a hidden prime. Two draws with the same label at one prime can reveal that prime through a greatest common divisor. The setup can also find a factor before it computes any labels. The probability calculation includes both routes, and it includes the extra checks the experiment performs when two public labels match exactly. [Search and duplicate handling](../experiments/twelve_residue_collision.py) · [The twelve-residue construction](comparing-twelve-remainders-at-once.md)

Write $N=pq$. Each public draw is uniform modulo $p$ and modulo $q$. At most 13 residues at either prime are exceptional, so one draw can trigger the setup with probability at most $13/p+13/q$. For two independent draws, once one is fixed and regular, at most twelve residues at each prime give the same label there. That pair contributes at most $12/p+12/q$. We include every local match, even when it gives the whole product as the gcd.

With $m$ draws there are $m$ possible exceptional draws and $\binom m2$ unordered pairs. Adding the individual upper bounds gives

$$
\Pr(\text{a factor is found}) \;\le\;
\left(13m+12\binom m2\right)\left(\frac1p+\frac1q\right).
$$

This bound allows different pairs to share a draw. It follows by counting a word once for each way it could make the search succeed, which can only overcount it. At $m=10^{12}$ the first parenthesis equals $6{,}000{,}000{,}000{,}007{,}000{,}000{,}000{,}000$. Since both primes are at least $2^{1023}$, twice that integer divided by $2^{1023}$ is less than $2^{-939}$.

A fast way to compare a trillion labels would still face this probability. The open question is whether the product can guide us to particular inputs whose labels agree at just one prime. That would use a different sampling rule and would require its own evidence. The published benchmark uses fixed pseudorandom seeds for reproducibility. The theorem describes independent uniform draws with replacement. [Formal sampling event and bound](../PrimeFactors/TwelvePracticalBudget.lean)
