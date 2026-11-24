# How many small-root searches cover scattered factor digits?

Suppose a proposed pattern for the larger divisor $q$ of $N=pq$ specifies every binary digit except those in a finite set $A$. Write $u=|A|$. We can measure exactly what this pattern buys a search using ordinary integer arithmetic progressions. With at most $2^k$ consecutive indices per progression, the minimum number of progressions covering **every word** consistent with the pattern is

$$
  2^{u-H},\qquad H=\max_{e\ge0}|A\cap[e,e+k)|.
$$

This counts the calls needed for complete coverage of a proposed pattern. The pattern itself is additional information. Below we also bound how frequently a menu of guesses chosen from public product digits can cover the true factor. [Lean proofs](../PrimeFactors/ScatteredFactor.lean)

## The exact cover

Consider any progression $a+dt$, $0\le t<2^k$, with positive integer step $d=2^e v$ and $v$ odd. The $k$-bit window of $x=a+dt$ beginning at $e$ has value

$$
  \left\lfloor x/2^e\right\rfloor\bmod 2^k
  =\left(\left\lfloor a/2^e\right\rfloor+vt\right)\bmod 2^k.
$$

These window values are distinct because $v$ is odd. At most $2^{|A\cap[e,e+k)|}$ satisfy the fixed digits. Summing over progressions, including those with different steps, proves the lower bound. To attain it, choose a maximizing window and enumerate assignments to the free positions outside it. For each assignment, retain the low and high digits outside the window and set the window to zero to get a start $a$. The progression $a+2^e t$ contains every compatible completion of that assignment. Other integers in the progression can be discarded after testing. The empty mask and the zero-length bit window obey the same formula. [Upper and lower bounds](../PrimeFactors/ScatteredFactor.lean)

For example, the free positions $\{1,3,5\}$ and base word 129 give the eight words $129,131,137,139,161,163,169,171$. A four-term progression hits at most two. The four progressions with step 2 and starts $129,137,161,169$ attain the bound. At the motivating size, fix the leading and trailing bits of a 1,024-bit word to one and leave precisely positions $1,3,\ldots,1021$ free. A 512-bit window contains at most 256 of these 511 unknown positions. A full cover therefore takes **exactly $2^{255}$ progressions** with at most $2^{512}$ terms each. Concentrating the same 511 unknown digits in a single window permits one progression. [Kernel-checked 1,024-bit mask](../PrimeFactors/ScatteredFactor.lean)

## What the lattice theorem supplies

Assume $q\ge\sqrt N$ is the divisor sought. A positive progression containing $q$ gives an index $t$ for which $a+dt$ vanishes modulo $q$. The constructed step is a power of two and $N$ is odd, so its modular inverse exists. This gives a monic linear polynomial in $t$ modulo the hidden divisor. May's Theorem 7 finds all such roots of size at most a fixed constant times $N^{1/4}$ in polynomial bit time. Retain only exact proper divisors. For 2,048-bit $N$, $2^{512}\le 2^{1/4}N^{1/4}$. After the mask is supplied, the constructed search takes $2^{u-H}\operatorname{poly}(\log N)$ bit operations, including generation of the starts. The theorem about the minimum number of progressions concerns literal integer words. Modularly wrapped values, useful multiples of divisors, and multivariate equations have different coverage. [May, Theorem 7, pp. 37–38](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38)

Herrmann and May treat scattered digits using one variable per unknown block. Their larger-dimensional result assumes their generated polynomials are algebraically independent and that their common roots can be extracted efficiently. Their asymptotic threshold for balanced factors approaches a known fraction of $\log 2$ of the factor digits, with positive slack, and their cost grows exponentially with the block count. The elementary cover above gives an unconditional bound that depends on the locations of the unknown digits. A mask on the factor sum has the same combinatorial cover, but the sum need not divide $N$, so the single-divisor lattice theorem applies here specifically to $q$. [Herrmann and May, Assumption 1 and Theorems 4–5](https://iacr.org/archive/asiacrypt2008/53500412/53500412.pdf)

## Guesses chosen from half the product

Put $X=2^{1023}$. Choose distinct primes $X\le p<q<2X$ uniformly from the pairs for which $pq$ has exactly 2,048 bits. Allow an arbitrary function of the entire residue $a=pq\bmod X$ to select a candidate set $C(a)$ of larger-factor words. For a fixed odd $q\in C(a)$, the congruence $pq\equiv a\bmod X$ determines $p$ modulo $X$. The interval $[X,2X)$ contains exactly one representative. Consequently the number of covered pairs is at most $\sum_{a\ {\rm odd}}|C(a)|$. This grants arbitrary preprocessing to the selector. [Finite injection](../PrimeFactors/ScatteredFactor.lean)

There are $X/2$ odd residues. The established prime count gives at least $\tfrac12(0.22X/\log X)^2$ eligible pairs. Thus if $|C(a)|\le C$ in every row, the hit probability is at most $C(\log X/0.22)^2/X<2^{24}C/X$. For a budget of $2^{40}$ progressions per residue, each carrying an alternating mask as above, the probability of a matching factor **inside the proposed mask** is less than $2^{-703}$, since $C\le2^{40+256}$. Even allowing every literal integer in each progression gives probability less than $2^{-447}$, with $C\le2^{40+512}$. The selector can choose different guesses for every low product word. These are bounds on the candidate sets it covers. Access to other product digits or an incidental factor found outside those sets requires a separate analysis. [Explicit prime-pair denominator](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Rosser and Schoenfeld, Corollary 1](https://doi.org/10.1215/ijm/1255631807)
