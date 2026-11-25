# When one equation can select a window

On the product **101,000,651**, a single quartic leaves one of 37 possible window labels. Window 26 contains the prime **10,007**. The reason this works is visible from the product: throughout the chosen interval any factor pair must have sum 20,100. Fermat's method already gives both primes on this example. For the existing general 2,048-bit search, the missing ingredient is a pair or collection of independent equations whose coefficients vary predictably across windows. Lean proves what that ingredient would buy and why simply translating the same collection loses the label. [Proof and worked input](../PrimeFactors/WindowEliminant.lean) · [Current complete window grid](recursive-integer-valued-windows.md)

## Keep the label while eliminating the offset

Write $T$ for a window label and $x$ for the position within that window. Suppose the product supplies a square matrix of integer polynomials $M(T)$ with $r$ rows, and every true factor at $(t,x)$ satisfies

$$M(t)(1,x,\ldots,x^{r-1})^{\mathsf T}=0.$$

Then $R(t)=0$ for $R(T)=\det M(T)$, since the first entry of that vector is one. If every coefficient in row $i$ has degree at most $b_i$ in $T$, then $\deg R\le E=\sum_i b_i$. A **nonzero** $R$ therefore leaves at most $E$ integer labels, independent of how many labels were provisionally possible. Each remaining label still needs an offset and a divisor check. This is classical elimination. For example, two equations in $x$ can supply the usual Sylvester matrix by taking suitable powers of $x$ times each equation. [Checked determinant and degree bounds](../PrimeFactors/WindowEliminant.lean) · [Sylvester’s original elimination paper, pp. 54–57](https://upload.wikimedia.org/wikipedia/commons/3/36/The_collected_mathematical_papers_of_James_Joseph_Sylvester_%28IA_collectedmathem01sylvrich%29.pdf)

There are two ways to obtain $R$. One can use the polynomial matrix directly, or evaluate its determinant at $E+1$ distinct public labels and interpolate over the rationals. The proof covers the latter even if all the readings are zero. To save work, the global coefficient formulas or a proved degree bound and an evaluator must already be available. Interpolating independently computed local reductions after visiting all windows has already incurred their cost. Forming the matrices, computing the determinants, working with their coefficient sizes and finding the integer roots all count. [Exact interpolation statement](../PrimeFactors/WindowEliminant.lean)

## The 37-window check

Let $N=101000651$ and $C=\lceil\sqrt N\rceil=10050$. Choose the odd trial divisors from $C+1-\lfloor\sqrt{(C+1)^2-N}\rfloor=9903$ to $\lfloor\sqrt N\rfloor=10049$. These endpoints give 74 positions. Write them as $d=9903+4t+2x$, with $0\le t<37$ and $x\in\{0,1\}$. If $d q=N$, then $d+q$ is even and at least $20100$. Were it at least $20102$, we would have

$$N\ge d(20102-d)\ge9903(20102-9903)=101000697>N.$$

The middle inequality follows from $(d-9903)(10199-d)\ge0$. Thus $d+q=20100$ throughout the interval at any divisor. Both the endpoint choice and the two offset equations use only $N$. [Endpoint arithmetic, sum and coverage](../PrimeFactors/WindowEliminant.lean)

Set $d_x=9903+4T+2x$ and $f_x(T)=d_x(20100-d_x)-N$. On $x\in\{0,1\}$ the factor equation is $f_0+(f_1-f_0)x=0$. Multiplying by $x$ and using $x^2=x$ supplies the second row. The determinant is

$$\det\begin{pmatrix}f_0&f_1-f_0\\0&f_1\end{pmatrix}
=f_0 f_1=(4T-104)(190-4T)(4T-102)(188-4T).$$

Its only integral roots are 26 and 47. Just 26 belongs to the 37 windows, and its first offset gives $N=10007\times10093$. Lean checks exhaustiveness on the interval and primality of both factors. The same arithmetic gives $C^2-N=1849=43^2$, explaining the simpler Fermat solution. The small example tests the label calculation and provides no comparison timing. [Checked roots and factorization](../PrimeFactors/WindowEliminant.lean)

## Why the obvious compressions lose information

Translating fixed equations by $x\mapsto x+h(T)$ multiplies their coefficient rows on the right by a triangular matrix with entries $\binom ijh(T)^{i-j}$ and diagonal entries one. Left multiplication by any determinant-one matrix also preserves the determinant. Consequently a fixed matrix of equations translated between windows has the same determinant everywhere. A nonzero constant supplies no occupied label, and a zero constant leaves every label. New independent local relations or a selection of different rows can break this invariance. The calculation explains why merely reusing a translated lattice basis cannot by itself make the determinant select a window. [Checked translation identity](../PrimeFactors/WindowEliminant.lean) · [Earlier basis reuse and measured costs](reusing-a-quartic-basis.md)

Multiplying equations from different windows separately can lose their pairing. For two windows, let the first list be $X-1,X-2$. The second list $X-1,X-3$ has one same-window match. Interchanging its two entries leaves its product polynomial unchanged and removes that match. In both arrangements the product polynomials have the common root 1. One must preserve which equations belong together, even when at most one window can match. [Checked two-window counterexample](../PrimeFactors/WindowEliminant.lean)

There is an exact size bound for a deterministic summary of **arbitrary independent** local linear rows. Over a finite field $K$, let the rows be $X-a_i$ for $L$ windows. If the summary must determine whether $a_i=u$ for any later query $(i,u)$, then two different lists must have different summaries. Thus there must be at least $|K|^L$ states. One remainder modulo a fixed monic degree-$s$ polynomial has only $|K|^s$ possibilities, giving $s\ge L$. Even if the second input supplies a whole linear row per window and promises at most one match, the same injectivity proof works when $|K|\ge3$. At a coordinate where two first inputs disagree, choose a query matching the first. At every other coordinate choose a value different from both. Ordinary interpolation attains $L$ coefficients when $L$ distinct label nodes exist. This is the deterministic indexing argument. The bound concerns reusable summaries of arbitrary lists. Product-dependent families with a short public description need not realize these arbitrary inputs. [Checked state count and interpolation](../PrimeFactors/WindowEliminant.lean) · [Kremer, Nisan and Ron on one-round communication](https://cris.huji.ac.il/en/publications/on-randomized-one-round-communication-complexity/)

The Taylor divisibility constraints by themselves allow every residual polynomial $P$: at anchor zero, $X^mP$ satisfies all $m$ conditions. A factor-window equation also has to meet a stringent size bound, which this construction does not impose. A useful next candidate would show that those size bounds force additional structure across the labels, producing a small **nonconstant** determinant before the block sweep. Ordinary fast evaluation of consecutive products already exploits the special structure of factorials. Its arithmetic cost is a separate question from encoding arbitrary local equations. [Checked Taylor example](../PrimeFactors/WindowEliminant.lean) · [Bostan, Gaudry and Schost on structured multipoint evaluation](https://cs.uwaterloo.ca/~eschost/publications/pollard.pdf)
