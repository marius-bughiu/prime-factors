# What changes when the interval grows?

For $143=11\cdot13$, the signed totals at lengths 7 and 8 are $-15$ and $-44$. Add 1,000 to both. The resulting readings, 985 and 956, still tell us the primes sum to 24. The shared error disappears when we take their difference. We used the known totals to make these readings. A way to obtain comparable readings cheaply at a large product remains open. [Checked example and two-reading theorem](../PrimeFactors/PrimitiveIntervalCutoffTrend.lean)

## When does the difference tell us the sum?

Write $S=p+q$ and $N=pq$ for two distinct odd primes $p<q<2p$. For an integer length $b$ between $\lfloor q/2\rfloor$ and $p-1$, both prime contributions have entered the formula, counting a possible zero contribution at the endpoint. The total is

$$V(b)=b^2+S^2-2N-(2b+2)S+4b+2.$$

If $b$ and $b+h$ both lie in this range, their totals differ by $h(2b+h+4-2S)$. At 143, use $b=7$ and $h=1$. The observed difference is $-29$, giving $-29=19-2S$ and $S=24$. For 1,024-bit primes the five lengths from $2^{1023}-2$ through $2^{1023}+2$ always work, so selecting two such lengths requires no knowledge of the factors. Balance alone can leave fewer choices. At $91=7\cdot13$ only length six qualifies. [Five universal lengths and the 91 example](../PrimeFactors/PrimitiveIntervalCutoffTrend.lean)

An error that changes with the length can absorb this entire signal. Suppose the measured total is $V(b)+mb+c$ with unknown integers $m,c$. On the indicated range, **every proposed sum** gives the same readings after a suitable change to $m$ and $c$. This is an ambiguity among the predicted readings. The product has a unique prime factorization. If the same error law also holds at lengths zero and one, genuine readings there fix $m,c$ because the true totals there are zero and one. A third reading at the public length then determines the sum. [Ambiguity and calibration proofs](../PrimeFactors/PrimitiveIntervalCutoffTrend.lean)

## What can we measure from the product alone?

Write $F(b)$ for the sum of $2-\gcd(N,i+j)$ over $1\le i,j\le b$. Below the smaller prime this is exactly the signed character total. For every length, including zero, we can obtain its second difference $F(b+2)-2F(b+1)+F(b)$ with just four gcds. If $f(t)=2-\gcd(N,t)$, it equals

$$f(2b+4)+2f(2b+3)+f(2b+2)-2f(b+2).$$

At 143 the second differences at lengths 4, 5 and 6 are $-18$, $-22$ and $2$. At the first two changes, the gcd inputs already include 11 and 13 respectively. Whenever all three lengths are in the range above, the second difference is exactly two for every prime pair. The cheap measurement therefore loses the coefficient containing the sum. [Four-gcd identity and all three numerical results](../PrimeFactors/TriangularGcdCurvature.lean)
