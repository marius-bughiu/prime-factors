"""Integral Newton coordinates on the nodes u, u+R, ..., u+dR."""

from math import gcd, prod


def coprime_factorials(n, degree):
    """Return the largest divisors of j! coprime to n, for j = 0,...,degree."""
    factorials = [1]
    for j in range(1, degree+1):
        part = j
        common = gcd(part, n)
        while common > 1:
            part //= common
            common = gcd(part, n)
        factorials.append(factorials[-1]*part)
    return factorials


def radix_threshold(bound, power, factorials):
    """Smallest positive radix meeting the strict, squared LLL norm bound."""
    dim = 2*power+1
    exponent = 2*power*dim
    rhs = dim**dim * 2**(power*dim) * bound**(2*power*(power+1))
    limit = rhs // prod(factorials)**2
    low, high = 0, 1 << ((limit.bit_length()+exponent-1)//exponent)
    while low+1 < high:
        middle = (low+high)//2
        if middle**exponent <= limit:
            low = middle
        else:
            high = middle
    return high


def congruences(factors, u, radix, factorials):
    """Newton coefficient of each weighted monomial, modulo its required divisor."""
    degree = len(factors)-1
    modulus = radix**degree * factorials[-1]
    bounds = [modulus//(radix**j*factorials[j]) for j in range(degree)]
    columns = [[0]*len(factors) for _ in bounds]
    coefficients = [1]
    for k, factor in enumerate(factors):
        for j, value in enumerate(coefficients[:degree]):
            columns[j][k] = value*factor % bounds[j]
        # X times the jth Newton basis polynomial equals the next basis
        # polynomial plus (u+jR) times the current one.
        updated = [0]*(len(coefficients)+1)
        for j, value in enumerate(coefficients):
            updated[j] = (updated[j]+(u+j*radix)*value) % modulus
            updated[j+1] = value
        coefficients = updated
    return bounds, columns


def vanishes_on_grid(coefficients, modulus):
    """d+1 consecutive zero values force every forward difference to vanish."""
    for k in range(len(coefficients)):
        value = 0
        for c in reversed(coefficients):
            value = (k*value+c) % modulus
        if value:
            return False
    return True
