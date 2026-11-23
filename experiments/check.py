"""Finite arithmetic checks for Goldbach counts on progressions."""

from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, prod


def equal(actual, expected, description):
    if actual != expected:
        raise AssertionError(f"{description}: found {actual}, expected {expected}")


def is_prime_trial(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def prime_sieve(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            for multiple in range(p*p, limit + 1, p):
                flags[multiple] = 0
    return flags


def goldbach_counts():
    n = 50_050
    flags = prime_sieve(n)
    primes = [p for p in range(2, n + 1) if flags[p]]
    # Multiplication in base 256**width gives a carry-free convolution.
    width = (n.bit_length() + 7) // 8
    digits = bytearray((n + 1) * width)
    for p in range(2, n + 1):
        if is_prime_trial(p):
            digits[p*width] = 1
    polynomial = int.from_bytes(digits, "little")
    square = (polynomial**2).to_bytes((2*n + 1)*width, "little")

    checks = prime_checks = 0
    for k in range(24, 49):
        counts = []
        for i in range(1, 11):
            target = n - 4*k*i
            direct = sum(flags[target-p] for p in primes if p <= target)
            offset = target * width
            coefficient = int.from_bytes(square[offset:offset + width], "little")
            equal(direct, coefficient, f"R({target})")
            counts.append(direct)
        checks += len(counts)
        if is_prime_trial(k):
            prime_checks += len(counts)
        if k in (35, 37):
            print(f"R(50050 - 4*{k}*i), i=1..10: {' '.join(map(str, counts))}")
    print(f"Direct vs. polynomial counts: {checks} (including {prime_checks} with prime k)")


def local_moments():
    primes = (3, 5, 7, 11)
    period = prod(primes)
    units = [k for k in range(period) if gcd(k, period) == 1]
    # The second family has u_p = exp(tau / p), tau = period * log(2).
    weight_families = ([Fraction(p-1, p-2) for p in primes],
                       [2**(period//p) for p in primes])
    comparisons = 0
    for residue in (210, 242, 512):
        n = 2000*period + residue
        for i in range(1, 25):
            for weights in weight_families:
                values = [prod(u for p, u in zip(primes, weights) if (n - 4*i*k) % p == 0)
                          for k in range(period)]
                for unit_only in (False, True):
                    sample = units if unit_only else range(period)
                    measured = sum((values[k] for k in sample), Fraction(0)) / len(sample)
                    expected = Fraction(1)
                    for p, u in zip(primes, weights):
                        if i % p == 0:
                            hit = int(n % p == 0)
                        elif unit_only:
                            hit = Fraction(int(n % p != 0), p-1)
                        else:
                            hit = Fraction(1, p)
                        expected *= 1 + (u-1)*hit
                    equal(measured, expected, f"periodic moment {n=}, {i=}, {unit_only=}")
                    comparisons += 1
    print(f"Exact product moments: {comparisons} comparisons, period {period}, {len(units)} unit classes")


def congruence_checks():
    primes = (7, 11, 13, 17)
    period = prod(primes)
    w_modulus = 60
    index_limit = 2*period + 17
    checks = 0
    for n in (7*2**26, 2**29, period*2**16):
        for k in (19, 23, 25):
            h = w_modulus * k
            first = (n * pow(h, -1, period)) % period or period
            actual = [i for i in range(1, index_limit + 1)
                      if all((n-i*h) % p == 0 for p in primes)]
            equal(actual, list(range(first, index_limit + 1, period)), f"CRT {n=}, {k=}")
            checks += 1
    print(f"Simultaneous CRT classes: {checks} progressions checked through index {index_limit}")

    n = 7*2**26
    # An ordinary multiplier may share a factor with the period.
    equal(any((n-i*w_modulus*11) % 11 == 0 for i in range(1, period + 1)), False,
          "incompatible class for k=11")

    def bad_primes(k):
        return {p for p in primes if any((n-i*w_modulus*k) % p == 0 for i in (1, 2))}

    roots = [1 if n % p == 0 else 2 for p in primes]
    good = sum(not bad_primes(k) for k in range(period))
    equal(good, prod(p-r for p, r in zip(primes, roots)), "complete sieve period")
    print(f"Sieve roots at {primes}: {roots}; complete-period survivors {good}/{period}")

    start, length = 101, 2093
    events = [bad_primes(k) for k in range(start, start + length)]
    survivors = sum(not event for event in events)
    partial = length
    bounds = []
    for j in range(1, len(primes) + 1):
        intersections = sum(sum(all(p in event for p in subset) for event in events)
                            for subset in combinations(primes, j))
        partial += (-1)**j * intersections
        if (j % 2 == 1 and partial > survivors) or (j % 2 == 0 and partial < survivors):
            raise AssertionError(f"Bonferroni bounds at order {j}")
        bounds.append(partial)
    equal(partial, survivors, "complete inclusion-exclusion")
    print(f"Sieve on {length} consecutive k: successive bounds {bounds}; survivors {survivors}")


if __name__ == "__main__":
    goldbach_counts()
    local_moments()
    congruence_checks()
