"""Exact integer audit for the 2,363,958 prime-subset reflection example."""

from collections import Counter
from math import isqrt


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def differences(points):
    return Counter(p - q for p in points for q in points)


def representations(points, target):
    return sorted((p, target - p) for p in points if p <= target - p in points)


def main():
    anchors = (1075141, 1271183, 1288607)
    step = 210
    offsets = (0, 1, 5, 6, 8)
    reflected = tuple(8 - t for t in offsets)
    a = {u + step * t for u in anchors for t in offsets}
    b = {u + step * t for u in anchors for t in reflected}
    n = min(anchors) + max(anchors) + step

    assert n == 2363958 and len(a) == len(b) == 15
    assert all(is_prime(p) and n <= 3 * p <= 2 * n for p in a | b)
    assert min(a) == min(b) and max(a) == max(b)
    assert a != b and {min(a) + max(a) - p for p in a} != b
    assert differences(a) == differences(b)
    for q in range(1, 8):
        assert Counter(p % q for p in a) == Counter(p % q for p in b)
    for degree in range(3):
        assert sum(p**degree for p in a) == sum(p**degree for p in b)
    assert representations(a, n) == [(1075141, 1288817), (1075351, 1288607)]
    assert representations(b, n) == []
    print(f"N={n}, |A|=|B|={len(a)}, distinct primes={len(a | b)}")
    print(f"ordered pairs per difference table={len(a)**2}, shifts={len(differences(a))}")
    print(f"A representations={representations(a, n)}, B representations=[]")
    print("moments 0..2, moduli 1..7, endpoints and noncongruence verified")


if __name__ == "__main__":
    main()
