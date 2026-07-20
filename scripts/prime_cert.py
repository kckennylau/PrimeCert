#!/usr/bin/env python3
"""Generate prime_cert% Lean 4 certificates using pock3 (cube-root Pocklington).

Usage:
    # Auto-factor N-1 (for small-to-medium primes):
    python3 scripts/prime_cert.py 16290860017

    # Supply factorisation of N-1 (for large primes, use alpertron.com.ar/ECM.HTM):
    python3 scripts/prime_cert.py 16290860017 '2^4 * 3 * 339392917'

For small primes, N-1 is factored automatically using sympy (via uv), GNU
coreutils factor, or built-in trial division + Pollard rho. For large primes,
supply the complete factorisation of N-1 as a second argument.
"""
import math, random, re, shutil, subprocess, sys

SMALL = 3000  # SmallPrimes.lean covers primes up to 3000
ALPERTRON = "https://www.alpertron.com.ar/ECM.HTM"

# -- Primality testing --

def is_prime(n):
    """Deterministic Miller-Rabin, correct for all n < 3.3 × 10^24.
    Only used internally on small numbers (QNR witnesses, rho cofactors)."""
    if n < 2: return False
    if n in (2, 3, 5, 7, 11, 13): return True
    if any(n % p == 0 for p in (2, 3, 5, 7, 11, 13)): return False
    d, r = n - 1, 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if a >= n: continue
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1: break
        else: return False
    return True

# -- Factoring backends --

def _sympy_factor(n):
    """Factor via sympy (uses ECM for large numbers)."""
    out = subprocess.check_output(
        ["uv", "run", "--with", "sympy", "python3", "-c",
         f"from sympy import factorint; print(factorint({n}))"],
        text=True, timeout=300)
    return eval(out.strip())

def _gnu_factor(n):
    """Factor via GNU coreutils `factor`."""
    out = subprocess.check_output(["factor", str(n)], text=True, timeout=60)
    fs = {}
    for p in out.split(":")[1].split():
        p = int(p); fs[p] = fs.get(p, 0) + 1
    return fs

def _rho(n):
    """Brent-Pollard rho. Practical for factors up to ~14 digits."""
    if n % 2 == 0: return 2
    for _ in range(50):
        y = c = random.randrange(1, n)
        m = random.randrange(1, n)
        g = q = r = 1
        while g == 1:
            x = y
            for _ in range(r): y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n)
                k += m
            r <<= 1
        if g == n:
            while True:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
                if g > 1: break
        if g != n: return g
    return None

def _py_factor(n):
    """Trial division + Pollard rho. Pure Python fallback."""
    fs = {}
    for p in (2, 3, 5):
        while n % p == 0: fs[p] = fs.get(p, 0) + 1; n //= p
    p = 7
    while p <= 10**6 and p * p <= n:
        for q in (p, p + 4):
            while n % q == 0: fs[q] = fs.get(q, 0) + 1; n //= q
        p += 6
    if n <= 1: return fs
    if is_prime(n): fs[n] = 1; return fs
    stack = [n]
    while stack:
        m = stack.pop()
        if m <= 1: continue
        if is_prime(m): fs[m] = fs.get(m, 0) + 1; continue
        d = _rho(m)
        if d is None:
            raise ValueError(
                f"Cannot factor {m} ({len(str(m))} digits) with built-in methods.\n"
                f"Either install uv (https://docs.astral.sh/uv/), or supply the\n"
                f"factorisation of N-1 as a second argument.\n"
                f"Use {ALPERTRON} to factor large numbers.")
        stack.extend([d, m // d])
    return fs

# Detect available backends once at import time
_HAS_UV = shutil.which("uv") is not None
_HAS_GNU_FACTOR = shutil.which("factor") is not None

def factor(n):
    """Factor n using the best available method."""
    if _HAS_UV:
        try: return _sympy_factor(n)
        except (subprocess.TimeoutExpired, subprocess.CalledProcessError): pass
    if _HAS_GNU_FACTOR:
        try: return _gnu_factor(n)
        except (subprocess.TimeoutExpired, subprocess.CalledProcessError): pass
    return _py_factor(n)

def parse_factorisation(s):
    """Parse '2^4 * 3 * 29' or '2^4 3 29'. Returns {prime: exponent}."""
    fs = {}
    for m in re.finditer(r'(\d+)(?:\^(\d+))?', s):
        p, e = int(m[1]), int(m[2] or 1); fs[p] = fs.get(p, 0) + e
    return fs

# -- Certificate generation --

def certify(N, nm1_factors=None, pool=None):
    """Return a prime_cert% Lean term certifying N is prime.

    `pool` is an optional `{prime: {factor: exponent}}` map of *already-proven* factorisations
    of `prime - 1`, consulted at every level of the recursion. This lets a certificate be
    rebuilt from an existing ladder without re-factoring any large `p - 1` (only enough of each
    `p - 1` to build the cube-root `F` is needed)."""
    smalls, steps, done = set(), [], set()
    pool = pool or {}

    def go(p):
        if p <= SMALL: smalls.add(p); return
        if p in done: return
        done.add(p)

        fs = (dict(pool[p]) if p in pool
              else dict(nm1_factors) if (p == N and nm1_factors)
              else factor(p - 1))
        e = fs.pop(2, 0)

        # Select smallest odd factors until F > p^(1/3)
        F, target = 1 << e, int(p ** (1/3)) + 2
        while (target + 1) ** 3 <= p: target += 1
        sel = []
        for q in sorted(fs):
            sel.append((q, fs[q])); F *= q ** fs[q]
            if F > target: break

        R = (p - 1) // F
        twoF = 2 * F
        r, s = R % twoF, R // twoF

        m = 1
        while 2*s + m*m >= (twoF + r)*m + 2: m += 1

        if s == 0: mode = "0"
        elif r*r < 8*s: mode = "<"
        else:
            v = r*r - 8*s
            for w in range(3, 10000, 2):
                if is_prime(w) and pow(v, (w-1)//2, w) == w - 1:
                    smalls.add(w); mode = str(w); break
            else: raise ValueError(f"no QNR witness for r={r}, s={s}")

        for q, _ in sel: go(q)
        exps = [(p - 1) // q for q in [2] + [q for q, _ in sel]]
        for a in range(2, 10000):
            if all(math.gcd(pow(a, ex, p) - 1, p) == 1 for ex in exps):
                break
        else: raise ValueError(f"no root for {p}")

        def pp(b, e): return str(b) if e == 1 else f"{b} ^ {e}"
        f = " * ".join(pp(q, x) for q, x in [(2, e)] + sel)
        steps.append(f"pock3 ({p}, {a}, {m}, {mode}, {f})")

    go(N)
    ss = "; ".join(str(s) for s in sorted(smalls))
    body = ",\n   ".join([f"small {{{ss}}}"] + steps)
    return f"theorem prime_{N} : Nat.Prime {N} := prime_cert%\n  [{body}]"

def load_pool(path):
    """Load a factor pool. Each line is `prime: factorisation` (e.g.
    `339392917: 2^2 * 3^4 * 29`); blank lines and `#` comments are ignored. The factorisation
    need only cover enough of `prime - 1` to build a cube-root `F`."""
    pool = {}
    with open(path) as fh:
        for line in fh:
            line = line.split("#", 1)[0].strip()
            if not line: continue
            p, fac = line.split(":", 1)
            pool[int(p)] = parse_factorisation(fac)
    return pool

if __name__ == "__main__":
    pos = [a for a in sys.argv[1:] if not a.startswith("--")]
    pool_path = next((a.split("=", 1)[1] for a in sys.argv[1:] if a.startswith("--pool=")), None)
    if not pos: print(__doc__); sys.exit(1)
    N = int(pos[0])
    pool = load_pool(pool_path) if pool_path else None
    fs = parse_factorisation(pos[1]) if len(pos) >= 2 else None
    if fs: assert math.prod(p**e for p, e in fs.items()) == N - 1, \
        f"factorisation product doesn't match N-1 = {N-1}"
    print(certify(N, fs, pool))
