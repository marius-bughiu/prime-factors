# Two certified primes below 2¹⁰²⁴

The Lean kernel checked `Nat.Prime (2^1024 - 105)` and `Nat.Prime (2^1024 - 179)`. These two fixed primes supply concrete endpoints for the factor research. Their certificates establish primality for those specific integers.

## Replay the proofs

Start at the root of `prime-factors` with Git, Python 3.8 or later, and Elan available. The commands create a separate checkout under `build/`. Its pinned toolchain is Lean 4.35.0-rc3. The main package uses Lean 4.19.

```sh
inputs="$PWD/research/endpoint-ecpp"
verifier="$PWD/build/endpoint-ecpp-theory"
mkdir -p build
git clone https://github.com/leanprover/hex-ecpp-theory.git "$verifier"
git -C "$verifier" checkout --detach 2911ff9bb39ce993181c03d4c035279744d700bf
python3 "$inputs/generate.py" "$verifier"
cd "$verifier"
elan toolchain install leanprover/lean4:v4.35.0-rc3
lake exe cache get
lake build HexECPPTheory.Soundness
lake env lean -j 1 -s 262144 -o Endpoint105.olean Endpoint105.lean
lake env lean -j 1 -s 262144 -o Endpoint179.olean Endpoint179.lean
```

Each file ends with a Lean axiom audit. Both commands should exit successfully and print the following lines, respectively.

```text
'endpointPrime105' depends on axioms: [propext, Classical.choice, Quot.sound]
'endpointPrime179' depends on axioms: [propext, Classical.choice, Quot.sound]
```

| Offset | ECPP steps | Modular inverses for the order checks | SHA-256 of generated Lean source |
| ---: | ---: | ---: | --- |
| 105 | 41 | 34,950 | `c251b1958469ec7c179d6971ae80921d3eff8f9404e7849cf465259055c5951f` |
| 179 | 43 | 33,314 | `1356eee72037b259ede1468d9d20bfd2341c8b3dbd748cf830b34d569d5a6969` |

With the verifier already built, the two proof files took 90.1 seconds and 86.8 seconds to check in one concurrent run on an Apple Silicon Mac. These times measure primality verification for the two supplied witnesses.

The Python generator uses only the standard library. Each PARI row supplies a modulus `n`, trace `t`, cofactor `s`, curve coefficient `a`, and affine point `P`. The generator recovers the other curve coefficient, sets `q = (n + 1 - t) / s`, computes the point `Q = sP`, and writes witnesses for each division in the binary multiplication `qQ`. The upstream Lean checker verifies the curve and its nonsingularity, checks the point, the divisions and `qQ = O`, and enforces its size bound on `q`. The next row supplies a proof of `Nat.Prime q`. A literal recursive Pocklington certificate closes each chain. The terminal primes are 90,941,182,547,304,469 and 11,591,317,473,247, respectively. [Upstream soundness theorem](https://github.com/leanprover/hex-ecpp-theory/blob/2911ff9bb39ce993181c03d4c035279744d700bf/HexECPPTheory/Soundness.lean)

The pinned project's `ecpp using` tactic has a 512-bit input limit. Each generated row applies the unrestricted upstream theorem `Hex.ECPP.natPrime_of_step` directly. Lean kernel reduction verifies the arithmetic premise with `rfl`. This uses the published verifier and its original mathematical checks. [Upstream tactic](https://github.com/leanprover/hex-ecpp-theory/blob/2911ff9bb39ce993181c03d4c035279744d700bf/HexECPPTheory/Elab.lean)

## Reproduce the PARI check

The two archived matrices contain numerical witness data generated with PARI/GP 2.19.1, with seed 1 for each input. At an interactive GP prompt, run the following two lines. The triples give the offset, whether the first row's subject equals the requested integer, and the result of verifying the certificate.

```gp
default(parisizemax,512000000)
for(i=1,2,d=[105,179][i];n=2^1024-d;setrand(1);c=primecert(n);print([d,c[1][1]==n,primecertisvalid(c)]))
```

The output is `[105, 1, 1]` and `[179, 1, 1]`. [PARI certificate format and verifier](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Arithmetic_functions.html#primecert)

The original Python generator uses this repository's MIT license. The externally fetched HexECPPTheory library uses Apache-2.0. PARI/GP uses GPL-2.0-or-later. [Repository license](../../LICENSE) · [HexECPPTheory license](https://github.com/leanprover/hex-ecpp-theory/blob/2911ff9bb39ce993181c03d4c035279744d700bf/LICENSE) · [PARI/GP distributions](https://pari.math.u-bordeaux.fr/download.html)
