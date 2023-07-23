# SIPP

https://eprint.iacr.org/2019/1177.pdf

The objective of SIPP is to efficiently compute the pairing $\vec{A}*\vec{B} := \prod_i e(A_i, B_i)$ of $\vec{A} \in \mathbb{G}_1^n$, $\vec{B} \in \mathbb{G}_2^n$.

## Procedure

1. The Prover computes $Z = \vec{A}*\vec{B}$ and passes it to the Verifier.

The Prover and Verifier repeat the following steps

1. The Prover calculates $Z_L = A_{[n/2:]} * B_{[:n/2]}$, $Z_R = A_{[:n/2]} * B_{[n/2:]}$ and passes them to the Verifier.
2. The Verifier randomly samples $x \in \mathbb{F}_r$ and passes it to the Prover.
3. Both the Verifier and Prover compute $A' = A_{[:n/2]} + x A_{[n/2:]}$, $B' = B_{[:n/2]} + x^{-1} B_{[n/2:]}$
4. The Verifier computes $Z' = Z_L^x Z Z_R^{x^{-1}}$
5. Update $\vec{A}\leftarrow \vec{A}', \vec{B}\leftarrow \vec{B}', Z \leftarrow Z', n \leftarrow n/2$

When $n = 1$, the Verifier checks if $e(A, B) \overset{?}{=} Z$, and accepts if this is the case.

## SIPP in SNARK

In this repository, I've implemented a plonky2 circuit for verifying the SIPP proof. The final pairing is merely included in the public inputs rather than being directly proven within the plonky2 circuit, due to the high cost of direct verification by plonky2.

Operations such as G1, G1 scalar multiplication, and Fq12 exponentiation have been implemented using starky. Their respective proofs are then recursively verified within the plonky2 circuit.

## test

`cargo test test_sipp_circuit -r -- --nocapture`

A result on M1MacBookPro(2021)

```
Aggregating 128 pairings into 1
Start: cirucit build
End: circuit build. took 35.545641375s
Start: proof generation
End: proof generation. took 145.043526708s
```

It took about 150secs for 128 pairing aggregation (without circuit build time).
