# SIPP

https://eprint.iacr.org/2019/1177.pdf

The objective of SIPP is to efficiently compute the pairing $\vec{A}*\vec{B} := \prod_i e(A_i, B_i)$ of $\vec{A} \in \mathbb{G}_1^n$, $\vec{B} \in \mathbb{G}_2^n$.

## Procedure

1. The Prover computes $Z = \vec{A}*\vec{B}$ and passes it to the Verifier.

The Prover and Verifier repeat the following steps

1. The Prover calculates $Z_L = A_{[n/2:]} * B_{[:n/2]}$, $Z_R = \vec{A}_{:n/2} * \vec{B}_{n/2:}$ and passes them to the Verifier.
2. The Verifier randomly samples $x \in \mathbb{F}_r$ and passes it to the Prover.
3. Both the Verifier and Prover compute $\vec{A}' = \vec{A}_{[:n/2]} + x \vec{A}_{[n/2:]}, \vec{B}' = \vec{B}_{[:n/2]} + x^{-1} \vec{B}_{[n/2:]}$
4. The Verifier computes $Z' = Z_L^x Z Z_R^{x^{-1}}$
5. Update $\vec{A}\leftarrow \vec{A}', \vec{B}\leftarrow \vec{B}', Z \leftarrow Z', n \leftarrow n/2$

When $n = 1$, the Verifier checks if $e(A, B) \overset{?}{=} Z$, and accepts if this is the case.
