# JSP-001005 literal published wording

This repository formalizes and proves a robust literal reading of the currently published Justin Sun Prize problem JSP-001005:

> Can prime residue classes with bounded reciprocal sum of moduli still cover a long initial integer interval?

The proof keeps a **uniform constant**, works for **every interval length `N ≥ 1`**, and uses **distinct prime moduli**. For the interval `1,...,N`, choose distinct primes `p_i > N` and the residue class `i mod p_i` for each `i = 1,...,N`. Each integer is covered by its corresponding class, and

`sum_i 1 / p_i ≤ N * (1 / N) = 1`.

Thus the literal published wording holds with the uniform constant `C = 1`.

## Scope distinction

This does **not** solve the stronger historical Erdős problem #1200. The maintained source formulation requires the modulus primes themselves to satisfy

`p_1 < ... < p_k < x`.

The published JSP-001005 wording omits the crucial upper bound `p_i < x`. The construction here deliberately uses primes larger than the interval endpoint, which is exactly what the historical condition forbids.

Source problem: https://www.erdosproblems.com/1200

## Lean theorem

Main theorem:

`JSP001005.jsp_001005_literal`

Source:

`JSP001005/Solution.lean`

The formal statement asserts the existence of a positive rational constant `C` such that for every `N ≥ 1` there are injectively indexed prime moduli and residues covering every integer `1 ≤ m ≤ N`, with reciprocal sum at most `C`.

## Reproduction

```bash
lake exe cache get
lake build
lake env lean JSP001005.lean
```

Toolchain: `leanprover/lean4:v4.33.0`

Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`

`JSP001005.lean` prints the axiom dependencies of the target theorem.

## Attribution

Literal mathematical construction and Lean formalization: `asdfdev0`.

No claim is made to solve Erdős #1200 or to have discovered the omission in the published JSP wording independently of prior public sources.
