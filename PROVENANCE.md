# Provenance and scope

## Published challenge

JSP-001005 is currently published as:

> Can prime residue classes with bounded reciprocal sum of moduli still cover a long initial integer interval?

## Historical source

Erdős problem #1200: https://www.erdosproblems.com/1200

The maintained source formulation includes the restriction that the prime moduli satisfy `p_1 < ... < p_k < x`. The literal JSP wording does not state the upper bound `p_i < x`.

## Submitted result

The theorem `JSP001005.jsp_001005_literal` proves a uniform version of the literal wording with bound `C = 1` for every interval length `N ≥ 1`, using distinct prime moduli. The construction chooses all moduli above `N`, so it intentionally does not satisfy the omitted historical upper-bound condition.

This repository therefore must not be cited as a proof of the stronger historical Erdős #1200 problem.

## Prior-art audit note

Before this formalization was prepared, public searches found scoped/numerical JSP-001005 submissions and an Erdős #1200 statement stub, but not a complete Lean proof of this literal residue-cover construction. Priority and attribution remain subject to the Justin Sun Prize maintainers' normal review and public challenge process.
