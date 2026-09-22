import Mathlib

namespace JSP001005

/-- Pick a prime strictly larger than `n`. -/
noncomputable def primeAbove (n : ℕ) : ℕ :=
  Classical.choose (Nat.exists_infinite_primes (n + 1))

lemma primeAbove_spec (n : ℕ) : n < primeAbove n ∧ Nat.Prime (primeAbove n) := by
  have h := Classical.choose_spec (Nat.exists_infinite_primes (n + 1))
  have hle : n + 1 ≤ primeAbove n := by
    simpa [primeAbove] using h.1
  have hp : Nat.Prime (primeAbove n) := by
    simpa [primeAbove] using h.2
  exact ⟨by omega, hp⟩

/-- A strictly increasing sequence of primes, all larger than the starting bound `B`. -/
noncomputable def largePrime (B : ℕ) : ℕ → ℕ
  | 0 => primeAbove B
  | k + 1 => primeAbove (largePrime B k)

lemma largePrime_prime (B k : ℕ) : Nat.Prime (largePrime B k) := by
  cases k with
  | zero => exact (primeAbove_spec B).2
  | succ k => exact (primeAbove_spec (largePrime B k)).2

lemma largePrime_lt_succ (B k : ℕ) : largePrime B k < largePrime B (k + 1) := by
  exact (primeAbove_spec (largePrime B k)).1

lemma largePrime_strictMono (B : ℕ) : StrictMono (largePrime B) := by
  exact strictMono_nat_of_lt_succ (largePrime_lt_succ B)

lemma largePrime_gt_base (B k : ℕ) : B < largePrime B k := by
  cases k with
  | zero => exact (primeAbove_spec B).1
  | succ k => exact lt_trans (largePrime_gt_base B k) (largePrime_lt_succ B k)

/-- A finite family of prime residue classes covers the initial interval `1,...,N`.
The `i`th modulus is `p i` and its chosen residue is `a i`. -/
def CoversInitial (N : ℕ) (p a : Fin N → ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ N → ∃ i : Fin N, m % p i = a i % p i

/-- Robust literal reading of JSP-001005: one uniform reciprocal-sum bound works for
arbitrarily long initial intervals, using distinct prime moduli.  Deliberately absent is the
historical Erdős #1200 restriction that every modulus prime must itself be below the interval
endpoint. -/
def HasUniformPrimeResidueCover : Prop :=
  ∃ C : ℚ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    ∃ p a : Fin N → ℕ,
      Function.Injective p ∧
      (∀ i, Nat.Prime (p i)) ∧
      CoversInitial N p a ∧
      (∑ i : Fin N, (1 : ℚ) / (p i : ℚ)) ≤ C

/-- Complete solution of the literal published JSP-001005 wording, with the uniform bound
`C = 1`.  For an interval of length `N`, assign its `i`th integer its own distinct prime
modulus larger than `N`; the corresponding residue class covers that integer. -/
theorem jsp_001005_literal : HasUniformPrimeResidueCover := by
  refine ⟨1, by norm_num, ?_⟩
  intro N hN
  let p : Fin N → ℕ := fun i => largePrime N i.val
  let a : Fin N → ℕ := fun i => i.val + 1
  refine ⟨p, a, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact (largePrime_strictMono N).injective hij
  · intro i
    exact largePrime_prime N i.val
  · intro m hm1 hmN
    have hmN' : m - 1 < N := by omega
    let i : Fin N := ⟨m - 1, hmN'⟩
    refine ⟨i, ?_⟩
    have hmp : m < p i := by
      have hNp : N < p i := by
        exact largePrime_gt_base N i.val
      omega
    have hai : a i = m := by
      simp [a, i]
      omega
    simp [Nat.mod_eq_of_lt hmp, hai]
  · calc
      (∑ i : Fin N, (1 : ℚ) / (p i : ℚ))
          ≤ ∑ _i : Fin N, (1 : ℚ) / (N : ℚ) := by
              apply Finset.sum_le_sum
              intro i hi
              have hNpNat : N ≤ p i := (largePrime_gt_base N i.val).le
              have hNp : (N : ℚ) ≤ (p i : ℚ) := by exact_mod_cast hNpNat
              have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
              exact one_div_le_one_div_of_le hNpos hNp
      _ = (N : ℚ) * ((1 : ℚ) / (N : ℚ)) := by simp
      _ = 1 := by
        field_simp

end JSP001005
