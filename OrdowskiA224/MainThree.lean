import OrdowskiA224.Main
import OrdowskiA224.ThreePrimes

/-!
# Main theorem, extended to products of three distinct odd primes
-/

namespace OeisA224

/-- `three_primes_case` without an ordering assumption. -/
theorem three_primes_case' (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hr2 : r ≠ 2) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ (p*q*r) ^ 2 ≡ 1 [MOD a (p*q*r) * (a (p*q*r) - 1)] := by
  rcases Nat.lt_or_gt_of_ne hpq with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hpr with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hqr with h3 | h3
  · exact three_primes_case p q r hp hq hr hp2 h1 h3
  · rw [show p*q*r = p*r*q by ring]; exact three_primes_case p r q hp hr hq hp2 h2 h3
  · omega
  · rw [show p*q*r = r*p*q by ring]; exact three_primes_case r p q hr hp hq hr2 h2 h1
  · rw [show p*q*r = q*p*r by ring]; exact three_primes_case q p r hq hp hr hq2 h1 h2
  · omega
  · rw [show p*q*r = q*r*p by ring]; exact three_primes_case q r p hq hr hp hq2 h3 h2
  · rw [show p*q*r = r*q*p by ring]; exact three_primes_case r q p hr hq hp hr2 h3 h1

/-- Main theorem (extended): Ordowski's conjecture holds for every `n > 1` that is even, an odd
prime power (including primes), a product of two distinct odd primes, or a product of three
distinct odd primes. -/
theorem conjecture_main_three (n : ℕ) (hn : 1 < n)
    (hcase : Even n ∨ (∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p ^ k) ∨
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ p ≠ q ∧ n = p * q) ∨
      ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ r ≠ 2 ∧
        p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p * q * r) :
    (n.Prime ∧ n ≠ 2) ↔ n ^ 2 ≡ 1 [MOD a n * (a n - 1)] := by
  rcases hcase with h | h | h | ⟨p, q, r, hp, hq, hr, hp2, hq2, hr2, hpq, hpr, hqr, rfl⟩
  · exact conjecture_main n hn (Or.inl h)
  · exact conjecture_main n hn (Or.inr (Or.inl h))
  · exact conjecture_main n hn (Or.inr (Or.inr h))
  · constructor
    · rintro ⟨hpr', -⟩
      exact absurd hpr' (Nat.not_prime_mul (Nat.mul_ne_zero hp.ne_zero hq.ne_zero |> fun _ =>
        by have := hp.two_le; have := hq.two_le; nlinarith) hr.ne_one)
    · intro h; exact absurd h (three_primes_case' p q r hp hq hr hp2 hq2 hr2 hpq hpr hqr)

end OeisA224
