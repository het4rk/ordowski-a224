import OrdowskiA224.Semiprime
import OrdowskiA224.PrimePower

/-!
# Main theorem

Ordowski's conjecture (OEIS A000224; formal-conjectures `OeisA224.conjecture`) holds for every
`n > 1` that is even, prime, or a product of two distinct odd primes.
-/

namespace OeisA224

theorem conjecture_of_even_or_prime_or_semiprime (n : ℕ) (hn : 1 < n)
    (hcase : Even n ∨ n.Prime ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ p ≠ q ∧ n = p * q) :
    (n.Prime ∧ n ≠ 2) ↔ n ^ 2 ≡ 1 [MOD a n * (a n - 1)] := by
  rcases hcase with he | hp | ⟨p, q, hp, hq, hp2, hq2, hpq, rfl⟩
  · constructor
    · rintro ⟨hpr, hne⟩
      rcases hpr.eq_two_or_odd with h | h
      · exact absurd h hne
      · obtain ⟨k, hk⟩ := he; omega
    · intro h; exact absurd h (even_case n he)
  · by_cases h2 : n = 2
    · subst h2; constructor
      · rintro ⟨-, h⟩; exact absurd rfl h
      · intro h; exact absurd h (even_case 2 even_two)
    · exact ⟨fun _ => prime_direction n hp h2, fun _ => ⟨hp, h2⟩⟩
  · constructor
    · rintro ⟨hpr, -⟩
      exact absurd hpr (Nat.not_prime_mul hp.ne_one hq.ne_one)
    · intro h
      rcases lt_or_gt_of_ne hpq with hlt | hlt
      · exact absurd h (semiprime_case p q hp hq hp2 hlt)
      · have h' := semiprime_case q p hq hp hq2 hlt
        rw [mul_comm q p] at h'
        exact absurd h h'

/-- Main theorem: the conjecture holds for every `n > 1` that is even, an odd prime power
(including primes), or a product of two distinct odd primes. -/
theorem conjecture_main (n : ℕ) (hn : 1 < n)
    (hcase : Even n ∨ (∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p ^ k) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ p ≠ q ∧ n = p * q) :
    (n.Prime ∧ n ≠ 2) ↔ n ^ 2 ≡ 1 [MOD a n * (a n - 1)] := by
  rcases hcase with he | ⟨p, k, hp, hk, rfl⟩ | hpq
  · exact conjecture_of_even_or_prime_or_semiprime _ hn (Or.inl he)
  · by_cases hk1 : k = 1
    · subst hk1; rw [pow_one] at hn ⊢
      exact conjecture_of_even_or_prime_or_semiprime _ hn (Or.inr (Or.inl hp))
    · by_cases hp2 : p = 2
      · subst hp2
        exact conjecture_of_even_or_prime_or_semiprime _ hn
          (Or.inl ((Nat.even_pow' (by omega)).mpr even_two))
      · constructor
        · rintro ⟨hpr, -⟩
          have hlt : p ^ 1 < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
          rcases hpr.eq_one_or_self_of_dvd p (dvd_pow_self p (by omega)) with h | h
          · exact absurd h hp.ne_one
          · rw [pow_one] at hlt; exact absurd h (by omega)
        · intro h; exact absurd h (prime_power_case p k hp hp2 (by omega))
  · exact conjecture_of_even_or_prime_or_semiprime _ hn (Or.inr (Or.inr hpq))

end OeisA224
