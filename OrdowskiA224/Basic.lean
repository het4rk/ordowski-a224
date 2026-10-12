import OrdowskiA224.Count

/-!
# The even case and the prime direction
-/

namespace OeisA224

/-- Even case: no even n satisfies the congruence. -/
theorem even_case (n : ℕ) (hn : Even n) : ¬ n ^ 2 ≡ 1 [MOD a n * (a n - 1)] := by
  intro h
  have hev : 2 ∣ a n * (a n - 1) := by
    rcases Nat.even_or_odd (a n) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Dvd.dvd.mul_right ⟨r, by omega⟩ _
    · exact Dvd.dvd.mul_left ⟨r, by omega⟩ _
  have h2 : n ^ 2 ≡ 1 [MOD 2] := Nat.ModEq.of_dvd hev h
  obtain ⟨m, rfl⟩ := hn
  have : (m + m) ^ 2 % 2 = 0 := by
    rw [show (m+m)^2 = 2*(2*m*m) by ring]; simp
  unfold Nat.ModEq at h2; omega

lemma small_dvd (p : ℕ) (d : ℤ) (hd0 : d ≠ 0) (hd : |d| ≤ 3) (h : (p:ℤ) ∣ d) : p ≤ 3 := by
  have h1 : p ∣ d.natAbs := Int.natCast_dvd.mp h
  have h2 : d.natAbs ≤ 3 := by have := abs_le.mp hd; omega
  exact le_trans (Nat.le_of_dvd (by omega) h1) h2

/-- For an odd prime `p`, `a p = (p+1)/2`. -/
theorem a_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : a p = (p + 1) / 2 := by
  haveI := Fact.mk hp; haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [a_eq_aZ, aZ_prime p hp2]

/-- The "easy" direction: every odd prime satisfies the congruence. -/
theorem prime_direction (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ 2 ≡ 1 [MOD a p * (a p - 1)] := by
  rw [a_prime p hp hp2]
  obtain ⟨m, rfl⟩ : ∃ m, p = 2*m+1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact ⟨p/2, by omega⟩
  have h1 : (2*m+1+1)/2 = m+1 := by omega
  rw [h1, Nat.add_sub_cancel]
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))]
  exact ⟨4, by ring_nf; omega⟩

end OeisA224
