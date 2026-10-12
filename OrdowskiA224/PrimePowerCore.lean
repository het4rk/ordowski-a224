import OrdowskiA224.Basic

/-!
# Prime-power arithmetic core (NOT tied to `a`)

These lemmas are unconditional statements about an integer `s` satisfying Stangl's closed
form for the number of squares modulo `p^k`. The identification `a (p^k) = s` (Stangl 1996)
is **not** formalized here, so these lemmas do not by themselves settle the prime-power case of
the conjecture.
-/

namespace OeisA224

/-- Prime-power core, even exponent: `s` with `2(p+1) s = p^(k+1) + p + 2`
(Stangl's closed form for the number of squares mod p^k, k even). -/
theorem pp_even (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) (s : ℤ)
    (hs : 2 * ((p:ℤ) + 1) * s = (p:ℤ) ^ (k+1) + p + 2) :
    ¬ s * (s - 1) ∣ (p:ℤ) ^ (2*k) - 1 := by
  rintro ⟨Q, hQ⟩
  set X : ℤ := (p:ℤ)^k with hX
  have hX2 : (p:ℤ)^(2*k) = X^2 := by rw [hX, ← pow_mul, mul_comm]
  have hpk : (p:ℤ)^(k+1) = p * X := by rw [hX, pow_succ, mul_comm]
  have e1 : 2*((p:ℤ)+1)*s = p*X+p+2 := by rw [hs, hpk]
  have hQ' : X^2 - 1 = s*(s-1)*Q := by rw [← hX2]; exact hQ
  have key : Q * (p*X + p + 2) * (p * (X - 1)) = 4 * ((p:ℤ)+1)^2 * (X^2 - 1) := by
    linear_combination (-Q*((p*X+p+2) + 2*((p:ℤ)+1)*s - 2*((p:ℤ)+1))) * e1 + (-(2*((p:ℤ)+1))^2) * hQ'
  have hpZ : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hd : (p:ℤ) ∣ 4 * ((p:ℤ)+1)^2 * (X^2 - 1) :=
    ⟨Q * (p*X+p+2) * (X-1), by rw [← key]; ring⟩
  have hpX : (p:ℤ) ∣ X := by rw [hX]; exact dvd_pow_self _ (by omega)
  rcases hpZ.dvd_or_dvd hd with h | h
  · rcases hpZ.dvd_or_dvd h with h | h
    · have h4 : p ∣ 4 := by exact_mod_cast h
      have : p ≤ 4 := Nat.le_of_dvd (by norm_num) h4
      have h2 := hp.two_le
      interval_cases p <;> first | omega | (norm_num at hp)
    · have h1 := hpZ.dvd_of_dvd_pow h
      have : (p:ℤ) ∣ 1 := by simpa using (dvd_sub h1 (dvd_refl (p:ℤ)))
      exact hpZ.not_dvd_one this
  · have : (p:ℤ) ∣ X^2 := dvd_pow hpX two_ne_zero
    have : (p:ℤ) ∣ 1 := by simpa using dvd_sub this h
    exact hpZ.not_dvd_one this

/-- Prime-power core, odd exponent ≥ 2 (used for k ≥ 3): `2(p+1) s = p^(k+1) + 2p + 1`. -/
theorem pp_odd (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) (s : ℤ)
    (hs : 2 * ((p:ℤ) + 1) * s = (p:ℤ) ^ (k+1) + 2*p + 1) :
    ¬ s * (s - 1) ∣ (p:ℤ) ^ (2*k) - 1 := by
  rintro ⟨Q, hQ⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp3' : (3:ℤ) ≤ p := by exact_mod_cast hp3
  set Y : ℤ := (p:ℤ)^(k-1) with hY
  set X : ℤ := (p:ℤ)^k with hX
  have hXY : X = p * Y := by
    rw [hX, hY, ← pow_succ']; congr 1; omega
  have hX2 : (p:ℤ)^(2*k) = X^2 := by rw [hX, ← pow_mul, mul_comm]
  have hpk : (p:ℤ)^(k+1) = p * X := by rw [hX, pow_succ, mul_comm]
  have hXbig : (p:ℤ)^2 ≤ X := by
    rw [hX]; exact pow_le_pow_right₀ (by linarith) hk
  clear_value X Y
  have e1 : 2*((p:ℤ)+1)*s = p*X+2*p+1 := by rw [hs, hpk]
  have key : Q * (p*X + 2*p + 1) * (p*X - 1) = 4 * ((p:ℤ)+1)^2 * (X^2 - 1) := by
    have hQ' : X^2 - 1 = s*(s-1)*Q := by rw [← hX2]; exact hQ
    linear_combination (-Q*((p*X+2*p+1) + 2*((p:ℤ)+1)*s - 2*((p:ℤ)+1))) * e1 + (-(2*((p:ℤ)+1))^2) * hQ'
  have hX9 : (9:ℤ) ≤ X := by nlinarith
  have hA : 0 < ((p:ℤ)*X + 2*p + 1) * (p*X - 1) := by
    apply mul_pos <;> nlinarith
  have hR : 0 < 4 * ((p:ℤ)+1)^2 * (X^2 - 1) := by
    apply mul_pos; positivity; nlinarith
  have hQpos : 0 < Q := by
    by_contra hneg; push Not at hneg
    have : Q * (((p:ℤ)*X + 2*p + 1) * (p*X - 1)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg hA.le
    nlinarith
  have hQlt : Q < 8 := by
    by_contra hge; push Not at hge
    have h8 : 8 * (((p:ℤ)*X + 2*p + 1) * (p*X - 1)) ≤ Q * (((p:ℤ)*X + 2*p + 1) * (p*X - 1)) :=
      mul_le_mul_of_nonneg_right hge hA.le
    have hpX : (3:ℤ)*X ≤ p*X := by nlinarith
    nlinarith [mul_le_mul hpX hpX (by linarith) (by nlinarith)]
  have hdiv : (p:ℤ) ∣ Q - 4 := by
    refine ⟨Q*(p*X^2+2*p*X-2) - (4*(p+2)*(X^2-1) + 4*p*Y^2), ?_⟩
    have : X^2 = p*(p*Y^2) := by rw [hXY]; ring
    linear_combination (-1:ℤ) * key - 4 * this
  interval_cases Q
  · -- Q = 1 : p ∣ -3 → p = 3
    have := small_dvd p (1-4) (by norm_num) (by norm_num) hdiv
    nlinarith
  · have := small_dvd p (2-4) (by norm_num) (by norm_num) hdiv
    have : p ≤ 2 := by
      have h1 : p ∣ (2-4:ℤ).natAbs := Int.natCast_dvd.mp hdiv
      exact Nat.le_of_dvd (by norm_num) h1
    omega
  · have h1 : p ∣ (3-4:ℤ).natAbs := Int.natCast_dvd.mp hdiv
    have := Nat.le_of_dvd (by norm_num) h1; omega
  · -- Q = 4
    nlinarith
  · have h1 : p ∣ (5-4:ℤ).natAbs := Int.natCast_dvd.mp hdiv
    have := Nat.le_of_dvd (by norm_num) h1; omega
  · have h1 : p ∣ (6-4:ℤ).natAbs := Int.natCast_dvd.mp hdiv
    have := Nat.le_of_dvd (by norm_num) h1; omega
  · -- Q = 7 : p = 3
    have h3 := small_dvd p (7-4) (by norm_num) (by norm_num) hdiv
    have hp' : p = 3 := by omega
    subst hp'
    push_cast at key
    rcases le_or_gt X 126 with h | h <;> nlinarith

end OeisA224
