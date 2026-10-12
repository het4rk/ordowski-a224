import OrdowskiA224.Basic
import OrdowskiA224.FiniteCheck

/-!
# The case n = p q
-/

namespace OeisA224

/-- Key reductions for n = p*q (p < q odd primes, but only p ≥ 3, q > p used here).
`s` is #squares mod pq, i.e. 4 s = (p+1)(q+1) (CRT multiplicativity + a(p) = (p+1)/2).
If s(s-1) ∣ (pq)^2 - 1, then p ≤ 61 and q + 1 ∣ 16(p^2 - 1). -/
theorem pq_reduction (p q s : ℤ) (hp : 3 ≤ p) (hpq : p < q)
    (hs : 4 * s = (p+1)*(q+1)) (hdvd : s * (s-1) ∣ (p*q)^2 - 1) :
    p ≤ 61 ∧ (q + 1) ∣ 16 * (p^2 - 1) := by
  obtain ⟨Q, hQ⟩ := hdvd
  set P := (p+1)*(q+1) with hP
  have key : Q * (P * (P - 4)) = 16 * ((p*q)^2 - 1) := by
    rw [hQ, ← hs]; ring
  constructor
  · have hPP : (p*q)^2 - 1 < P * (P - 4) := by rw [hP]; nlinarith [mul_pos (by linarith : (0:ℤ) < p) (by linarith : (0:ℤ) < q)]
    have h9 : 9 ≤ p*q := by nlinarith
    have hn : 0 < (p*q)^2 - 1 := by nlinarith
    have hpos : 0 < P * (P - 4) := by linarith
    have hQ16 : Q < 16 := by
      by_contra h; push Not at h
      nlinarith [mul_le_mul_of_nonneg_right h hpos.le]
    have hQ15 : Q * (P*(P-4)) ≤ 15 * (P*(P-4)) := mul_le_mul_of_nonneg_right (by omega) hpos.le
    have hlt : 16 * ((p*q)^2 - 1) < 15 * P^2 := by
      have : 0 < P := by rw [hP]; exact mul_pos (by linarith) (by linarith)
      nlinarith
    by_contra hbig; push Not at hbig
    have h62 : (62:ℤ) ≤ p := by omega
    have hq : p ≤ q := hpq.le
    have h1 : (q+1)*p ≤ (p+1)*q := by nlinarith
    have h2 : P * p ≤ (p+1)^2 * q := by rw [hP]; nlinarith
    have h3 : P^2 * p^2 ≤ (p+1)^4 * q^2 := by
      have h0 : 0 ≤ P * p := mul_nonneg (by rw [hP]; exact mul_nonneg (by linarith) (by linarith)) (by linarith)
      have := mul_le_mul h2 h2 h0 (mul_nonneg (sq_nonneg _) (by linarith))
      nlinarith
    have h4 : 15*(p+1)^4 ≤ 16*p^4 - 16 := by nlinarith [sq_nonneg (p-62), sq_nonneg p, mul_pos (by linarith : (0:ℤ) < p) (by linarith : (0:ℤ) < p)]
    have h5 : 15 * P^2 * p^2 ≤ 16 * p^2 * ((p*q)^2 - 1) := by
      have hq2 : p^2 ≤ q^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h4 (sq_nonneg q)]
    have hp2 : 0 < p^2 := by positivity
    nlinarith [mul_lt_mul_of_pos_right hlt hp2]
  · have h4 : (q+1) ∣ 4*s := ⟨p+1, by rw [hs]; ring⟩
    have hA : (q+1) ∣ 16 * ((p*q)^2 - 1) := by
      rw [← key]; exact ⟨(p+1)*Q*(P-4), by rw [hP]; ring⟩
    have hB : (q+1) ∣ 16 * p^2 * (q^2 - 1) := ⟨16*p^2*(q-1), by ring⟩
    have : 16 * (p^2 - 1) = 16 * ((p*q)^2 - 1) - 16 * p^2 * (q^2 - 1) := by ring
    rw [this]; exact dvd_sub hA hB

end OeisA224

namespace OeisA224

theorem pq_case (p q s : ℕ) (hpp : p.Prime) (hp3 : 3 ≤ p) (hpo : p % 2 = 1) (hqo : q % 2 = 1) (hpq : p < q)
    (hs : 4 * s = (p+1)*(q+1)) : ¬ s * (s-1) ∣ (p*q)^2 - 1 := by
  intro hd
  have hs1 : 1 ≤ s := by nlinarith
  have hdZ : (s:ℤ) * ((s:ℤ)-1) ∣ ((p:ℤ)*q)^2 - 1 := by
    have h1 : 1 ≤ (p*q)^2 := Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
    have := Int.natCast_dvd_natCast.mpr hd
    push_cast [Nat.cast_sub hs1, Nat.cast_sub h1] at this
    exact this
  obtain ⟨h61, hdiv⟩ := pq_reduction p q s (by exact_mod_cast hp3) (by exact_mod_cast hpq)
    (by exact_mod_cast hs) hdZ
  have h61' : p ≤ 61 := by exact_mod_cast h61
  have hp2 : 1 ≤ p^2 := Nat.one_le_pow _ _ (by omega)
  have hdivN : (q+1) ∣ 16*(p^2-1) := by
    have : ((q+1 : ℕ) : ℤ) ∣ ((16*(p^2-1) : ℕ) : ℤ) := by push_cast [Nat.cast_sub hp2]; exact hdiv
    exact_mod_cast this
  have h9 : 9 ≤ p^2 := by nlinarith
  have hle : q + 1 ≤ 16*(p^2-1) := Nat.le_of_dvd (by omega) hdivN
  have hok := finCheck_spec p (mem_primesTo61 p hpp hp3 h61') (q+1) (by omega)
  have hsdef : (p+1)*(q+1)/4 = s := by omega
  have := okPair_spec p (q+1) hok (Nat.mod_eq_zero_of_dvd hdivN) (by omega) (by omega)
  simp only [Nat.add_sub_cancel, hsdef] at this
  exact this (Nat.mod_eq_zero_of_dvd hd)


/-- Unconditional: for distinct odd primes p < q, n = p*q fails Ordowski's congruence. -/
theorem semiprime_case (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hpq : p < q) :
    ¬ (p*q) ^ 2 ≡ 1 [MOD a (p*q) * (a (p*q) - 1)] := by
  haveI := Fact.mk hp; haveI := Fact.mk hq
  haveI : NeZero p := ⟨hp.ne_zero⟩; haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hpo : p % 2 = 1 := by rcases hp.eq_two_or_odd with h | h; exact absurd h hp2; exact h
  have hqo : q % 2 = 1 := by rcases hq.eq_two_or_odd with h | h; exact absurd h hq2; exact h
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  have ha : a (p*q) = (p+1)/2 * ((q+1)/2) := by
    rw [a_eq_aZ, aZ_mul hcop, aZ_prime p hp2, aZ_prime q hq2]
  have hs : 4 * a (p*q) = (p+1)*(q+1) := by
    rw [ha]; obtain ⟨i, hi⟩ : 2 ∣ p+1 := by omega
    obtain ⟨j, hj⟩ : 2 ∣ q+1 := by omega
    rw [hi, hj]; simp; ring
  intro h
  have h1 : 1 ≤ (p*q)^2 := Nat.one_le_pow _ _ (Nat.mul_pos hp.pos hq.pos)
  exact pq_case p q _ hp (by have := hp.two_le; omega) hpo hqo hpq hs
    ((Nat.modEq_iff_dvd' h1).mp h.symm)



end OeisA224
