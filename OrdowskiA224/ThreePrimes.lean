import OrdowskiA224.Semiprime
import OrdowskiA224.FiniteCheck3

/-!
# The case `n = p q r`, three distinct odd primes

Let `s = a(n) = (p+1)(q+1)(r+1)/8` and `P = 8 s`. If `s(s-1) ∣ n² - 1`, write
`n² - 1 = Q s (s-1)`; then `1 ≤ Q ≤ 63` and `Q P (P - 8) = 64 (n² - 1)`.
A size argument gives `p ≤ 400`. Viewing the identity as a quadratic in `r`,
`c₂ r² = c₁ r + c₀` with `c₁, c₀ > 0`, forces `c₂ > 0`, which forces
`d := 64 p² - Q (p+1)² > 0` and `d q < 6 Q (p+1)²` (for `q ≥ 8`). The remaining finitely many
`(p, Q, q)` are checked by the kernel (`finCheck3_true`).
-/

namespace OeisA224

/-! ### Specification of the finite check -/

theorem rootFree_spec (q a b e r : ℕ) (h : rootFree q a b e = true) (ha : 0 < a) (he : 0 < e)
    (hr : a * r ^ 2 = b * r + e) : r ≤ q := by
  unfold rootFree at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  generalize nsqrt 200 (b*b + 4*a*e) (b + 2*a*e/(b+1) + 1) = c at h
  rcases h with h0 | ⟨⟨h1, h2⟩, h3⟩
  · omega
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hr; omega
    · exact h
  have hbr : b < 2 * a * r := by
    have : b * r < a * r * r := by nlinarith
    have : b < a * r := Nat.lt_of_mul_lt_mul_right (a := r) (by linarith)
    nlinarith
  have ht : (2*a*r - b) * (2*a*r - b) = b*b + 4*a*e := by
    zify [hbr.le]
    have hrz : (a:ℤ) * r^2 = b * r + e := by exact_mod_cast hr
    linear_combination 4 * (a:ℤ) * hrz
  have hct : c = 2*a*r - b := by
    rw [← ht] at h1 h2
    have := Nat.mul_self_le_mul_self_iff.mp h1
    have := Nat.mul_self_lt_mul_self_iff.mp h2
    omega
  have hbc : b + c = 2 * a * r := by omega
  rw [hbc, ← ht, hct, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by omega)] at h3
  simpa using h3

theorem finCheck3_spec (p Q q : ℕ) (hp : p ∈ primesTo400) (hQ : Q < 64)
    (hd : Q*(p+1)^2 < 64*p^2) (hq : q ≤ qmax p Q) : okTriple p Q q = true := by
  have hc := finCheck3_true
  unfold finCheck3 at hc
  rw [List.all_eq_true] at hc
  have h := hc p hp
  rw [List.all_eq_true] at h
  have h := h Q (List.mem_range.mpr hQ)
  unfold okPQ at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · rw [List.all_eq_true] at h
    exact h q (List.mem_range.mpr (by omega))

theorem mem_primesTo400 (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) (h400 : p ≤ 400) :
    p ∈ primesTo400 := by
  interval_cases p <;> first | decide | (norm_num at hp)

/-! ### The algebra over `ℤ` -/

theorem pqr_Q (p q r s : ℤ) (hp : 3 ≤ p) (hpq : p < q) (hqr : q < r)
    (hs : 8 * s = (p+1)*(q+1)*(r+1)) (hd : s * (s-1) ∣ (p*q*r)^2 - 1) :
    ∃ Q : ℤ, 1 ≤ Q ∧ Q ≤ 63 ∧
      Q * ((p+1)*(q+1)*(r+1)) * ((p+1)*(q+1)*(r+1) - 8) = 64 * ((p*q*r)^2 - 1) := by
  obtain ⟨Q, hQ⟩ := hd
  set P := (p+1)*(q+1)*(r+1) with hP
  set n := p*q*r with hn
  have key : Q * P * (P - 8) = 64 * (n^2 - 1) := by
    linear_combination (-64) * hQ - Q * (P + 8*s - 8) * hs
  have hpq0 : 0 < p*q := by nlinarith
  have hn8 : 8 ≤ n := by rw [hn]; nlinarith
  have hPn : n + 8 ≤ P - 8 + 8 ∧ n ≤ P - 8 := by
    constructor <;> (rw [hP, hn]; nlinarith [mul_pos hpq0 (by linarith : (0:ℤ) < r)])
  have hbig : n^2 - 1 < P * (P - 8) := by nlinarith
  have hpos : 0 < n^2 - 1 := by nlinarith
  refine ⟨Q, ?_, ?_, key⟩
  · by_contra h; push Not at h
    have : Q * (P * (P - 8)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by nlinarith)
    nlinarith
  · by_contra h; push Not at h
    have : 64 * (P * (P - 8)) ≤ Q * (P * (P - 8)) := mul_le_mul_of_nonneg_right (by omega) (by nlinarith)
    nlinarith

theorem poly_401 (p : ℤ) (hp : 401 ≤ p) : 65 ≤ 64 * p^6 - 63 * (p+1)^6 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ p = 401 + t := ⟨p - 401, by linarith, by ring⟩
  nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5, pow_nonneg ht 6]

theorem pqr_p_le_aux (p q r Q P n : ℤ) (hp : 3 ≤ p) (hpq : p < q) (hqr : q < r) (hQ : Q ≤ 63)
    (hP : P = (p+1)*(q+1)*(r+1)) (hn : n = p*q*r)
    (key : Q * P * (P - 8) = 64 * (n^2 - 1)) : p ≤ 400 := by
  by_contra hbig; push Not at hbig
  have hp0 : 0 < p := by linarith
  have hpq0 : 0 < p*q := mul_pos hp0 (by linarith)
  have hpqr : 0 < p*q*(r-p) := mul_pos hpq0 (by linarith)
  have hppq : 0 < p*p*(q-p) := mul_pos (mul_pos hp0 hp0) (by linarith)
  have hP8 : 0 ≤ P - 8 := by
    rw [hP]; nlinarith [mul_pos hpq0 (by linarith : (0:ℤ) < r)]
  have hP0 : 0 < P := by linarith
  have h1 : 64 * (n^2 - 1) ≤ 63 * P^2 := by
    rw [← key]
    have := mul_le_mul_of_nonneg_right hQ (mul_nonneg hP0.le hP8)
    have e : Q * P * (P - 8) = Q * (P * (P - 8)) := by ring
    rw [e]; nlinarith
  have h2 : p^3 * P ≤ (p+1)^3 * n := by
    have a1 : p * (q+1) ≤ (p+1) * q := by linarith
    have a2 : p * (r+1) ≤ (p+1) * r := by linarith
    have b1 : p*(q+1)*(p*(r+1)) ≤ (p+1)*q*((p+1)*r) :=
      mul_le_mul a1 a2 (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
    have b2 := mul_le_mul_of_nonneg_left b1 (by positivity : (0:ℤ) ≤ (p+1)*p)
    have e1 : p^3 * P = (p+1)*p*(p*(q+1)*(p*(r+1))) := by rw [hP]; ring
    have e2 : (p+1)^3 * n = (p+1)*p*((p+1)*q*((p+1)*r)) := by rw [hn]; ring
    rw [e1, e2]; exact b2
  have h3 : p^6 * P^2 ≤ (p+1)^6 * n^2 := by
    have := pow_le_pow_left₀ (by positivity) h2 2
    have e1 : (p^3 * P)^2 = p^6 * P^2 := by ring
    have e2 : ((p+1)^3 * n)^2 = (p+1)^6 * n^2 := by ring
    rwa [e1, e2] at this
  have hg := poly_401 p (by omega)
  have hn3 : p^6 < n^2 := by
    have h : p^3 < n := by rw [hn]; nlinarith
    have := pow_lt_pow_left₀ h (by positivity) two_ne_zero
    have e1 : (p^3)^2 = p^6 := by ring
    rwa [e1] at this
  have hp6 : 0 < p^6 := by positivity
  have h4 := mul_le_mul_of_nonneg_left h1 hp6.le
  have h5 := mul_le_mul_of_nonneg_right hg (sq_nonneg n)
  nlinarith

theorem pqr_p_le (p q r Q : ℤ) (hp : 3 ≤ p) (hpq : p < q) (hqr : q < r) (hQ : Q ≤ 63)
    (key : Q * ((p+1)*(q+1)*(r+1)) * ((p+1)*(q+1)*(r+1) - 8) = 64 * ((p*q*r)^2 - 1)) :
    p ≤ 400 :=
  pqr_p_le_aux p q r Q _ _ hp hpq hqr hQ rfl rfl key

theorem pqr_quad (p q r Q : ℤ)
    (key : Q * ((p+1)*(q+1)*(r+1)) * ((p+1)*(q+1)*(r+1) - 8) = 64 * ((p*q*r)^2 - 1)) :
    (64*(p*q)^2 - Q*((p+1)*(q+1))^2) * r^2 =
      (2*Q*((p+1)*(q+1))^2 - 8*Q*((p+1)*(q+1))) * r +
        (Q*((p+1)*(q+1))^2 - 8*Q*((p+1)*(q+1)) + 64) := by
  linear_combination (-1) * key

theorem pqr_bounds (p q r Q : ℤ) (hp : 3 ≤ p) (hpq : p < q) (hqr : q < r) (hQ1 : 1 ≤ Q)
    (hquad : (64*(p*q)^2 - Q*((p+1)*(q+1))^2) * r^2 =
      (2*Q*((p+1)*(q+1))^2 - 8*Q*((p+1)*(q+1))) * r +
        (Q*((p+1)*(q+1))^2 - 8*Q*((p+1)*(q+1)) + 64)) :
    0 < 64*(p*q)^2 - Q*((p+1)*(q+1))^2 ∧ 0 < 64*p^2 - Q*(p+1)^2 ∧
      (q < 8 ∨ (64*p^2 - Q*(p+1)^2) * q < 6 * (Q*(p+1)^2)) := by
  obtain ⟨A, hA⟩ : ∃ A, A = (p+1)*(q+1) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = Q*(p+1)^2 := ⟨_, rfl⟩
  rw [← hA] at hquad ⊢
  rw [← hK]
  have hA20 : 20 ≤ A := by rw [hA]; nlinarith
  have hQA : 20 ≤ Q * A := by nlinarith
  have hc1 : 0 < 2*Q*A^2 - 8*Q*A := by nlinarith [mul_pos (by linarith : (0:ℤ) < Q*A) (by linarith : (0:ℤ) < A - 4)]
  have hc0 : 0 < Q*A^2 - 8*Q*A + 64 := by nlinarith [mul_pos (by linarith : (0:ℤ) < Q*A) (by linarith : (0:ℤ) < A - 8)]
  have hA2 : Q*A^2 = K*(q+1)^2 := by rw [hA, hK]; ring
  have hc2form : 64*(p*q)^2 - Q*A^2 = (64*p^2 - K)*q^2 - K*(2*q+1) := by rw [hA2]; ring
  have hsum : (2*Q*A^2 - 8*Q*A) + (Q*A^2 - 8*Q*A + 64) < 3 * (K*(q+1)^2) := by
    rw [← hA2]; linarith
  generalize 2*Q*A^2 - 8*Q*A = c1 at hquad hc1 hsum
  generalize Q*A^2 - 8*Q*A + 64 = c0 at hquad hc0 hsum
  generalize 64*(p*q)^2 - Q*A^2 = c2 at hquad hc2form ⊢
  generalize 64*p^2 - K = d at hc2form ⊢
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < q := by linarith
  have hK0 : 0 < K := by rw [hK]; exact mul_pos (by linarith) (by positivity)
  have hc2pos : 0 < c2 := by
    by_contra h; push Not at h
    have : c2 * r^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    nlinarith [mul_pos hc1 hr0]
  have hd0 : 0 < d := by
    by_contra h; push Not at h
    have : d * q^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    nlinarith [mul_pos hK0 (by linarith : (0:ℤ) < 2*q+1)]
  refine ⟨hc2pos, hd0, ?_⟩
  by_contra h; push Not at h
  obtain ⟨hq8, hdq⟩ := h
  have hcr : c2 * r ≤ c1 + c0 := by
    have e1 : c2 * r * r = c1 * r + c0 := by rw [← hquad]; ring
    have e2 : c0 ≤ c0 * r := le_mul_of_one_le_right hc0.le (by linarith)
    have : c2 * r * r ≤ (c1 + c0) * r := by rw [e1, add_mul]; linarith
    exact le_of_mul_le_mul_right this hr0
  have hcq : c2 * q < c2 * r := mul_lt_mul_of_pos_left hqr hc2pos
  have hlhs : c2 * q < 3 * (K * (q+1)^2) := by linarith
  rw [hc2form] at hlhs
  have h6 : 6 * K * q^2 ≤ d * q * q^2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hq2 : 0 < q^2 - 7*q - 3 := by nlinarith
  have h7 := mul_pos hK0 hq2
  have e3 : ((d * q^2 - K * (2*q+1)) * q) = d * q * q^2 - 2 * K * q^2 - K * q := by ring
  have e4 : 3 * (K * (q+1)^2) = 3 * K * q^2 + 6 * K * q + 3 * K := by ring
  have e5 : K * (q^2 - 7*q - 3) = K * q^2 - 7 * (K * q) - 3 * K := by ring
  have e6 : 6 * K * q^2 = 6 * (K * q^2) := by ring
  have e7 : 2 * K * q^2 = 2 * (K * q^2) := by ring
  have e8 : 3 * K * q^2 = 3 * (K * q^2) := by ring
  have e9 : 6 * K * q = 6 * (K * q) := by ring
  rw [e3, e7] at hlhs; rw [e4, e8, e9] at hlhs; rw [e6] at h6; rw [e5] at h7
  linarith

/-! ### The main statement -/

theorem pqr_no (p q r : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hpq : p < q) (hqr : q < r) (s : ℕ)
    (hs : 8 * s = (p+1)*(q+1)*(r+1)) : ¬ s * (s-1) ∣ (p*q*r)^2 - 1 := by
  intro hdv
  have hs1 : 1 ≤ s := by
    have : 0 < (p+1)*(q+1)*(r+1) := by positivity
    omega
  have hdZ : (s:ℤ) * ((s:ℤ)-1) ∣ ((p:ℤ)*q*r)^2 - 1 := by
    have h1 : 1 ≤ (p*q*r)^2 := Nat.one_le_pow _ _ (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
    have := Int.natCast_dvd_natCast.mpr hdv
    push_cast [Nat.cast_sub hs1, Nat.cast_sub h1] at this
    exact this
  have hpZ : (3:ℤ) ≤ p := by exact_mod_cast hp3
  have hpqZ : (p:ℤ) < q := by exact_mod_cast hpq
  have hqrZ : (q:ℤ) < r := by exact_mod_cast hqr
  obtain ⟨Q, hQ1, hQ63, key⟩ := pqr_Q p q r s hpZ hpqZ hqrZ (by exact_mod_cast hs) hdZ
  have hp400 : (p:ℤ) ≤ 400 := pqr_p_le p q r Q hpZ hpqZ hqrZ hQ63 key
  have hquad := pqr_quad _ _ _ _ key
  obtain ⟨hc2, hd, hqb⟩ := pqr_bounds _ _ _ _ hpZ hpqZ hqrZ hQ1 hquad
  lift Q to ℕ using (by omega)
  have hQ64 : Q < 64 := by omega
  have hdN : Q*(p+1)^2 < 64*p^2 := by exact_mod_cast (by linarith : ((Q:ℤ)*(p+1)^2 < 64*p^2))
  have hqmax : q ≤ qmax p Q := by
    unfold qmax
    rcases hqb with h | h
    · have : q < 8 := by exact_mod_cast h
      exact le_trans (by omega : q ≤ 8) (Nat.le_add_left _ _)
    · have h' : (64*p^2 - Q*(p+1)^2) * q < 6*(Q*(p+1)^2) := by
        have := h
        zify [hdN.le]
        exact this
      have : q ≤ 6*Q*(p+1)^2 / (64*p^2 - Q*(p+1)^2) := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        nlinarith
      omega
  have hok := finCheck3_spec p Q q (mem_primesTo400 p hp hp3 (by exact_mod_cast hp400)) hQ64
    hdN hqmax
  unfold okTriple at hok
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with h | h
  · omega
  -- nat versions of the coefficients
  have hA8 : 8 ≤ (p+1)*(q+1) := by nlinarith
  have hc2N : Q*((p+1)*(q+1))^2 < 64*(p*q)^2 := by
    have : ((Q*((p+1)*(q+1))^2 : ℕ) : ℤ) < ((64*(p*q)^2 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have hle1 : 8*Q*((p+1)*(q+1)) ≤ 2*Q*((p+1)*(q+1))^2 := by
    have := Nat.mul_le_mul_left (Q*((p+1)*(q+1))) hA8; nlinarith
  have hle0 : 8*Q*((p+1)*(q+1)) ≤ Q*((p+1)*(q+1))^2 := by
    have := Nat.mul_le_mul_left (Q*((p+1)*(q+1))) hA8; nlinarith
  have hrle := rootFree_spec q (c2 p Q q) (c1 p Q q) (c0 p Q q) r h
    (by unfold c2; omega) (by unfold c0; omega) (by
      unfold c2 c1 c0
      zify [hc2N.le, hle1, hle0]
      push_cast
      linear_combination hquad)
  omega

/-- Unconditional: for distinct odd primes `p < q < r`, `n = p q r` fails Ordowski's
congruence. -/
theorem three_primes_case (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hp2 : p ≠ 2)
    (hpq : p < q) (hqr : q < r) :
    ¬ (p*q*r) ^ 2 ≡ 1 [MOD a (p*q*r) * (a (p*q*r) - 1)] := by
  have := Fact.mk hp; have := Fact.mk hq; have := Fact.mk hr
  haveI : NeZero p := ⟨hp.ne_zero⟩; haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  haveI : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  haveI : NeZero (p*q*r) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq2 : q ≠ 2 := by omega
  have hr2 : r ≠ 2 := by omega
  have hpo : p % 2 = 1 := by rcases hp.eq_two_or_odd with h | h; exact absurd h hp2; exact h
  have hqo : q % 2 = 1 := by rcases hq.eq_two_or_odd with h | h; exact absurd h hq2; exact h
  have hro : r % 2 = 1 := by rcases hr.eq_two_or_odd with h | h; exact absurd h hr2; exact h
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  have hcr : Nat.Coprime (p*q) r :=
    Nat.coprime_mul_iff_left.mpr ⟨(Nat.coprime_primes hp hr).mpr (by omega),
      (Nat.coprime_primes hq hr).mpr (by omega)⟩
  have ha : a (p*q*r) = (p+1)/2 * ((q+1)/2) * ((r+1)/2) := by
    rw [a_eq_aZ, aZ_mul hcr, aZ_mul hcpq, aZ_prime p hp2, aZ_prime q hq2, aZ_prime r hr2]
  have hs : 8 * a (p*q*r) = (p+1)*(q+1)*(r+1) := by
    rw [ha]
    obtain ⟨i, hi⟩ : 2 ∣ p+1 := by omega
    obtain ⟨j, hj⟩ : 2 ∣ q+1 := by omega
    obtain ⟨k, hk⟩ : 2 ∣ r+1 := by omega
    rw [hi, hj, hk]; simp; ring
  intro h
  have h1 : 1 ≤ (p*q*r)^2 := Nat.one_le_pow _ _ (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
  exact pqr_no p q r hp hp3 hpq hqr _ hs ((Nat.modEq_iff_dvd' h1).mp h.symm)

end OeisA224
