import OrdowskiA224.Basic
import OrdowskiA224.PrimePowerCore

/-!
# Stangl's formula for `a (p^k)`, fully formalized, and the odd prime power case
-/

namespace OeisA224

open Finset

/-- The set of squares modulo `n`, as residues in `[0, n)`. -/
def Sq (n : ℕ) : Finset ℕ := (range n).image (fun k : ℕ => k ^ 2 % n)

theorem a_eq_card_Sq (n : ℕ) (hn : n ≠ 0) : a n = (Sq n).card := by
  unfold a Sq; rw [if_neg hn]

/-- Splitting off the squares divisible by `p`. -/
theorem card_Sq_split (p M : ℕ) (hp : p.Prime) (hM : 0 < M) :
    (Sq (p^2*M)).card = ((Sq (p^2*M)).filter (fun y => ¬ p ∣ y)).card + (Sq M).card := by
  have hp0 : 0 < p := hp.pos
  have himg : (Sq (p^2*M)).filter (fun y => p ∣ y) = (Sq M).image (fun z => p^2 * z) := by
    ext y
    simp only [Sq, mem_filter, mem_image, mem_range]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hpy⟩
      have hpx2 : p ∣ x^2 := by
        have h1 : p ∣ p^2*M * (x^2 / (p^2*M)) := Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self p two_ne_zero) _) _
        have := Nat.div_add_mod (x^2) (p^2*M)
        have h2 : p ∣ p^2*M * (x^2 / (p^2*M)) + x^2 % (p^2*M) := dvd_add h1 hpy
        rwa [this] at h2
      obtain ⟨t, rfl⟩ := hp.dvd_of_dvd_pow hpx2
      refine ⟨(t % M)^2 % M, ⟨t % M, Nat.mod_lt _ hM, rfl⟩, ?_⟩
      rw [← Nat.pow_mod, mul_pow, Nat.mul_mod_mul_left]
    · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨⟨p*t, ?_, ?_⟩, Dvd.dvd.mul_right (dvd_pow_self p two_ne_zero) _⟩
      · have : t < p*M := lt_of_lt_of_le ht (Nat.le_mul_of_pos_left M hp0)
        calc p*t < p*(p*M) := Nat.mul_lt_mul_of_pos_left this hp0
          _ = p^2*M := by ring
      · rw [mul_pow, Nat.mul_mod_mul_left]
  have hinj : Set.InjOn (fun z => p^2 * z) (Sq M) := by
    intro x _ y _ h; exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  rw [← card_filter_add_card_filter_not (fun y => p ∣ y), himg, card_image_of_injOn hinj,
    add_comm]

/-- The unit squares modulo `p^k` number `φ(p^k)/2`. -/
theorem two_mul_card_unit_Sq (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    2 * ((Sq (p^k)).filter (fun y => ¬ p ∣ y)).card = Nat.totient (p^k) := by
  set N := p^k with hN
  have hpN : p ∣ N := dvd_pow_self p (by omega)
  have hNodd : N % 2 = 1 := by
    have : Odd p := hp.odd_of_ne_two hp2
    exact Nat.odd_iff.mp (this.pow)
  have hNpos : 0 < N := pow_pos hp.pos k
  set A := (range N).filter (fun x => ¬ p ∣ x) with hA
  set A' := A.filter (fun x => 2 * x < N) with hA'
  -- p ∤ x²%N ↔ p ∤ x
  have hdvd_iff : ∀ x, p ∣ x^2 % N ↔ p ∣ x := by
    intro x
    have hdm := Nat.div_add_mod (x^2) N
    constructor
    · intro h
      have : p ∣ N * (x^2 / N) + x^2 % N := dvd_add (Dvd.dvd.mul_right hpN _) h
      rw [hdm] at this; exact hp.dvd_of_dvd_pow this
    · intro h
      have h2 : p ∣ x^2 := Dvd.dvd.pow h two_ne_zero
      have : x^2 % N = x^2 - N * (x^2 / N) := by omega
      rw [this]; exact Nat.dvd_sub h2 (Dvd.dvd.mul_right hpN _)
  have hmirror_sq : ∀ x, x ≤ N → N ≤ 2*x → (N - x)^2 % N = x^2 % N := by
    intro x h1 h2
    have : x^2 = (N-x)^2 + N*(2*x - N) := by
      zify [h1, h2]; ring
    rw [this, Nat.add_mul_mod_self_left]
  have hmirror_dvd : ∀ x, x ≤ N → (p ∣ N - x ↔ p ∣ x) := by
    intro x hx; constructor
    · intro h; have := Nat.dvd_sub hpN h; rwa [Nat.sub_sub_self hx] at this
    · intro h; exact Nat.dvd_sub hpN h
  -- (i) image
  have himg : (Sq N).filter (fun y => ¬ p ∣ y) = A'.image (fun x => x^2 % N) := by
    ext y
    simp only [Sq, hA', hA, mem_filter, mem_image, mem_range]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hpy⟩
      have hpx : ¬ p ∣ x := fun h => hpy ((hdvd_iff x).mpr h)
      by_cases h2x : 2 * x < N
      · exact ⟨x, ⟨⟨hx, hpx⟩, h2x⟩, rfl⟩
      · have hx0 : x ≠ 0 := by rintro rfl; exact hpx (dvd_zero p)
        refine ⟨N - x, ⟨⟨by omega, fun h => hpx ((hmirror_dvd x hx.le).mp h)⟩, by omega⟩, ?_⟩
        exact hmirror_sq x hx.le (by omega)
    · rintro ⟨x, ⟨⟨hx, hpx⟩, _⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, fun h => hpx ((hdvd_iff x).mp h)⟩
  -- (ii) injectivity
  have hpZ : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hinj : Set.InjOn (fun x => x^2 % N) A' := by
    intro x hx y hy hxy
    simp only [hA', hA, coe_filter, mem_filter, mem_range, Set.mem_setOf_eq] at hx hy
    obtain ⟨⟨hxN, hpx⟩, h2x⟩ := hx
    obtain ⟨⟨hyN, hpy⟩, h2y⟩ := hy
    have hmod : x^2 ≡ y^2 [MOD N] := hxy
    have hd : (N:ℤ) ∣ (y:ℤ)^2 - (x:ℤ)^2 := by
      have := (Nat.modEq_iff_dvd.mp hmod); push_cast at this; exact this
    have hfac : (y:ℤ)^2 - (x:ℤ)^2 = ((y:ℤ) - x) * ((y:ℤ) + x) := by ring
    rw [hfac] at hd
    have hNZ : (N:ℤ) = (p:ℤ)^k := by rw [hN]; push_cast; rfl
    rw [hNZ] at hd
    by_cases hps : (p:ℤ) ∣ (y:ℤ) + x
    · have hnd : ¬ (p:ℤ) ∣ (y:ℤ) - x := by
        intro h
        have h2 : (p:ℤ) ∣ 2 * (y:ℤ) := by
          have := dvd_add h hps; rwa [show (y:ℤ) - x + (y + x) = 2*y by ring] at this
        rcases hpZ.dvd_or_dvd h2 with h3 | h3
        · have : p ∣ 2 := by exact_mod_cast h3
          have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this; exact hp2 this
        · exact hpy (by exact_mod_cast h3)
      have := hpZ.pow_dvd_of_dvd_mul_left k hnd hd
      rw [← hNZ] at this
      have hle := Int.le_of_dvd (by have : (0:ℤ) < y + x := by
                                      have hx0 : x ≠ 0 := by rintro rfl; exact hpx (dvd_zero p)
                                      omega
                                    exact this) this
      omega
    · have := hpZ.pow_dvd_of_dvd_mul_right k hps hd
      rw [← hNZ] at this
      have h0 := Int.eq_zero_of_abs_lt_dvd this (by rw [abs_lt]; constructor <;> omega)
      omega
  -- (iii) counting: A = A' ∪ mirror(A')
  have hsplit : A = A' ∪ A'.image (fun x => N - x) := by
    ext x
    simp only [hA', hA, mem_union, mem_filter, mem_image, mem_range]
    constructor
    · rintro ⟨hx, hpx⟩
      by_cases h2x : 2 * x < N
      · exact Or.inl ⟨⟨hx, hpx⟩, h2x⟩
      · have hx0 : x ≠ 0 := by rintro rfl; exact hpx (dvd_zero p)
        exact Or.inr ⟨N - x, ⟨⟨by omega, fun h => hpx ((hmirror_dvd x hx.le).mp h)⟩, by omega⟩,
          by omega⟩
    · rintro (⟨h, _⟩ | ⟨y, ⟨⟨hy, hpy⟩, h2y⟩, rfl⟩)
      · exact h
      · have hy0 : y ≠ 0 := by rintro rfl; exact hpy (dvd_zero p)
        exact ⟨by omega, fun h => hpy ((hmirror_dvd y hy.le).mp h)⟩
  have hdisj : Disjoint A' (A'.image (fun x => N - x)) := by
    rw [disjoint_left]
    intro x hx hx'
    simp only [hA', hA, mem_filter, mem_image, mem_range] at hx hx'
    obtain ⟨y, ⟨⟨hy, _⟩, h2y⟩, rfl⟩ := hx'
    omega
  have hinj2 : Set.InjOn (fun x => N - x) A' := by
    intro x hx y hy h
    simp only [hA', hA, coe_filter, mem_filter, mem_range, Set.mem_setOf_eq] at hx hy
    simp only at h; omega
  have hcardA : A.card = 2 * A'.card := by
    rw [hsplit, card_union_of_disjoint hdisj, card_image_of_injOn hinj2]; ring
  have htot : Nat.totient N = A.card := by
    rw [Nat.totient_eq_card_coprime, hA]
    congr 1; ext x
    simp only [mem_filter, mem_range, and_congr_right_iff]
    intro _
    rw [hN, Nat.coprime_pow_left_iff (by omega), Nat.Prime.coprime_iff_not_dvd hp]
  rw [himg, card_image_of_injOn hinj, htot, hcardA]

theorem a_one : a 1 = 1 := by decide

/-- Stangl's formula: `2(p+1) a(p^j) = p^(j+1) + c_j` with `c_j = p+2` (j even) or `2p+1` (j odd). -/
theorem stangl (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ∀ j : ℕ,
    2 * (p + 1) * a (p^j) = p^(j+1) + (if j % 2 = 0 then p + 2 else 2*p + 1)
  | 0 => by simp [a_one]; ring
  | 1 => by
    have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    rw [pow_one, a_prime p hp hp2]; simp
    obtain ⟨m, rfl⟩ : ∃ m, p = 2*m+1 := ⟨p/2, by omega⟩
    rw [show (2*m+1+1)/2 = m+1 by omega]; ring
  | j+2 => by
    have ih := stangl p hp hp2 j
    have hp0 : 0 < p := hp.pos
    have hne : p^(j+2) ≠ 0 := by positivity
    have hpj : p^(j+2) = p^2 * p^j := by ring
    have hsplit := card_Sq_split p (p^j) hp (by positivity)
    rw [← hpj] at hsplit
    have hu := two_mul_card_unit_Sq p (j+2) hp hp2 (by omega)
    rw [Nat.totient_prime_pow hp (by omega)] at hu
    rw [a_eq_card_Sq _ hne, hsplit, ← a_eq_card_Sq _ (by positivity)]
    have hj2 : (j+2) % 2 = j % 2 := by omega
    rw [hj2]
    have e : 2 * (p+1) * ((Sq (p^(j+2))).filter (fun y => ¬ p ∣ y)).card
        = (p+1) * (p^(j+2-1) * (p-1)) := by rw [← hu]; ring
    rw [mul_add, e, ih, show j+2-1 = j+1 by omega]
    have h1 : 1 ≤ p := hp0
    zify [h1]; ring

/-- The conjecture fails (as it should) for every odd prime power `p^k`, `k ≥ 2`. -/
theorem prime_power_case (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) :
    ¬ (p^k) ^ 2 ≡ 1 [MOD a (p^k) * (a (p^k) - 1)] := by
  intro h
  have hpk : 0 < p^k := by have := hp.pos; positivity
  have h1 : 1 ≤ (p^k)^2 := Nat.one_le_pow _ _ hpk
  have hd := (Nat.modEq_iff_dvd' h1).mp h.symm
  have hst := stangl p hp hp2 k
  have hs1 : 1 ≤ a (p^k) := by
    by_contra h0; push Not at h0
    have : a (p^k) = 0 := by omega
    rw [this] at hst; split_ifs at hst
  have hdZ : ((a (p^k) : ℕ) : ℤ) * (((a (p^k) : ℕ) : ℤ) - 1) ∣ (p:ℤ)^(2*k) - 1 := by
    have := Int.natCast_dvd_natCast.mpr hd
    push_cast [Nat.cast_sub hs1, Nat.cast_sub h1] at this
    rw [show (p:ℤ)^(2*k) = ((p:ℤ)^k)^2 by ring]; exact this
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hk2 : k % 2 = 0 := by omega
    rw [if_pos hk2] at hst
    exact pp_even p k hp hp2 (by omega) _ (by exact_mod_cast hst) hdZ
  · have hk2 : k % 2 ≠ 0 := by omega
    rw [if_neg hk2] at hst
    exact pp_odd p k hp hp2 hk _ (by exact_mod_cast hst) hdZ

end OeisA224
