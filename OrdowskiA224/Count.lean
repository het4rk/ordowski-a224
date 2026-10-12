import OrdowskiA224.Defs

/-!
# Counting squares: reduction to `ZMod n`, CRT multiplicativity, and the prime case
-/

namespace OeisA224

/-- number of squares in `ZMod n`. -/
def aZ (n : ℕ) [NeZero n] : ℕ := (Finset.univ.image (fun x : ZMod n => x ^ 2)).card

theorem a_eq_aZ (n : ℕ) [NeZero n] : a n = aZ n := by
  have hn : n ≠ 0 := NeZero.ne n
  unfold a aZ; rw [if_neg hn]
  have : (Finset.range n).image (fun k : ℕ => k ^ 2 % n) =
      (Finset.univ.image (fun x : ZMod n => x ^ 2)).image ZMod.val := by
    ext y; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, -, rfl⟩
      exact ⟨(k : ZMod n)^2, ⟨k, rfl⟩, by rw [← Nat.cast_pow, ZMod.val_natCast]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨x.val, ZMod.val_lt x, ?_⟩
      conv_rhs => rw [← ZMod.natCast_zmod_val x]
      rw [← Nat.cast_pow, ZMod.val_natCast]
  rw [this, Finset.card_image_of_injective _ (ZMod.val_injective n)]

theorem aZ_mul {m n : ℕ} [NeZero m] [NeZero n] (h : Nat.Coprime m n) :
    haveI : NeZero (m*n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    aZ (m * n) = aZ m * aZ n := by
  haveI : NeZero (m*n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  unfold aZ
  set e := ZMod.chineseRemainder h
  have h1 : (Finset.univ.image (fun x : ZMod (m*n) => x ^ 2)).map e.toEquiv.toEmbedding =
      (Finset.univ.image (fun x : ZMod m => x ^ 2)) ×ˢ (Finset.univ.image (fun x : ZMod n => x ^ 2)) := by
    ext ⟨u, v⟩
    simp only [Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_product,
      Equiv.coe_toEmbedding, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, hx⟩
      rw [map_pow] at hx
      exact ⟨⟨(e x).1, by simpa using congrArg Prod.fst hx⟩, ⟨(e x).2, by simpa using congrArg Prod.snd hx⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      refine ⟨_, ⟨e.symm (x, y), rfl⟩, ?_⟩
      rw [map_pow, RingEquiv.apply_symm_apply, ← hx, ← hy]; rfl
  rw [← Finset.card_product, ← h1, Finset.card_map]

theorem aZ_prime (p : ℕ) [hp : Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) : aZ p = (p + 1) / 2 := by
  unfold aZ
  set S : Finset (ZMod p) := (Finset.range ((p-1)/2 + 1)).image (fun k : ℕ => (k : ZMod p)) with hS
  have hpp := hp.out.two_le
  have hodd : p % 2 = 1 := (hp.out.eq_one_or_self_of_dvd 2 |> fun _ => by
    rcases hp.out.eq_two_or_odd with h | h; exact absurd h hp2; exact h)
  have himg : Finset.univ.image (fun x : ZMod p => x ^ 2) = S.image (fun x => x ^ 2) := by
    ext y; simp only [Finset.mem_image, Finset.mem_univ, true_and, hS, Finset.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x.val ≤ (p-1)/2
      · exact ⟨x, ⟨x.val, by omega, ZMod.natCast_zmod_val x⟩, rfl⟩
      · refine ⟨-x, ⟨(-x).val, ?_, ZMod.natCast_zmod_val _⟩, by ring⟩
        have hx0 : x ≠ 0 := by rintro rfl; simp at hx
        rw [ZMod.neg_val, if_neg hx0]
        have := ZMod.val_lt x; omega
    · rintro ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  have hinj : Set.InjOn (fun x : ZMod p => x ^ 2) S := by
    intro x hx y hy hxy
    simp only [hS, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx; obtain ⟨j, hj, rfl⟩ := hy
    have : ((i:ZMod p) - j) * ((i:ZMod p) + j) = 0 := by simp only at hxy; linear_combination hxy
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · have h' : ((i + j : ℕ) : ZMod p) = 0 := by push_cast; exact h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have : i + j = 0 := Nat.eq_zero_of_dvd_of_lt h' (by omega)
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      rw [hi0, hj0]
  rw [himg, Finset.card_image_of_injOn hinj, hS, Finset.card_image_of_injOn]
  · simp; omega
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have := congrArg ZMod.val hij
    simp only [ZMod.val_natCast] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

end OeisA224
