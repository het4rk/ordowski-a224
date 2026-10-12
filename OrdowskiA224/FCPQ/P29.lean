import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 29 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_29_1 : okPQ2 29 1 = true := by decide +kernel
theorem okPQ2_29_2 : okPQ2 29 2 = true := by decide +kernel
theorem okPQ2_29_3 : okPQ2 29 3 = true := by decide +kernel
theorem okPQ2_29_4 : okPQ2 29 4 = true := by decide +kernel
theorem okPQ2_29_5 : okPQ2 29 5 = true := by decide +kernel
theorem okPQ2_29_6 : okPQ2 29 6 = true := by decide +kernel
theorem okPQ2_29_7 : okPQ2 29 7 = true := by decide +kernel
theorem okPQ2_29_8 : okPQ2 29 8 = true := by decide +kernel
theorem okPQ2_29_9 : okPQ2 29 9 = true := by decide +kernel
theorem okPQ2_29_10 : okPQ2 29 10 = true := by decide +kernel
theorem okPQ2_29_11 : okPQ2 29 11 = true := by decide +kernel
theorem okPQ2_29_12 : okPQ2 29 12 = true := by decide +kernel
theorem okPQ2_29_13 : okPQ2 29 13 = true := by decide +kernel
theorem okPQ2_29_14 : okPQ2 29 14 = true := by decide +kernel
theorem okPQ2_29_15 : okPQ2 29 15 = true := by decide +kernel
theorem okPQ2_29_16 : okPQ2 29 16 = true := by decide +kernel
theorem okPQ2_29_17 : okPQ2 29 17 = true := by decide +kernel
theorem okPQ2_29_18 : okPQ2 29 18 = true := by decide +kernel
theorem okPQ2_29_19 : okPQ2 29 19 = true := by decide +kernel
theorem okPQ2_29_20 : okPQ2 29 20 = true := by decide +kernel
theorem okPQ2_29_21 : okPQ2 29 21 = true := by decide +kernel
theorem okPQ2_29_22 : okPQ2 29 22 = true := by decide +kernel
theorem okPQ2_29_23 : okPQ2 29 23 = true := by decide +kernel
theorem okPQ2_29_24 : okPQ2 29 24 = true := by decide +kernel
theorem okPQ2_29_25 : okPQ2 29 25 = true := by decide +kernel
theorem okPQ2_29_26 : okPQ2 29 26 = true := by decide +kernel
theorem okPQ2_29_27 : okPQ2 29 27 = true := by decide +kernel
theorem okPQ2_29_28 : okPQ2 29 28 = true := by decide +kernel
theorem okPQ2_29_29 : okPQ2 29 29 = true := by decide +kernel
theorem okPQ2_29_30 : okPQ2 29 30 = true := by decide +kernel
theorem okPQ2_29_31 : okPQ2 29 31 = true := by decide +kernel
theorem okPQ2_29_32 : okPQ2 29 32 = true := by decide +kernel
theorem okPQ2_29_33 : okPQ2 29 33 = true := by decide +kernel
theorem okPQ2_29_34 : okPQ2 29 34 = true := by decide +kernel
theorem okPQ2_29_35 : okPQ2 29 35 = true := by decide +kernel
theorem okPQ2_29_36 : okPQ2 29 36 = true := by decide +kernel
theorem okPQ2_29_37 : okPQ2 29 37 = true := by decide +kernel
theorem okPQ2_29_38 : okPQ2 29 38 = true := by decide +kernel
theorem okPQ2_29_39 : okPQ2 29 39 = true := by decide +kernel
theorem okPQ2_29_40 : okPQ2 29 40 = true := by decide +kernel

theorem okP2_29 : okP2 29 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_29_1
  · right; exact okPQ2_29_2
  · right; exact okPQ2_29_3
  · right; exact okPQ2_29_4
  · right; exact okPQ2_29_5
  · right; exact okPQ2_29_6
  · right; exact okPQ2_29_7
  · right; exact okPQ2_29_8
  · right; exact okPQ2_29_9
  · right; exact okPQ2_29_10
  · right; exact okPQ2_29_11
  · right; exact okPQ2_29_12
  · right; exact okPQ2_29_13
  · right; exact okPQ2_29_14
  · right; exact okPQ2_29_15
  · right; exact okPQ2_29_16
  · right; exact okPQ2_29_17
  · right; exact okPQ2_29_18
  · right; exact okPQ2_29_19
  · right; exact okPQ2_29_20
  · right; exact okPQ2_29_21
  · right; exact okPQ2_29_22
  · right; exact okPQ2_29_23
  · right; exact okPQ2_29_24
  · right; exact okPQ2_29_25
  · right; exact okPQ2_29_26
  · right; exact okPQ2_29_27
  · right; exact okPQ2_29_28
  · right; exact okPQ2_29_29
  · right; exact okPQ2_29_30
  · right; exact okPQ2_29_31
  · right; exact okPQ2_29_32
  · right; exact okPQ2_29_33
  · right; exact okPQ2_29_34
  · right; exact okPQ2_29_35
  · right; exact okPQ2_29_36
  · right; exact okPQ2_29_37
  · right; exact okPQ2_29_38
  · right; exact okPQ2_29_39
  · right; exact okPQ2_29_40

end OeisA224
