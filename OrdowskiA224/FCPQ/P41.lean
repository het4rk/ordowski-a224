import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 41 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_41_1 : okPQ2 41 1 = true := by decide +kernel
theorem okPQ2_41_2 : okPQ2 41 2 = true := by decide +kernel
theorem okPQ2_41_3 : okPQ2 41 3 = true := by decide +kernel
theorem okPQ2_41_4 : okPQ2 41 4 = true := by decide +kernel
theorem okPQ2_41_5 : okPQ2 41 5 = true := by decide +kernel
theorem okPQ2_41_6 : okPQ2 41 6 = true := by decide +kernel
theorem okPQ2_41_7 : okPQ2 41 7 = true := by decide +kernel
theorem okPQ2_41_8 : okPQ2 41 8 = true := by decide +kernel
theorem okPQ2_41_9 : okPQ2 41 9 = true := by decide +kernel
theorem okPQ2_41_10 : okPQ2 41 10 = true := by decide +kernel
theorem okPQ2_41_11 : okPQ2 41 11 = true := by decide +kernel
theorem okPQ2_41_12 : okPQ2 41 12 = true := by decide +kernel
theorem okPQ2_41_13 : okPQ2 41 13 = true := by decide +kernel
theorem okPQ2_41_14 : okPQ2 41 14 = true := by decide +kernel
theorem okPQ2_41_15 : okPQ2 41 15 = true := by decide +kernel
theorem okPQ2_41_16 : okPQ2 41 16 = true := by decide +kernel
theorem okPQ2_41_17 : okPQ2 41 17 = true := by decide +kernel
theorem okPQ2_41_18 : okPQ2 41 18 = true := by decide +kernel
theorem okPQ2_41_19 : okPQ2 41 19 = true := by decide +kernel
theorem okPQ2_41_20 : okPQ2 41 20 = true := by decide +kernel
theorem okPQ2_41_21 : okPQ2 41 21 = true := by decide +kernel
theorem okPQ2_41_22 : okPQ2 41 22 = true := by decide +kernel
theorem okPQ2_41_23 : okPQ2 41 23 = true := by decide +kernel
theorem okPQ2_41_24 : okPQ2 41 24 = true := by decide +kernel
theorem okPQ2_41_25 : okPQ2 41 25 = true := by decide +kernel
theorem okPQ2_41_26 : okPQ2 41 26 = true := by decide +kernel
theorem okPQ2_41_27 : okPQ2 41 27 = true := by decide +kernel
theorem okPQ2_41_28 : okPQ2 41 28 = true := by decide +kernel
theorem okPQ2_41_29 : okPQ2 41 29 = true := by decide +kernel
theorem okPQ2_41_30 : okPQ2 41 30 = true := by decide +kernel
theorem okPQ2_41_31 : okPQ2 41 31 = true := by decide +kernel
theorem okPQ2_41_32 : okPQ2 41 32 = true := by decide +kernel
theorem okPQ2_41_33 : okPQ2 41 33 = true := by decide +kernel
theorem okPQ2_41_34 : okPQ2 41 34 = true := by decide +kernel
theorem okPQ2_41_35 : okPQ2 41 35 = true := by decide +kernel
theorem okPQ2_41_36 : okPQ2 41 36 = true := by decide +kernel
theorem okPQ2_41_37 : okPQ2 41 37 = true := by decide +kernel
theorem okPQ2_41_38 : okPQ2 41 38 = true := by decide +kernel
theorem okPQ2_41_39 : okPQ2 41 39 = true := by decide +kernel
theorem okPQ2_41_40 : okPQ2 41 40 = true := by decide +kernel

theorem okP2_41 : okP2 41 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_41_1
  · right; exact okPQ2_41_2
  · right; exact okPQ2_41_3
  · right; exact okPQ2_41_4
  · right; exact okPQ2_41_5
  · right; exact okPQ2_41_6
  · right; exact okPQ2_41_7
  · right; exact okPQ2_41_8
  · right; exact okPQ2_41_9
  · right; exact okPQ2_41_10
  · right; exact okPQ2_41_11
  · right; exact okPQ2_41_12
  · right; exact okPQ2_41_13
  · right; exact okPQ2_41_14
  · right; exact okPQ2_41_15
  · right; exact okPQ2_41_16
  · right; exact okPQ2_41_17
  · right; exact okPQ2_41_18
  · right; exact okPQ2_41_19
  · right; exact okPQ2_41_20
  · right; exact okPQ2_41_21
  · right; exact okPQ2_41_22
  · right; exact okPQ2_41_23
  · right; exact okPQ2_41_24
  · right; exact okPQ2_41_25
  · right; exact okPQ2_41_26
  · right; exact okPQ2_41_27
  · right; exact okPQ2_41_28
  · right; exact okPQ2_41_29
  · right; exact okPQ2_41_30
  · right; exact okPQ2_41_31
  · right; exact okPQ2_41_32
  · right; exact okPQ2_41_33
  · right; exact okPQ2_41_34
  · right; exact okPQ2_41_35
  · right; exact okPQ2_41_36
  · right; exact okPQ2_41_37
  · right; exact okPQ2_41_38
  · right; exact okPQ2_41_39
  · right; exact okPQ2_41_40

end OeisA224
