import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 31 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_31_1 : okPQ2 31 1 = true := by decide +kernel
theorem okPQ2_31_2 : okPQ2 31 2 = true := by decide +kernel
theorem okPQ2_31_3 : okPQ2 31 3 = true := by decide +kernel
theorem okPQ2_31_4 : okPQ2 31 4 = true := by decide +kernel
theorem okPQ2_31_5 : okPQ2 31 5 = true := by decide +kernel
theorem okPQ2_31_6 : okPQ2 31 6 = true := by decide +kernel
theorem okPQ2_31_7 : okPQ2 31 7 = true := by decide +kernel
theorem okPQ2_31_8 : okPQ2 31 8 = true := by decide +kernel
theorem okPQ2_31_9 : okPQ2 31 9 = true := by decide +kernel
theorem okPQ2_31_10 : okPQ2 31 10 = true := by decide +kernel
theorem okPQ2_31_11 : okPQ2 31 11 = true := by decide +kernel
theorem okPQ2_31_12 : okPQ2 31 12 = true := by decide +kernel
theorem okPQ2_31_13 : okPQ2 31 13 = true := by decide +kernel
theorem okPQ2_31_14 : okPQ2 31 14 = true := by decide +kernel
theorem okPQ2_31_15 : okPQ2 31 15 = true := by decide +kernel
theorem okPQ2_31_16 : okPQ2 31 16 = true := by decide +kernel
theorem okPQ2_31_17 : okPQ2 31 17 = true := by decide +kernel
theorem okPQ2_31_18 : okPQ2 31 18 = true := by decide +kernel
theorem okPQ2_31_19 : okPQ2 31 19 = true := by decide +kernel
theorem okPQ2_31_20 : okPQ2 31 20 = true := by decide +kernel
theorem okPQ2_31_21 : okPQ2 31 21 = true := by decide +kernel
theorem okPQ2_31_22 : okPQ2 31 22 = true := by decide +kernel
theorem okPQ2_31_23 : okPQ2 31 23 = true := by decide +kernel
theorem okPQ2_31_24 : okPQ2 31 24 = true := by decide +kernel
theorem okPQ2_31_25 : okPQ2 31 25 = true := by decide +kernel
theorem okPQ2_31_26 : okPQ2 31 26 = true := by decide +kernel
theorem okPQ2_31_27 : okPQ2 31 27 = true := by decide +kernel
theorem okPQ2_31_28 : okPQ2 31 28 = true := by decide +kernel
theorem okPQ2_31_29 : okPQ2 31 29 = true := by decide +kernel
theorem okPQ2_31_30 : okPQ2 31 30 = true := by decide +kernel
theorem okPQ2_31_31 : okPQ2 31 31 = true := by decide +kernel
theorem okPQ2_31_32 : okPQ2 31 32 = true := by decide +kernel
theorem okPQ2_31_33 : okPQ2 31 33 = true := by decide +kernel
theorem okPQ2_31_34 : okPQ2 31 34 = true := by decide +kernel
theorem okPQ2_31_35 : okPQ2 31 35 = true := by decide +kernel
theorem okPQ2_31_36 : okPQ2 31 36 = true := by decide +kernel
theorem okPQ2_31_37 : okPQ2 31 37 = true := by decide +kernel
theorem okPQ2_31_38 : okPQ2 31 38 = true := by decide +kernel
theorem okPQ2_31_39 : okPQ2 31 39 = true := by decide +kernel
theorem okPQ2_31_40 : okPQ2 31 40 = true := by decide +kernel

theorem okP2_31 : okP2 31 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_31_1
  · right; exact okPQ2_31_2
  · right; exact okPQ2_31_3
  · right; exact okPQ2_31_4
  · right; exact okPQ2_31_5
  · right; exact okPQ2_31_6
  · right; exact okPQ2_31_7
  · right; exact okPQ2_31_8
  · right; exact okPQ2_31_9
  · right; exact okPQ2_31_10
  · right; exact okPQ2_31_11
  · right; exact okPQ2_31_12
  · right; exact okPQ2_31_13
  · right; exact okPQ2_31_14
  · right; exact okPQ2_31_15
  · right; exact okPQ2_31_16
  · right; exact okPQ2_31_17
  · right; exact okPQ2_31_18
  · right; exact okPQ2_31_19
  · right; exact okPQ2_31_20
  · right; exact okPQ2_31_21
  · right; exact okPQ2_31_22
  · right; exact okPQ2_31_23
  · right; exact okPQ2_31_24
  · right; exact okPQ2_31_25
  · right; exact okPQ2_31_26
  · right; exact okPQ2_31_27
  · right; exact okPQ2_31_28
  · right; exact okPQ2_31_29
  · right; exact okPQ2_31_30
  · right; exact okPQ2_31_31
  · right; exact okPQ2_31_32
  · right; exact okPQ2_31_33
  · right; exact okPQ2_31_34
  · right; exact okPQ2_31_35
  · right; exact okPQ2_31_36
  · right; exact okPQ2_31_37
  · right; exact okPQ2_31_38
  · right; exact okPQ2_31_39
  · right; exact okPQ2_31_40

end OeisA224
