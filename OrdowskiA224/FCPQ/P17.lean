import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 17 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_17_1 : okPQ2 17 1 = true := by decide +kernel
theorem okPQ2_17_2 : okPQ2 17 2 = true := by decide +kernel
theorem okPQ2_17_3 : okPQ2 17 3 = true := by decide +kernel
theorem okPQ2_17_4 : okPQ2 17 4 = true := by decide +kernel
theorem okPQ2_17_5 : okPQ2 17 5 = true := by decide +kernel
theorem okPQ2_17_6 : okPQ2 17 6 = true := by decide +kernel
theorem okPQ2_17_7 : okPQ2 17 7 = true := by decide +kernel
theorem okPQ2_17_8 : okPQ2 17 8 = true := by decide +kernel
theorem okPQ2_17_9 : okPQ2 17 9 = true := by decide +kernel
theorem okPQ2_17_10 : okPQ2 17 10 = true := by decide +kernel
theorem okPQ2_17_11 : okPQ2 17 11 = true := by decide +kernel
theorem okPQ2_17_12 : okPQ2 17 12 = true := by decide +kernel
theorem okPQ2_17_13 : okPQ2 17 13 = true := by decide +kernel
theorem okPQ2_17_14 : okPQ2 17 14 = true := by decide +kernel
theorem okPQ2_17_15 : okPQ2 17 15 = true := by decide +kernel
theorem okPQ2_17_16 : okPQ2 17 16 = true := by decide +kernel
theorem okPQ2_17_17 : okPQ2 17 17 = true := by decide +kernel
theorem okPQ2_17_18 : okPQ2 17 18 = true := by decide +kernel
theorem okPQ2_17_19 : okPQ2 17 19 = true := by decide +kernel
theorem okPQ2_17_20 : okPQ2 17 20 = true := by decide +kernel
theorem okPQ2_17_21 : okPQ2 17 21 = true := by decide +kernel
theorem okPQ2_17_22 : okPQ2 17 22 = true := by decide +kernel
theorem okPQ2_17_23 : okPQ2 17 23 = true := by decide +kernel
theorem okPQ2_17_24 : okPQ2 17 24 = true := by decide +kernel
theorem okPQ2_17_25 : okPQ2 17 25 = true := by decide +kernel
theorem okPQ2_17_26 : okPQ2 17 26 = true := by decide +kernel
theorem okPQ2_17_27 : okPQ2 17 27 = true := by decide +kernel
theorem okPQ2_17_28 : okPQ2 17 28 = true := by decide +kernel
theorem okPQ2_17_29 : okPQ2 17 29 = true := by decide +kernel
theorem okPQ2_17_30 : okPQ2 17 30 = true := by decide +kernel
theorem okPQ2_17_31 : okPQ2 17 31 = true := by decide +kernel
theorem okPQ2_17_32 : okPQ2 17 32 = true := by decide +kernel
theorem okPQ2_17_33 : okPQ2 17 33 = true := by decide +kernel
theorem okPQ2_17_34 : okPQ2 17 34 = true := by decide +kernel
theorem okPQ2_17_35 : okPQ2 17 35 = true := by decide +kernel
theorem okPQ2_17_36 : okPQ2 17 36 = true := by decide +kernel
theorem okPQ2_17_37 : okPQ2 17 37 = true := by decide +kernel
theorem okPQ2_17_38 : okPQ2 17 38 = true := by decide +kernel
theorem okPQ2_17_39 : okPQ2 17 39 = true := by decide +kernel
theorem okPQ2_17_40 : okPQ2 17 40 = true := by decide +kernel

theorem okP2_17 : okP2 17 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_17_1
  · right; exact okPQ2_17_2
  · right; exact okPQ2_17_3
  · right; exact okPQ2_17_4
  · right; exact okPQ2_17_5
  · right; exact okPQ2_17_6
  · right; exact okPQ2_17_7
  · right; exact okPQ2_17_8
  · right; exact okPQ2_17_9
  · right; exact okPQ2_17_10
  · right; exact okPQ2_17_11
  · right; exact okPQ2_17_12
  · right; exact okPQ2_17_13
  · right; exact okPQ2_17_14
  · right; exact okPQ2_17_15
  · right; exact okPQ2_17_16
  · right; exact okPQ2_17_17
  · right; exact okPQ2_17_18
  · right; exact okPQ2_17_19
  · right; exact okPQ2_17_20
  · right; exact okPQ2_17_21
  · right; exact okPQ2_17_22
  · right; exact okPQ2_17_23
  · right; exact okPQ2_17_24
  · right; exact okPQ2_17_25
  · right; exact okPQ2_17_26
  · right; exact okPQ2_17_27
  · right; exact okPQ2_17_28
  · right; exact okPQ2_17_29
  · right; exact okPQ2_17_30
  · right; exact okPQ2_17_31
  · right; exact okPQ2_17_32
  · right; exact okPQ2_17_33
  · right; exact okPQ2_17_34
  · right; exact okPQ2_17_35
  · right; exact okPQ2_17_36
  · right; exact okPQ2_17_37
  · right; exact okPQ2_17_38
  · right; exact okPQ2_17_39
  · right; exact okPQ2_17_40

end OeisA224
