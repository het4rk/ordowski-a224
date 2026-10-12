import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 23 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_23_1 : okPQ2 23 1 = true := by decide +kernel
theorem okPQ2_23_2 : okPQ2 23 2 = true := by decide +kernel
theorem okPQ2_23_3 : okPQ2 23 3 = true := by decide +kernel
theorem okPQ2_23_4 : okPQ2 23 4 = true := by decide +kernel
theorem okPQ2_23_5 : okPQ2 23 5 = true := by decide +kernel
theorem okPQ2_23_6 : okPQ2 23 6 = true := by decide +kernel
theorem okPQ2_23_7 : okPQ2 23 7 = true := by decide +kernel
theorem okPQ2_23_8 : okPQ2 23 8 = true := by decide +kernel
theorem okPQ2_23_9 : okPQ2 23 9 = true := by decide +kernel
theorem okPQ2_23_10 : okPQ2 23 10 = true := by decide +kernel
theorem okPQ2_23_11 : okPQ2 23 11 = true := by decide +kernel
theorem okPQ2_23_12 : okPQ2 23 12 = true := by decide +kernel
theorem okPQ2_23_13 : okPQ2 23 13 = true := by decide +kernel
theorem okPQ2_23_14 : okPQ2 23 14 = true := by decide +kernel
theorem okPQ2_23_15 : okPQ2 23 15 = true := by decide +kernel
theorem okPQ2_23_16 : okPQ2 23 16 = true := by decide +kernel
theorem okPQ2_23_17 : okPQ2 23 17 = true := by decide +kernel
theorem okPQ2_23_18 : okPQ2 23 18 = true := by decide +kernel
theorem okPQ2_23_19 : okPQ2 23 19 = true := by decide +kernel
theorem okPQ2_23_20 : okPQ2 23 20 = true := by decide +kernel
theorem okPQ2_23_21 : okPQ2 23 21 = true := by decide +kernel
theorem okPQ2_23_22 : okPQ2 23 22 = true := by decide +kernel
theorem okPQ2_23_23 : okPQ2 23 23 = true := by decide +kernel
theorem okPQ2_23_24 : okPQ2 23 24 = true := by decide +kernel
theorem okPQ2_23_25 : okPQ2 23 25 = true := by decide +kernel
theorem okPQ2_23_26 : okPQ2 23 26 = true := by decide +kernel
theorem okPQ2_23_27 : okPQ2 23 27 = true := by decide +kernel
theorem okPQ2_23_28 : okPQ2 23 28 = true := by decide +kernel
theorem okPQ2_23_29 : okPQ2 23 29 = true := by decide +kernel
theorem okPQ2_23_30 : okPQ2 23 30 = true := by decide +kernel
theorem okPQ2_23_31 : okPQ2 23 31 = true := by decide +kernel
theorem okPQ2_23_32 : okPQ2 23 32 = true := by decide +kernel
theorem okPQ2_23_33 : okPQ2 23 33 = true := by decide +kernel
theorem okPQ2_23_34 : okPQ2 23 34 = true := by decide +kernel
theorem okPQ2_23_35 : okPQ2 23 35 = true := by decide +kernel
theorem okPQ2_23_36 : okPQ2 23 36 = true := by decide +kernel
theorem okPQ2_23_37 : okPQ2 23 37 = true := by decide +kernel
theorem okPQ2_23_38 : okPQ2 23 38 = true := by decide +kernel
theorem okPQ2_23_39 : okPQ2 23 39 = true := by decide +kernel
theorem okPQ2_23_40 : okPQ2 23 40 = true := by decide +kernel

theorem okP2_23 : okP2 23 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_23_1
  · right; exact okPQ2_23_2
  · right; exact okPQ2_23_3
  · right; exact okPQ2_23_4
  · right; exact okPQ2_23_5
  · right; exact okPQ2_23_6
  · right; exact okPQ2_23_7
  · right; exact okPQ2_23_8
  · right; exact okPQ2_23_9
  · right; exact okPQ2_23_10
  · right; exact okPQ2_23_11
  · right; exact okPQ2_23_12
  · right; exact okPQ2_23_13
  · right; exact okPQ2_23_14
  · right; exact okPQ2_23_15
  · right; exact okPQ2_23_16
  · right; exact okPQ2_23_17
  · right; exact okPQ2_23_18
  · right; exact okPQ2_23_19
  · right; exact okPQ2_23_20
  · right; exact okPQ2_23_21
  · right; exact okPQ2_23_22
  · right; exact okPQ2_23_23
  · right; exact okPQ2_23_24
  · right; exact okPQ2_23_25
  · right; exact okPQ2_23_26
  · right; exact okPQ2_23_27
  · right; exact okPQ2_23_28
  · right; exact okPQ2_23_29
  · right; exact okPQ2_23_30
  · right; exact okPQ2_23_31
  · right; exact okPQ2_23_32
  · right; exact okPQ2_23_33
  · right; exact okPQ2_23_34
  · right; exact okPQ2_23_35
  · right; exact okPQ2_23_36
  · right; exact okPQ2_23_37
  · right; exact okPQ2_23_38
  · right; exact okPQ2_23_39
  · right; exact okPQ2_23_40

end OeisA224
