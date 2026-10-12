import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 59 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_59_1 : okPQ2 59 1 = true := by decide +kernel
theorem okPQ2_59_2 : okPQ2 59 2 = true := by decide +kernel
theorem okPQ2_59_3 : okPQ2 59 3 = true := by decide +kernel
theorem okPQ2_59_4 : okPQ2 59 4 = true := by decide +kernel
theorem okPQ2_59_5 : okPQ2 59 5 = true := by decide +kernel
theorem okPQ2_59_6 : okPQ2 59 6 = true := by decide +kernel
theorem okPQ2_59_7 : okPQ2 59 7 = true := by decide +kernel
theorem okPQ2_59_8 : okPQ2 59 8 = true := by decide +kernel
theorem okPQ2_59_9 : okPQ2 59 9 = true := by decide +kernel
theorem okPQ2_59_10 : okPQ2 59 10 = true := by decide +kernel
theorem okPQ2_59_11 : okPQ2 59 11 = true := by decide +kernel
theorem okPQ2_59_12 : okPQ2 59 12 = true := by decide +kernel
theorem okPQ2_59_13 : okPQ2 59 13 = true := by decide +kernel
theorem okPQ2_59_14 : okPQ2 59 14 = true := by decide +kernel
theorem okPQ2_59_15 : okPQ2 59 15 = true := by decide +kernel
theorem okPQ2_59_16 : okPQ2 59 16 = true := by decide +kernel
theorem okPQ2_59_17 : okPQ2 59 17 = true := by decide +kernel
theorem okPQ2_59_18 : okPQ2 59 18 = true := by decide +kernel
theorem okPQ2_59_19 : okPQ2 59 19 = true := by decide +kernel
theorem okPQ2_59_20 : okPQ2 59 20 = true := by decide +kernel
theorem okPQ2_59_21 : okPQ2 59 21 = true := by decide +kernel
theorem okPQ2_59_22 : okPQ2 59 22 = true := by decide +kernel
theorem okPQ2_59_23 : okPQ2 59 23 = true := by decide +kernel
theorem okPQ2_59_24 : okPQ2 59 24 = true := by decide +kernel
theorem okPQ2_59_25 : okPQ2 59 25 = true := by decide +kernel
theorem okPQ2_59_26 : okPQ2 59 26 = true := by decide +kernel
theorem okPQ2_59_27 : okPQ2 59 27 = true := by decide +kernel
theorem okPQ2_59_28 : okPQ2 59 28 = true := by decide +kernel
theorem okPQ2_59_29 : okPQ2 59 29 = true := by decide +kernel
theorem okPQ2_59_30 : okPQ2 59 30 = true := by decide +kernel
theorem okPQ2_59_31 : okPQ2 59 31 = true := by decide +kernel
theorem okPQ2_59_32 : okPQ2 59 32 = true := by decide +kernel
theorem okPQ2_59_33 : okPQ2 59 33 = true := by decide +kernel
theorem okPQ2_59_34 : okPQ2 59 34 = true := by decide +kernel
theorem okPQ2_59_35 : okPQ2 59 35 = true := by decide +kernel
theorem okPQ2_59_36 : okPQ2 59 36 = true := by decide +kernel
theorem okPQ2_59_37 : okPQ2 59 37 = true := by decide +kernel
theorem okPQ2_59_38 : okPQ2 59 38 = true := by decide +kernel
theorem okPQ2_59_39 : okPQ2 59 39 = true := by decide +kernel
theorem okPQ2_59_40 : okPQ2 59 40 = true := by decide +kernel

theorem okP2_59 : okP2 59 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_59_1
  · right; exact okPQ2_59_2
  · right; exact okPQ2_59_3
  · right; exact okPQ2_59_4
  · right; exact okPQ2_59_5
  · right; exact okPQ2_59_6
  · right; exact okPQ2_59_7
  · right; exact okPQ2_59_8
  · right; exact okPQ2_59_9
  · right; exact okPQ2_59_10
  · right; exact okPQ2_59_11
  · right; exact okPQ2_59_12
  · right; exact okPQ2_59_13
  · right; exact okPQ2_59_14
  · right; exact okPQ2_59_15
  · right; exact okPQ2_59_16
  · right; exact okPQ2_59_17
  · right; exact okPQ2_59_18
  · right; exact okPQ2_59_19
  · right; exact okPQ2_59_20
  · right; exact okPQ2_59_21
  · right; exact okPQ2_59_22
  · right; exact okPQ2_59_23
  · right; exact okPQ2_59_24
  · right; exact okPQ2_59_25
  · right; exact okPQ2_59_26
  · right; exact okPQ2_59_27
  · right; exact okPQ2_59_28
  · right; exact okPQ2_59_29
  · right; exact okPQ2_59_30
  · right; exact okPQ2_59_31
  · right; exact okPQ2_59_32
  · right; exact okPQ2_59_33
  · right; exact okPQ2_59_34
  · right; exact okPQ2_59_35
  · right; exact okPQ2_59_36
  · right; exact okPQ2_59_37
  · right; exact okPQ2_59_38
  · right; exact okPQ2_59_39
  · right; exact okPQ2_59_40

end OeisA224
