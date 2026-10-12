import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 53 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_53_1 : okPQ2 53 1 = true := by decide +kernel
theorem okPQ2_53_2 : okPQ2 53 2 = true := by decide +kernel
theorem okPQ2_53_3 : okPQ2 53 3 = true := by decide +kernel
theorem okPQ2_53_4 : okPQ2 53 4 = true := by decide +kernel
theorem okPQ2_53_5 : okPQ2 53 5 = true := by decide +kernel
theorem okPQ2_53_6 : okPQ2 53 6 = true := by decide +kernel
theorem okPQ2_53_7 : okPQ2 53 7 = true := by decide +kernel
theorem okPQ2_53_8 : okPQ2 53 8 = true := by decide +kernel
theorem okPQ2_53_9 : okPQ2 53 9 = true := by decide +kernel
theorem okPQ2_53_10 : okPQ2 53 10 = true := by decide +kernel
theorem okPQ2_53_11 : okPQ2 53 11 = true := by decide +kernel
theorem okPQ2_53_12 : okPQ2 53 12 = true := by decide +kernel
theorem okPQ2_53_13 : okPQ2 53 13 = true := by decide +kernel
theorem okPQ2_53_14 : okPQ2 53 14 = true := by decide +kernel
theorem okPQ2_53_15 : okPQ2 53 15 = true := by decide +kernel
theorem okPQ2_53_16 : okPQ2 53 16 = true := by decide +kernel
theorem okPQ2_53_17 : okPQ2 53 17 = true := by decide +kernel
theorem okPQ2_53_18 : okPQ2 53 18 = true := by decide +kernel
theorem okPQ2_53_19 : okPQ2 53 19 = true := by decide +kernel
theorem okPQ2_53_20 : okPQ2 53 20 = true := by decide +kernel
theorem okPQ2_53_21 : okPQ2 53 21 = true := by decide +kernel
theorem okPQ2_53_22 : okPQ2 53 22 = true := by decide +kernel
theorem okPQ2_53_23 : okPQ2 53 23 = true := by decide +kernel
theorem okPQ2_53_24 : okPQ2 53 24 = true := by decide +kernel
theorem okPQ2_53_25 : okPQ2 53 25 = true := by decide +kernel
theorem okPQ2_53_26 : okPQ2 53 26 = true := by decide +kernel
theorem okPQ2_53_27 : okPQ2 53 27 = true := by decide +kernel
theorem okPQ2_53_28 : okPQ2 53 28 = true := by decide +kernel
theorem okPQ2_53_29 : okPQ2 53 29 = true := by decide +kernel
theorem okPQ2_53_30 : okPQ2 53 30 = true := by decide +kernel
theorem okPQ2_53_31 : okPQ2 53 31 = true := by decide +kernel
theorem okPQ2_53_32 : okPQ2 53 32 = true := by decide +kernel
theorem okPQ2_53_33 : okPQ2 53 33 = true := by decide +kernel
theorem okPQ2_53_34 : okPQ2 53 34 = true := by decide +kernel
theorem okPQ2_53_35 : okPQ2 53 35 = true := by decide +kernel
theorem okPQ2_53_36 : okPQ2 53 36 = true := by decide +kernel
theorem okPQ2_53_37 : okPQ2 53 37 = true := by decide +kernel
theorem okPQ2_53_38 : okPQ2 53 38 = true := by decide +kernel
theorem okPQ2_53_39 : okPQ2 53 39 = true := by decide +kernel
theorem okPQ2_53_40 : okPQ2 53 40 = true := by decide +kernel

theorem okP2_53 : okP2 53 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_53_1
  · right; exact okPQ2_53_2
  · right; exact okPQ2_53_3
  · right; exact okPQ2_53_4
  · right; exact okPQ2_53_5
  · right; exact okPQ2_53_6
  · right; exact okPQ2_53_7
  · right; exact okPQ2_53_8
  · right; exact okPQ2_53_9
  · right; exact okPQ2_53_10
  · right; exact okPQ2_53_11
  · right; exact okPQ2_53_12
  · right; exact okPQ2_53_13
  · right; exact okPQ2_53_14
  · right; exact okPQ2_53_15
  · right; exact okPQ2_53_16
  · right; exact okPQ2_53_17
  · right; exact okPQ2_53_18
  · right; exact okPQ2_53_19
  · right; exact okPQ2_53_20
  · right; exact okPQ2_53_21
  · right; exact okPQ2_53_22
  · right; exact okPQ2_53_23
  · right; exact okPQ2_53_24
  · right; exact okPQ2_53_25
  · right; exact okPQ2_53_26
  · right; exact okPQ2_53_27
  · right; exact okPQ2_53_28
  · right; exact okPQ2_53_29
  · right; exact okPQ2_53_30
  · right; exact okPQ2_53_31
  · right; exact okPQ2_53_32
  · right; exact okPQ2_53_33
  · right; exact okPQ2_53_34
  · right; exact okPQ2_53_35
  · right; exact okPQ2_53_36
  · right; exact okPQ2_53_37
  · right; exact okPQ2_53_38
  · right; exact okPQ2_53_39
  · right; exact okPQ2_53_40

end OeisA224
