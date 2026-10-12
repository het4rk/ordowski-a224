import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 19 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_19_1 : okPQ2 19 1 = true := by decide +kernel
theorem okPQ2_19_2 : okPQ2 19 2 = true := by decide +kernel
theorem okPQ2_19_3 : okPQ2 19 3 = true := by decide +kernel
theorem okPQ2_19_4 : okPQ2 19 4 = true := by decide +kernel
theorem okPQ2_19_5 : okPQ2 19 5 = true := by decide +kernel
theorem okPQ2_19_6 : okPQ2 19 6 = true := by decide +kernel
theorem okPQ2_19_7 : okPQ2 19 7 = true := by decide +kernel
theorem okPQ2_19_8 : okPQ2 19 8 = true := by decide +kernel
theorem okPQ2_19_9 : okPQ2 19 9 = true := by decide +kernel
theorem okPQ2_19_10 : okPQ2 19 10 = true := by decide +kernel
theorem okPQ2_19_11 : okPQ2 19 11 = true := by decide +kernel
theorem okPQ2_19_12 : okPQ2 19 12 = true := by decide +kernel
theorem okPQ2_19_13 : okPQ2 19 13 = true := by decide +kernel
theorem okPQ2_19_14 : okPQ2 19 14 = true := by decide +kernel
theorem okPQ2_19_15 : okPQ2 19 15 = true := by decide +kernel
theorem okPQ2_19_16 : okPQ2 19 16 = true := by decide +kernel
theorem okPQ2_19_17 : okPQ2 19 17 = true := by decide +kernel
theorem okPQ2_19_18 : okPQ2 19 18 = true := by decide +kernel
theorem okPQ2_19_19 : okPQ2 19 19 = true := by decide +kernel
theorem okPQ2_19_20 : okPQ2 19 20 = true := by decide +kernel
theorem okPQ2_19_21 : okPQ2 19 21 = true := by decide +kernel
theorem okPQ2_19_22 : okPQ2 19 22 = true := by decide +kernel
theorem okPQ2_19_23 : okPQ2 19 23 = true := by decide +kernel
theorem okPQ2_19_24 : okPQ2 19 24 = true := by decide +kernel
theorem okPQ2_19_25 : okPQ2 19 25 = true := by decide +kernel
theorem okPQ2_19_26 : okPQ2 19 26 = true := by decide +kernel
theorem okPQ2_19_27 : okPQ2 19 27 = true := by decide +kernel
theorem okPQ2_19_28 : okPQ2 19 28 = true := by decide +kernel
theorem okPQ2_19_29 : okPQ2 19 29 = true := by decide +kernel
theorem okPQ2_19_30 : okPQ2 19 30 = true := by decide +kernel
theorem okPQ2_19_31 : okPQ2 19 31 = true := by decide +kernel
theorem okPQ2_19_32 : okPQ2 19 32 = true := by decide +kernel
theorem okPQ2_19_33 : okPQ2 19 33 = true := by decide +kernel
theorem okPQ2_19_34 : okPQ2 19 34 = true := by decide +kernel
theorem okPQ2_19_35 : okPQ2 19 35 = true := by decide +kernel
theorem okPQ2_19_36 : okPQ2 19 36 = true := by decide +kernel
theorem okPQ2_19_37 : okPQ2 19 37 = true := by decide +kernel
theorem okPQ2_19_38 : okPQ2 19 38 = true := by decide +kernel
theorem okPQ2_19_39 : okPQ2 19 39 = true := by decide +kernel
theorem okPQ2_19_40 : okPQ2 19 40 = true := by decide +kernel

theorem okP2_19 : okP2 19 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_19_1
  · right; exact okPQ2_19_2
  · right; exact okPQ2_19_3
  · right; exact okPQ2_19_4
  · right; exact okPQ2_19_5
  · right; exact okPQ2_19_6
  · right; exact okPQ2_19_7
  · right; exact okPQ2_19_8
  · right; exact okPQ2_19_9
  · right; exact okPQ2_19_10
  · right; exact okPQ2_19_11
  · right; exact okPQ2_19_12
  · right; exact okPQ2_19_13
  · right; exact okPQ2_19_14
  · right; exact okPQ2_19_15
  · right; exact okPQ2_19_16
  · right; exact okPQ2_19_17
  · right; exact okPQ2_19_18
  · right; exact okPQ2_19_19
  · right; exact okPQ2_19_20
  · right; exact okPQ2_19_21
  · right; exact okPQ2_19_22
  · right; exact okPQ2_19_23
  · right; exact okPQ2_19_24
  · right; exact okPQ2_19_25
  · right; exact okPQ2_19_26
  · right; exact okPQ2_19_27
  · right; exact okPQ2_19_28
  · right; exact okPQ2_19_29
  · right; exact okPQ2_19_30
  · right; exact okPQ2_19_31
  · right; exact okPQ2_19_32
  · right; exact okPQ2_19_33
  · right; exact okPQ2_19_34
  · right; exact okPQ2_19_35
  · right; exact okPQ2_19_36
  · right; exact okPQ2_19_37
  · right; exact okPQ2_19_38
  · right; exact okPQ2_19_39
  · right; exact okPQ2_19_40

end OeisA224
