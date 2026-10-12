import OrdowskiA224.FCPQ.P5Q23_b0
import OrdowskiA224.FCPQ.P5Q23_b1
import OrdowskiA224.FCPQ.P5Q23_b2
import OrdowskiA224.FCPQ.P5Q23_b3
import OrdowskiA224.FCPQ.P5Q23_b4
import OrdowskiA224.FCPQ.P5Q23_b5
import OrdowskiA224.FCPQ.P5Q23_b6
import OrdowskiA224.FCPQ.P5Q23_b7
import OrdowskiA224.FCPQ.P5Q23_s1
import OrdowskiA224.FCPQ.P5Q23_s2
import OrdowskiA224.FCPQ.P5Q23_s3
import OrdowskiA224.FCPQ.P5Q23_s4
import OrdowskiA224.FCPQ.P5Q23_s5

namespace OeisA224

theorem okPQ2_5_23 : okPQ2 5 23 = true := by
  have hq : qUpos 5 23 = 31000 := by decide
  have hbb : bigBranch 5 23 31000 = true := by
    rw [bigBranch_eq, show (31000+1 : ℕ) = 4000+4000+4000+4000+4000+4000+4000+3001 from rfl,
      ← bbR_append, ← bbR_append, ← bbR_append, ← bbR_append, ← bbR_append, ← bbR_append,
      ← bbR_append]
    simp only [Nat.zero_add, Nat.reduceAdd, bb_5_23_0, bb_5_23_1, bb_5_23_2, bb_5_23_3,
      bb_5_23_4, bb_5_23_5, bb_5_23_6, bb_5_23_7, Bool.and_true]
  have hap : allPow 5 2000000 (fun a X => bigX 5 23 X || smallCheck 5 23 a) 200 1 5 = true := by
    apply allPow_of 5 2000000 _ 199
    · norm_num
    · intro k _ hk
      have : k ≤ 8 := by
        by_contra h
        have : 5*5^9 ≤ 5*5^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        norm_num at this; omega
      interval_cases k
      · simp [sc_5_23_1]
      · simp [sc_5_23_2]
      · simp [sc_5_23_3]
      · simp [sc_5_23_4]
      · simp [sc_5_23_5]
      all_goals (apply Bool.or_eq_true_iff.mpr; left; decide +kernel)
  unfold okPQ2
  rw [hq, hbb, hap]
  decide +kernel

end OeisA224
