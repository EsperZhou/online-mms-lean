import OnlineMMS.ObliviousDeterministicFloor
import OnlineMMS.ObliviousLower
import OnlineMMS.ObliviousPair

namespace OnlineMMS

/-- Proposition 2.3. Both constants are absolute, including at zero failure
probability. Success means all agents simultaneously on each fixed sequence. -/
theorem oblivious_MMS_order {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1) :
    let scale := max (1 / Real.sqrt (k:ℝ)) (Real.sqrt δ)
    (1/434:ℝ)*scale ≤ alphaOblivious k δ ∧ alphaOblivious k δ ≤ 5*scale := by
  have hbase := oblivious_deterministic_floor hk hδ
  have ht : (1/434:ℝ)*Real.sqrt δ ≤ alphaOblivious k δ := by
    rcases hδ.eq_or_lt with he|hp
    · subst δ
      rw [Real.sqrt_zero,mul_zero]
      exact (show (0:ℝ) ≤ (1/434:ℝ)*(1/Real.sqrt (k:ℝ)) by positivity).trans hbase
    · have h := (ObliviousFixed.sqrt_failure_attainable k hp hd).le_optimum
      exact (mul_le_mul_of_nonneg_right (by norm_num : (1/434:ℝ) ≤ 1/136) (Real.sqrt_nonneg _)).trans h
  dsimp only
  constructor
  · rcases le_total (1/Real.sqrt (k:ℝ)) (Real.sqrt δ) with h|h
    · rw [max_eq_right h]; exact ht
    · rw [max_eq_left h]; exact hbase
  · exact alphaOblivious_upper hk hδ

end OnlineMMS
