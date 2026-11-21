import OnlineMMS.FiniteEnvelope

namespace OnlineMMS

/-- The strict crossover with the 1/k baseline, including both boundary
integers. This proof only uses bounds on the integer bucket multiplier. -/
theorem two_width_beats_baseline_iff {k : ℕ} (hk : 0 < k) :
    1/(k:ℝ) < 1/(2*(bucketMultiplier k:ℝ)) ↔ 457 ≤ k := by
  have hh := (bucketMultiplier_bounds hk).1
  have hp : (0:ℝ) < k := by exact_mod_cast hk
  have hp' : (0:ℝ) < 2*(bucketMultiplier k:ℝ) := by positivity
  rw [one_div_lt_one_div hp hp']
  have eq : (2:ℝ)*(bucketMultiplier k:ℝ)<k ↔ 2*bucketMultiplier k<k := by exact_mod_cast Iff.rfl
  rw [eq]
  by_cases hlow : k ≤ 288
  · omega
  by_cases hmid : k ≤ 512
  · obtain ⟨j,hj,hfit,hmin⟩ := bucketMultiplier_spec k
    have hj4 : j = 4 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hl|hg
      · have hh' := Nat.pow_le_pow_left (show j ≤ 3 by omega) 2
        omega
      · have := hmin 4 hg
        omega
    rw [hj,hj4]; omega
  · have hkr : (513:ℝ) ≤ k := by exact_mod_cast (show 513 ≤ k by omega)
    have hs : Real.sqrt ((k:ℝ)/2) < ((k:ℝ)-432)/2 :=
      (Real.sqrt_lt' (by linarith)).2 (by nlinarith [sq_nonneg ((k:ℝ)-513)])
    have hcap := (bucketMultiplier_estimate hk).2
    have H : (2:ℝ)*(bucketMultiplier k:ℝ)<k := by linarith
    constructor
    · omega
    · exact fun _ => eq.mp H

end OnlineMMS
