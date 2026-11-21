import OnlineMMS.General
import OnlineMMS.Uniform
import OnlineMMS.Asymptotic

namespace OnlineMMS

open Filter

/-- Worst-case best TPS fraction, including the infimum over positive horizons. -/
noncomputable def alphaTPS (k : ℕ) : ℝ :=
  uniformFactor (fun n _ _ v => truncatedShare v n) k

/-- Worst-case best MMS fraction, including the infimum over positive horizons. -/
noncomputable def alphaMMS (k : ℕ) : ℝ :=
  uniformFactor (fun n hn _ v => maximinShare v n hn) k

theorem explicit_fraction_le_alphaTPS {k : ℕ} (hk : 0 < k) :
    1 / (2 * (bucketMultiplier k : ℝ)) ≤ alphaTPS k := by
  have h : (216 : ℝ) ≤ bucketMultiplier k := by exact_mod_cast (bucketMultiplier_bounds hk).1
  apply le_uniformFactor
  · have hp : 0 < 2 * (bucketMultiplier k : ℝ) := by linarith
    exact ⟨by positivity, (div_le_one hp).mpr (by linarith)⟩
  · intro n hn m v hv
    obtain ⟨policy, hp⟩ := general_tps_guarantee hn hk v hv
    exact ⟨policy, by simpa [div_eq_mul_inv, mul_comm] using hp⟩

theorem alphaTPS_le_alphaMMS (k : ℕ) : alphaTPS k ≤ alphaMMS k :=
  uniformFactor_antitone_benchmark _ _ _ (fun _ hn _ v hv =>
    maximinShare_le_truncatedShare v hv hn)

/-- The asymptotic comparison in Theorem 3.1. -/
theorem general_asymptotic_guarantee :
    let mms := liminf (fun k : ℕ => ((Real.sqrt (k : ℝ) * alphaMMS k : ℝ) : EReal)) atTop
    let tps := liminf (fun k : ℕ => ((Real.sqrt (k : ℝ) * alphaTPS k : ℝ) : EReal)) atTop
    tps ≤ mms ∧ ((1 / Real.sqrt 2 : ℝ) : EReal) ≤ tps := by
  dsimp
  constructor
  · refine liminf_le_liminf (Eventually.of_forall (fun k => ?_))
      (by isBoundedDefault) (by isBoundedDefault)
    exact_mod_cast mul_le_mul_of_nonneg_left (alphaTPS_le_alphaMMS k) (Real.sqrt_nonneg _)
  · exact le_liminf_scaled_guarantee alphaTPS (fun _ hk => explicit_fraction_le_alphaTPS hk)

end OnlineMMS
