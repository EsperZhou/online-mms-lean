import OnlineMMS.PairObstruction
import OnlineMMS.PairCount
import Mathlib.Analysis.Asymptotics.Theta

namespace OnlineMMS

open Filter Asymptotics
open scoped Topology

/-- The exact finite pair bound with the manuscript's largest permissible p. -/
theorem alphaMMS_le_pairParameter {k : ℕ} (hk : 7 ≤ k) :
    alphaMMS k ≤ 1 / (pairParameter k : ℝ) := by
  obtain ⟨hp, hcount, _⟩ := pairParameter_spec hk
  exact alphaMMS_le_pair_fraction (by omega) hcount

/-- The two-arrival comparison with the explicit finite pair parameter. -/
theorem pair_twoArrival_bounds_at_parameter {k : ℕ} (hk : 7 ≤ k) :
    alphaTwoArrivalTPS k ≤ alphaTwoArrivalMMS k ∧
      alphaTwoArrivalMMS k ≤ alphaTwoArrivalBinaryMMS k ∧
      alphaTwoArrivalBinaryMMS k ≤ 1 / (pairParameter k : ℝ) := by
  obtain ⟨hp, hcount, _⟩ := pairParameter_spec hk
  exact pair_twoArrival_bounds (by omega) hcount

/-- The pair instance gives the asymptotic upper coefficient in the manuscript. -/
theorem alphaMMS_scaled_limsup_le_sqrt_two :
    limsup (fun k : ℕ => ((Real.sqrt (k : ℝ) * alphaMMS k : ℝ) : EReal)) atTop
      ≤ ((Real.sqrt 2 : ℝ) : EReal) := by
  have hlimit : Tendsto
      (fun k : ℕ => ((Real.sqrt (k : ℝ) / (pairParameter k : ℝ) : ℝ) : EReal))
      atTop (𝓝 ((Real.sqrt 2 : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp tendsto_sqrt_div_pairParameter
  rw [← hlimit.limsup_eq]
  refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop (7 : ℕ)] with k hk
  have hs := mul_le_mul_of_nonneg_left (alphaMMS_le_pairParameter hk) (Real.sqrt_nonneg (k : ℝ))
  exact_mod_cast (by simpa [div_eq_mul_inv, mul_assoc] using hs :
    Real.sqrt (k : ℝ) * alphaMMS k ≤ Real.sqrt (k : ℝ) / (pairParameter k : ℝ))

/-- For all sufficiently large k, the normalized optimum is bounded between
two positive constants by Algorithm 1 and the pair obstruction. -/
theorem alphaMMS_scaled_bounds :
    ∀ᶠ k : ℕ in atTop,
      (1 / 2 : ℝ) ≤ Real.sqrt (k : ℝ) * alphaMMS k ∧
        Real.sqrt (k : ℝ) * alphaMMS k ≤ 2 := by
  have hlo := tendsto_scaled_tps_fraction.eventually_const_le
    (show (1 / 2 : ℝ) < 1 / Real.sqrt 2 by
      have hp : 0 < Real.sqrt (2 : ℝ) := by positivity
      have hs : Real.sqrt (2 : ℝ) < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
      apply (lt_div_iff₀ hp).mpr
      linarith)
  have hhi := tendsto_sqrt_div_pairParameter.eventually_le_const
    (show Real.sqrt (2 : ℝ) < 2 from (Real.sqrt_lt' (by norm_num)).2 (by norm_num))
  filter_upwards [eventually_ge_atTop (7 : ℕ), hlo, hhi] with k hk hl hu
  have hkpos : 0 < k := by omega
  have hnonneg := Real.sqrt_nonneg (k : ℝ)
  have hlow := (explicit_fraction_le_alphaTPS hkpos).trans (alphaTPS_le_alphaMMS k)
  have hhigh := alphaMMS_le_pairParameter hk
  constructor
  · exact hl.trans (by
      simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hlow hnonneg)
  · exact (show Real.sqrt (k : ℝ) * alphaMMS k ≤
        Real.sqrt (k : ℝ) / (pairParameter k : ℝ) by
      simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hhigh hnonneg).trans hu

/-- The uniform deterministic MMS guarantee is Theta(1/sqrt(k)). -/
theorem alphaMMS_isTheta_inv_sqrt :
    alphaMMS =Θ[atTop] (fun k : ℕ => 1 / Real.sqrt (k : ℝ)) := by
  have hbounds : ∀ᶠ k : ℕ in atTop,
      1 / Real.sqrt (k : ℝ) ≤ 2 * alphaMMS k ∧
        alphaMMS k ≤ 2 * (1 / Real.sqrt (k : ℝ)) ∧ 0 ≤ alphaMMS k := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), alphaMMS_scaled_bounds] with k hk hb
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hs := Real.sqrt_pos.2 hkpos
    have hn : 0 ≤ alphaMMS k := by
      by_contra! hneg
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hs.le hneg.le
      linarith [hb.1]
    refine ⟨(div_le_iff₀ hs).mpr ?_, ?_, hn⟩
    · calc
        (1 : ℝ) = 2 * (1 / 2) := by norm_num
        _ ≤ 2 * (Real.sqrt (k : ℝ) * alphaMMS k) :=
          mul_le_mul_of_nonneg_left hb.1 (by norm_num)
        _ = _ := by ring
    · rw [mul_one_div]
      exact (le_div_iff₀ hs).mpr (by simpa [mul_comm] using hb.2)
  constructor
  · refine isBigO_iff.2 ⟨2, ?_⟩
    filter_upwards [hbounds] with k hb
    simpa only [Real.norm_of_nonneg hb.2.2,
      Real.norm_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (k : ℝ))] using hb.2.1
  · refine isBigO_iff.2 ⟨2, ?_⟩
    filter_upwards [hbounds] with k hb
    simpa only [Real.norm_of_nonneg hb.2.2,
      Real.norm_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (k : ℝ))] using hb.1

end OnlineMMS
