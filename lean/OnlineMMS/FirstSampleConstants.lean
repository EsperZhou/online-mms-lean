import OnlineMMS.Sampling
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OnlineMMS.FirstSample
open Filter
open scoped Topology
noncomputable section

def pairRate (h : ℝ) : ℝ := 1/(2*(1-1/(2*h))*h^2)

def productRate (h : ℝ) : ℝ := Real.exp (1-1/h) / h^(2-1/(2*h))

private theorem product_rate_normalized {h : ℝ} (hp : 0 < h) :
    h^2 * productRate h = Real.exp (1-h⁻¹ + (Real.log h / h)/2) := by
  have he : h^2 / h^(2-1/(2*h) : ℝ) = h^(1/(2*h) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hp]
    congr 1
    norm_num
  unfold productRate
  calc
    _ = Real.exp (1-1/h) * (h^2/h^(2-1/(2*h):ℝ)) := by ring
    _ = _ := by rw [he, Real.rpow_def_of_pos hp, ← Real.exp_add]; congr 1; ring

/-- The first-sample event bounds divided by `k/h²` have respective limits `1/2`
and `e`. This gives the meaning of the `o(1)` in the product comparison. -/
theorem first_sample_normalized_rates :
    Tendsto (fun h : ℝ => h^2*pairRate h) atTop (𝓝 (1/2)) ∧
    Tendsto (fun h : ℝ => h^2*productRate h) atTop (𝓝 (Real.exp 1)) := by
  have inv : Tendsto (fun h : ℝ => h⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have logRatio : Tendsto (fun h : ℝ => Real.log h / h) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have one : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  constructor
  · have aux : Tendsto (fun h : ℝ => 1/(2*(1-h⁻¹/2))) atTop (𝓝 (1/2)) := by
      simpa only [Pi.div_apply, Pi.mul_apply, Pi.sub_apply, zero_div, sub_zero, mul_one] using
        one.div ((tendsto_const_nhds (x := (2:ℝ))).mul (one.sub (inv.div_const 2))) (by norm_num)
    apply aux.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with h hp
    unfold pairRate
    rw [show 1/(2*h)=h⁻¹/2 by ring]
    let C := 2*(1-h⁻¹/2)
    change 1/C = h^2*(1/(C*h^2))
    simp only [one_div, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hp.ne'), one_mul]
  · have aux : Tendsto (fun h : ℝ => 1-h⁻¹ + (Real.log h / h)/2) atTop (𝓝 1) := by
      simpa using (one.sub inv).add (logRatio.div_const 2)
    apply ((Real.continuous_exp.tendsto 1).comp aux).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with h hp
    exact (product_rate_normalized hp).symm

/-- If `h = c√k`, so `k = (h/c)²`, the bounds on failure probability tend to
`1/(2c²)` for the pair score and `e/c²` for the product. The normalized payment
`√k/(2h)` equals `1/(2c)` on this scale. -/
theorem first_sample_width_scale {c : ℝ} (hc : 0 < c) :
    Tendsto (fun h : ℝ => (h/c)^2*pairRate h) atTop (𝓝 (1/(2*c^2))) ∧
    Tendsto (fun h : ℝ => (h/c)^2*productRate h) atTop (𝓝 (Real.exp 1 / c^2)) ∧
    ∀ h : ℝ, 0 < h → Real.sqrt ((h/c)^2)/(2*h) = 1/(2*c) := by
  obtain ⟨h1,h2⟩ := first_sample_normalized_rates
  constructor
  · rw [show 1/(2*c^2) = (1/2)/c^2 by ring]
    convert h1.div_const (c^2) using 1
    ext h
    ring
  constructor
  · convert h2.div_const (c^2) using 1
    ext h
    ring
  · intro h hh
    rw [Real.sqrt_sq (div_nonneg hh.le hc.le)]
    field_simp
    ring

/-- The two leading bounds cross one at `c=1/√2` and `c=√e`.
The product's payment coefficient is approximately 0.30. -/
theorem first_sample_crossing_constants :
    let p := 1/Real.sqrt 2
    let q := Real.sqrt (Real.exp 1)
    1/(2*p^2) = 1 ∧ Real.exp 1/q^2 = 1 ∧
      1/(2*p) = 1/Real.sqrt 2 ∧ (0.30:ℝ) < 1/(2*q) ∧ 1/(2*q) < 0.305 := by
  dsimp only
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hspos : 0 < Real.sqrt 2 := by positivity
  have he := Real.sq_sqrt (Real.exp_pos 1).le
  have hep : 0 < Real.sqrt (Real.exp 1) := by positivity
  have hq : Real.sqrt (Real.exp 1) < 5/3 := by
    apply (Real.sqrt_lt' (by norm_num)).mpr
    linarith [Real.exp_one_lt_d9]
  have hlo : (100/61:ℝ) < Real.sqrt (Real.exp 1) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    linarith [Real.exp_one_gt_d9]
  refine ⟨?_, by rw [he, div_self (Real.exp_pos _).ne'], ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · apply (lt_div_iff₀ (by positivity)).mpr
    linarith
  · apply (div_lt_iff₀ (by positivity)).mpr
    linarith

end
end OnlineMMS.FirstSample
