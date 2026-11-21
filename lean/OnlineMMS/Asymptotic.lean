import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic
import OnlineMMS.Model

namespace OnlineMMS

open Filter
open scoped Topology

/-- The least-integer definition of the multiplier agrees with the paper's ceiling formula. -/
theorem bucketMultiplier_eq_ceil (k : ℕ) :
    bucketMultiplier k = 212 + 4 * Nat.ceil (Real.sqrt ((k : ℝ) / 32)) := by
  obtain ⟨j, hEq, hj, hmin⟩ := bucketMultiplier_spec k
  let q := Nat.ceil (Real.sqrt ((k : ℝ) / 32))
  have hjReal : (k : ℝ) ≤ 32 * (j : ℝ) ^ 2 := by exact_mod_cast hj
  have hq : q = j := by
    apply le_antisymm
    · apply Nat.ceil_le.2
      exact (Real.sqrt_le_iff).2 ⟨by positivity, by linarith only [hjReal]⟩
    · by_contra! hlt
      have hbad : (32 : ℝ) * (q : ℝ) ^ 2 < k := by exact_mod_cast hmin q hlt
      have hqUpper : Real.sqrt ((k : ℝ) / 32) ≤ (q : ℝ) := Nat.le_ceil _
      have hsquare := ((Real.sqrt_le_iff).1 hqUpper).2
      linarith only [hbad, hsquare]
  rw [hEq, ← hq]

/-- The integer multiplier differs from the limiting square-root expression by at most 216. -/
theorem bucketMultiplier_estimate {k : ℕ} (hk : 0 < k) :
    Real.sqrt ((k : ℝ) / 2) + 212 ≤ (bucketMultiplier k : ℝ) ∧
      (bucketMultiplier k : ℝ) ≤ Real.sqrt ((k : ℝ) / 2) + 216 := by
  obtain ⟨j, hEq, hj, hmin⟩ := bucketMultiplier_spec k
  have hjpos : 0 < j := by
    by_contra! hjzero
    simp [Nat.eq_zero_of_le_zero hjzero] at hj
    omega
  have hjReal : (k : ℝ) ≤ 32 * (j : ℝ) ^ 2 := by
    exact_mod_cast hj
  have hprev := hmin (j - 1) (by omega)
  have hprevReal : (32 : ℝ) * ((↑(j - 1 : ℕ)) : ℝ) ^ 2 < (k : ℝ) := by
    exact_mod_cast hprev
  rw [Nat.cast_sub (show 1 ≤ j by omega)] at hprevReal
  push_cast at hprevReal
  have hlower : Real.sqrt ((k : ℝ) / 2) ≤ 4 * (j : ℝ) :=
    (Real.sqrt_le_iff).2 ⟨by positivity, by nlinarith only [hjReal]⟩
  have hupper : 4 * ((j : ℝ) - 1) < Real.sqrt ((k : ℝ) / 2) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith only [hprevReal])
  rw [hEq]
  constructor <;> push_cast <;> linarith

private theorem twice_sqrt_half (x : ℝ) (hx : 0 ≤ x) :
    2 * Real.sqrt (x / 2) = Real.sqrt 2 * Real.sqrt x := by
  rw [Real.sqrt_div hx, ← mul_div_assoc]
  have hpos : 0 < Real.sqrt (2 : ℝ) := by positivity
  apply (div_eq_iff hpos.ne').2
  have hsquare : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc
    2 * Real.sqrt x = Real.sqrt (2 : ℝ) ^ 2 * Real.sqrt x := by rw [hsquare]
    _ = Real.sqrt 2 * Real.sqrt x * Real.sqrt 2 := by ring

/-- The coefficient of the explicit TPS fraction from the general-k algorithm. -/
theorem tendsto_scaled_tps_fraction :
    Tendsto (fun k : ℕ => Real.sqrt (k : ℝ) / (2 * (bucketMultiplier k : ℝ)))
      atTop (𝓝 (1 / Real.sqrt 2)) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hcast (b ^ 2)] with k hk
    exact Real.le_sqrt_of_sq_le hk
  have hzero : Tendsto (fun k : ℕ => (Real.sqrt (k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hlimitUpper : Tendsto (fun k : ℕ => Real.sqrt 2 + 432 * (Real.sqrt (k : ℝ))⁻¹)
      atTop (𝓝 (Real.sqrt 2)) := by
    have hconst : Tendsto (fun _ : ℕ => (432 : ℝ)) atTop (𝓝 432) := tendsto_const_nhds
    have hsqrtConst : Tendsto (fun _ : ℕ => Real.sqrt 2) atTop (𝓝 (Real.sqrt 2)) :=
      tendsto_const_nhds
    simpa using hsqrtConst.add (hconst.mul hzero)
  have hlimit : Tendsto (fun k : ℕ => (2 * (bucketMultiplier k : ℝ)) / Real.sqrt (k : ℝ))
      atTop (𝓝 (Real.sqrt 2)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimitUpper
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
      have hkpos : 0 < k := by omega
      have hx : 0 < (k : ℝ) := by exact_mod_cast hkpos
      have hpos := Real.sqrt_pos.2 hx
      have hbound := (bucketMultiplier_estimate hkpos).1
      apply (le_div_iff₀ hpos).2
      rw [← twice_sqrt_half (k : ℝ) hx.le]
      linarith
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
      have hkpos : 0 < k := by omega
      have hx : 0 < (k : ℝ) := by exact_mod_cast hkpos
      have hpos := Real.sqrt_pos.2 hx
      have hbound := (bucketMultiplier_estimate hkpos).2
      apply (div_le_iff₀ hpos).2
      rw [add_mul, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one,
        ← twice_sqrt_half (k : ℝ) hx.le]
      linarith
  have hpos : 0 < Real.sqrt (2 : ℝ) := by positivity
  simpa only [inv_div, one_div] using hlimit.inv₀ hpos.ne'

/-- Any uniform-in-horizon guarantee above the explicit TPS fraction inherits its coefficient.
The liminf is taken in the extended reals, where it also allows an infinite limit. -/
theorem le_liminf_scaled_guarantee (a : ℕ → ℝ)
    (ha : ∀ k > 0, 1 / (2 * (bucketMultiplier k : ℝ)) ≤ a k) :
    ((1 / Real.sqrt 2 : ℝ) : EReal) ≤
      liminf (fun k : ℕ => ((Real.sqrt (k : ℝ) * a k : ℝ) : EReal)) atTop := by
  have hlimit : Tendsto
      (fun k : ℕ => ((Real.sqrt (k : ℝ) / (2 * (bucketMultiplier k : ℝ)) : ℝ) : EReal))
      atTop (𝓝 ((1 / Real.sqrt 2 : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp tendsto_scaled_tps_fraction
  rw [← hlimit.liminf_eq]
  refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hkpos : 0 < k := by omega
  have hscaled : Real.sqrt (k : ℝ) / (2 * (bucketMultiplier k : ℝ)) ≤
      Real.sqrt (k : ℝ) * a k := by
    simpa [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_of_nonneg_left (ha k hkpos) (Real.sqrt_nonneg (k : ℝ))
  exact_mod_cast hscaled

end OnlineMMS
