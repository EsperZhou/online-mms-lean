import Mathlib.Data.Nat.Choose.Basic
import OnlineMMS.Asymptotic

namespace OnlineMMS

open Filter
open scoped Topology

/-- The MMS of the all-goods type in the pair obstruction. -/
noncomputable def pairParameter (k : ℕ) : ℕ :=
  Nat.floor ((1 + Real.sqrt (8 * (k : ℝ) - 7)) / 4)

private theorem choose_double (q : ℕ) : Nat.choose (q + q) 2 = q * (q + q - 1) := by
  rw [Nat.choose_two_right]
  calc
    (q + q) * (q + q - 1) / 2 = 2 * (q * (q + q - 1)) / 2 := by
      congr 1
      ring
    _ = q * (q + q - 1) := Nat.mul_div_cancel_left _ (by decide)

private theorem cast_choose_double {q : ℕ} (hq : 0 < q) :
    (Nat.choose (q + q) 2 : ℝ) = (q : ℝ) * (2 * (q : ℝ) - 1) := by
  rw [choose_double, Nat.cast_mul, Nat.cast_sub (show 1 ≤ q + q by omega)]
  push_cast
  ring

/-- The floor formula is equivalent to fitting the all-goods type and one type per pair. -/
theorem pairCount_le_iff {k : ℕ} (hk : 7 ≤ k) (q : ℕ) :
    1 + Nat.choose (q + q) 2 ≤ k ↔ q ≤ pairParameter k := by
  by_cases hq0 : q = 0
  · simp [hq0, show 1 ≤ k by omega]
  have hkR : (7 : ℝ) ≤ k := by exact_mod_cast hk
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hrad : 0 ≤ 8 * (k : ℝ) - 7 := by linarith
  rw [pairParameter, Nat.le_floor_iff (by positivity : 0 ≤ (1 + Real.sqrt (8 * (k : ℝ) - 7)) / 4),
    le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  have hqpos : 0 ≤ (q : ℝ) * 4 - 1 := by linarith
  have hchoose := cast_choose_double (q := q) (by omega)
  constructor
  · intro h
    have hReal : ((1 + Nat.choose (q + q) 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast h
    push_cast at hReal
    rw [hchoose] at hReal
    have hsq : ((q : ℝ) * 4 - 1) ^ 2 ≤ 8 * (k : ℝ) - 7 := by nlinarith only [hReal]
    linarith only [(Real.le_sqrt hqpos hrad).mpr hsq]
  · intro h
    have hroot : (q : ℝ) * 4 - 1 ≤ Real.sqrt (8 * (k : ℝ) - 7) := by linarith only [h]
    have hsq := (Real.le_sqrt hqpos hrad).mp hroot
    have hReal : ((1 + Nat.choose (q + q) 2 : ℕ) : ℝ) ≤ k := by
      push_cast
      rw [hchoose]
      nlinarith only [hsq]
    exact_mod_cast hReal

theorem pairParameter_spec {k : ℕ} (hk : 7 ≤ k) :
    2 ≤ pairParameter k ∧
      1 + Nat.choose (pairParameter k + pairParameter k) 2 ≤ k ∧
      ∀ q : ℕ, 1 + Nat.choose (q + q) 2 ≤ k → q ≤ pairParameter k := by
  refine ⟨(pairCount_le_iff hk 2).mp ?_, (pairCount_le_iff hk _).mpr le_rfl,
    fun q => (pairCount_le_iff hk q).mp⟩
  simpa using hk

/-- The largest feasible pair parameter is within one of the square-root scale. -/
theorem pairParameter_estimate {k : ℕ} (hk : 7 ≤ k) :
    Real.sqrt ((k : ℝ) / 2) - 1 ≤ (pairParameter k : ℝ) ∧
      (pairParameter k : ℝ) ≤ Real.sqrt ((k : ℝ) / 2) + 1 := by
  have hkR : (7 : ℝ) ≤ k := by exact_mod_cast hk
  let s := Real.sqrt ((k : ℝ) / 2)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = (k : ℝ) / 2 := Real.sq_sqrt (by linarith)
  have hsone : 1 ≤ s := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hi : Real.sqrt (8 * (k : ℝ) - 7) ≤ 4 * s :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith only [hsq]⟩
  have hlo : 4 * s - 1 ≤ Real.sqrt (8 * (k : ℝ) - 7) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hsq, hsone]
  have hfloor := Nat.floor_le (by positivity : 0 ≤ (1 + Real.sqrt (8 * (k : ℝ) - 7)) / 4)
  have hlt := Nat.lt_floor_add_one ((1 + Real.sqrt (8 * (k : ℝ) - 7)) / 4)
  change s - 1 ≤ (pairParameter k : ℝ) ∧ (pairParameter k : ℝ) ≤ s + 1
  unfold pairParameter
  constructor <;> linarith only [hi, hlo, hfloor, hlt]

/-- The upper bound from the obstruction has asymptotic coefficient `sqrt 2`. -/
theorem tendsto_sqrt_div_pairParameter :
    Tendsto (fun k : ℕ => Real.sqrt (k : ℝ) / (pairParameter k : ℝ))
      atTop (𝓝 (Real.sqrt 2)) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hcast (b ^ 2)] with k hk
    exact Real.le_sqrt_of_sq_le hk
  have hzero : Tendsto (fun k : ℕ => (Real.sqrt (k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hconst : Tendsto (fun _ : ℕ => (Real.sqrt 2)⁻¹) atTop (𝓝 (Real.sqrt 2)⁻¹) :=
    tendsto_const_nhds
  have hlower : Tendsto (fun k : ℕ => (Real.sqrt 2)⁻¹ - (Real.sqrt (k : ℝ))⁻¹)
      atTop (𝓝 (Real.sqrt 2)⁻¹) := by simpa using hconst.sub hzero
  have hupper : Tendsto (fun k : ℕ => (Real.sqrt 2)⁻¹ + (Real.sqrt (k : ℝ))⁻¹)
      atTop (𝓝 (Real.sqrt 2)⁻¹) := by simpa using hconst.add hzero
  have hidentity (k : ℕ) (hk : 7 ≤ k) :
      Real.sqrt ((k : ℝ) / 2) / Real.sqrt (k : ℝ) = (Real.sqrt 2)⁻¹ := by
    have hpos : 0 < Real.sqrt (k : ℝ) := by
      apply Real.sqrt_pos.2
      exact_mod_cast (show 0 < k by omega)
    rw [Real.sqrt_div (Nat.cast_nonneg k)]
    exact div_div_cancel_left' hpos.ne'
  have hratio : Tendsto (fun k : ℕ => (pairParameter k : ℝ) / Real.sqrt (k : ℝ))
      atTop (𝓝 (Real.sqrt 2)⁻¹) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    · filter_upwards [eventually_ge_atTop (7 : ℕ)] with k hk
      rw [← hidentity k hk, ← one_div (Real.sqrt (k : ℝ)), ← sub_div]
      exact div_le_div_of_nonneg_right (pairParameter_estimate hk).1 (Real.sqrt_nonneg _)
    · filter_upwards [eventually_ge_atTop (7 : ℕ)] with k hk
      rw [← hidentity k hk, ← one_div (Real.sqrt (k : ℝ)), ← add_div]
      exact div_le_div_of_nonneg_right (pairParameter_estimate hk).2 (Real.sqrt_nonneg _)
  have hpos : 0 < Real.sqrt (2 : ℝ) := by positivity
  simpa only [inv_div, inv_inv] using hratio.inv₀ (inv_ne_zero hpos.ne')

end OnlineMMS
