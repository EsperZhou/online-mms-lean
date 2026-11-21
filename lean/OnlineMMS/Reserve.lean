import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

namespace OnlineMMS

/-- The payment threshold in Algorithm 1. -/
noncomputable def threshold (h : ℝ) : ℝ := 1 / (2 * h)

/-- Removing a good of weight at most one, then trimming to the next reference
weight, cannot increase the deficit. Here `W` is the total before removal. -/
theorem trim_reserve {N W a : ℝ} (hN : 1 ≤ N) (hW : W ≤ N)
    (haW : a ≤ W) (ha : a ≤ 1) :
    let next := min (W - a) (N - 1)
    0 ≤ next ∧ next ≤ N - 1 ∧ N - 1 - next ≤ N - W := by
  dsimp
  refine ⟨le_min (sub_nonneg.mpr haW) (sub_nonneg.mpr hN), min_le_right _ _, ?_⟩
  have h₁ : W - 1 ≤ W - a := by linarith
  have h₂ : W - 1 ≤ N - 1 := by linarith
  linarith [le_min h₁ h₂]

/-- Sampling keeps the reference weight fixed and adds exactly the sampled
weight to the deficit. -/
theorem sample_deficit (N W a : ℝ) :
    N - (W - a) = (N - W) + a := by ring

private theorem threshold_le_one {h : ℝ} (hh : 216 ≤ h) : threshold h ≤ 1 := by
  unfold threshold
  apply (div_le_iff₀ (show 0 < 2 * h by linarith)).2
  linarith

private theorem two_threshold {h : ℝ} (hh : h ≠ 0) : 1 / h = 2 * threshold h := by
  unfold threshold
  field_simp [hh]

/-- A reserve of at least `N/4 + β` before all nonfinal arrivals. -/
theorem nonfinal_reserve {h W : ℝ} {r s : ℕ} (hh : 216 ≤ h) (hr : 2 ≤ r)
    (zero : s = 0 → W = (r : ℝ) + s)
    (first : s = 1 → (r : ℝ) + s - W ≤ 2 - threshold h)
    (later : 2 ≤ s →
      (r : ℝ) + s - W ≤ 3 - threshold h + (3 / 4 : ℝ) * ((s : ℝ) - 2)) :
    ((r : ℝ) + s) / 4 + threshold h ≤ W := by
  have hreal : (2 : ℝ) ≤ r := by exact_mod_cast hr
  by_cases hs0 : s = 0
  · have hzero := zero hs0
    simp [hs0] at hzero ⊢
    linarith [threshold_le_one hh]
  by_cases hs1 : s = 1
  · have hfirst := first hs1
    norm_num [hs1] at hfirst ⊢
    linarith
  · have hlater := later (by omega)
    linarith

/-- A final arrival receives at least `β` by receiving the entire reserve. -/
theorem final_reserve {h W : ℝ} {s : ℕ} (hh : 216 ≤ h)
    (zero : s = 0 → W = (1 : ℝ) + s)
    (first : s = 1 → (1 : ℝ) + s - W ≤ 2 - threshold h)
    (later : 2 ≤ s →
      (1 : ℝ) + s - W ≤ 3 - threshold h + (3 / 4 : ℝ) * ((s : ℝ) - 2)) :
    threshold h ≤ W := by
  by_cases hs0 : s = 0
  · simpa [zero hs0, hs0] using threshold_le_one hh
  by_cases hs1 : s = 1
  · have hfirst := first hs1
    norm_num [hs1] at hfirst
    linarith
  · have hs : 2 ≤ s := by omega
    have hsreal : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith [later hs]

/-- The sorted-list bound pays the threshold in the first sample. -/
theorem first_sample_payment {h N pay : ℝ} (hh : 216 ≤ h) (hN : 0 < N)
    (sorted : N / (h * N) - threshold h ≤ pay) :
    threshold h ≤ pay := by
  have hh0 : h ≠ 0 := by linarith
  have heq : N / (h * N) = 1 / h := by
    field_simp [hh0, ne_of_gt hN]
    ring
  rw [heq] at sorted
  linarith [two_threshold (show h ≠ 0 by linarith)]

/-- The narrower width pays the threshold in every later sample. -/
theorem later_sample_payment {h N W pay : ℝ} (hh : 216 ≤ h) (hN : 0 < N)
    (reserve : N / 4 ≤ W)
    (sorted : W / ((h / 4) * N) - threshold h ≤ pay) :
    threshold h ≤ pay := by
  have hh0 : 0 < h := by linarith
  have hwidth : 0 < (h / 4) * N := by positivity
  have hdiv := div_le_div_of_nonneg_right reserve hwidth.le
  have heq : (N / 4) / ((h / 4) * N) = 1 / h := by
    field_simp [ne_of_gt hh0, ne_of_gt hN]
    ring
  rw [heq] at hdiv
  linarith [two_threshold (show h ≠ 0 by linarith)]

/-- The numerical bound on the first-sample objective, using the prescribed
offset in `h` through `k ≤ 2(h-212)^2`. -/
theorem first_objective_bound {h k : ℝ} (hh : 216 ≤ h)
    (hk : k ≤ 2 * (h - 212)^2) :
    k / h^2 * (1 + 384 / h) ≤ 2 - 1 / h := by
  have hh0 : 0 < h := by linarith
  have hp : 0 < h^3 := by positivity
  have hplus : 0 ≤ h + 384 := by linarith
  have hleft : k / h^2 * (1 + 384 / h) = k * (h + 384) / h^3 := by
    have hf : 1 + 384 / h = (h + 384) / h := by
      field_simp [ne_of_gt hh0]
    rw [hf, div_mul_div_comm, ← pow_succ]
  have hright : 2 - 1 / h = ((2 * h - 1) * h^2) / h^3 := by
    field_simp [ne_of_gt hh0]
    ring
  rw [hleft, hright]
  apply div_le_div_of_nonneg_right _ hp.le
  refine (mul_le_mul_of_nonneg_right hk hplus).trans ?_
  have hdiff : (2 * h - 1) * h^2 - 2 * (h - 212)^2 * (h + 384) =
      79 * (h - 212)^2 + 269240 * (h - 212) + 19011312 := by ring
  nlinarith [sq_nonneg (h - 212)]

private theorem exp_one_le_rational : Real.exp 1 ≤ 68 / 25 :=
  Real.exp_one_lt_d9.le.trans (by norm_num)

private theorem log_64_margin : 4 + 1 / 8 < Real.log 64 := by
  rw [show (64 : ℝ) = 2^6 by norm_num, Real.log_pow]
  norm_num
  linarith [Real.log_two_gt_d9]

private theorem log_216_rate : 16 / 3 ≤ Real.log 216 := by
  have hone : 1 ≤ Real.log (68 / 25 : ℝ) :=
    (Real.le_log_iff_exp_le (by norm_num)).2 exp_one_le_rational
  have hpow : (68 / 25 : ℝ)^16 ≤ (216 : ℝ)^3 := by norm_num
  have h := Real.log_le_log (show 0 < (68 / 25 : ℝ)^16 by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

private theorem threshold_log_bound {h : ℝ} (hh : 216 ≤ h) :
    threshold h * Real.log h ≤ 1 / 8 := by
  have h₈ : 0 < h / 8 := by linarith
  have hlog₈ := Real.log_le_sub_one_of_pos (show 0 < (8 : ℝ) by norm_num)
  have hlogratio := Real.log_le_sub_one_of_pos h₈
  have hlog : Real.log h = Real.log 8 + Real.log (h / 8) := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt h₈)]
    congr 1
    ring
  have hbound : Real.log h ≤ h / 4 := by linarith
  unfold threshold
  rw [div_mul_eq_mul_div, one_mul]
  exact (div_le_iff₀ (show 0 < 2 * h by linarith)).2 (by linarith)

/-- Product control implies the later-sample deficit bound used for payments.
The lower potential is written as `exp (D * log h)` for `h ^ D`. -/
theorem later_deficit_budget {h s D : ℝ} (hh : 216 ≤ h) (hs : 2 ≤ s)
    (potential : Real.exp (D * Real.log h) ≤
      h^3 / 64 * Real.exp (4 * (s - 1))) :
    D ≤ 3 - threshold h + (3 / 4 : ℝ) * (s - 2) := by
  have hh0 : 0 < h := by linarith
  have hlog0 : 0 < Real.log h := Real.log_pos (by linarith)
  have hp : h ≠ 0 := ne_of_gt hh0
  have hlog := Real.log_le_log (Real.exp_pos _) potential
  rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_div (pow_ne_zero _ hp) (by norm_num), Real.log_pow, Real.log_exp] at hlog
  norm_num at hlog
  have hrate : (16 / 3 : ℝ) ≤ Real.log h :=
    log_216_rate.trans (Real.log_le_log (by norm_num) hh)
  have hstep : 4 * (s - 2) ≤ (3 / 4 * Real.log h) * (s - 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  apply (mul_le_mul_right hlog0).mp
  nlinarith [threshold_log_bound hh, log_64_margin]

/-- One later sample charges a single multiplicative factor `e^4`. -/
theorem product_budget_step {h s P next : ℝ}
    (old : P ≤ h^3 / 64 * Real.exp (4 * (s - 1)))
    (growth : next ≤ P * Real.exp 4) :
    next ≤ h^3 / 64 * Real.exp (4 * s) := by
  refine growth.trans ((mul_le_mul_of_nonneg_right old (Real.exp_nonneg _)).trans_eq ?_)
  rw [mul_assoc, ← Real.exp_add]
  rw [show 4 * (s - 1) + 4 = 4 * s by ring]

end OnlineMMS
