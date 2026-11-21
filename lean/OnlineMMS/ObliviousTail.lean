import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

namespace OnlineMMS.ObliviousFixed

noncomputable def charge (h : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 9 / h ^ 2
  | j + 2 => (3 / h ^ 2) * (1 / 2) ^ j

theorem charge_nonneg (h : ℝ) (r : ℕ) : 0 ≤ charge h r := by
  rcases r with _ | _ | j <;> simp only [charge] <;> positivity

private theorem half_power {h : ℝ} (hh : 0 < h) (j : ℕ) :
    h ^ ((j : ℝ) / 2) = (Real.sqrt h) ^ j := by
  rw [show (j : ℝ) / 2 = (1 / 2 : ℝ) * j by ring, Real.rpow_mul hh.le,
    ← Real.sqrt_eq_rpow, Real.rpow_natCast]

theorem nonfinal_charge {h W : ℝ} {r s : ℕ} (hh : 16 ≤ h) (hr : 2 ≤ r) (hs : 0 < s)
    (hw : W < ((r : ℝ) + s) / 4) :
    1 ≤ charge h r * (h ^ ((r : ℝ) + s - W) / (3 : ℝ) ^ s) := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  push_cast at hw ⊢
  have hh0 : 0 < h := by linarith
  have hroot : 3 ≤ Real.sqrt h := (Real.le_sqrt (by norm_num) hh0.le).2 (by linarith)
  let A := (j : ℝ) + 2 + (u + 1) - W
  have he : 2 + (j : ℝ)/2 + (u : ℝ)/2 ≤ A := by
    dsimp [A]
    linarith [Nat.cast_nonneg (α := ℝ) j, Nat.cast_nonneg (α := ℝ) u]
  have hp : h ^ 2 * (2 : ℝ)^j * (3 : ℝ)^u ≤ h ^ A := by
    calc
      _ ≤ h ^ 2 * (Real.sqrt h)^j * (Real.sqrt h)^u := by
        gcongr
        linarith
      _ = h ^ (2 + (j : ℝ)/2 + (u : ℝ)/2) := by
        rw [Real.rpow_add hh0, Real.rpow_add hh0, half_power hh0, half_power hh0]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) he
  change 1 ≤ (3 / h^2 * (1 / 2 : ℝ)^j) * (h ^ A / (3 : ℝ) ^ (u + 1))
  calc
    1 ≤ h^A / (h^2 * (2:ℝ)^j * (3:ℝ)^u) :=
      (le_div_iff₀ (by positivity)).2 (by simpa using hp)
    _ = _ := by
      rw [one_div_pow, pow_succ (3:ℝ) u]
      field_simp
      ring

theorem final_charge {h W : ℝ} {s : ℕ} (hh : 16 ≤ h) (hs : 0 < s)
    (hw : W < 1 / (8*h)) :
    1 ≤ charge h 1 * (h ^ ((1 : ℝ) + s - W) / (3 : ℝ)^s) := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  have hh0 : 0 < h := by linarith
  have hl : Real.log h * (1 / (8*h)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith [Real.log_le_sub_one_of_pos hh0]
  have hsmall : h ^ (1 / (8*h)) ≤ 3 := by
    rw [Real.rpow_def_of_pos hh0]
    exact (Real.exp_le_exp.mpr hl).trans (by linarith [Real.exp_one_lt_d9])
  let A := 1 + (↑(u+1) : ℝ) - W
  have hp : h^2 * (3 : ℝ)^u ≤ 3 * h^A := by
    calc
      _ ≤ h^2 * h^u := by
        gcongr
        linarith
      _ = h ^ (1 + (↑(u+1) : ℝ)) := by
        rw [show (1 : ℝ) + (↑(u+1) : ℝ) = (↑(2+u) : ℝ) by push_cast; ring,
          Real.rpow_natCast, pow_add]
      _ ≤ h ^ (A + 1 / (8*h)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp [A]; linarith)
      _ = h^A * h^(1/(8*h)) := Real.rpow_add hh0 _ _
      _ ≤ _ := by rw [mul_comm (3:ℝ)]; gcongr
  change 1 ≤ (9 / h^2) * (h ^ A / (3 : ℝ)^(u+1))
  calc
    1 ≤ 3*h^A / (h^2 * (3:ℝ)^u) :=
      (le_div_iff₀ (by positivity)).2 (by simpa using hp)
    _ = _ := by
      rw [pow_succ (3:ℝ) u]
      field_simp
      ring

theorem total_charge {h : ℝ} (hh : 16 ≤ h) (n : ℕ) :
    (∑ j : Fin n, charge h (n-j.val)) ≤ 15/h^2 := by
  have hsum (t : ℕ) : (∑ j : Fin t, charge h (t-j.val)) =
      ∑ j ∈ Finset.range t, charge h (j+1) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Fin.sum_univ_succ, Finset.sum_range_succ]
      simpa [Nat.succ_sub_succ_eq_sub, add_comm] using congrArg (fun q => charge h (t+1) + q) ih
  rw [hsum]
  cases n with
  | zero => simp; positivity
  | succ t =>
    rw [Finset.sum_range_succ', show charge h (0+1) = 9/h^2 by rfl]
    change (∑ j ∈ Finset.range t, (3/h^2) * (1/2 : ℝ)^j) + 9/h^2 ≤ _
    rw [← Finset.mul_sum]
    have hc := mul_le_mul_of_nonneg_left (sum_geometric_two_le t) (show 0 ≤ 3/h^2 by positivity)
    calc
      _ ≤ 3/h^2 * 2 + 9/h^2 := add_le_add_right hc _
      _ = _ := by ring

theorem sqrt_failure_parameters {δ : ℝ} (hd : 0 < δ) (h1 : δ < 1) :
    ∃ h : ℕ, 16 ≤ h ∧ 15/(h:ℝ)^2 ≤ δ ∧ (1/136:ℝ)*Real.sqrt δ ≤ 1/(8*(h:ℝ)) := by
  let y := Real.sqrt δ
  have hy : 0 < y := Real.sqrt_pos.2 hd
  have hsq : y^2 = δ := Real.sq_sqrt hd.le
  have hy1 : y ≤ 1 := by nlinarith
  let h : ℕ := ⌈16 / y⌉₊
  have hceil : 16/y ≤ (h:ℝ) := Nat.le_ceil _
  have hu := Nat.ceil_lt_add_one (show 0 ≤ 16/y by positivity)
  change (h:ℝ) < _ at hu
  have hlo : 16 ≤ (h:ℝ)*y := (div_le_iff₀ hy).1 hceil
  have hhi : (h:ℝ)*y ≤ 17 := by
    have hz := mul_lt_mul_of_pos_right hu hy
    rw [add_mul, div_mul_cancel₀ _ hy.ne', one_mul] at hz
    linarith
  have ha : (16:ℝ) ≤ (h:ℝ) := (le_div_iff₀ hy).2 (by linarith) |>.trans hceil
  have hp : (0:ℝ) < (h:ℝ) := by linarith
  refine ⟨h, by exact_mod_cast ha, (div_le_iff₀ (sq_pos_of_pos hp)).2 ?_,
    (le_div_iff₀ (by positivity)).2 ?_⟩
  · have hs := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 16) hlo
    rw [← hsq]
    nlinarith only [hs]
  · change (1/136:ℝ) * y * (8 * (h:ℝ)) ≤ 1
    linarith only [hhi]

end OnlineMMS.ObliviousFixed
