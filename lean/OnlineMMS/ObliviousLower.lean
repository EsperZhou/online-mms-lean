import OnlineMMS.ObliviousLowerSteps
import OnlineMMS.ObliviousTail

/-! Randomized lower bound for Proposition 2.3. At each sampling round we draw one
uniform representative independently from every full bucket. For a type `u` with
positive TPS, `h ^ (r + s - Wᵤ) / 3 ^ s` has nonincreasing conditional expectation.
A failure for the type arriving with `r` agents left charges that type's potential.
Summing those charges along a fixed sequence gives `15/h²`, independently of `n` and `k`.
This argument establishes the square-root order directly in the manuscript's model. -/

namespace OnlineMMS.ObliviousFixed
noncomputable section

/-- A uniform representative from each full bucket of width `h(r+s)` suffices
against a fixed sequence. The lottery is chosen before any arrival. -/
theorem fixed_width_attainable {k h : ℕ} (hh : 16 ≤ h) {x δ : ℝ} (hx : 0 ≤ x)
    (htarget : x ≤ 1/(8*(h:ℝ))) (hfailure : 15/(h:ℝ)^2 ≤ δ) :
    ObliviousAttainable k δ x := by
  classical
  have h16 : (16:ℝ) ≤ h := by exact_mod_cast hh
  have hR : (0:ℝ)<h := by linarith
  have hβ : 0 ≤ 1/(8*(h:ℝ)) := by positivity
  refine ⟨⟨hx, htarget.trans ((div_le_one₀ (by positivity : (0:ℝ)<8*h)).mpr (by linarith))⟩, ?_⟩
  intro n hn m v hv
  let d := fun t => truncatedShare (v t) n
  let floor := fun t => x * maximinShare (v t) n hn
  have hd (t) : 0 ≤ d t := (truncatedShare_spec _ (hv t) hn).1.1
  have hfloor (t) : floor t ≤ d t*(1/(8*(h:ℝ))) := by
    calc
      _ ≤ x*d t := mul_le_mul_of_nonneg_left (maximinShare_le_truncatedShare _ (hv t) hn) hx
      _ ≤ _ := by rw [mul_comm x]; exact mul_le_mul_of_nonneg_left htarget (hd t)
  have hsteps := bucket_step hh v hv d floor hd hfloor (charge h) (charge_nonneg h)
    (fun _ _ hs hw => final_charge h16 hs hw)
    (fun _ _ _ hr hs hw => nonfinal_charge h16 hr hs hw)
  obtain ⟨D, leg, bounds⟩ := policy_law_of_steps FixedWidth.State.remaining (admissible v d)
    (fun _ hz => hz.2 rfl) v floor (charge h) (charge_nonneg h) (potential h d) hsteps
    n (FixedWidth.init v n ()) ⟨FixedWidth.valid_init hn v hv (), fun h0 => (hn.ne' h0).elim⟩
  refine ⟨D.toPolicyLottery leg, fun seq => ?_⟩
  rw [Law.success_eq_one_sub_mean_failure]
  have hb := bounds seq
  have hc : (∑ j : Fin n, charge h (n-j.val) * potential h d n (FixedWidth.init v n ()) (seq j)) ≤
      ∑ j : Fin n, charge h (n-j.val) := by
    apply Finset.sum_le_sum
    intro j _
    simpa using mul_le_mul_of_nonneg_left (potential_initial v hv hn h (seq j))
      (charge_nonneg h (n-j.val))
  have he := hb.trans (hc.trans ((total_charge h16 n).trans hfailure))
  exact sub_le_sub_left he 1

/-- Unconditional square-root lower bound for positive failure probability.
It is independent of both the possible type count and the number of arrivals. -/
theorem sqrt_failure_attainable (k : ℕ) {δ : ℝ} (hd : 0 < δ) (h1 : δ < 1) :
    ObliviousAttainable k δ ((1/136:ℝ)*Real.sqrt δ) := by
  obtain ⟨h, hh, herr, hscale⟩ := sqrt_failure_parameters hd h1
  exact fixed_width_attainable hh (by positivity) hscale herr

end
end OnlineMMS.ObliviousFixed
