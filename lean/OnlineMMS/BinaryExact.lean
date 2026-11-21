import OnlineMMS.BinaryRuntime
import OnlineMMS.OptimalOrder

namespace OnlineMMS

/-- The pair parameter extended to the full-MMS range and to one type. -/
noncomputable def binaryPairParameter (k : ℕ) : ℕ :=
  if 7 ≤ k then pairParameter k else 1

/-- For at least two types, this is exactly the largest integer whose
all-goods type and all pair types fit in the instance's type list. -/
theorem binaryPairParameter_spec {k : ℕ} (hk : 2 ≤ k) :
    0 < binaryPairParameter k ∧
      1 + (binaryPairParameter k + binaryPairParameter k).choose 2 ≤ k ∧
      ∀ q : ℕ, 1 + (q + q).choose 2 ≤ k → q ≤ binaryPairParameter k := by
  by_cases hlarge : 7 ≤ k
  · simp only [binaryPairParameter, if_pos hlarge]
    obtain ⟨hp, hcard, hmax⟩ := pairParameter_spec hlarge
    exact ⟨by omega, hcard, hmax⟩
  · simp only [binaryPairParameter, if_neg hlarge]
    refine ⟨Nat.one_pos, ?_, ?_⟩
    · change 2 ≤ k
      exact hk
    · intro q hq
      by_cases hsmall : q ≤ 1
      · exact hsmall
      · have hchoose : 6 ≤ (q + q).choose 2 := by
          calc
            6 = (4 : ℕ).choose 2 := by decide
            _ ≤ (q + q).choose 2 := Nat.choose_le_choose 2 (by omega)
        omega

theorem binary_exact_guarantee {m k : ℕ} (v : Fin k → Fin m → ℝ)
    (hv : ∀ t g, v t g = 0 ∨ v t g = 1) :
    ∃ policy : Policy m k 2, policy.Guarantees v
      (fun t => (1 / (binaryPairParameter k : ℝ)) * maximinShare (v t) 2 (by decide))
      Finset.univ := by
  classical
  have hrep (t : Fin k) := approvalValue_approvals (v t) (hv t)
  choose S hS using hrep
  have he : v = fun t => approvalValue (S t) := funext hS
  rw [he]
  refine ⟨BinaryRuntime.policy S, ?_⟩
  by_cases hk : 7 ≤ k
  · simpa only [binaryPairParameter, if_pos hk, BinaryRuntime.ratio, if_neg (show ¬k ≤ 6 by omega)]
      using BinaryRuntime.policy_guarantees S
  · simpa [binaryPairParameter, BinaryRuntime.ratio, if_neg hk, if_pos (show k ≤ 6 by omega)]
      using BinaryRuntime.policy_guarantees S

private theorem binaryFraction_le_one (k : ℕ) :
    1 / (binaryPairParameter k : ℝ) ≤ 1 := by
  by_cases h : 7 ≤ k
  · have hp := (pairParameter_spec h).1
    have hp₁ : (1 : ℝ) ≤ (pairParameter k : ℝ) := by
      exact_mod_cast (show 1 ≤ pairParameter k by omega)
    simp only [binaryPairParameter, if_pos h]
    exact (div_le_iff₀ (by linarith)).mpr (by simpa using hp₁)
  · simp [binaryPairParameter, if_neg h]

private theorem alphaTwoArrivalBinaryMMS_le_one (k : ℕ) :
    alphaTwoArrivalBinaryMMS k ≤ 1 := by
  unfold alphaTwoArrivalBinaryMMS
  let v : Fin k → Fin 0 → ℝ := fun _ _ => 0
  let b := fun t => maximinShare (v t) 2 (by decide)
  apply le_trans ?_ ((instanceFactor_attained v b 2).1.1.2)
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨m, w, hw, hbw, rfl⟩
    exact instanceFactor_nonneg w _ 2
  · exact ⟨0, v, (fun _ _ => le_rfl), (fun _ _ => Or.inl rfl), rfl⟩

/-- Exact worst-case deterministic MMS fraction for binary valuations
and two arrivals, including full MMS when at most six types are listed. -/
theorem alphaTwoArrivalBinaryMMS_exact (k : ℕ) :
    alphaTwoArrivalBinaryMMS k = 1 / (binaryPairParameter k : ℝ) := by
  apply le_antisymm
  · by_cases hk : 7 ≤ k
    · simpa only [binaryPairParameter, if_pos hk] using (pair_twoArrival_bounds_at_parameter hk).2.2
    · simpa [binaryPairParameter, if_neg hk] using alphaTwoArrivalBinaryMMS_le_one k
  · unfold alphaTwoArrivalBinaryMMS
    apply le_csInf
    · let v : Fin k → Fin 0 → ℝ := fun _ _ => 0
      exact ⟨_, 0, v, (fun _ _ => le_rfl), (fun _ _ => Or.inl rfl), rfl⟩
    · rintro a ⟨m, v, _, hv, rfl⟩
      obtain ⟨policy, hp⟩ := binary_exact_guarantee v hv
      exact (instanceFactor_attained v (fun t => maximinShare (v t) 2 (by decide)) 2).2
        ⟨⟨by positivity, binaryFraction_le_one k⟩, policy, hp⟩

theorem alphaTwoArrivalBinaryMMS_of_le_six {k : ℕ} (hk : k ≤ 6) :
    alphaTwoArrivalBinaryMMS k = 1 := by
  simp [alphaTwoArrivalBinaryMMS_exact, binaryPairParameter, show ¬7 ≤ k by omega]

theorem scaled_alphaTwoArrivalBinaryMMS_tendsto :
    Filter.Tendsto (fun k : ℕ => Real.sqrt (k : ℝ) * alphaTwoArrivalBinaryMMS k)
      Filter.atTop (nhds (Real.sqrt 2)) := by
  apply tendsto_sqrt_div_pairParameter.congr'
  filter_upwards [Filter.eventually_ge_atTop (7 : ℕ)] with k hk
  simp [alphaTwoArrivalBinaryMMS_exact, binaryPairParameter, if_pos hk, div_eq_mul_inv]

end OnlineMMS
