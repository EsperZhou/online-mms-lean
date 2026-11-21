import OnlineMMS.FinitePartitions
import OnlineMMS.Uniform

namespace OnlineMMS

private def horizonFactors (b : Benchmark) (k n : ℕ) (hn : 0 < n) : Set ℝ :=
  {a | ∃ (m : ℕ) (v : Fin k → Fin m → ℝ),
    (∀ t g, 0 ≤ v t g) ∧ a = instanceFactor v (fun t => b n hn m (v t)) n}

/-- Worst attainable fraction at the specified horizon. -/
noncomputable def horizonFactor (b : Benchmark) (k n : ℕ) (hn : 0 < n) : ℝ :=
  sInf (horizonFactors b k n hn)

noncomputable def alphaHorizonMMS (k n : ℕ) (hn : 0 < n) : ℝ :=
  horizonFactor (fun n hn _ v => maximinShare v n hn) k n hn

noncomputable def alphaHorizonTPS (k n : ℕ) (hn : 0 < n) : ℝ :=
  horizonFactor (fun n _ _ v => truncatedShare v n) k n hn

private theorem horizonFactors_nonempty (b : Benchmark) (k n : ℕ) (hn : 0 < n) :
    (horizonFactors b k n hn).Nonempty :=
  ⟨_, 0, fun _ _ => 0, fun _ _ => le_rfl, rfl⟩

private theorem horizonFactors_bddBelow (b : Benchmark) (k n : ℕ) (hn : 0 < n) :
    BddBelow (horizonFactors b k n hn) := by
  refine ⟨0, ?_⟩
  rintro q ⟨m, v, _, rfl⟩
  exact instanceFactor_nonneg v _ n

theorem horizonFactor_le_instance (b : Benchmark) {k n m : ℕ} (hn : 0 < n)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    horizonFactor b k n hn ≤ instanceFactor v (fun t => b n hn m (v t)) n :=
  csInf_le (horizonFactors_bddBelow b k n hn) ⟨m, v, hv, rfl⟩

theorem le_horizonFactor (b : Benchmark) {k n : ℕ} (hn : 0 < n) {q : ℝ}
    (h : ∀ (m : ℕ) (v : Fin k → Fin m → ℝ),
      (∀ t g, 0 ≤ v t g) → q ≤ instanceFactor v (fun t => b n hn m (v t)) n) :
    q ≤ horizonFactor b k n hn := by
  apply le_csInf (horizonFactors_nonempty b k n hn)
  rintro a ⟨m, v, hv, rfl⟩
  exact h m v hv

theorem le_horizonFactor_of_policies (b : Benchmark) {k n : ℕ} (hn : 0 < n) {q : ℝ}
    (hq : q ∈ Set.Icc 0 1)
    (h : ∀ (m : ℕ) (v : Fin k → Fin m → ℝ),
      (∀ t g, 0 ≤ v t g) →
      ∃ p : Policy m k n, p.Guarantees v (fun t => q * b n hn m (v t)) Finset.univ) :
    q ≤ horizonFactor b k n hn := by
  apply le_horizonFactor b hn
  intro m v hv
  apply (instanceFactor_attained v _ n).2
  exact ⟨hq, h m v hv⟩

theorem horizonFactor_le_one (b : Benchmark) {k n : ℕ} (hn : 0 < n) :
    horizonFactor b k n hn ≤ 1 := by
  let v : Fin k → Fin 0 → ℝ := fun _ _ => 0
  refine (horizonFactor_le_instance b hn v (fun _ _ => le_rfl)).trans ?_
  exact (instanceFactor_attained v _ n).1.1.2

/-- The exact two-type, two-arrival value. -/
theorem alpha_two_types_two_arrivals : alphaHorizonMMS 2 2 (by decide) = 1 := by
  apply le_antisymm (horizonFactor_le_one _ (by decide))
  apply le_horizonFactor_of_policies _ (by decide) (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  intro m v _
  simpa only [one_mul] using two_arrival_mms_policy v

end OnlineMMS
