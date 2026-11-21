import OnlineMMS.FinitePadding
import OnlineMMS.FiniteThree
import OnlineMMS.MainTheorem
import OnlineMMS.PairObstruction
import Mathlib.Topology.Order.MonotoneConvergence

namespace OnlineMMS

open Filter
open scoped Topology

private theorem horizonFactor_nonneg (b : Benchmark) {k n : ℕ} (hn : 0 < n) :
    0 ≤ horizonFactor b k n hn :=
  le_horizonFactor b hn fun _m v _ => instanceFactor_nonneg v _ n

private theorem horizonFactors_bounded (b : Benchmark) (k : ℕ) :
    BddBelow (Set.range (fun n : ℕ => horizonFactor b k (n+1) (by omega))) := by
  refine ⟨0,?_⟩
  rintro _ ⟨n,rfl⟩
  exact horizonFactor_nonneg b (by omega)

theorem uniformFactor_eq_iInf_horizon (b : Benchmark) (k : ℕ) :
    uniformFactor b k = ⨅ n : ℕ, horizonFactor b k (n+1) (by omega) := by
  apply le_antisymm
  · apply le_ciInf
    intro n
    apply le_horizonFactor b (by omega)
    intro m v hv
    exact uniformFactor_le_instance b (by omega) v hv
  · change (⨅ n : ℕ, horizonFactor b k (n+1) (by omega)) ≤ sInf (instanceFactors b k)
    have hne : (instanceFactors b k).Nonempty :=
      ⟨_,1,by decide,0,fun _ _ => 0,fun _ _ => le_rfl,rfl⟩
    apply le_csInf hne
    rintro _ ⟨n,hn,m,v,hv,rfl⟩
    have h := ciInf_le (horizonFactors_bounded b k) (n-1)
    have hindex : (n-1)+1=n := by omega
    exact (show (⨅ i : ℕ, horizonFactor b k (i+1) (by omega)) ≤ horizonFactor b k n hn by
      simpa [hindex] using h).trans (horizonFactor_le_instance b hn v hv)

theorem alpha_horizon_mms_antitone (k : ℕ) :
    Antitone (fun n : ℕ => alphaHorizonMMS k (n+1) (by omega)) :=
  antitone_nat_of_succ_le fun n => alpha_horizon_mms_padding (show 0 < n+1 by omega)

theorem alpha_horizon_tps_antitone (k : ℕ) :
    Antitone (fun n : ℕ => alphaHorizonTPS k (n+1) (by omega)) :=
  antitone_nat_of_succ_le fun n => alpha_horizon_tps_padding (show 0 < n+1 by omega)

/-- The uniform MMS fraction equals the limit of the fixed-horizon values. -/
theorem alpha_horizon_mms_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => alphaHorizonMMS k (n+1) (by omega)) atTop (𝓝 (alphaMMS k)) := by
  unfold alphaMMS
  rw [uniformFactor_eq_iInf_horizon]
  exact tendsto_atTop_ciInf (alpha_horizon_mms_antitone k) (horizonFactors_bounded _ k)

/-- The uniform TPS fraction equals the limit of the fixed-horizon values. -/
theorem alpha_horizon_tps_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => alphaHorizonTPS k (n+1) (by omega)) atTop (𝓝 (alphaTPS k)) := by
  unfold alphaTPS
  rw [uniformFactor_eq_iInf_horizon]
  exact tendsto_atTop_ciInf (alpha_horizon_tps_antitone k) (horizonFactors_bounded _ k)

/-- The three-arrival upper bound persists at every longer horizon. -/
theorem alpha_two_types_from_three_upper {n : ℕ} (hn : 3 ≤ n) :
    alphaHorizonMMS 2 n (by omega) ≤ 9/10 := by
  rw [← alpha_two_types_three_arrivals]
  have h := alpha_horizon_mms_antitone 2 (show 2 ≤ n-1 by omega)
  have he : (n-1)+1=n := by omega
  simpa [he] using h


/-- The generic horizon-two MMS quantity agrees with the quantity used by
the pair obstruction. -/
theorem alpha_horizon_two_mms_consistent (k : ℕ) :
    alphaHorizonMMS k 2 (by decide) = alphaTwoArrivalMMS k := by
  apply congrArg sInf
  ext a
  change
    (∃ (m : ℕ) (v : Fin k → Fin m → ℝ), (∀ t g, 0 ≤ v t g) ∧
      a = instanceFactor v (fun t => maximinShare (v t) 2 (by decide)) 2) ↔
    (∃ (m : ℕ) (v : Fin k → Fin m → ℝ), (∀ t g, 0 ≤ v t g) ∧ True ∧
      a = instanceFactor v (fun t => maximinShare (v t) 2 (by decide)) 2)
  simp

theorem alpha_horizon_two_tps_consistent (k : ℕ) :
    alphaHorizonTPS k 2 (by decide) = alphaTwoArrivalTPS k := by
  apply congrArg sInf
  ext a
  change
    (∃ (m : ℕ) (v : Fin k → Fin m → ℝ), (∀ t g, 0 ≤ v t g) ∧
      a = instanceFactor v (fun t => truncatedShare (v t) 2) 2) ↔
    (∃ (m : ℕ) (v : Fin k → Fin m → ℝ), (∀ t g, 0 ≤ v t g) ∧ True ∧
      a = instanceFactor v (fun t => truncatedShare (v t) 2) 2)
  simp

end OnlineMMS
