import OnlineMMS.ManuscriptModel

namespace OnlineMMS

open private algorithmInitial from OnlineMMS.General
open private AlgorithmState.finalNext AlgorithmState.sampleNext AlgorithmState.smallNext from OnlineMMS.General

private theorem supply_step {m k r h b : ℕ} {d : Fin k → ℝ} {x y : AlgorithmState m k}
    {t : Fin k} {B : Finset (Fin m)} (hs : AlgorithmState.Step h b d r x t B y) :
    y.remaining = x.remaining \ B ∧ (r=0 → y.remaining=∅) := by
  cases hs <;> simp_all [AlgorithmState.finalNext,AlgorithmState.smallNext,AlgorithmState.sampleNext]

private theorem follows_full {m k n h b : ℕ} {v : Fin k → Fin m → ℝ} {d floor : Fin k → ℝ}
    (p : Policy m k n) (x : AlgorithmState m k) (hx : n=0 → x.remaining=∅)
    (hf : p.Follows (AlgorithmState.Step h b d) x) (hg : p.Guarantees v floor x.remaining) :
    p.FullAllocation x.remaining := by
  induction p generalizing x with
  | done => exact hx rfl
  | @step r B next ih =>
    intro t
    obtain ⟨y,hs,hf'⟩ := hf t
    obtain ⟨hrem,hempty⟩ := supply_step hs
    refine ⟨(hg t).1, ?_⟩
    rw [← hrem]
    exact ih t y hempty hf' (hrem ▸ (hg t).2.2)

/-- Strengthened Theorem 3.1. Every conforming execution itself exhausts the
supply and guarantees both original benchmarks on every branch. -/
theorem algorithm1_full_guarantee {m n k : ℕ} (hn : 0<n) (hk : 0<k)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    (∃ p : Policy m k n, FollowsAlgorithm1 v p) ∧
    ∀ p : Policy m k n, FollowsAlgorithm1 v p →
      p.FullAllocation Finset.univ ∧
      p.Guarantees v (fun t => truncatedShare (v t) n/(2*(bucketMultiplier k:ℝ))) Finset.univ ∧
      p.Guarantees v (fun t => maximinShare (v t) n hn/(2*(bucketMultiplier k:ℝ))) Finset.univ := by
  obtain ⟨hExist,hguar⟩ := general_algorithm1_certified hn hk v hv
  refine ⟨hExist,fun p hp => ⟨?_,hguar p hp,algorithm1_mms_of_follows hn hk v hv p hp⟩⟩
  exact follows_full p (algorithmInitial n v) (by omega) hp (hguar p hp)

end OnlineMMS
