import OnlineMMS.RationalFixedWidthQuadratic

namespace OnlineMMS.RationalFixedWidth

open BucketBitComplexity
open RationalAlgorithm1 (materialize materialize_apply)

/-- The quadratic estimator uses one cumulative weight per type. -/
def compactQuadraticRule {m k : ℕ} (h : ℕ) : SampleRule m k (Fin k → ℚ) := fun x _ bs =>
  let pre := materialize (quadraticPrefixQ h x.stats)
  let gs := selectQ x.weight 1 1 0 (fun _ => 0) [pre] bs
  (gs, materialize (fun i => x.stats i + (gs.map (x.weight i)).sum))

private def collapse {m k : ℕ} (x : State m k (Fin k → List ℚ)) : State m k (Fin k → ℚ) :=
  ⟨x.remaining, x.samples, x.weight, materialize (fun i => (x.stats i).sum)⟩

private theorem collapse_small {m k : ℕ} (r : ℕ) (x : State m k (Fin k → List ℚ))
    (B : Finset (Fin m)) :
    collapse (small r x B) = small r (collapse x) B := rfl

private theorem collapse_rule {m k : ℕ} (h : ℕ) (x : State m k (Fin k → List ℚ)) (t : Fin k)
    (bs : List (Finset (Fin m))) :
    (compactQuadraticRule h (collapse x) t bs).1 = (quadraticRule h x t bs).1 ∧
    collapse (sample x (quadraticRule h x t bs).1 (quadraticRule h x t bs).2) =
      sample (collapse x) (compactQuadraticRule h (collapse x) t bs).1
        (compactQuadraticRule h (collapse x) t bs).2 := by
  constructor
  · rfl
  · simp only [compactQuadraticRule, quadraticRule, collapse, sample]
    congr 1
    funext t
    simp only [materialize_apply, List.sum_append]

private theorem collapse_advance {m k : ℕ} (h : ℕ) (β : ℚ) (d : Fin k → ℚ)
    (r : ℕ) (x : State m k (Fin k → List ℚ)) (t : Fin k) :
    let out := advance h β d (quadraticRule h) r x t
    advance h β d (compactQuadraticRule h) r (collapse x) t = (out.1, collapse out.2) := by
  by_cases hr : r = 0
  · simp [advance, hr, collapse]
  by_cases ht : 0 < d t
  · let eligible := x.remaining.filter (fun g => β ≤ x.weight t g)
    have he : (collapse x).remaining.filter (fun g => β ≤ (collapse x).weight t g) = eligible := rfl
    simp only [advance, if_neg hr, if_pos ht, he]
    by_cases hne : eligible.Nonempty
    · rw [dif_pos hne, dif_pos hne]
      rw [collapse_small]
    · rw [dif_neg hne, dif_neg hne]
      let bs := RationalAlgorithm1.rationalBuckets (x.weight t) (h * (r + 1 + x.samples)) x.remaining
      have hrel := collapse_rule h x t bs
      change ((compactQuadraticRule h (collapse x) t bs).1.toFinset, _) =
        ((quadraticRule h x t bs).1.toFinset, _)
      exact Prod.ext (congrArg List.toFinset hrel.1) hrel.2.symm
  · simp only [advance, if_neg hr, if_neg ht, collapse_small]

private theorem collapse_policy {m k : ℕ} (h : ℕ) (β : ℚ) (d : Fin k → ℚ) (r : ℕ)
    (x : State m k (Fin k → List ℚ)) :
    policyFrom h β d (compactQuadraticRule h) r (collapse x) =
      policyFrom h β d (quadraticRule h) r x := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
    unfold policyFrom
    congr 1
    · funext t
      rw [collapse_advance]
    · funext t
      rw [collapse_advance]
      exact ih _

/-- Implementation of the supplementary quadratic estimator with per-type totals.
The next theorem identifies it with the version that stores the full history. -/
def compactQuadraticEstimatorPolicy {m k n : ℕ} (v : Fin k → Fin m → ℚ) : Policy m k n :=
  let h := FixedWidth.quadraticParameterQ k
  let d := materialize (fun t => rationalTPS (v t) n)
  policyFrom h (1 / (8 * (h : ℚ))) d (compactQuadraticRule h) n
    (initialWithTPS v d (fun _ : Fin k => (0 : ℚ)))

theorem compactQuadraticEstimatorPolicy_eq {m k n : ℕ} (v : Fin k → Fin m → ℚ) :
    compactQuadraticEstimatorPolicy (n := n) v = quadraticEstimatorPolicy (n := n) v := by
  unfold compactQuadraticEstimatorPolicy quadraticEstimatorPolicy quadraticPolicy
  dsimp only
  let d := materialize (fun t => rationalTPS (v t) n)
  have he : collapse (initialWithTPS v d (fun _ : Fin k => ([] : List ℚ))) =
      initialWithTPS v d (fun _ : Fin k => (0 : ℚ)) := by
    simp only [collapse, initialWithTPS]
    congr 1
    funext i
    simp
  change policyFrom _ _ d _ n (initialWithTPS v d (fun _ : Fin k => (0 : ℚ))) =
    policyFrom _ _ d _ n (initialWithTPS v d (fun _ : Fin k => ([] : List ℚ)))
  rw [← he]
  exact collapse_policy _ _ _ _ _

theorem compactQuadraticEstimatorPolicy_guarantees {m k n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (compactQuadraticEstimatorPolicy (n := n) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => truncatedShare (fun g => (v t g : ℝ)) n /
        (8 * (FixedWidth.quadraticMultiplier k : ℝ))) Finset.univ := by
  rw [compactQuadraticEstimatorPolicy_eq]
  exact quadraticEstimatorPolicy_guarantees hn hk v hv

end OnlineMMS.RationalFixedWidth
