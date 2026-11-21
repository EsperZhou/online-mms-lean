import OnlineMMS.ObliviousPairCounting
import OnlineMMS.RandomBenchmark

namespace OnlineMMS

/-- The binary pair instance bounds every feasible randomized fraction.
The second type is fixed independently of the sampled policy tree. -/
theorem oblivious_pair_upper {k : ℕ} (hk : 7 ≤ k) {δ x : ℝ} (hδ : 0 ≤ δ)
    (attainable : ObliviousAttainable k δ x) :
    x ≤ 1 / (pairParameter k : ℝ) + 2 * Real.sqrt δ := by
  classical
  obtain ⟨hp, fit, _⟩ := pairParameter_spec hk
  have hp' : 0 < pairParameter k := by omega
  by_cases positive : 0 < x
  · obtain ⟨v, first, binary, count⟩ := ObliviousPair.failure_count_bound fit
    have hv (t g) : 0 ≤ v t g := by
      rcases binary t g with h | h <;> simp [h]
    obtain ⟨D, success⟩ := attainable.2 2 (by decide) _ v hv
    apply ObliviousPair.fraction_le_of_count hp' positive hδ
    apply count positive attainable.1.2 D.mass D.nonneg D.total D.policy
    intro s
    let seq := ObliviousPair.pairSeq first s
    let G (i : Fin D.size) := (D.policy i).GuaranteesSequence v
      (fun t => x * maximinShare (v t) 2 (by decide)) Finset.univ seq
    have partition : (∑ i, if G i then (0:ℝ) else D.mass i) +
        (∑ i, if G i then D.mass i else 0) = 1 := by
      rw [← Finset.sum_add_distrib, ← D.total]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : G i <;> simp [h]
    have hsuccess := success seq
    change 1 - δ ≤ ∑ i, if G i then D.mass i else 0 at hsuccess
    change (∑ i, if G i then (0:ℝ) else D.mass i) ≤ δ
    linarith
  · exact (le_of_not_gt positive).trans (by positivity)

/-- The same explicit pair bound holds for the supremum, even if a maximizing
lottery has not been chosen. -/
theorem alphaOblivious_pair_upper {k : ℕ} (hk : 7 ≤ k) {δ : ℝ} (hδ : 0 ≤ δ) :
    alphaOblivious k δ ≤ 1 / (pairParameter k : ℝ) + 2 * Real.sqrt δ := by
  apply Real.sSup_le _ (by positivity)
  exact fun _ H => oblivious_pair_upper hk hδ H

/-- A common absolute constant works for every positive type count and
every nonnegative failure budget, including zero. -/
theorem alphaOblivious_upper {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 ≤ δ) :
    alphaOblivious k δ ≤ 5 * max (1 / Real.sqrt (k : ℝ)) (Real.sqrt δ) := by
  let scale := max (1 / Real.sqrt (k : ℝ)) (Real.sqrt δ)
  have hroot : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hdet : 1 / Real.sqrt (k : ℝ) ≤ scale := le_max_left _ _
  have hprob : Real.sqrt δ ≤ scale := le_max_right _ _
  have hscale : 0 ≤ scale := (Real.sqrt_nonneg δ).trans hprob
  apply Real.sSup_le _ (by change 0 ≤ 5 * scale; positivity)
  intro x H
  have attainable : ObliviousAttainable k δ x := H
  change x ≤ 5 * scale
  by_cases hk7 : 7 ≤ k
  · let p := pairParameter k
    have hp : (2 : ℝ) ≤ p := by exact_mod_cast (pairParameter_spec hk7).1
    have hp0 : 0 < (p : ℝ) := by linarith
    have hfit := (pairParameter_estimate hk7).1
    rw [Real.sqrt_div (Nat.cast_nonneg k)] at hfit
    have hs2 : 0 < Real.sqrt (2 : ℝ) := by positivity
    have hs2max : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hkp : Real.sqrt (k : ℝ) ≤ 3 * p := calc
      _ ≤ ((p : ℝ) + 1) * Real.sqrt 2 := (div_le_iff₀ hs2).mp (by linarith)
      _ ≤ ((p : ℝ) + 1) * 2 := mul_le_mul_of_nonneg_left hs2max (by linarith)
      _ ≤ _ := by linarith
    have hinv : 1 / (p : ℝ) ≤ 3 * (1 / Real.sqrt (k : ℝ)) := by
      rw [mul_one_div]
      exact (div_le_div_iff₀ hp0 hroot).mpr (by simpa using hkp)
    have hpair := oblivious_pair_upper hk7 hδ attainable
    change x ≤ 1 / (p : ℝ) + 2 * Real.sqrt δ at hpair
    linarith
  · have hsmall : (k : ℝ) ≤ 6 := by exact_mod_cast (show k ≤ 6 by omega)
    have hrootSmall : Real.sqrt (k : ℝ) ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    have hfloor : 1 ≤ 3 * (1 / Real.sqrt (k : ℝ)) := by
      rw [mul_one_div]
      exact (le_div_iff₀ hroot).mpr (by simpa using hrootSmall)
    linarith [attainable.1.2]

end OnlineMMS
