import OnlineMMS.FinitePTASRational

namespace OnlineMMS

open scoped BigOperators

/-- Candidate count for one transition layer of the rounded optimizer. -/
def roundedCandidatesAtLayer {m n : ℕ} (w : Fin m → ℕ) (r : Fin m) : ℕ :=
  n * (roundedFrontier n (fun g : Fin r.val => w ⟨m-r.val+g,by
    have := r.isLt
    have := g.isLt
    omega⟩)).length

/-- Count generated candidates, an upper bound on deduplication comparisons
using a scan against the retained list, and the final scoring pass. -/
def roundedPartitionWork {m n : ℕ} (w : Fin m → ℕ) : ℕ :=
  (∑ r, (roundedCandidatesAtLayer (n := n) w r + roundedCandidatesAtLayer (n := n) w r ^ 2)) +
    2 * (n * (roundedFrontier n w).length)

theorem roundedCandidatesAtLayer_le {m n W : ℕ} (w : Fin m → ℕ)
    (hw : ∀ g, w g ≤ W) (r : Fin m) :
    roundedCandidatesAtLayer (n := n) w r ≤ n * (m*W+1)^n := by
  unfold roundedCandidatesAtLayer
  apply Nat.mul_le_mul_left
  apply (roundedFrontier_length_le _ (fun g => hw _)).trans
  apply pow_le_pow_left' _ _
  have hh := Nat.mul_le_mul_right W r.isLt.le
  omega

theorem roundedPartitionWork_le {m n W : ℕ} (w : Fin m → ℕ) (hw : ∀ g, w g ≤ W) :
    roundedPartitionWork (n := n) w ≤
      let C := n * (m*W+1)^n
      m * (C + C^2) + 2*C := by
  let C := n * (m*W+1)^n
  apply add_le_add
  · calc
      _ ≤ ∑ _ : Fin m, (C + C^2) := by
        apply Finset.sum_le_sum
        intro r _
        have h : roundedCandidatesAtLayer (n := n) w r ≤ C :=
          roundedCandidatesAtLayer_le w hw r
        exact add_le_add h (pow_le_pow_left' h _)
      _ = _ := by simp [C]
  · exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (roundedFrontier_length_le w hw))

/-- A polynomial bound for fixed horizon at most five and fixed precision. -/
theorem roundedMMSWork_short {m n L : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (horizon : n ≤ 5) :
    roundedPartitionWork (n := n) (roundedMMSWeights v n L) ≤
      let C := 5 * (2*L*m^2 + 1)^5
      m * (C + C^2) + 2*C := by
  let K := m * (2 * m * L) + 1
  let C := n * K^n
  let C₅ := 5 * (2*L*m^2 + 1)^5
  have hK : K = 2*L*m^2+1 := by dsimp [K]; ring
  have hC : C ≤ C₅ := by
    dsimp [C,C₅]
    rw [← hK]
    apply Nat.mul_le_mul horizon
    exact pow_le_pow_right' (by dsimp [K]; omega) horizon
  refine (roundedPartitionWork_le _ (roundedMMSWeights_le v hv hn)).trans ?_
  exact add_le_add (Nat.mul_le_mul_left _ (add_le_add hC (pow_le_pow_left' hC _))) (Nat.mul_le_mul_left 2 hC)

/-- Polynomial preprocessing-work bound for the executable rational partition algorithm. -/
theorem rationalMMSWork_short {m n L : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (horizon : n ≤ 5) :
    roundedPartitionWork (n := n) (rationalMMSWeights v n L) ≤
      let C := 5 * (2*L*m^2 + 1)^5
      m * (C + C^2) + 2*C := by
  rw [rationalMMSWeights_eq v hv hn]
  have hvR : ∀ g, (0 : ℝ) ≤ (v g : ℝ) := fun g => by exact_mod_cast hv g
  exact roundedMMSWork_short _ hvR hn horizon

end OnlineMMS
