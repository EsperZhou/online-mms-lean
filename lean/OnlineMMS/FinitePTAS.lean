import OnlineMMS.FinitePTASLoads
import OnlineMMS.FiniteFourFive

namespace OnlineMMS

open scoped BigOperators

theorem half_truncatedShare_le_maximinShare {m n : ℕ} (v : Fin m → ℝ)
    (hv : ∀ g, 0 ≤ v g) (hn : 0 < n) :
    truncatedShare v n / 2 ≤ maximinShare v n hn := by
  by_cases hd : 0 < truncatedShare v n
  · have h : HasPaymentPartition (normalizedWeight v n) Finset.univ n (1/2) := by
      apply partition_from_bounded_mass _ _ hn (by norm_num)
      · intro g _
        simpa using normalizedWeight_le_one v hd g
      · rw [bundleValue, sum_normalizedWeight v hv hn hd]
        linarith
    obtain ⟨p,hp⟩ := transfer_weight_partition v (normalizedWeight v n) Finset.univ
      hd.le (truncatedShare_mul_normalizedWeight_le v hd) h
    calc
      truncatedShare v n / 2 = truncatedShare v n * (1/2) := by ring
      _ ≤ partitionMin v hn p := by
        apply Finset.le_inf'
        intro j _
        exact hp j
      _ ≤ _ := partitionMin_le_maximinShare v hn p
  · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hd) (by norm_num)).trans
      (maximinShare_nonnegative v hv hn)

/-- The DP uses weights obtained by scaling the normalized capped values and rounding down. -/
noncomputable def roundedMMSWeights {m : ℕ} (v : Fin m → ℝ) (n L : ℕ) (g : Fin m) : ℕ :=
  ⌊(2*m*L : ℕ) * normalizedWeight v n g⌋₊

theorem roundedMMSWeights_le {m n L : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (g : Fin m) : roundedMMSWeights v n L g ≤ 2*m*L := by
  apply Nat.floor_le_of_le
  apply mul_le_of_le_one_right (Nat.cast_nonneg _)
  by_cases hd : 0 < truncatedShare v n
  · exact normalizedWeight_le_one v hd g
  · have hz := le_antisymm (le_of_not_gt hd) (truncatedShare_spec v hv hn).1.1
    simp [normalizedWeight, hz]

private theorem roundedLoad_cast_eq {m n : ℕ} (w : Fin m → ℕ) (p : Fin m → Fin n) (j : Fin n) :
    (roundedLoads w p j : ℝ) = ∑ g ∈ Finset.univ.filter (fun g => p g = j), (w g : ℝ) := by
  simp [roundedLoads, Nat.cast_sum, Finset.sum_filter, apply_ite]

private theorem roundedLoadScore_attained {n : ℕ} (hn : 0 < n) (s : Fin n → ℕ) :
    ∃ j, roundedLoadScore hn s = s j := by
  unfold roundedLoadScore
  obtain ⟨j,_, hj⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) ⟨⟨0,hn⟩,Finset.mem_univ _⟩ s
  exact ⟨j,hj⟩

/-- The rounded-load optimizer attains at least (1 - 1/L) times MMS in every part. -/
theorem roundedMMSAssignment_guarantee {m n L : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (hL : 0 < L) :
    ∀ j, (1 - (1 : ℝ)/L) * maximinShare v n hn ≤
      partitionValue v (roundedOptimalAssignment hn (roundedMMSWeights v n L)) j := by
  let d := truncatedShare v n
  let μ := maximinShare v n hn
  let a := roundedMMSWeights v n L
  let p := roundedOptimalAssignment hn a
  intro j
  change (1 - (1 : ℝ)/L) * μ ≤ partitionValue v p j
  have hμd : μ ≤ d := maximinShare_le_truncatedShare v hv hn
  have hμ : 0 ≤ μ := maximinShare_nonnegative v hv hn
  by_cases hd : 0 < d
  · have hm : 0 < m := by
      by_contra! hnz
      interval_cases m
      have hsum := sum_normalizedWeight v hv hn hd
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      simp at hsum
      linarith
    let S : ℝ := ((2*m*L : ℕ) : ℝ)
    let δ := d / S
    have hS : 0 < S := by
      dsimp [S]
      positivity
    have hδ : 0 ≤ δ := (div_pos hd hS).le
    have hcancel : δ * S = d := div_mul_cancel₀ _ hS.ne'
    have hδS (g : Fin m) : δ * (S * normalizedWeight v n g) = min (v g) d := by
      rw [← mul_assoc, hcancel, normalizedWeight]
      exact mul_div_cancel₀ _ hd.ne'
    have hround (g : Fin m) : δ * a g ≤ min (v g) d := by
      rw [← hδS g]
      apply mul_le_mul_of_nonneg_left _ hδ
      exact Nat.floor_le (mul_nonneg hS.le (normalizedWeight_nonneg v hv hd g))
    have herr (g : Fin m) : min (v g) d ≤ δ * a g + δ := by
      rw [← hδS g, show δ * (a g : ℝ) + δ = δ * ((a g : ℝ)+1) by ring]
      exact mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one (S * normalizedWeight v n g)).le hδ
    obtain ⟨p₀,hp₀⟩ := maximinShare_attained v hn
    obtain ⟨j₀,hj₀⟩ := roundedLoadScore_attained hn (roundedLoads a p₀)
    let R := Finset.univ.filter (fun g => p₀ g = j₀)
    have hR : μ ≤ ∑ g ∈ R, min (v g) d := by
      have hbase : μ ≤ partitionValue v p₀ j₀ := by
        rw [show μ = partitionMin v hn p₀ by exact hp₀.symm]
        exact partitionMin_le_partitionValue v hn p₀ j₀
      exact (cap_preserves_threshold v hv R hμ hbase).trans
        (Finset.sum_le_sum (fun g _ => min_le_min_left _ hμd))
    have hcard : (R.card : ℝ) ≤ m := by
      exact_mod_cast (Finset.card_le_univ R).trans_eq (Fintype.card_fin m)
    have hload : roundedLoads a p₀ j₀ ≤ roundedLoads a p j := by
      rw [← hj₀]
      exact (roundedOptimalAssignment_max hn a p₀).trans (roundedLoadScore_le hn _ j)
    have hpartition : δ * roundedLoads a p j ≤ partitionValue v p j := by
      rw [roundedLoad_cast_eq, Finset.mul_sum]
      exact Finset.sum_le_sum (fun g _ => (hround g).trans (min_le_left _ _))
    have hscale : (m : ℝ) * δ = d/(2*L) := by
      dsimp [δ,S]
      push_cast
      have hmR : (m : ℝ) ≠ 0 := by positivity
      have hLR : (L : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    have hμbound : μ ≤ partitionValue v p j + d/(2*L) := by
      calc
        μ ≤ ∑ g ∈ R, min (v g) d := hR
        _ ≤ ∑ g ∈ R, (δ * a g + δ) := Finset.sum_le_sum (fun g _ => herr g)
        _ = δ * roundedLoads a p₀ j₀ + (R.card : ℝ) * δ := by
          rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,roundedLoad_cast_eq,Finset.mul_sum]
        _ ≤ partitionValue v p j + (m : ℝ)*δ := by
          exact add_le_add
            ((mul_le_mul_of_nonneg_left (by exact_mod_cast hload) hδ).trans hpartition)
            (mul_le_mul_of_nonneg_right hcard hδ)
        _ = _ := by rw [hscale]
    have herror : d/(2*L) ≤ μ/L := by
      rw [← div_div]
      exact div_le_div_of_nonneg_right (half_truncatedShare_le_maximinShare v hv hn)
        (Nat.cast_nonneg _)
    calc
      (1-(1 : ℝ)/L)*μ = μ - μ/L := by ring
      _ ≤ _ := by linarith
  · have hz : μ = 0 := le_antisymm (hμd.trans (le_of_not_gt hd)) hμ
    rw [hz,mul_zero]
    exact Finset.sum_nonneg (fun g _ => hv g)

theorem roundedMMSPartition {m n L : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (hL : 0 < L) :
    HasPaymentPartition v Finset.univ n ((1 - (1 : ℝ)/L) * maximinShare v n hn) :=
  ⟨roundedOptimalAssignment hn (roundedMMSWeights v n L), roundedMMSAssignment_guarantee v hv hn hL⟩

end OnlineMMS
