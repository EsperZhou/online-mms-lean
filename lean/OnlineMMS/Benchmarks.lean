import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! The original TPS and MMS for one additive valuation on a finite set of goods. -/

namespace OnlineMMS

open scoped BigOperators
open Set

noncomputable section

variable {m n : ℕ}

def tpsFeasible (v : Fin m → ℝ) (n : ℕ) : Set ℝ :=
  {q | 0 ≤ q ∧ (n : ℝ) * q ≤ ∑ g, min (v g) q}

noncomputable def truncatedShare (v : Fin m → ℝ) (n : ℕ) : ℝ :=
  sSup (tpsFeasible v n)

/-- An assignment to labeled recipients represents a partition allowing empty parts. -/
def partitionValue (v : Fin m → ℝ) (p : Fin m → Fin n) (j : Fin n) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g => p g = j), v g

noncomputable def partitionMin (v : Fin m → ℝ) (hn : 0 < n)
    (p : Fin m → Fin n) : ℝ :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Finset.univ.inf' Finset.univ_nonempty (partitionValue v p)

noncomputable def maximinShare (v : Fin m → ℝ) (n : ℕ) (hn : 0 < n) : ℝ := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.univ.sup' Finset.univ_nonempty (partitionMin v hn)

theorem maximinShare_attained (v : Fin m → ℝ) (hn : 0 < n) :
    ∃ p : Fin m → Fin n, partitionMin v hn p = maximinShare v n hn := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (partitionMin v hn)
  exact ⟨p, hp.symm⟩

theorem partitionMin_le_maximinShare (v : Fin m → ℝ) (hn : 0 < n)
    (p : Fin m → Fin n) : partitionMin v hn p ≤ maximinShare v n hn := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.le_sup' (partitionMin v hn) (Finset.mem_univ p)

theorem partitionMin_nonneg (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) (hn : 0 < n)
    (p : Fin m → Fin n) : 0 ≤ partitionMin v hn p := by
  apply Finset.le_inf'
  intro j _
  exact Finset.sum_nonneg fun g _ => hv g

theorem partitionMin_le_partitionValue (v : Fin m → ℝ) (hn : 0 < n)
    (p : Fin m → Fin n) (j : Fin n) : partitionMin v hn p ≤ partitionValue v p j :=
  Finset.inf'_le (partitionValue v p) (Finset.mem_univ j)

theorem truncatedShare_spec (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) (hn : 0 < n) :
    IsGreatest (tpsFeasible v n) (truncatedShare v n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hne : (tpsFeasible v n).Nonempty := by
    refine ⟨0, le_rfl, ?_⟩
    have hmin (g : Fin m) : min (v g) 0 = 0 := min_eq_right (hv g)
    simp [hmin]
  have hinterval : tpsFeasible v n ⊆ Icc 0 ((∑ g, v g) / n) := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    apply (le_div_iff₀ hnR).2
    rw [mul_comm]
    exact hq.2.trans (Finset.sum_le_sum (fun _ _ => min_le_left _ _))
  have hclosed : IsClosed (tpsFeasible v n) := by
    change IsClosed (Ici (0 : ℝ) ∩ {q : ℝ | (n : ℝ) * q ≤ ∑ g, min (v g) q})
    exact isClosed_Ici.inter (isClosed_le (continuous_const.mul continuous_id)
      (continuous_finset_sum _ (fun _ _ => continuous_const.min continuous_id)))
  obtain ⟨d, hd⟩ := (isCompact_Icc.of_isClosed_subset hclosed hinterval).exists_isGreatest hne
  simpa only [truncatedShare, hd.csSup_eq] using hd

theorem truncatedShare_saturates (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) (hn : 0 < n) :
    (∑ g, min (v g) (truncatedShare v n)) = (n : ℝ) * truncatedShare v n := by
  let d := truncatedShare v n
  let total := ∑ g, min (v g) d
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd := truncatedShare_spec v hv hn
  apply le_antisymm _ hd.1.2
  change total ≤ (n : ℝ) * d
  by_contra! hstrict
  let q := d + (total - (n : ℝ) * d) / n
  have hdq : d < q := lt_add_of_pos_right _ (div_pos (sub_pos.mpr hstrict) hnR)
  have hqtotal : (n : ℝ) * q = total := by
    dsimp [q]
    field_simp [ne_of_gt hnR]
    ring
  have hqfeas : q ∈ tpsFeasible v n := by
    refine ⟨hd.1.1.trans hdq.le, ?_⟩
    rw [hqtotal]
    exact Finset.sum_le_sum fun _ _ => min_le_min_left _ hdq.le
  exact (not_le_of_gt hdq) (hd.2 hqfeas)

theorem cap_preserves_threshold (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (s : Finset (Fin m)) {q : ℝ} (hq : 0 ≤ q) (hs : q ≤ ∑ g ∈ s, v g) :
    q ≤ ∑ g ∈ s, min (v g) q := by
  by_cases hlarge : ∃ g ∈ s, q ≤ v g
  · obtain ⟨g, hg, hqg⟩ := hlarge
    have hsingle :
        min (v g) q ≤ ∑ i ∈ s, min (v i) q :=
      Finset.single_le_sum (fun i _ => le_min (hv i) hq) hg
    simpa [min_eq_right hqg] using hsingle
  · convert hs using 1
    apply Finset.sum_congr rfl
    intro g hg
    exact min_eq_left (le_of_not_ge (fun h => hlarge ⟨g, hg, h⟩))

theorem maximinShare_le_truncatedShare (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) : maximinShare v n hn ≤ truncatedShare v n := by
  let q := maximinShare v n hn
  obtain ⟨p, hp⟩ := maximinShare_attained v hn
  have hq : 0 ≤ q := by
    change 0 ≤ maximinShare v n hn
    rw [← hp]
    exact partitionMin_nonneg v hv hn p
  have hparts (j : Fin n) : q ≤ ∑ g ∈ Finset.univ.filter (fun g => p g = j), min (v g) q := by
    apply cap_preserves_threshold v hv _ hq
    change maximinShare v n hn ≤ partitionValue v p j
    rw [← hp]
    exact partitionMin_le_partitionValue v hn p j
  apply (truncatedShare_spec v hv hn).2
  refine ⟨hq, ?_⟩
  calc
    (n : ℝ) * q = ∑ _j : Fin n, q := by simp [nsmul_eq_mul]
    _ ≤ ∑ j : Fin n, ∑ g ∈ Finset.univ.filter (fun g => p g = j), min (v g) q :=
      Finset.sum_le_sum (fun j _ => hparts j)
    _ = ∑ g, min (v g) q := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp

noncomputable def normalizedWeight (v : Fin m → ℝ) (n : ℕ) (g : Fin m) : ℝ :=
  min (v g) (truncatedShare v n) / truncatedShare v n

theorem normalizedWeight_eq (v : Fin m → ℝ)
    (hd : 0 < truncatedShare v n) (g : Fin m) :
    normalizedWeight v n g = min 1 (v g / truncatedShare v n) := by
  rcases le_total (v g) (truncatedShare v n) with h | h
  · rw [normalizedWeight, min_eq_left h, min_eq_right ((div_le_one₀ hd).2 h)]
  · rw [normalizedWeight, min_eq_right h, div_self hd.ne',
      min_eq_left ((one_le_div₀ hd).2 h)]

theorem normalizedWeight_nonneg (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hd : 0 < truncatedShare v n) (g : Fin m) : 0 ≤ normalizedWeight v n g :=
  div_nonneg (le_min (hv g) hd.le) hd.le

theorem normalizedWeight_le_one (v : Fin m → ℝ)
    (hd : 0 < truncatedShare v n) (g : Fin m) : normalizedWeight v n g ≤ 1 := by
  rw [normalizedWeight, div_le_iff₀ hd, one_mul]
  exact min_le_right _ _

theorem truncatedShare_mul_normalizedWeight_le (v : Fin m → ℝ)
    (hd : 0 < truncatedShare v n) (g : Fin m) :
    truncatedShare v n * normalizedWeight v n g ≤ v g := by
  rw [normalizedWeight, mul_div_cancel₀ _ (ne_of_gt hd)]
  exact min_le_left _ _

theorem sum_normalizedWeight (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (hd : 0 < truncatedShare v n) :
    (∑ g, normalizedWeight v n g) = (n : ℝ) := by
  simp only [normalizedWeight, ← Finset.sum_div, truncatedShare_saturates v hv hn,
    mul_div_cancel_right₀ _ (ne_of_gt hd)]

end

end OnlineMMS
