import OnlineMMS.RationalTPS
import Mathlib.Order.Interval.Finset.Fin

namespace OnlineMMS

open private tps_high_count from OnlineMMS.RationalTPS

/-- The original TPS is the least uncapped residual average over deletions of fewer
than the number of agents. This formulation makes no ordering assumption on the goods. -/
theorem truncatedShare_least_residual {m n : ℕ} (hn : 0 < n)
    (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) :
    IsLeast {y : ℝ | ∃ S : Finset (Fin m), S.card < n ∧
      y = (∑ g ∈ Sᶜ, v g) / ((n : ℝ) - S.card)} (truncatedShare v n) := by
  classical
  let d := truncatedShare v n
  have hsplit (S : Finset (Fin m)) :
      (∑ g ∈ S, min (v g) d) + (∑ g ∈ Sᶜ, min (v g) d) = (n : ℝ) * d := by
    rw [Finset.sum_add_sum_compl, truncatedShare_saturates v hv hn]
  constructor
  · let S := Finset.univ.filter (fun g => d < v g)
    have hc : S.card < n := tps_high_count hn hv
    have hden : (0 : ℝ) < n - (S.card : ℝ) := sub_pos.mpr (by exact_mod_cast hc)
    refine ⟨S, hc, (eq_div_iff hden.ne').mpr ?_⟩
    have h1 : (∑ g ∈ S, min (v g) d) = S.card * d := by
      calc
        _ = ∑ _g ∈ S, d := Finset.sum_congr rfl fun g hg =>
          min_eq_right (le_of_lt (Finset.mem_filter.mp hg).2)
        _ = _ := by simp
    have h2 : (∑ g ∈ Sᶜ, min (v g) d) = ∑ g ∈ Sᶜ, v g := by
      apply Finset.sum_congr rfl
      intro g hg
      apply min_eq_left
      simpa [S] using hg
    have H := hsplit S
    rw [h1, h2] at H
    change d * _ = _
    linarith only [H]
  · rintro y ⟨S, hc, rfl⟩
    apply (le_div_iff₀ (sub_pos.mpr (by exact_mod_cast hc) :
      (0 : ℝ) < n - (S.card : ℝ))).mpr
    have h1 : (∑ g ∈ S, min (v g) d) ≤ S.card * d := by
      simpa using (Finset.sum_le_sum (s := S) fun g _ => min_le_right (v g) d)
    have h2 : (∑ g ∈ Sᶜ, min (v g) d) ≤ ∑ g ∈ Sᶜ, v g :=
      Finset.sum_le_sum fun g _ => min_le_left (v g) d
    change d * _ ≤ _
    linarith only [hsplit S, h1, h2]

private theorem prefix_card {m c : ℕ} (hc : c ≤ m) :
    (Finset.univ.filter (fun i : Fin m => i.val < c)).card = c := by
  by_cases hw : c < m
  · have h : Finset.univ.filter (fun i : Fin m => i.val < c) = Finset.Iio (⟨c, hw⟩ : Fin m) := by
      ext i
      simp [Fin.lt_def]
    rw [h, Fin.card_Iio]
  · have hm : c = m := by omega
    subst c
    simp

/-- Lemma 2.1. For a decreasing enumeration of item values, deleting the first
`c` goods gives the suffix sum in the manuscript, with `0 ≤ c ≤ m` and `c < n`. -/
theorem sorted_tps_closed_form {m n : ℕ} (hn : 0 < n) (v : Fin m → ℝ)
    (hv : ∀ g, 0 ≤ v g) (hsort : Antitone v) :
    IsLeast {y : ℝ | ∃ c : ℕ, c ≤ m ∧ c < n ∧
      y = (∑ g ∈ Finset.univ.filter (fun g : Fin m => c ≤ g.val), v g) /
        ((n : ℝ) - c)} (truncatedShare v n) := by
  classical
  let d := truncatedShare v n
  let S := Finset.univ.filter (fun g => d < v g)
  let c := S.card
  have hhigh : S.card < n := tps_high_count hn hv
  have hm : c ≤ m := by simpa [c] using S.card_le_univ
  have hpre : S = Finset.univ.filter (fun g : Fin m => g.val < c) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      have hsub : Finset.Iic i ⊆ S := fun j hj => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hi).2).trans_le (hsort (Finset.mem_Iic.mp hj))⟩
      have hb := Finset.card_le_card hsub
      rw [Fin.card_Iic] at hb
      exact hb
    · intro hi
      by_contra hmem
      have hval : v i ≤ d := by simpa [S] using hmem
      have hsub : S ⊆ Finset.Iio i := by
        intro j hj
        exact Finset.mem_Iio.mpr (lt_of_not_ge (fun hij =>
          (not_lt_of_ge ((hsort hij).trans hval)) (Finset.mem_filter.mp hj).2))
      have hb := Finset.card_le_card hsub
      rw [Fin.card_Iio] at hb
      exact (not_lt_of_ge hb) hi
  have hcomp (a : ℕ) :
      (Finset.univ.filter (fun g : Fin m => g.val < a))ᶜ =
      Finset.univ.filter (fun g : Fin m => a ≤ g.val) := by ext g; simp
  have hb := truncatedShare_least_residual hn v hv
  constructor
  · refine ⟨c, hm, hhigh, ?_⟩
    have hden : (0 : ℝ) < n - (c : ℝ) := sub_pos.mpr (by exact_mod_cast hhigh)
    apply (eq_div_iff hden.ne').mpr
    have hsat := truncatedShare_saturates v hv hn
    have hparts := Finset.sum_add_sum_compl S (fun g => min (v g) d)
    have h1 : (∑ g ∈ S, min (v g) d) = c * d := by
      calc
        _ = ∑ _g ∈ S, d := Finset.sum_congr rfl fun g hg => min_eq_right (le_of_lt (Finset.mem_filter.mp hg).2)
        _ = _ := by simp [c]
    have h2 : (∑ g ∈ Sᶜ, min (v g) d) = ∑ g ∈ Sᶜ, v g := by
      exact Finset.sum_congr rfl fun g hg => min_eq_left (by simpa [S] using hg)
    rw [h1, h2, hpre, hcomp] at hparts
    change d * _ = _
    linarith only [hparts, hsat]
  · rintro y ⟨a, ham, han, rfl⟩
    apply hb.2
    refine ⟨Finset.univ.filter (fun g : Fin m => g.val < a), ?_, ?_⟩
    · rwa [prefix_card ham]
    · rw [hcomp, prefix_card ham]

end OnlineMMS
