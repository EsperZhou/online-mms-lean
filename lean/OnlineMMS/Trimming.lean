import OnlineMMS.Model
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

namespace OnlineMMS

/-- Trimming toward a total below the current weight. The definition scans the
    supplied good order, using up the amount to remove before moving on. -/
private noncomputable def trimmedListWeight {G : Type*} [DecidableEq G]
    (w : G → ℝ) : List G → ℝ → G → ℝ
  | [], _, _ => 0
  | g :: gs, remove, x =>
      if x = g then max 0 (w g - remove)
      else trimmedListWeight w gs (max 0 (remove - w g)) x

private theorem trimmedListWeight_bounds {G : Type*} [DecidableEq G]
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (gs : List G) (d : ℝ)
    (hd : 0 ≤ d) (x : G) :
    0 ≤ trimmedListWeight w gs d x ∧ trimmedListWeight w gs d x ≤ w x := by
  induction gs generalizing d with
  | nil => exact ⟨le_rfl, hw x⟩
  | cons g gs ih =>
    by_cases hx : x = g
    · subst x
      simp only [trimmedListWeight, if_pos rfl]
      exact ⟨le_max_left _ _, max_le (hw g) (sub_le_self _ hd)⟩
    · simp only [trimmedListWeight, if_neg hx]
      exact ih _ (le_max_left _ _)

private theorem trimmedListWeight_sum {G : Type*} [DecidableEq G]
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (gs : List G) (hnodup : gs.Nodup)
    (d : ℝ) (hd : 0 ≤ d) :
    ∑ g ∈ gs.toFinset, trimmedListWeight w gs d g =
      max 0 ((∑ g ∈ gs.toFinset, w g) - d) := by
  induction gs generalizing d with
  | nil => simp [max_eq_left (neg_nonpos.mpr hd)]
  | cons g gs ih =>
    have hnot : g ∉ gs := (List.nodup_cons.mp hnodup).1
    have htail := (List.nodup_cons.mp hnodup).2
    have hg : g ∉ gs.toFinset := by simpa using hnot
    simp only [List.toFinset_cons, Finset.sum_insert hg]
    rw [show trimmedListWeight w (g :: gs) d g = max 0 (w g - d) by
      simp [trimmedListWeight]]
    have htailSum :
        (∑ x ∈ gs.toFinset, trimmedListWeight w (g :: gs) d x) =
          ∑ x ∈ gs.toFinset, trimmedListWeight w gs (max 0 (d - w g)) x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hne : x ≠ g := by
        rintro rfl
        exact hg hx
      simp [trimmedListWeight, hne]
    rw [htailSum, ih htail _ (le_max_left _ _)]
    have hsum : 0 ≤ ∑ x ∈ gs.toFinset, w x :=
      Finset.sum_nonneg (fun x _ => hw x)
    by_cases h : w g ≤ d
    · rw [max_eq_left (sub_nonpos.mpr h), max_eq_right (sub_nonneg.mpr h), zero_add]
      congr 1
      linarith
    · have h' : d ≤ w g := le_of_lt (lt_of_not_ge h)
      rw [max_eq_right (sub_nonneg.mpr h'), max_eq_left (sub_nonpos.mpr h'), sub_zero,
        max_eq_right hsum, max_eq_right (by linarith : 0 ≤ w g + (∑ x ∈ gs.toFinset, w x) - d)]
      linarith

/-- Trim the remaining goods in increasing order of their fixed indices.
    The scan exhausts one good's weight before removing weight from the next. -/
noncomputable def trimWeights {m : ℕ} (remaining : Finset (Fin m))
    (w : Fin m → ℝ) (cap : ℝ) : Fin m → ℝ :=
  trimmedListWeight w (remaining.sort (· ≤ ·)) (max 0 (bundleValue w remaining - cap))

/-- Fixed-order trimming maintains pointwise domination and reaches the cap
    whenever the original total is at least the cap. -/
theorem trimWeights_spec {m : ℕ} (remaining : Finset (Fin m))
    (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g) (cap : ℝ) (hcap : 0 ≤ cap) :
    (∀ g, 0 ≤ trimWeights remaining w cap g ∧ trimWeights remaining w cap g ≤ w g) ∧
      bundleValue (trimWeights remaining w cap) remaining = min (bundleValue w remaining) cap := by
  let gs := remaining.sort (· ≤ ·)
  have hgs : gs.toFinset = remaining := Finset.sort_toFinset _ _
  have hnodup : gs.Nodup := Finset.sort_nodup _ _
  let total := bundleValue w remaining
  let removal := max 0 (total - cap)
  refine ⟨fun g => trimmedListWeight_bounds w hw gs removal (le_max_left _ _) g, ?_⟩
  have hsum := trimmedListWeight_sum w hw gs hnodup removal (le_max_left _ _)
  rw [hgs] at hsum
  change bundleValue (trimmedListWeight w gs removal) remaining = max 0 (total - removal) at hsum
  change bundleValue (trimmedListWeight w gs removal) remaining = min total cap
  rw [hsum]
  have htotal : 0 ≤ total := Finset.sum_nonneg (fun g _ => hw g)
  by_cases hc : total ≤ cap
  · simp [removal, max_eq_left (sub_nonpos.mpr hc), max_eq_right htotal, min_eq_left hc]
  · have hle : cap ≤ total := le_of_lt (lt_of_not_ge hc)
    have hsimpl : total - removal = cap := by
      dsimp [removal]
      rw [max_eq_right (sub_nonneg.mpr hle)]
      linarith
    rw [hsimpl, max_eq_right hcap, min_eq_right hle]

/-- We can trim to any nonnegative cap, maintaining pointwise domination. -/
theorem can_trim {m : ℕ} (remaining : Finset (Fin m))
    (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g) (cap : ℝ) (hcap : 0 ≤ cap) :
    ∃ w' : Fin m → ℝ, (∀ g, 0 ≤ w' g ∧ w' g ≤ w g) ∧
      bundleValue w' remaining = min (bundleValue w remaining) cap :=
  ⟨trimWeights remaining w cap, trimWeights_spec remaining w hw cap hcap⟩

end OnlineMMS
