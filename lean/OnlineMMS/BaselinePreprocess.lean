import OnlineMMS.Model
import Mathlib.Data.Finset.Card

namespace OnlineMMS

/-- Preprocess by holding up to one singleton per remaining arrival for each
type. An unsaturated type reserves every good that reaches its threshold. -/
theorem exists_initial_reserves {m k : ℕ} (w : Fin k → Fin m → ℝ) (r : ℕ) (β : ℝ) :
    ∃ F : Fin k → Finset (Finset (Fin m)),
      (∀ i, (F i).card ≤ r) ∧
      (∀ i, ∀ B ∈ F i, ∃ g, B = {g} ∧ β ≤ w i g) ∧
      (∀ i, (F i).card < r → ∀ g, β ≤ w i g → {g} ∈ F i) := by
  classical
  let high (i : Fin k) := Finset.univ.filter fun g => β ≤ w i g
  have hchoose (i : Fin k) :=
    Finset.exists_subset_card_eq (min_le_right r (high i).card)
  choose goods hsub hcard using hchoose
  let reserves (i : Fin k) : Finset (Finset (Fin m)) :=
    (goods i).image fun g => {g}
  have hcount (i : Fin k) : (reserves i).card = min r (high i).card :=
    (Finset.card_image_of_injective _ Finset.singleton_injective).trans (hcard i)
  refine ⟨reserves, fun i => (hcount i).le.trans (min_le_left _ _), ?_, ?_⟩
  · intro i B hB
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨g, rfl, (Finset.mem_filter.mp (hsub i hg)).2⟩
  · intro i hunsat g hhigh
    have hsize : (high i).card < r := by
      by_contra! h
      rw [hcount, min_eq_left h] at hunsat
      exact (lt_irrefl r) hunsat
    have heq : goods i = high i := by
      apply Finset.eq_of_subset_of_card_le (hsub i)
      rw [hcard, min_eq_right hsize.le]
    unfold reserves
    rw [heq]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hhigh⟩)

end OnlineMMS
