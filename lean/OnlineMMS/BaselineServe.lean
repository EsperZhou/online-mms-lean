import OnlineMMS.Model
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff

namespace OnlineMMS

/-- Remove the allocated bag from every reserve, then trim each reserve to
the new horizon. A reserve below the new cap lost only the allocated bag,
and was below the old cap before allocation. -/
theorem exists_trim_reserves {m k r : ℕ}
    (F : Fin k → Finset (Finset (Fin m))) (B : Finset (Fin m)) :
    ∃ F' : Fin k → Finset (Finset (Fin m)),
      (∀ i, F' i ⊆ (F i).erase B) ∧
      (∀ i, (F' i).card ≤ r) ∧
      (∀ i, (F' i).card < r → (F i).card < r + 1 ∧ F' i = (F i).erase B) := by
  classical
  have hchoose (i : Fin k) :=
    Finset.exists_subset_card_eq (min_le_right r ((F i).erase B).card)
  choose F' hsub hcard using hchoose
  refine ⟨F', hsub, (fun i => (hcard i).le.trans (min_le_left _ _)), ?_⟩
  intro i hsmall
  have hlt : ((F i).erase B).card < r := by
    by_contra! hge
    rw [hcard, min_eq_left hge] at hsmall
    omega
  have heq : F' i = (F i).erase B := by
    apply Finset.eq_of_subset_of_card_le (hsub i)
    rw [hcard, min_eq_right hlt.le]
  refine ⟨?_, heq⟩
  by_cases hmem : B ∈ F i
  · have h := Finset.card_erase_add_one hmem
    omega
  · rw [Finset.erase_eq_of_not_mem hmem] at hlt
    omega

/-- Trimming reserves preserves the feasibility of every kept bag after
allocating an entire bag disjoint from the others. -/
theorem trimmed_reserve_subset_remaining {m k : ℕ}
    {F F' : Fin k → Finset (Finset (Fin m))}
    {B remaining : Finset (Fin m)}
    (htrim : ∀ i, F' i ⊆ (F i).erase B)
    (hsub : ∀ i C, C ∈ F i → C ⊆ remaining)
    (hdisj : ∀ i C, C ∈ F i → C ≠ B → Disjoint C B) :
    ∀ i C, C ∈ F' i → C ⊆ remaining \ B := by
  intro i C hC
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp (htrim i hC)
  exact Finset.subset_sdiff.mpr ⟨hsub i C hmem, hdisj i C hmem hne⟩

end OnlineMMS
