import OnlineMMS.Model
import Mathlib.Tactic.Linarith

namespace OnlineMMS

/-- If every free good is below the threshold, the first threshold-crossing
bag costs at most twice the threshold for every active type. -/
theorem exists_crossing_bag {m k : ℕ} (w : Fin k → Fin m → ℝ)
    (pool : Finset (Fin m)) (active : Finset (Fin k)) {β : ℝ} (hβ : 0 < β)
    (hitems : ∀ i ∈ active, ∀ g ∈ pool, w i g < β)
    (hfill : ∃ i ∈ active, β ≤ bundleValue (w i) pool) :
    ∃ B ⊆ pool, B.Nonempty ∧ (∃ i ∈ active, β ≤ bundleValue (w i) B) ∧
      (∀ i ∈ active, bundleValue (w i) B ≤ 2 * β) ∧
      ∃ last ∈ B, ∀ i ∈ active, bundleValue (w i) (B.erase last) < β := by
  classical
  induction pool using Finset.induction_on with
  | empty =>
    obtain ⟨i, _, hi⟩ := hfill
    simp [bundleValue] at hi
    exact False.elim (hβ.not_le hi)
  | @insert g pool hg ih =>
    by_cases hprev : ∃ i ∈ active, β ≤ bundleValue (w i) pool
    · obtain ⟨B, hsub, hne, hhit, hbound, hlast⟩ := ih
        (fun i hi x hx => hitems i hi x (Finset.mem_insert_of_mem hx)) hprev
      exact ⟨B, hsub.trans (Finset.subset_insert _ _), hne, hhit, hbound, hlast⟩
    · have hsmall (i : Fin k) (hi : i ∈ active) : bundleValue (w i) pool < β :=
        lt_of_not_ge fun h => hprev ⟨i, hi, h⟩
      have hmem : g ∈ insert g pool := Finset.mem_insert_self _ _
      refine ⟨insert g pool, Finset.Subset.rfl, ⟨g, hmem⟩, hfill, ?_,
        ⟨g, hmem, ?_⟩⟩
      · intro i hi
        have hlast := hitems i hi g hmem
        have hfirst := hsmall i hi
        rw [show bundleValue (w i) (insert g pool) =
            w i g + bundleValue (w i) pool from Finset.sum_insert hg]
        linarith
      · intro i hi
        simpa only [Finset.erase_insert hg] using hsmall i hi

end OnlineMMS
