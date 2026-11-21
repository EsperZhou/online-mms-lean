import OnlineMMS.Model
import OnlineMMS.Benchmarks

namespace OnlineMMS

private theorem policy_of_common_partition {m k n : ℕ}
    (v : Fin k → Fin m → ℝ) (target : Fin k → ℝ) (parts : Fin n → Finset (Fin m))
    (hdisjoint : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hpay : ∀ t i, target t ≤ bundleValue (v t) (parts i)) :
    ∀ (indices : Finset (Fin n)) (remaining : Finset (Fin m)),
      (∀ i ∈ indices, parts i ⊆ remaining) →
      ∃ policy : Policy m k indices.card, policy.Guarantees v target remaining := by
  intro indices
  induction indices using Finset.induction_on with
  | empty =>
      intro remaining _
      exact ⟨.done, trivial⟩
  | @insert i indices hi ih =>
      intro remaining hsubset
      have hpart : parts i ⊆ remaining := hsubset i (Finset.mem_insert_self _ _)
      have hrest (j : Fin n) (hj : j ∈ indices) : parts j ⊆ remaining \ parts i := by
        have hne : j ≠ i := by
          rintro rfl
          exact hi hj
        exact Finset.subset_sdiff.mpr
          ⟨hsubset j (Finset.mem_insert_of_mem hj), hdisjoint hne⟩
      obtain ⟨next, hnext⟩ := ih (remaining \ parts i) hrest
      rw [Finset.card_insert_of_not_mem hi]
      exact ⟨.step (fun _ => parts i) (fun _ => next), fun t => ⟨hpart, hpay t i, hnext⟩⟩

/-- With only one type, an attained MMS partition can be assigned in a fixed
order and yields full MMS at every arrival. -/
theorem exists_one_type_mms_policy {m n : ℕ} (hn : 0 < n) (v : Fin 1 → Fin m → ℝ) :
    ∃ policy : Policy m 1 n,
      policy.Guarantees v (fun t => maximinShare (v t) n hn) Finset.univ := by
  obtain ⟨p, hp⟩ := maximinShare_attained (v 0) hn
  let parts : Fin n → Finset (Fin m) := fun i => Finset.univ.filter (fun g => p g = i)
  have hdisjoint : Pairwise (fun i j => Disjoint (parts i) (parts j)) := by
    intro i j hij
    refine Finset.disjoint_left.mpr fun g hi hj => hij ?_
    exact (Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2
  have hpay (t : Fin 1) (i : Fin n) :
      maximinShare (v t) n hn ≤ bundleValue (v t) (parts i) := by
    have ht : t = 0 := Subsingleton.elim t 0
    subst t
    rw [← hp]
    exact partitionMin_le_partitionValue (v 0) hn p i
  have h := policy_of_common_partition v _ parts hdisjoint hpay Finset.univ Finset.univ
    (fun _ _ => Finset.subset_univ _)
  rw [Finset.card_fin] at h
  exact h

end OnlineMMS
