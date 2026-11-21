import OnlineMMS.FinitePartitions
import Mathlib.Algebra.BigOperators.Fin

namespace OnlineMMS

private theorem repeat_type (types : Fin 3 → Fin 2) :
    ∃ i j : Fin 3, i ≠ j ∧ types i = types j := by
  by_cases h01 : types 0 = types 1
  · exact ⟨0,1,by decide,h01⟩
  by_cases h02 : types 0 = types 2
  · exact ⟨0,2,by decide,h02⟩
  refine ⟨1,2,by decide,Fin.ext ?_⟩
  have h0 := (types 0).isLt
  have h1 := (types 1).isLt
  have h2 := (types 2).isLt
  have hv01 : (types 0).val ≠ (types 1).val := fun h => h01 (Fin.ext h)
  have hv02 : (types 0).val ≠ (types 2).val := fun h => h02 (Fin.ext h)
  omega

private theorem one_remaining_slot {i j : Fin 3} (hij : i ≠ j) :
    ∃ u : Fin 3, ∀ x : Fin 3, x = i ∨ x = j ∨ x = u := by
  have hd : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  let u : Fin 3 := ⟨3 - i.val - j.val, by omega⟩
  refine ⟨u,fun x => ?_⟩
  have hx := x.isLt
  have h : x.val = i.val ∨ x.val = j.val ∨ x.val = u.val := by dsimp [u]; omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- A reservation for each known arrival slot. The slot labels encode only
the type multiplicities, and the assigned bundles can be used in any order. -/
theorem three_arrivals_known_count_reservations {m : ℕ} (v : Fin 2 → Fin m → ℝ)
    (types : Fin 3 → Fin 2) :
    ∃ p : Fin m → Fin 3, ∀ j : Fin 3,
      maximinShare (v (types j)) 3 (by decide) ≤ partitionValue (v (types j)) p j := by
  classical
  obtain ⟨i,j,hij,htype⟩ := repeat_type types
  obtain ⟨u,hu⟩ := one_remaining_slot hij
  let t := types i
  obtain ⟨p,hp⟩ := paymentPartition_of_mms (v t) (by decide : 0 < 3)
  have hmajor (j : Fin 3) : maximinShare (v t) 3 (by decide) ≤ partitionValue (v t) p j := hp j
  have hex : ∃ best : Fin 3, maximinShare (v (types u)) 3 (by decide) ≤
      partitionValue (v (types u)) p best := by
    by_contra! h
    have hsum := sum_paymentParts (v (types u)) Finset.univ p
    have hM := paymentPartition_total (paymentPartition_of_mms (v (types u)) (by decide : 0 < 3))
    norm_num at hM
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    rw [Fin.sum_univ_three] at hsum
    change partitionValue (v (types u)) p 0 + partitionValue (v (types u)) p 1 +
      partitionValue (v (types u)) p 2 = _ at hsum
    linarith
  obtain ⟨b,hb⟩ := hex
  let e := Equiv.swap u b
  refine ⟨e ∘ p,fun k => ?_⟩
  have heq : partitionValue (v (types k)) (e ∘ p) k =
      partitionValue (v (types k)) p (e.symm k) := by
    unfold partitionValue
    congr 1
    ext g
    simp [Equiv.apply_eq_iff_eq_symm_apply]
  rw [heq]
  rcases hu k with hi | hj | hu'
  · rw [hi]
    exact hmajor _
  · rw [hj, ← htype]
    exact hmajor _
  · rw [hu']
    simpa [e] using hb

end OnlineMMS
