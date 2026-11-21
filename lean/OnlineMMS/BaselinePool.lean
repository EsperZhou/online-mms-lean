import OnlineMMS.Model
import Mathlib.Tactic

/-! Counting the goods held in tentative allocations for the one-over-k baseline. -/

namespace OnlineMMS

variable {m k : ℕ}

/-- All tentative bundles. A bundle reserved for multiple types occurs only once. -/
def reserveBank (reserves : Fin k → Finset (Finset (Fin m))) : Finset (Finset (Fin m)) :=
  Finset.univ.biUnion reserves

@[simp] theorem mem_reserveBank {reserves : Fin k → Finset (Finset (Fin m))}
    {B : Finset (Fin m)} : B ∈ reserveBank reserves ↔ ∃ t, B ∈ reserves t := by
  simp [reserveBank]

/-- Remaining goods outside every tentative bundle. -/
def freePool (remaining : Finset (Fin m)) (reserves : Fin k → Finset (Finset (Fin m))) :
    Finset (Fin m) :=
  remaining \ (reserveBank reserves).biUnion id

theorem freePool_subset (remaining : Finset (Fin m)) (reserves : Fin k → Finset (Finset (Fin m))) :
    freePool remaining reserves ⊆ remaining :=
  Finset.sdiff_subset

theorem disjoint_of_subset_freePool {remaining B C : Finset (Fin m)}
    {reserves : Fin k → Finset (Finset (Fin m))}
    (hB : B ⊆ freePool remaining reserves) (hC : C ∈ reserveBank reserves) :
    Disjoint B C := by
  refine Finset.disjoint_left.2 fun g hgB hgC => ?_
  have hbank : g ∈ (reserveBank reserves).biUnion id := Finset.mem_biUnion.2 ⟨C, hC, hgC⟩
  exact (Finset.mem_sdiff.1 (hB hgB)).2 hbank

private theorem value_union_le_sum (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g)
    (bank : Finset (Finset (Fin m))) :
    bundleValue w (bank.biUnion id) ≤ ∑ B ∈ bank, bundleValue w B := by
  classical
  induction bank using Finset.induction_on with
  | empty => simp [bundleValue]
  | insert B bank hB ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hB]
    change bundleValue w (B ∪ bank.biUnion id) ≤ _
    have hdisj : Disjoint B (bank.biUnion id \ B) := Finset.disjoint_sdiff
    have hUnion : B ∪ bank.biUnion id = B ∪ (bank.biUnion id \ B) := by
      ext g
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    have hsum : bundleValue w (B ∪ (bank.biUnion id \ B)) =
        bundleValue w B + bundleValue w (bank.biUnion id \ B) :=
      Finset.sum_union hdisj
    have hmono : bundleValue w (bank.biUnion id \ B) ≤ bundleValue w (bank.biUnion id) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun g _ _ => hw g)
    rw [hUnion, hsum]
    exact add_le_add_left (hmono.trans ih) _

private theorem card_bank_le (reserves : Fin k → Finset (Finset (Fin m)))
    (r : ℕ) (current : Fin k) (hcap : ∀ t, (reserves t).card ≤ r)
    (hempty : reserves current = ∅) :
    (reserveBank reserves).card ≤ (k - 1) * r := by
  have hEq : reserveBank reserves = (Finset.univ.erase current).biUnion reserves := by
    ext B
    constructor
    · intro hB
      obtain ⟨t, ht⟩ := mem_reserveBank.1 hB
      have hne : t ≠ current := by
        intro heq
        subst t
        simp [hempty] at ht
      exact Finset.mem_biUnion.2 ⟨t, Finset.mem_erase.2 ⟨hne, Finset.mem_univ t⟩, ht⟩
    · intro hB
      obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 hB
      exact mem_reserveBank.2 ⟨t, ht⟩
  rw [hEq]
  simpa [Finset.card_erase_of_mem (Finset.mem_univ current)] using
    Finset.card_biUnion_le_card_mul (Finset.univ.erase current) reserves r (fun t _ => hcap t)

/-- If the current type has no tentative bundle and sees less than the target
in each reserved bundle, enough value remains to fill a bag. -/
theorem threshold_le_freePool (w : Fin m → ℝ) (remaining : Finset (Fin m))
    (reserves : Fin k → Finset (Finset (Fin m))) (r : ℕ) (current : Fin k)
    (hr : 0 < r) (hw : ∀ g, 0 ≤ w g) (hcap : ∀ t, (reserves t).card ≤ r)
    (hempty : reserves current = ∅)
    (hsmall : ∀ B ∈ reserveBank reserves, bundleValue w B ≤ 1 / (k : ℝ))
    (hleft : (r : ℝ) ≤ bundleValue w remaining) :
    1 / (k : ℝ) ≤ bundleValue w (freePool remaining reserves) := by
  let occupied := (reserveBank reserves).biUnion id
  have hk : 1 ≤ k := Nat.zero_lt_of_lt current.isLt
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hrone : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hcount : ((reserveBank reserves).card : ℝ) ≤ ((k : ℝ) - 1) * (r : ℝ) := by
    have hcast : ((reserveBank reserves).card : ℝ) ≤ (((k - 1) * r : ℕ) : ℝ) :=
      Nat.cast_le.2 (card_bank_le reserves r current hcap hempty)
    push_cast [Nat.cast_sub hk] at hcast
    exact hcast
  have hoccupied : bundleValue w occupied ≤ ((k : ℝ) - 1) * (r : ℝ) / (k : ℝ) := calc
    bundleValue w occupied ≤ ∑ B ∈ reserveBank reserves, bundleValue w B :=
      value_union_le_sum w hw _
    _ ≤ ((reserveBank reserves).card : ℝ) * (1 / (k : ℝ)) := by
      simpa only [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul (reserveBank reserves) (bundleValue w) _ hsmall
    _ ≤ _ := by
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_right hcount (one_div_nonneg.mpr hkpos.le)
  have hsplit : bundleValue w (freePool remaining reserves) +
      bundleValue w (remaining ∩ occupied) = bundleValue w remaining := by
    change (∑ g ∈ remaining \ occupied, w g) +
      (∑ g ∈ remaining ∩ occupied, w g) = ∑ g ∈ remaining, w g
    rw [← Finset.sdiff_inter_self_left]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have hoverlap : bundleValue w (remaining ∩ occupied) ≤ bundleValue w occupied :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun g _ _ => hw g)
  have hidentity : ((k : ℝ) - 1) * (r : ℝ) / (k : ℝ) = (r : ℝ) - (r : ℝ) / k := by
    field_simp [ne_of_gt hkpos]
    ring
  rw [hidentity] at hoccupied
  have hmin : 1 / (k : ℝ) ≤ (r : ℝ) / (k : ℝ) :=
    div_le_div_of_nonneg_right hrone hkpos.le
  linarith

end OnlineMMS
