import OnlineMMS.Benchmarks
import OnlineMMS.BaselinePreprocess
import OnlineMMS.Model
import Mathlib.Algebra.BigOperators.Fin

namespace OnlineMMS

/-- Two blocks of `k` equal goods realize the threshold ratio for the
singleton rule of the (1/k) policy. -/
noncomputable def baselineExample (k : ℕ) : Fin (k + k) → ℝ :=
  fun _ => 1 / (k : ℝ)

private theorem baselineExample_tps_le_one {k : ℕ} (hk : 0 < k) :
    truncatedShare (baselineExample k) 2 ≤ 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hv : ∀ g, 0 ≤ baselineExample k g := fun _ => by
    unfold baselineExample
    positivity
  have himp := (truncatedShare_spec (baselineExample k) hv (show 0 < 2 by decide)).1.2
  have hsum : (∑ g : Fin (k + k), baselineExample k g) = 2 := by
    simp [baselineExample, nsmul_eq_mul]
    field_simp
    ring
  have hle := Finset.sum_le_sum
    (fun g (_ : g ∈ (Finset.univ : Finset (Fin (k + k)))) =>
      min_le_left (baselineExample k g) (truncatedShare (baselineExample k) 2))
  rw [hsum] at hle
  norm_num at himp
  linarith

/-- Both equal blocks are worth exactly one. The total is two, so a
two-part maximin partition cannot improve this value. -/
theorem baselineExample_mms {k : ℕ} (hk : 0 < k) :
    maximinShare (baselineExample k) 2 (by decide) = 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hv : ∀ g, 0 ≤ baselineExample k g := fun _ => by
    unfold baselineExample
    positivity
  apply le_antisymm
    ((maximinShare_le_truncatedShare (baselineExample k) hv (by decide)).trans
      (baselineExample_tps_le_one hk))
  let p : Fin (k + k) → Fin 2 := Fin.addCases (fun _ => 0) (fun _ => 1)
  have hpLeft (g : Fin k) : p (g.castAdd k) = 0 := Fin.addCases_left g
  have hpRight (g : Fin k) : p (g.addNat k) = 1 := by
    rw [← Fin.natAdd_eq_addNat]
    exact Fin.addCases_right g
  have hpart (j : Fin 2) : partitionValue (baselineExample k) p j = 1 := by
    unfold partitionValue
    rw [Finset.sum_filter, Fin.sum_univ_add]
    fin_cases j <;>
      simp [hpLeft, hpRight, baselineExample, nsmul_eq_mul, hkR.ne']
  apply le_trans _ (partitionMin_le_maximinShare (baselineExample k) (by decide) p)
  apply Finset.le_inf'
  exact fun j _ => (hpart j).ge

/-- Taking any singleton from a full reserve attains exactly the claimed
fraction on this two-arrival instance, regardless of tie-breaking. -/
theorem baselineExample_singleton_payment {k : ℕ} (hk : 0 < k) (g : Fin (k + k)) :
    bundleValue (baselineExample k) {g} =
      maximinShare (baselineExample k) 2 (by decide) / (k : ℝ) := by
  simp [bundleValue, baselineExample, baselineExample_mms hk]

private theorem baselineExample_normalizedWeight {k : ℕ} (hk : 0 < k)
    (g : Fin (k + k)) :
    normalizedWeight (baselineExample k) 2 g = 1 / (k : ℝ) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hv : ∀ g, 0 ≤ baselineExample k g := fun _ => by
    unfold baselineExample
    positivity
  have htps : truncatedShare (baselineExample k) 2 = 1 := by
    apply le_antisymm (baselineExample_tps_le_one hk)
    rw [← baselineExample_mms hk]
    exact maximinShare_le_truncatedShare (baselineExample k) hv (by decide)
  have hb : 1 / (k : ℝ) ≤ 1 := (div_le_one₀ (by linarith)).mpr hkR
  unfold normalizedWeight
  rw [htps]
  change min (1 / (k : ℝ)) 1 / 1 = 1 / (k : ℝ)
  rw [min_eq_left hb, div_one]

/-- On this normalized instance, every allowed preprocessing result fills
both slots for every type. Every permitted choice for the first arrival
therefore yields exactly the claimed fraction of the original MMS. -/
theorem baselineExample_first_reserved_payment {k : ℕ} (hk : 0 < k)
    (F : Fin k → Finset (Finset (Fin (k + k))))
    (hcap : ∀ i, (F i).card ≤ 2)
    (hsingle : ∀ i, ∀ B ∈ F i, ∃ g, B = {g} ∧
      1 / (k : ℝ) ≤ normalizedWeight (baselineExample k) 2 g)
    (hcomplete : ∀ i, (F i).card < 2 → ∀ g,
      1 / (k : ℝ) ≤ normalizedWeight (baselineExample k) 2 g → {g} ∈ F i) :
    ∀ i, (F i).card = 2 ∧ (F i).Nonempty ∧ ∀ B ∈ F i,
      bundleValue (baselineExample k) B =
        maximinShare (baselineExample k) 2 (by decide) / (k : ℝ) := by
  intro i
  have hfull : (F i).card = 2 := by
    by_contra! hne
    have hlt : (F i).card < 2 := lt_of_le_of_ne (hcap i) hne
    let allSingletons := (Finset.univ : Finset (Fin (k + k))).image
      (fun g => ({g} : Finset (Fin (k + k))))
    have hsub : allSingletons ⊆ F i := by
      intro B hB
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hB
      apply hcomplete i hlt g
      simp [baselineExample_normalizedWeight hk]
    have hcount : allSingletons.card = k + k := by
      simp [allSingletons, Finset.card_image_of_injective _ Finset.singleton_injective]
    have hle := Finset.card_le_card hsub
    omega
  refine ⟨hfull, Finset.card_pos.mp (by rw [hfull]; decide), ?_⟩
  intro B hB
  obtain ⟨g, rfl, _⟩ := hsingle i B hB
  exact baselineExample_singleton_payment hk g

/-- The preprocessing routine produces a full singleton reserve on the
two-arrival witness, and its first allocation attains exactly one over k. -/
theorem baselineExample_tight {k : ℕ} (hk : 0 < k) :
    ∃ F : Fin k → Finset (Finset (Fin (k + k))), ∀ i,
      (F i).card = 2 ∧ (F i).Nonempty ∧ ∀ B ∈ F i,
        bundleValue (baselineExample k) B =
          maximinShare (baselineExample k) 2 (by decide) / (k : ℝ) := by
  obtain ⟨F, hcap, hsingle, hcomplete⟩ :=
    exists_initial_reserves (fun _ : Fin k => normalizedWeight (baselineExample k) 2) 2
      (1 / (k : ℝ))
  exact ⟨F, baselineExample_first_reserved_payment hk F hcap hsingle hcomplete⟩

end OnlineMMS
