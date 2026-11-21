import OnlineMMS.TwoTypePacking
import OnlineMMS.MainTheorem
import Mathlib.Tactic

namespace OnlineMMS.TwoType

private def other (t : Fin 2) : Fin 2 := if t = 0 then 1 else 0

private theorem same_or_other (t i : Fin 2) : i = t ∨ i = other t := by
  fin_cases t <;> fin_cases i <;> simp [other]

private theorem cheapest_le_average {m r : ℕ} (hr : 0 < r)
    {w : Fin m → ℝ} {R : Finset (Fin m)} (G : Candidates w R r)
    (u : Fin m → ℝ) (hu : ∀ g, 0 ≤ u g) :
    ∃ j : Fin r, (∀ i, bundleValue u (G.bag j) ≤ bundleValue u (G.bag i)) ∧
      (r : ℝ) * bundleValue u (G.bag j) ≤ bundleValue u R := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image (fun i => bundleValue u (G.bag i))
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin r)).Nonempty)
  refine ⟨j, fun i => hj i (Finset.mem_univ i), ?_⟩
  calc
    (r : ℝ) * bundleValue u (G.bag j) = ∑ _i : Fin r, bundleValue u (G.bag j) := by simp [nsmul_eq_mul]
    _ ≤ ∑ i : Fin r, bundleValue u (G.bag i) := Finset.sum_le_sum hj
    _ = bundleValue u (Finset.univ.biUnion G.bag) := by
      unfold bundleValue
      rw [Finset.sum_biUnion]
      intro i _ j _ hne
      exact G.disjoint hne
    _ ≤ bundleValue u R := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun g _ _ => hu g)
      intro g hg
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
      exact G.subset i hi

/-- Every pair of admissible nonnegative scales yields a paying policy.
At each nonfinal positive-scale arrival it uses disjoint candidates and a
least-cost candidate for the other type. -/
theorem two_type_admissible_scales {m n : ℕ}
    (v : Fin 2 → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g)
    (scale : Fin 2 → ℝ) (hscale : ∀ t, 0 ≤ scale t)
    (hinit : ∀ t, 0 < scale t →
      (n : ℝ) ≤ bundleValue (fun g => score (v t g / scale t)) Finset.univ) :
    ∃ policy : Policy m 2 n, policy.Guarantees v scale Finset.univ := by
  classical
  let x : Fin 2 → Fin m → ℝ := fun t g => v t g / scale t
  let w : Fin 2 → Fin m → ℝ := fun t g => score (x t g)
  have hx (t : Fin 2) (g : Fin m) : 0 ≤ x t g := div_nonneg (hv t g) (hscale t)
  have hscore (t : Fin 2) (g : Fin m) : 0 ≤ w t g := score_nonneg (hx t g)
  let valid (r : ℕ) (R : Finset (Fin m)) : Prop :=
    ∀ t, 0 < scale t → (r : ℝ) ≤ bundleValue (w t) R
  have hpay {t : Fin 2} {B : Finset (Fin m)} (ht : 0 < scale t)
      (hB : 1 ≤ bundleValue (w t) B) : scale t ≤ bundleValue (v t) B := by
    calc
      scale t = scale t * 1 := (mul_one _).symm
      _ ≤ scale t * bundleValue (w t) B := mul_le_mul_of_nonneg_left hB ht.le
      _ = ∑ g ∈ B, scale t * w t g := Finset.mul_sum ..
      _ ≤ bundleValue (v t) B := by
        refine Finset.sum_le_sum (fun g _ => ?_)
        calc
          _ ≤ scale t * x t g := mul_le_mul_of_nonneg_left (score_le_value (hx t g)) ht.le
          _ = _ := by dsimp [x]; rw [mul_div_cancel₀ _ ht.ne']
  apply policy_of_steps id valid v scale _ n Finset.univ hinit
  intro r R hR t
  by_cases hr : r = 0
  · subst r
    refine ⟨R, ∅, Finset.Subset.rfl, ?_, by simp, ?_⟩
    · by_cases ht : 0 < scale t
      · exact hpay ht (by simpa using hR t ht)
      · exact (le_of_not_gt ht).trans (Finset.sum_nonneg fun g _ => hv t g)
    · intro i _
      simp [bundleValue]
  · by_cases ht : 0 < scale t
    · obtain ⟨G⟩ := score_pack (x t) (hx t) (r + 1) R (hR t ht)
      obtain ⟨j, _, hcost⟩ := cheapest_le_average (by omega) G (w (other t)) (hscore (other t))
      let B := G.bag j
      refine ⟨B, R \ B, G.subset j, hpay ht (G.pays j), rfl, ?_⟩
      intro i hi
      rcases same_or_other t i with he | he
      · subst i
        have hleave := G.leaves j
        change ((r + 1 : ℕ) : ℝ) - 1 ≤ bundleValue (w t) (R \ B) at hleave
        simpa only [Nat.cast_succ, add_sub_cancel_right] using hleave
      · subst i
        have hprev := hR (other t) hi
        have he : bundleValue (w (other t)) (R \ B) + bundleValue (w (other t)) B =
            bundleValue (w (other t)) R := Finset.sum_sdiff (G.subset j)
        change ((r + 1 : ℕ) : ℝ) * bundleValue (w (other t)) B ≤ bundleValue (w (other t)) R at hcost
        push_cast at hcost hprev
        have hmul := mul_le_mul_of_nonneg_left hprev (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
        apply (mul_le_mul_left (show (0 : ℝ) < (r : ℝ) + 1 by positivity)).mp
        nlinarith only [hcost, hmul, mul_le_mul_of_nonneg_left he.le (show 0 ≤ (r : ℝ) + 1 by positivity),
          mul_le_mul_of_nonneg_left he.ge (show 0 ≤ (r : ℝ) + 1 by positivity)]
    · have hz : scale t = 0 := le_antisymm (le_of_not_gt ht) (hscale t)
      refine ⟨∅, R, Finset.empty_subset _, by simp [hz, bundleValue], by simp, ?_⟩
      intro i hi
      exact (by exact_mod_cast Nat.le_succ r : (r : ℝ) ≤ ↑(r + 1)).trans (hR i hi)

/-- The two-type score policy guarantees four sevenths of original MMS for
any horizon and every revelation history. -/
theorem two_type_four_sevenths {m n : ℕ} (hn : 0 < n)
    (v : Fin 2 → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    ∃ policy : Policy m 2 n, policy.Guarantees v
      (fun t => (4 / 7 : ℝ) * maximinShare (v t) n hn) Finset.univ := by
  classical
  let scale : Fin 2 → ℝ := fun t => (4 / 7 : ℝ) * maximinShare (v t) n hn
  let x : Fin 2 → Fin m → ℝ := fun t g => v t g / scale t
  let w : Fin 2 → Fin m → ℝ := fun t g => score (x t g)
  have hscale (t : Fin 2) : 0 ≤ scale t := by
    obtain ⟨p, hp⟩ := maximinShare_attained (v t) hn
    unfold scale
    rw [← hp]
    exact mul_nonneg (by norm_num) (partitionMin_nonneg (v t) (hv t) hn p)
  have hx (t : Fin 2) (g : Fin m) : 0 ≤ x t g := div_nonneg (hv t g) (hscale t)
  apply two_type_admissible_scales v hv scale hscale
  intro t ht
  change (n : ℝ) ≤ bundleValue (w t) Finset.univ
  obtain ⟨p, hp⟩ := maximinShare_attained (v t) hn
  have hpart (j : Fin n) :
      1 ≤ bundleValue (w t) (Finset.univ.filter (fun g => p g = j)) := by
    apply score_initialization (x t) (hx t)
    unfold bundleValue x
    rw [← Finset.sum_div]
    apply (le_div_iff₀ ht).mpr
    have hval := (partitionMin_le_partitionValue (v t) hn p j)
    rw [hp] at hval
    change (7 / 4 : ℝ) * ((4 / 7 : ℝ) * maximinShare (v t) n hn) ≤ partitionValue (v t) p j
    linarith
  calc
    (n : ℝ) = ∑ _j : Fin n, (1 : ℝ) := by simp
    _ ≤ ∑ j : Fin n, bundleValue (w t) (Finset.univ.filter (fun g => p g = j)) :=
      Finset.sum_le_sum (fun j _ => hpart j)
    _ = bundleValue (w t) Finset.univ := by
      unfold bundleValue
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp

/-- The four-sevenths guarantee survives the infimum over all instances. -/
theorem four_sevenths_le_alphaMMS_two : (4 / 7 : ℝ) ≤ alphaMMS 2 := by
  apply le_uniformFactor
  · norm_num
  · intro n hn m v hv
    exact two_type_four_sevenths hn v hv

end OnlineMMS.TwoType
