import OnlineMMS.FiniteHorizon
import OnlineMMS.FiniteRowMatrix
import OnlineMMS.FiniteThreeUpper

namespace OnlineMMS

/-- Targets for the first type and the other type respectively. -/
def orientedTarget (q : Fin 2 → ℝ) (a b : ℝ) (first : Fin 2) (t : Fin 2) : ℝ :=
  (if t = first then a else b) * q t

theorem two_type_alternative (t : Fin 2) : ∃ u : Fin 2, u ≠ t ∧ ∀ i : Fin 2, i = t ∨ i = u := by
  fin_cases t
  · refine ⟨1, by decide, fun i => ?_⟩
    fin_cases i <;> simp
  · refine ⟨0, by decide, fun i => ?_⟩
    fin_cases i <;> simp

/-- The three-arrival choice works on any supplied partition minima
and after either first-type revelation. -/
theorem three_arrival_first_choice {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g)
    (R : Finset (Fin m)) (q : Fin 2 → ℝ)
    (h : ∀ t, HasPaymentPartition (v t) R 3 (q t)) (first : Fin 2) :
    ∃ (G : Finset (Fin m)) (policy : Policy m 2 2),
      G ⊆ R ∧ q first ≤ bundleValue (v first) G ∧
        policy.Guarantees v (orientedTarget q 1 (9/10) first) (R \ G) := by
  obtain ⟨other, hne, hcases⟩ := two_type_alternative first
  obtain ⟨rows, hrows⟩ := h first
  obtain ⟨deleted, hother⟩ := choosing_row_preserves_nine_tenths (v other) (hv other)
    R rows (h other)
  let G := R.filter (fun g => rows g = deleted)
  have hself := paymentPartition_removePart (v first) R (by decide : 0 < 2) rows deleted hrows
  obtain ⟨p,hp⟩ := two_arrival_policy_of_partitions v (R \ G)
    (orientedTarget q 1 (9/10) first) (by
      intro t
      rcases hcases t with rfl | rfl
      · simpa [orientedTarget] using hself
      · simpa [orientedTarget,hne] using hother)
  exact ⟨G,p,Finset.filter_subset _ _,hrows _,hp⟩

/-- The three-arrival policy gives 9/10 of each supplied nonnegative
partition minimum on every history. -/
theorem three_arrival_policy_of_partitions {m : ℕ} (v : Fin 2 → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (R : Finset (Fin m)) (q : Fin 2 → ℝ)
    (hq : ∀ t, 0 ≤ q t) (h : ∀ t, HasPaymentPartition (v t) R 3 (q t)) :
    ∃ policy : Policy m 2 3, policy.Guarantees v (fun t => (9 / 10) * q t) R := by
  apply policy_step_of_choices
  intro first
  obtain ⟨G,p,hsub,hfirst,hrest⟩ := three_arrival_first_choice v hv R q h first
  have hl (t : Fin 2) : (9 / 10) * q t ≤ q t := by
    nlinarith [hq t]
  refine ⟨G,p,hsub,(hl first).trans hfirst,hrest.mono ?_⟩
  intro t
  by_cases he : t = first
  · simpa [orientedTarget,he] using hl t
  · simp [orientedTarget,he]

/-- In the two-type three-arrival case the best uniform deterministic
guarantee is exactly 9/10 of original MMS. -/
theorem alpha_two_types_three_arrivals : alphaHorizonMMS 2 3 (by decide) = 9 / 10 := by
  apply le_antisymm
  · obtain ⟨v,hv,hupper⟩ := three_arrival_upper_instance
    let q : Fin 2 → ℝ := fun t => maximinShare (v t) 3 (by decide)
    have hinstance : instanceFactor v q 3 ≤ 9 / 10 := by
      by_contra! hbad
      obtain ⟨_,p,hp⟩ := (instanceFactor_attained v q 3).1
      exact hupper _ hbad p hp
    exact (horizonFactor_le_instance (fun n hn _ w => maximinShare w n hn)
      (show 0 < 3 by decide) v hv).trans hinstance
  · apply le_horizonFactor_of_policies _ (by decide)
      (show (9 / 10 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    intro m v hv
    exact three_arrival_policy_of_partitions v hv Finset.univ
      (fun t => maximinShare (v t) 3 (by decide))
      (fun t => maximinShare_nonnegative (v t) (hv t) (by decide))
      (fun t => paymentPartition_of_mms (v t) (by decide))

end OnlineMMS
