import OnlineMMS.Benchmarks
import Mathlib.Algebra.BigOperators.Fin

namespace OnlineMMS

private theorem two_agent_mms_le_half_total {m : ℕ} (v : Fin m → ℝ)
    (hv : ∀ g, 0 ≤ v g) :
    maximinShare v 2 (by decide) ≤ (∑ g, v g) / 2 := by
  refine (maximinShare_le_truncatedShare v hv (by decide)).trans ?_
  have ht := (truncatedShare_spec v hv (show 0 < 2 by decide)).1.2
  have hsum : (∑ g, min (v g) (truncatedShare v 2)) ≤ ∑ g, v g :=
    Finset.sum_le_sum fun _ _ => min_le_left _ _
  norm_num at ht
  linarith

/-- On (2p) goods, all worth one, the two-way MMS is (p). -/
theorem two_agent_unit_mms (p : ℕ) :
    maximinShare (fun _ : Fin (p + p) => (1 : ℝ)) 2 (by decide) = (p : ℝ) := by
  apply le_antisymm
  · have h := two_agent_mms_le_half_total (fun _ : Fin (p + p) => (1 : ℝ))
      (fun _ => zero_le_one)
    simpa using h
  · let assign : Fin (p + p) → Fin 2 := Fin.addCases (fun _ => 0) (fun _ => 1)
    have hleft (g : Fin p) : assign (g.castAdd p) = 0 := Fin.addCases_left g
    have hright (g : Fin p) : assign (g.addNat p) = 1 := by
      rw [← Fin.natAdd_eq_addNat]
      exact Fin.addCases_right g
    have hpart (i : Fin 2) :
        partitionValue (fun _ => (1 : ℝ)) assign i = (p : ℝ) := by
      unfold partitionValue
      rw [Finset.sum_filter, Fin.sum_univ_add]
      fin_cases i <;> simp [hleft, hright]
    refine le_trans ?_ (partitionMin_le_maximinShare _ (by decide) assign)
    apply Finset.le_inf'
    exact fun i _ => (hpart i).ge

/-- Approving exactly two goods gives two-way MMS one. -/
theorem two_agent_pair_mms {m : ℕ} (S : Finset (Fin m)) (hS : S.card = 2) :
    maximinShare (fun g => if g ∈ S then (1 : ℝ) else 0) 2 (by decide) = 1 := by
  let v : Fin m → ℝ := fun g => if g ∈ S then 1 else 0
  change maximinShare v 2 (by decide) = 1
  have hv (g : Fin m) : 0 ≤ v g := by
    dsimp [v]
    split <;> norm_num
  apply le_antisymm
  · have hsum : (∑ g, v g) = 2 := by
      simp [v, hS]
    simpa [hsum] using two_agent_mms_le_half_total v hv
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
    let assign (g : Fin m) : Fin 2 := if g = a then 0 else 1
    have ha : 1 ≤ partitionValue v assign (0 : Fin 2) := by
      unfold partitionValue
      exact (show (1 : ℝ) = v a by simp [v]) ▸
        (Finset.single_le_sum (fun g _ => hv g) (by simp [assign]))
    have hb : 1 ≤ partitionValue v assign (1 : Fin 2) := by
      unfold partitionValue
      exact (show (1 : ℝ) = v b by simp [v]) ▸
        (Finset.single_le_sum (fun g _ => hv g) (by simp [assign, hab.symm]))
    refine le_trans ?_ (partitionMin_le_maximinShare _ (by decide) assign)
    apply Finset.le_inf'
    intro i _
    fin_cases i <;> assumption

end OnlineMMS
