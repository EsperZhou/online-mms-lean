import OnlineMMS.TwoTypeScalePreparation
import OnlineMMS.TwoTypePacketPolicy

namespace OnlineMMS.TwoType

private theorem fourSevenths_admissible {m n : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (hM : 0 < maximinShare v n hn) :
    AdmissibleScale v n (4 / 7 * maximinShare v n hn) := by
  classical
  let a : ℝ := 4 / 7 * maximinShare v n hn
  let x (g : Fin m) := v g / a
  have ha : 0 < a := mul_pos (by norm_num) hM
  refine ⟨ha, ?_⟩
  obtain ⟨p, hp⟩ := maximinShare_attained v hn
  have hpart (j : Fin n) :
      1 ≤ bundleValue (fun g => score (x g)) (Finset.univ.filter (fun g => p g = j)) := by
    apply score_initialization x (fun g => div_nonneg (hv g) ha.le)
    unfold bundleValue x
    rw [← Finset.sum_div]
    apply (le_div_iff₀ ha).mpr
    have hval := partitionMin_le_partitionValue v hn p j
    rw [hp] at hval
    change (7 / 4 : ℝ) * (4 / 7 * maximinShare v n hn) ≤ partitionValue v p j
    linarith
  calc
    (n : ℝ) = ∑ _j : Fin n, (1 : ℝ) := by simp
    _ ≤ ∑ j : Fin n, bundleValue (fun g => score (x g)) (Finset.univ.filter (fun g => p g = j)) :=
      Finset.sum_le_sum (fun j _ => hpart j)
    _ = _ := by
      unfold bundleValue
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp [x, a]

/-- The fully specified two-type decision rule on explicit rational data. -/
def rationalPacketPolicy {m : ℕ} (v : Fin 2 → Fin m → ℚ) (n : ℕ) : Policy m 2 n :=
  let y (t : Fin 2) := rationalScale (v t) n
  let tag (t : Fin 2) (g : Fin m) := roundedTagRat (scaleScanLimit (v t)) (v t g / y t)
  packetPolicy y tag n Finset.univ

theorem rationalPacketPolicy_first_payment {m n : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hn : 0 < n) (target : Fin 2 → ℝ)
    (h : (rationalPacketPolicy v n).Guarantees (fun t g => (v t g : ℝ)) target Finset.univ)
    (t : Fin 2) :
    let y (i : Fin 2) := rationalScale (v i) n
    let tag (i : Fin 2) (g : Fin m) := roundedTagRat (scaleScanLimit (v i)) (v i g / y i)
    target t ≤ bundleValue (fun g => (v t g : ℝ)) (packetChoice y tag n Finset.univ t) := by
  cases n with
  | zero => omega
  | succ r => exact (h t).2.1

/-- Executable breakpoint search, packet merging, and least-cost selection
deliver 4/7 of original MMS at every adaptive history. -/
theorem rationalPacketPolicy_guarantees {m n : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (hn : 0 < n) :
    (rationalPacketPolicy v n).Guarantees (fun t g => (v t g : ℝ))
      (fun t => 4 / 7 * maximinShare (fun g => (v t g : ℝ)) n hn) Finset.univ := by
  let y (t : Fin 2) := rationalScale (v t) n
  let tag (t : Fin 2) (g : Fin m) := roundedTagRat (scaleScanLimit (v t)) (v t g / y t)
  let w (t : Fin 2) (g : Fin m) : ℝ := v t g
  have hspec (t : Fin 2) := rationalScale_spec (v t) (hv t) hn
  have hy (t : Fin 2) : 0 ≤ y t := by
    rcases hspec t with ⟨h, _⟩ | h
    · simp [y, h]
    · have hp : (0 : ℝ) < (y t : ℝ) := h.1.1
      exact_mod_cast hp.le
  have hw (t : Fin 2) (g : Fin m) : 0 ≤ w t g := by
    dsimp [w]
    exact_mod_cast hv t g
  have htag (t : Fin 2) (g : Fin m) :
      score (w t g / (y t : ℝ)) = (tag t g).elim 0 PacketLevel.weight :=
    (rationalScale_tag_correct (v t) (hv t) hn g).symm
  have hInit (t : Fin 2) (ht : 0 < y t) :
      (n : ℝ) ≤ bundleValue (fun g => score (w t g / (y t : ℝ))) (Finset.univ : Finset (Fin m)) := by
    rcases hspec t with ⟨h, _⟩ | h
    · simp [y, h] at ht
    · exact h.1.2
  change (packetPolicy y tag n Finset.univ).Guarantees w
    (fun t => 4 / 7 * maximinShare (w t) n hn) Finset.univ
  apply (packetPolicy_guarantees w hw y hy tag htag n Finset.univ hInit).mono
  intro t
  by_cases hp : 0 < maximinShare (w t) n hn
  · have hA := fourSevenths_admissible (w t) (hw t) hn hp
    rcases hspec t with ⟨_, he⟩ | h
    · exact (he _ hA).elim
    · exact h.2 hA
  · exact (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt hp)).trans
      (by exact_mod_cast hy t)

end OnlineMMS.TwoType
