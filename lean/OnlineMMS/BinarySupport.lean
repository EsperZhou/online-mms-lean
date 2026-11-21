import OnlineMMS.Benchmarks
import OnlineMMS.Model

namespace OnlineMMS

/-- A binary valuation is the indicator of its approval set. -/
def approvalValue {m : ℕ} (S : Finset (Fin m)) (g : Fin m) : ℝ :=
  if g ∈ S then 1 else 0

theorem approvalValue_bundle {m : ℕ} (S G : Finset (Fin m)) :
    bundleValue (approvalValue S) G = ((G.filter (· ∈ S)).card : ℝ) := by
  classical
  simp [bundleValue, approvalValue, Finset.sum_filter]
  congr 1

private theorem partition_approval_count {m : ℕ} (S : Finset (Fin m))
    (a : Fin m → Fin 2) (i : Fin 2) :
    partitionValue (approvalValue S) a i = ((S.filter (fun g => a g = i)).card : ℝ) := by
  change bundleValue (approvalValue S) (Finset.univ.filter (fun g => a g = i)) = _
  rw [approvalValue_bundle]
  have h : (Finset.univ.filter (fun g => a g = i)).filter (· ∈ S) =
      S.filter (fun g => a g = i) := by
    ext g
    simp [and_comm]
  rw [h]

/-- A type with a binary valuation and two arrivals has MMS equal to
half the number of its approved goods, rounded down. -/
theorem binary_two_agent_mms {m : ℕ} (S : Finset (Fin m)) :
    maximinShare (approvalValue S) 2 (by decide) = ((S.card / 2 : ℕ) : ℝ) := by
  classical
  apply le_antisymm
  · obtain ⟨a, ha⟩ := maximinShare_attained (approvalValue S) (show 0 < 2 by decide)
    by_contra! hbad
    have hlarge (i : Fin 2) : S.card / 2 < (S.filter (fun g => a g = i)).card := by
      have hi := (hbad.trans_le ((ha.symm.trans_le
        (partitionMin_le_partitionValue (approvalValue S) (by decide) a i))))
      rw [partition_approval_count] at hi
      exact_mod_cast hi
    have hcomplement : S.filter (fun g => a g = 1) = S.filter (fun g => ¬a g = 0) := by
      ext g
      have h : a g = 1 ↔ ¬a g = 0 := by
        generalize a g = j
        fin_cases j <;> decide
      simp [h]
    have heq : S.filter (fun g => ¬a g = 0) = S \ S.filter (fun g => a g = 0) := by
      ext g
      simp [Finset.mem_sdiff]
      tauto
    have htotal := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun g => a g = 0) S)
    rw [← heq, ← hcomplement] at htotal
    have h0 := hlarge 0
    have h1 := hlarge 1
    omega
  · obtain ⟨G, hG, hcard⟩ := Finset.exists_subset_card_eq (s := S) (Nat.div_le_self S.card 2)
    let a (g : Fin m) : Fin 2 := if g ∈ G then 0 else 1
    have h0 : S.filter (fun g => a g = 0) = G := by
      ext g
      simp [a, and_iff_right_of_imp (fun h => hG h)]
    have h1 : S.filter (fun g => a g = 1) = S \ G := by
      ext g
      simp [a, Finset.mem_sdiff, ite_eq_right_iff]
    refine le_trans ?_ (partitionMin_le_maximinShare _ (by decide) a)
    apply Finset.le_inf'
    intro i _
    rw [partition_approval_count]
    fin_cases i
    · change _ ≤ ((S.filter (fun g => a g = 0)).card : ℝ)
      rw [h0, hcard]
    · change _ ≤ ((S.filter (fun g => a g = 1)).card : ℝ)
      rw [h1, Finset.card_sdiff hG, hcard]
      exact_mod_cast (show S.card / 2 ≤ S.card - S.card / 2 by omega)

theorem approvalValue_approvals {m : ℕ} (v : Fin m → ℝ)
    (hv : ∀ g, v g = 0 ∨ v g = 1) :
    ∃ S : Finset (Fin m), v = approvalValue S := by
  classical
  refine ⟨Finset.univ.filter (fun g => v g = 1), ?_⟩
  funext g
  rcases hv g with hg | hg <;> simp [approvalValue, hg]

private theorem exists_binaryDemand (a : ℕ) {p : ℕ} (hp : 0 < p) :
    ∃ c : ℕ, a / 2 ≤ p * c :=
  ⟨a / 2, Nat.le_mul_of_pos_left _ hp⟩

/-- The minimum number of approved goods for a one-over-p MMS payment. -/
noncomputable def binaryDemand (a p : ℕ) : ℕ :=
  if hp : 0 < p then Nat.find (exists_binaryDemand a hp) else 0

theorem binaryDemand_pays (a : ℕ) {p : ℕ} (hp : 0 < p) :
    a / 2 ≤ p * binaryDemand a p := by
  simp only [binaryDemand, dif_pos hp]
  exact Nat.find_spec (exists_binaryDemand a hp)

theorem binaryDemand_le_half (a : ℕ) {p : ℕ} (hp : 0 < p) :
    binaryDemand a p ≤ a / 2 := by
  simp only [binaryDemand, dif_pos hp]
  exact Nat.find_min' (exists_binaryDemand a hp) (Nat.le_mul_of_pos_left _ hp)

theorem binaryDemand_min (a : ℕ) {p c : ℕ} (hp : 0 < p)
    (hc : c < binaryDemand a p) : p * c < a / 2 := by
  simp only [binaryDemand, dif_pos hp] at hc
  exact lt_of_not_ge (Nat.find_min (exists_binaryDemand a hp) hc)

/-- The first arrival receives the computed bundle, and the second receives all remaining goods. -/
def binaryPolicy {m k : ℕ} (X : Fin k → Finset (Fin m)) : Policy m k 2 :=
  .step X (fun first => .step (fun _ => Finset.univ \ X first) (fun _ => .done))

/-- Correctness of the specific policy induced by a first-bundle function. -/
theorem binaryPolicy_guarantees {m k p : ℕ} (hp : 0 < p)
    (S : Fin k → Finset (Fin m)) (X : Fin k → Finset (Fin m))
    (hchoice : ∀ first, X first ⊆ S first ∧
      binaryDemand (S first).card p ≤ (X first).card ∧
      ∀ t, binaryDemand (S t).card p ≤ (S t \ X first).card) :
    (binaryPolicy X).Guarantees (fun t => approvalValue (S t))
      (fun t => (1 / (p : ℝ)) * maximinShare (approvalValue (S t)) 2 (by decide))
      Finset.univ := by
  have hsub first := (hchoice first).1
  have hfirst first := (hchoice first).2.1
  have hsecond first := (hchoice first).2.2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpay (a c : ℕ) (hc : binaryDemand a p ≤ c) :
      (1 / (p : ℝ)) * ((a / 2 : ℕ) : ℝ) ≤ (c : ℝ) := by
    have hi := (binaryDemand_pays a hp).trans (Nat.mul_le_mul_left p hc)
    have hr : ((a / 2 : ℕ) : ℝ) ≤ (p : ℝ) * (c : ℝ) := by exact_mod_cast hi
    rw [one_div, ← div_eq_inv_mul]
    exact (div_le_iff₀ hpR).mpr (by simpa [mul_comm] using hr)
  refine fun first => ⟨Finset.subset_univ _, ?_, ?_⟩
  · change (1 / (p : ℝ)) * maximinShare (approvalValue (S first)) 2 (by decide) ≤ _
    rw [binary_two_agent_mms, approvalValue_bundle, Finset.filter_true_of_mem (hsub first)]
    exact hpay _ _ (hfirst first)
  · intro t
    refine ⟨Finset.Subset.refl _, ?_, trivial⟩
    change (1 / (p : ℝ)) * maximinShare (approvalValue (S t)) 2 (by decide) ≤
      bundleValue (approvalValue (S t)) (Finset.univ \ X first)
    rw [binary_two_agent_mms, approvalValue_bundle]
    have hf : ((Finset.univ \ X first).filter (· ∈ S t)) = S t \ X first := by
      ext g
      simp [and_comm]
    rw [hf]
    exact hpay _ _ (hsecond first t)

/-- Existence of a correct policy from existence of a first bundle for every type. -/
theorem binary_policy_of_demands {m k p : ℕ} (hp : 0 < p)
    (S : Fin k → Finset (Fin m))
    (hchoice : ∀ first : Fin k, ∃ X : Finset (Fin m), X ⊆ S first ∧
      binaryDemand (S first).card p ≤ X.card ∧
      ∀ t, binaryDemand (S t).card p ≤ (S t \ X).card) :
    ∃ policy : Policy m k 2, policy.Guarantees (fun t => approvalValue (S t))
      (fun t => (1 / (p : ℝ)) * maximinShare (approvalValue (S t)) 2 (by decide))
      Finset.univ := by
  classical
  choose X hsub hfirst hsecond using hchoice
  exact ⟨binaryPolicy X, binaryPolicy_guarantees hp S X
    (fun first => ⟨hsub first, hfirst first, hsecond first⟩)⟩

end OnlineMMS
