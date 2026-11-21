import OnlineMMS.BinaryRuntimeLarge
import OnlineMMS.BinaryRuntimeSmall

namespace OnlineMMS.BinaryRuntime

/-- The paper's computable binary algorithm for all type counts. -/
def policy {m k : ℕ} (S : Fin k → Finset (Fin m)) : Policy m k 2 :=
  if k ≤ 6 then binaryPolicy (smallBundle S)
  else binaryPolicy (largeBundle (parameterCount k) S)

/-- The paper's binary approximation ratio. -/
noncomputable def ratio (k : ℕ) : ℝ :=
  if k ≤ 6 then 1 else 1 / (pairParameter k : ℝ)

theorem policy_guarantees {m k : ℕ} (S : Fin k → Finset (Fin m)) :
    (policy S).Guarantees (fun t => approvalValue (S t))
      (fun t => ratio k * maximinShare (approvalValue (S t)) 2 (by decide))
      Finset.univ := by
  by_cases hk : k ≤ 6
  · simpa [policy, ratio, hk] using smallPolicy_guarantees hk S
  · simpa [policy, ratio, hk] using largePolicy_guarantees (show 7 ≤ k by omega) S

/-- Total modeled scan work for a revealed first type and the final allocation. -/
def policyCost {m k : ℕ} (S : Fin k → Finset (Fin m)) (first : Fin k) : ℕ :=
  if k ≤ 6 then smallPolicyCost S first else largePolicyCost S first

/-- A degree-four bound in the number of goods, with polynomial dependence on
    the number of listed types. The constant includes the five-bit search. -/
theorem policyCost_polynomial {m k : ℕ}
    (S : Fin k → Finset (Fin m)) (first : Fin k) :
    policyCost S first ≤
      (10 * (m + 1) * ((m + 1) * (m*m + m + 1) + 11^2 * 252 + 1) + 3 * (m + 1)^2) +
      (k + 1 + (k + 1) * (m + 1)^2 + (k * (m + 1) + 1)^2 +
        (k * (m + 1)) * (m + 1) + (m + 1)^3 * (k * m + 1) + 3 * (m + 1)^2) := by
  by_cases hk : k ≤ 6
  · rw [policyCost, if_pos hk]
    exact (smallPolicyCost_le S first).trans (Nat.le_add_right _ _)
  · rw [policyCost, if_neg hk]
    exact (largePolicyCost_le (show 7 ≤ k by omega) S first).trans (Nat.le_add_left _ _)

end OnlineMMS.BinaryRuntime
