import OnlineMMS.EmptySupply
import OnlineMMS.BinaryRuntime
import OnlineMMS.RationalFixedWidthQuadratic

/-! Empty-supply branches in the binary and one-width algorithms. The empty
branch performs one return per arrival, independently of the type count. -/

namespace OnlineMMS

/-- The ordinary constructor is evaluated only if some goods exist. -/
def withSupplyCheck {m k n : ℕ} (ordinary : Unit → Policy m k n) : Policy m k n :=
  if m = 0 then emptySupplyPolicy n else ordinary ()

theorem withSupplyCheck_eq {m k n : ℕ} (ordinary : Unit → Policy m k n) :
    withSupplyCheck ordinary = ordinary () := by
  by_cases hm : m = 0
  · subst m
    simp only [withSupplyCheck, if_true]
    exact (emptySupplyPolicy_unique _).symm
  · simp [withSupplyCheck,hm]

theorem withSupplyCheck_empty {k r : ℕ} (ordinary : Unit → Policy 0 k (r+1)) (t : Fin k) :
    (match withSupplyCheck ordinary with | .step b _ => b t) = ∅ ∧
      (emptySupplyAction (m := 0) t).2 = 1 :=
  emptySupplyPolicy_arrival_work r t

def BinaryRuntime.supplyCheckedPolicy {m k : ℕ} (S : Fin k → Finset (Fin m)) : Policy m k 2 :=
  withSupplyCheck (fun _ => BinaryRuntime.policy S)

theorem BinaryRuntime.supplyCheckedPolicy_guarantees {m k : ℕ} (S : Fin k → Finset (Fin m)) :
    (supplyCheckedPolicy S).Guarantees (fun t => approvalValue (S t))
      (fun t => ratio k * maximinShare (approvalValue (S t)) 2 (by decide)) Finset.univ := by
  simpa only [supplyCheckedPolicy,withSupplyCheck_eq] using policy_guarantees S

/-- The single supply test is charged with the nonempty branch; the empty
branch just returns the empty action. -/
def BinaryRuntime.supplyCheckedCost {m k : ℕ} (S : Fin k → Finset (Fin m)) (i : Fin k) : ℕ :=
  if m = 0 then 1 else 1 + policyCost S i

/-- Explicit polynomial scan budget for the two binary branches. -/
def BinaryRuntime.workBudget (k m : ℕ) : ℕ :=
  (10 * (m + 1) * ((m + 1) * (m*m + m + 1) + 11^2 * 252 + 1) + 3 * (m + 1)^2) +
    (k + 1 + (k + 1) * (m + 1)^2 + (k * (m + 1) + 1)^2 +
      (k * (m + 1)) * (m + 1) + (m + 1)^3 * (k * m + 1) + 3 * (m + 1)^2)

/-- For explicitly listed binary approvals, the input uses at least one
bit for each of the (km) entries. The cost bound is polynomial in its
encoded length even when no goods are present. -/
theorem BinaryRuntime.supplyCheckedCost_le {m k : ℕ} (S : Fin k → Finset (Fin m)) (i : Fin k)
    (L : ℕ) (hcells : k*m ≤ L) :
    supplyCheckedCost S i ≤ 1 + workBudget L L := by
  by_cases hm : m = 0
  · simp [supplyCheckedCost,hm]
  · have hm' : 0 < m := Nat.pos_of_ne_zero hm
    have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
    have h1 := calc k ≤ k*m := Nat.le_mul_of_pos_right _ hm'
                    _ ≤ L := hcells
    have h2 := calc m ≤ k*m := Nat.le_mul_of_pos_left _ hk
                    _ ≤ L := hcells
    rw [supplyCheckedCost,if_neg hm]
    apply Nat.add_le_add_left
    refine (policyCost_polynomial S i).trans ?_
    unfold workBudget
    gcongr

def RationalFixedWidth.supplyCheckedPolicy {m k n : ℕ} (v : Fin k → Fin m → ℚ) : Policy m k n :=
  withSupplyCheck (fun _ => oneWidthPolicy v)

theorem RationalFixedWidth.supplyCheckedPolicy_guarantees {m k n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (supplyCheckedPolicy (n := n) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => truncatedShare (fun g => (v t g : ℝ)) n /
        (6 * (FixedWidth.productMultiplier k : ℝ))) Finset.univ := by
  simpa only [supplyCheckedPolicy,withSupplyCheck_eq] using oneWidthPolicy_guarantees hn hk v hv

end OnlineMMS
