import OnlineMMS.RationalAlgorithm1Fast
import OnlineMMS.EmptySupply

namespace OnlineMMS.RationalAlgorithm1

/-- Search the inclusive interval `[lo, hi]`. The second component counts
the tests of `k ≤ 32 * mid ^ 2` actually made on this path. -/
private def bisectIndex (k lo hi : ℕ) : ℕ × ℕ :=
  if more : lo < hi then
    let mid := (lo + hi) / 2
    let rest := if k ≤ 32 * mid ^ 2 then bisectIndex k lo mid
                else bisectIndex k (mid + 1) hi
    (rest.1, rest.2 + 1)
  else (lo, 0)
termination_by hi - lo
decreasing_by all_goals omega

private theorem bisectIndex_stop {k lo hi : ℕ} (halt : ¬lo < hi) :
    bisectIndex k lo hi = (lo, 0) := by
  rw [bisectIndex]
  simp [halt]

private theorem bisectIndex_spec {k z : ℕ} (hz : k ≤ 32 * z ^ 2)
    (minimal : ∀ i < z, 32 * i ^ 2 < k) (fuel lo hi : ℕ)
    (left : lo ≤ z) (right : z ≤ hi) (width : hi - lo < 2 ^ fuel) :
    (bisectIndex k lo hi).1 = z ∧ (bisectIndex k lo hi).2 ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [pow_zero] at width
    rw [bisectIndex_stop (by omega)]
    exact ⟨by dsimp; omega, le_rfl⟩
  | succ fuel ih =>
    by_cases more : lo < hi
    · let mid := (lo + hi) / 2
      rw [pow_succ] at width
      by_cases test : k ≤ 32 * mid ^ 2
      · have inLeft : z ≤ mid := by
          by_contra! h
          exact (not_lt_of_ge test) (minimal mid h)
        have shrink : mid - lo < 2 ^ fuel := by dsimp [mid]; omega
        have sub := ih lo mid left inLeft shrink
        have step : bisectIndex k lo hi = ((bisectIndex k lo mid).1, (bisectIndex k lo mid).2 + 1) := by
          have atMid : k ≤ 32 * ((lo + hi) / 2) ^ 2 := test
          rw [bisectIndex]
          simp only [dif_pos more, if_pos more, if_pos atMid, mid]
        rw [step]
        exact ⟨sub.1, Nat.succ_le_succ sub.2⟩
      · have inRight : mid + 1 ≤ z := by
          apply Nat.succ_le_of_lt
          apply lt_of_not_ge
          intro contrary
          exact test (hz.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left contrary 2)))
        have shrink : hi - (mid + 1) < 2 ^ fuel := by dsimp [mid]; omega
        have sub := ih (mid + 1) hi inRight right shrink
        have step : bisectIndex k lo hi = ((bisectIndex k (mid + 1) hi).1, (bisectIndex k (mid + 1) hi).2 + 1) := by
          have atMid : ¬k ≤ 32 * ((lo + hi) / 2) ^ 2 := test
          rw [bisectIndex]
          simp only [dif_pos more, if_pos more, if_neg atMid, mid]
        rw [step]
        exact ⟨sub.1, Nat.succ_le_succ sub.2⟩
    · rw [bisectIndex_stop more]
      exact ⟨by dsimp; omega, Nat.zero_le _⟩

/-- The least index meeting the manuscript's integer threshold, paired with
the number of feasibility probes in its binary search. -/
def parameterSearch (k : ℕ) : ℕ × ℕ := bisectIndex k 0 k

theorem parameterSearch_spec (k : ℕ) :
    k ≤ 32 * (parameterSearch k).1 ^ 2 ∧
    (∀ i < (parameterSearch k).1, 32 * i ^ 2 < k) ∧
    (parameterSearch k).2 ≤ k.log2 + 1 ∧
    212 + 4 * (parameterSearch k).1 = parameterQ k := by
  obtain ⟨z, hmult, hz, minimal⟩ := bucketMultiplier_spec k
  have topFits : k ≤ 32 * k ^ 2 :=
    (by simpa [pow_two] using Nat.le_mul_self k : k ≤ k ^ 2).trans (Nat.le_mul_of_pos_left _ (by decide))
  have top : z ≤ k := by
    by_contra! h
    exact (not_lt_of_ge topFits) (minimal k h)
  have result := bisectIndex_spec hz minimal (k.log2 + 1) 0 k (Nat.zero_le _) top
    (by simpa using (Nat.lt_log2_self (n := k)))
  change (parameterSearch k).1 = z ∧ (parameterSearch k).2 ≤ k.log2 + 1 at result
  rw [result.1, parameterQ_eq, hmult]
  exact ⟨hz, minimal, result.2, rfl⟩

/-- An explicit `O(log(k + 1))` comparison bound, also valid at `k = 0`. -/
theorem parameterSearch_probes_log (k : ℕ) :
    (parameterSearch k).2 ≤ 2 * (k + 1).log2 := by
  by_cases empty : k = 0
  · subst k
    change (bisectIndex 0 0 0).2 ≤ _
    rw [bisectIndex_stop (by decide)]
    exact Nat.zero_le _
  · have mono : k.log2 ≤ (k + 1).log2 :=
      (Nat.le_log2 (Nat.succ_ne_zero k)).mpr ((Nat.log2_self_le empty).trans (Nat.le_succ k))
    have one : 1 ≤ (k + 1).log2 :=
      (Nat.le_log2 (Nat.succ_ne_zero k)).mpr (by rw [pow_one]; omega)
    have bound := (parameterSearch_spec k).2.2.1
    omega

def binaryParameterQ (k : ℕ) : ℕ := 212 + 4 * (parameterSearch k).1

theorem binaryParameterQ_eq (k : ℕ) : binaryParameterQ k = parameterQ k :=
  (parameterSearch_spec k).2.2.2

open private initialWithTPS from OnlineMMS.RationalAlgorithm1
open private policyFromFast from OnlineMMS.RationalAlgorithm1Fast

/-- The policy and the counts of midpoint probes and type rows submitted to
TPS preprocessing. -/
structure BinaryInitialization (m k n : ℕ) where
  policy : Policy m k n
  parameterProbes : ℕ
  tpsRows : ℕ

/-- With zero goods the constant empty rule returns immediately. With goods,
compute the multiplier by bisection and materialize a TPS for each type. -/
def initializeBinaryFast {m n k : ℕ} (v : Fin k → Fin m → ℚ) : BinaryInitialization m k n :=
  if m = 0 then ⟨emptySupplyPolicy n, 0, 0⟩ else
    let search := parameterSearch k
    let h := 212 + 4 * search.1
    let d := materialize (fun t => rationalTPSFast (v t) n)
    ⟨policyFromFast h (h / 4) d n (initialWithTPS v d), search.2, k⟩

theorem initializeBinaryFast_zero_goods {n k : ℕ} (v : Fin k → Fin 0 → ℚ) :
    initializeBinaryFast (n := n) v = ⟨emptySupplyPolicy n, 0, 0⟩ := rfl

theorem initializeBinaryFast_probes {m n k : ℕ} (v : Fin k → Fin m → ℚ) :
    (initializeBinaryFast (n := n) v).parameterProbes ≤ 2 * (k + 1).log2 := by
  by_cases empty : m = 0
  · simp [initializeBinaryFast, empty]
  · simpa [initializeBinaryFast, empty] using parameterSearch_probes_log k

def binaryFastPolicy {m n k : ℕ} (v : Fin k → Fin m → ℚ) : Policy m k n :=
  (initializeBinaryFast (n := n) v).policy

theorem binaryFastPolicy_zero_goods {k n : ℕ} (v : Fin k → Fin 0 → ℚ) :
    binaryFastPolicy (n := n) v = emptySupplyPolicy n := rfl

theorem binaryFastPolicy_eq_fastPolicy {m n k : ℕ} (v : Fin k → Fin m → ℚ) :
    binaryFastPolicy (n := n) v = fastPolicy (n := n) v := by
  by_cases empty : m = 0
  · subst m
    rw [binaryFastPolicy_zero_goods]
    exact (emptySupplyPolicy_unique _).symm
  · have eq := binaryParameterQ_eq k
    unfold binaryParameterQ at eq
    simp only [binaryFastPolicy, initializeBinaryFast, if_neg empty, fastPolicy, eq]

theorem binaryFastPolicy_guarantees_tps {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (binaryFastPolicy (n := n) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => truncatedShare (fun g => (v t g : ℝ)) n / (2 * (bucketMultiplier k : ℝ)))
      Finset.univ := by
  rw [binaryFastPolicy_eq_fastPolicy]
  exact fastPolicy_guarantees_tps hn hk v hv

end OnlineMMS.RationalAlgorithm1
