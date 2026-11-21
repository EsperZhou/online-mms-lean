import OnlineMMS.AlgorithmDigits
import OnlineMMS.ManuscriptParameter
import OnlineMMS.RationalAlgorithm1FastWork

namespace OnlineMMS.RationalAlgorithm1

open private tpsSweepVisits from OnlineMMS.RationalTPSSweep

/-- Every explicitly supplied rational has a positive denominator, whose
encoding occupies at least one binary digit. -/
theorem table_cells_le_inputDigits {m k : ℕ} (v : Fin k → Fin m → ℚ) :
    k * m ≤ inputDigits v := by
  have row (t : Fin k) : m ≤ valuationInputDigits (v t) := by
    unfold valuationInputDigits
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun g _ =>
      show 1 ≤ (v t g).num.natAbs.size + (v t g).den.size from
      (show 1 ≤ (v t g).den.size from Nat.size_pos.mpr (v t g).pos).trans (Nat.le_add_left _ _))
  simpa [inputDigits, nsmul_eq_mul] using
    (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun t _ => row t))

theorem types_le_inputDigits {m k : ℕ} (hm : 0 < m) (v : Fin k → Fin m → ℚ) :
    k ≤ inputDigits v := (Nat.le_mul_of_pos_right k hm).trans (table_cells_le_inputDigits v)

/-- Comparisons in the row's actual merge sort and the arithmetic count of
the subsequent TPS sweep. -/
def tpsRowWork {m : ℕ} (v : Fin m → ℚ) (n : ℕ) : ℕ :=
  let leQ := fun g g' => decide (v g ≤ v g')
  mergeSortComparisons leQ (List.finRange m) +
    tpsSweepVisits v n m 0 ((List.finRange m).mergeSort leQ)

/-- Charge each midpoint probe, each counted row operation, each normalized
weight, and each type's initial product. The empty branch has none of these
operations. Dispatching the branch itself costs one comparison. -/
def preprocessingWork {m k : ℕ} (n : ℕ) (v : Fin k → Fin m → ℚ) : ℕ :=
  if m = 0 then 1 else
    1 + (initializeBinaryFast (n := n) v).parameterProbes +
      (∑ t, tpsRowWork (v t) n) + k * (m + 1)

theorem preprocessingWork_empty {k n : ℕ} (v : Fin k → Fin 0 → ℚ) :
    preprocessingWork n v = 1 := rfl

private theorem preprocessing_nonempty {m k : ℕ} (n : ℕ) (hm : m ≠ 0)
    (v : Fin k → Fin m → ℚ) :
    preprocessingWork n v ≤ 1 + (parameterSearch k).2 +
      (k * m) * m.size + 7 * (k * m + k) := by
  have rows : (∑ t, tpsRowWork (v t) n) ≤ k * (m.size * m + 6 * (m + 1)) := by
    calc
      _ ≤ ∑ _t : Fin k, (m.size * m + 6 * (m + 1)) :=
        Finset.sum_le_sum fun t _ => rationalTPSFast_work_le (v t) n
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ = 1 + (parameterSearch k).2 + (∑ t, tpsRowWork (v t) n) + k * (m + 1) := by
      simp only [preprocessingWork, initializeBinaryFast, if_neg hm]
    _ ≤ 1 + (parameterSearch k).2 + k * (m.size * m + 6 * (m + 1)) + k * (m + 1) := by omega
    _ = _ := by ring

/-- Both the dimension-sensitive bound in Appendix F and an explicit
polynomial in the binary input length apply to the same preprocessing count. -/
theorem algorithm1_preprocessing_work {m k : ℕ} (hk : 0 < k)
    (n : ℕ) (v : Fin k → Fin m → ℚ) :
    preprocessingWork n v ≤ 11 * k * (m + 1) * ((m + 2).log2 + 1) ∧
    preprocessingWork n v ≤ 16 * (encodingLength n v + 1)^2 := by
  by_cases empty : m = 0
  · subst m
    rw [preprocessingWork_empty]
    constructor <;> apply Nat.succ_le_of_lt <;> positivity
  · have core := preprocessing_nonempty n empty v
    have probes : (parameterSearch k).2 ≤ 2 * k := by
      have h := (parameterSearch_spec k).2.2.1
      have logBound := Nat.log2_le_self k
      omega
    constructor
    · let B := (m + 2).log2 + 1
      have hB : 0 < B := Nat.succ_pos _
      have bits : m.size ≤ B := Nat.size_le.mpr
        ((show m ≤ m + 2 by omega).trans_lt (Nat.lt_log2_self (n := m + 2)))
      let perTable := k * (m + 1) * B
      have cells : k * m ≤ k * (m + 1) := Nat.mul_le_mul_left k (by omega)
      have sort : (k * m) * m.size ≤ perTable := Nat.mul_le_mul cells bits
      have scans : k * m + k ≤ perTable := calc
        _ = k * (m + 1) := by ring
        _ ≤ _ := Nat.le_mul_of_pos_right _ hB
      have types : k ≤ k * m + k := Nat.le_add_left _ _
      calc
        _ ≤ 1 + (parameterSearch k).2 + (k * m) * m.size + 7 * (k * m + k) := core
        _ ≤ 11 * perTable := by omega
        _ = _ := by dsimp [perTable, B]; ring
    · let L := encodingLength n v
      have encoded : inputDigits v ≤ L := by dsimp [L, encodingLength]; omega
      have bits : m.size ≤ L := by dsimp [L, encodingLength]; omega
      have cells := (table_cells_le_inputDigits v).trans encoded
      have types := (types_le_inputDigits (Nat.pos_of_ne_zero empty) v).trans encoded
      have sort := Nat.mul_le_mul cells bits
      calc
        _ ≤ 1 + (parameterSearch k).2 + (k * m) * m.size + 7 * (k * m + k) := core
        _ ≤ 1 + 2 * L + L * L + 7 * (2 * L) := by omega
        _ ≤ 16 * (L + 1)^2 := by nlinarith [Nat.zero_le (L * L)]

/-- At a nonempty instance the policy already holds its TPS values and its
state after `past`. Charge only the call serving the new arrival. The empty
supply rule has its own constant action and needs neither of those inputs. -/
def supplyCheckedArrival {m k : ℕ} (n : ℕ) (v : Fin k → Fin m → ℚ)
    (past : List (Fin k)) (t : Fin k) : Finset (Fin m) × ℕ :=
  if m = 0 then emptySupplyAction t else
    let h := binaryParameterQ k
    let d := materialize (fun i => rationalTPSFast (v i) n)
    let r := n - (past.length + 1)
    let state := policyState v n past
    let counted := advanceFastCounted h (h / 4) d r state t
    (counted.1.1, counted.2)

theorem supplyCheckedArrival_empty {k n : ℕ} (v : Fin k → Fin 0 → ℚ)
    (past : List (Fin k)) (t : Fin k) : supplyCheckedArrival n v past t = (∅, 1) := rfl

theorem supplyCheckedArrival_nonempty {m n k : ℕ} (hm : m ≠ 0) (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ i g, 0 ≤ v i g) (past : List (Fin k)) (t : Fin k) :
    let h := parameterQ k
    let d := materialize (fun i => rationalTPSFast (v i) n)
    let r := n - (past.length + 1)
    let state := policyState v n past
    (supplyCheckedArrival n v past t).1 = (advanceFast h (h / 4) d r state t).1 ∧
      (supplyCheckedArrival n v past t).2 ≤ 64 * (k * (m + 1) + m * ((m + 2).log2 + 1)) := by
  have step := fastPolicy_arrival_work hn hk v hv past t
  simp only [supplyCheckedArrival, if_neg hm, binaryParameterQ_eq]
  exact ⟨congrArg Prod.fst step.1, step.2⟩

/-- Each arrival after any actual prefix obeys both Lemma 3.9's arithmetic
bound and a polynomial in the original binary input length. -/
theorem algorithm1_arrival_work {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ i g, 0 ≤ v i g) (past : List (Fin k)) (t : Fin k) :
    (supplyCheckedArrival n v past t).2 ≤ 64 * (k * (m + 1) + m * ((m + 2).log2 + 1)) ∧
    (supplyCheckedArrival n v past t).2 ≤ 256 * (encodingLength n v + 1)^2 := by
  by_cases empty : m = 0
  · subst m
    rw [supplyCheckedArrival_empty]
    constructor <;> apply Nat.succ_le_of_lt <;> positivity
  · have dimension := (supplyCheckedArrival_nonempty empty hn hk v hv past t).2
    refine ⟨dimension, ?_⟩
    let L := encodingLength n v
    have encoded : inputDigits v ≤ L := by dsimp [L, encodingLength]; omega
    have cells := (table_cells_le_inputDigits v).trans encoded
    have types := (types_le_inputDigits (Nat.pos_of_ne_zero empty) v).trans encoded
    have goods : m ≤ L := (Nat.le_mul_of_pos_left m hk).trans cells
    have bits : (m + 2).log2 + 1 ≤ L + 3 := by
      have h := Nat.log2_le_self (m + 2)
      omega
    have sorting := Nat.mul_le_mul goods bits
    have scans : k * (m + 1) ≤ 2 * L := by rw [Nat.mul_add, Nat.mul_one]; omega
    calc
      _ ≤ 64 * (k * (m + 1) + m * ((m + 2).log2 + 1)) := dimension
      _ ≤ 64 * (2 * L + L * (L + 3)) := by omega
      _ ≤ 256 * (L + 1)^2 := by nlinarith only [Nat.zero_le L, Nat.zero_le (L * L)]

end OnlineMMS.RationalAlgorithm1
