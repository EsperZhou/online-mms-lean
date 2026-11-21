import OnlineMMS.RationalTPS
import OnlineMMS.RationalArithmetic

namespace OnlineMMS

open RationalArithmetic

def commonValuationDenominator {m : ℕ} (v : Fin m → ℚ) : ℕ :=
  ∏ g, (v g).den

def scaledValuationNumerator {m : ℕ} (v : Fin m → ℚ) (g : Fin m) : ℕ :=
  (v g).num.natAbs * (commonValuationDenominator v / (v g).den)

theorem commonValuationDenominator_pos {m : ℕ} (v : Fin m → ℚ) :
    0 < commonValuationDenominator v := by
  unfold commonValuationDenominator
  exact Finset.prod_pos fun g _ => (v g).pos

theorem scaledValuation_ratio {m : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    (g : Fin m) :
    v g = (scaledValuationNumerator v g : ℚ) / commonValuationDenominator v := by
  let D := commonValuationDenominator v
  have hD : 0 < D := commonValuationDenominator_pos v
  have hdiv : (v g).den ∣ D := by
    apply Finset.dvd_prod_of_mem (f := fun i => (v i).den)
    exact Finset.mem_univ g
  have hmul : D / (v g).den * (v g).den = D := Nat.div_mul_cancel hdiv
  have hnum : ((v g).num.natAbs : ℤ) = (v g).num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (hv g))
  conv_lhs => rw [← Rat.num_div_den (v g)]
  change (↑(v g).num : ℚ) / (v g).den = (↑((v g).num.natAbs * (D / (v g).den)) : ℚ) / D
  have he : ((v g).num.natAbs : ℚ) = ((v g).num : ℚ) := by
    exact congrArg (fun a : ℤ => (a : ℚ)) hnum
  rw [Nat.cast_mul, he]
  apply (div_eq_div_iff (by exact_mod_cast (v g).pos.ne') (by exact_mod_cast hD.ne')).mpr
  rw [mul_assoc, ← Nat.cast_mul, hmul]

def valuationInputDigits {m : ℕ} (v : Fin m → ℚ) : ℕ :=
  ∑ g, ((v g).num.natAbs.size + (v g).den.size)

private theorem prod_size_le_sum {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∏ x ∈ s, f x).size ≤ (∑ x ∈ s, (f x).size) + 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.size_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h := size_mul_le (f a) (∏ x ∈ s, f x)
    omega

theorem commonValuationDenominator_digits {m : ℕ} (v : Fin m → ℚ) :
    (commonValuationDenominator v).size ≤ valuationInputDigits v + 1 := by
  unfold commonValuationDenominator valuationInputDigits
  apply (prod_size_le_sum _ _).trans
  exact Nat.add_le_add_right
    (Finset.sum_le_sum (fun _ _ => Nat.le_add_left _ _)) _

theorem scaledValuation_total_digits {m : ℕ} (v : Fin m → ℚ) :
    (∑ g, scaledValuationNumerator v g).size ≤ 2 * valuationInputDigits v + m + 1 := by
  let b := 2 * valuationInputDigits v + 1
  have ht (g : Fin m) : (scaledValuationNumerator v g).size ≤ b := by
    unfold scaledValuationNumerator
    have hg : (v g).num.natAbs.size ≤ valuationInputDigits v := by
      unfold valuationInputDigits
      exact (Nat.le_add_right _ _).trans
        (Finset.single_le_sum (fun i _ => Nat.zero_le ((v i).num.natAbs.size + (v i).den.size))
          (Finset.mem_univ g))
    have hb := commonValuationDenominator_digits v
    have hdiv := Nat.size_le_size (Nat.div_le_self (commonValuationDenominator v) (v g).den)
    have hm := size_mul_le (v g).num.natAbs
      (commonValuationDenominator v / (v g).den)
    dsimp [b]
    omega
  apply Nat.size_le.mpr
  rw [show 2 * valuationInputDigits v + m + 1 = b + m by dsimp [b]; omega]
  have hsum : (∑ g, scaledValuationNumerator v g) ≤ m * 2 ^ b := by
    calc
      _ ≤ ∑ _g : Fin m, 2 ^ b :=
        Finset.sum_le_sum fun g _ => (Nat.size_le.mp (ht g)).le
      _ = _ := by simp [nsmul_eq_mul]
  apply hsum.trans_lt
  calc
    m * 2 ^ b < 2 ^ m * 2 ^ b := Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self (n := m))
      (show 0 < (2 : ℕ)^b from Nat.pow_pos (by decide : 0 < (2 : ℕ)))
    _ = 2 ^ (b + m) := by
      rw [Nat.add_comm b m]
      exact (pow_add (2 : ℕ) m b).symm

def normalizedWeightQ {m : ℕ} (v : Fin m → ℚ) (n : ℕ) (g : Fin m) : ℚ :=
  min (v g) (rationalTPS v n) / rationalTPS v n

theorem normalizedWeightQ_cast {m n : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (g : Fin m) :
    (normalizedWeightQ v n g : ℝ) = normalizedWeight (fun g => (v g : ℝ)) n g := by
  simp [normalizedWeightQ, normalizedWeight, rationalTPS_correct hn v hv]

/-- The denominator input required by the rational trimming and sampler
certificates is available for every explicit rational valuation. -/
theorem normalizedWeightQ_initial_grid {m n : ℕ} (v : Fin m → ℚ)
    (hv : ∀ g, 0 ≤ v g) (hn : 0 < n)
    (hd : 0 < truncatedShare (fun g => (v g : ℝ)) n) :
    ∃ A : ℕ, 0 < A ∧ A.size ≤ 2 * valuationInputDigits v + m + 1 ∧
      ∀ g, OnGrid A (normalizedWeightQ v n g) := by
  let w : Fin m → ℚ := fun g => (scaledValuationNumerator v g : ℚ) / commonValuationDenominator v
  have he : v = w := funext (scaledValuation_ratio v hv)
  have hd' : 0 < truncatedShare (fun g => (w g : ℝ)) n := by simpa only [← he] using hd
  obtain ⟨A, hA, hm, hu⟩ := rationalTPS_normalized_common_denominator
    hn (commonValuationDenominator_pos v) (scaledValuationNumerator v) hd'
  refine ⟨A, hA, (Nat.size_le_size hm).trans (scaledValuation_total_digits v), ?_⟩
  intro g
  obtain ⟨u, _, heq⟩ := hu g
  change normalizedWeight (fun g => (w g : ℝ)) n g = (u : ℝ) / A at heq
  rw [← he] at heq
  refine ⟨(u : ℤ), Rat.cast_injective (α := ℝ) ?_⟩
  rw [normalizedWeightQ_cast v hv hn, heq]
  push_cast
  rfl

end OnlineMMS
