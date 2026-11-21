import OnlineMMS.FiniteEnvelope
import OnlineMMS.QuadraticEstimator

namespace OnlineMMS.FixedWidth

open private ceilSquareDiv ceil_sqrt_eq gNat gNat_eq from OnlineMMS.FiniteEnvelope

/-- Exact integer index for the fixed-width product estimator. -/
def productParameterQ (k : ℕ) : ℕ := gNat k

theorem productParameterQ_eq (k : ℕ) :
    productParameterQ k = productMultiplier k :=
  (gNat_eq k).symm

/-- Exact integer index for the fixed-width quadratic estimator. -/
def quadraticParameterQ (k : ℕ) : ℕ := ceilSquareDiv (16 * k) 1

theorem quadraticParameterQ_eq (k : ℕ) :
    quadraticParameterQ k = quadraticMultiplier k := by
  unfold quadraticParameterQ quadraticMultiplier
  symm
  apply ceil_sqrt_eq (by decide)
  · positivity
  · push_cast
    have he := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith only [he]

end OnlineMMS.FixedWidth
