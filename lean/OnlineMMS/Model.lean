import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find

namespace OnlineMMS

/-- A policy for a fixed instance is a tree. Each edge sees one revealed type,
    allocates a bundle, and specifies the policy for the remaining arrivals. -/
inductive Policy (m k : ℕ) : ℕ → Type
  | done : Policy m k 0
  | step {r : ℕ} (bundle : Fin k → Finset (Fin m)) (next : Fin k → Policy m k r) :
      Policy m k (r + 1)

/-- Bundle payoff under a nonnegative additive valuation on individual goods. -/
def bundleValue {m : ℕ} (v : Fin m → ℝ) (bundle : Finset (Fin m)) : ℝ :=
  ∑ g ∈ bundle, v g

/-- Every revealed type gets its target at the present node, with the same
    requirement recursively applied to all possible future revelations. -/
def Policy.Guarantees {m k : ℕ} (v : Fin k → Fin m → ℝ)
    (target : Fin k → ℝ) :
    {r : ℕ} → Policy m k r → Finset (Fin m) → Prop
  | 0, .done, _ => True
  | _ + 1, .step bundle next, remaining =>
      ∀ t, bundle t ⊆ remaining ∧
        target t ≤ bundleValue (v t) (bundle t) ∧
        (next t).Guarantees v target (remaining \ bundle t)

/-- A one-step extension that maintains an invariant builds a deterministic
    strategy for all horizons and all revelation histories. -/
theorem policy_of_steps {m k : ℕ} {State : Type}
    (remaining : State → Finset (Fin m))
    (valid : ℕ → State → Prop)
    (v : Fin k → Fin m → ℝ) (target : Fin k → ℝ)
    (advance : ∀ r state, valid (r + 1) state → ∀ t : Fin k,
      ∃ bundle next, bundle ⊆ remaining state ∧
        target t ≤ bundleValue (v t) bundle ∧
        remaining next = remaining state \ bundle ∧ valid r next) :
    ∀ r state, valid r state →
      ∃ policy : Policy m k r, policy.Guarantees v target (remaining state) := by
  classical
  intro r
  induction r with
  | zero =>
    intro state _
    exact ⟨.done, trivial⟩
  | succ r ih =>
    intro state hs
    have children (t : Fin k) :
        ∃ pair : Finset (Fin m) × Policy m k r,
          pair.1 ⊆ remaining state ∧ target t ≤ bundleValue (v t) pair.1 ∧
          pair.2.Guarantees v target (remaining state \ pair.1) := by
      obtain ⟨bundle, next, hsub, hpay, hnext, hvalid⟩ := advance r state hs t
      obtain ⟨policy, hpolicy⟩ := ih next hvalid
      exact ⟨(bundle, policy), hsub, hpay, hnext ▸ hpolicy⟩
    exact ⟨.step (fun t => (Classical.choose (children t)).1)
      (fun t => (Classical.choose (children t)).2),
      fun t => Classical.choose_spec (children t)⟩

private theorem exists_bucket_parameter (k : ℕ) :
    ∃ j : ℕ, k ≤ 32 * j ^ 2 := by
  refine ⟨k + 1, ?_⟩
  calc
    k ≤ k + 1 := Nat.le_succ k
    _ ≤ (k + 1) ^ 2 := by
      simpa only [pow_two, Nat.mul_comm, Nat.one_mul] using
        Nat.mul_le_mul_right (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
    _ ≤ 32 * (k + 1) ^ 2 := by
      exact Nat.le_mul_of_pos_left _ (by decide)

/-- The least j with k ≤ 32 j² is the paper's ceil(sqrt(k/32)). -/
noncomputable def bucketMultiplier (k : ℕ) : ℕ :=
  212 + 4 * Nat.find (exists_bucket_parameter k)

theorem bucketMultiplier_spec (k : ℕ) :
    ∃ j : ℕ, bucketMultiplier k = 212 + 4 * j ∧ k ≤ 32 * j ^ 2 ∧
      ∀ i < j, 32 * i ^ 2 < k :=
  ⟨Nat.find (exists_bucket_parameter k), rfl, Nat.find_spec (exists_bucket_parameter k),
    fun _ hi => Nat.lt_of_not_ge (Nat.find_min (exists_bucket_parameter k) hi)⟩

theorem bucketMultiplier_bounds {k : ℕ} (hk : 0 < k) :
    216 ≤ bucketMultiplier k ∧
      4 ∣ bucketMultiplier k ∧
      k ≤ 2 * (bucketMultiplier k - 212) ^ 2 := by
  let j := Nat.find (exists_bucket_parameter k)
  have hj : k ≤ 32 * j ^ 2 := Nat.find_spec (exists_bucket_parameter k)
  have hjpos : 0 < j := by
    by_contra hn
    have hz : j = 0 := Nat.eq_zero_of_not_pos hn
    simp [hz] at hj
    omega
  change 216 ≤ 212 + 4 * j ∧ 4 ∣ 212 + 4 * j ∧
    k ≤ 2 * (212 + 4 * j - 212) ^ 2
  refine ⟨by omega, ⟨53 + j, by omega⟩, ?_⟩
  rw [show 212 + 4 * j - 212 = 4 * j by omega, mul_pow]
  simpa [← Nat.mul_assoc] using hj

theorem Policy.Guarantees.mono {m k n : ℕ} {policy : Policy m k n}
    {remaining : Finset (Fin m)} {v : Fin k → Fin m → ℝ} {a b : Fin k → ℝ}
    (hp : policy.Guarantees v a remaining) (hle : ∀ t, b t ≤ a t) :
    policy.Guarantees v b remaining := by
  induction policy generalizing remaining with
  | done => trivial
  | step bundle next ih =>
    intro t
    obtain ⟨hsub, hpay, hchild⟩ := hp t
    exact ⟨hsub, (hle t).trans hpay, ih t hchild⟩

end OnlineMMS
