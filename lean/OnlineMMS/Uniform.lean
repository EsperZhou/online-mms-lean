import OnlineMMS.Model
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-! The attainable instance fractions and their worst case over all instances and horizons. -/

namespace OnlineMMS

open Set

/-- A fixed benchmark from a type's original horizon and item valuation. -/
abbrev Benchmark := (n : ℕ) → 0 < n → (m : ℕ) → (Fin m → ℝ) → ℝ

variable {m n k : ℕ}

def achievableFactors (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ) (n : ℕ) : Set ℝ :=
  {a | a ∈ Icc 0 1 ∧ ∃ policy : Policy m k n,
      policy.Guarantees v (fun t => a * b t) Finset.univ}

noncomputable def instanceFactor (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ) (n : ℕ) : ℝ :=
  sSup (achievableFactors v b n)

/-- The best deterministic fraction on each finite instance with nonnegative valuations. -/
def instanceFactors (b : Benchmark) (k : ℕ) : Set ℝ :=
  {q | ∃ n : ℕ, ∃ hn : 0 < n, ∃ m : ℕ, ∃ v : Fin k → Fin m → ℝ,
    (∀ t g, 0 ≤ v t g) ∧ q = instanceFactor v (fun t => b n hn m (v t)) n}

noncomputable def uniformFactor (b : Benchmark) (k : ℕ) : ℝ :=
  sInf (instanceFactors b k)

theorem achievableFactors_zero (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ) (n : ℕ) :
    0 ∈ achievableFactors v b n := by
  refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
  have hzero : ∃ policy : Policy m k n,
    policy.Guarantees v (fun _ => 0) Finset.univ := by
    apply policy_of_steps (fun _ : Unit => Finset.univ) (fun _ _ => True) v
      (fun _ => 0) ?_ n () trivial
    intro r state _ t
    exact ⟨∅, (), by simp, by simp [bundleValue], by simp, trivial⟩
  simpa only [zero_mul] using hzero

private theorem achievableFactors_bddAbove (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ) (n : ℕ) :
    BddAbove (achievableFactors v b n) :=
  ⟨1, fun _ ha => ha.1.2⟩

theorem instanceFactor_nonneg (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ) (n : ℕ) :
    0 ≤ instanceFactor v b n :=
  le_csSup (achievableFactors_bddAbove v b n) (achievableFactors_zero v b n)

private theorem finite_policy (m k n : ℕ) : Finite (Policy m k n) := by
  induction n with
  | zero =>
    apply Finite.of_injective (fun (_ : Policy m k 0) => ())
    intro p q _
    cases p
    cases q
    rfl
  | succ n ih =>
    letI := ih
    let encode : Policy m k (n + 1) → (Fin k → Finset (Fin m)) × (Fin k → Policy m k n)
      | .step bundle next => (bundle, next)
    apply Finite.of_injective encode
    intro p q h
    cases p
    cases q
    simpa [encode] using h

private theorem isClosed_guarantees (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ)
    (p : Policy m k n) (remaining : Finset (Fin m)) :
    IsClosed {a : ℝ | p.Guarantees v (fun t => a * b t) remaining} := by
  induction n generalizing remaining with
  | zero =>
    cases p
    exact isClosed_const
  | succ n ih =>
    cases p with
    | step bundle next =>
      have hEq : {a : ℝ | (Policy.step bundle next).Guarantees v (fun t => a * b t) remaining} =
          ⋂ t, (setOf (fun _ : ℝ => bundle t ⊆ remaining) ∩
            ({a : ℝ | a * b t ≤ bundleValue (v t) (bundle t)} ∩
              {a : ℝ | (next t).Guarantees v (fun i => a * b i) (remaining \ bundle t)})) := by
        ext a
        simp [Policy.Guarantees]
      rw [hEq]
      exact isClosed_iInter fun t => isClosed_const.inter
        ((isClosed_le (continuous_id.mul continuous_const) continuous_const).inter (ih _ _))

/-- The instance supremum is attained by a feasible deterministic policy. -/
theorem instanceFactor_attained (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ) (n : ℕ) :
    IsGreatest (achievableFactors v b n) (instanceFactor v b n) := by
  letI : Finite (Policy m k n) := finite_policy m k n
  have hEq : achievableFactors v b n =
      Icc 0 1 ∩ ⋃ p : Policy m k n, {a : ℝ | p.Guarantees v (fun t => a * b t) Finset.univ} := by
    ext a
    simp [achievableFactors]
  have hc : IsClosed (achievableFactors v b n) := by
    rw [hEq]
    exact isClosed_Icc.inter (isClosed_iUnion_of_finite fun p => isClosed_guarantees v b p _)
  have hsubset : achievableFactors v b n ⊆ Icc 0 1 := fun _ ha => ha.1
  obtain ⟨a, ha⟩ := (isCompact_Icc.of_isClosed_subset hc hsubset).exists_isGreatest
    ⟨0, achievableFactors_zero v b n⟩
  simpa only [instanceFactor, ha.csSup_eq] using ha

private theorem instanceFactors_nonempty (b : Benchmark) (k : ℕ) : (instanceFactors b k).Nonempty :=
  ⟨_, 1, Nat.zero_lt_one, 0, (fun _ _ => 0), (fun _ _ => le_rfl), rfl⟩

private theorem instanceFactors_bddBelow (b : Benchmark) (k : ℕ) : BddBelow (instanceFactors b k) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, hn, m, v, _, rfl⟩
  exact instanceFactor_nonneg v (fun t => b n hn m (v t)) n

/-- One admissible instance upper-bounds the uniform guarantee. -/
theorem uniformFactor_le_instance (b : Benchmark) (hn : 0 < n)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    uniformFactor b k ≤ instanceFactor v (fun t => b n hn m (v t)) n :=
  csInf_le (instanceFactors_bddBelow b k) ⟨n, hn, m, v, hv, rfl⟩

/-- A common policy guarantee for every finite instance survives taking the worst case. -/
theorem le_uniformFactor (b : Benchmark) (k : ℕ) {a : ℝ} (ha : a ∈ Icc 0 1)
    (policy : ∀ n (hn : 0 < n) m (v : Fin k → Fin m → ℝ), (∀ t g, 0 ≤ v t g) →
      ∃ p : Policy m k n, p.Guarantees v (fun t => a * b n hn m (v t)) Finset.univ) :
    a ≤ uniformFactor b k := by
  apply le_csInf (instanceFactors_nonempty b k)
  rintro _ ⟨n, hn, m, v, hv, rfl⟩
  exact le_csSup (achievableFactors_bddAbove v _ n) ⟨ha, policy n hn m v hv⟩

/-- On a fixed instance, larger benchmarks give a smaller best fraction. -/
theorem instanceFactor_antitone_benchmark (v : Fin k → Fin m → ℝ)
    {b₁ b₂ : Fin k → ℝ} (hb : ∀ t, b₁ t ≤ b₂ t) :
    instanceFactor v b₂ n ≤ instanceFactor v b₁ n := by
  apply csSup_le ⟨0, achievableFactors_zero v b₂ n⟩
  rintro a ⟨ha, p, hp⟩
  apply le_csSup (achievableFactors_bddAbove v b₁ n)
  exact ⟨ha, p, hp.mono (fun t => mul_le_mul_of_nonneg_left (hb t) ha.1)⟩

/-- Comparing two benchmarks pointwise reverses the comparison of their attainable fractions. -/
theorem uniformFactor_antitone_benchmark (b₁ b₂ : Benchmark) (k : ℕ)
    (hb : ∀ n (hn : 0 < n) m (v : Fin m → ℝ), (∀ g, 0 ≤ v g) → b₁ n hn m v ≤ b₂ n hn m v) :
    uniformFactor b₂ k ≤ uniformFactor b₁ k := by
  apply le_csInf (instanceFactors_nonempty b₁ k)
  rintro _ ⟨n, hn, m, v, hv, rfl⟩
  let b₁' : Fin k → ℝ := fun t => b₁ n hn m (v t)
  let b₂' : Fin k → ℝ := fun t => b₂ n hn m (v t)
  calc
    uniformFactor b₂ k ≤ instanceFactor v b₂' n :=
      csInf_le (instanceFactors_bddBelow b₂ k) ⟨n, hn, m, v, hv, rfl⟩
    _ ≤ instanceFactor v b₁' n :=
      instanceFactor_antitone_benchmark v (fun t => hb n hn m (v t) (hv t))

end OnlineMMS
