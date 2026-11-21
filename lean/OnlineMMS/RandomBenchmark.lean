import OnlineMMS.MainTheorem
import OnlineMMS.RandomTape

open scoped BigOperators

namespace OnlineMMS

/-- Every branch allocates only available goods and exhausts the supply. -/
def Policy.FullAllocation {m k : ℕ} :
    {n : ℕ} → Policy m k n → Finset (Fin m) → Prop
  | 0, .done, R => R = ∅
  | _ + 1, .step bundle next, R =>
      ∀ t, bundle t ⊆ R ∧ (next t).FullAllocation (R \ bundle t)

/-- A lottery is chosen for the known instance, before the sequence is revealed.
Its finitely many atoms may have arbitrary real probabilities. -/
structure PolicyLottery (m k n : ℕ) where
  size : ℕ
  mass : Fin size → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1
  policy : Fin size → Policy m k n
  feasible : ∀ i, (policy i).FullAllocation Finset.univ

noncomputable def PolicyLottery.successMass {m k n : ℕ} (D : PolicyLottery m k n)
    (v : Fin k → Fin m → ℝ) (target : Fin k → ℝ) (seq : Fin n → Fin k) : ℝ := by
  classical
  exact ∑ i, if (D.policy i).GuaranteesSequence v target Finset.univ seq then D.mass i else 0

/-- Paper benchmark. The same lottery must serve every fixed sequence on a given instance. -/
def ObliviousAttainable (k : ℕ) (δ x : ℝ) : Prop :=
  x ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ (n : ℕ) (hn : 0 < n) (m : ℕ) (v : Fin k → Fin m → ℝ),
    (∀ t g, 0 ≤ v t g) → ∃ D : PolicyLottery m k n, ∀ seq : Fin n → Fin k,
      1 - δ ≤ D.successMass v (fun t => x * maximinShare (v t) n hn) seq

/-- The supremum over simultaneous MMS fractions for oblivious sequences. -/
noncomputable def alphaOblivious (k : ℕ) (δ : ℝ) : ℝ :=
  sSup {x : ℝ | ObliviousAttainable k δ x}

end OnlineMMS
