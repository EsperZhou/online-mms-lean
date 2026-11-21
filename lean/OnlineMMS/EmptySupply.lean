import OnlineMMS.RandomBenchmark

namespace OnlineMMS

/-- With no remaining goods, one return of the empty bundle serves the current
arrival. The second component counts that return. No valuations are read. -/
def emptySupplyAction {m k : ℕ} (_ : Fin k) : Finset (Fin m) × ℕ := (∅, 1)

/-- Unfold the constant action for the given number of arrivals. Each child
uses the same rule, regardless of which type arrives. -/
def emptySupplyPolicy {m k : ℕ} : (n : ℕ) → Policy m k n
  | 0 => .done
  | r + 1 => .step (fun t => (emptySupplyAction t).1) (fun _ => emptySupplyPolicy r)

theorem emptySupplyPolicy_arrival_work {m k : ℕ} (r : ℕ) (t : Fin k) :
    (match emptySupplyPolicy (m := m) (k := k) (r+1) with
     | .step bundle _ => bundle t) = (∅ : Finset (Fin m)) ∧
    (emptySupplyAction (m := m) t).2 = 1 := ⟨rfl, rfl⟩

theorem emptySupplyPolicy_full {m k n : ℕ} :
    (emptySupplyPolicy (m := m) (k := k) n).FullAllocation ∅ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    intro t
    exact ⟨fun _ h => h, by simpa [emptySupplyAction] using ih⟩

theorem emptySupplyPolicy_guarantees {m k n : ℕ} (v : Fin k → Fin m → ℝ)
    (target : Fin k → ℝ) (ht : ∀ t, target t ≤ 0) :
    (emptySupplyPolicy n).Guarantees v target ∅ := by
  induction n with
  | zero => trivial
  | succ n ih =>
    intro t
    exact ⟨fun _ h => h, by simpa [emptySupplyAction, bundleValue] using ht t,
      by simpa [emptySupplyAction] using ih⟩

/-- On a ground set with zero goods, every deterministic policy gives exactly
these bundles on all branches and for all arrival counts. -/
theorem emptySupplyPolicy_unique {k n : ℕ} (π : Policy 0 k n) : π = emptySupplyPolicy n := by
  induction π with
  | done => rfl
  | @step r bundle next ih =>
    change Policy.step bundle next =
      Policy.step (fun t => (emptySupplyAction (m := 0) t).1) (fun _ => emptySupplyPolicy r)
    have sameBundle : bundle = fun t => (emptySupplyAction (m := 0) t).1 := by
      funext t
      ext g
      exact Fin.elim0 g
    rw [sameBundle, funext ih]

end OnlineMMS
