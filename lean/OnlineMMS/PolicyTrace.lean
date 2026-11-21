import OnlineMMS.Model

namespace OnlineMMS
namespace Policy

/-- Each action and its continuation must be obtained by the given transition
rule. The transition's first argument is the number of arrivals after the action. -/
def Follows {m k : ℕ} {σ : Type} (step : ℕ → σ → Fin k → Finset (Fin m) → σ → Prop) :
    {r : ℕ} → Policy m k r → σ → Prop
  | 0, .done, _ => True
  | r + 1, .step bundle next, state =>
    ∀ t, ∃ state', step r state t (bundle t) state' ∧ (next t).Follows step state'

theorem follows_of_steps {m k : ℕ} {σ : Type}
    (step : ℕ → σ → Fin k → Finset (Fin m) → σ → Prop) (valid : ℕ → σ → Prop)
    (advance : ∀ r state, valid (r + 1) state → ∀ t,
      ∃ bundle state', step r state t bundle state' ∧ valid r state') :
    ∀ r state, valid r state → ∃ policy : Policy m k r, policy.Follows step state := by
  classical
  intro r
  induction r with
  | zero => intro state _; exact ⟨.done, trivial⟩
  | succ r ih =>
    intro state hs
    have children (t : Fin k) :
        ∃ response : Finset (Fin m) × Policy m k r,
          ∃ next, step r state t response.1 next ∧ response.2.Follows step next := by
      obtain ⟨bundle, next, hstep, hvalid⟩ := advance r state hs t
      obtain ⟨child, hchild⟩ := ih next hvalid
      exact ⟨(bundle, child), next, hstep, hchild⟩
    exact ⟨.step (fun t => (Classical.choose (children t)).1)
      (fun t => (Classical.choose (children t)).2), fun t => Classical.choose_spec (children t)⟩

theorem Follows.guarantees {m k r : ℕ} {σ : Type}
    {step : ℕ → σ → Fin k → Finset (Fin m) → σ → Prop}
    (valid : ℕ → σ → Prop) (remaining : σ → Finset (Fin m))
    (v : Fin k → Fin m → ℝ) (target : Fin k → ℝ)
    (correct : ∀ r state t bundle next, valid (r + 1) state → step r state t bundle next →
      bundle ⊆ remaining state ∧ target t ≤ bundleValue (v t) bundle ∧
        remaining next = remaining state \ bundle ∧ valid r next)
    {policy : Policy m k r} {state : σ} (hp : policy.Follows step state)
    (hv : valid r state) : policy.Guarantees v target (remaining state) := by
  induction policy generalizing state with
  | done => trivial
  | step bundles next ih =>
    intro t
    obtain ⟨state', hstep, hchild⟩ := hp t
    obtain ⟨hsub, hpay, hremaining, hvalid⟩ := correct _ _ _ _ _ hv hstep
    exact ⟨hsub, hpay, hremaining ▸ ih t hchild hvalid⟩

end Policy
end OnlineMMS
