import OnlineMMS.Model
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Fintype.Pi

namespace OnlineMMS

/-- Feasibility and target payments on one fixed sequence of revealed types. -/
def Policy.GuaranteesSequence {m k : ℕ} (v : Fin k → Fin m → ℝ)
    (target : Fin k → ℝ) :
    {n : ℕ} → Policy m k n → Finset (Fin m) → (Fin n → Fin k) → Prop
  | 0, .done, _, _ => True
  | _ + 1, .step bundle next, remaining, seq =>
      bundle (seq 0) ⊆ remaining ∧
        target (seq 0) ≤ bundleValue (v (seq 0)) (bundle (seq 0)) ∧
        (next (seq 0)).GuaranteesSequence v target (remaining \ bundle (seq 0)) (Fin.tail seq)

theorem Policy.guarantees_iff_sequences {m k n : ℕ} (v : Fin k → Fin m → ℝ)
    (target : Fin k → ℝ) (p : Policy m k n) (R : Finset (Fin m)) :
    p.Guarantees v target R ↔ ∀ seq, p.GuaranteesSequence v target R seq := by
  induction p generalizing R with
  | done => simp [Policy.Guarantees, Policy.GuaranteesSequence]
  | @step r bundle next ih =>
    constructor
    · intro hp seq
      obtain ⟨hsub, hpay, hchild⟩ := hp (seq 0)
      exact ⟨hsub, hpay, (ih (seq 0) _).mp hchild (Fin.tail seq)⟩
    · intro hp t
      let seq : Fin (r + 1) → Fin k := fun _ => t
      have h := hp seq
      change bundle t ⊆ R ∧ target t ≤ bundleValue (v t) (bundle t) ∧
        (next t).GuaranteesSequence v target (R \ bundle t) (Fin.tail seq) at h
      refine ⟨h.1, h.2.1, (ih t _).mpr (fun tail => ?_)⟩
      have he := hp (Fin.cons (α := fun _ => Fin k) t tail)
      simpa [Policy.GuaranteesSequence] using he.2.2

open Filter

/-- A finite intersection of probability-one success events allows one fixed
tape to serve every arrival history. The filter can be the almost-everywhere
filter of any probability distribution on tapes. -/
theorem exists_tape_guaranteeing_all_sequences {Tape : Type*} {m k n : ℕ}
    (f : Filter Tape) [NeBot f] (policy : Tape → Policy m k n)
    (v : Fin k → Fin m → ℝ) (target : Fin k → ℝ) (R : Finset (Fin m))
    (h : ∀ seq, ∀ᶠ tape in f, (policy tape).GuaranteesSequence v target R seq) :
    ∃ tape, (policy tape).Guarantees v target R := by
  have hall : ∀ᶠ tape in f, ∀ seq, (policy tape).GuaranteesSequence v target R seq :=
    Filter.eventually_all.mpr h
  obtain ⟨tape, htape⟩ := hall.exists
  exact ⟨tape, (Policy.guarantees_iff_sequences v target (policy tape) R).mpr htape⟩

end OnlineMMS
