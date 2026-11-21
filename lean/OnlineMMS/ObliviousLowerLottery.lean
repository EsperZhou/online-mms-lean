import OnlineMMS.RandomBenchmark
import Mathlib.Data.Fintype.BigOperators

namespace OnlineMMS.ObliviousFixed

/-- A finite probability space carrying an outcome. Different policies may be represented by
different atoms even when their online behavior agrees. -/
structure Law (α : Type) where
  Atom : Type
  finite : Fintype Atom
  mass : Atom → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1
  val : Atom → α

attribute [instance] Law.finite

noncomputable section
namespace Law

def mean {α} (D : Law α) (f : α → ℝ) : ℝ := ∑ i, D.mass i * f (D.val i)

def All {α} (D : Law α) (P : α → Prop) : Prop := ∀ i, P (D.val i)

def pure {α} (a : α) : Law α :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => by norm_num, by simp, fun _ => a⟩

def map {α β} (D : Law α) (f : α → β) : Law β :=
  ⟨D.Atom, D.finite, D.mass, D.nonneg, D.total, f ∘ D.val⟩

def bind {α β} (D : Law α) (f : α → Law β) : Law β where
  Atom := Σ i : D.Atom, (f (D.val i)).Atom
  finite := inferInstance
  mass a := D.mass a.1 * (f (D.val a.1)).mass a.2
  nonneg a := mul_nonneg (D.nonneg a.1) ((f _).nonneg _)
  total := by
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum, Law.total, mul_one]
  val a := (f (D.val a.1)).val a.2

@[simp] theorem mean_pure {α} (a : α) (f : α → ℝ) : (pure a).mean f = f a := by
  simp [mean, pure]

@[simp] theorem mean_map {α β} (D : Law α) (f : α → β) (g : β → ℝ) :
    (D.map f).mean g = D.mean (fun a => g (f a)) := rfl

@[simp] theorem mean_bind {α β} (D : Law α) (f : α → Law β) (g : β → ℝ) :
    (D.bind f).mean g = D.mean (fun a => (f a).mean g) := by
  change (∑ a : Σ i : D.Atom, (f (D.val i)).Atom,
    (D.mass a.1 * (f (D.val a.1)).mass a.2) * g ((f (D.val a.1)).val a.2)) = _
  rw [Fintype.sum_sigma]
  simp only [mean, mul_assoc, Finset.mul_sum]

@[simp] theorem mean_const {α} (D : Law α) (c : ℝ) : D.mean (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, D.total]

theorem mean_congr {α} {D : Law α} {f g : α → ℝ} (h : D.All (fun a => f a = g a)) :
    D.mean f = D.mean g := Finset.sum_congr rfl (fun i _ => congrArg (D.mass i * ·) (h i))

theorem mean_mono {α} {D : Law α} {f g : α → ℝ} (h : D.All (fun a => f a ≤ g a)) :
    D.mean f ≤ D.mean g := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (D.nonneg i))

theorem mean_add {α} (D : Law α) (f g : α → ℝ) :
    D.mean (fun a => f a + g a) = D.mean f + D.mean g := by simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_smul {α} (D : Law α) (c : ℝ) (f : α → ℝ) :
    D.mean (fun a => c * f a) = c * D.mean f := by
  unfold mean
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mean_sum {α I : Type} [Fintype I] (D : Law α) (f : I → α → ℝ) :
    D.mean (fun a => ∑ i, f i a) = ∑ i, D.mean (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem all_bind {α β} {D : Law α} {f : α → Law β} {P : β → Prop}
    (h : D.All (fun a => (f a).All P)) : (D.bind f).All P := fun a => h a.1 a.2

/-- Draw an independent branch for each possible next announcement before it is known. -/
def joint {α} : (k : ℕ) → (Fin k → Law α) → Law (Fin k → α)
  | 0, _ => pure Fin.elim0
  | k+1, f => (f 0).bind fun a =>
      (joint k (Fin.tail f)).map (fun b => Fin.cons a b)

theorem joint_marginal {α} {k} (f : Fin k → Law α) (t : Fin k) (g : α → ℝ) :
    (joint k f).mean (fun choices => g (choices t)) = (f t).mean g := by
  induction k with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun t => ?_) t
    · simp [joint, Fin.cons_zero]
    · simp only [joint, mean_bind, mean_map, Fin.cons_succ, ih, mean_const, Fin.tail]

theorem joint_all {α} {k} (f : Fin k → Law α) (P : Fin k → α → Prop)
    (h : ∀ t, (f t).All (P t)) : (joint k f).All (fun a => ∀ t, P t (a t)) := by
  induction k with
  | zero => exact fun _ t => Fin.elim0 t
  | succ k ih =>
    apply all_bind
    intro a i t
    refine Fin.cases (by simpa [joint, map, Function.comp_def] using h 0 a)
      (fun t => ?_) t
    have hrest := ih (Fin.tail f) (fun t => P t.succ) (fun t => h t.succ) i t
    simpa [map, Fin.cons_succ, Function.comp_def] using hrest

/-- Use the finite support of a policy law as the random tape from Section 2. -/
def toPolicyLottery {m k n} (D : Law (Policy m k n))
    (h : D.All (fun p => p.FullAllocation Finset.univ)) : PolicyLottery m k n where
  size := Fintype.card D.Atom
  mass i := D.mass ((Fintype.equivFin D.Atom).symm i)
  nonneg i := D.nonneg _
  total := by
    rw [← Equiv.sum_comp (Fintype.equivFin D.Atom)]; simpa using D.total
  policy i := D.val ((Fintype.equivFin D.Atom).symm i)
  feasible i := h _

def failure {m k n} (p : Policy m k n) (v : Fin k → Fin m → ℝ)
    (target : Fin k → ℝ) (R : Finset (Fin m)) (seq : Fin n → Fin k) : ℝ :=
  @ite _ (p.GuaranteesSequence v target R seq) (Classical.propDecidable _) 0 1

theorem success_eq_one_sub_mean_failure {m k n} (D : Law (Policy m k n))
    (h : D.All (fun p => p.FullAllocation Finset.univ)) (v : Fin k → Fin m → ℝ)
    (target : Fin k → ℝ) (seq : Fin n → Fin k) :
    (D.toPolicyLottery h).successMass v target seq =
      1 - D.mean (fun p => failure p v target Finset.univ seq) := by
  classical
  unfold PolicyLottery.successMass toPolicyLottery
  rw [← Equiv.sum_comp (Fintype.equivFin D.Atom)]
  simp only [Equiv.symm_apply_apply]
  unfold mean failure
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Eq.trans (Finset.sum_congr (g := D.mass) rfl ?_) D.total
  intro i _
  by_cases hp : (D.val i).GuaranteesSequence v target Finset.univ seq <;> simp [hp]

end Law
end
end OnlineMMS.ObliviousFixed
