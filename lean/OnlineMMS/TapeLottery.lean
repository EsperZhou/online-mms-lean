import OnlineMMS.PolicyPaths
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Real

/-! Correspondence between finite policy lotteries and probability measures on
arbitrary random tapes. Random choices may have arbitrary real probabilities. -/

open MeasureTheory

namespace OnlineMMS

variable {m k n : ℕ}

/-- Probability of any property of the realized deterministic policy. -/
noncomputable def PolicyLottery.eventMass (D : PolicyLottery m k n)
    (P : Policy m k n → Prop) : ℝ := by
  classical
  exact ∑ i, if P (D.policy i) then D.mass i else 0

theorem PolicyLottery.eventMass_ofFintype {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (h1 : ∑ a, w a = 1)
    (pol : A → Policy m k n) (hpol : ∀ a, (pol a).FullAllocation Finset.univ)
    (P : Policy m k n → Prop) [DecidablePred P] :
    (PolicyLottery.ofFintype w hw h1 pol hpol).eventMass P =
      ∑ a, if P (pol a) then w a else 0 := by
  classical
  unfold PolicyLottery.eventMass
  apply Fintype.sum_equiv (Fintype.equivFin A).symm
  intro i
  by_cases hp : P (pol ((Fintype.equivFin A).symm i)) <;> simp [PolicyLottery.ofFintype, hp]

/-- Measurability of the response to each individual type prefix makes the
realized policy measurable in the discrete finite policy space. -/
theorem measurable_policy_fiber_of_prefixes {T : Type*} [MeasurableSpace T]
    (draw : T → Policy m k n)
    (h : ∀ j s B, MeasurableSet {ω | (draw ω).toPrefixRule j s = B}) (p : Policy m k n) :
    MeasurableSet (draw ⁻¹' {p}) := by
  have he : draw ⁻¹' {p} =
      ⋂ (j : Fin n) (s : Fin (j.val + 1) → Fin k),
        {ω | (draw ω).toPrefixRule j s = p.toPrefixRule j s} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro hω
      rw [hω]
      intros
      rfl
    · intro hω
      apply policyPrefixEquiv.injective
      funext j s
      exact hω j s
  rw [he]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun s => h j s _

/-- Every measurable random tape induces one lottery preserving all events
on policies simultaneously. If feasibility holds almost surely, the choices
on its null exceptional set can be replaced by one feasible policy. -/
theorem exists_lottery_of_measurable_random_tape {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (draw : T → Policy m k n)
    (hm : ∀ p, MeasurableSet (draw ⁻¹' {p}))
    (hf : ∀ᵐ ω ∂μ, (draw ω).FullAllocation Finset.univ) :
    ∃ D : PolicyLottery m k n, ∀ P : Policy m k n → Prop,
      D.eventMass P = μ.real {ω | P (draw ω)} := by
  classical
  letI : Finite (Policy m k n) := policy_is_finite m k n
  letI : Fintype (Policy m k n) := Fintype.ofFinite _
  obtain ⟨ω₀, h₀⟩ := hf.exists
  let repair (p : Policy m k n) := if p.FullAllocation Finset.univ then p else draw ω₀
  have hrepair (p : Policy m k n) : (repair p).FullAllocation Finset.univ := by
    by_cases h : p.FullAllocation Finset.univ <;> simp [repair, h, h₀]
  let w (p : Policy m k n) := μ.real (draw ⁻¹' {p})
  have hw (p : Policy m k n) : 0 ≤ w p := measureReal_nonneg
  have h1 : ∑ p, w p = 1 := by
    simpa [w] using
      (sum_measureReal_preimage_singleton (μ := μ) Finset.univ (fun p _ => hm p))
  refine ⟨PolicyLottery.ofFintype w hw h1 repair hrepair, fun P => ?_⟩
  rw [PolicyLottery.eventMass_ofFintype, ← Finset.sum_filter]
  let S := Finset.univ.filter (fun p => P (repair p))
  calc
    ∑ p ∈ S, w p = μ.real (draw ⁻¹' (S : Set (Policy m k n))) :=
      sum_measureReal_preimage_singleton S (fun p _ => hm p)
    _ = μ.real {ω | P (draw ω)} := by
      apply measureReal_congr
      filter_upwards [hf] with ω hω
      change (draw ω ∈ S) = P (draw ω)
      simp [S, repair, hω]

/-- In particular the very same lottery has the tape's probability of paying
every agent, for every sequence, every valuation and every fixed target. -/
theorem exists_lottery_preserving_fixed_sequences {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (draw : T → Policy m k n)
    (hm : ∀ p, MeasurableSet (draw ⁻¹' {p}))
    (hf : ∀ᵐ ω ∂μ, (draw ω).FullAllocation Finset.univ) :
    ∃ D : PolicyLottery m k n, ∀ (v : Fin k → Fin m → ℝ) (target : Fin k → ℝ)
      (s : Fin n → Fin k), D.successMass v target s =
        μ.real {ω | (draw ω).GuaranteesSequence v target Finset.univ s} := by
  obtain ⟨D, hD⟩ := exists_lottery_of_measurable_random_tape μ draw hm hf
  exact ⟨D, fun v target s => hD (fun p => p.GuaranteesSequence v target Finset.univ s)⟩

/-- It suffices that each fixed sequence has a complete allocation almost
surely. There are finitely many sequences, so a single full-measure set of
tapes is feasible for all of them. Only the decisions at individual
prefixes are required to be measurable. -/
theorem exists_lottery_of_prefix_randomness {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (draw : T → Policy m k n)
    (hm : ∀ j s B, MeasurableSet {ω | (draw ω).toPrefixRule j s = B})
    (hf : ∀ s, ∀ᵐ ω ∂μ, completePartition (((draw ω).playHistory s).map Prod.snd) Finset.univ) :
    ∃ D : PolicyLottery m k n, ∀ P : Policy m k n → Prop,
      D.eventMass P = μ.real {ω | P (draw ω)} := by
  apply exists_lottery_of_measurable_random_tape μ draw (measurable_policy_fiber_of_prefixes draw hm)
  have hall := Filter.eventually_all.mpr hf
  filter_upwards [hall] with ω hω
  exact ((draw ω).fullAllocation_iff_partitions _).2 hω

/-- Conversely, a real-weight lottery is represented by the discrete tape
selecting an index according to its stated mass. -/
noncomputable def PolicyLottery.tapeMeasure (D : PolicyLottery m k n) : Measure (Fin D.size) :=
  ∑ i, ENNReal.ofReal (D.mass i) • Measure.dirac i

theorem PolicyLottery.tapeMeasure_apply (D : PolicyLottery m k n) (s : Set (Fin D.size))
    [DecidablePred (· ∈ s)] :
    D.tapeMeasure s = ENNReal.ofReal (∑ i, if i ∈ s then D.mass i else 0) := by
  classical
  have hnn (i : Fin D.size) : 0 ≤ if i ∈ s then D.mass i else 0 := by
    split_ifs <;> simp [D.nonneg]
  rw [PolicyLottery.tapeMeasure, Measure.finset_sum_apply, ENNReal.ofReal_sum_of_nonneg
    (fun i _ => hnn i)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [Measure.smul_apply, Measure.dirac_apply, Set.indicator, hi]

instance PolicyLottery.tapeMeasure_probability (D : PolicyLottery m k n) :
    IsProbabilityMeasure D.tapeMeasure := by
  constructor
  simp [D.tapeMeasure_apply, D.total]

theorem PolicyLottery.tapeMeasure_event (D : PolicyLottery m k n) (P : Policy m k n → Prop) :
    D.tapeMeasure.real {i | P (D.policy i)} = D.eventMass P := by
  classical
  unfold Measure.real PolicyLottery.eventMass
  rw [D.tapeMeasure_apply, ENNReal.toReal_ofReal]
  · rfl
  · apply Finset.sum_nonneg
    intro i _
    split_ifs <;> simp [D.nonneg]

end OnlineMMS
