import OnlineMMS.PolicyPaths
import OnlineMMS.FiniteHorizon

/-! Observed type prefixes and the fixed-agent probability-one benchmark. -/

namespace OnlineMMS

variable {m k n : ℕ}

/-- Includes the type of the current arrival (j). -/
def typePrefix (s : Fin n → Fin k) (j : Fin n) : Fin (j.val + 1) → Fin k :=
  fun i => s ⟨i.val, lt_of_lt_of_le i.isLt j.isLt⟩

/-- Each recorded bundle is the value of the policy's prefix map at the
observed prefix; future types have no effect on that bundle. -/
theorem Policy.playHistory_eq_prefixes (p : Policy m k n) (s : Fin n → Fin k) :
    p.playHistory s = List.ofFn (fun j => (s j, p.toPrefixRule j (typePrefix s j))) := by
  induction p with
  | done => simp [Policy.playHistory]
  | @step r b q ih =>
    rw [List.ofFn_succ]
    exact congrArg (List.cons (s 0, b (s 0))) (ih (s 0) (Fin.tail s))

/-- A single distribution on complete policies chosen for each known
instance must satisfy the same target on all its fixed sequences. -/
def FixedObliviousAttainable (k n : ℕ) (hn : 0 < n) (δ x : ℝ) : Prop :=
  x ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ m (v : Fin k → Fin m → ℝ),
    (∀ t g, 0 ≤ v t g) → ∃ D : PolicyLottery m k n, ∀ s,
      1 - δ ≤ D.successMass v (fun t => x * maximinShare (v t) n hn) s

/-- Exact endpoint of the randomized optimum for the given number of agents. -/
theorem fixedOblivious_zero_iff (k n : ℕ) (hn : 0 < n) (x : ℝ) :
    FixedObliviousAttainable k n hn 0 x ↔
      x ∈ Set.Icc (0 : ℝ) 1 ∧ x ≤ alphaHorizonMMS k n hn := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, le_horizonFactor_of_policies _ hn hx ?_⟩
    intro m v hv
    obtain ⟨D,hD⟩ := h m v hv
    obtain ⟨p,_,hp⟩ := (oblivious_probability_one_iff v _).1
      ⟨D, fun s => by simpa using hD s⟩
    exact ⟨p,hp⟩
  · rintro ⟨hx,hx'⟩
    refine ⟨hx, fun m v hv => ?_⟩
    let b := fun t => maximinShare (v t) n hn
    have hle : x ≤ instanceFactor v b n :=
      hx'.trans (horizonFactor_le_instance (fun n hn _ w => maximinShare w n hn) hn v hv)
    obtain ⟨_, p, hp⟩ := (instanceFactor_attained v b n).1
    have hpay := hp.mono (b := fun t => x * b t) (fun t =>
      mul_le_mul_of_nonneg_right hle (maximinShare_nonnegative _ (hv t) hn))
    obtain ⟨D, hD⟩ := (oblivious_probability_one_iff v _).2
      ⟨p.finish _, p.finish_full hn _, p.guarantees_finish hv hpay⟩
    exact ⟨D, fun s => by simpa [b] using hD s⟩

theorem fixedOblivious_zero_sup (k n : ℕ) (hn : 0 < n) :
    sSup {x : ℝ | FixedObliviousAttainable k n hn 0 x} = alphaHorizonMMS k n hn := by
  have h0 : 0 ≤ alphaHorizonMMS k n hn :=
    le_horizonFactor _ hn fun m v _ => instanceFactor_nonneg v _ n
  have h1 : alphaHorizonMMS k n hn ≤ 1 := horizonFactor_le_one _ hn
  apply IsGreatest.csSup_eq
  exact ⟨(fixedOblivious_zero_iff _ _ hn _).2 ⟨⟨h0,h1⟩, le_rfl⟩,
    fun x hx => ((fixedOblivious_zero_iff _ _ hn _).1 hx).2⟩

end OnlineMMS
