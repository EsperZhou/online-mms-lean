import OnlineMMS.RandomBenchmark
import OnlineMMS.FinitePartitions

/-! Policy trees, feasible allocations, and the capped score in Section 2. -/

namespace OnlineMMS

variable {m k n : ℕ}

/-- On a legal history, retain each early decision and give the last arrival all
remaining goods. Intersection also makes the completed policy legal off such histories. -/
def Policy.finish : {n : ℕ} → Policy m k n → Finset (Fin m) → Policy m k n
  | 0, .done, _ => .done
  | 1, .step _ _, R => .step (fun _ => R) (fun _ => .done)
  | _ + 2, .step b q, R => .step (fun t => b t ∩ R)
      (fun t => (q t).finish (R \ (b t ∩ R)))

theorem Policy.finish_full (p : Policy m k n) (hn : 0 < n) (R : Finset (Fin m)) :
    (p.finish R).FullAllocation R := by
  induction n generalizing R with
  | zero => omega
  | succ n ih =>
    cases p with
    | step b q =>
      cases n with
      | zero => intro t; exact ⟨Finset.Subset.rfl, Finset.sdiff_self R⟩
      | succ n =>
        intro t
        exact ⟨Finset.inter_subset_right, ih (q t) (by omega) _⟩

theorem Policy.guaranteesSequence_finish (p : Policy m k n)
    {v : Fin k → Fin m → ℝ} {target : Fin k → ℝ} {R : Finset (Fin m)}
    (hv : ∀ t g, 0 ≤ v t g) (seq : Fin n → Fin k)
    (h : p.GuaranteesSequence v target R seq) :
    (p.finish R).GuaranteesSequence v target R seq := by
  induction n generalizing R with
  | zero => cases p; trivial
  | succ n ih =>
    cases p with
    | step b q =>
      obtain ⟨hsub, hpay, htail⟩ := h
      cases n with
      | zero =>
        exact ⟨Finset.Subset.rfl, hpay.trans (bundleValue_mono _ (hv _) hsub), trivial⟩
      | succ n =>
        change b (seq 0) ∩ R ⊆ R ∧ target (seq 0) ≤ bundleValue _ (b (seq 0) ∩ R) ∧
          ((q (seq 0)).finish (R \ (b (seq 0) ∩ R))).GuaranteesSequence v target
            (R \ (b (seq 0) ∩ R)) (Fin.tail seq)
        rw [Finset.inter_eq_left.mpr hsub]
        exact ⟨hsub, hpay, ih (q (seq 0)) _ htail⟩

theorem Policy.guarantees_finish (p : Policy m k n)
    {v : Fin k → Fin m → ℝ} {target : Fin k → ℝ} {R : Finset (Fin m)}
    (hv : ∀ t g, 0 ≤ v t g) (h : p.Guarantees v target R) :
    (p.finish R).Guarantees v target R := by
  exact (Policy.guarantees_iff_sequences _ _ _ _).2 fun seq =>
    p.guaranteesSequence_finish hv seq ((Policy.guarantees_iff_sequences _ _ _ _).1 h seq)

/-- The same fractions are attainable when complete allocation is imposed. -/
theorem achievableFactors_iff_full {v : Fin k → Fin m → ℝ} (hv : ∀ t g, 0 ≤ v t g)
    (b : Fin k → ℝ) (hn : 0 < n) (x : ℝ) :
    x ∈ achievableFactors v b n ↔ x ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ p : Policy m k n, p.FullAllocation Finset.univ ∧
        p.Guarantees v (fun t => x * b t) Finset.univ := by
  constructor
  · rintro ⟨hx, p, hp⟩
    exact ⟨hx, p.finish Finset.univ, p.finish_full hn _, p.guarantees_finish hv hp⟩
  · rintro ⟨hx, p, _, hp⟩
    exact ⟨hx, p, hp⟩

/-- Point mass on a feasible deterministic policy. -/
def PolicyLottery.ofFull (p : Policy m k n) (h : p.FullAllocation Finset.univ) :
    PolicyLottery m k n where
  size := 1
  mass := fun _ => 1
  nonneg := fun _ => zero_le_one
  total := by simp
  policy := fun _ => p
  feasible := fun _ => h

theorem PolicyLottery.exists_positive (D : PolicyLottery m k n) : ∃ i, 0 < D.mass i := by
  by_contra! h
  have : ∑ i, D.mass i ≤ 0 := Finset.sum_nonpos fun i _ => h i
  linarith [D.total]

theorem PolicyLottery.successMass_one_iff (D : PolicyLottery m k n)
    (v : Fin k → Fin m → ℝ) (target : Fin k → ℝ) (seq : Fin n → Fin k) :
    1 ≤ D.successMass v target seq ↔
      ∀ i, 0 < D.mass i → (D.policy i).GuaranteesSequence v target Finset.univ seq := by
  classical
  let wins := fun i => (D.policy i).GuaranteesSequence v target Finset.univ seq
  change 1 ≤ ∑ i, (if wins i then D.mass i else 0) ↔ ∀ i, 0 < D.mass i → wins i
  constructor
  · intro h i hi
    by_contra hfail
    have hstrict : (∑ j, if wins j then D.mass j else 0) < ∑ j, D.mass j :=
      Finset.sum_lt_sum (fun j _ => by split_ifs <;> simp [D.nonneg])
        ⟨i, Finset.mem_univ i, by simpa [hfail] using hi⟩
    linarith [D.total]
  · intro h
    apply le_of_eq
    calc 1 = ∑ i, D.mass i := D.total.symm
      _ = ∑ i, (if wins i then D.mass i else 0) := Finset.sum_congr rfl fun i _ => by
        by_cases hw : wins i
        · simp [hw]
        · have hzero : D.mass i = 0 := le_antisymm (le_of_not_gt (fun hi => hw (h i hi))) (D.nonneg i)
          simp [hw, hzero]

/-- At failure tolerance zero a single positive-mass policy serves all
sequences. Both directions use the manuscript's full-allocation rule. -/
theorem oblivious_probability_one_iff (v : Fin k → Fin m → ℝ)
    (target : Fin k → ℝ) :
    (∃ D : PolicyLottery m k n, ∀ seq, 1 ≤ D.successMass v target seq) ↔
    ∃ p : Policy m k n, p.FullAllocation Finset.univ ∧ p.Guarantees v target Finset.univ := by
  classical
  constructor
  · rintro ⟨D, hD⟩
    obtain ⟨i, hi⟩ := D.exists_positive
    exact ⟨D.policy i, D.feasible i, (Policy.guarantees_iff_sequences _ _ _ _).2 fun seq =>
      (D.successMass_one_iff v target seq).1 (hD seq) i hi⟩
  · rintro ⟨p, hfull, hp⟩
    refine ⟨PolicyLottery.ofFull p hfull, fun seq => ?_⟩
    exact ((PolicyLottery.ofFull p hfull).successMass_one_iff _ _ _).2
      fun _ _ => (Policy.guarantees_iff_sequences _ _ _ _).1 hp seq

theorem oblivious_zeroFailure_attainable_iff (k : ℕ) (x : ℝ) :
    ObliviousAttainable k 0 x ↔ x ∈ Set.Icc (0 : ℝ) 1 ∧ x ≤ alphaMMS k := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, le_uniformFactor _ _ hx ?_⟩
    intro n hn m v hv
    obtain ⟨D,hD⟩ := h n hn m v hv
    obtain ⟨p, _, hpay⟩ := (oblivious_probability_one_iff v _).1
      ⟨D, fun seq => by simpa using hD seq⟩
    exact ⟨p,hpay⟩
  · rintro ⟨hx,hα⟩
    refine ⟨hx, fun n hn m v hv => ?_⟩
    let b := fun t => maximinShare (v t) n hn
    have hx' : x ≤ instanceFactor v b n := hα.trans
      (uniformFactor_le_instance (fun n hn _ w => maximinShare w n hn) hn v hv)
    obtain ⟨_, p, hp⟩ := (instanceFactor_attained v b n).1
    have hpay := hp.mono (b := fun t => x * b t) (fun t =>
      mul_le_mul_of_nonneg_right hx' (maximinShare_nonnegative _ (hv t) hn))
    obtain ⟨D, hD⟩ := (oblivious_probability_one_iff v _).2
      ⟨p.finish _, p.finish_full hn _, p.guarantees_finish hv hpay⟩
    exact ⟨D, fun seq => by simpa [b] using hD seq⟩

theorem alphaOblivious_zero (k : ℕ) : alphaOblivious k 0 = alphaMMS k := by
  have hα₀ : 0 ≤ alphaMMS k := by
    apply le_uniformFactor _ _ ⟨le_rfl, zero_le_one⟩
    intro n hn m v hv
    exact (achievableFactors_zero v (fun t => maximinShare (v t) n hn) n).2
  let v : Fin k → Fin 0 → ℝ := fun _ _ => 0
  have hα₁ : alphaMMS k ≤ 1 :=
    (uniformFactor_le_instance (fun n hn _ w => maximinShare w n hn)
      (n := 1) (by decide) v (by intros; exact le_rfl)).trans (instanceFactor_attained _ _ _).1.1.2
  apply IsGreatest.csSup_eq
  exact ⟨(oblivious_zeroFailure_attainable_iff k _).2 ⟨⟨hα₀,hα₁⟩, le_rfl⟩,
    fun x hx => ((oblivious_zeroFailure_attainable_iff k _).1 hx).2⟩

end OnlineMMS
