import OnlineMMS.ManuscriptModel

/-! Adaptive arrivals in Section 2. A single opponent observes allocations and
chooses the next type. Its branches carry no random tape or unobserved policy. -/

namespace OnlineMMS

variable {m k n : ℕ}

/-- At a node the opponent first chooses an arriving type. Only the resulting
bundle is available when it selects its continuation. -/
inductive ArrivalAdversary (m k : ℕ) : ℕ → Type
  | done : ArrivalAdversary m k 0
  | ask {n : ℕ} (t : Fin k) (after : Finset (Fin m) → ArrivalAdversary m k n) :
      ArrivalAdversary m k (n + 1)

def ArrivalAdversary.constant (t : Fin k) : (n : ℕ) → ArrivalAdversary m k n
  | 0 => .done
  | n + 1 => .ask t (fun _ => constant t n)

/-- Interaction induces a type sequence; its next entry only depends on the
previously observed bundles and previous types. -/
def ArrivalAdversary.play : {n : ℕ} → ArrivalAdversary m k n → Policy m k n → Fin n → Fin k
  | 0, .done, .done => Fin.elim0
  | _ + 1, .ask t after, .step bundle next =>
    Fin.cons t ((after (bundle t)).play (next t))

/-- The target is attainable at a node exactly when every revealed type admits
a paying bundle with an attainable continuation. -/
theorem exists_guaranteeing_policy_succ (v : Fin k → Fin m → ℝ) (target : Fin k → ℝ)
    (R : Finset (Fin m)) (n : ℕ) :
    (∃ p : Policy m k (n+1), p.Guarantees v target R) ↔
    ∀ t : Fin k, ∃ B : Finset (Fin m), B ⊆ R ∧ target t ≤ bundleValue (v t) B ∧
      ∃ q : Policy m k n, q.Guarantees v target (R \ B) := by
  constructor
  · rintro ⟨p, hp⟩
    cases p with
    | step b next =>
      intro t
      obtain ⟨hsub, hpay, htail⟩ := hp t
      exact ⟨b t, hsub, hpay, next t, htail⟩
  · intro h
    choose b hsub hpay q hnext using h
    exact ⟨.step b q, fun t => ⟨hsub t, hpay t, hnext t⟩⟩

/-- At every losing history, one observation-based adversary defeats every
policy, including all realizations of a randomized policy simultaneously. -/
theorem exists_adversary_defeating_every_policy (v : Fin k → Fin m → ℝ)
    (target : Fin k → ℝ) (R : Finset (Fin m))
    (hlose : ¬∃ p : Policy m k n, p.Guarantees v target R) :
    ∃ a : ArrivalAdversary m k n, ∀ p : Policy m k n,
      ¬p.GuaranteesSequence v target R (a.play p) := by
  classical
  induction n generalizing R with
  | zero => exact (hlose ⟨.done, trivial⟩).elim
  | succ n ih =>
    rw [exists_guaranteeing_policy_succ] at hlose
    push_neg at hlose
    obtain ⟨t, ht⟩ := hlose
    have branch (B : Finset (Fin m)) : ∃ a : ArrivalAdversary m k n,
        ∀ p : Policy m k n, B ⊆ R → target t ≤ bundleValue (v t) B →
          ¬p.GuaranteesSequence v target (R \ B) (a.play p) := by
      by_cases hsub : B ⊆ R
      · by_cases hpay : target t ≤ bundleValue (v t) B
        · obtain ⟨a, ha⟩ := ih (R \ B) (by
            rintro ⟨p, hp⟩
            exact (ht B hsub hpay p) hp)
          exact ⟨a, fun p _ _ => ha p⟩
        · exact ⟨.constant t n, fun _ _ h => (hpay h).elim⟩
      · exact ⟨.constant t n, fun _ h => (hsub h).elim⟩
    choose after hafter using branch
    refine ⟨.ask t after, ?_⟩
    intro p
    cases p with
    | step b q =>
      simp only [ArrivalAdversary.play, Policy.GuaranteesSequence, Fin.cons_zero, Fin.tail_cons]
      rintro ⟨hsub, hpay, htail⟩
      exact hafter _ _ hsub hpay htail

noncomputable def PolicyLottery.adaptiveSuccessMass (D : PolicyLottery m k n)
    (v : Fin k → Fin m → ℝ) (target : Fin k → ℝ) (a : ArrivalAdversary m k n) : ℝ := by
  classical
  exact ∑ i, if (D.policy i).GuaranteesSequence v target Finset.univ (a.play (D.policy i))
    then D.mass i else 0

/-- A positive simultaneous probability of success against every adaptive
opponent is equivalent to the deterministic guarantee on the same instance. -/
theorem adaptive_lottery_iff_deterministic (v : Fin k → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (target : Fin k → ℝ) (hn : 0 < n)
    {δ : ℝ} (hδ : 0 ≤ δ) (hlt : δ < 1) :
    (∃ D : PolicyLottery m k n, ∀ a : ArrivalAdversary m k n,
      1 - δ ≤ D.adaptiveSuccessMass v target a) ↔
    ∃ p : Policy m k n, p.FullAllocation Finset.univ ∧ p.Guarantees v target Finset.univ := by
  classical
  constructor
  · rintro ⟨D, hD⟩
    by_contra hno
    have hlose : ¬∃ p : Policy m k n, p.Guarantees v target Finset.univ := by
      rintro ⟨p, hp⟩
      exact hno ⟨p.finish Finset.univ, p.finish_full hn _, p.guarantees_finish hv hp⟩
    obtain ⟨a, ha⟩ := exists_adversary_defeating_every_policy v target Finset.univ hlose
    have hzero : D.adaptiveSuccessMass v target a = 0 := by
      simp [PolicyLottery.adaptiveSuccessMass, ha]
    have := hD a
    linarith
  · rintro ⟨p, hfull, hpay⟩
    refine ⟨PolicyLottery.ofFull p hfull, ?_⟩
    intro a
    have hseq := (Policy.guarantees_iff_sequences _ _ _ _).1 hpay (a.play p)
    simp [PolicyLottery.adaptiveSuccessMass, PolicyLottery.ofFull, hseq, hδ]

/-- Every allowed number of agents and instance must admit one lottery that
achieves the same target against all observation-based opponents. -/
def AdaptiveAttainable (k : ℕ) (δ x : ℝ) : Prop :=
  x ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ n (hn : 0 < n) m (v : Fin k → Fin m → ℝ),
    (∀ t g, 0 ≤ v t g) → ∃ D : PolicyLottery m k n, ∀ a : ArrivalAdversary m k n,
       1 - δ ≤ D.adaptiveSuccessMass v (fun t => x * maximinShare (v t) n hn) a

theorem adaptiveAttainable_iff (k : ℕ) {δ x : ℝ} (hδ : 0 ≤ δ) (hlt : δ < 1) :
    AdaptiveAttainable k δ x ↔ ObliviousAttainable k 0 x := by
  constructor
  · rintro ⟨hx,h⟩
    refine ⟨hx, fun n hn m v hv => ?_⟩
    obtain ⟨p,hfull,hpay⟩ := (adaptive_lottery_iff_deterministic v hv _ hn hδ hlt).1 (h n hn m v hv)
    simpa using (oblivious_probability_one_iff v _).2 ⟨p,hfull,hpay⟩
  · rintro ⟨hx,h⟩
    refine ⟨hx, fun n hn m v hv => ?_⟩
    obtain ⟨p,hfull,hpay⟩ := (oblivious_probability_one_iff v _).1 (by simpa using h n hn m v hv)
    exact (adaptive_lottery_iff_deterministic v hv _ hn hδ hlt).2 ⟨p,hfull,hpay⟩

/-- For every failure tolerance below one, adaptive arrivals have precisely
the deterministic, worst-case original-MMS optimum. -/
theorem adaptive_sup_eq_alphaMMS (k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hlt : δ < 1) :
    sSup {x : ℝ | AdaptiveAttainable k δ x} = alphaMMS k := by
  have h : {x : ℝ | AdaptiveAttainable k δ x} = {x | ObliviousAttainable k 0 x} :=
    Set.ext fun _ => adaptiveAttainable_iff k hδ hlt
  rw [h]
  exact alphaOblivious_zero k

end OnlineMMS
