import OnlineMMS.ManuscriptModel

/-! Literal representations of the type-prefix maps, complete allocations and
capped fraction in Section 2. -/

namespace OnlineMMS

variable {m k n : ℕ}

/-- A set valuation additive on disjoint bundles is exactly the sum of its
singleton values. Every such valuation is therefore represented by the
item-indexed real inputs to the formal model. -/
theorem additive_valuation_eq_sum_singletons {G : Type*} [DecidableEq G]
    (V : Finset G → ℝ) (h0 : V ∅ = 0)
    (hu : ∀ S T, Disjoint S T → V (S ∪ T) = V S + V T) (S : Finset G) :
    V S = ∑ g ∈ S, V {g} := by
  induction S using Finset.induction_on with
  | empty => simpa using h0
  | @insert g S hg ih =>
    have hdis : Disjoint ({g} : Finset G) S := by simpa using hg
    simpa [hg, ih] using hu {g} S hdis

/-- Relabeling the finite set of goods by `Fin m` preserves every payoff. -/
theorem bundleValue_reindex {G : Type*} (e : G ≃ Fin m) (v : G → ℝ) (S : Finset G) :
    bundleValue (fun i => v (e.symm i)) (S.map e.toEmbedding) = ∑ g ∈ S, v g := by
  simp [bundleValue]

/-- Exact MMS threshold in terms of the paper's labeled, disjoint bundles
covering all original goods. Empty parts are allowed. -/
theorem mms_threshold_iff_partition (w : Fin m → ℝ) (hn : 0 < n) (x : ℝ) :
    x ≤ maximinShare w n hn ↔ ∃ U : Fin n → Finset (Fin m),
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧ (∀ g, ∃ i, g ∈ U i) ∧
      ∀ i, x ≤ bundleValue w (U i) := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp⟩ := maximinShare_attained w hn
    refine ⟨fun i => Finset.univ.filter (fun g => p g = i), ?_, ?_, ?_⟩
    · intro i j hij
      apply Finset.disjoint_left.2
      intro g hi hj
      exact hij ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hj).2)
    · intro g
      exact ⟨p g, by simp⟩
    · intro i
      exact (h.trans hp.ge).trans (partitionMin_le_partitionValue w hn p i)
  · rintro ⟨U, hdis, hcover, hval⟩
    choose p hp using hcover
    have hparts (i : Fin n) : U i = Finset.univ.filter (fun g => p g = i) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hg
        by_contra hne
        exact Finset.disjoint_left.1 (hdis (p g) i hne) (hp g) hg
      · rintro rfl
        exact hp g
    apply le_trans _ (partitionMin_le_maximinShare w hn p)
    apply Finset.le_inf'
    intro i _
    simpa [hparts i, partitionValue, bundleValue] using hval i

/-- In round `j.val + 1` the allocator has seen exactly that many types. -/
abbrev PrefixRule (m k n : ℕ) :=
  (j : Fin n) → (Fin (j.val + 1) → Fin k) → Finset (Fin m)

def PrefixRule.toPolicy : {n : ℕ} → PrefixRule m k n → Policy m k n
  | 0, _ => .done
  | _ + 1, f => .step (fun t => f 0 (fun _ => t))
      (fun t => toPolicy (fun j s => f j.succ (Fin.cons t s)))

def Policy.toPrefixRule : {n : ℕ} → Policy m k n → PrefixRule m k n
  | 0, .done => fun j => Fin.elim0 j
  | _ + 1, .step b q => Fin.cases (fun s => b (s 0))
      (fun j s => (q (s 0)).toPrefixRule j (Fin.tail s))

@[simp] theorem Policy.toPrefixRule_toPolicy (p : Policy m k n) :
    PrefixRule.toPolicy p.toPrefixRule = p := by
  induction p with
  | done => rfl
  | @step n b q ih =>
    unfold Policy.toPrefixRule PrefixRule.toPolicy
    congr 1
    funext t
    simpa only [Fin.cases_zero, Fin.cases_succ, Fin.cons_zero, Fin.tail_cons] using ih t

@[simp] theorem PrefixRule.toPolicy_toPrefixRule (f : PrefixRule m k n) :
    (PrefixRule.toPolicy f).toPrefixRule = f := by
  induction n with
  | zero => funext j; exact Fin.elim0 j
  | succ n ih =>
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · funext s
      change f 0 (fun _ => s 0) = f 0 s
      congr 1
      funext a
      apply congrArg s
      apply Fin.ext
      have ha := a.isLt
      change a.val < 1 at ha
      change 0 = a.val
      omega
    · funext s
      change ((PrefixRule.toPolicy (fun j u => f j.succ (Fin.cons (s 0) u))).toPrefixRule i
        (Fin.tail s)) = f i.succ s
      rw [ih]
      simp

/-- The paper's prefix-indexed family of maps and Lean's finite policy tree
describe exactly the same deterministic decisions. -/
def policyPrefixEquiv : Policy m k n ≃ PrefixRule m k n where
  toFun := Policy.toPrefixRule
  invFun := PrefixRule.toPolicy
  left_inv := Policy.toPrefixRule_toPolicy
  right_inv := PrefixRule.toPolicy_toPrefixRule

theorem policy_is_finite (m k n : ℕ) : Finite (Policy m k n) :=
  Finite.of_injective policyPrefixEquiv policyPrefixEquiv.injective

/-- Finite lotteries in the benchmark admit arbitrary real probabilities on
any finite sample space, including the entire space of feasible policies. -/
noncomputable def PolicyLottery.ofFintype {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (h1 : ∑ a, w a = 1)
    (pol : A → Policy m k n) (hpol : ∀ a, (pol a).FullAllocation Finset.univ) :
    PolicyLottery m k n where
  size := Fintype.card A
  mass := fun i => w ((Fintype.equivFin A).symm i)
  nonneg := fun _ => hw _
  total := by
    rw [← h1]
    apply Fintype.sum_equiv (Fintype.equivFin A).symm
    intro i
    rfl
  policy := fun i => pol ((Fintype.equivFin A).symm i)
  feasible := fun _ => hpol _

theorem PolicyLottery.successMass_ofFintype {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (h1 : ∑ a, w a = 1)
    (pol : A → Policy m k n) (hpol : ∀ a, (pol a).FullAllocation Finset.univ)
    (v : Fin k → Fin m → ℝ) (target : Fin k → ℝ) (s : Fin n → Fin k)
    [DecidablePred (fun a => (pol a).GuaranteesSequence v target Finset.univ s)] :
    (PolicyLottery.ofFintype w hw h1 pol hpol).successMass v target s =
      ∑ a, if (pol a).GuaranteesSequence v target Finset.univ s then w a else 0 := by
  classical
  unfold PolicyLottery.successMass
  apply Fintype.sum_equiv (Fintype.equivFin A).symm
  intro i
  by_cases hp : (pol ((Fintype.equivFin A).symm i)).GuaranteesSequence v target Finset.univ s <;>
    simp [PolicyLottery.ofFintype, hp]

/-- An ordered record of actual types and their bundles. -/
def Policy.playHistory : {n : ℕ} → Policy m k n → (Fin n → Fin k) →
    List (Fin k × Finset (Fin m))
  | 0, .done, _ => []
  | _ + 1, .step b q, s => (s 0, b (s 0)) :: (q (s 0)).playHistory (Fin.tail s)

private def coveredGoods : List (Finset (Fin m)) → Finset (Fin m)
  | [] => ∅
  | B :: rest => B ∪ coveredGoods rest

private theorem disjoint_coveredGoods (B : Finset (Fin m)) (bs : List (Finset (Fin m))) :
    Disjoint B (coveredGoods bs) ↔ ∀ A ∈ bs, Disjoint B A := by
  induction bs with
  | nil => simp [coveredGoods]
  | cons A tail ih => simp [coveredGoods, Finset.disjoint_union_right, ih]

/-- The portion of the manuscript's feasibility condition that pertains to
one play. Empty bundles may appear and must be included in the union. -/
def completePartition (bs : List (Finset (Fin m))) (R : Finset (Fin m)) : Prop :=
  bs.Pairwise Disjoint ∧ coveredGoods bs = R

private theorem completePartition_cons (B : Finset (Fin m)) (bs : List (Finset (Fin m)))
    (R : Finset (Fin m)) :
    completePartition (B :: bs) R ↔ B ⊆ R ∧ completePartition bs (R \ B) := by
  classical
  simp only [completePartition, List.pairwise_cons, coveredGoods, ← disjoint_coveredGoods]
  constructor
  · rintro ⟨⟨hd, hpair⟩, rfl⟩
    refine ⟨Finset.subset_union_left, hpair, ?_⟩
    ext g
    have hgd : g ∈ B → g ∉ coveredGoods bs :=
      fun hB htail => (Finset.disjoint_left.1 hd) hB htail
    simp [Finset.mem_sdiff, Finset.mem_union]
    tauto
  · rintro ⟨hsub, hpair, hcover⟩
    rw [hcover]
    refine ⟨⟨?_, hpair⟩, ?_⟩
    · exact Finset.disjoint_left.2 fun g hg h => (Finset.mem_sdiff.1 h).2 hg
    · ext g
      simp only [Finset.mem_union, Finset.mem_sdiff]
      have := @hsub g
      tauto

/-- The recursive full-allocation predicate equals pairwise disjointness and
exhaustion of the initial goods on every type sequence. -/
theorem Policy.fullAllocation_iff_partitions (p : Policy m k n) (R : Finset (Fin m)) :
    p.FullAllocation R ↔ ∀ s, completePartition ((p.playHistory s).map Prod.snd) R := by
  induction p generalizing R with
  | done =>
    simp [Policy.FullAllocation, Policy.playHistory, completePartition, coveredGoods, eq_comm]
  | @step n b q ih =>
    constructor
    · intro h s
      exact (completePartition_cons _ _ _).2
        ⟨(h (s 0)).1, (ih (s 0) _).1 (h (s 0)).2 (Fin.tail s)⟩
    · intro h t
      have hh (s : Fin n → Fin k) := h (Fin.cons t s)
      simp only [Policy.playHistory, Fin.cons_zero, Fin.tail_cons, List.map_cons,
        completePartition_cons] at hh
      exact ⟨(hh fun _ => t).1, (ih t _).2 (fun s => (hh s).2)⟩

/-- The minimum of one and the value/share ratios of agents with positive
original share. A history with only zero shares has score one. -/
noncomputable def cappedHistoryScore (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ) :
    List (Fin k × Finset (Fin m)) → ℝ
  | [] => 1
  | (t,B) :: rest => if 0 < b t then min (bundleValue (v t) B / b t) (cappedHistoryScore v b rest)
      else cappedHistoryScore v b rest

theorem cappedHistoryScore_one_of_zero_shares (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ)
    (h : List (Fin k × Finset (Fin m))) (hzero : ∀ e ∈ h, b e.1 = 0) :
    cappedHistoryScore v b h = 1 := by
  induction h with
  | nil => rfl
  | cons e tail ih =>
    obtain ⟨t,B⟩ := e
    have ht : b t = 0 := hzero (t,B) (List.mem_cons_self ..)
    simp [cappedHistoryScore, ht, ih fun e he => hzero e (List.mem_cons_of_mem _ he)]

theorem le_cappedHistoryScore_iff (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ)
    (h : List (Fin k × Finset (Fin m))) (x : ℝ) :
    x ≤ cappedHistoryScore v b h ↔
      x ≤ 1 ∧ ∀ e ∈ h, 0 < b e.1 → x ≤ bundleValue (v e.1) e.2 / b e.1 := by
  induction h with
  | nil => simp [cappedHistoryScore]
  | cons e h ih =>
    obtain ⟨t,B⟩ := e
    by_cases ht : 0 < b t <;>
      simp [cappedHistoryScore, ht, le_min_iff, ih, and_assoc, and_left_comm, and_comm]

/-- Under the manuscript's feasibility convention, the event used by the
oblivious lottery is exactly the condition that the published capped score
is at least the requested fraction. The fixed benchmark is never recomputed. -/
theorem Policy.score_iff_guaranteesSequence (p : Policy m k n)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) (b : Fin k → ℝ)
    (hb : ∀ t, 0 ≤ b t) (x : ℝ) (hx : x ≤ 1) (R : Finset (Fin m))
    (hfull : p.FullAllocation R) (s : Fin n → Fin k) :
    x ≤ cappedHistoryScore v b (p.playHistory s) ↔
      p.GuaranteesSequence v (fun t => x * b t) R s := by
  induction p generalizing R with
  | done => simp [Policy.playHistory, cappedHistoryScore, Policy.GuaranteesSequence, hx]
  | @step n bundles next ih =>
    obtain ⟨hsub, htail⟩ := hfull (s 0)
    have hiff := ih (s 0) _ htail (Fin.tail s)
    by_cases ht : 0 < b (s 0)
    · simp only [Policy.playHistory, cappedHistoryScore, if_pos ht, le_min_iff,
        le_div_iff₀ ht, hiff, Policy.GuaranteesSequence, hsub, true_and]
    · have hzero := le_antisymm (le_of_not_gt ht) (hb (s 0))
      have hval : 0 ≤ bundleValue (v (s 0)) (bundles (s 0)) :=
        Finset.sum_nonneg fun g _ => hv _ g
      simp only [Policy.playHistory, cappedHistoryScore, if_neg ht, hiff, Policy.GuaranteesSequence,
        hsub, true_and, hzero, mul_zero, hval, lt_irrefl, if_false]

/-- The least capped score of a policy over every length-`n` sequence. -/
noncomputable def Policy.worstScore (p : Policy m k n) (hk : 0 < k)
    (v : Fin k → Fin m → ℝ) (b : Fin k → ℝ) : ℝ := by
  letI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  exact Finset.univ.inf' Finset.univ_nonempty (fun s => cappedHistoryScore v b (p.playHistory s))

private theorem cappedHistoryScore_bounds (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g)
    (b : Fin k → ℝ) (h : List (Fin k × Finset (Fin m))) :
    0 ≤ cappedHistoryScore v b h ∧ cappedHistoryScore v b h ≤ 1 := by
  induction h with
  | nil => exact ⟨zero_le_one, le_rfl⟩
  | cons e tail ih =>
    obtain ⟨t,B⟩ := e
    by_cases ht : 0 < b t
    · have hval : 0 ≤ bundleValue (v t) B := Finset.sum_nonneg fun g _ => hv t g
      rw [cappedHistoryScore, if_pos ht]
      exact ⟨le_min (div_nonneg hval ht.le) ih.1, (min_le_right _ _).trans ih.2⟩
    · simpa [cappedHistoryScore, ht] using ih

/-- The library's instance optimum equals the paper's attained maximum,
over feasible policies, of the minimum score over the type sequence. This
applies to the original MMS and to the original TPS, including zero shares. -/
theorem instanceFactor_isGreatest_worstScore (v : Fin k → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (b : Fin k → ℝ) (hb : ∀ t, 0 ≤ b t)
    (hn : 0 < n) (hk : 0 < k) :
    IsGreatest {z : ℝ | ∃ p : Policy m k n, p.FullAllocation Finset.univ ∧
      z = p.worstScore hk v b} (instanceFactor v b n) := by
  classical
  letI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  have best := instanceFactor_attained v b n
  have upper (p : Policy m k n) (hf : p.FullAllocation Finset.univ) :
      p.worstScore hk v b ≤ instanceFactor v b n := by
    let w := p.worstScore hk v b
    have hmin (s : Fin n → Fin k) : w ≤ cappedHistoryScore v b (p.playHistory s) :=
      Finset.inf'_le _ (Finset.mem_univ s)
    have hzero : 0 ≤ w := Finset.le_inf' _ _ fun s _ => (cappedHistoryScore_bounds v hv b _).1
    let s : Fin n → Fin k := fun _ => ⟨0,hk⟩
    have hone := (hmin s).trans (cappedHistoryScore_bounds v hv b _).2
    apply best.2
    refine ⟨⟨hzero,hone⟩,p,(Policy.guarantees_iff_sequences _ _ _ _).2 (fun s => ?_)⟩
    exact (p.score_iff_guaranteesSequence v hv b hb w hone _ hf s).1 (hmin s)
  constructor
  · obtain ⟨_, p, hf, hp⟩ :=
      (achievableFactors_iff_full hv b hn (instanceFactor v b n)).1 best.1
    refine ⟨p,hf,le_antisymm ?_ (upper p hf)⟩
    apply Finset.le_inf'
    intro s _
    exact (p.score_iff_guaranteesSequence v hv b hb _ best.1.1.2 _ hf s).2
      ((Policy.guarantees_iff_sequences _ _ _ _).1 hp s)
  · rintro _ ⟨p,hp,rfl⟩
    exact upper p hp

end OnlineMMS
