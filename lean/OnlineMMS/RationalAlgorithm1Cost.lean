import OnlineMMS.RationalAlgorithm1
import OnlineMMS.BucketSelectorCost

namespace OnlineMMS.RationalAlgorithm1

open RationalArithmetic BucketBitComplexity
open private initial initialWithTPS smallQ sampleQ widthQ qCoeff cCoeff eligible
  from OnlineMMS.RationalAlgorithm1

/-- A ghost history pairs each sampled good with the weights recorded at
the time of its removal. Distinct goods bound all product lengths. -/
structure GridHistory {m k : ℕ} (h : ℕ) (D : Fin k → ℕ) (x : State m k) : Prop where
  weights : ∀ t g, OnGrid (D t) (x.weight t g) ∧ (0 ≤ x.weight t g ∧ x.weight t g ≤ 1)
  recorded : ∃ past : List (Fin m × (Fin k → ℚ)),
    (past.map Prod.fst).Nodup ∧
    (∀ g ∈ past.map Prod.fst, g ∉ x.remaining) ∧
    (∀ p ∈ past, ∀ t, OnGrid (D t) (p.2 t) ∧ (0 ≤ p.2 t ∧ p.2 t ≤ 1)) ∧
    ∀ t, x.products t = sampleProductQ h (past.map (fun p => p.2 t))

private theorem sampleProductQ_append (h : ℚ) (a b : List ℚ) :
    sampleProductQ h (a ++ b) = sampleProductQ h a * sampleProductQ h b := by
  simp [sampleProductQ]

private theorem GridHistory.small {m k h : ℕ} {D : Fin k → ℕ} (hD : ∀ t, 0 < D t)
    {x : State m k} (hx : GridHistory h D x) (r : ℕ) (B : Finset (Fin m)) :
    GridHistory h D (smallQ r x B) := by
  obtain ⟨past, hnd, hrem, he, hp⟩ := hx.recorded
  constructor
  · intro t g
    have hg := trimWeightsQ_onGrid (hD t) (x.remaining \ B) (x.weight t)
      (r + x.sampleCount) (fun i => (hx.weights t i).1) g
    have hb := (trimWeights_spec (x.remaining \ B) (fun i => (x.weight t i : ℝ))
      (fun i => by dsimp; exact_mod_cast (hx.weights t i).2.1)
      ((r : ℝ) + x.sampleCount) (by positivity)).1 g
    have hreal := trimWeightsQ_cast (x.remaining \ B) (x.weight t) (r + (x.sampleCount : ℚ)) g
    push_cast at hreal
    rw [← hreal] at hb
    have hl := hb.2.trans (show (x.weight t g : ℝ) ≤ 1 by exact_mod_cast (hx.weights t g).2.2)
    rw [smallQ_weight]
    exact ⟨by simpa only [Nat.cast_add] using hg,
      by exact_mod_cast hb.1, by exact_mod_cast hl⟩
  · exact ⟨past, hnd, fun g hg h => hrem g hg (Finset.mem_sdiff.mp h).1, he, hp⟩

private theorem GridHistory.sample {m k h : ℕ} {D : Fin k → ℕ}
    {x : State m k} (hx : GridHistory h D x) {gs : List (Fin m)}
    (hg : gs.toFinset ⊆ x.remaining) (hnd : gs.Nodup) :
    GridHistory h D (sampleQ h x gs) := by
  obtain ⟨past, hPast, hrem, he, hp⟩ := hx.recorded
  let add := gs.map (fun g => (g, fun t => x.weight t g))
  have hadd : add.map Prod.fst = gs := by simp [add, List.map_map, Function.comp_def]
  refine ⟨hx.weights, past ++ add, ?_, ?_, ?_, ?_⟩
  · rw [List.map_append, hadd, List.nodup_append]
    exact ⟨hPast, hnd, List.disjoint_left.mpr
      (fun g hi hj => hrem g hi (hg (List.mem_toFinset.mpr hj)))⟩
  · intro g hmem h
    rw [List.map_append, hadd] at hmem
    obtain hi | hi := List.mem_append.mp hmem
    · exact hrem g hi (Finset.mem_sdiff.mp h).1
    · exact (Finset.mem_sdiff.mp h).2 (List.mem_toFinset.mpr hi)
  · intro p hp' t
    obtain h | h := List.mem_append.mp hp'
    · exact he p h t
    · obtain ⟨g, _, rfl⟩ := List.mem_map.mp h
      exact hx.weights t g
  · intro t
    rw [sampleQ_products, hp t, List.map_append, sampleProductQ_append]
    simp [add, List.map_map, Function.comp_def]

private theorem widthQ_pos {m k h b r : ℕ} {x : State m k} (hh : 0 < h) (hb : 0 < b) :
    0 < widthQ h b r x := by
  unfold widthQ
  split <;> exact Nat.mul_pos (by assumption) (by omega)

theorem advance_gridHistory {m k h b : ℕ} (hh : 0 < h) (hb : 0 < b) (d : Fin k → ℚ)
    {D : Fin k → ℕ} (hD : ∀ t, 0 < D t) (r : ℕ) {x : State m k}
    (hx : GridHistory h D x) (t : Fin k) :
    GridHistory h D (advance h b d r x t).2 := by
  by_cases hr : r = 0
  · obtain ⟨past, hnd, _, he, hp⟩ := hx.recorded
    rw [advance, if_pos hr]
    exact ⟨hx.weights, past, hnd, by simp, he, hp⟩
  rw [advance, if_neg hr]
  by_cases ht : 0 < d t
  · rw [if_pos ht]
    dsimp only
    by_cases hne : (eligible h x t).Nonempty
    · rw [dif_pos hne]
      exact hx.small hD r _
    · rw [dif_neg hne]
      let H := widthQ h b r x
      let buckets := rationalBuckets (x.weight t) H x.remaining
      have hH : 0 < H := widthQ_pos hh hb
      have hs := rationalBuckets_spec (x.weight t) hH x.remaining
      have hneB : ∀ B ∈ buckets, B.Nonempty :=
        fun B hB => Finset.card_pos.mp (hs.bucket_size B hB ▸ hH)
      have hg := selectQ_greedy x.weight h (qCoeff x) (cCoeff h x) x.products buckets hneB []
      have hsel := (greedy_sample_le_mean _ _ _ _ _ _ _ hg).1
      exact hx.sample (hs.selected_valid hsel).1 (hs.selected_valid hsel).2
  · rw [if_neg ht]
    exact hx.small hD r ∅

theorem initial_gridHistory {m k n h : ℕ} (v : Fin k → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (hn : 0 < n) :
    ∃ D : Fin k → ℕ, (∀ t, 0 < D t ∧ (D t).size ≤ 2 * valuationInputDigits (v t) + m + 1) ∧
      GridHistory h D (initial v n) := by
  classical
  have hD (t : Fin k) : ∃ D : ℕ, 0 < D ∧ D.size ≤ 2 * valuationInputDigits (v t) + m + 1 ∧
      ∀ g, OnGrid D (normalizedWeightQ (v t) n g) := by
    by_cases hd : 0 < truncatedShare (fun g => (v t g : ℝ)) n
    · exact normalizedWeightQ_initial_grid (v t) (hv t) hn hd
    · have he : truncatedShare (fun g => (v t g : ℝ)) n = 0 :=
        le_antisymm (le_of_not_gt hd) (truncatedShare_spec _ (fun g => by exact_mod_cast hv t g) hn).1.1
      have hz : (rationalTPS (v t) n : ℝ) = 0 := (rationalTPS_correct hn (v t) (hv t)).trans he
      have hp : rationalTPS (v t) n = 0 := by exact_mod_cast hz
      refine ⟨1, by decide, by simp [Nat.size_one], ?_⟩
      intro g
      simpa [normalizedWeightQ, hp] using onGrid_zero 1
  choose D hDpos hDb hd using hD
  refine ⟨D, fun t => ⟨hDpos t, hDb t⟩, ?_⟩
  constructor
  · intro t g
    rw [initial_weight]
    refine ⟨hd t g, ?_⟩
    have hD0 : (0 : ℚ) ≤ rationalTPS (v t) n := by
      rw [← Rat.cast_nonneg (K := ℝ), rationalTPS_correct hn (v t) (hv t)]
      exact (truncatedShare_spec _ (fun g => by exact_mod_cast hv t g) hn).1.1
    by_cases hp : 0 < rationalTPS (v t) n
    · change 0 ≤ normalizedWeightQ (v t) n g ∧ normalizedWeightQ (v t) n g ≤ 1
      unfold normalizedWeightQ
      exact ⟨div_nonneg (le_min (hv t g) hD0) hD0, (div_le_one hp).mpr (min_le_right _ _)⟩
    · have hz := le_antisymm (le_of_not_gt hp) hD0
      simp [normalizedWeightQ, hz]
  · exact ⟨[], by simp, by simp, by simp, by simp [initial, initialWithTPS, sampleProductQ]⟩

/-- Recorded products at any certified state use at most one factor per
original good. -/
theorem GridHistory.products_bounded {m k h B : ℕ} {D : Fin k → ℕ}
    {x : State m k} (hh : 1 ≤ h) (hD : ∀ t, 0 < D t ∧ (D t).size + 1 ≤ B)
    (hx : GridHistory h D x) (t : Fin k) :
    Bounded (x.products t) (productCoefficientBits h m B) := by
  obtain ⟨past, hnd, _, he, hp⟩ := hx.recorded
  have hlen := recorded_factors_le_goods (past.map Prod.fst) hnd
  rw [List.length_map] at hlen
  rw [hp t]
  apply (bounded_sampleProductQ h (past.map (fun p => p.2 t)) B hh ?_).mono
  · have h := Nat.mul_le_mul_left (h.size + B + 3) hlen
    simp only [List.length_map, productCoefficientBits]
    omega
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hg, h0, h1⟩ := he p hp t
    exact (hg.bounded (hD t).1 h0 h1).mono (hD t).2

/-- Evolve the actual rational state through a given prefix of arrivals. -/
def traceState {m k : ℕ} (h b : ℕ) (d : Fin k → ℚ) :
    ℕ → State m k → List (Fin k) → State m k
  | _, x, [] => x
  | r, x, t :: ts => traceState h b d (r - 1) (advance h b d (r - 1) x t).2 ts

theorem traceState_gridHistory {m k h b : ℕ} (hh : 0 < h) (hb : 0 < b) (d : Fin k → ℚ)
    {D : Fin k → ℕ} (hD : ∀ i, 0 < D i) (n : ℕ) {x : State m k}
    (hx : GridHistory h D x) (ts : List (Fin k)) :
    GridHistory h D (traceState h b d n x ts) := by
  induction ts generalizing n x with
  | nil => exact hx
  | cons t ts ih => exact ih _ (advance_gridHistory hh hb d hD _ hx _)

theorem length_le_candidateCount {m : ℕ} {buckets : List (Finset (Fin m))}
    (hne : ∀ B ∈ buckets, B.Nonempty) : buckets.length ≤ candidateCount buckets := by
  induction buckets with
  | nil => simp [candidateCount]
  | cons B bs ih =>
    have hpos := Finset.card_pos.mpr (hne B (by simp))
    have htail := ih (fun S hS => hne S (by simp [hS]))
    simp only [candidateCount, List.map_cons, List.length_cons, List.sum_cons] at htail ⊢
    omega

/-- For each state satisfying the inductive denominator and history
bounds, the actual sample call has polynomially bounded operands and
work in the rational-arithmetic cost model. -/
theorem rational_sampling_certificate {m k h b Dbits : ℕ} (hh : 0 < h) (hb : 0 < b)
    (r : ℕ) {x : State m k} (t : Fin k) {D : Fin k → ℕ}
    (hD : ∀ i, 0 < D i ∧ (D i).size + 1 ≤ Dbits)
    (hx : GridHistory h D x) :
    let buckets := rationalBuckets (x.weight t) (widthQ h b r x) x.remaining
    let budget := objectiveBits h k m (Dbits + m.size) (productCoefficientBits h m Dbits)
    let run := selectCosted x.weight h (qCoeff x) (cCoeff h x) x.products [] buckets
    run.1 = selectQ x.weight h (qCoeff x) (cCoeff h x) x.products [] buckets ∧
    ScoresBounded x.weight h (qCoeff x) (cCoeff h x) x.products budget [] buckets ∧
    bitCostEnvelope run.2 budget ≤ 30 * (k + 1) * (m + 1)^3 * (budget + 1)^3 := by
  let H := widthQ h b r x
  let buckets := rationalBuckets (x.weight t) H x.remaining
  let C := productCoefficientBits h m Dbits
  have hH : 0 < H := widthQ_pos hh hb
  have hs := rationalBuckets_spec (x.weight t) hH x.remaining
  have hne : ∀ B ∈ buckets, B.Nonempty :=
    fun B hB => Finset.card_pos.mp (hs.bucket_size B hB ▸ hH)
  have hCand : candidateCount buckets ≤ m := candidateCount_le_goods buckets hs.pairwise_disjoint
  have hm : ([] : List (Fin k → ℚ)).length + buckets.length ≤ m :=
    by simpa only [List.length_nil, zero_add] using (length_le_candidateCount hne).trans hCand
  have hC : 1 ≤ C := by unfold C productCoefficientBits; omega
  have hq : Bounded (qCoeff x) C := by
    unfold qCoeff
    split
    · exact bounded_one.mono hC
    · exact bounded_zero.mono hC
  have hc : Bounded (cCoeff h x) C := by
    unfold cCoeff
    split
    · exact (bounded_firstCoefficient hh).mono (by unfold C productCoefficientBits; omega)
    · exact bounded_one.mono hC
  have hprod : ∀ i, Bounded (x.products i) C := hx.products_bounded hh hD
  have hw (i : Fin k) (g : Fin m) : Bounded (x.weight i g) (Dbits + m.size) := by
    obtain ⟨hg, h0, h1⟩ := hx.weights i g
    exact (hg.bounded (hD i).1 h0 h1).mono (by have := (hD i).2; omega)
  have hmean (B : Finset (Fin m)) (hB : B ∈ buckets) (i : Fin k) :
      Bounded (slotMeanQ x.weight B i) (Dbits + m.size) := by
    have hsB := hs.bucket_size B hB
    have hM : H ≤ m := by
      rw [← hsB]
      simpa only [Fintype.card_fin] using Finset.card_le_univ B
    exact (slotMeanQ_bounded (hD i).1 hH x.weight B hsB i
      (fun g => (hx.weights i g).1) (fun g => (hx.weights i g).2)).mono (by
        have h1 := (hD i).2
        have h2 := Nat.size_le_size hM
        omega)
  obtain ⟨_, hscore, hcost⟩ := selectCosted_complete_certificate x.weight h
    (Dbits + m.size) C (qCoeff x) (cCoeff h x) x.products hh hq hc hprod hw buckets []
    (by simp) hmean hne hm hCand
  exact ⟨selectCosted_value .., hscore, hcost⟩

def inputDigits {m k : ℕ} (v : Fin k → Fin m → ℚ) : ℕ :=
  ∑ t, valuationInputDigits (v t)

/-- The rational state after a type prefix, with the horizon fixed at
initialization. -/
def policyState {m k : ℕ} (v : Fin k → Fin m → ℚ) (n : ℕ) (ts : List (Fin k)) : State m k :=
  let h := parameterQ k
  let d := materialize (fun t => rationalTPS (v t) n)
  traceState h (h / 4) d n (initial v n) ts

/-- The recorded-weight proof supplies the sampler's bit hypotheses
uniformly over every history of the implemented rule. -/
theorem policyState_gridHistory {m k n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    ∃ D : Fin k → ℕ,
      (∀ t, 0 < D t ∧ (D t).size + 1 ≤ 2 * inputDigits v + m + 2) ∧
      ∀ ts, GridHistory (parameterQ k) D (policyState v n ts) := by
  obtain ⟨D, hD, hinit⟩ := initial_gridHistory (h := parameterQ k) v hv hn
  have hh : 216 ≤ parameterQ k := by rw [parameterQ_eq]; exact (bucketMultiplier_bounds hk).1
  refine ⟨D, fun t => ⟨(hD t).1, ?_⟩, ?_⟩
  · have hsub : valuationInputDigits (v t) ≤ inputDigits v := by
      unfold inputDigits
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (valuationInputDigits (v i)))
        (Finset.mem_univ t)
    have hb := (hD t).2
    omega
  · intro ts
    exact traceState_gridHistory (by omega) (by omega) _ (fun t => (hD t).1) n hinit ts

end OnlineMMS.RationalAlgorithm1
