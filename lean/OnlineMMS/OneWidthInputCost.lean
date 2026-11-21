import OnlineMMS.EmptySupplyVariants
import OnlineMMS.ManuscriptPreprocessing
import OnlineMMS.RationalAlgorithm1Cost

/-! Appendix C.1. Denominator and operation bounds along the actual
one-width policy, including the recorded product after successive samples. -/

namespace OnlineMMS.RationalFixedWidth

open RationalArithmetic BucketBitComplexity
open RationalAlgorithm1 (GridHistory rationalBuckets rationalBuckets_spec length_le_candidateCount
  initial_gridHistory inputDigits)
open private RationalAlgorithm1.GridHistory.small RationalAlgorithm1.GridHistory.sample
  from OnlineMMS.RationalAlgorithm1Cost

private def productStateData {m k : ℕ} (x : State m k (Fin k → ℚ)) : RationalAlgorithm1.State m k :=
  ⟨x.remaining, x.samples, x.weight, x.stats⟩

private theorem product_advance_grid {m k h : ℕ} (hh : 0 < h) (d : Fin k → ℚ)
    {D : Fin k → ℕ} (hD : ∀ i, 0 < D i) (r : ℕ) (x : State m k (Fin k → ℚ))
    (hx : GridHistory h D (productStateData x)) (i : Fin k) :
    GridHistory h D (productStateData (advance h (1/(6*(h:ℚ))) d (productRule h) r x i).2) := by
  by_cases hr : r=0
  · obtain ⟨past,hd,_,he,hp⟩ := hx.recorded
    rw [advance, if_pos hr]
    exact ⟨hx.weights,past,hd,by simp [productStateData],he,hp⟩
  rw [advance,if_neg hr]
  by_cases ht : 0 < d i
  · rw [if_pos ht]
    dsimp only
    by_cases hel : (x.remaining.filter (fun g => 1/(6*(h:ℚ)) ≤ x.weight i g)).Nonempty
    · rw [dif_pos hel]
      exact RationalAlgorithm1.GridHistory.small hD hx r _
    · rw [dif_neg hel]
      let H := h*(r+1+x.samples)
      let bs := rationalBuckets (x.weight i) H x.remaining
      have hH : 0 < H := Nat.mul_pos hh (by omega)
      have hs := rationalBuckets_spec (x.weight i) hH x.remaining
      have hne (B : Finset (Fin m)) (hB : B ∈ bs) : B.Nonempty :=
        Finset.card_pos.mp (hs.bucket_size B hB ▸ hH)
      have hsel := (greedy_sample_le_mean _ _ _ _ _ _ _
        (selectQ_greedy x.weight h 0 1 x.stats bs hne [])).1
      exact RationalAlgorithm1.GridHistory.sample hx (hs.selected_valid hsel).1 (hs.selected_valid hsel).2
  · rw [if_neg ht]
    exact RationalAlgorithm1.GridHistory.small hD hx r ∅

private def productTrace {m k : ℕ} (h : ℕ) (d : Fin k → ℚ) :
    ℕ → State m k (Fin k → ℚ) → List (Fin k) → State m k (Fin k → ℚ)
  | _, x, [] => x
  | n, x, i :: is => productTrace h d (n-1) (advance h (1/(6*(h:ℚ))) d (productRule h) (n-1) x i).2 is

private theorem productTrace_grid {m k h : ℕ} (hh : 0 < h) (d : Fin k → ℚ)
    {D : Fin k → ℕ} (hD : ∀ i, 0 < D i) (n : ℕ) (x : State m k (Fin k → ℚ))
    (hx : GridHistory h D (productStateData x)) (ts : List (Fin k)) :
    GridHistory h D (productStateData (productTrace h d n x ts)) := by
  induction ts generalizing n x with
  | nil => exact hx
  | cons t ts ih => exact ih _ _ (product_advance_grid hh d hD _ _ hx t)

/-- The one-width implementation's state after the given type prefix. -/
def oneWidthState {m k : ℕ} (v : Fin k → Fin m → ℚ) (n : ℕ) (ts : List (Fin k)) :
    State m k (Fin k → ℚ) :=
  let h := FixedWidth.productParameterQ k
  let d := RationalAlgorithm1.materialize (fun t => rationalTPS (v t) n)
  productTrace h d n (initialWithTPS v d (fun _ => 1)) ts

/-- Read a policy tree at the next arrival after an observed prefix. -/
def bundleAfter {m k : ℕ} : {n : ℕ} → Policy m k n → List (Fin k) → Fin k → Option (Finset (Fin m))
  | 0, .done, _, _ => none
  | _+1, .step b _, [], t => some (b t)
  | _+1, .step _ q, a::as, t => bundleAfter (q a) as t

private theorem productTrace_response {m k : ℕ} (h : ℕ) (d : Fin k → ℚ)
    (n : ℕ) (x : State m k (Fin k → ℚ)) (ts : List (Fin k)) (i : Fin k) (ht : ts.length < n) :
    bundleAfter (policyFrom h (1/(6*(h:ℚ))) d (productRule h) n x) ts i =
      some (advance h (1/(6*(h:ℚ))) d (productRule h) (n-ts.length-1) (productTrace h d n x ts) i).1 := by
  induction ts generalizing n x with
  | nil => cases n with
    | zero => simp at ht
    | succ n => rfl
  | cons a as ih => cases n with
    | zero => simp at ht
    | succ n =>
      simpa only [policyFrom,bundleAfter,productTrace,List.length_cons,Nat.succ_sub_succ_eq_sub,
        Nat.add_sub_cancel] using ih n (advance h (1/(6*(h:ℚ))) d (productRule h) n x a).2
          (by simpa using ht)

/-- On every legal prefix, the state audited below gives precisely the
next bundle of the named, supply-checked Appendix C.1 policy. -/
theorem oneWidthState_policy_response {m k n : ℕ} (v : Fin k → Fin m → ℚ)
    (ts : List (Fin k)) (i : Fin k) (ht : ts.length < n) :
    let h := FixedWidth.productParameterQ k
    let d := RationalAlgorithm1.materialize (fun t => rationalTPS (v t) n)
    bundleAfter (supplyCheckedPolicy (n := n) v) ts i =
      some (advance h (1/(6*(h:ℚ))) d (productRule h) (n-ts.length-1) (oneWidthState v n ts) i).1 := by
  rw [supplyCheckedPolicy,withSupplyCheck_eq]
  exact productTrace_response _ _ _ _ _ _ ht

private theorem oneWidth_grid {m k n : ℕ} (hn : 0 < n)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    ∃ D : Fin k → ℕ, (∀ t, 0 < D t ∧ (D t).size+1 ≤ 2*inputDigits v + m + 2) ∧
      ∀ ts, GridHistory (FixedWidth.productParameterQ k) D (productStateData (oneWidthState v n ts)) := by
  let h := FixedWidth.productParameterQ k
  obtain ⟨D,hd,hi⟩ := initial_gridHistory (h := h) v hv hn
  have hh : 0 < h := by dsimp [h]; rw [FixedWidth.productParameterQ_eq]; have := (FixedWidth.productMultiplier_bounds k).1; omega
  let d := RationalAlgorithm1.materialize (fun t => rationalTPS (v t) n)
  let x : State m k (Fin k → ℚ) := initialWithTPS v d (fun _ => 1)
  have hi' : GridHistory h D (productStateData x) := hi
  refine ⟨D, fun t => ⟨(hd t).1, ?_⟩, fun ts => productTrace_grid hh d (fun t => (hd t).1) n x hi' ts⟩
  have hrow : valuationInputDigits (v t) ≤ inputDigits v :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (valuationInputDigits (v j))) (Finset.mem_univ t)
  have := (hd t).2
  omega

/-- For every prefix of the Appendix C.1 implementation, all score
comparisons in its next sampling call have polynomial bit length and the
charged bit operations obey the displayed polynomial. -/
theorem oneWidth_sampling_certificate {m k n : ℕ} (hn : 0 < n)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) (ts : List (Fin k)) (r : ℕ) (i : Fin k) :
    let h := FixedWidth.productParameterQ k
    let x := oneWidthState v n ts
    let buckets := rationalBuckets (x.weight i) (h*(r+1+x.samples)) x.remaining
    let d := 2*inputDigits v + m + 2
    let budget := objectiveBits h k m (d+m.size) (productCoefficientBits h m d)
    let run := selectCosted x.weight h 0 1 x.stats [] buckets
    run.1 = (productRule h x i buckets).1 ∧ ScoresBounded x.weight h 0 1 x.stats budget [] buckets ∧
      bitCostEnvelope run.2 budget ≤ 30*(k+1)*(m+1)^3*(budget+1)^3 := by
  dsimp only
  let h := FixedWidth.productParameterQ k
  let x := oneWidthState v n ts
  let H := h*(r+1+x.samples)
  let bs := rationalBuckets (x.weight i) H x.remaining
  let d := 2*inputDigits v + m + 2
  let C := productCoefficientBits h m d
  obtain ⟨D,hd,ht⟩ := oneWidth_grid hn v hv
  have hh : 0 < h := by dsimp [h]; rw [FixedWidth.productParameterQ_eq]; have := (FixedWidth.productMultiplier_bounds k).1; omega
  have hH : 0 < H := Nat.mul_pos hh (by omega)
  have hs := rationalBuckets_spec (x.weight i) hH x.remaining
  have hx := ht ts
  have hne (B : Finset (Fin m)) (hB : B ∈ bs) : B.Nonempty :=
    Finset.card_pos.mp (hs.bucket_size B hB ▸ hH)
  have hc : candidateCount bs ≤ m := candidateCount_le_goods bs hs.pairwise_disjoint
  have hlen : bs.length ≤ m := (length_le_candidateCount hne).trans hc
  have hC : 1 ≤ C := by dsimp [C,productCoefficientBits]; omega
  have hprod (t : Fin k) : Bounded (x.stats t) C := hx.products_bounded hh hd t
  have hw (t : Fin k) (g : Fin m) : Bounded (x.weight t g) (d+m.size) := by
    obtain ⟨hg,h0,h1⟩ := hx.weights t g
    exact (hg.bounded (hd t).1 h0 h1).mono (by have := (hd t).2; dsimp [d]; omega)
  have hmean (B : Finset (Fin m)) (hB : B ∈ bs) (t : Fin k) :
      Bounded (slotMeanQ x.weight B t) (d+m.size) := by
    have hsize := hs.bucket_size B hB
    have hM : H ≤ m := by rw [← hsize]; simpa only [Fintype.card_fin] using Finset.card_le_univ B
    exact (slotMeanQ_bounded (hd t).1 hH x.weight B hsize t
      (fun g => (hx.weights t g).1) (fun g => (hx.weights t g).2)).mono
      (by have := Nat.size_le_size hM; have := (hd t).2; dsimp [d]; omega)
  obtain ⟨_,hscore,hcost⟩ := selectCosted_complete_certificate x.weight h (d+m.size) C 0 1 x.stats hh
    (bounded_zero.mono hC) (bounded_one.mono hC) hprod hw bs [] (by simp) hmean hne (by simpa) hc
  exact ⟨selectCosted_value ..,hscore,hcost⟩

/-- A single polynomial in the bit length of the encoded input. -/
def oneWidthInputBudget (L : ℕ) : ℕ :=
  let p := 4*(L+1)
  let d := 3*L+2
  let b := d+L
  let C := (p+d+3)*L + 3*(p+1)+10
  (((2*b+2)*(L+1)^2 + (p+b+3)*L + 3*C+4)+1)*L+1

theorem oneWidth_budget_le_input {m k n : ℕ} (hm : 0 < m) (hk : 0 < k) (v : Fin k → Fin m → ℚ) :
    let h := FixedWidth.productParameterQ k
    let d := 2*inputDigits v + m + 2
    objectiveBits h k m (d+m.size) (productCoefficientBits h m d) ≤
      oneWidthInputBudget (RationalAlgorithm1.encodingLength n v) := by
  let L := RationalAlgorithm1.encodingLength n v
  have hd : inputDigits v ≤ L := by dsimp [L,RationalAlgorithm1.encodingLength]; omega
  have hcells := (RationalAlgorithm1.table_cells_le_inputDigits v).trans hd
  have hkL : k ≤ L := (Nat.le_mul_of_pos_right k hm).trans hcells
  have hmL : m ≤ L := (Nat.le_mul_of_pos_left m hk).trans hcells
  have hmBits : m.size ≤ L := by dsimp [L,RationalAlgorithm1.encodingLength]; omega
  have hh : FixedWidth.productParameterQ k ≤ 4*(L+1) := by
    rw [FixedWidth.productParameterQ_eq,FixedWidth.productMultiplier]
    apply max_le (by omega)
    apply Nat.ceil_le.mpr
    have hs := Real.sq_sqrt (x := (k:ℝ)) (by positivity)
    have hkl : (k:ℝ) ≤ (L:ℝ) := by exact_mod_cast hkL
    push_cast
    nlinarith [sq_nonneg (Real.sqrt (k:ℝ)-1/2)]
  have hp : (FixedWidth.productParameterQ k).size ≤ 4*(L+1) :=
    (Nat.size_le.mpr (Nat.lt_two_pow_self (n := FixedWidth.productParameterQ k))).trans hh
  change objectiveBits _ _ _ _ _ ≤ oneWidthInputBudget L
  dsimp [objectiveBits,rowBits,productCoefficientBits,oneWidthInputBudget]
  have hd' : 2*inputDigits v + m + 2 ≤ 3*L+2 := by omega
  gcongr

end OnlineMMS.RationalFixedWidth
