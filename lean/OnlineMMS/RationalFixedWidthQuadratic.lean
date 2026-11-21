import OnlineMMS.RationalFixedWidth
import OnlineMMS.FixedWidthParameters

namespace OnlineMMS.RationalFixedWidth

open BucketBitComplexity
open RationalAlgorithm1 (materialize)
open private FixedWidth.quad_reserve FixedWidth.linearTotal FixedWidth.pairTotal
  FixedWidth.quadraticMultiplier_bounds from OnlineMMS.QuadraticEstimator

noncomputable def historyLift {k : ℕ} (record : Fin k → List ℚ) : FixedWidth.History k :=
  fun i => (record i).map (fun z : ℚ => (z : ℝ))

/-- The quadratic estimator records exact rational weights. Its decisions use
their per-type sums, and the full history certifies the invariant. -/
def quadraticRule {m k : ℕ} (h : ℕ) : SampleRule m k (Fin k → List ℚ) := fun x _ bs =>
  let L := materialize (fun i => (x.stats i).sum)
  let pre := materialize (quadraticPrefixQ h L)
  let gs := selectQ x.weight 1 1 0 (fun _ => 0) [pre] bs
  (gs, materialize (fun i => x.stats i ++ gs.map (x.weight i)))

def quadraticPolicy {m k n : ℕ} (h : ℕ) (v : Fin k → Fin m → ℚ) : Policy m k n :=
  let d := materialize (fun t => rationalTPS (v t) n)
  policyFrom h (1 / (8 * (h : ℚ))) d (quadraticRule h)
    n (initialWithTPS v d (fun _ : Fin k => ([] : List ℚ)))

theorem quadraticPolicy_guarantees {m k n h : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hh : 0 < h) (hcap : (k : ℝ) ≤ (h : ℝ)^2 / 16)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (quadraticPolicy (n := n) h v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => truncatedShare (fun g => (v t g : ℝ)) n / (8 * (h : ℝ))) Finset.univ := by
  let vR : Fin k → Fin m → ℝ := fun t g => (v t g : ℝ)
  let d : Fin k → ℚ := fun t => rationalTPS (v t) n
  let dR : Fin k → ℝ := fun t => truncatedShare (vR t) n
  let β : ℚ := 1 / (8 * (h : ℚ))
  have hvR (t : Fin k) (g : Fin m) : 0 ≤ vR t g := by dsimp [vR]; exact_mod_cast hv t g
  have hTPS (t : Fin k) : (d t : ℝ) = dR t := rationalTPS_correct hn (v t) (hv t)
  have hdR (t : Fin k) : 0 ≤ dR t := (truncatedShare_spec (vR t) (hvR t) hn).1.1
  have hd (t : Fin k) : 0 ≤ d t := by have hz := hdR t; rw [← hTPS t] at hz; exact_mod_cast hz
  have hdf : (fun t => (d t : ℝ)) = dR := funext hTPS
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by positivity
  have hβcast : (β : ℝ) = 1 / (8 * (h : ℝ)) := by simp [β]
  have hβle : (β : ℝ) ≤ 1 / 4 := by
    rw [hβcast]
    apply (div_le_iff₀ (show (0 : ℝ) < 8 * h by positivity)).mpr
    linarith
  have hcast := initial_cast historyLift v hv hn (fun _ : Fin k => ([] : List ℚ))
  have hp : (policyFrom h β d (quadraticRule h) n (initial v n (fun _ : Fin k => ([] : List ℚ)))).Guarantees
      vR (fun t => (d t : ℝ) * β) Finset.univ := by
    refine policyFrom_guarantees historyLift vR hvR d hd h hh β (by dsimp [β]; positivity)
      (quadraticRule h) (FixedWidth.QuadInv (h : ℝ) dR) ?_ ?_ ?_ ?_ n _ ?_ ?_
    · intro r x hx hi B hsub hB
      rw [hdf] at hx
      have hnew := (FixedWidth.small_valid hx hdR hsub hB).2
      exact ⟨hi.1, fun t ht => (hnew t).trans (hi.2.1 t ht), hi.2.2⟩
    · intro r x hx hi t bs hb
      rw [hdf] at hx
      have hc := FixedWidth.quadratic_rational_sample_preserves hk hh hx hi x.weight
        (fun i => (x.stats i).sum) (fun _ _ => rfl)
        (fun i => by simp [toReal, historyLift]) t bs hb
      have hm (f : Fin k → ℚ) : materialize f = f := funext (RationalAlgorithm1.materialize_apply f)
      have hdata (gs : List (Fin m)) :
          historyLift (materialize (fun i => x.stats i ++ gs.map (x.weight i))) =
          fun i => historyLift x.stats i ++ gs.map (fun g => (x.weight i g : ℝ)) := by
        funext i
        simp [historyLift, List.map_append, List.map_map, Function.comp_def]
      simpa only [quadraticRule, hm, hdata] using hc
    · intro r x hr hx hi t ht
      rw [hdf] at hx
      rw [hTPS] at ht
      have hW := FixedWidth.quad_reserve hh0 hcap (by omega : 0 < r + 1) hx hi t ht
      have he : 2 * (β : ℝ) * ((h * (r + 1 + x.samples) : ℕ) : ℝ) =
          (((r + 1 : ℕ) : ℝ) + x.samples) / 4 := by
        rw [hβcast]; push_cast; field_simp [hh0.ne']; ring
      exact he ▸ hW
    · intro x hx hi t ht
      rw [hdf] at hx
      rw [hTPS] at ht
      have hW := FixedWidth.quad_reserve hh0 hcap (by decide : 0 < 1) hx hi t ht
      norm_num at hW
      linarith [Nat.cast_nonneg (α := ℝ) x.samples]
    · rw [hcast, hdf]
      exact FixedWidth.valid_init hn vR hvR _
    · rw [hcast]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [FixedWidth.init, historyLift]
      · intro t ht
        have he : FixedWidth.total
            (FixedWidth.init vR n (historyLift (fun _ : Fin k => ([] : List ℚ)))) t = n :=
          sum_normalizedWeight (vR t) (hvR t) hn ht
        unfold FixedWidth.deficit
        rw [he]
        simp [FixedWidth.init, historyLift]
      · simp [FixedWidth.init, historyLift, FixedWidth.linearTotal]
      · simp [FixedWidth.init, historyLift, FixedWidth.pairTotal, pairSum]
  simpa [quadraticPolicy, initial, β, vR, hTPS, div_eq_mul_inv, materialize_eq] using hp

/-- The one-width product policy of Proposition C.1, with its integer multiplier. -/
def oneWidthPolicy {m k n : ℕ} (v : Fin k → Fin m → ℚ) : Policy m k n :=
  productPolicy (FixedWidth.productParameterQ k) v

/-- Supplementary quadratic-estimator policy with its integer multiplier. -/
def quadraticEstimatorPolicy {m k n : ℕ} (v : Fin k → Fin m → ℚ) : Policy m k n :=
  quadraticPolicy (FixedWidth.quadraticParameterQ k) v

theorem oneWidthPolicy_guarantees {m k n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (oneWidthPolicy (n := n) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => truncatedShare (fun g => (v t g : ℝ)) n /
        (6 * (FixedWidth.productMultiplier k : ℝ))) Finset.univ := by
  obtain ⟨hh, hcap⟩ := FixedWidth.productMultiplier_bounds k
  simpa only [oneWidthPolicy, FixedWidth.productParameterQ_eq] using
    productPolicy_guarantees hn hk hh hcap v hv

theorem quadraticEstimatorPolicy_guarantees {m k n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (quadraticEstimatorPolicy (n := n) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => truncatedShare (fun g => (v t g : ℝ)) n /
        (8 * (FixedWidth.quadraticMultiplier k : ℝ))) Finset.univ := by
  obtain ⟨hh, hcap⟩ := FixedWidth.quadraticMultiplier_bounds hk
  simpa only [quadraticEstimatorPolicy, FixedWidth.quadraticParameterQ_eq] using
    quadraticPolicy_guarantees hn hk (by omega) hcap v hv

theorem oneWidthPolicy_guarantees_mms {m k n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (oneWidthPolicy (n := n) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => maximinShare (fun g => (v t g : ℝ)) n hn /
        (6 * (FixedWidth.productMultiplier k : ℝ))) Finset.univ := by
  apply (oneWidthPolicy_guarantees hn hk v hv).mono
  intro t
  apply div_le_div_of_nonneg_right
  · exact maximinShare_le_truncatedShare _ (fun g => by exact_mod_cast hv t g) hn
  · positivity

theorem quadraticEstimatorPolicy_guarantees_mms {m k n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (quadraticEstimatorPolicy (n := n) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => maximinShare (fun g => (v t g : ℝ)) n hn /
        (8 * (FixedWidth.quadraticMultiplier k : ℝ))) Finset.univ := by
  apply (quadraticEstimatorPolicy_guarantees hn hk v hv).mono
  intro t
  apply div_le_div_of_nonneg_right
  · exact maximinShare_le_truncatedShare _ (fun g => by exact_mod_cast hv t g) hn
  · positivity

end OnlineMMS.RationalFixedWidth
