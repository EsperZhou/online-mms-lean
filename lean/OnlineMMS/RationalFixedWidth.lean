import OnlineMMS.RationalAlgorithm1
import OnlineMMS.FixedWidthProduct
import OnlineMMS.QuadraticEstimator

namespace OnlineMMS.RationalFixedWidth

open BucketBitComplexity
open RationalAlgorithm1 (materialize materializeTable)
open private FixedWidth.valued from OnlineMMS.FixedWidthKernel
open private FixedWidth.product_deficit_bound FixedWidth.growth from OnlineMMS.FixedWidthProduct
open private FixedWidth.quad_reserve FixedWidth.linearTotal FixedWidth.pairTotal
  from OnlineMMS.QuadraticEstimator

structure State (m k : ℕ) (σ : Type) where
  remaining : Finset (Fin m)
  samples : ℕ
  weight : Fin k → Fin m → ℚ
  stats : σ

def toReal {m k : ℕ} {σ τ : Type} (lift : σ → τ) (x : State m k σ) : FixedWidth.State m k τ :=
  ⟨x.remaining, x.samples, fun t g => x.weight t g, lift x.stats⟩

theorem materialize_eq {a : ℕ} {α : Type} (f : Fin a → α) : materialize f = f :=
  funext (RationalAlgorithm1.materialize_apply f)

@[noinline] def initialWithTPS {m k : ℕ} {σ : Type}
    (v : Fin k → Fin m → ℚ) (d : Fin k → ℚ) (data : σ) : State m k σ :=
  ⟨Finset.univ, 0, materializeTable (fun t g => min (v t g) (d t) / d t), data⟩

def initial {m k : ℕ} {σ : Type} (v : Fin k → Fin m → ℚ) (n : ℕ) (data : σ) : State m k σ :=
  initialWithTPS v (materialize (fun t => rationalTPS (v t) n)) data

theorem initial_cast {m k n : ℕ} {σ τ : Type} (lift : σ → τ)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) (hn : 0 < n) (data : σ) :
    toReal lift (initial v n data) = FixedWidth.init (fun t g => (v t g : ℝ)) n (lift data) := by
  simp only [toReal, initial, initialWithTPS, FixedWidth.init,
    RationalAlgorithm1.materializeTable_apply, RationalAlgorithm1.materialize_apply]
  congr 1
  funext t g
  exact normalizedWeightQ_cast (v t) (hv t) hn g

def small {m k : ℕ} {σ : Type} (r : ℕ) (x : State m k σ) (B : Finset (Fin m)) : State m k σ :=
  ⟨x.remaining \ B, x.samples, materializeTable (fun t =>
    trimWeightsQ (x.remaining \ B) (x.weight t) (r + (x.samples : ℚ))), x.stats⟩

theorem small_cast {m k : ℕ} {σ τ : Type} (lift : σ → τ) (r : ℕ)
    (x : State m k σ) (B : Finset (Fin m)) :
    toReal lift (small r x B) = FixedWidth.afterSmall r (toReal lift x) B := by
  simp only [toReal, small, FixedWidth.afterSmall, RationalAlgorithm1.materializeTable_apply]
  congr 1
  funext t g
  rw [trimWeightsQ_cast]
  push_cast
  rfl

def sample {m k : ℕ} {σ : Type} (x : State m k σ) (gs : List (Fin m)) (data : σ) : State m k σ :=
  ⟨x.remaining \ gs.toFinset, x.samples + 1, x.weight, data⟩

theorem sample_cast {m k : ℕ} {σ τ : Type} (lift : σ → τ)
    (x : State m k σ) (gs : List (Fin m)) (data : σ) :
    toReal lift (sample x gs data) = FixedWidth.afterSample (toReal lift x) gs (lift data) := rfl

abbrev SampleRule (m k : ℕ) (σ : Type) :=
  State m k σ → Fin k → List (Finset (Fin m)) → List (Fin m) × σ

def advance {m k : ℕ} {σ : Type} (h : ℕ) (β : ℚ) (d : Fin k → ℚ)
    (choose : SampleRule m k σ) (r : ℕ) (x : State m k σ) (t : Fin k) :
    Finset (Fin m) × State m k σ :=
  if r = 0 then (x.remaining, {x with remaining := ∅})
  else if 0 < d t then
    let eligible := x.remaining.filter (fun g => β ≤ x.weight t g)
    if he : eligible.Nonempty then
      let B := {eligible.min' he}
      (B, small r x B)
    else
      let bs := RationalAlgorithm1.rationalBuckets (x.weight t) (h * (r + 1 + x.samples)) x.remaining
      let out := choose x t bs
      (out.1.toFinset, sample x out.1 out.2)
  else (∅, small r x ∅)

def policyFrom {m k : ℕ} {σ : Type} (h : ℕ) (β : ℚ) (d : Fin k → ℚ)
    (choose : SampleRule m k σ) : (r : ℕ) → State m k σ → Policy m k r
  | 0, _ => .done
  | r + 1, x =>
      .step (fun t => (advance h β d choose r x t).1)
        (fun t => policyFrom h β d choose r (advance h β d choose r x t).2)

/-- The generic executable fixed-width loop. All sample obligations concern
the callback actually called by the program, rather than an existential
choice of another sample. -/
theorem policyFrom_guarantees {m k : ℕ} {σ τ : Type}
    (lift : σ → τ) (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g)
    (d : Fin k → ℚ) (hd : ∀ t, 0 ≤ d t) (h : ℕ) (hh : 0 < h)
    (β : ℚ) (hβ : 0 ≤ β) (choose : SampleRule m k σ)
    (inv : ℕ → FixedWidth.State m k τ → Prop)
    (htrim : ∀ r x, FixedWidth.Valid v (fun t => (d t : ℝ)) (r + 1) x → inv (r + 1) x →
      ∀ B ⊆ x.remaining, (∀ t, bundleValue (x.weight t) B ≤ 1) →
        inv r (FixedWidth.afterSmall r x B))
    (hchoose : ∀ r x, FixedWidth.Valid v (fun t => (d t : ℝ)) (r + 1) (toReal lift x) →
      inv (r + 1) (toReal lift x) → ∀ t bs,
      SortedBuckets ((toReal lift x).weight t) (h * (r + 1 + x.samples)) x.remaining bs →
      List.Forall₂ (fun B g => g ∈ B) bs (choose x t bs).1 ∧
        inv r (FixedWidth.afterSample (toReal lift x) (choose x t bs).1 (lift (choose x t bs).2)))
    (hnonfinal : ∀ r x, r ≠ 0 → FixedWidth.Valid v (fun t => (d t : ℝ)) (r + 1) x →
      inv (r + 1) x → ∀ t, 0 < (d t : ℝ) →
      2 * (β : ℝ) * ((h * (r + 1 + x.samples) : ℕ) : ℝ) ≤ FixedWidth.total x t)
    (hfinal : ∀ x, FixedWidth.Valid v (fun t => (d t : ℝ)) 1 x → inv 1 x →
      ∀ t, 0 < (d t : ℝ) → (β : ℝ) ≤ FixedWidth.total x t)
    (r : ℕ) (x : State m k σ)
    (hx : FixedWidth.Valid v (fun t => (d t : ℝ)) r (toReal lift x))
    (hi : inv r (toReal lift x)) :
    (policyFrom h β d choose r x).Guarantees v (fun t => (d t : ℝ) * β) x.remaining := by
  have hdR (t : Fin k) : (0 : ℝ) ≤ d t := by exact_mod_cast hd t
  have hβR : (0 : ℝ) ≤ β := by exact_mod_cast hβ
  induction r generalizing x with
  | zero => trivial
  | succ r ih =>
    change ∀ t, (advance h β d choose r x t).1 ⊆ x.remaining ∧ _
    intro t
    have hsmall (B : Finset (Fin m)) (hsub : B ⊆ x.remaining)
        (hB : ∀ i, bundleValue ((toReal lift x).weight i) B ≤ 1)
        (hpay : (d t : ℝ) * β ≤ bundleValue (v t) B) :
        B ⊆ x.remaining ∧ (d t : ℝ) * β ≤ bundleValue (v t) B ∧
        (policyFrom h β d choose r (small r x B)).Guarantees v
          (fun i => (d i : ℝ) * β) (x.remaining \ B) := by
      have hvalid := (FixedWidth.small_valid hx hdR hsub hB).1
      have hinv := htrim r (toReal lift x) hx hi B hsub hB
      rw [← small_cast lift] at hvalid hinv
      exact ⟨hsub, hpay, ih _ hvalid hinv⟩
    by_cases hr : r = 0
    · subst r
      simp only [advance, if_pos rfl, policyFrom, Policy.Guarantees, and_true]
      refine ⟨Finset.Subset.rfl, ?_⟩
      by_cases ht : 0 < d t
      · exact FixedWidth.valued (v := v) (d := fun i => (d i : ℝ)) (x := toReal lift x)
          (t := t) (β := (β : ℝ)) (hdR t) (hx.value t) (hfinal _ hx hi t (by exact_mod_cast ht))
      · have hz : d t = 0 := le_antisymm (le_of_not_gt ht) (hd t)
        simp only [hz, Rat.cast_zero, zero_mul]
        exact Finset.sum_nonneg fun g _ => hv t g
    by_cases ht : 0 < d t
    · let eligible := x.remaining.filter (fun g => β ≤ x.weight t g)
      by_cases he : eligible.Nonempty
      · let g := eligible.min' he
        obtain ⟨hg, hpay⟩ := Finset.mem_filter.mp (eligible.min'_mem he)
        have hpayR : (β : ℝ) ≤ (x.weight t g : ℝ) := by exact_mod_cast hpay
        have hs := hsmall {g} (Finset.singleton_subset_iff.mpr hg)
          (fun i => by simpa [bundleValue] using (hx.weights i g).2)
          (FixedWidth.valued (v := v) (d := fun i => (d i : ℝ)) (x := toReal lift x)
            (t := t) (B := {g}) (β := (β : ℝ)) (hdR t) (hx.value t)
            (by simpa [bundleValue, toReal] using hpayR))
        simpa only [advance, if_neg hr, if_pos ht,
          dif_pos (show (x.remaining.filter (fun g => β ≤ x.weight t g)).Nonempty from he)] using hs
      · let H := h * (r + 1 + x.samples)
        let bs := RationalAlgorithm1.rationalBuckets (x.weight t) H x.remaining
        let out := choose x t bs
        have hH : 0 < H := Nat.mul_pos hh (by omega)
        have hb := RationalAlgorithm1.rationalBuckets_spec (x.weight t) hH x.remaining
        obtain ⟨hg, hinv⟩ := hchoose r x hx hi t bs hb
        obtain ⟨hsub, hnd⟩ := hb.selected_valid hg
        have hpre := hnonfinal r (toReal lift x) hr hx hi t (by exact_mod_cast ht)
        have hsorted := hb.payment hg (fun g => (hx.weights t g).1) hβR (by
          intro g hg
          have hlt : x.weight t g < β := lt_of_not_ge
            (fun hp => he ⟨g, Finset.mem_filter.mpr ⟨hg, hp⟩⟩)
          exact_mod_cast hlt.le)
        have hpay : (β : ℝ) ≤ (out.1.map (fun g => (x.weight t g : ℝ))).sum := by
          have hhR : (0 : ℝ) < H := by exact_mod_cast hH
          have hcombined := hpre.trans hsorted
          change (2 * (β : ℝ)) * H ≤ (H : ℝ) * (β + _) at hcombined
          rw [mul_comm (2 * (β : ℝ))] at hcombined
          have hz := (mul_le_mul_left hhR).mp hcombined
          linarith
        have hvalid := (FixedWidth.sample_valid hx hsub hnd (lift out.2)).1
        have hnext := ih (sample x out.1 out.2) hvalid hinv
        have hvalue : (d t : ℝ) * β ≤ bundleValue (v t) out.1.toFinset := by
          apply FixedWidth.valued (v := v) (d := fun i => (d i : ℝ)) (x := toReal lift x)
            (t := t) (β := (β : ℝ)) (hdR t) (hx.value t)
          exact (FixedWidth.weight_list_sum _ _ hnd) ▸ hpay
        simpa only [advance, if_neg hr, if_pos ht,
          dif_neg (show ¬(x.remaining.filter (fun g => β ≤ x.weight t g)).Nonempty from he)] using
          (show out.1.toFinset ⊆ x.remaining ∧ (d t : ℝ) * β ≤ bundleValue (v t) out.1.toFinset ∧
            (policyFrom h β d choose r (sample x out.1 out.2)).Guarantees v
              (fun i => (d i : ℝ) * β) (x.remaining \ out.1.toFinset) from ⟨hsub, hvalue, hnext⟩)
    · have hz : d t = 0 := le_antisymm (le_of_not_gt ht) (hd t)
      have hs := hsmall ∅ (Finset.empty_subset _) (fun _ => by simp [bundleValue])
        (by simp [hz, bundleValue])
      simpa only [advance, if_neg hr, if_neg ht] using hs

noncomputable def productLift {k : ℕ} (P : Fin k → ℚ) : Fin k → ℝ := fun t => (P t : ℝ)

def productRule {m k : ℕ} (h : ℕ) : SampleRule m k (Fin k → ℚ) := fun x _ bs =>
  let gs := selectQ x.weight (h : ℚ) 0 1 x.stats [] bs
  (gs, materialize (FixedWidth.productUpdateQ h x.stats x.weight gs))

/-- Executable fixed-width product policy, with its integer width parameter
supplied explicitly. The theorem below permits the paper's least width. -/
def productPolicy {m k n : ℕ} (h : ℕ) (v : Fin k → Fin m → ℚ) : Policy m k n :=
  let d := materialize (fun t => rationalTPS (v t) n)
  policyFrom h (1 / (6 * (h : ℚ))) d (productRule h)
    n (initialWithTPS v d (fun _ : Fin k => (1 : ℚ)))

theorem productPolicy_guarantees {m k n h : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hh : 4 ≤ h) (hcap : (k : ℝ) ≤ (h : ℝ)^2 / 4)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (productPolicy (n := n) h v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => truncatedShare (fun g => (v t g : ℝ)) n / (6 * (h : ℝ))) Finset.univ := by
  let vR : Fin k → Fin m → ℝ := fun t g => (v t g : ℝ)
  let d : Fin k → ℚ := fun t => rationalTPS (v t) n
  let dR : Fin k → ℝ := fun t => truncatedShare (vR t) n
  let β : ℚ := 1 / (6 * (h : ℚ))
  have hvR (t : Fin k) (g : Fin m) : 0 ≤ vR t g := by dsimp [vR]; exact_mod_cast hv t g
  have hTPS (t : Fin k) : (d t : ℝ) = dR t := rationalTPS_correct hn (v t) (hv t)
  have hdR (t : Fin k) : 0 ≤ dR t := (truncatedShare_spec (vR t) (hvR t) hn).1.1
  have hd (t : Fin k) : 0 ≤ d t := by have hz := hdR t; rw [← hTPS t] at hz; exact_mod_cast hz
  have hdf : (fun t => (d t : ℝ)) = dR := funext hTPS
  have hhR : (4 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hβcast : (β : ℝ) = 1 / (6 * (h : ℝ)) := by simp [β]
  have hβle : (β : ℝ) ≤ 1 := by
    rw [hβcast]
    apply (div_le_one₀ (show (0 : ℝ) < 6 * h by positivity)).mpr
    linarith
  have hreserve : ∀ r (x : FixedWidth.State m k (Fin k → ℝ)),
      FixedWidth.Valid vR dR r x → FixedWidth.ProductInv (h : ℝ) dR r x →
      ∀ t, 0 < dR t → 0 < x.samples →
      FixedWidth.deficit x r t ≤ 2 - (β : ℝ) + (2 / 3 : ℝ) * ((x.samples : ℝ) - 1) := by
    intro r x hx hi t ht hs
    have hp := (hi.2.1 t ht).trans <| (Finset.single_le_sum
      (fun i _ => hi.1 i) (Finset.mem_univ t)).trans hi.2.2
    rw [hβcast]
    exact FixedWidth.product_deficit_bound hh hk hcap hs _ hp
  have hcast := initial_cast productLift v hv hn (fun _ : Fin k => (1 : ℚ))
  have hp : (policyFrom h β d (productRule h) n (initial v n (fun _ : Fin k => (1 : ℚ)))).Guarantees
      vR (fun t => (d t : ℝ) * β) Finset.univ := by
    refine policyFrom_guarantees productLift vR hvR d hd h (by omega) β (by dsimp [β]; positivity)
      (productRule h) (FixedWidth.ProductInv (h : ℝ) dR) ?_ ?_ ?_ ?_ n _ ?_ ?_
    · intro r x hx hi B hsub hB
      rw [hdf] at hx
      have hnew := (FixedWidth.small_valid hx hdR hsub hB).2
      exact ⟨hi.1, fun t ht =>
        (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ h) (hnew t)).trans
          (hi.2.1 t ht), hi.2.2⟩
    · intro r x hx hi t bs hb
      rw [hdf] at hx
      have hc := FixedWidth.product_rational_sample_preserves hh hx hi x.weight x.stats
        (fun _ _ => rfl) (fun _ => rfl) t bs hb
      have hdata : productLift (materialize (FixedWidth.productUpdateQ h x.stats x.weight
          (selectQ x.weight (h : ℚ) 0 1 x.stats [] bs))) =
          fun i => (x.stats i : ℝ) * sampleProduct (h : ℝ)
            ((selectQ x.weight (h : ℚ) 0 1 x.stats [] bs).map (fun g => (x.weight i g : ℝ))) := by
        funext i
        simp [productLift, FixedWidth.productUpdateQ, sampleProductQ_cast,
          List.map_map, Function.comp_def]
      simpa only [productRule, hdata] using hc
    · intro r x hr hx hi t ht
      rw [hdf] at hx
      rw [hTPS] at ht
      let N : ℝ := ((r + 1 : ℕ) : ℝ) + x.samples
      have hpaid : N / 3 ≤ FixedWidth.total x t := by
        by_cases hz : x.samples = 0
        · rw [hx.exactBefore hz t ht]
          simp only [N, hz, Nat.cast_zero, add_zero, Nat.cast_succ]
          linarith [Nat.cast_nonneg (α := ℝ) r]
        · have hs := hreserve (r + 1) x hx hi t ht (by omega)
          have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
          unfold FixedWidth.deficit at hs
          dsimp [N]
          push_cast at hs ⊢
          linarith [show (0 : ℝ) ≤ β by exact_mod_cast (show (0 : ℚ) ≤ β by dsimp [β]; positivity)]
      have he : 2 * (β : ℝ) * ((h * (r + 1 + x.samples) : ℕ) : ℝ) = N / 3 := by
        rw [hβcast]
        dsimp [N]
        push_cast
        field_simp [hh0.ne']
        ring
      exact he ▸ hpaid
    · intro x hx hi t ht
      rw [hdf] at hx
      rw [hTPS] at ht
      by_cases hz : x.samples = 0
      · simpa [hx.exactBefore hz t ht] using hβle
      · have hs := hreserve 1 x hx hi t ht (by omega)
        have hsR : (1 : ℝ) ≤ x.samples := by exact_mod_cast (show 1 ≤ x.samples by omega)
        unfold FixedWidth.deficit at hs
        norm_num at hs
        linarith
    · rw [hcast, hdf]
      exact FixedWidth.valid_init hn vR hvR _
    · rw [hcast]
      refine ⟨?_, ?_, ?_⟩
      · intro t; norm_num [FixedWidth.init, productLift]
      · intro t ht
        have he : FixedWidth.total (FixedWidth.init vR n (productLift (fun _ : Fin k => (1 : ℚ)))) t = n :=
          sum_normalizedWeight (vR t) (hvR t) hn ht
        have hz : FixedWidth.deficit (FixedWidth.init vR n (productLift (fun _ : Fin k => (1 : ℚ)))) n t = 0 := by
          unfold FixedWidth.deficit
          rw [he]
          simp [FixedWidth.init]
        rw [hz, Real.rpow_zero]
        norm_num [FixedWidth.init, productLift]
      · simp [FixedWidth.init, productLift, nsmul_eq_mul]
  simpa [productPolicy, initial, β, vR, hTPS, div_eq_mul_inv, materialize_eq] using hp

end OnlineMMS.RationalFixedWidth
