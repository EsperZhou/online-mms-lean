import OnlineMMS.General
import OnlineMMS.BucketBitComplexity
import OnlineMMS.RationalTPSInitialization

namespace OnlineMMS.RationalAlgorithm1

open BucketBitComplexity
open private AlgorithmState.sampleWidth AlgorithmState.finalNext AlgorithmState.smallNext
  AlgorithmState.sampleNext AlgorithmState.sampleProducts AlgorithmState.protectedTypes
  algorithmInitial from OnlineMMS.General

/-- Integer parameter from a bounded search for the last infeasible bucket index. -/
def parameterQ (k : ℕ) : ℕ :=
  if k = 0 then 212 else 212 + 4 * (Nat.findGreatest (fun j => 32 * j^2 < k) k + 1)

theorem parameterQ_eq (k : ℕ) : parameterQ k = bucketMultiplier k := by
  obtain ⟨j, hj, hfit, hmin⟩ := bucketMultiplier_spec k
  by_cases hk : k = 0
  · have hj0 : j = 0 := by by_contra h; have := hmin 0 (by omega); omega
    rw [parameterQ, if_pos hk, hj, hj0]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero (fun hz => hk (by simpa [hz] using hfit))
    have hjbound : j ≤ k + 1 := by
      apply le_of_not_gt
      intro h
      have hbad := hmin k (by omega)
      have hkSq : k ≤ k^2 := by
        simpa [pow_two] using Nat.mul_le_mul_left k (show 1 ≤ k by omega)
      omega
    have hl : 32 * (j - 1)^2 < k := hmin _ (by omega)
    have hle : j - 1 ≤ Nat.findGreatest (fun j => 32 * j^2 < k) k :=
      Nat.le_findGreatest (by omega) hl
    have hg : 32 * (Nat.findGreatest (fun j => 32 * j^2 < k) k)^2 < k :=
      Nat.findGreatest_spec (P := fun i => 32 * i^2 < k) (show j - 1 ≤ k by omega) hl
    have hupper : Nat.findGreatest (fun j => 32 * j^2 < k) k < j := by
      apply lt_of_not_ge
      intro h
      have hsq := Nat.pow_le_pow_left h 2
      omega
    simp only [parameterQ, if_neg hk, hj]
    omega

private def fullBlocks {m : ℕ} (width : ℕ) : ℕ → List (Fin m) → List (Finset (Fin m))
  | 0, _ => []
  | fuel + 1, goods =>
    if goods.length < width then []
    else (goods.take width).toFinset :: fullBlocks width fuel (goods.drop width)

private theorem fullBlocks_spec {m width fuel : ℕ} {w : Fin m → ℚ}
    (hwidth : 0 < width) (goods : List (Fin m)) (hfuel : goods.length ≤ fuel)
    (hnd : goods.Nodup) (hsort : goods.Pairwise (fun g x => w x ≤ w g)) :
    SortedBuckets (fun g => (w g : ℝ)) width goods.toFinset (fullBlocks width fuel goods) := by
  induction fuel generalizing goods with
  | zero =>
    have hg : goods = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hfuel)
    subst goods
    exact .tail (by simpa using hwidth)
  | succ fuel ih =>
    by_cases hshort : goods.length < width
    · simpa only [fullBlocks, if_pos hshort] using
        (SortedBuckets.tail (w := fun g => (w g : ℝ))
          (show goods.toFinset.card < width by rwa [List.toFinset_card_of_nodup hnd]))
    · let head := goods.take width
      let tail := goods.drop width
      have happ : head ++ tail = goods := List.take_append_drop _ _
      have hnd' : (head ++ tail).Nodup := happ ▸ hnd
      have hs' : (head ++ tail).Pairwise (fun g x => w x ≤ w g) := happ ▸ hsort
      have hsplit := List.pairwise_append.mp hs'
      have hdisj : Disjoint head.toFinset tail.toFinset := by
        refine Finset.disjoint_left.mpr (fun x hx hy => ?_)
        exact List.disjoint_left.mp (List.nodup_append.mp hnd').2.2
          (by simpa using hx) (by simpa using hy)
      have htlen : tail.length ≤ fuel := by
        simp only [tail, List.length_drop]
        omega
      have hrest := ih tail htlen (List.nodup_append.mp hnd').2.1 hsplit.2.1
      have hunion : head.toFinset ∪ tail.toFinset = goods.toFinset := by
        rw [← List.toFinset_append, happ]
      simp only [fullBlocks, if_neg hshort]
      exact hunion ▸ SortedBuckets.full
        (by
          rw [List.toFinset_card_of_nodup (List.nodup_append.mp hnd').1]
          exact List.length_take_of_le (Nat.le_of_not_gt hshort))
        hdisj (fun g hg x hx => by
          exact_mod_cast hsplit.2.2 g (by simpa using hg) x (by simpa using hx)) hrest

/-- Sort in descending rational weight order, breaking ties by the incoming
index order, then discard the short last block. -/
def rationalBuckets {m : ℕ} (w : Fin m → ℚ) (width : ℕ) (remaining : Finset (Fin m)) :
    List (Finset (Fin m)) :=
  let goods := (remaining.sort (· ≤ ·)).mergeSort (fun g x => decide (w x ≤ w g))
  fullBlocks width goods.length goods

theorem rationalBuckets_spec {m width : ℕ} (w : Fin m → ℚ) (hwidth : 0 < width)
    (remaining : Finset (Fin m)) :
    SortedBuckets (fun g => (w g : ℝ)) width remaining (rationalBuckets w width remaining) := by
  let rel : Fin m → Fin m → Prop := fun g x => w x ≤ w g
  letI : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))
  letI : IsTotal (Fin m) rel := ⟨fun g x => le_total (w x) (w g)⟩
  letI : IsTrans (Fin m) rel := ⟨fun _ _ _ h h' => le_trans h' h⟩
  let goods := (remaining.sort (· ≤ ·)).mergeSort (fun g x => decide (rel g x))
  have hperm : goods.Perm (remaining.sort (· ≤ ·)) := List.mergeSort_perm _ _
  have hnd : goods.Nodup := hperm.nodup_iff.mpr (remaining.sort_nodup _)
  have hs : goods.Pairwise rel := List.sorted_mergeSort' rel _
  have heq : goods.toFinset = remaining := by
    ext g
    simpa using hperm.mem_iff (a := g)
  have hb := fullBlocks_spec hwidth goods le_rfl hnd hs
  rw [heq] at hb
  exact hb

structure State (m k : ℕ) where
  remaining : Finset (Fin m)
  sampleCount : ℕ
  weight : Fin k → Fin m → ℚ
  products : Fin k → ℚ

def State.toReal {m k : ℕ} (x : State m k) : AlgorithmState m k :=
  ⟨x.remaining, x.sampleCount, fun t g => x.weight t g, fun t => x.products t⟩

-- Returning the accessor in a structure keeps Lean's compiler from moving
-- the array construction into the accessor body.
private structure Cached (α : Type*) where
  read : α

@[noinline] private def buildColumn {n : ℕ} {α : Type*} (f : Fin n → α) :
    Cached (Fin n → α) :=
  let column := Vector.ofFn f
  ⟨fun i => column[i.val]⟩

/-- Evaluate a finite column once and use its array entries on subsequent reads. -/
@[macro_inline] def materialize {n : ℕ} {α : Type*} (f : Fin n → α) : Fin n → α :=
  (buildColumn f).read

@[simp] theorem materialize_apply {n : ℕ} {α : Type*} (f : Fin n → α) (i : Fin n) :
    materialize f i = f i := by
  simp [materialize, buildColumn]

private theorem materialize_eq {n : ℕ} {α : Type*} (f : Fin n → α) : materialize f = f :=
  funext (materialize_apply f)

@[noinline] private def buildRows {m k : ℕ} {α : Type*} (f : Fin k → Fin m → α) :
    Cached (Fin k → Fin m → α) :=
  let rows := Vector.ofFn (fun t => Vector.ofFn (f t))
  ⟨fun t g => rows[t.val][g.val]⟩

/-- Evaluate each row and its entries once. -/
@[macro_inline] def materializeTable {m k : ℕ} {α : Type*} (f : Fin k → Fin m → α) :
    Fin k → Fin m → α :=
  (buildRows f).read

@[simp] theorem materializeTable_apply {m k : ℕ} {α : Type*}
    (f : Fin k → Fin m → α) (t : Fin k) (g : Fin m) :
    materializeTable f t g = f t g := by
  simp [materializeTable, buildRows]

@[noinline] private def initialWithTPS {m k : ℕ} (v : Fin k → Fin m → ℚ)
    (d : Fin k → ℚ) : State m k :=
  ⟨Finset.univ, 0, materializeTable (fun t g => min (v t g) (d t) / d t), fun _ => 1⟩

private def initial {m k : ℕ} (v : Fin k → Fin m → ℚ) (n : ℕ) : State m k :=
  initialWithTPS v (materialize (fun t => rationalTPS (v t) n))

@[simp] theorem initial_weight {m k : ℕ} (v : Fin k → Fin m → ℚ) (n : ℕ)
    (t : Fin k) (g : Fin m) : (initial v n).weight t g = normalizedWeightQ (v t) n g := by
  simp [initial, initialWithTPS, normalizedWeightQ]

@[simp] theorem initial_products {m k : ℕ} (v : Fin k → Fin m → ℚ) (n : ℕ)
    (t : Fin k) : (initial v n).products t = 1 := rfl

private def thresholdQ (h : ℕ) : ℚ := 1 / (2 * (h : ℚ))

private theorem thresholdQ_cast (h : ℕ) : (thresholdQ h : ℝ) = threshold h := by
  simp [thresholdQ, threshold]

private def protectedQ {k : ℕ} (d : Fin k → ℚ) : Finset (Fin k) :=
  Finset.univ.filter (fun t => 0 < d t)

private theorem protectedQ_eq {k : ℕ} (d : Fin k → ℚ) :
    protectedQ d = AlgorithmState.protectedTypes (fun t => (d t : ℝ)) := by
  ext t
  simp [protectedQ, AlgorithmState.protectedTypes]

private def smallQ {m k : ℕ} (r : ℕ) (x : State m k) (bundle : Finset (Fin m)) : State m k :=
  let rem := x.remaining \ bundle
  ⟨rem, x.sampleCount,
    materializeTable (fun t => trimWeightsQ rem (x.weight t) (r + (x.sampleCount : ℚ))),
    x.products⟩

@[simp] theorem smallQ_weight {m k : ℕ} (r : ℕ) (x : State m k)
    (bundle : Finset (Fin m)) (t : Fin k) (g : Fin m) :
    (smallQ r x bundle).weight t g =
      trimWeightsQ (x.remaining \ bundle) (x.weight t) (r + (x.sampleCount : ℚ)) g := by
  simp [smallQ]

private theorem smallQ_cast {m k : ℕ} (r : ℕ) (x : State m k) (bundle : Finset (Fin m)) :
    (smallQ r x bundle).toReal = AlgorithmState.smallNext r x.toReal bundle := by
  simp only [State.toReal, smallQ, AlgorithmState.smallNext]
  congr 1
  funext t g
  rw [materializeTable_apply, trimWeightsQ_cast]
  push_cast
  rfl

private def sampleQ {m k : ℕ} (h : ℕ) (x : State m k) (gs : List (Fin m)) : State m k :=
  ⟨x.remaining \ gs.toFinset, x.sampleCount + 1, x.weight,
    materialize (fun t => x.products t * sampleProductQ h (gs.map (x.weight t)))⟩

@[simp] theorem sampleQ_products {m k : ℕ} (h : ℕ) (x : State m k) (gs : List (Fin m))
    (t : Fin k) : (sampleQ h x gs).products t =
      x.products t * sampleProductQ h (gs.map (x.weight t)) := by
  simp [sampleQ]

private theorem sampleQ_cast {m k : ℕ} (h : ℕ) (x : State m k) (gs : List (Fin m)) :
    (sampleQ h x gs).toReal = AlgorithmState.sampleNext h x.toReal gs := by
  simp only [State.toReal, sampleQ, AlgorithmState.sampleNext, AlgorithmState.sampleProducts]
  congr 1
  funext t
  unfold AlgorithmState.sampleProducts
  simp [sampleProductQ_cast, List.map_map, Function.comp_def]

private def widthQ {m k : ℕ} (h b r : ℕ) (x : State m k) : ℕ :=
  (if x.sampleCount = 0 then h else b) * (r + 1 + x.sampleCount)

private def qCoeff {m k : ℕ} (x : State m k) : ℚ :=
  if x.sampleCount = 0 then 1 else 0

private def cCoeff {m k : ℕ} (h : ℕ) (x : State m k) : ℚ :=
  if x.sampleCount = 0 then 128 / (h : ℚ) ^ 3 else 1

private def eligible {m k : ℕ} (h : ℕ) (x : State m k) (t : Fin k) : Finset (Fin m) :=
  x.remaining.filter (fun g => thresholdQ h ≤ x.weight t g)

/-- Deterministic transition on an explicitly represented rational state. -/
def advance {m k : ℕ} (h b : ℕ) (d : Fin k → ℚ) (r : ℕ) (x : State m k) (t : Fin k) :
    Finset (Fin m) × State m k :=
  if r = 0 then (x.remaining, {x with remaining := ∅})
  else if 0 < d t then
    let goods := eligible h x t
    if hn : goods.Nonempty then
      let bundle := {goods.min' hn}
      (bundle, smallQ r x bundle)
    else
      let buckets := rationalBuckets (x.weight t) (widthQ h b r x) x.remaining
      let gs := selectQ x.weight h (qCoeff x) (cCoeff h x) x.products [] buckets
      (gs.toFinset, sampleQ h x gs)
  else (∅, smallQ r x ∅)

private def Masked {m k : ℕ} (d : Fin k → ℚ) (x : State m k) : Prop :=
  ∀ t ∉ protectedQ d, ∀ g, x.weight t g = 0

private theorem trimListQ_zero {m : ℕ} (w : Fin m → ℚ) (hw : ∀ g, w g = 0)
    (l : List (Fin m)) (remove : ℚ) (hr : 0 ≤ remove) (g : Fin m) :
    trimListQ w l remove g = 0 := by
  induction l generalizing remove with
  | nil => rfl
  | cons a l ih =>
    by_cases hg : g = a
    · simp [trimListQ, hg, hw, max_eq_left (show -remove ≤ 0 by linarith)]
    · simp [trimListQ, hg, hw, ih remove hr, max_eq_right hr]

private theorem smallQ_masked {m k : ℕ} (r : ℕ) (d : Fin k → ℚ) (x : State m k)
    (bundle : Finset (Fin m)) (hx : Masked d x) : Masked d (smallQ r x bundle) := by
  intro t ht g
  rw [smallQ_weight]
  exact trimListQ_zero _ (hx t ht) _ _ (le_max_left _ _) _

private theorem advance_spec {m k h b : ℕ} (hh : 0 < h) (hb : 0 < b) (d : Fin k → ℚ)
    (hd : ∀ t, 0 ≤ d t) (r : ℕ) (x : State m k) (hx : Masked d x) (t : Fin k) :
    let out := advance h b d r x t
    AlgorithmState.Step h b (fun i => (d i : ℝ)) r x.toReal t out.1 out.2.toReal ∧
      Masked d out.2 := by
  by_cases hr : r = 0
  · simpa only [advance, if_pos hr] using
      (show AlgorithmState.Step h b (fun i => (d i : ℝ)) r x.toReal t x.remaining
        ({x with remaining := ∅} : State m k).toReal ∧ Masked d x from ⟨.final hr, hx⟩)
  by_cases ht : 0 < d t
  · have htR : 0 < (d t : ℝ) := by exact_mod_cast ht
    let goods := eligible h x t
    by_cases hn : goods.Nonempty
    · let g := goods.min' hn
      obtain ⟨hmem, hpay⟩ := Finset.mem_filter.mp (goods.min'_mem hn)
      have hcast : threshold h ≤ (x.weight t g : ℝ) := by
        rw [← thresholdQ_cast]
        exact_mod_cast hpay
      have hfirst (a : Fin m) (ha : a ∈ x.remaining)
          (hp : threshold h ≤ (x.weight t a : ℝ)) : g ≤ a := by
        apply goods.min'_le
        apply Finset.mem_filter.mpr
        refine ⟨ha, ?_⟩
        rw [← thresholdQ_cast] at hp
        exact_mod_cast hp
      simp only [advance, if_neg hr, if_pos ht, dif_pos (show (eligible h x t).Nonempty from hn)]
      change AlgorithmState.Step h b (fun i => (d i : ℝ)) r x.toReal t
        {g} (smallQ r x {g}).toReal ∧ Masked d (smallQ r x {g})
      rw [smallQ_cast]
      exact ⟨.singleton hr htR hmem hcast hfirst, smallQ_masked r d x {g} hx⟩
    · let width := widthQ h b r x
      let buckets := rationalBuckets (x.weight t) width x.remaining
      let gs := selectQ x.weight h (qCoeff x) (cCoeff h x) x.products [] buckets
      have hwidth : 0 < width := by
        dsimp only [width, widthQ]
        split <;> exact Nat.mul_pos (by assumption) (by omega)
      have hsorted := rationalBuckets_spec (x.weight t) hwidth x.remaining
      have hne (B : Finset (Fin m)) (hB : B ∈ buckets) : B.Nonempty :=
        Finset.card_pos.mp (hsorted.bucket_size B hB ▸ hwidth)
      have hsmall (g : Fin m) (hg : g ∈ x.remaining) : (x.weight t g : ℝ) < threshold h := by
        rw [← thresholdQ_cast]
        exact_mod_cast (show x.weight t g < thresholdQ h from
          lt_of_not_ge (fun hpay => hn ⟨g, Finset.mem_filter.mpr ⟨hg, hpay⟩⟩))
      have hgreedy := selectQ_protected_greedy x.weight h (qCoeff x) (cCoeff h x)
        x.products (protectedQ d) hx buckets hne
      have hgreedy' : IsProtectedGreedySample x.toReal.weight (h : ℝ)
          (if x.sampleCount = 0 then 1 else 0)
          (if x.sampleCount = 0 then 128 / (h : ℝ) ^ 3 else 1)
          x.toReal.products (AlgorithmState.protectedTypes (fun t => (d t : ℝ))) [] buckets gs := by
        by_cases hs : x.sampleCount = 0 <;>
          simpa [State.toReal, qCoeff, cCoeff, hs, protectedQ_eq, gs] using hgreedy
      have hstep : AlgorithmState.Step h b (fun i => (d i : ℝ)) r x.toReal t
          gs.toFinset (AlgorithmState.sampleNext h x.toReal gs) :=
        .sample hr htR hsmall hsorted hgreedy'
      simp only [advance, if_neg hr, if_pos ht, dif_neg (show ¬(eligible h x t).Nonempty from hn)]
      change AlgorithmState.Step h b (fun i => (d i : ℝ)) r x.toReal t
        gs.toFinset (sampleQ h x gs).toReal ∧ Masked d (sampleQ h x gs)
      rw [sampleQ_cast]
      exact ⟨hstep, hx⟩
  · have hz : d t = 0 := le_antisymm (le_of_not_gt ht) (hd t)
    have hzR : (d t : ℝ) = 0 := by exact_mod_cast hz
    simpa only [advance, if_neg hr, if_neg ht, smallQ_cast] using
      ⟨AlgorithmState.Step.empty hr hzR, smallQ_masked r d x ∅ hx⟩

private def policyFrom {m k : ℕ} (h b : ℕ) (d : Fin k → ℚ) :
    (n : ℕ) → State m k → Policy m k n
  | 0, _ => .done
  | r + 1, x =>
    .step (fun t => (advance h b d r x t).1)
      (fun t => policyFrom h b d r (advance h b d r x t).2)

private theorem policyFrom_follows {m k h b : ℕ} (hh : 0 < h) (hb : 0 < b)
    (d : Fin k → ℚ) (hd : ∀ t, 0 ≤ d t) (n : ℕ) (x : State m k) (hx : Masked d x) :
    (policyFrom h b d n x).Follows (AlgorithmState.Step h b (fun t => (d t : ℝ))) x.toReal := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    intro t
    obtain ⟨hstep, hmask⟩ := advance_spec hh hb d hd n x hx t
    exact ⟨(advance h b d n x t).2.toReal, hstep, ih _ hmask⟩

/-- Executable Algorithm 1 for nonnegative rational valuation inputs. -/
def policy {m n k : ℕ} (v : Fin k → Fin m → ℚ) : Policy m k n :=
  let h := parameterQ k
  let d := materialize (fun t => rationalTPS (v t) n)
  policyFrom h (h / 4) d n (initialWithTPS v d)

theorem policy_follows {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    FollowsAlgorithm1 (fun t g => (v t g : ℝ)) (policy (n := n) v) := by
  let d : Fin k → ℚ := fun t => rationalTPS (v t) n
  let vR : Fin k → Fin m → ℝ := fun t g => (v t g : ℝ)
  have hTPS (t : Fin k) : (d t : ℝ) = truncatedShare (vR t) n :=
    rationalTPS_correct hn (v t) (hv t)
  have hd (t : Fin k) : 0 ≤ d t := by
    have hr : 0 ≤ (d t : ℝ) := by
      rw [hTPS]
      exact (truncatedShare_spec (vR t) (fun g => by change 0 ≤ (v t g : ℝ); exact_mod_cast hv t g) hn).1.1
    exact_mod_cast hr
  have hmask : Masked d (initial v n) := by
    intro t ht g
    have hh : ¬0 < d t := by simpa [protectedQ] using ht
    have hz : d t = 0 := le_antisymm (le_of_not_gt hh) (hd t)
    rw [initial_weight]
    simp [normalizedWeightQ, show rationalTPS (v t) n = 0 from hz]
  have hinit : (initial v n).toReal = algorithmInitial n vR := by
    simp only [State.toReal, algorithmInitial]
    congr 1
    · funext t g
      change ((initial v n).weight t g : ℝ) = normalizedWeight (vR t) n g
      rw [initial_weight]
      exact normalizedWeightQ_cast (v t) (hv t) hn g
    · funext t
      norm_num [State.toReal, initial, initialWithTPS, algorithmInitial]
  have hh := (bucketMultiplier_bounds hk).1
  have h := policyFrom_follows (show 0 < bucketMultiplier k by omega)
    (show 0 < bucketMultiplier k / 4 by omega) d hd n (initial v n) hmask
  rw [hinit, funext hTPS] at h
  have hbase : initialWithTPS v (fun t => rationalTPS (v t) n) = initial v n := by
    simp only [initial, materialize_eq]
  simpa only [policy, parameterQ_eq, FollowsAlgorithm1, materialize_eq, hbase] using h

theorem policy_guarantees_tps {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (policy (n := n) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => truncatedShare (fun g => (v t g : ℝ)) n / (2 * (bucketMultiplier k : ℝ)))
      Finset.univ := by
  exact (general_algorithm1_certified hn hk _ (fun t g => by exact_mod_cast hv t g)).2 _
    (policy_follows hn hk v hv)

theorem policy_guarantees_mms {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (policy (n := n) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => maximinShare (fun g => (v t g : ℝ)) n hn / (2 * (bucketMultiplier k : ℝ)))
      Finset.univ := by
  exact algorithm1_mms_of_follows hn hk _ (fun t g => by exact_mod_cast hv t g) _
    (policy_follows hn hk v hv)

end OnlineMMS.RationalAlgorithm1
