import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped BigOperators

namespace OnlineMMS

noncomputable section

/-- Sum over unordered pairs of positions, so twice this sum counts ordered pairs. -/
def pairSum : List ℝ → ℝ
  | [] => 0
  | x :: xs => x * xs.sum + pairSum xs

theorem pairSum_nonneg (xs : List ℝ) (hx : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ pairSum xs := by
  induction xs with
  | nil => simp [pairSum]
  | cons x xs ih =>
    have hx₀ := hx x (by simp)
    have hrest : ∀ y ∈ xs, 0 ≤ y := fun y hy => hx y (List.mem_cons_of_mem x hy)
    have hs : 0 ≤ xs.sum := List.sum_nonneg hrest
    exact add_nonneg (mul_nonneg hx₀ hs) (ih hrest)

theorem twice_pairSum_le_sum_sq (xs : List ℝ) :
    2 * pairSum xs ≤ xs.sum ^ 2 := by
  induction xs with
  | nil => simp [pairSum]
  | cons x xs ih =>
    simp only [pairSum, List.sum_cons]
    nlinarith [sq_nonneg x]

/-- The first-sample deficit bound, by induction on the selected weights. -/
theorem sum_le_one_add_pairSum (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) : xs.sum ≤ 1 + pairSum xs := by
  induction xs with
  | nil => norm_num [pairSum]
  | cons x xs ih =>
    have hx₀ := hx x (by simp)
    have hrest : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ 1 :=
      fun y hy => hx y (List.mem_cons_of_mem x hy)
    simp only [List.sum_cons, pairSum]
    by_cases hs : 1 ≤ xs.sum
    · nlinarith [ih hrest, mul_nonneg hx₀.1 (sub_nonneg.mpr hs)]
    · have hp := pairSum_nonneg xs (fun y hy => (hrest y hy).1)
      nlinarith [mul_nonneg (sub_nonneg.mpr hx₀.2) (sub_nonneg.mpr (le_of_not_ge hs))]

theorem pairSum_append (xs ys : List ℝ) :
    pairSum (xs ++ ys) = pairSum xs + pairSum ys + xs.sum * ys.sum := by
  induction xs with
  | nil => simp [pairSum]
  | cons x xs ih =>
    simp [pairSum, ih, List.sum_append]
    ring

/-- Each factor corresponds to one bucket. -/
def sampleProduct (h : ℝ) (xs : List ℝ) : ℝ :=
  (xs.map (fun x => 1 + (h - 1) * x)).prod

theorem sampleProduct_nonneg {h : ℝ} (hh : 1 ≤ h) (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ sampleProduct h xs := by
  induction xs with
  | nil => simp [sampleProduct]
  | cons x xs ih =>
    have hx₀ := hx x (by simp)
    have hrest : ∀ y ∈ xs, 0 ≤ y := fun y hy => hx y (List.mem_cons_of_mem x hy)
    change 0 ≤ (1 + (h - 1) * x) * sampleProduct h xs
    exact mul_nonneg (by linarith [mul_nonneg (sub_nonneg.mpr hh) hx₀]) (ih hrest)

theorem sampleProduct_le_exp {h : ℝ} (hh : 1 ≤ h) (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x) :
    sampleProduct h xs ≤ Real.exp ((h - 1) * xs.sum) := by
  induction xs with
  | nil => simp [sampleProduct]
  | cons x xs ih =>
    have hx₀ := hx x (by simp)
    have hrest : ∀ y ∈ xs, 0 ≤ y := fun y hy => hx y (List.mem_cons_of_mem x hy)
    change (1 + (h - 1) * x) * sampleProduct h xs ≤ Real.exp ((h - 1) * (x + xs.sum))
    rw [mul_add, Real.exp_add]
    exact mul_le_mul (by linarith [Real.add_one_le_exp ((h - 1) * x)]) (ih hrest)
      (sampleProduct_nonneg hh xs hrest) (Real.exp_nonneg _)

theorem rpow_sum_le_sampleProduct {h : ℝ} (hh : 1 ≤ h) (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) :
    h ^ xs.sum ≤ sampleProduct h xs := by
  have hh₀ : 0 < h := by linarith
  induction xs with
  | nil => simp [sampleProduct]
  | cons x xs ih =>
    have hx₀ := hx x (by simp)
    have hrest : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ 1 :=
      fun y hy => hx y (List.mem_cons_of_mem x hy)
    have hfactor : h ^ x ≤ 1 + (h - 1) * x := by
      have hconv := convexOn_exp.2 (show (0 : ℝ) ∈ Set.univ from trivial)
        (show Real.log h ∈ Set.univ from trivial) (sub_nonneg.mpr hx₀.2) hx₀.1
        (show 1 - x + x = 1 by ring)
      rw [Real.rpow_def_of_pos hh₀]
      simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
        Real.exp_log hh₀] at hconv
      rw [mul_comm (Real.log h)]
      linarith
    change h ^ (x + xs.sum) ≤ (1 + (h - 1) * x) * sampleProduct h xs
    rw [Real.rpow_add hh₀]
    exact mul_le_mul hfactor (ih hrest) (Real.rpow_nonneg (le_of_lt hh₀) _)
      (le_trans (Real.rpow_nonneg (le_of_lt hh₀) _) hfactor)

section Selection

variable {TypeIndex Good : Type*} [Fintype TypeIndex]

noncomputable def slotMean (w : TypeIndex → Good → ℝ) (B : Finset Good) :
    TypeIndex → ℝ :=
  fun t => (∑ g ∈ B, w t g) / (B.card : ℝ)

noncomputable def slotMeans (w : TypeIndex → Good → ℝ) (buckets : List (Finset Good)) :
    List (TypeIndex → ℝ) :=
  buckets.map (slotMean w)

def rowObjective (h q c p : ℝ) (xs : List ℝ) : ℝ :=
  q * (2 * pairSum xs) + c * p * sampleProduct h xs

/-- Setting `q = 1` and `c = 128 / h^3` is the first-sample objective.
Setting `q = 0` and `c = 1` is the later objective. -/
noncomputable def sampleObjective (h q c : ℝ) (P : TypeIndex → ℝ)
    (slots : List (TypeIndex → ℝ)) : ℝ :=
  ∑ t, rowObjective h q c (P t) (slots.map (fun z => z t))

def slotCoefficient (h q c p : ℝ) (left right : List ℝ) : ℝ :=
  2 * q * (left.sum + right.sum) +
    c * p * sampleProduct h left * sampleProduct h right * (h - 1)

theorem rowObjective_slot (h q c p : ℝ) (left right : List ℝ) (x : ℝ) :
    rowObjective h q c p (left ++ x :: right) =
      rowObjective h q c p (left ++ 0 :: right) + x * slotCoefficient h q c p left right := by
  simp only [rowObjective, slotCoefficient, pairSum_append, pairSum, List.sum_cons,
    sampleProduct, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  ring

theorem sampleObjective_slot (h q c : ℝ) (P : TypeIndex → ℝ)
    (left right : List (TypeIndex → ℝ)) (z : TypeIndex → ℝ) :
    sampleObjective h q c P (left ++ z :: right) =
      sampleObjective h q c P (left ++ (fun _ => 0) :: right) +
        ∑ t, z t * slotCoefficient h q c (P t)
          (left.map (fun x => x t)) (right.map (fun x => x t)) := by
  unfold sampleObjective
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro t _
  simpa only [List.map_append, List.map_cons] using
    rowObjective_slot h q c (P t) (left.map (fun x => x t)) (right.map (fun x => x t)) (z t)

private theorem min_weighted_score_le_mean (w : TypeIndex → Good → ℝ) (B : Finset Good)
    (coeff : TypeIndex → ℝ) (g : Good) (hg : g ∈ B)
    (hmin : ∀ a ∈ B, (∑ t, w t g * coeff t) ≤ ∑ t, w t a * coeff t) :
    (∑ t, w t g * coeff t) ≤ ∑ t, slotMean w B t * coeff t := by
  classical
  let score (a : Good) := ∑ t, w t a * coeff t
  have hc : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr ⟨g, hg⟩
  calc
    score g = (∑ a ∈ B, score g) / (B.card : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, hc.ne']
    _ ≤ (∑ a ∈ B, score a) / (B.card : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hmin) hc.le
    _ = ∑ t, slotMean w B t * coeff t := by
      unfold score slotMean
      rw [Finset.sum_comm, Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro t _
      rw [← Finset.sum_mul]
      ring

private def GreedyForSlots (w : TypeIndex → Good → ℝ)
    (objective : List (TypeIndex → ℝ) → ℝ) :
    List (TypeIndex → ℝ) → List (Finset Good) → List Good → Prop
  | _, [], [] => True
  | left, B :: buckets, g :: selected =>
      g ∈ B ∧
        (∀ a ∈ B,
          objective (left ++ (fun t => w t g) :: slotMeans w buckets) ≤
            objective (left ++ (fun t => w t a) :: slotMeans w buckets)) ∧
        GreedyForSlots w objective (left ++ [fun t => w t g]) buckets selected
  | _, _, _ => False

/-- Each selected good minimizes the objective with the previously chosen
goods fixed and the unvisited buckets represented by their mean profiles. -/
def IsGreedySample (w : TypeIndex → Good → ℝ) (h q c : ℝ) (P : TypeIndex → ℝ) :
    List (TypeIndex → ℝ) → List (Finset Good) → List Good → Prop :=
  GreedyForSlots w (sampleObjective h q c P)

/-- The objective summed over precisely the types protected by the policy. -/
def protectedSampleObjective (h q c : ℝ) (P : TypeIndex → ℝ)
    (protectedTypes : Finset TypeIndex) (slots : List (TypeIndex → ℝ)) : ℝ :=
  ∑ t ∈ protectedTypes, rowObjective h q c (P t) (slots.map (fun z => z t))

/-- Conditional minimization using only the protected rows. -/
def IsProtectedGreedySample (w : TypeIndex → Good → ℝ) (h q c : ℝ) (P : TypeIndex → ℝ)
    (protectedTypes : Finset TypeIndex) :
    List (TypeIndex → ℝ) → List (Finset Good) → List Good → Prop :=
  GreedyForSlots w (protectedSampleObjective h q c P protectedTypes)

private theorem pairSum_product_of_zeros (h : ℝ) (xs : List ℝ)
    (hz : ∀ x ∈ xs, x = 0) : pairSum xs = 0 ∧ sampleProduct h xs = 1 := by
  induction xs with
  | nil => simp [pairSum, sampleProduct]
  | cons x xs ih =>
    have heq := hz x (by simp)
    obtain ⟨hpair, hprod⟩ := ih (fun y hy => hz y (List.mem_cons_of_mem x hy))
    constructor
    · simp [pairSum, heq, hpair]
    · change (1 + (h - 1) * x) * sampleProduct h xs = 1
      simp [heq, hprod]

private theorem sampleObjective_eq_protected [DecidableEq TypeIndex]
    (h q c : ℝ) (P : TypeIndex → ℝ) (protectedTypes : Finset TypeIndex)
    (slots : List (TypeIndex → ℝ))
    (hz : ∀ z ∈ slots, ∀ t ∉ protectedTypes, z t = 0) :
    sampleObjective h q c P slots = (∑ t ∈ Finset.univ \ protectedTypes, c * P t) +
      protectedSampleObjective h q c P protectedTypes slots := by
  unfold sampleObjective protectedSampleObjective
  rw [← Finset.sum_sdiff (Finset.subset_univ protectedTypes)]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have ht' : t ∉ protectedTypes := (Finset.mem_sdiff.mp ht).2
  have hrow (x : ℝ) (hx : x ∈ slots.map (fun z => z t)) : x = 0 := by
    obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hx
    exact hz z hz' t ht'
  obtain ⟨hpair, hprod⟩ := pairSum_product_of_zeros h _ hrow
  simp [rowObjective, hpair, hprod]

private theorem greedy_sample_iff_protected_aux (w : TypeIndex → Good → ℝ)
    (h q c : ℝ) (P : TypeIndex → ℝ) (protectedTypes : Finset TypeIndex)
    (hzero : ∀ t ∉ protectedTypes, ∀ g, w t g = 0)
    (buckets : List (Finset Good)) (left : List (TypeIndex → ℝ)) (selected : List Good)
    (hleft : ∀ z ∈ left, ∀ t ∉ protectedTypes, z t = 0) :
    IsGreedySample w h q c P left buckets selected ↔
      IsProtectedGreedySample w h q c P protectedTypes left buckets selected := by
  classical
  unfold IsGreedySample IsProtectedGreedySample
  induction buckets generalizing left selected with
  | nil => cases selected <;> rfl
  | cons B buckets ih =>
    cases selected with
    | nil => rfl
    | cons g selected =>
      have hf (a : Good) : ∀ z ∈ left ++ (fun t => w t a) :: slotMeans w buckets,
          ∀ t ∉ protectedTypes, z t = 0 := by
        intro z hz t ht
        rcases List.mem_append.mp hz with hfixed | hrest
        · exact hleft z hfixed t ht
        · rcases List.mem_cons.mp hrest with heq | hmean
          · rw [heq]
            exact hzero t ht a
          · obtain ⟨C, _, rfl⟩ := List.mem_map.mp hmean
            simp [slotMean, hzero t ht]
      have happ : ∀ z ∈ left ++ [fun t => w t g], ∀ t ∉ protectedTypes, z t = 0 := by
        intro z hz t ht
        rcases List.mem_append.mp hz with ha | ha
        · exact hleft z ha t ht
        · have heq := List.mem_singleton.mp ha
          rw [heq]
          exact hzero t ht g
      have hcmp :
          (∀ a ∈ B, sampleObjective h q c P (left ++ (fun t => w t g) :: slotMeans w buckets) ≤
            sampleObjective h q c P (left ++ (fun t => w t a) :: slotMeans w buckets)) ↔
          (∀ a ∈ B, protectedSampleObjective h q c P protectedTypes
              (left ++ (fun t => w t g) :: slotMeans w buckets) ≤
            protectedSampleObjective h q c P protectedTypes
              (left ++ (fun t => w t a) :: slotMeans w buckets)) := by
        apply forall_congr'
        intro a
        apply forall_congr'
        intro _
        rw [sampleObjective_eq_protected h q c P protectedTypes _ (hf g),
          sampleObjective_eq_protected h q c P protectedTypes _ (hf a),
          add_le_add_iff_left]
      simp only [GreedyForSlots, hcmp, ih _ _ happ]

/-- Zero-weight rows add a constant independent of the sample, so dropping
them preserves every minimizer, including ties. -/
theorem greedy_sample_iff_protected (w : TypeIndex → Good → ℝ)
    (h q c : ℝ) (P : TypeIndex → ℝ) (protectedTypes : Finset TypeIndex)
    (hzero : ∀ t ∉ protectedTypes, ∀ g, w t g = 0)
    (buckets : List (Finset Good)) (selected : List Good) :
    IsGreedySample w h q c P [] buckets selected ↔
      IsProtectedGreedySample w h q c P protectedTypes [] buckets selected :=
  greedy_sample_iff_protected_aux w h q c P protectedTypes hzero buckets [] selected (by simp)

private theorem greedy_sample_le_mean_aux (w : TypeIndex → Good → ℝ)
    (h q c : ℝ) (P : TypeIndex → ℝ) (buckets : List (Finset Good))
    (left : List (TypeIndex → ℝ)) (selected : List Good)
    (hgreedy : IsGreedySample w h q c P left buckets selected) :
    List.Forall₂ (fun B g => g ∈ B) buckets selected ∧
      sampleObjective h q c P (left ++ selected.map (fun g t => w t g)) ≤
        sampleObjective h q c P (left ++ slotMeans w buckets) := by
  induction buckets generalizing left selected with
  | nil =>
    cases selected with
    | nil => exact ⟨.nil, le_rfl⟩
    | cons g selected => exact False.elim hgreedy
  | cons B buckets ih =>
    cases selected with
    | nil => exact False.elim hgreedy
    | cons g selected =>
      obtain ⟨hg, hmin, hrest⟩ := hgreedy
      let right := slotMeans w buckets
      let coeff (t : TypeIndex) := slotCoefficient h q c (P t)
        (left.map (fun z => z t)) (right.map (fun z => z t))
      have hc (a : Good) (ha : a ∈ B) :
          (∑ t, w t g * coeff t) ≤ ∑ t, w t a * coeff t := by
        have harg := hmin a ha
        rw [sampleObjective_slot h q c P left right (fun t => w t g),
          sampleObjective_slot h q c P left right (fun t => w t a)] at harg
        exact (add_le_add_iff_left _).mp harg
      obtain ⟨hselected, hscore⟩ := ih (left ++ [fun t => w t g]) selected hrest
      refine ⟨.cons hg hselected, ?_⟩
      calc
        _ ≤ sampleObjective h q c P (left ++ (fun t => w t g) :: right) := by
          simpa only [List.append_assoc, List.singleton_append, List.map_cons] using hscore
        _ ≤ _ := by
          change sampleObjective h q c P (left ++ (fun t => w t g) :: right) ≤
            sampleObjective h q c P (left ++ slotMean w B :: right)
          rw [sampleObjective_slot h q c P left right (fun t => w t g),
            sampleObjective_slot h q c P left right (slotMean w B)]
          exact add_le_add_left (min_weighted_score_le_mean w B coeff g hg hc) _

/-- Every sequence of conditional-mean minimizers selects a good from each
bucket and has objective at most its initial conditional mean. -/
theorem greedy_sample_le_mean (w : TypeIndex → Good → ℝ)
    (h q c : ℝ) (P : TypeIndex → ℝ) (buckets : List (Finset Good))
    (selected : List Good) (hgreedy : IsGreedySample w h q c P [] buckets selected) :
    List.Forall₂ (fun B g => g ∈ B) buckets selected ∧
      sampleObjective h q c P (selected.map (fun g t => w t g)) ≤
        sampleObjective h q c P (slotMeans w buckets) := by
  simpa only [List.nil_append] using
    greedy_sample_le_mean_aux w h q c P buckets [] selected hgreedy

private theorem selectSampleAux (w : TypeIndex → Good → ℝ)
    (h q c : ℝ) (P : TypeIndex → ℝ) (buckets : List (Finset Good))
    (hne : ∀ B ∈ buckets, B.Nonempty) (left : List (TypeIndex → ℝ)) :
    ∃ selected : List Good, IsGreedySample w h q c P left buckets selected := by
  induction buckets generalizing left with
  | nil => exact ⟨[], trivial⟩
  | cons B buckets ih =>
    let cost (g : Good) :=
      sampleObjective h q c P (left ++ (fun t => w t g) :: slotMeans w buckets)
    obtain ⟨g, hg, hmin⟩ := B.exists_min_image cost (hne B (by simp))
    have hrest : ∀ C ∈ buckets, Finset.Nonempty C :=
      fun C hC => hne C (List.mem_cons_of_mem B hC)
    obtain ⟨selected, hselected⟩ := ih hrest (left ++ [fun t => w t g])
    exact ⟨g :: selected, hg, hmin, hselected⟩

/-- Conditional-mean selection when the objective includes fixed preceding
profiles as well as one profile per bucket. -/
theorem exists_prefixed_sample_le_mean (w : TypeIndex → Good → ℝ)
    (h q c : ℝ) (P : TypeIndex → ℝ) (left : List (TypeIndex → ℝ))
    (buckets : List (Finset Good)) (hne : ∀ B ∈ buckets, B.Nonempty) :
    ∃ selected : List Good, List.Forall₂ (fun B g => g ∈ B) buckets selected ∧
      sampleObjective h q c P (left ++ selected.map (fun g t => w t g)) ≤
        sampleObjective h q c P (left ++ slotMeans w buckets) := by
  obtain ⟨selected, hs⟩ := selectSampleAux w h q c P buckets hne left
  exact ⟨selected, greedy_sample_le_mean_aux w h q c P buckets left selected hs⟩

/-- Starting from all bucket means, successively fix a minimizer of each
conditional mean. The selected sample's objective is at most the initial mean. -/
theorem exists_greedy_sample_le_mean (w : TypeIndex → Good → ℝ)
    (h q c : ℝ) (P : TypeIndex → ℝ) (buckets : List (Finset Good))
    (hne : ∀ B ∈ buckets, B.Nonempty) :
    ∃ selected : List Good, List.Forall₂ (fun B g => g ∈ B) buckets selected ∧
      IsGreedySample w h q c P [] buckets selected ∧
      sampleObjective h q c P (selected.map (fun g t => w t g)) ≤
        sampleObjective h q c P (slotMeans w buckets) := by
  obtain ⟨selected, hgreedy⟩ := selectSampleAux w h q c P buckets hne []
  obtain ⟨hselected, hbound⟩ := greedy_sample_le_mean w h q c P buckets selected hgreedy
  exact ⟨selected, hselected, hgreedy, hbound⟩

theorem exists_sample_le_mean (w : TypeIndex → Good → ℝ)
    (h q c : ℝ) (P : TypeIndex → ℝ) (buckets : List (Finset Good))
    (hne : ∀ B ∈ buckets, B.Nonempty) :
    ∃ selected : List Good, List.Forall₂ (fun B g => g ∈ B) buckets selected ∧
      sampleObjective h q c P (selected.map (fun g t => w t g)) ≤
        sampleObjective h q c P (slotMeans w buckets) := by
  obtain ⟨selected, hselected, _, hbound⟩ := exists_greedy_sample_le_mean w h q c P buckets hne
  exact ⟨selected, hselected, hbound⟩


section BucketMass

variable [DecidableEq Good]

private def bucketUnion (buckets : List (Finset Good)) : Finset Good :=
  buckets.foldr (· ∪ ·) ∅

private theorem mem_bucketUnion (buckets : List (Finset Good)) (g : Good) :
    g ∈ bucketUnion buckets ↔ ∃ B ∈ buckets, g ∈ B := by
  induction buckets with
  | nil => simp [bucketUnion]
  | cons B buckets ih =>
    change g ∈ B ∪ bucketUnion buckets ↔ _
    rw [Finset.mem_union, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (hg | ⟨C, hC, hg⟩)
      · exact ⟨B, Or.inl rfl, hg⟩
      · exact ⟨C, Or.inr hC, hg⟩
    · rintro ⟨C, rfl | hC, hg⟩
      · exact Or.inl hg
      · exact Or.inr ⟨C, hC, hg⟩

private theorem sum_bucket_totals (f : Good → ℝ) (buckets : List (Finset Good))
    (hdisj : buckets.Pairwise Disjoint) :
    (buckets.map (fun B => ∑ g ∈ B, f g)).sum = ∑ g ∈ bucketUnion buckets, f g := by
  induction buckets with
  | nil => simp [bucketUnion]
  | cons B buckets ih =>
    obtain ⟨hB, htail⟩ := List.pairwise_cons.mp hdisj
    have hu : Disjoint B (bucketUnion buckets) := by
      refine Finset.disjoint_left.mpr ?_
      intro g hg hu
      obtain ⟨C, hC, hgC⟩ := (mem_bucketUnion buckets g).mp hu
      exact Finset.disjoint_left.mp (hB C hC) hg hgC
    change (∑ g ∈ B, f g) + (buckets.map (fun C => ∑ g ∈ C, f g)).sum =
      ∑ g ∈ B ∪ bucketUnion buckets, f g
    rw [Finset.sum_union hu, ih htail]

omit [Fintype TypeIndex] [DecidableEq Good] in
theorem slotMeans_nonneg (w : TypeIndex → Good → ℝ) (buckets : List (Finset Good))
    (t : TypeIndex) (hw : ∀ g, 0 ≤ w t g) :
    ∀ x ∈ (slotMeans w buckets).map (fun z => z t), 0 ≤ x := by
  intro x hx
  rw [slotMeans, List.map_map] at hx
  obtain ⟨B, _, rfl⟩ := List.mem_map.mp hx
  exact div_nonneg (Finset.sum_nonneg (fun g _ => hw g)) (Nat.cast_nonneg _)

omit [Fintype TypeIndex] in
/-- Bucket means sum to at most the remaining total divided by the full-bucket width. -/
theorem slotMeans_sum_le_of_width (w : TypeIndex → Good → ℝ)
    (buckets : List (Finset Good)) (remaining : Finset Good) (width : ℕ)
    (hdisj : buckets.Pairwise Disjoint)
    (hwidth : ∀ B ∈ buckets, B.card = width)
    (hsubset : ∀ B ∈ buckets, B ⊆ remaining)
    (t : TypeIndex) (hw : ∀ g, 0 ≤ w t g) :
    ((slotMeans w buckets).map (fun z => z t)).sum ≤
      (∑ g ∈ remaining, w t g) / (width : ℝ) := by
  have hmass :
      ((slotMeans w buckets).map (fun z => z t)).sum =
        (buckets.map (fun B => ∑ g ∈ B, w t g)).sum / (width : ℝ) := by
    clear hdisj hsubset
    induction buckets with
    | nil => simp [slotMeans]
    | cons B buckets ih =>
      have hB := hwidth B (by simp)
      have htail : ∀ C ∈ buckets, Finset.card C = width :=
        fun C hC => hwidth C (List.mem_cons_of_mem B hC)
      simp only [slotMeans, List.map_cons, List.sum_cons, slotMean] at *
      rw [ih htail, hB, add_div]
  rw [hmass, sum_bucket_totals (w t) buckets hdisj]
  refine div_le_div_of_nonneg_right
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun g _ _ => hw g)) (Nat.cast_nonneg _)
  intro g hg
  obtain ⟨B, hB, hg⟩ := (mem_bucketUnion buckets g).mp hg
  exact hsubset B hB hg

end BucketMass

theorem firstSample_mean_bound {h : ℝ} (hh : 1 ≤ h) (slots : List (TypeIndex → ℝ))
    (hnonneg : ∀ t, ∀ x ∈ slots.map (fun z => z t), 0 ≤ x)
    (hmass : ∀ t, (slots.map (fun z => z t)).sum ≤ 1 / h) :
    sampleObjective h 1 (128 / h ^ 3) (fun _ => 1) slots ≤
      (Fintype.card TypeIndex : ℝ) / h ^ 2 * (1 + 384 / h) := by
  have hh₀ : 0 < h := by linarith
  have hc : 0 ≤ 128 / h ^ 3 := by positivity
  unfold sampleObjective
  calc
    _ ≤ ∑ _t : TypeIndex, (1 / h ^ 2 + 128 / h ^ 3 * 3) := by
      refine Finset.sum_le_sum ?_
      intro t _
      let xs := slots.map (fun z => z t)
      have hsum₀ : 0 ≤ xs.sum := List.sum_nonneg (hnonneg t)
      have hQ : 2 * pairSum xs ≤ 1 / h ^ 2 := by
        calc
          _ ≤ xs.sum ^ 2 := twice_pairSum_le_sum_sq xs
          _ ≤ (1 / h) ^ 2 := pow_le_pow_left₀ hsum₀ (hmass t) _
          _ = _ := by ring
      have hexp : (h - 1) * xs.sum ≤ 1 := by
        calc
          _ ≤ h * xs.sum := by nlinarith
          _ ≤ h * (1 / h) := mul_le_mul_of_nonneg_left (hmass t) hh₀.le
          _ = 1 := by field_simp
      have hP : sampleProduct h xs ≤ 3 :=
        (sampleProduct_le_exp hh xs (hnonneg t)).trans <|
          (Real.exp_le_exp.mpr hexp).trans <| le_of_lt <|
            Real.exp_one_lt_d9.trans (by norm_num)
      simpa only [rowObjective, one_mul, mul_one] using
        add_le_add hQ (mul_le_mul_of_nonneg_left hP hc)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
      ring

theorem laterSample_mean_bound {h : ℝ} (hh : 1 ≤ h) (P : TypeIndex → ℝ)
    (hP : ∀ t, 0 ≤ P t) (slots : List (TypeIndex → ℝ))
    (hnonneg : ∀ t, ∀ x ∈ slots.map (fun z => z t), 0 ≤ x)
    (hmass : ∀ t, (slots.map (fun z => z t)).sum ≤ 4 / h) :
    sampleObjective h 0 1 P slots ≤ (∑ t, P t) * Real.exp 4 := by
  have hh₀ : 0 < h := by linarith
  unfold sampleObjective
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro t _
  let xs := slots.map (fun z => z t)
  have hsum₀ : 0 ≤ xs.sum := List.sum_nonneg (hnonneg t)
  have hexp : (h - 1) * xs.sum ≤ 4 := by
    calc
      _ ≤ h * xs.sum := by nlinarith
      _ ≤ h * (4 / h) := mul_le_mul_of_nonneg_left (hmass t) hh₀.le
      _ = 4 := by field_simp
  simp only [rowObjective, zero_mul, one_mul, zero_add]
  exact mul_le_mul_of_nonneg_left
    ((sampleProduct_le_exp hh xs (hnonneg t)).trans (Real.exp_le_exp.mpr hexp))
    (hP t)


/-- Convert the first-sample objective bound into both reserve and potential bounds. -/
theorem firstSample_bounds_of_objective {h : ℝ} (hh : 1 ≤ h)
    (slots : List (TypeIndex → ℝ))
    (hslots : ∀ z ∈ slots, ∀ t, 0 ≤ z t ∧ z t ≤ 1)
    (hobj : sampleObjective h 1 (128 / h ^ 3) (fun _ => 1) slots ≤ 2 - 1 / h) :
    (∀ t, (slots.map (fun z => z t)).sum ≤ 2 - 1 / (2 * h)) ∧
      (∑ t, sampleProduct h (slots.map (fun z => z t))) ≤ h ^ 3 / 64 := by
  have hh₀ : 0 < h := by linarith
  have hc : 0 < 128 / h ^ 3 := by positivity
  have hx (t : TypeIndex) : ∀ x ∈ slots.map (fun z => z t), 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact hslots z hz t
  have hQ (t : TypeIndex) := pairSum_nonneg (slots.map (fun z => z t))
    (fun x hx' => (hx t x hx').1)
  have hP (t : TypeIndex) := sampleProduct_nonneg hh (slots.map (fun z => z t))
    (fun x hx' => (hx t x hx').1)
  constructor
  · intro t
    let xs := slots.map (fun z => z t)
    have hrow : rowObjective h 1 (128 / h ^ 3) 1 xs ≤
        sampleObjective h 1 (128 / h ^ 3) (fun _ => 1) slots := by
      unfold sampleObjective
      refine Finset.single_le_sum
        (f := fun i => rowObjective h 1 (128 / h ^ 3) 1 (slots.map (fun z => z i)))
        (fun i _ => ?_) (Finset.mem_univ t)
      simpa only [rowObjective, one_mul, mul_one] using
        add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hQ i))
          (mul_nonneg hc.le (hP i))
    have hpair : 2 * pairSum xs ≤ 2 - 1 / h := by
      calc
        _ ≤ rowObjective h 1 (128 / h ^ 3) 1 xs := by
          simp only [rowObjective, one_mul, mul_one]
          exact le_add_of_nonneg_right (mul_nonneg hc.le (hP t))
        _ ≤ _ := hrow.trans hobj
    have hden : 1 / (2 * h) = (1 / h) / 2 := by ring
    rw [hden]
    linarith [sum_le_one_add_pairSum xs (hx t)]
  · apply (mul_le_mul_left hc).mp
    calc
      _ = ∑ t, 128 / h ^ 3 * sampleProduct h (slots.map (fun z => z t)) :=
        Finset.mul_sum ..
      _ ≤ sampleObjective h 1 (128 / h ^ 3) (fun _ => 1) slots := by
        unfold sampleObjective
        refine Finset.sum_le_sum (fun t _ => ?_)
        simp only [rowObjective, one_mul, mul_one]
        exact le_add_of_nonneg_left (by linarith [hQ t])
      _ ≤ 2 := hobj.trans (by linarith [show 0 ≤ 1 / h by positivity])
      _ = _ := by field_simp; ring

theorem rpow_deficit_add_le {h D P : ℝ} (hh : 1 ≤ h) (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) (hD : h ^ D ≤ P) :
    h ^ (D + xs.sum) ≤ P * sampleProduct h xs := by
  have hh₀ : 0 < h := by linarith
  rw [Real.rpow_add hh₀]
  exact mul_le_mul hD (rpow_sum_le_sampleProduct hh xs hx)
    (Real.rpow_nonneg hh₀.le _) ((Real.rpow_nonneg hh₀.le _).trans hD)

end Selection

end

end OnlineMMS
