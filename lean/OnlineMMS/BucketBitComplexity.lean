import OnlineMMS.RationalArithmetic
import OnlineMMS.Sampling
import OnlineMMS.Trimming
import Mathlib.Data.List.MinMax

/-! Rational evaluation of the bucket objectives for Theorem 3.1,
Proposition C.1 and the supplementary quadratic estimator. The cast lemmas
connect the executable expressions to the real-valued allocation proofs. -/

namespace OnlineMMS.BucketBitComplexity

open RationalArithmetic

open private trimmedListWeight from OnlineMMS.Trimming
open private greedy_sample_le_mean_aux from OnlineMMS.Sampling

def trimListQ {G : Type*} [DecidableEq G] (w : G → ℚ) : List G → ℚ → G → ℚ
  | [], _, _ => 0
  | g :: gs, remove, x =>
      if x = g then max 0 (w g - remove)
      else trimListQ w gs (max 0 (remove - w g)) x

def trimWeightsQ {m : ℕ} (remaining : Finset (Fin m)) (w : Fin m → ℚ)
    (cap : ℚ) : Fin m → ℚ :=
  trimListQ w (remaining.sort (· ≤ ·)) (max 0 ((∑ g ∈ remaining, w g) - cap))

theorem trimListQ_cast {G : Type*} [DecidableEq G] (w : G → ℚ)
    (gs : List G) (remove : ℚ) (x : G) :
    (trimListQ w gs remove x : ℝ) =
      trimmedListWeight (fun g => (w g : ℝ)) gs (remove : ℝ) x := by
  induction gs generalizing remove with
  | nil => simp [trimListQ, trimmedListWeight]
  | cons g gs ih =>
    by_cases hx : x = g
    · simp [trimListQ, trimmedListWeight, hx]
    · simp [trimListQ, trimmedListWeight, hx, ih]

theorem trimWeightsQ_cast {m : ℕ} (remaining : Finset (Fin m)) (w : Fin m → ℚ)
    (cap : ℚ) (g : Fin m) :
    (trimWeightsQ remaining w cap g : ℝ) =
      trimWeights remaining (fun i => (w i : ℝ)) (cap : ℝ) g := by
  simp [trimWeightsQ, trimWeights, trimListQ_cast, bundleValue]

theorem onGrid_finset_sum {G : Type*} [DecidableEq G] (D : ℕ) (s : Finset G)
    (w : G → ℚ) (hw : ∀ g ∈ s, OnGrid D (w g)) : OnGrid D (∑ g ∈ s, w g) := by
  induction s using Finset.induction_on with
  | empty => simpa using onGrid_zero D
  | @insert g s hg ih =>
    rw [Finset.sum_insert hg]
    exact (hw g (by simp)).add (ih (fun i hi => hw i (by simp [hi])))

theorem trimListQ_onGrid {G : Type*} [DecidableEq G] (D : ℕ) (w : G → ℚ)
    (hw : ∀ g, OnGrid D (w g)) (gs : List G) (remove : ℚ) (hr : OnGrid D remove)
    (g : G) : OnGrid D (trimListQ w gs remove g) := by
  induction gs generalizing remove with
  | nil => exact onGrid_zero D
  | cons x xs ih =>
    simp only [trimListQ]
    split
    · exact (onGrid_zero D).max ((hw x).sub hr)
    · exact ih _ ((onGrid_zero D).max (hr.sub (hw x)))

/-- Integer-target trimming never multiplies the common denominator. -/
theorem trimWeightsQ_onGrid {m D : ℕ} (hD : 0 < D) (remaining : Finset (Fin m))
    (w : Fin m → ℚ) (N : ℕ) (hw : ∀ g, OnGrid D (w g)) (g : Fin m) :
    OnGrid D (trimWeightsQ remaining w N g) :=
  trimListQ_onGrid D w hw _ _
    ((onGrid_zero D).max ((onGrid_finset_sum D remaining w (fun i _ => hw i)).sub
      (onGrid_nat hD N))) g

theorem trimWeightsQ_bounded {m D : ℕ} (hD : 0 < D) (remaining : Finset (Fin m))
    (w : Fin m → ℚ) (N : ℕ) (hw : ∀ g, OnGrid D (w g))
    (hunit : ∀ g, 0 ≤ w g ∧ w g ≤ 1) (g : Fin m) :
    Bounded (trimWeightsQ remaining w N g) (D.size + 1) := by
  have hreal := (trimWeights_spec remaining (fun i => (w i : ℝ))
    (fun i => by dsimp; exact_mod_cast (hunit i).1) (N : ℝ) (by positivity)).1 g
  have he := trimWeightsQ_cast remaining w (N : ℚ) g
  norm_num at he
  rw [← he] at hreal
  apply (trimWeightsQ_onGrid hD remaining w N hw g).bounded hD
  · exact_mod_cast hreal.1
  · have hb : (trimWeightsQ remaining w N g : ℝ) ≤ 1 :=
      hreal.2.trans (by exact_mod_cast (hunit g).2)
    exact_mod_cast hb

def pairSumQ : List ℚ → ℚ
  | [] => 0
  | x :: xs => x * xs.sum + pairSumQ xs

def sampleProductQ (h : ℚ) (xs : List ℚ) : ℚ :=
  (xs.map (fun x => 1 + (h - 1) * x)).prod

def rowObjectiveQ (h q c p : ℚ) (xs : List ℚ) : ℚ :=
  q * (2 * pairSumQ xs) + c * p * sampleProductQ h xs

def objectiveQ {k : ℕ} (h q c : ℚ) (P : Fin k → ℚ)
    (slots : List (Fin k → ℚ)) : ℚ :=
  ∑ t, rowObjectiveQ h q c (P t) (slots.map (fun z => z t))

def slotMeanQ {m k : ℕ} (w : Fin k → Fin m → ℚ) (B : Finset (Fin m))
    (t : Fin k) : ℚ := (∑ g ∈ B, w t g) / B.card

def slotMeansQ {m k : ℕ} (w : Fin k → Fin m → ℚ)
    (buckets : List (Finset (Fin m))) : List (Fin k → ℚ) :=
  buckets.map (slotMeanQ w)

def realProfiles {k : ℕ} (slots : List (Fin k → ℚ)) : List (Fin k → ℝ) :=
  slots.map (fun z t => (z t : ℝ))

theorem pairSumQ_cast (xs : List ℚ) :
    (pairSumQ xs : ℝ) = pairSum (xs.map (fun x : ℚ => (x : ℝ))) := by
  induction xs with
  | nil => simp [pairSumQ, pairSum]
  | cons x xs ih => simp [pairSumQ, pairSum, ih]

theorem sampleProductQ_cast (h : ℚ) (xs : List ℚ) :
    (sampleProductQ h xs : ℝ) = sampleProduct (h : ℝ) (xs.map (fun x : ℚ => (x : ℝ))) := by
  simp [sampleProductQ, sampleProduct, List.map_map, Function.comp_def]

theorem rowObjectiveQ_cast (h q c p : ℚ) (xs : List ℚ) :
    (rowObjectiveQ h q c p xs : ℝ) =
      rowObjective (h : ℝ) (q : ℝ) (c : ℝ) (p : ℝ) (xs.map (fun x : ℚ => (x : ℝ))) := by
  simp [rowObjectiveQ, rowObjective, pairSumQ_cast, sampleProductQ_cast]

theorem objectiveQ_cast {k : ℕ} (h q c : ℚ) (P : Fin k → ℚ)
    (slots : List (Fin k → ℚ)) :
    (objectiveQ h q c P slots : ℝ) =
      sampleObjective (h : ℝ) (q : ℝ) (c : ℝ) (fun t => (P t : ℝ)) (realProfiles slots) := by
  simp [objectiveQ, sampleObjective, rowObjectiveQ_cast, realProfiles, List.map_map,
    Function.comp_def]

theorem slotMeanQ_cast {m k : ℕ} (w : Fin k → Fin m → ℚ) (B : Finset (Fin m))
    (t : Fin k) : (slotMeanQ w B t : ℝ) = slotMean (fun i g => (w i g : ℝ)) B t := by
  simp [slotMeanQ, slotMean]

theorem slotMeansQ_cast {m k : ℕ} (w : Fin k → Fin m → ℚ)
    (bs : List (Finset (Fin m))) :
    realProfiles (slotMeansQ w bs) = slotMeans (fun i g => (w i g : ℝ)) bs := by
  simp only [realProfiles, slotMeansQ, slotMeans, List.map_map]
  apply List.map_congr_left
  intro B _
  funext t
  exact slotMeanQ_cast w B t

/-- A bucket mean adds its width, and only its width, to the denominator. -/
theorem slotMeanQ_bounded {m k D H : ℕ} (hD : 0 < D) (hH : 0 < H)
    (w : Fin k → Fin m → ℚ) (B : Finset (Fin m)) (hB : B.card = H)
    (t : Fin k) (hw : ∀ g, OnGrid D (w t g))
    (hu : ∀ g, 0 ≤ w t g ∧ w t g ≤ 1) :
    Bounded (slotMeanQ w B t) (D.size + H.size + 1) := by
  have hgrid : OnGrid (D * H) (slotMeanQ w B t) := by
    simpa [slotMeanQ, hB] using
      (onGrid_finset_sum D B (w t) (fun g _ => hw g)).div_nat (H := H)
  have hpos : (0 : ℚ) < H := by exact_mod_cast hH
  have hn : 0 ≤ slotMeanQ w B t := by
    apply div_nonneg
    · exact Finset.sum_nonneg fun g _ => (hu g).1
    · positivity
  have hs : (∑ g ∈ B, w t g) ≤ (H : ℚ) := by
    calc
      _ ≤ ∑ _g ∈ B, (1 : ℚ) := Finset.sum_le_sum (fun g _ => (hu g).2)
      _ = H := by simp [hB]
  have hb : slotMeanQ w B t ≤ 1 := by
    dsimp [slotMeanQ]
    rw [hB]
    exact (div_le_one hpos).mpr hs
  exact (hgrid.bounded (Nat.mul_pos hD hH) hn hb).mono
    (by have := size_mul_le D H; omega)

/-- Exact conditional-expectation selection. Each bucket is visited in fixed
good order, and the first minimizer is selected. Empty buckets are skipped;
the correctness theorem assumes precisely the nonempty buckets used by the
allocation algorithm. -/
def selectQ {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ) (P : Fin k → ℚ) :
    List (Fin k → ℚ) → List (Finset (Fin m)) → List (Fin m)
  | _, [] => []
  | left, B :: bs =>
      let cost (g : Fin m) := objectiveQ h q c P
        (left ++ (fun t => w t g) :: slotMeansQ w bs)
      match (B.sort (· ≤ ·)).argmin cost with
      | none => selectQ w h q c P left bs
      | some g => g :: selectQ w h q c P (left ++ [fun t => w t g]) bs

theorem selectQ_greedy {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (bs : List (Finset (Fin m)))
    (hne : ∀ B ∈ bs, B.Nonempty) (left : List (Fin k → ℚ)) :
    IsGreedySample (fun t g => (w t g : ℝ)) (h : ℝ) (q : ℝ) (c : ℝ)
      (fun t => (P t : ℝ)) (realProfiles left) bs (selectQ w h q c P left bs) := by
  induction bs generalizing left with
  | nil => trivial
  | cons B bs ih =>
    let cost (g : Fin m) := objectiveQ h q c P
      (left ++ (fun t => w t g) :: slotMeansQ w bs)
    have hrest : ∀ C ∈ bs, C.Nonempty := fun C hC => hne C (by simp [hC])
    have hB := hne B (by simp)
    cases he : (B.sort (· ≤ ·)).argmin cost with
    | none =>
      have hz : B.sort (· ≤ ·) = [] := List.argmin_eq_none.mp he
      obtain ⟨g, hg⟩ := hB
      have : g ∈ B.sort (· ≤ ·) := by simpa using hg
      simp [hz] at this
    | some g =>
      have hg : g ∈ B := by
        have hm := List.argmin_mem (show g ∈ (B.sort (· ≤ ·)).argmin cost by simp [he])
        simpa using hm
      have hm (a : Fin m) (ha : a ∈ B) : cost g ≤ cost a :=
        List.le_of_mem_argmin (l := B.sort (· ≤ ·)) (f := cost)
          (by simpa using ha) (by simp [he])
      dsimp only [cost] at he
      simp only [selectQ, he]
      change g ∈ B ∧ (∀ a ∈ B, _ ≤ _) ∧ _
      refine ⟨hg, ?_, ?_⟩
      · intro a ha
        have hh : (cost g : ℝ) ≤ (cost a : ℝ) := by exact_mod_cast hm a ha
        have hmeans : (slotMeansQ w bs).map (fun z t => (z t : ℝ)) =
            slotMeans (fun i g => (w i g : ℝ)) bs := slotMeansQ_cast w bs
        simpa only [cost, objectiveQ_cast, realProfiles, List.map_append, List.map_cons,
          hmeans] using hh
      · simpa only [realProfiles, List.map_append, List.map_cons, List.map_nil] using
          ih hrest (left ++ [fun t => w t g])

/-- Thus the rational program satisfies the same conditional-mean guarantee
used by both product estimators and by the quadratic prefixed objective. -/
theorem selectQ_objective_le {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (bs : List (Finset (Fin m))) (hne : ∀ B ∈ bs, B.Nonempty) :
    List.Forall₂ (fun B g => g ∈ B) bs (selectQ w h q c P [] bs) ∧
      objectiveQ h q c P ((selectQ w h q c P [] bs).map (fun g t => w t g)) ≤
        objectiveQ h q c P (slotMeansQ w bs) := by
  obtain ⟨hv, hobj⟩ := greedy_sample_le_mean (fun t g => (w t g : ℝ))
    (h : ℝ) (q : ℝ) (c : ℝ) (fun t => (P t : ℝ)) bs _
      (selectQ_greedy w h q c P bs hne [])
  refine ⟨hv, ?_⟩
  have hl := objectiveQ_cast h q c P ((selectQ w h q c P [] bs).map (fun g t => w t g))
  have hr := objectiveQ_cast h q c P (slotMeansQ w bs)
  rw [slotMeansQ_cast] at hr
  have hc : (objectiveQ h q c P ((selectQ w h q c P [] bs).map (fun g t => w t g)) : ℝ) ≤
      (objectiveQ h q c P (slotMeansQ w bs) : ℝ) := by
    rw [hl, hr]
    simpa only [realProfiles, List.map_map, Function.comp_def] using hobj
  exact_mod_cast hc

theorem selectQ_protected_greedy {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (protectedTypes : Finset (Fin k))
    (hz : ∀ t ∉ protectedTypes, ∀ g, w t g = 0)
    (bs : List (Finset (Fin m))) (hne : ∀ B ∈ bs, B.Nonempty) :
    IsProtectedGreedySample (fun t g => (w t g : ℝ)) (h : ℝ) (q : ℝ) (c : ℝ)
      (fun t => (P t : ℝ)) protectedTypes [] bs (selectQ w h q c P [] bs) := by
  apply (greedy_sample_iff_protected (fun t g => (w t g : ℝ)) (h : ℝ) (q : ℝ)
    (c : ℝ) (fun t => (P t : ℝ)) protectedTypes ?_ bs _).mp
  · exact selectQ_greedy w h q c P bs hne []
  · intro t ht g
    simp [hz t ht g]

/-- The prefix form is the one used by the cross-round quadratic estimator. -/
theorem selectQ_prefixed_objective_le {m k : ℕ} (w : Fin k → Fin m → ℚ)
    (h q c : ℚ) (P : Fin k → ℚ) (left : List (Fin k → ℚ))
    (bs : List (Finset (Fin m))) (hne : ∀ B ∈ bs, B.Nonempty) :
    List.Forall₂ (fun B g => g ∈ B) bs (selectQ w h q c P left bs) ∧
      objectiveQ h q c P (left ++ (selectQ w h q c P left bs).map (fun g t => w t g)) ≤
        objectiveQ h q c P (left ++ slotMeansQ w bs) := by
  obtain ⟨hv, hobj⟩ := greedy_sample_le_mean_aux (fun t g => (w t g : ℝ))
    (h : ℝ) (q : ℝ) (c : ℝ) (fun t => (P t : ℝ)) bs (realProfiles left) _
      (selectQ_greedy w h q c P bs hne left)
  refine ⟨hv, ?_⟩
  have hl := objectiveQ_cast h q c P
    (left ++ (selectQ w h q c P left bs).map (fun g t => w t g))
  have hr := objectiveQ_cast h q c P (left ++ slotMeansQ w bs)
  have he : realProfiles (left ++ slotMeansQ w bs) = realProfiles left ++
      slotMeans (fun i g => (w i g : ℝ)) bs := by
    rw [realProfiles, List.map_append]
    change realProfiles left ++ realProfiles (slotMeansQ w bs) = _
    rw [slotMeansQ_cast]
  rw [he] at hr
  have hc : (objectiveQ h q c P
      (left ++ (selectQ w h q c P left bs).map (fun g t => w t g)) : ℝ) ≤
      (objectiveQ h q c P (left ++ slotMeansQ w bs) : ℝ) := by
    rw [hl, hr]
    simpa only [realProfiles, List.map_append, List.map_map, Function.comp_def] using hobj
  exact_mod_cast hc

theorem bounded_pairSumQ (xs : List ℚ) (b : ℕ) (hx : ∀ x ∈ xs, Bounded x b) :
    Bounded (pairSumQ xs) ((2 * b + 2) * (xs.length + 1)^2) := by
  induction xs with
  | nil => exact bounded_zero.mono (by simp)
  | cons x xs ih =>
    have ht : ∀ y ∈ xs, Bounded y b := fun y hy => hx y (by simp [hy])
    have hb := ((hx x (by simp)).mul (bounded_sum xs b ht)).add (ih ht)
    change Bounded (x * xs.sum + pairSumQ xs) _
    apply hb.mono
    simp only [List.length_cons]
    nlinarith [Nat.zero_le b, Nat.zero_le xs.length]

theorem bounded_sampleProductQ (h : ℕ) (xs : List ℚ) (b : ℕ)
    (hh : 1 ≤ h) (hx : ∀ x ∈ xs, Bounded x b) :
    Bounded (sampleProductQ (h : ℚ) xs) ((h.size + b + 3) * xs.length + 1) := by
  have hf : ∀ z ∈ xs.map (fun x => 1 + ((h : ℚ) - 1) * x),
      Bounded z (h.size + b + 3) := by
    intro z hz
    obtain ⟨x, hxmem, rfl⟩ := List.mem_map.mp hz
    have hn : (h - 1 : ℕ).size ≤ h.size := Nat.size_le_size (Nat.sub_le h 1)
    have hb := bounded_one.add ((bounded_nat (h - 1)).mul (hx x hxmem))
    have he : ((h - 1 : ℕ) : ℚ) = (h : ℚ) - 1 := by rw [Nat.cast_sub hh]; simp
    rw [he] at hb
    exact hb.mono (by omega)
  simpa [sampleProductQ] using bounded_prod _ (h.size + b + 3) hf

/-- Explicit numerator/denominator digit bound for an evaluated type row. -/
def rowBits (h m b c : ℕ) : ℕ :=
  (2 * b + 2) * (m + 1)^2 + (h.size + b + 3) * m + 3 * c + 4

theorem bounded_rowObjectiveQ (h : ℕ) (q c p : ℚ) (xs : List ℚ) (b C : ℕ)
    (hh : 1 ≤ h) (hq : Bounded q C) (hc : Bounded c C) (hp : Bounded p C)
    (hx : ∀ x ∈ xs, Bounded x b) :
    Bounded (rowObjectiveQ (h : ℚ) q c p xs) (rowBits h xs.length b C) := by
  have htwo : Bounded (2 : ℚ) 2 := ⟨2, 1, by decide, by norm_num, by decide, by decide⟩
  have hpair := hq.mul (htwo.mul (bounded_pairSumQ xs b hx))
  have hprod := (hc.mul hp).mul (bounded_sampleProductQ h xs b hh hx)
  exact (hpair.add hprod).mono (by unfold rowBits; omega)

def objectiveBits (h k m b C : ℕ) : ℕ := (rowBits h m b C + 1) * k + 1

theorem bounded_objectiveQ {k : ℕ} (h : ℕ) (q c : ℚ) (P : Fin k → ℚ)
    (slots : List (Fin k → ℚ)) (b C : ℕ) (hh : 1 ≤ h)
    (hq : Bounded q C) (hc : Bounded c C) (hp : ∀ t, Bounded (P t) C)
    (hs : ∀ z ∈ slots, ∀ t, Bounded (z t) b) :
    Bounded (objectiveQ (h : ℚ) q c P slots) (objectiveBits h k slots.length b C) := by
  let rows := List.ofFn fun t : Fin k =>
    rowObjectiveQ (h : ℚ) q c (P t) (slots.map (fun z => z t))
  have hb : ∀ y ∈ rows, Bounded y (rowBits h slots.length b C) := by
    intro y hy
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hy
    apply (bounded_rowObjectiveQ h q c (P t) _ b C hh hq hc (hp t) ?_).mono
    · simp
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      exact hs z hz t
  have hsum := bounded_sum rows (rowBits h slots.length b C) hb
  simpa [rows, objectiveBits, objectiveQ, List.sum_ofFn] using hsum

theorem bounded_firstCoefficient {h : ℕ} (hh : 0 < h) :
    Bounded (128 / (h : ℚ)^3) (3 * (h.size + 1) + 9) := by
  have h128 : Bounded (128 : ℚ) 9 :=
    ⟨128, 1, by decide, by norm_num, by decide, by decide⟩
  have hh3 := ((bounded_nat h).mul (bounded_nat h)).mul (bounded_nat h)
  have hpow : Bounded ((h : ℚ)^3) (3 * (h.size + 1)) := by
    convert hh3 using 1 <;> ring
  exact (h128.div hpow (by positivity)).mono (by omega)

/-- One common coefficient budget covers the main first round, the later
product rounds, and the fixed-width product estimator. -/
def productCoefficientBits (h m b : ℕ) : ℕ :=
  (h.size + b + 3) * m + 3 * (h.size + 1) + 10

theorem bounded_productObjective {k m : ℕ} (h b : ℕ) (hh : 1 ≤ h)
    (history : Fin k → List ℚ) (slots : List (Fin k → ℚ))
    (hhist : ∀ t, (history t).length ≤ m)
    (hb : ∀ t x, x ∈ history t → Bounded x b)
    (hs : ∀ z ∈ slots, ∀ t, Bounded (z t) b) :
    Bounded (objectiveQ (h : ℚ) 1 (128 / (h : ℚ)^3)
      (fun t => sampleProductQ (h : ℚ) (history t)) slots)
      (objectiveBits h k slots.length b (productCoefficientBits h m b)) ∧
    Bounded (objectiveQ (h : ℚ) 0 1
      (fun t => sampleProductQ (h : ℚ) (history t)) slots)
      (objectiveBits h k slots.length b (productCoefficientBits h m b)) := by
  have hC : 1 ≤ productCoefficientBits h m b := by unfold productCoefficientBits; omega
  have hp (t : Fin k) : Bounded (sampleProductQ (h : ℚ) (history t))
      (productCoefficientBits h m b) := by
    apply (bounded_sampleProductQ h (history t) b hh (hb t)).mono
    have hm := Nat.mul_le_mul_left (h.size + b + 3) (hhist t)
    unfold productCoefficientBits
    omega
  have hc : Bounded (128 / (h : ℚ)^3) (productCoefficientBits h m b) :=
    (bounded_firstCoefficient (by omega)).mono (by unfold productCoefficientBits; omega)
  exact ⟨bounded_objectiveQ h 1 _ _ slots b _ hh (bounded_one.mono hC) hc hp hs,
    bounded_objectiveQ h 0 1 _ slots b _ hh (bounded_zero.mono hC) (bounded_one.mono hC) hp hs⟩

def quadraticPrefixQ {k : ℕ} (h : ℕ) (L : Fin k → ℚ) (t : Fin k) : ℚ :=
  L t + ((2 * (∑ i, L i) / h + (k : ℚ) / (h : ℚ)^2) / ((k : ℚ) / h)) / 2

theorem quadraticPrefixQ_cast {k : ℕ} (h : ℕ) (L : Fin k → ℚ) (t : Fin k) :
    (quadraticPrefixQ h L t : ℝ) =
      (L t : ℝ) + ((2 * (∑ i, (L i : ℝ)) / h + (k : ℝ) / (h : ℝ)^2) /
        ((k : ℝ) / h)) / 2 := by
  simp [quadraticPrefixQ]

def quadraticPrefixBits (h k b : ℕ) : ℕ :=
  (b + 1) * k + b + 4 * (h.size + 1) + 2 * (k.size + 1) + 7

/-- The cross-round quadratic coefficient is rational with polynomial-size
numerator and denominator, including its two nonzero divisions. -/
theorem bounded_quadraticPrefixQ {k h : ℕ} (hk : 0 < k) (hh : 0 < h)
    (L : Fin k → ℚ) (b : ℕ) (hb : ∀ t, Bounded (L t) b) (t : Fin k) :
    Bounded (quadraticPrefixQ h L t) (quadraticPrefixBits h k b) := by
  have htwo : Bounded (2 : ℚ) 2 := ⟨2, 1, by decide, by norm_num, by decide, by decide⟩
  have hsum : Bounded (∑ i, L i) ((b + 1) * k + 1) := by
    simpa [List.sum_ofFn] using bounded_sum (List.ofFn L) b
      (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hb i)
  have hfirst := (htwo.mul hsum).div (bounded_nat h) (by positivity)
  have hsecond := (bounded_nat k).div ((bounded_nat h).mul (bounded_nat h)) (by positivity)
  have hden := (bounded_nat k).div (bounded_nat h) (by positivity)
  have hratio := (hfirst.add hsecond).div hden (by positivity)
  have hout := (hb t).add (hratio.div htwo (by norm_num))
  have hbound := hout.mono (show _ ≤ quadraticPrefixBits h k b by
    unfold quadraticPrefixBits
    omega)
  simpa only [quadraticPrefixQ, pow_two] using hbound

/-- Counting additions and multiplications in the literal recursive pair
evaluator; summing an `n`-entry tail costs at most `n` additions. -/
def pairOps : ℕ → ℕ
  | 0 => 0
  | n + 1 => pairOps n + n + 2

theorem pairOps_le (n : ℕ) : pairOps n ≤ (n + 1)^2 := by
  induction n with
  | zero => simp [pairOps]
  | succ n ih => simp only [pairOps]; nlinarith

/-- A costed sum; the second component counts rational additions. -/
def sumCosted : List ℚ → ℚ × ℕ
  | [] => (0, 0)
  | x :: xs => let tail := sumCosted xs; (x + tail.1, tail.2 + 1)

theorem sumCosted_spec (xs : List ℚ) : sumCosted xs = (xs.sum, xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumCosted, ih]

/-- Costed literal pair evaluator. Costs are attached to the actual recursive
calls, including each recomputation of a tail sum. -/
def pairCosted : List ℚ → ℚ × ℕ
  | [] => (0, 0)
  | x :: xs =>
      let total := sumCosted xs
      let tail := pairCosted xs
      (x * total.1 + tail.1, total.2 + tail.2 + 2)

theorem pairCosted_spec (xs : List ℚ) :
    pairCosted xs = (pairSumQ xs, pairOps xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairCosted, sumCosted_spec, ih, pairSumQ, pairOps, Nat.add_comm]

def productCosted (h : ℚ) : List ℚ → ℚ × ℕ
  | [] => (1, 0)
  | x :: xs =>
      let tail := productCosted h xs
      ((1 + (h - 1) * x) * tail.1, tail.2 + 4)

theorem productCosted_spec (h : ℚ) (xs : List ℚ) :
    productCosted h xs = (sampleProductQ h xs, 4 * xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [productCosted, sampleProductQ, ih, Nat.mul_add]

def rowCosted (h q c p : ℚ) (xs : List ℚ) : ℚ × ℕ :=
  let pairs := pairCosted xs
  let product := productCosted h xs
  (q * (2 * pairs.1) + c * p * product.1, pairs.2 + product.2 + 5)

theorem rowCosted_spec (h q c p : ℚ) (xs : List ℚ) :
    rowCosted h q c p xs =
      (rowObjectiveQ h q c p xs, pairOps xs.length + 4 * xs.length + 5) := by
  simp [rowCosted, pairCosted_spec, productCosted_spec, rowObjectiveQ]

def sumResults : List (ℚ × ℕ) → ℚ × ℕ
  | [] => (0, 0)
  | p :: ps =>
      let tail := sumResults ps
      (p.1 + tail.1, p.2 + tail.2 + 1)

theorem sumResults_spec (ps : List (ℚ × ℕ)) :
    sumResults ps = ((ps.map Prod.fst).sum, (ps.map (fun p => p.2 + 1)).sum) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sumResults, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

def objectiveCosted {k : ℕ} (h q c : ℚ) (P : Fin k → ℚ)
    (slots : List (Fin k → ℚ)) : ℚ × ℕ :=
  sumResults (List.ofFn (fun t : Fin k => rowCosted h q c (P t) (slots.map (fun z => z t))))

theorem objectiveCosted_spec {k : ℕ} (h q c : ℚ) (P : Fin k → ℚ)
    (slots : List (Fin k → ℚ)) :
    objectiveCosted h q c P slots =
      (objectiveQ h q c P slots, k * (pairOps slots.length + 4 * slots.length + 6)) := by
  simp [objectiveCosted, sumResults_spec, List.map_ofFn, rowCosted_spec,
    List.sum_ofFn, objectiveQ, nsmul_eq_mul, Nat.add_assoc]

/-- A conservative arithmetic-operation count for the direct evaluator;
four operations per product factor include forming `h - 1`. -/
def objectiveOps (k n : ℕ) : ℕ := k * (pairOps n + 4 * n + 7)

theorem objectiveOps_le (k n : ℕ) : objectiveOps k n ≤ 12 * k * (n + 1)^2 := by
  have h := pairOps_le n
  have hrow : pairOps n + 4 * n + 7 ≤ 12 * (n + 1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_left k hrow
  dsimp [objectiveOps]
  nlinarith only [hm]

theorem objectiveCosted_polynomial {k : ℕ} (h q c : ℚ) (P : Fin k → ℚ)
    (slots : List (Fin k → ℚ)) :
    (objectiveCosted h q c P slots).1 = objectiveQ h q c P slots ∧
      (objectiveCosted h q c P slots).2 ≤ 12 * k * (slots.length + 1)^2 := by
  rw [objectiveCosted_spec]
  refine ⟨rfl, ?_⟩
  apply le_trans (Nat.mul_le_mul_left k (show pairOps slots.length + 4 * slots.length + 6 ≤
    pairOps slots.length + 4 * slots.length + 7 by omega))
  exact objectiveOps_le k slots.length

/-- The input size for a bucket scan is the total number of candidates,
not the exponentially many possible complete samples. -/
def candidateCount {m : ℕ} (bs : List (Finset (Fin m))) : ℕ :=
  (bs.map Finset.card).sum

theorem candidateCount_le_goods {m : ℕ} (bs : List (Finset (Fin m)))
    (hdisjoint : bs.Pairwise Disjoint) : candidateCount bs ≤ m := by
  let all := bs.flatMap (fun B => B.sort (· ≤ ·))
  have hn : all.Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun B _ => Finset.sort_nodup _ _, ?_⟩
    apply hdisjoint.imp
    intro B C hBC
    apply List.disjoint_left.mpr
    intro g hg hC
    exact Finset.disjoint_left.mp hBC (by simpa using hg) (by simpa using hC)
  have hb := hn.length_le_card
  simpa [all, candidateCount, List.length_flatMap, List.map_map, Function.comp_def] using hb

def selectionOps (k m candidates : ℕ) : ℕ :=
  2 * candidates * (objectiveOps k m + 2 * k * (m + 1) + 1)

theorem selectionOps_le {k m candidates : ℕ} (hc : candidates ≤ m) :
    selectionOps k m candidates ≤ 30 * (k + 1) * (m + 1)^3 := by
  have ho := objectiveOps_le k m
  have hlin : k * (m + 1) ≤ k * (m + 1)^2 := by
    exact Nat.mul_le_mul_left k (by nlinarith)
  have hinner : objectiveOps k m + 2 * k * (m + 1) + 1 ≤ 15 * (k + 1) * (m + 1)^2 := by
    nlinarith [show 1 ≤ (m + 1)^2 by nlinarith]
  unfold selectionOps
  calc
    2 * candidates * (objectiveOps k m + 2 * k * (m + 1) + 1) ≤
        (2 * (m + 1)) * (15 * (k + 1) * (m + 1)^2) :=
      Nat.mul_le_mul (by omega) hinner
    _ = 30 * (k + 1) * (m + 1)^3 := by ring

/-- A bit-cost envelope obtained when each rational operation/comparison is
charged at most a cubic function of the maximum operand bit length. This is
an explicit arithmetic cost model, not a claim about Lean VM execution time. -/
def bitCostEnvelope (operations bits : ℕ) : ℕ := operations * (bits + 1)^3

theorem selection_bitCostEnvelope_le {k m candidates bits : ℕ} (hc : candidates ≤ m) :
    bitCostEnvelope (selectionOps k m candidates) bits ≤
      30 * (k + 1) * (m + 1)^3 * (bits + 1)^3 :=
  Nat.mul_le_mul_right _ (selectionOps_le hc)

/-- Because selected goods are removed, the number of stored individual
factors is bounded by the original goods count. -/
theorem recorded_factors_le_goods {m : ℕ} (goods : List (Fin m)) (hg : goods.Nodup) :
    goods.length ≤ m := by simpa using hg.length_le_card

end OnlineMMS.BucketBitComplexity
